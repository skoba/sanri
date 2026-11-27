"""基準日版の検体検査のコード候補・属性・関係をローカルで照合する。"""

import argparse
from collections import Counter, defaultdict
import csv
from datetime import date
import hashlib
from itertools import combinations, product
import json
import unicodedata
import zipfile

from .audit_residual_urine import FILES, load_snapshot
from .fee_coverage import clause_paths
from .fee_ledger import INVENTORY, compare_points, load_lean, read_index
from .local_pdf import verified_pdf_pages
from .pdf_sources import NOTICE_PDF, NOTICE_SOURCE
from .r08_inventory import compact, notice_spans
from .procedure_master import (
    ARCHIVE_SHA256, INDEX_COLUMNS, LOCAL, _write, index_rows,
    load_registered, require,
)

DAY = date(2026, 10, 22)
SNAPSHOT = LOCAL / "ika/2026-10-13"
TABLE_ARCHIVE_HASH = "fc760da4394b51da006080660fbcec06612668ab2f8b21fea3d0da6a4ff3a2e0"

MATCH = "一致"
REPRESENTATION = "表現の差"
OMITTED = "意図された非収載"
MODEL_ERROR = "Lean側の形式化の誤りの疑い"
UNMODELED = "Lean側の未形式化"
SOURCE_CONFLICT = "資料間の不一致の疑い"
UNKNOWN = "情報不足で判定できない"
CLASSES = (MATCH, REPRESENTATION, OMITTED, MODEL_ERROR, UNMODELED, SOURCE_CONFLICT, UNKNOWN)

# 既存の原文レビューで確認した告示注番号とコード表項番の違い。
NOTE_NUMBERS = {
    ("D002", 0): 3, ("D006-5", 4): 1, ("D400", 3): 2,
    ("D401", 1): 0, ("D416", 3): 0,
}
GLYCEMIC = {("D005", 9), ("D007", 17), ("D007", 21)}
GLYCEMIC_SOURCES = ["notice/D005/paragraph/9", "notice/D007/paragraph/14"]

# 各準用の通知段落と対象項目を既存の独立した規則から得る。
REVIEWED_REFERENCES = {
    ("D001", "stripProteinCreatinineRatio"): ("D007", 1, "notice/D001/paragraph/11"),
    ("D007", "urinarySulfatedBileAcids"): ("D007", 18, "notice/D007/paragraph/15"),
    ("D004", "cxcl10"): ("D004", 15, "notice/D004/paragraph/15"),
    ("D023", "bk"): ("D023", 17, "notice/D023/paragraph/42"),
    ("D023", "mycobacteria"): ("D023", 25, "notice/D023/paragraph/43"),
    ("D006-17", "apoe"): ("D006-17", 0, "notice/D006-17/paragraph/2"),
}


def code_kind(record):
    if record.ref_division:
        return "reference"
    if record.notice_kind in {"7", "9"} or record.schedule_kind == "7":
        return "note"
    if (record.notice_kind, record.schedule_kind) == ("1", "1"):
        return "base"
    return None


UNNUMBERED = {"D019-2", "D021", "D022"}


def correspondence(record, by_key, reviewed_names=None):
    kind = code_kind(record)
    number = NOTE_NUMBERS.get((record.division, record.item), record.item) if kind == "note" else record.item
    if kind == "base" and record.division in UNNUMBERED and number == 1:
        number = 0
    # 率・減点・合成行に所定点数を当てない。
    if record.point_kind != "3":
        return None, [], "非単価"
    if kind is None:
        return None, [], "種別の射影なし"
    if kind == "reference":
        if (record.ref_chapter, record.ref_part) != (2, 3):
            return None, [], "準用元の章・部が対象外"
        candidates = [
            item for (division, _, k), items in by_key.items()
            if division == record.division and k == "reference"
            for item in items
            if REVIEWED_REFERENCES.get((division, item["item"]), ())[:2]
            == (record.ref_division, record.ref_item)
        ]
        if (record.division, record.item, record.ref_division, record.ref_item) == ("D001", 4, "D001", 4):
            candidates = by_key.get(("D001", 4, "base"), [])
    else:
        candidates = by_key.get((record.division, number, kind), [])
    matches = [p for p in candidates if p["points"] is not None and p["points"] == record.points]
    if not matches and kind == "base" and record.division == "D000" and number == 0:
        remote = by_key.get(("D000", 0, "remote"), [])
        replacements = [p for p in remote if p["points"] == record.points and record.in_out == "2"]
        if len(replacements) == 1:
            return replacements[0], remote, "通則の置換点数"
    if len(matches) == 1:
        return matches[0], candidates, "準用元・通知" if kind == "reference" else (
            "項番表記差" if number != record.item else "構造・点数")
    if len(matches) > 1:
        name = unicodedata.normalize("NFKC", record.name)
        species = (reviewed_names or {}).get((record.division, number), {}).get(name)
        named = [p for p in matches if p["item"].rsplit(".", 1)[-1] == species]
        if len(named) == 1:
            return named[0], candidates, "名称による"
    return None, candidates, "複数候補" if len(matches) > 1 else "根拠不足"


def grade(classification, reason, **details):
    return {"classification": classification, "reason": reason, **details}


def judgment_projection(point):
    """D026の通常振分けと遺伝子の指定区分。D004系の個別振分けは部分比較。"""
    division, number = point["division"], point["number"]
    major, *suffix = map(int, division[1:].split("-"))
    branch = suffix[0] if suffix else 0
    if point["kind"] != "base":
        return None
    if major == 26 and 1 <= number <= 7:
        return 2, {1: 1, 2: 17, 3: 2, 4: 3, 5: 4, 6: 5, 7: 6}[number]
    if major == 0:
        return 1, 0  # D000の判断料除外
    if major == 4:
        return (1, 17) if branch == 3 or (branch == 2 and number == 1) else None
    if major == 6 and branch in {*range(2, 10), *range(11, 21), *range(22, 32)}:
        return 1, 17
    if 1 <= major <= 23:
        return 1, next(group for end, group in ((3, 1), (6, 2), (7, 3), (10, 4),
                                                (16, 5), (23, 6)) if major <= end)
    return None


def bundle_projection(point):
    division, number = point["division"], point["number"]
    if point["kind"] != "base":
        return None
    if division == "D006":
        return 6 if 14 <= number <= 34 else 0
    if division == "D007":
        return 1 if 1 <= number <= 8 else 0
    if division == "D008":
        return 2 if 12 <= number <= 51 else 0
    if division == "D009":
        return 5 if 1 <= number <= 24 else 0
    if division == "D013":
        return 3 if 3 <= number <= 14 else 0
    if division == "D014":
        return 7 if 10 <= number <= 16 or number in {18, 19, 23, 35, 36} else 0
    if division == "D015":
        return 11 if number == 13 else 0
    return None


AGE_NOTES = {
    **{(d, 0): f"primary/{d}/note/unnumbered/1" for d in
       ("D401", "D402", "D403", "D404", "D404-2", "D407", "D416", "D417")},
    ("D400", 2): "primary/D400/note/2",
    ("D405", 0): "primary/D405/note/unnumbered/1",
    ("D419", 2): "primary/D419/item/2/note",
    ("D419", 3): "primary/D419/item/3/note/2",
    ("D419", 4): "primary/D419/item/4/note",
    ("D419", 5): "primary/D419/item/5/note/3",
}
FACILITY_ITEMS = {
    "D006-19": "primary/D006-19/note/1",
    "D409-2": "primary/D409-2/note/unnumbered/1",
    "D412-3": "primary/D412-3/note/unnumbered/1",
    "D415-5": "primary/D415-5/note/unnumbered/1",
    "D415-6": "primary/D415-6/note/unnumbered/1",
}


def inpatient_reference(record):
    if record.in_out != "1":
        return None
    if record.division == "D026" and record.item in {8, 9}:
        return f"primary/D026/note/{4 if record.item == 8 else 5}"
    if record.division in {"D025", "D027"}:
        return f"primary/{record.division}/note/1"
    return None


def age_comparison(record, point, by_key, records_by_code, archive_lines):
    if point["kind"] != "base":
        return None
    division = point["division"]
    number = 2 if division == "D400" else point["number"] if division == "D419" else 0
    clause = AGE_NOTES.get((division, number))
    if not clause:
        return None
    cutoff = "03" if division == "D405" else "06"
    expected = {p["points"] for p in by_key.get((division, number, "note"), []) if p["item"] == "infant"}
    for lower, upper, code in record.age_additions:
        target = records_by_code.get(str(code))
        if (target and target.usable_on(DAY) and target.point_kind == "3" and code_kind(target) == "note"
                and (lower, upper) == ("00", cutoff) and target.points in expected):
            return grade(REPRESENTATION if target.division != division else MATCH,
                         "年齢区間と加算点数。基本コードから加算コードを参照",
                         clauses=[clause], addition_archive_line=archive_lines[target.code])
    return grade(UNKNOWN, "年齢区間と点数が揃う有効加算行を未確認", clauses=[clause])


def compare_attributes(record, point, method, clauses, by_key, records_by_code, archive_lines):
    result = {}
    if reference := inpatient_reference(record):
        result["in_out"] = grade(MATCH, "モデルでは入院側参照。マスターも入院のみ",
                                 clauses=[reference])
        result["points"] = grade(UNMODELED, "入院側参照につき単価は外来モデルの範囲外",
                                 clauses=[reference])
    if point:
        result["points"] = grade(REPRESENTATION if method in {"項番表記差", "通則の置換点数"} else MATCH, method)
        io_ok = record.in_out in {"0", "2"}
        result["in_out"] = grade(MATCH if io_ok else UNKNOWN, "外来射影と入外適用欄")
        if point["kind"] == "remote":
            result["points"]["clauses"] = ["primary/ch2-part3/general/7"]
        if method == "準用元・通知":
            proof = REVIEWED_REFERENCES.get((point["division"], point["item"]))
            result["points"]["clauses"] = [proof[2] if proof else "notice/D001/paragraph/2"]
        expected = judgment_projection(point)
        if expected is not None:
            found = record.judgment_kind, record.judgment_group
            result["judgment"] = grade(
                MATCH if (int(found[0]), found[1]) == expected else UNKNOWN,
                "D026の通常振分け・遺伝子振分け・D000除外の単項目射影", expected=expected)
        expected = bundle_projection(point)
        if expected is not None:
            result["bundle_group"] = grade(
                MATCH if record.bundle_group == expected else UNKNOWN,
                "包括の対象項目への所属。群の履歴単位や点数は別", expected=expected,
                clauses=[BUNDLE_CLAUSES[point["division"]]])
        key = point["division"], point["number"]
        if age := age_comparison(record, point, by_key, records_by_code, archive_lines):
            result["age"] = age
        facility = FACILITY_ITEMS.get(point["division"]) if point["kind"] == "base" else None
        if key == ("D413", 1):
            facility = "primary/D413/note/unnumbered/1"
        if key == ("D026", 8) and point["item"] == "managementI":
            facility = "primary/D026/note/4/i"
        if facility:
            result["facility"] = grade(MATCH if any(record.facility_codes) else UNKNOWN,
                                       "施設要件の有無の射影。適合と届出の充足は別",
                                       clauses=[facility])
        if key in GLYCEMIC and point["kind"] == "base":
            result["max_count"] = grade(
                REPRESENTATION if record.max_count == 2 else UNKNOWN,
                "コード別の欄と通知の共有枠。期間・エラー処理はこの欄から決まらない",
                clauses=GLYCEMIC_SOURCES)
        if key == ("D006-12", 0) and point["kind"] == "base" and record.reduction == "1":
            result["reduction"] = grade(
                REPRESENTATION, "逓減対象の存在。適用条件・額の射影は未比較",
                clauses=["primary/D006-12/note/unnumbered/1"])
    for field in ("points", "in_out", "judgment", "bundle_group", "max_count", "max_count_handling",
                  "facility", "age", "reduction"):
        result.setdefault(field, grade(UNKNOWN, "対応する射影又はコード同定を確認できていない"))
        result[field].setdefault("clauses", clauses)
    return result


def exclusion_key(row):
    """対称行だけをまとめ、算定優先と特例、期間を保つ。"""
    first, second, direction = row[1], row[3], row[5]
    if second < first:
        first, second = second, first
        direction = {"1": "2", "2": "1", "3": "3"}[direction]
    return first, second, direction, row[6], row[-2], row[-1]


def table_rows(snapshot, codes):
    evidence = snapshot["evidence"]
    parents = defaultdict(list)
    specimen_parents = defaultdict(list)
    valid_auxiliary = set()
    for entry in evidence["auxiliary"]:
        if not entry["active_as_of"]:
            continue
        row = entry["fields"]
        require(row[1] not in valid_auxiliary, "補助マスターの基準日有効コードが重複")
        valid_auxiliary.add(row[1])
        for slot in (3, 5, 7):
            if row[slot] != "0":
                reference = (row[1], row[slot], entry["line"], slot + 1)
                parents[row[slot + 1]].append(reference)
                if row[1] in codes:
                    specimen_parents[row[slot + 1]].append(reference)
    result = {"inclusion": []}
    seen_inclusion_lines = set()
    for entry in evidence["inclusion"]:
        if not entry["active_as_of"]:
            continue
        row = entry["fields"]
        parent_index = parents if row[2] in codes else specimen_parents
        for parent, unit, line, column in parent_index.get(row[1], ()):
            seen_inclusion_lines.add(entry["line"])
            result["inclusion"].append({
                "codes": [parent, row[2]], "unit": unit, "special": row[4] == "1",
                "auxiliary_line": line, "auxiliary_column": column, "line": entry["line"],
            })
    for key, entries in evidence.items():
        if key.startswith("exclusion_"):
            pairs = defaultdict(list)
            for e in entries:
                if e["active_as_of"]:
                    pairs[exclusion_key(e["fields"])].append(e)
            result[key] = [{"codes": [a, b], "direction": direction, "special": flag == "1",
                            "rows": entries} for (a, b, direction, flag, _, _), entries in pairs.items()]
    result["frequency"] = [
        {"codes": [e["fields"][1]], "unit": e["fields"][3], "limit": int(e["fields"][5]),
         "special": e["fields"][6] == "1", "rows": [e]}
        for e in evidence["frequency"] if e["active_as_of"]
    ]
    result["auxiliary"] = [{"codes": [e["fields"][1]], "rows": [e]}
                           for e in evidence["auxiliary"]
                           if e["active_as_of"] and e["fields"][1] in codes]
    return result, seen_inclusion_lines


def item_key(point):
    return point["division"], point["item"].rsplit(".", 1)[-1]


# 通知から読み取った二件制約。範囲が違う場合も相手を照合し、差を残す。
# None は同時・同日・一連の境界が独立モデルで未確定であることを表す。
CHOICES = (
    ("sedimentMethodGroup", "notice/D002/paragraph/5", None,
     ("D002", "microscopy"), ("D002-2", "flow")),
    ("morphologyGroups", "notice/D005/paragraph/3", "specimen",
     ("D005", "eosinophilCount"), ("D005", "automatedDifferential")),
    ("morphologyGroups", "notice/D005/paragraph/3", "specimen",
     ("D005", "eosinophilCount"), ("D005", "microscopicDifferential")),
    ("morphologyGroups", "notice/D005/paragraph/7", None,
     ("D005", "bloodMicroorganisms"), ("D005", "dnaContainingRedCellCount")),
    ("chemistryCombinationGroup", "notice/D007/paragraph/2", "exclusion_simultaneous",
     ("D007", "calcium"), ("D007", "ionizedCalcium")),
    ("chemistryCombinationGroup", "notice/D007/paragraph/3", "exclusion_simultaneous",
     ("D007", "tibcColorimetric"), ("D007", "uibcColorimetric")),
    ("hepatitisGroup", "notice/D013/paragraph/5", "exclusion_simultaneous",
     ("D013", "hbcAntibody"), ("D013", "hbcIgM")),
    ("hepatitisGroup", "notice/D013/paragraph/6", "exclusion_simultaneous",
     ("D013", "haAntibody"), ("D013", "haIgM")),
) + tuple(
    ("sedimentBacteriaGroup", "primary/D017/note/unnumbered/1", "specimen", sediment, ("D017", bacteria))
    for sediment in (("D002", "microscopy"), ("D002-2", "flow"))
    for bacteria in ("specializedMicroscopy", "heatedAmoeba", "otherMicroscopy")
)

def same_division_choices(fn, division, paragraph, scope, items, peers=None):
    pairs = combinations(items, 2) if peers is None else product(items, peers)
    return tuple((fn, f"notice/{division}/paragraph/{paragraph}", scope, (division, a), (division, b))
                 for a, b in pairs)


CHOICES += (
    ("colitisChoice", "notice/D001/paragraph/6/i", "exclusion_month",
     ("D001", "prostaglandinEMajorMetabolite"), ("D003", "calprotectin")),
    ("atopyProteinGroup", "notice/D015/paragraph/11/i", "exclusion_month",
     ("D015", "scca2"), ("D015", "tarc")),
) + tuple(
    ("jointFluidGroup", "notice/D004/paragraph/1", None, ("D004", "jointFluid"), ("D017", bacteria))
    for bacteria in ("specializedMicroscopy", "heatedAmoeba", "otherMicroscopy")
)
CHOICES += same_division_choices("renalSimultaneousGroup", "D001", "3", "exclusion_simultaneous",
                                 ("transferrin", "albuminQuantitative", "typeIVCollagen"))
CHOICES += same_division_choices("urineSpecialSelectionInput", "D001", "9/i", None, ("lFabp", "ngal"))
CHOICES += same_division_choices("csfRatioGroup", "D004", "13/i", None,
                                 ("phosphoTau", "amyloidRatio", "phosphoTauAmyloidRatio"))
CHOICES += same_division_choices("coagulationMarkerGroup", "D006", "8/i", "exclusion_simultaneous",
                                 ("tat", "prothrombinFragment", "fibrinMonomer"))
CHOICES += same_division_choices("troponinMonthGroup", "D007", "22", "exclusion_month", ("troponinI",),
                                 ("troponinTQualitative", "troponinTQuantitative"))
for paragraph, anchor, peers in (
    ("27", ("hFabpQualitative", "hFabpQuantitative"), ("myoglobinQualitative", "myoglobinQuantitative")),
    ("30", ("typeIVCollagen", "typeIVCollagen7S"), ("procollagenIII", "mac2")),
    ("40/i", ("mac2",), ("typeIVCollagen", "typeIVCollagen7S", "procollagenIII", "hyaluronicAcid")),
    ("41/i", ("autotaxin",), ("typeIVCollagen", "typeIVCollagen7S", "procollagenIII", "hyaluronicAcid", "mac2")),
    ("42/i", ("ck18f",), ("typeIVCollagen", "typeIVCollagen7S", "procollagenIII", "hyaluronicAcid", "mac2", "autotaxin")),
    ("43/u", ("elfScore",), ("typeIVCollagen", "typeIVCollagen7S", "mac2", "autotaxin", "ck18f")),
):
    CHOICES += same_division_choices("lateChemistryGroup", "D007", paragraph, None, anchor, peers)
for paragraph, items, peers in (
    ("3", ("reninActivity", "reninQuantitative"), None),
    ("6/i", ("hcgBeta",), ("hcgQualitative", "hcgQuantitative", "hcgSemiquantitative")),
    ("13", ("ntx", "osteocalcin", "urineDpd"), None),
    ("15", ("tracp5b",), ("ntx", "osteocalcin", "urineDpd")),
    ("16", ("bap", "pinp", "intactPinp"), None),
    ("18", ("urineBetaCtx", "betaCtx"), None),
    ("25", ("metanephrine", "normetanephrine"), None),
    ("26/i", ("igfbp3", "somatomedinC"), None),
):
    CHOICES += same_division_choices("endocrineGroup", "D008", paragraph, None, items, peers)
CHOICES += same_division_choices("natriureticWeekGroup", "D008", "7/i", "exclusion_week",
                                 ("bnp", "ntProBnp", "anp"))
CHOICES += same_division_choices("herpesSkinRule", "D012", "34", None, ("herpesSkin",),
                                 ("herpesAntigen", "herpesCornea", "herpesGenital"))
CHOICES += same_division_choices("thyroidAntibodyGroup", "D014", "8", "exclusion_simultaneous",
                                 ("trab", "tsab"))
CHOICES += same_division_choices("electrophoresisGroup", "D015", "4/i", "specimen",
                                 ("wholeAntiserum", "specificAntiserum", "drugImmunofixation"))


FREQUENCIES = {
    ("D007", "cardiacMyosinLightChainI"): ("121", 1, "notice/D007/paragraph/38", "withMyosinHistory"),
    ("D007", "infliximabQualitative"): ("53", 3, "notice/D007/paragraph/49", "withInfliximabHistory"),
    ("D007", "vegf"): ("131", 1, "notice/D007/paragraph/51", "withVegfHistory"),
    ("D007", "elfScore"): ("146", 1, "notice/D007/paragraph/43/a", "elfSixMonthInterval"),
    ("D400", "otherBlood"): ("121", 1, "primary/D400/heading", "確認済みの日内既算定"),
    ("D419", "arterialBlood"): ("121", 1, "primary/D419/item/3", "確認済みの日内既算定"),
    ("D400", "venousBlood"): ("121", 1, "primary/D400/heading", "確認済みの日内既算定"),
}

FREQUENCIES.update({
    ("D026", name): ("131", 1, "notice/D026/paragraph/2", "DailyJudgment.previousClaimLimit")
    for name in ("urineFecal", "geneticChromosomal", "hematological", "biochemicalI",
                 "biochemicalII", "immunological", "microbiological")
})
FREQUENCY_UNITS = {"53": "患者当り", "121": "日", "131": "月", "138": "週", "141": "一連",
                   "144": "3月", "145": "4月", "146": "6月", "147": "12月"}

BUNDLE_CLAUSES = {
    "D006": "primary/D006/note/unnumbered/1",
    "D007": "primary/D007/note/unnumbered/1",
    "D008": "primary/D008/note/unnumbered/1",
    "D009": "primary/D009/note/2",
    "D013": "primary/D013/note/unnumbered/1",
    "D014": "primary/D014/note/1",
    "D015": "primary/D015/item/13/note",
}


def relation_positions(table, rel):
    if table == "inclusion":
        return {"child_line": rel["line"], "parent_line": rel["auxiliary_line"],
                "parent_column": rel["auxiliary_column"]}
    return {"lines": [entry["line"] for entry in rel["rows"]]}


def compare_tables(tables, mapping):
    inverse = defaultdict(set)
    for code, entry in mapping.items():
        if (p := entry["lean"]) and p["kind"] == "base":
            inverse[item_key(p)].add(code)
    glycemic = (inverse[("D005", "hemoglobinA1c")] | inverse[("D007", "glycatedAlbumin")]
               | inverse[("D007", "anhydroglucitol")])
    choice_lookup = defaultdict(list)
    for fn, clause, scope, a, b in CHOICES:
        choice_lookup[frozenset((a, b))].append((fn, clause, scope))
    by_choice = defaultdict(list)
    by_frequency = defaultdict(list)
    elf_rows = defaultdict(list)
    glycemic_pairs, glycemic_counts = defaultdict(list), defaultdict(list)
    for table, relations in tables.items():
        for rel in relations:
            codes = rel["codes"]
            points = [mapping[c]["lean"] if c in mapping else None for c in codes]
            keys = frozenset(item_key(p) for p in points if p)
            monthly_pair = table == "exclusion_month" and rel["direction"] == "3" and len(set(codes)) == 2
            monthly_count = table == "frequency" and (rel["unit"], rel["limit"]) == ("131", 1)
            if (monthly_pair or monthly_count) and rel["special"] and set(codes) <= glycemic:
                comparison = grade(REPRESENTATION, "通常月の件数射影。特例条件は通知で確認",
                                   clauses=GLYCEMIC_SOURCES)
                found = glycemic_pairs if monthly_pair else glycemic_counts
                found[frozenset(codes)].append(relation_positions(table, rel))
            elif table.startswith("exclusion_") and (choices := choice_lookup.get(keys)):
                projections = []
                for fn, clause, scope in choices:
                    same = scope == table and rel["direction"] == "3" and not rel["special"]
                    by_choice[keys, clause].append({"table": table, "same_projection": same,
                                                    "special": rel["special"], **relation_positions(table, rel)})
                    projections.append({"clause": clause, "definition": fn, "scope": scope, "same": same})
                if any(p["same"] for p in projections):
                    classification = MATCH
                elif all(p["scope"] is None for p in projections):
                    classification = UNMODELED
                else:
                    classification = UNKNOWN
                comparison = grade(
                    classification,
                    "相手と採否の射影を照合。適用範囲・群の履歴単位・特例は条項ごとに確認",
                    clauses=[p["clause"] for p in projections], projections=projections)
            elif table == "frequency" and points[0] and (expected := FREQUENCIES.get(item_key(points[0]))):
                unit, limit, clause, fn = expected
                same = (rel["unit"], rel["limit"]) == (unit, limit) and not rel["special"]
                if same:
                    by_frequency[item_key(points[0])].append(relation_positions(table, rel))
                comparison = grade(
                    (REPRESENTATION if fn == "elfSixMonthInterval" else MATCH) if same else UNKNOWN,
                    "単位・回数の射影。月の起算と患者・機関の範囲は欄から確定しない" if same else
                    "回数・単位又は特例の条件に照合残件あり",
                    clauses=[clause], lean_definition=fn, lean_unit=unit, lean_limit=limit)
            elif table == "inclusion" and rel["unit"] == "3" and not rel["special"] and all(points) and (
                item_key(points[0]) == ("D007", "elfScore") and
                item_key(points[1]) in {("D007", "procollagenIII"), ("D007", "hyaluronicAcid")}
            ):
                comparison = grade(MATCH, "構成成分を同時測定してスコアに含めた場合の非別算定",
                                   clauses=["notice/D007/paragraph/43/i"],
                                   lean_definition="BloodChemistryLate.Context.includedInElf")
                elf_rows[item_key(points[1])].append(relation_positions(table, rel))
            elif table == "inclusion" and mapping.get(codes[0], {}).get("master", {}).get("区分") == "D025":
                comparison = grade(UNMODELED, "入院包括の子の同定は外来判断料への確認入力",
                                   clauses=["primary/D025/note/2", "notice/D026/paragraph/5"])
            elif table == "inclusion" and all(points) and points[0]["kind"] == "note":
                parent, child = points
                division = parent["division"]
                if (division in BUNDLE_CLAUSES and child["division"] == division
                        and bundle_projection(child) and parent["item"].startswith("bundle")):
                    comparison = grade(
                        REPRESENTATION, "対象項目の所属が一致。一採血・項目数・選択の順序は別に確認",
                        clauses=[BUNDLE_CLAUSES[division]])
                else:
                    comparison = grade(UNKNOWN, "親の注と子の対応規則が未確認")
            elif table == "auxiliary":
                row = rel["rows"][0]["fields"]
                comparison = grade(UNKNOWN, "関係欄は索引。個別行の照合は各テーブルを参照",
                                   relation_flags=row[9:13])
            else:
                comparison = grade(UNKNOWN, "関係の適用条件・相手又は単位の対応が未確認")
            rel.update(comparison)
    reverse = {}
    for fn, clause, scope, a, b in CHOICES:
        hits = by_choice[frozenset((a, b)), clause]
        reverse[f"{clause}/{a[1]}/{b[1]}"] = grade(
            MATCH if any(hit["same_projection"] for hit in hits) else UNKNOWN,
            "対応した項目対のテーブル行を検索。関係なしの判定には使わない",
            clauses=[clause], lean_definition=fn, lean_scope=scope,
            mapping_sizes=[len(inverse[a]), len(inverse[b])], electronic_rows=hits)
    for rel in tables["frequency"]:
        rel["unit_label"] = FREQUENCY_UNITS.get(rel["unit"])
    for key, (unit, limit, clause, fn) in FREQUENCIES.items():
        hits = by_frequency[key]
        reverse[f"{clause}/{key[1]}"] = grade(
            MATCH if hits else UNKNOWN, "対応コードの単位・回数で検索",
            clauses=[clause], lean_definition=fn, unit=unit, limit=limit, electronic_rows=hits)
    for child in (("D007", "procollagenIII"), ("D007", "hyaluronicAcid")):
        hits = elf_rows[child]
        reverse[f"notice/D007/paragraph/43/i/{child[1]}"] = grade(
            MATCH if hits else UNKNOWN, "構成成分を子とする同時包括を検索",
            clauses=["notice/D007/paragraph/43/i"], electronic_rows=hits)
    complete = (len(glycemic) == 3 and len(glycemic_pairs) == 3 and len(glycemic_counts) == 3)
    reverse["glycemic_monthly"] = grade(
        REPRESENTATION if complete else UNKNOWN,
        "通知の共有制約から、コード別上限と全異種対の同一月背反を検索",
        clauses=GLYCEMIC_SOURCES, frequency_rows=list(glycemic_counts.values()),
        exclusion_rows=list(glycemic_pairs.values()))
    for division, clause in BUNDLE_CLAUSES.items():
        members = [(code, entry) for code, entry in mapping.items()
                   if (p := entry["lean"]) and p["division"] == division and bundle_projection(p)]
        relations = [relation_positions("inclusion", rel) for rel in tables["inclusion"]
                     if rel["classification"] == REPRESENTATION and clause in rel.get("clauses", ())]
        reverse[f"{clause}/membership"] = grade(
            REPRESENTATION if relations else UNKNOWN,
            "包括親子の対応を検索。なおマスター第16列は対象項目の所属を別に表現する",
            clauses=[clause], mapped_members=len(members),
            master_members=sum(entry["attributes"]["bundle_group"]["classification"] == MATCH
                               for _, entry in members),
            electronic_rows=relations)
    return reverse


def combination_reviews(reverse, tables, mapping):
    reviews = {}
    reviewed_sets = {
        "D002/D002-2/D017": {"microscopy", "flow", "specializedMicroscopy", "heatedAmoeba", "otherMicroscopy"},
        "D013": {"hbcAntibody", "hbcIgM", "haAntibody", "haIgM"},
        "D005": {"eosinophilCount", "automatedDifferential", "microscopicDifferential"},
    }
    for division, prefixes, conclusion in (
        ("D002/D002-2/D017", ("notice/D002/paragraph/5/", "primary/D017/note/unnumbered/1/"),
         "二件の同時背反は同時・同一検体の三件から高々一件を残す読みと両立する。"
         "二件ごとの算定義務や特例の内容は表から導けない"),
        ("D013", ("notice/D013/paragraph/5/", "notice/D013/paragraph/6/", "primary/D013/"),
         "同時背反と包括対象の所属は別に確認する。選択で外れた実施を一採血の項目数に数えるかは表から決まらない"),
        ("D005", ("notice/D005/paragraph/3/", "notice/D005/paragraph/7/"),
         "二者の同時背反で検出した組を記録する。検体の一致や三件併施全体の選択は決まらない"),
    ):
        names = reviewed_sets[division]
        codes = {code for code, entry in mapping.items()
                 if (p := entry["lean"]) and p["kind"] == "base"
                 and p["division"] in division.split("/") and item_key(p)[1] in names}
        projected = {}
        for table, rels in tables.items():
            if table == "inclusion" or table.startswith("exclusion_"):
                projected[table] = [
                    {"items": [item_key(mapping[c]["lean"]) for c in rel["codes"]],
                     "special": rel["special"], **relation_positions(table, rel)}
                    for rel in rels if all(c in codes for c in rel["codes"])
                ]
        reviews[division] = {"conclusion": conclusion, "direct_table_rows": projected, "evidence": {
            key: value for key, value in reverse.items() if key.startswith(prefixes)
        }}
    return reviews


def point_difference_evidence(point_sets, mapping, records_by_code, archive_lines):
    findings = []
    for row in point_sets["comparisons"]:
        if row["status"] == "match":
            continue
        division, number = row["division"], row["number"]
        for master in row["master"]:
            code = master["診療行為コード"]
            entry = mapping[code]
            findings.append({"side": "master", "code": code, "division": division, "number": number,
                             "archive_line": entry["archive_line"], **entry["attributes"]["points"]})
        for point in row["lean"]:
            fixed = [entry["archive_line"] for entry in mapping.values() if entry["lean"] == point]
            linked = []
            clause = AGE_NOTES.get((division, number))
            comparison = grade(MATCH, "個別の対応行を確認", archive_lines=fixed)
            if not fixed and point["item"] == "infant" and clause:
                for entry in mapping.values():
                    age = entry["attributes"]["age"]
                    if clause in age.get("clauses", ()) and "addition_archive_line" in age:
                        linked.append({"base_line": entry["archive_line"],
                                       "addition_line": age["addition_archive_line"]})
            if not fixed and (division, point["item"]) == ("D415-4", "guideSheath"):
                clause = "primary/D415-4/note/unnumbered/1"
                parents = [r for r in records_by_code.values() if r.division == division and r.usable_on(DAY)
                           and r.addition_key[0] > 0 and r.addition_key[1] == "0"]
                children = [r for r in records_by_code.values() if r.division == "D415" and r.item == 1
                            and r.usable_on(DAY) and code_kind(r) == "note" and r.points == point["points"]]
                linked = [{"base_line": archive_lines[parent.code], "addition_line": archive_lines[child.code]}
                          for parent in parents for child in children
                          if (parent.addition_key[0], "1") == child.addition_key]
            if linked:
                comparison = grade(REPRESENTATION, "同一区分の単価行に代わり共通加算行を参照",
                                   clauses=[clause], links=linked)
            elif not fixed:
                comparison = grade(UNKNOWN, "対応する有効コード又は加算リンクを未確認")
            findings.append({"side": "lean", "point": point, **comparison})
    return findings


def pack_inclusion(relations):
    """文字列の判定根拠と原本参照を別に持ち、直積の反復を抑える。"""
    results = []
    result_ids = {}
    rows = []
    for rel in relations:
        evidence = {k: rel[k] for k in ("classification", "reason", "clauses") if k in rel}
        key = evidence["classification"], evidence["reason"], tuple(evidence.get("clauses", ()))
        if key not in result_ids:
            result_ids[key] = len(results)
            results.append(evidence)
        rows.append([*rel["codes"], rel["unit"], rel["special"], rel["auxiliary_line"],
                     rel["auxiliary_column"], rel["line"], result_ids[key]])
    return {"columns": ["parent_code", "child_code", "unit", "special", "auxiliary_line",
                        "auxiliary_column", "inclusion_line", "result_index"],
            "results": results, "rows": rows}


def registered_snapshot(codes):
    # 変換版が配布ZIPのCSVと同じ内容であることを確認してから列を検査する。
    archive = SNAPSHOT / "tensuhyo_02.zip"
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == TABLE_ARCHIVE_HASH,
            "電子点数表ZIPが登録版と異なる")
    with zipfile.ZipFile(archive, metadata_encoding="cp932") as bundle:
        for filename, _ in FILES.values():
            members = [name for name in bundle.namelist() if name.rsplit("/", 1)[-1] == filename]
            require(len(members) == 1, f"ZIP内のCSVを一意に同定できない: {filename}")
            original = bundle.read(members[0]).decode("cp932").replace("\r\n", "\n")
            converted = (SNAPSHOT / "tables" / filename).read_bytes().decode("utf-8")
            require(original == converted, f"登録ZIPと変換CSVの内容が異なる: {filename}")
    return load_snapshot(SNAPSHOT, codes, DAY, cross_references=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-ledger", type=lambda value: LOCAL / "inventory" / value,
                        help="inventory 内に保存した FeeLedger.lean の出力ファイル名")
    options = parser.parse_args()
    backlog = read_index("specimen-backlog.json")
    require(backlog["revision_as_of"] == DAY.isoformat(), "通知索引の基準日が異なる")
    divisions = {r["code"] for r in backlog["rows"]}
    master_source = read_index("master-coverage.json")
    require(master_source["as_of"] == DAY.isoformat()
            and master_source["source"]["archive_sha256"] == ARCHIVE_SHA256, "マスター索引の版が異なる")
    records = load_registered()
    with (INVENTORY / "master-index.tsv").open(encoding="utf-8", newline="") as stream:
        reader = csv.reader(stream, delimiter="\t", strict=True)
        require(tuple(next(reader)) == INDEX_COLUMNS, "マスター索引の列が異なる")
        rows = list(reader)
    require(rows == [list(map(str, row)) for row in index_rows(records, DAY)],
            "マスター索引が原本からの再生成結果と異なる")
    archive_lines = {r.code: i for i, r in enumerate(records, 1)}
    records_by_code = {r.code: r for r in records}

    if options.lean_ledger:
        require(options.lean_ledger.resolve().parent == INVENTORY.resolve(),
                "Lean台帳は inventory 配下のファイル名を指定")
        with options.lean_ledger.open(encoding="utf-8") as stream:
            ledger = json.load(stream)
    else:
        ledger = load_lean()
    points = [p for p in ledger["points"] if p["division"] in divisions]
    by_key = defaultdict(list)
    for point in points:
        by_key[point["division"], point["number"], point["kind"]].append(point)
    clauses_by_division = defaultdict(set)
    for rule in ledger["rules"]:
        for path in clause_paths(rule):
            if path[1] in divisions:
                clauses_by_division[path[1]].add("/".join(path))

    require(INVENTORY.resolve() == INVENTORY, "入出力は tensuhyo/inventory 内に限る")
    names_path = INVENTORY / "specimen-reviewed-names.json"
    name_review = read_index(names_path.name) if names_path.exists() else []
    reviewed_names = {(r["division"], r["number"]): r["names"] for r in name_review}
    require(len(reviewed_names) == len(name_review), "名称確認の区分・項番が重複")
    notice = read_index("notice-impact.json")
    require(notice["as_of"] == DAY.isoformat(), "準用索引の基準日が異なる")
    references = {r["master"]["診療行為コード"]: r for r in notice["references"]}
    notice_pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
    notice_blocks = notice_spans(notice_pages, read_index("notice-index.json"), "paragraph")
    mapping = {}
    for index_line, row in enumerate(rows, 2):
        master = dict(zip(INDEX_COLUMNS, row, strict=True))
        if (master["区分"] not in divisions or master["基準日に使用可能"] != "1"
                or (master["章"], master["部"]) != ("2", "3")):
            continue
        code = master["診療行為コード"]
        record = records_by_code[code]
        item, candidates, method = correspondence(record, by_key, reviewed_names)
        clauses = sorted(clauses_by_division[record.division])
        name_candidates = []
        if record.ref_division and not item:
            key_name = compact(record.name)
            name_candidates = [{"clause": f"notice/{d}/paragraph/{n}", "pdf_pages": [start, end]}
                               for (d, n), blocks in notice_blocks.items()
                               if d in {record.division, record.ref_division}
                               for start, end, body in blocks
                               if len(key_name) >= 3 and key_name in body]
        mapping[code] = {
            "master": master, "archive_line": archive_lines[code], "index_line": index_line,
            "lean": item, "method": method, "candidates": candidates,
            "source_candidates": clauses, "reference_search": references.get(code),
            "notice_exact_name_candidates": name_candidates,
            "master_extra": {"addition_key": record.addition_key, "facility_codes": record.facility_codes,
                             "age_additions": record.age_additions},
            "attributes": compare_attributes(record, item, method, clauses, by_key,
                                             records_by_code, archive_lines),
        }

    snapshot = registered_snapshot(set(mapping))
    tables, inclusion_lines = table_rows(snapshot, set(mapping))
    reverse = compare_tables(tables, mapping)
    point_sets = compare_points(points, [entry["master"] for entry in mapping.values()])
    point_differences = point_difference_evidence(point_sets, mapping, records_by_code, archive_lines)
    classifications = Counter()
    attribute_counts = defaultdict(Counter)
    for entry in mapping.values():
        for field, value in entry["attributes"].items():
            attribute_counts[field][value["classification"]] += 1
            classifications[value["classification"]] += 1
    table_counts = {}
    for table, relations in tables.items():
        table_counts[table] = Counter(row["classification"] for row in relations)
        classifications.update(table_counts[table])
    classifications.update(value["classification"] for value in reverse.values())
    classifications.update(value["classification"] for value in point_differences)
    reference_status = Counter(
        "通知・Lean対応" if entry["lean"] else (entry["reference_search"] or {}).get("status", "索引なし")
        for entry in mapping.values() if entry["master"]["準用元区分"]
    )
    summary = {
        "divisions": len(divisions), "codes": len(mapping),
        "mapped": sum(entry["lean"] is not None for entry in mapping.values()),
        "name_based": sum(entry["method"] == "名称による" for entry in mapping.values()),
        "inclusion_source_rows": len(inclusion_lines),
        "reference_status": reference_status,
        "unmapped_reference_with_notice_name_hits": sum(bool(e["notice_exact_name_candidates"])
                                                        for e in mapping.values()),
        "previous_point_set_differences": Counter(r["classification"] for r in point_differences),
        "lean_to_electronic": Counter(r["classification"] for r in reverse.values()),
        "methods": Counter(entry["method"] for entry in mapping.values()),
        "attributes": attribute_counts, "tables": table_counts,
        "special": {table: sum(row.get("special", False) for row in rels)
                    for table, rels in tables.items()},
        "classifications": {key: classifications[key] for key in CLASSES},
    }
    report = {
        "as_of": DAY.isoformat(), "summary": summary, "master_source": master_source["source"],
        "table_source": {k: v for k, v in snapshot.items() if k != "evidence"},
        "clause_index": {d: sorted(ids) for d, ids in clauses_by_division.items()},
        "mapping_by_code": mapping, "electronic_to_lean": tables, "lean_to_electronic": reverse,
        "previous_point_set_differences": point_differences,
        "three_combination_reviews": combination_reviews(reverse, tables, mapping),
    }
    report["electronic_to_lean"]["inclusion"] = pack_inclusion(tables["inclusion"])
    path = INVENTORY / "specimen-external-audit.json"
    _write(path, json.dumps(report, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(path)
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

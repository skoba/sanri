"""基準日版の検体検査のコード候補・属性・関係をローカルで照合する。"""

import argparse
from collections import Counter, defaultdict
import csv
from datetime import date
import hashlib
from itertools import combinations, product
import json
import re
import unicodedata
import zipfile

from .audit_residual_urine import FILES, load_snapshot
from .fee_coverage import clause_paths
from .fee_ledger import INVENTORY, compare_points, load_lean, read_index
from .local_pdf import verified_pdf_pages
from .pdf_sources import NOTICE_PDF, NOTICE_SOURCE, R08_DOWNLOADS
from .r08_inventory import compact, notice_spans
from .specimen_audit_groups import group_inventory
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


UNNUMBERED = {"D006-23", "D019-2", "D021", "D022"}


def normalized_name(name):
    return "".join(unicodedata.normalize("NFKC", name).split())


REFERENCE_TERMS = re.compile(r"準じ|準用|所定点数|により算定")


def reference_candidates(record, notice_blocks, divisions):
    """索引済みの全対象段落を探索し、名称又は準用先の区分・項を候補にする。"""
    name = compact(record.name)
    item = f"「{record.ref_item}」"
    results = []
    for (division, paragraph), blocks in notice_blocks.items():
        if division not in divisions:
            continue
        for start, end, body in blocks:
            terms = sorted(set(REFERENCE_TERMS.findall(body)))
            if not terms:
                continue
            exact = len(name) >= 3 and name in body
            target = (division == record.ref_division and item in body
                      or re.search(re.escape(record.ref_division) + r".{0,50}" + re.escape(item), body))
            if exact or target:
                results.append({"clause": f"notice/{division}/paragraph/{paragraph}",
                                "pdf_pages": [start, end], "terms": terms,
                                "exact_name": exact, "target_item_candidate": bool(target)})
    return results


def reviewed_point(points, selection, price):
    if isinstance(selection, str):
        selection = {"item": selection}
    if selection is None:
        return None
    matches = [p for p in points if p["item"].rsplit(".", 1)[-1] == selection["item"]
               and p["points"] == price
               and ("branch" not in selection or p["branch"] == selection["branch"])]
    return matches[0] if len(matches) == 1 else None


def reference_rate_projection(record, by_key, evidence):
    target = (evidence or {}).get("reference_rate")
    if target is None or (record.ref_chapter, record.ref_part) != (2, 3):
        return None
    if (record.ref_division, record.ref_item) != (target["division"], target["master_item"]):
        return None
    points = by_key.get((target["division"], target["number"], "base"), ())
    point = reviewed_point(points, target["item"], record.points)
    if point:
        return {"point": point, "master_item": record.ref_item,
                "item_status": "項番一致" if record.ref_item == point["number"] else "項番差・由来未確定",
                "scope": "準用先の単価候補。元の検体・適格性の対応は未確定"}
    return None


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
    name = normalized_name(record.name)
    reviewed_item = (reviewed_names or {}).get((record.division, number), {}).get(name)
    if isinstance(reviewed_item, dict) and "number" in reviewed_item:
        lookup = (record.division, reviewed_item["number"], reviewed_item["kind"])
        candidates = by_key.get(lookup, [])
        point = reviewed_point(candidates, reviewed_item, record.points)
        return point, candidates, "名称による" if point else "根拠不足"
    if (record.division, number, kind) == ("D000", 0, "note") and reviewed_item:
        general = by_key.get(("D000", 0, "general"), [])
        named = [p for p in general if p["item"] == reviewed_item and p["points"] == record.points]
        if len(named) == 1:
            return named[0], general, "名称による"
    if (record.division, record.item, record.ref_division, record.ref_item, reviewed_item) == (
            "D012", 42, "D012", 39, "herpesSkin"):
        candidates = by_key.get(("D012", 42, "base"), [])
        named = [p for p in candidates if item_key(p)[1] == reviewed_item and p["points"] == record.points]
        if len(named) == 1:
            return named[0], candidates, "名称による"
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
    if point := reviewed_point(matches, reviewed_item, record.points):
        return point, candidates, "名称による"
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
    if (record.division, record.item, code_kind(record)) == ("D007", 65, "note"):
        return "primary/D007/note/unnumbered/2"
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
        if record.in_out == "1":
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
    ("BloodChemistryLate.rules", "notice/D007/paragraph/46/i", "exclusion_month",
     ("D003", "calprotectin"), ("D007", "lrg")),
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
for paragraph, scope, left, right in (
    ("2", None, ("mycoplasmaQual", "mycoplasmaSemi", "mycoplasmaChromatography", "mycoplasmaFluorescence"), None),
    ("4", "exclusion_simultaneous", ("stoolAdenovirus",), ("stoolRotavirusQual", "stoolRotavirusQuant")),
    ("23", None, ("pneumoniaeIgM",), ("pneumoniaeIgG", "pneumoniaeIgA")),
    ("28", None, ("ecoliO157Antibody", "ecoliO157Antigen"), None),
    ("31/i", None, ("pneumococcusWall", "pneumococcusCapsule"), None),
    ("48/e", None, ("dengueAntigen", "dengueCombo"), None),
    ("56", None, ("toxoplasmaAntibody", "toxoplasmaAvidity"), None),
):
    CHOICES += same_division_choices("infectionGroup", "D012", paragraph, scope, left, right)


# D004-2 (7) の「1」は簡易・複雑の三つの基本項目に射影する。
HEMATOLOGIC_PARTNERS = (
    ("D006-2", "hematopoieticTumorGene"),
    ("D006-6", "immuneRearrangement"),
    ("D006-14", "flt3"),
    ("D006-16", "jak2"),
)
CHOICES += tuple(
    ("hematologicMonthlyGroup", "notice/D004-2/paragraph/7", "exclusion_month", a, b)
    for a, b in (
        *product((("D004-2", item) for item in ("drugAid", "otherSimple", "complex")),
                 HEMATOLOGIC_PARTNERS),
        *combinations(HEMATOLOGIC_PARTNERS, 2),
    )
)


FREQUENCIES = {
    ("D000", "emergencyAddition"): ("121", 1, "primary/ch2-part3-section1-subsection1/general/1", "Examinations.assessSpecimen"),
    ("D000", "rapidAddition"): ("121", 5, "primary/ch2-part3-section1-subsection1/general/3", "Examinations.assessSpecimen"),
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
FREQUENCIES.update({
    ("D001", "myoinositol"): ("147", 1, "notice/D001/paragraph/5", "D001.myoinositolRule"),
    ("D001", "prostaglandinEMajorMetabolite"): ("144", 1, "notice/D001/paragraph/6/a", "D001.pgeRule"),
    ("D001", "oxalate"): ("147", 1, "notice/D001/paragraph/7", "D001.oxalateRule"),
    ("D001", "lFabp"): ("144", 1, "notice/D001/paragraph/8", "D001.lfabpRule"),
    ("D007", "lipoproteinA"): ("144", 1, "notice/D007/paragraph/19", "lipoproteinIntervalRule"),
    ("D007", "pentosidine"): ("144", 1, "notice/D007/paragraph/25", "pentosidineRule"),
    ("D007", "inulin"): ("146", 1, "notice/D007/paragraph/26", "inulinRule"),
    ("D007", "remnantLipoproteinCholesterol"): ("144", 1, "notice/D007/paragraph/33", "remnantThreeMonthInterval"),
    ("D006-6", "immuneRearrangement"): ("146", 1, "notice/D006-6/paragraph/1", "Immune.frequencyRule"),
    ("D006-16", "jak2"): ("53", 1, "notice/D006-16/paragraph/1", "Jak2.indicationRule"),
    ("D009", "22"): ("131", 1, "notice/D009/paragraph/13", "D009.p53Rule"),
    ("D006-30", "retinalDystrophy"): ("53", 1, "notice/D006-30/paragraph/1", "retinalRule"),
    ("D006-31", "idh1"): ("53", 1, "notice/D006-31/paragraph/unnumbered", "D006Late.idh1Rule"),
    ("D004-2", "sensitivity"): ("53", 1, "notice/D004-2/paragraph/13", "D004Tumor.sensitivityRule"),
    ("D007", "manganese"): ("144", 1, "notice/D007/paragraph/8", "BloodChemistry.manganeseRule"),
    ("D007", "lrg"): ("144", 1, "notice/D007/paragraph/46/a", "BloodChemistryLate.rules"),
    ("D013", "hcvSerotype"): ("53", 1, "notice/D013/paragraph/7", "D013.serotype"),
    ("D013", "hbcrAntigen"): ("131", 1, "notice/D013/paragraph/8", "D013.coreRelatedAntigen"),
    ("D013", "hbvGenotype"): ("53", 1, "notice/D013/paragraph/9", "D013.genotype"),
    ("D419", "gastricDuodenalFluid"): ("141", 1, "primary/D419/item/1", "確認済みの一連の既算定"),
    ("D419", "adrenalVenousSampling"): ("141", 1, "primary/D419/item/5", "確認済みの一連の既算定"),
})
for item, paragraph in (
    ("ros1", "2/a"), ("alk", "3/a"), ("metEx14", "4/a"), ("ntrk", "5/a"),
    ("ras", "6/a"), ("braf", "7/a"), ("colorectalHer2", "8"),
    ("lungHer2", "9/a"), ("microsatellite", "10/a"), ("otherSolidHer2", "12"), ("esr1", "13"),
):
    FREQUENCIES["D006-27", item] = (
        "53", 1, f"notice/D006-27/paragraph/{paragraph}", "D006PlasmaPanel.prior")
RENAL_FREQUENCIES = {("D001", item) for item in ("transferrin", "albuminQuantitative", "typeIVCollagen")}
FREQUENCIES.update({key: ("144", 1, "notice/D001/paragraph/3", "D001.renalRule")
                    for key in RENAL_FREQUENCIES})
FREQUENCY_EXCEPTIONS = {
    ("D001", "prostaglandinEMajorMetabolite"): "医学的必要性による月1回と記録",
    ("D001", "oxalate"): "通知が原則とする上限。例外の詳細は欄から読めない",
    ("D001", "lFabp"): "医学的必要性と摘要記載",
    ("D007", "lrg"): "医学的必要性がある月一回経路と診療録・摘要の記載",
}

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


def code_reason(record, candidates, method):
    if method == "非単価":
        return "率・減算等の非単価"
    if record.in_out == "1" or inpatient_reference(record):
        return "入院のみ"
    if record.ref_division:
        return "準用の由来・項目未確定"
    if method == "複数候補":
        if (record.division, record.item) == ("D007", 29):
            return "定性・定量を合成したコードとLeanの方式別項目"
        if (record.division, record.item) == ("D007", 1):
            return "複数の検査種類・方法とLeanの項目・算定単位の対応未確定"
        if (record.division, record.item) == ("D007", 3):
            return "複数の検査種類をまとめたコード"
        return "告示の検査種類との対応未確定"
    if record.division == "D006-4":
        if record.item == 5:
            return "複数疾患の包括点数候補の同定未確認"
        if record.item == 4:
            return "通知の疾患枝と等級の対応未確認"
    if record.bundle_group and code_kind(record) == "note":
        return "包括点数候補の同定未確認"
    if not candidates:
        return "台帳に同じ区分・項番・種別の項目なし"
    return "点数又は種別の対応未確認"


def relation_scope(codes, mapping, locations):
    unknown_location = any(c not in mapping and c not in locations for c in codes)
    if unknown_location:
        return "相手の区分未同定"
    if any(c not in mapping for c in codes):
        return "対象範囲外（相手が検体検査外）"
    if any(mapping[c]["master"]["入外適用区分"] == "1" for c in codes):
        return "対象範囲外（入院のみ）"
    if any(mapping[c]["lean"] is None for c in codes):
        return "検体検査のコード未対応"
    return "両端対応済み"


def reason_counts(rows):
    return Counter(row.get("reason_type", row["classification"]) for row in rows)


def collection_inclusion(parent, child_location, rel):
    if not parent or parent["kind"] != "base" or rel["unit"] != "3" or rel["special"]:
        return None
    if parent["division"] in {"D412", "D412-2"} and child_location in {
            (2, 3, "D208"), (2, 3, "D215")}:
        division = parent["division"]
        return grade(
            REPRESENTATION, "親の非別算定規則と子の検査区分が対応。各行の実施目的は表から読めない",
            reason_type="非別算定の区分・同時単位の射影",
            clauses=[f"notice/{division}/paragraph/unnumbered"])
    return None


def pair_coverage(left, right, hits):
    """対応済みのコードの直積で、方向・単位を保った背反の被覆を比較する。"""
    expected = {frozenset((a, b)) for a, b in product(left, right) if a != b}
    seen = {frozenset(hit["codes"]) for hit in hits if hit["same_projection"]}
    matching = expected & seen
    if not expected:
        status = "コード未対応" if not left or not right else "同一コードへ縮約"
    elif matching == expected:
        status = "全対一致"
    elif matching:
        status = "一部のみ"
    else:
        status = "一致対なし"
    return {"status": status, "expected": len(expected), "matching": len(matching)}


def compare_tables(tables, mapping, locations):
    inverse = defaultdict(set)
    for code, entry in mapping.items():
        if (p := entry["lean"]) and p["kind"] in {"base", "general"}:
            inverse[item_key(p)].add(code)
    glycemic = (inverse[("D005", "hemoglobinA1c")] | inverse[("D007", "glycatedAlbumin")]
               | inverse[("D007", "anhydroglucitol")])
    choice_lookup = defaultdict(list)
    for fn, clause, scope, a, b in CHOICES:
        choice_lookup[frozenset((a, b))].append((fn, clause, scope))
    by_choice = defaultdict(list)
    by_frequency = defaultdict(list)
    elf_rows = defaultdict(list)
    general_day_rows = []
    inclusion_pairs = set()
    glycemic_pairs, glycemic_counts = defaultdict(list), defaultdict(list)
    for table, relations in tables.items():
        for rel in relations:
            codes = rel["codes"]
            points = [mapping[c]["lean"] if c in mapping else None for c in codes]
            keys = frozenset(item_key(p) for p in points if p)
            monthly_pair = table == "exclusion_month" and rel["direction"] == "3" and len(set(codes)) == 2
            monthly_count = table == "frequency" and (rel["unit"], rel["limit"]) == ("131", 1)
            scope = None
            if table.startswith("exclusion_"):
                scope = relation_scope(codes, mapping, locations)
                rel["structure"] = scope
                rel["locations"] = [locations.get(code) for code in codes]
            if table == "inclusion" and codes[0] not in mapping:
                reason = ("対象範囲外（親が検体検査外）" if codes[0] in locations
                          else "親の区分未同定")
                comparison = grade(UNKNOWN, "親の区分による対象範囲の分類", reason_type=reason)
            elif table == "inclusion" and (included := collection_inclusion(
                    points[0], locations.get(codes[1]), rel)):
                comparison = included
            elif table == "inclusion" and codes[1] not in mapping:
                comparison = grade(UNKNOWN, "親の規則と子の具体的な関連費用の対応未確認",
                                   reason_type="子が検体検査外・非別算定の条件未照合")
            elif scope and scope != "両端対応済み":
                comparison = grade(UNKNOWN, "背反の相手・入外・対応の構造", reason_type=scope)
            elif (monthly_pair or monthly_count) and rel["special"] and set(codes) <= glycemic:
                comparison = grade(REPRESENTATION, "通常月の件数射影。特例条件は通知で確認",
                                   clauses=GLYCEMIC_SOURCES)
                found = glycemic_pairs if monthly_pair else glycemic_counts
                found[frozenset(codes)].append(relation_positions(table, rel))
            elif (table == "exclusion_day" and not rel["special"]
                  and keys == {("D000", "emergencyAddition"), ("D000", "rapidAddition")}
                  and rel["direction"] in {"1", "2"}
                  and item_key(points[int(rel["direction"]) - 1])[1] == "emergencyAddition"):
                comparison = grade(
                    MATCH, "緊急加算を算定する同日に迅速加算を別算定できない",
                    reason_type="同日・優先方向の射影",
                    clauses=["primary/ch2-part3-section1-subsection1/general/1"],
                    lean_definition="Examinations.assessSpecimen")
                general_day_rows.append(relation_positions(table, rel))
            elif table.startswith("exclusion_") and (choices := choice_lookup.get(keys)):
                projections = []
                for fn, clause, scope in choices:
                    same = scope == table and rel["direction"] == "3" and not rel["special"]
                    by_choice[keys, clause].append({"table": table, "same_projection": same,
                                                    "codes": codes, "direction": rel["direction"],
                                                    "special": rel["special"], **relation_positions(table, rel)})
                    projections.append({"clause": clause, "definition": fn, "scope": scope, "same": same})
                if any(p["same"] for p in projections):
                    classification = MATCH
                elif not rel["special"] and rel["direction"] == "3" and any(
                        p["scope"] is not None and p["scope"] != table for p in projections):
                    classification = REPRESENTATION
                else:
                    classification = UNKNOWN
                comparison = grade(
                    classification,
                    "相手と採否の射影を照合。適用範囲・群の履歴単位・特例は条項ごとに確認",
                    clauses=[p["clause"] for p in projections], projections=projections,
                    reason_type=("単位・同一性の差" if classification == REPRESENTATION else
                                 "優先方向の対応未確認" if rel["direction"] != "3" else
                                 "特例条件未確認" if rel["special"] else
                                 "履歴単位未確定" if classification == UNKNOWN else "同じ単位・採否の射影"))
            elif table == "frequency" and points[0] and (expected := FREQUENCIES.get(item_key(points[0]))):
                unit, limit, clause, fn = expected
                key = item_key(points[0])
                exception = FREQUENCY_EXCEPTIONS.get(key)
                same = ((rel["unit"], rel["limit"]) == (unit, limit)
                        and (not rel["special"] or exception is not None))
                shared = key in RENAL_FREQUENCIES or key == ("D006-30", "retinalDystrophy")
                representation = (shared or rel["special"] or fn == "elfSixMonthInterval"
                                  or key == ("D000", "rapidAddition"))
                if same:
                    by_frequency[item_key(points[0])].append(relation_positions(table, rel))
                comparison = grade(
                    (REPRESENTATION if representation else MATCH)
                    if same else UNKNOWN,
                    "単位・回数の射影。月の起算と患者・機関の範囲は欄から確定しない" if same else
                    "回数・単位又は特例の条件に照合残件あり",
                    clauses=[clause], lean_definition=fn, lean_unit=unit, lean_limit=limit,
                    reason_type=("単位・回数の射影" if same else "特例条件未確認" if rel["special"]
                                 else "単位・回数未一致"),
                    shared_scope=shared, notice_exception=exception,
                    unreadable=["月の起算", "患者・機関の範囲", "一連の範囲",
                                *(["特例の具体的な適用条件"] if rel["special"] else [])])
            elif (table == "frequency" and points[0] and points[0]["division"] == "D010"
                  and points[0]["number"] == 8 and (rel["unit"], rel["limit"]) == ("131", 1)
                  and not rel["special"]):
                note = 2 if points[0]["branch"] == 4 else 1
                comparison = grade(
                    REPRESENTATION, "月一回の数値と単位を照合。施設条件と枝間の共有は残る",
                    clauses=[f"primary/D010/note/{note}"], lean_definition="D010.MonthAvailable",
                    reason_type="単位・回数の射影")
            elif (table == "frequency" and points[0] and points[0]["division"] == "D006-4"
                  and (rel["unit"], rel["limit"]) == ("53", 1) and rel["special"]):
                comparison = grade(
                    REPRESENTATION, "患者当り一回の通常枠を照合。台帳の疾患別履歴とコード別欄を区別",
                    clauses=["notice/D006-4/paragraph/1"], lean_definition="D006Genetic.RepeatCondition",
                    reason_type="疾患別履歴とコード別枠の差",
                    notice_exception="反復が医学的に必要な場合。理由の摘要記載",
                    unreadable=["電子表の特例の具体的な適用条件"])
            elif (table == "frequency" and points[0] and points[0]["kind"] == "base"
                  and points[0]["division"] == "D009" and (rel["unit"], rel["limit"]) == ("53", 1)
                  and not rel["special"]):
                comparison = grade(
                    REPRESENTATION, "通常の診断経路では診断上の一連を照会。表は患者当りのコード別枠",
                    clauses=["primary/D009/note/1", "notice/D009/paragraph/1"],
                    lean_definition="D009.EpisodeAvailable",
                    reason_type="患者当りと診断上の一連の差",
                    unreadable=["診断上の一連の範囲", "管理料経路", "通知の例外"])
            elif table == "frequency" and mapping[codes[0]]["master"]["入外適用区分"] == "1":
                comparison = grade(UNKNOWN, "入院の回数行", reason_type="対象範囲外（入院のみ）")
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
            if "reason_type" not in comparison:
                if comparison["classification"] == UNKNOWN:
                    reason = ("特例条件未確認" if rel.get("special") else
                              "検体検査のコード未対応" if not all(points) else
                              "対応する条項・適用単位未確認")
                else:
                    reason = comparison["classification"]
                comparison["reason_type"] = reason
            rel.update(comparison)
            if table == "inclusion" and all(points):
                inclusion_pairs.add(keys)
    reverse = {
        "primary/ch2-part3-section1-subsection1/general/1/day": grade(
            MATCH if general_day_rows else UNKNOWN, "緊急加算の優先方向と同日背反を検索",
            clauses=["primary/ch2-part3-section1-subsection1/general/1"],
            electronic_rows=general_day_rows)
    }
    for fn, clause, scope, a, b in CHOICES:
        hits = by_choice[frozenset((a, b)), clause]
        reverse[f"{clause}/{a[1]}/{b[1]}"] = grade(
            MATCH if any(hit["same_projection"] for hit in hits) else UNKNOWN,
            "対応した項目対のテーブル行を検索。関係なしの判定には使わない",
            clauses=[clause], lean_definition=fn, lean_scope=scope,
            mapping_sizes=[len(inverse[a]), len(inverse[b])], electronic_rows=hits,
            coverage=pair_coverage(inverse[a], inverse[b], hits),
            reason_type=("同じ単位・採否の射影" if any(hit["same_projection"] for hit in hits) else
                         "単位違い" if any(scope and hit["table"] != scope for hit in hits) else
                         "コード未対応" if not (inverse[a] and inverse[b]) else
                         "包括側に同じ項目対あり・条件未照合" if frozenset((a, b)) in inclusion_pairs else
                         "特例・方向・適用単位未確認" if hits else "不明"))
    for rel in tables["frequency"]:
        rel["unit_label"] = FREQUENCY_UNITS.get(rel["unit"])
    for key, (unit, limit, clause, fn) in FREQUENCIES.items():
        hits = by_frequency[key]
        reverse[f"{clause}/{key[1]}"] = grade(
            (REPRESENTATION if key in RENAL_FREQUENCIES or key in FREQUENCY_EXCEPTIONS
             or key == ("D006-30", "retinalDystrophy") or fn == "elfSixMonthInterval" or key == ("D000", "rapidAddition") else MATCH)
            if hits else UNKNOWN, "対応コードの単位・回数で検索",
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


def compare_count_attributes(mapping, frequencies, records):
    by_code = defaultdict(list)
    for row in frequencies:
        if row["classification"] in {MATCH, REPRESENTATION}:
            by_code[row["codes"][0]].append(row)
    for code, entry in mapping.items():
        record = records[code]
        attributes = entry["attributes"]
        rows = by_code[code]
        if rows:
            evidence = {"clauses": sorted({clause for row in rows for clause in row["clauses"]}),
                        "frequency_lines": [line for row in rows
                                            for line in relation_positions("frequency", row)["lines"]]}
            if record.max_count > 0 and all(record.max_count == row["limit"] for row in rows):
                attributes["max_count"] = grade(
                    REPRESENTATION, "数値が一致。コード上限欄から通知の期間・共有範囲は読めない",
                    reason_type="回数の数値のみ対応", **evidence)
            else:
                attributes["max_count"].setdefault(
                    "reason_type", "上限なしの欄と別表の制限" if record.max_count == 0
                    else "上限欄と別表の数値の対応未確定")
        attributes["max_count"].setdefault("reason_type", "対応する頻度条項未確認")
        attributes["max_count_handling"] = grade(
            UNMODELED, "上限超過時の確認・上限回数での算定は請求時の処理",
            reason_type="Leanモデルの対象外（請求時の処理）",
            value=record.max_count_handling,
            meaning=MAX_COUNT_HANDLING[record.max_count_handling],
            **(evidence if rows else {}))


MAX_COUNT_HANDLING = {"0": "上限回数の確認", "1": "上限回数による算定"}


def count_buckets(counts):
    return [{"reason_type": reason, "special": special, "count": count}
            for (reason, special), count in counts.items()]


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
        evidence = {k: rel[k] for k in ("classification", "reason", "reason_type", "clauses") if k in rel}
        key = (evidence["classification"], evidence["reason"], evidence.get("reason_type"),
               tuple(evidence.get("clauses", ())))
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
    reviewed_names = {(r["division"], r["number"]): {
        normalized_name(name): item for name, item in r["names"].items()} for r in name_review}
    name_evidence = {(r["division"], r["number"], normalized_name(name)): proof
                     for r in name_review for name, proof in r.get("evidence", {}).items()}
    require(len(reviewed_names) == len(name_review), "名称確認の区分・項番が重複")
    notice = read_index("notice-impact.json")
    require(notice["as_of"] == DAY.isoformat(), "準用索引の基準日が異なる")
    references = {r["master"]["診療行為コード"]: r for r in notice["references"]}
    notice_pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
    notice_blocks = notice_spans(notice_pages, read_index("notice-index.json"), "paragraph")
    revisions = read_index("notice-revisions.json")
    require(revisions["as_of"] == DAY.isoformat(), "改正索引の基準日が異なる")
    amendment_hits = defaultdict(list)
    searched_amendments = set()
    for amendment in revisions["amendments"]:
        source = amendment["source"]
        filename = source["path"].rsplit("/", 1)[-1]
        pages = verified_pdf_pages(NOTICE_PDF.parent / "amendments" / filename,
                                   R08_DOWNLOADS["amendments"][filename])
        searched_amendments.add(filename)
        for change in amendment["changes"]:
            division, page = change["code"], change["page"]
            amendment_hits[division].append((
                compact(pages[page - 1]), {"document": filename, "pdf_page": page,
                                          "paragraph": change["paragraph"],
                                          "applies_on_as_of": change["applies_on_as_of"]}))
    require(searched_amendments == set(R08_DOWNLOADS["amendments"]), "登録改正と索引の資料が異なる")
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
        wording_candidates = []
        origin_status = None
        if record.ref_division and (not item or method == "名称による"):
            key_name = compact(record.name)
            wording_candidates = reference_candidates(record, notice_blocks, divisions)
            name_candidates = [{"clause": f"notice/{d}/paragraph/{n}", "pdf_pages": [start, end]}
                               for (d, n), blocks in notice_blocks.items()
                               if d in {record.division, record.ref_division}
                               for start, end, body in blocks
                               if len(key_name) >= 3 and key_name in body]
        amendment_candidates = []
        if record.ref_division and (not item or method == "名称による"):
            amendment_candidates = [evidence for division in {record.division, record.ref_division}
                                    for body, evidence in amendment_hits[division]
                                    if len(key_name) >= 3 and key_name in body]
            if not item:
                origin_status = {
                    "baseline_item_candidate": "登録通知の項候補・個別条件未照合",
                    "amendment_item": "改正の項候補・適用日と個別条件未照合",
                }.get((references.get(code) or {}).get("status"),
                      "由来未確定・索引外資料や過去の改廃を要確認")
                if any(candidate["exact_name"] for candidate in wording_candidates):
                    origin_status = "登録通知の名称候補・準用関係未確認"
        evidence = name_evidence.get((record.division, record.item, normalized_name(record.name)))
        rate = reference_rate_projection(record, by_key, evidence)
        mapping[code] = {
            "master": master, "archive_line": archive_lines[code], "index_line": index_line,
            "lean": item, "method": method, "candidates": candidates,
            "reason_type": None if item else code_reason(record, candidates, method),
            "name_evidence": evidence if method == "名称による" or rate else None,
            "reference_rate_projection": rate,
            "many_to_one": bool(item and evidence and evidence.get("projection") == "多対一"),
            "amendment_name_candidates": amendment_candidates,
            "reference_review_status": ((evidence or {}).get("reference_status",
                                        "対象行の通知段落確認・準用先の項番表記差あり")
                                       if method == "名称による" and record.ref_division else None),
            "source_candidates": clauses, "reference_search": references.get(code),
            "notice_exact_name_candidates": name_candidates,
            "notice_reference_candidates": wording_candidates,
            "reference_origin_status": origin_status,
            "master_extra": {"addition_key": record.addition_key, "facility_codes": record.facility_codes,
                             "age_additions": record.age_additions},
            "attributes": compare_attributes(record, item, method, clauses, by_key,
                                             records_by_code, archive_lines),
        }

    snapshot = registered_snapshot(set(mapping))
    tables, inclusion_lines = table_rows(snapshot, set(mapping))
    locations = {r.code: (r.chapter, r.part, r.division) for r in records}
    reverse = compare_tables(tables, mapping, locations)
    compare_count_attributes(mapping, tables["frequency"], records_by_code)
    parent_counts = defaultdict(Counter)
    parent_division_counts = defaultdict(Counter)
    exclusion_counts = defaultdict(Counter)
    day_counts = Counter()
    for rel in tables["inclusion"]:
        parent = rel["codes"][0]
        bucket = (rel["reason_type"], rel["special"])
        parent_counts[parent][bucket] += 1
        parent_division_counts[locations.get(parent, (None, None, None))][bucket] += 1
    for table, relations in tables.items():
        if table.startswith("exclusion_"):
            for rel in relations:
                pair = tuple(sorted(tuple(loc) if loc else (0, 0, "") for loc in rel["locations"]))
                exclusion_counts[table][pair, rel["reason_type"]] += 1
                if table == "exclusion_day":
                    day_counts[tuple(tuple(loc or (None, None, None)) for loc in rel["locations"])] += 1
    frequency_by_division = defaultdict(Counter)
    for row in tables["frequency"]:
        frequency_by_division[mapping[row["codes"][0]]["master"]["区分"]][row["reason_type"]] += 1
    unmapped_by_division = defaultdict(Counter)
    for entry in mapping.values():
        if entry["lean"] is None:
            unmapped_by_division[entry["master"]["区分"]][entry["reason_type"]] += 1
    point_sets = compare_points(points, [entry["master"] for entry in mapping.values()])
    point_differences = point_difference_evidence(point_sets, mapping, records_by_code, archive_lines)
    classifications = Counter()
    attribute_counts = defaultdict(Counter)
    for entry in mapping.values():
        for field, value in entry["attributes"].items():
            attribute_counts[field][value["classification"]] += 1
            classifications[value["classification"]] += 1
    count_attribute_reasons = {
        field: reason_counts(e["attributes"][field] for e in mapping.values())
        for field in ("max_count", "max_count_handling")
    }
    table_counts = {}
    for table, relations in tables.items():
        table_counts[table] = Counter(row["classification"] for row in relations)
        classifications.update(table_counts[table])
    classifications.update(value["classification"] for value in reverse.values())
    classifications.update(value["classification"] for value in point_differences)
    reference_status = Counter(
        entry["reference_review_status"] or ("通知・Lean対応" if entry["lean"] else (entry["reference_search"] or {}).get("status", "索引なし"))
        for entry in mapping.values() if entry["master"]["準用元区分"]
    )
    groups = group_inventory(reverse, mapping)
    summary = {
        "divisions": len(divisions), "codes": len(mapping),
        "mapped": sum(entry["lean"] is not None for entry in mapping.values()),
        "name_based": sum(entry["method"] == "名称による" for entry in mapping.values()),
        "many_to_one": sum(entry["many_to_one"] for entry in mapping.values()),
        "group_status": {kind: Counter(e["status"] for e in groups if e["kind"] == kind)
                         for kind in ("選択", "包括")},
        "max_count_handling_values": Counter(r["attributes"]["max_count_handling"]["value"]
                                            for r in mapping.values()),
        "reference_origin_status": Counter(e["reference_origin_status"] for e in mapping.values()
                                           if e["reference_origin_status"]),
        "reference_rate_projection": Counter(e["reference_rate_projection"]["item_status"]
                                             for e in mapping.values() if e["reference_rate_projection"]),
        "inclusion_source_rows": len(inclusion_lines),
        "reference_status": reference_status,
        "amendment_name_hits": sum(bool(e["amendment_name_candidates"]) for e in mapping.values()),
        "unmapped_reference_with_notice_name_hits": sum(bool(e["notice_exact_name_candidates"])
                                                        for e in mapping.values()),
        "previous_point_set_differences": Counter(r["classification"] for r in point_differences),
        "lean_to_electronic": Counter(r["classification"] for r in reverse.values()),
        "methods": Counter(entry["method"] for entry in mapping.values()),
        "count_attribute_reasons": count_attribute_reasons,
        "attributes": attribute_counts, "tables": table_counts,
        "frequency_by_division": frequency_by_division,
        "table_reason_types": {table: reason_counts(rows) for table, rows in tables.items()},
        "unmapped_by_division": unmapped_by_division,
        "unmapped_reason_types": sum(unmapped_by_division.values(), Counter()),
        "reverse_reason_types": reason_counts(reverse.values()),
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
        "group_inventory": groups,
        "day_locations": [{"pair": pair, "count": count} for pair, count in day_counts.most_common()],
        "exclusions_by_division_pair": {
            table: [{"pair": pair, "reason_type": reason, "count": count}
                    for (pair, reason), count in counts.most_common()]
            for table, counts in exclusion_counts.items()
        },
        "inclusion_parents": {code: {"location": locations.get(code), "counts": count_buckets(counts)}
                              for code, counts in parent_counts.items()},
        "inclusion_parent_divisions": [{"location": location, "counts": count_buckets(counts)}
                                       for location, counts in parent_division_counts.items()],
        "reference_search_scope": {"baseline": "当該区分と準用元区分の登録通知段落",
                                   "wording_candidates": "対象区分の索引済み通知全段落・名称又は準用元項",
                                   "amendments": sorted(R08_DOWNLOADS["amendments"]),
                                   "amendment_scope": "改正索引で区分を同定した指示頁の完全名称候補",
                                   "limits": "行をまたぐ名称・略称・未索引箇所は要確認"},
        "three_combination_reviews": combination_reviews(reverse, tables, mapping),
    }
    report["electronic_to_lean"]["inclusion"] = pack_inclusion(tables["inclusion"])
    path = INVENTORY / "specimen-external-audit.json"
    _write(path, json.dumps(report, ensure_ascii=False, separators=(",", ":")) + "\n")
    print(path)
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

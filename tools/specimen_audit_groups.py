"""外来検体検査の棚卸しで接続・部分接続した群の索引。"""

from collections import defaultdict
from itertools import product


# 複数段落による一群は主条項で識別する。
SELECTION_GROUPS = {
    "D001": "3 4/i 6/i 9/i",
    "D002": "5",
    "D003": "4/u",
    "D004": "1 13/i",
    "D004-2": "7 8 9 10 11",
    "D005": "3 7 9",
    "D006": "8/i",
    "D006-15": "3",
    "D006-22": "3",
    "D006-24": "2",
    "D007": "2 3 5 7 9 12 15 17/e 18 21 22 23/i 26 27 30 38 40/i 41/i 42/i 43/u",
    "D008": "3 4 6/i 7/i 13 15 16 18 19 25 26/i",
    "D009": "3 5 8 10/i 15 20/u 21/u 21/e 24/i",
    "D011": "4/u",
    "D012": "2 4 23 28 31/i 38/i 43/i 48/e 56",
    "D013": "5 6 8",
    "D014": "8 12",
    "D015": "4/i 11/i",
    "D018": "1/u 1/e",
    "D023": "16/u 36/i 37/u 37/e 39/i",
    "D023-2": "1/i 4/i",
}

BUNDLE_GROUPS = {
    "D004-2": ("item/1/note/1", "item/1/note/2"),
    "D006": ("note/unnumbered/1",),
    "D006-4": ("note/2",),
    "D006-27": ("note/1", "note/2"),
    "D007": ("note/unnumbered/1",),
    "D008": ("note/unnumbered/1",),
    "D009": ("note/2",),
    "D012": ("item/11/note", "item/46/note"),
    "D013": ("note/unnumbered/1",),
    "D014": ("note/1",),
    "D015": ("item/13/note",),
    "D016": ("item/2", "item/4", "item/5"),
    "D019": ("heading",),
    "D021": ("heading",),
}

SELECTION_IDS = [
    f"notice/{division}/paragraph/{paragraph}"
    for division, paragraphs in SELECTION_GROUPS.items()
    for paragraph in paragraphs.split()
] + ["primary/D006-4/note/2", "primary/D017/note/unnumbered/1",
     "notice/ch2-part3-section4/general/3"]

BUNDLE_IDS = [
    f"primary/{division}/{path}"
    for division, paths in BUNDLE_GROUPS.items() for path in paths
] + ["notice/D011/paragraph/1", "notice/D017/paragraph/2", "notice/D020/paragraph/1"]


# 項目数別の包括額とは別に、実施方法・菌種・一連の集約を検索する範囲。
METHOD_BUNDLES = {
    "primary/D016/item/2": {2},
    "primary/D016/item/4": {4},
    "primary/D016/item/5": {5},
    "primary/D019/heading": {1, 2, 3},
    "primary/D021/heading": {0},
    "notice/D011/paragraph/1": {3},
    "notice/D017/paragraph/2": {1, 2, 3},
    "notice/D020/paragraph/1": {1, 2},
}

# CHOICES の対が対象群の一部の経路に限られるもの。
PARTIAL_SCOPE = {
    "notice/D001/paragraph/6/i", "notice/D004-2/paragraph/7", "notice/D005/paragraph/3",
    "notice/D008/paragraph/15", "notice/D008/paragraph/16", "notice/D012/paragraph/28",
    "notice/D001/paragraph/4/i", "notice/D004-2/paragraph/8", "notice/D004-2/paragraph/9",
    "notice/D006-22/paragraph/3", "notice/D006-24/paragraph/2",
    "notice/D009/paragraph/5", "notice/D009/paragraph/10/i", "notice/D009/paragraph/20/u",
    "notice/D009/paragraph/21/u", "notice/D009/paragraph/21/e",
    "notice/D018/paragraph/1/u", "notice/D018/paragraph/1/e",
    "notice/D012/paragraph/43/i", "notice/D007/paragraph/26",
    "notice/D004-2/paragraph/11", "notice/D007/paragraph/17/e",
}


def pair_presence(expected, observed):
    """項目対又はコード対の収載を数える。収載行の適用条件はここでは判定しない。"""
    missing = expected - observed
    status = ("比較対象なし" if not expected else "全対あり" if not missing else
              "全対なし" if missing == expected else "一部のみ")
    return {"status": status, "expected": len(expected), "missing": len(missing)}


def group_pair_presence(group_pairs, inverse, tables):
    by_pair = defaultdict(list)
    codes = set().union(*inverse.values())
    for table, rows in tables.items():
        if table != "inclusion" and not table.startswith("exclusion_"):
            continue
        for row in rows:
            if not all(code in codes for code in row["codes"]):
                continue
            by_pair[tuple(sorted(row["codes"]))].append({
                "table": table, "codes": row["codes"], "special": row["special"],
                **({"unit": row["unit"], "child_line": row["line"],
                    "parent_line": row["auxiliary_line"],
                    "parent_column": row.get("auxiliary_column")} if table == "inclusion" else
                   {"direction": row["direction"], "lines": [r["line"] for r in row["rows"]]}),
            })
    result = {}
    for group in sorted(set(SELECTION_IDS) | group_pairs.keys()):
        pairs = sorted(group_pairs.get(group, ()))
        item_rows, observed_items, missing_items = [], set(), set()
        code_pairs, observed_codes = set(), set()
        for a, b in pairs:
            missing_items.update(item for item in (a, b) if not inverse.get(item))
            expected = {tuple(sorted((x, y))) for x, y in product(inverse.get(a, ()), inverse.get(b, ()))
                        if x != y}
            observed = {pair for pair in expected if pair in by_pair}
            if observed:
                observed_items.add((a, b))
            code_pairs.update(expected)
            observed_codes.update(observed)
            item_rows.append({
                "items": (a, b), "code_pairs": pair_presence(expected, observed),
                "missing_code_pairs": sorted(expected - observed),
                "rows": [row for pair in sorted(observed) for row in by_pair[pair]],
            })
        result[group] = {
            "scope": ("対の定義なし" if not pairs else "構成項目のコード未対応" if missing_items
                      else "限定した対の射影" if group in PARTIAL_SCOPE else "登録済みの対"),
            "unmapped_items": sorted(missing_items),
            "item_pairs": pair_presence(set(pairs), observed_items),
            "code_pairs": pair_presence(code_pairs, observed_codes),
            "pairs": item_rows,
        }
    return result


def choice_review(pairs, partial_scope):
    if not pairs:
        return {"status": "未判定", "reason_type": "構成項目・関係の個別照合待ち",
                "representation": [], "mapping_sizes_by_pair": None}
    sizes = [p["mapping_sizes"] for p in pairs]
    rows = [r for p in pairs for r in p["electronic_rows"]]
    inclusions = [r for p in pairs for r in p.get("inclusion_rows", [])]
    reasons = {p["reason_type"] for p in pairs}
    counts = [p["coverage"] for p in pairs]
    expected = sum(c["expected"] for c in counts)
    matching = sum(c["matching"] for c in counts)
    if any(not all(size) for size in sizes):
        status, reason = "未判定", "コード未対応"
    elif expected and matching == expected and not partial_scope:
        status, reason = "全対一致", "同じ方向・単位の背反"
    elif matching:
        status, reason = "一部のみ", "一致対あり・他の対又は適用範囲が残る"
    elif "単位違い" in reasons:
        status, reason = "未判定", "単位違い"
    elif any(not r.get("same_direction", r["direction"] == "3") for r in rows):
        status, reason = "未判定", "優先方向の対応未確認"
    elif reasons == {"不明"}:
        status, reason = "未判定", "表での表現が不明"
    else:
        status, reason = "未判定", "特例・適用単位未確認"
    return {"status": status, "reason_type": reason,
            "representation": (["背反"] if rows else []) + (["包括"] if inclusions else []),
            "pairs_with_inclusion": sum(bool(p.get("inclusion_rows")) for p in pairs),
            "mapping_sizes_by_pair": sizes, "expected_pairs": expected, "matching_pairs": matching,
            "symmetric_simultaneous_pairs": sum(
                any(r["table"] == "exclusion_simultaneous" and r["direction"] == "3" and not r["special"]
                    for r in p["electronic_rows"]) for p in pairs),
            "pairs_with_any_row": sum(bool(p["electronic_rows"]) for p in pairs)}


def group_inventory(reverse, mapping, bundle_reviews):
    reverse_pairs = {}
    for row in reverse.values():
        if "coverage" in row:
            reverse_pairs.setdefault(row["clauses"][0], []).append(row)
    result = []
    for group in SELECTION_IDS:
        review = choice_review(reverse_pairs.get(group, ()), group in PARTIAL_SCOPE)
        if group == "notice/D015/paragraph/4/i" and (
                review.get("pairs_with_any_row") == 1 and review.get("expected_pairs") == 3
                and review.get("symmetric_simultaneous_pairs") == 1
                and review["reason_type"] == "単位違い"):
            review.update(status="一部のみ", reason_type="同一検体かつ同時に限定した一対")
        result.append({"id": group, "division": group.split("/")[1], "kind": "選択",
                       **review})
    for group in BUNDLE_IDS:
        entry = reverse.get(f"{group}/membership", {})
        mapped = entry.get("mapped_members")
        seen = entry.get("master_members")
        row = {"id": group, "division": group.split("/")[1], "kind": "包括",
               "mapped_members": mapped, "master_members": seen,
               "status": "所属の部分照合" if seen else "未判定",
               "reason_type": "適用単位・群の完全性は未確認" if seen else "構成項目・関係の個別照合待ち",
               "representation": ["包括"] if seen else []}
        if group in METHOD_BUNDLES:
            direct = bundle_reviews[group]
            observed = direct["electronic_rows"]
            row.update(
                status="実施単位の関連を検索",
                reason_type=("関連行あり・集約条件未照合" if observed else
                             "方法・菌種・一連の集約に対応する関係を未同定"),
                representation=sorted(observed), direct_review=direct)
        elif direct := bundle_reviews.get(group):
            membership = direct["membership"]
            unresolved = direct["unmapped_lean_items"] or membership["master_only_unresolved"]
            differs = membership["lean_only"] or membership["master_only_mapped"]
            reason = ("所属差候補・適用条件未確認" if differs else
                      "未対応項目の所属未確認" if unresolved else "対応項目の所属一致・包括額未同定")
            row.update(status="所属の双方向照合", reason_type=reason, representation=["包括対象検査欄"],
                       mapped_members=len(membership["both"]) + len(membership["lean_only"]),
                       master_members=sum(len(codes) for k, codes in membership.items() if k != "lean_only"),
                       direct_review=direct)
        if group == "primary/D006-4/note/2":
            matched = sum((entry.get("name_evidence") or {}).get("clause") == group
                          and entry["lean"] is not None for entry in mapping.values())
            if matched:
                row.update(mapped_members=matched, status="包括額の部分照合",
                           reason_type="所定点数欄の包括額・施設と一採取の条件は別",
                           representation=["包括額（マスター）"])
        result.append(row)
    return result


def reviewed_partial_scopes(presence):
    """限定した二群について、通知上の対象と五表の収載を対応付ける。"""
    tumor = "notice/D004-2/paragraph/7"
    pf4 = "notice/D011/paragraph/4/u"
    if tumor not in presence or pf4 not in presence:
        return {}
    tumor_scope = {("D004-2", "drugAid"), ("D004-2", "complex")}
    peers = {("D006-2", "hematopoieticTumorGene"), ("D006-6", "immuneRearrangement"),
             ("D006-14", "flt3"), ("D006-16", "jak2")}
    pairs = set()
    for row in presence[tumor]["pairs"]:
        items = set(map(tuple, row["items"]))
        if items & tumor_scope and items & peers:
            pairs.update(map(tuple, row["missing_code_pairs"]))
    tumor_complete = len(pairs) == presence[tumor]["code_pairs"]["missing"] == 12
    pf4_complete = presence[pf4]["code_pairs"] == {"status": "一部のみ", "expected": 3, "missing": 2}
    return {
        tumor: {"classification": "資料間の不一致の疑い" if tumor_complete else "情報不足で判定できない",
                "reason_type": "通知の同月併施対象内・五表で関連行なし" if tumor_complete else
                               "原本レビューの分母と現在の収載が異なる",
                "pdf_pages": [335, 336, 337], "primary_pdf_pages": [175],
                "synopsis": "各実施の適格性と同一患者の同一暦月を確認した範囲。通知(7)は第1項全体を参照。",
                "missing_code_pairs": sorted(pairs) if tumor_complete else [],
                "lean_definition": "D004Tumor.hematologicRule"},
        pf4: {"classification": "表現の差" if pf4_complete else "情報不足で判定できない",
              "reason_type": "三方式の一連と二件の同時背反の非包含" if pf4_complete else
                             "原本レビューの分母と現在の収載が異なる",
              "pdf_pages": [369, 370], "primary_pdf_pages": [184],
              "synopsis": "欠落二対を含む三方式が一連の発動範囲。二方式だけで発動する独立した背反は導かれない。",
              "missing_code_pairs": [pair for r in presence[pf4]["pairs"] for pair in r["missing_code_pairs"]]
                                    if pf4_complete else [],
              "lean_definition": "Pf4Tables.notice_selection_iff"},
    }

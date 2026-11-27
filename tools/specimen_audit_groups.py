"""外来検体検査の棚卸しで接続・部分接続した群の索引。"""

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

# CHOICES の対が対象群の一部の経路に限られるもの。
PARTIAL_SCOPE = {
    "notice/D001/paragraph/6/i", "notice/D004-2/paragraph/7", "notice/D005/paragraph/3",
    "notice/D008/paragraph/15", "notice/D008/paragraph/16", "notice/D012/paragraph/28",
}


def choice_review(pairs, partial_scope):
    if not pairs:
        return {"status": "未判定", "reason_type": "構成項目・関係の個別照合待ち",
                "representation": [], "mapping_sizes_by_pair": None}
    sizes = [p["mapping_sizes"] for p in pairs]
    rows = [r for p in pairs for r in p["electronic_rows"]]
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
        status, reason = "表現の差", "単位違い"
    elif any(r["direction"] != "3" for r in rows):
        status, reason = "未判定", "優先方向の対応未確認"
    elif reasons == {"不明"}:
        status, reason = "未判定", "表での表現が不明"
    else:
        status, reason = "未判定", "特例・適用単位未確認"
    return {"status": status, "reason_type": reason,
            "representation": ["背反"] if rows else [],
            "mapping_sizes_by_pair": sizes, "expected_pairs": expected, "matching_pairs": matching,
            "symmetric_simultaneous_pairs": sum(
                any(r["table"] == "exclusion_simultaneous" and r["direction"] == "3" and not r["special"]
                    for r in p["electronic_rows"]) for p in pairs),
            "pairs_with_any_row": sum(bool(p["electronic_rows"]) for p in pairs)}


def group_inventory(reverse, mapping):
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
        if group == "primary/D006-4/note/2":
            matched = sum((entry.get("name_evidence") or {}).get("clause") == group
                          and entry["lean"] is not None for entry in mapping.values())
            if matched:
                row.update(mapped_members=matched, status="包括額の部分照合",
                           reason_type="所定点数欄の包括額・施設と一採取の条件は別",
                           representation=["包括額（マスター）"])
        result.append(row)
    return result

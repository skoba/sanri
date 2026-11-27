"""登録版の通知索引に適用日の確定した改正指示を対応付ける。"""

from collections import Counter
import json
import re

from .pdf_sources import LOCAL, NOTICE_SOURCE, R08_AS_OF, require_source

SPECIMEN = re.compile(r"D(?:00\d|01\d|02[0-7]|4\d\d)(?:-\d+)?\Z")
PARAGRAPH = re.compile(r"\((\d+)\)(.*)\Z")

# キーは訂正資料の物理頁・抽出行、値は登録通知の物理頁。
# 挿入（下線）と取消（取消線）を画像で確認し、訂正後の記載を登録版と比較した。
CORRECTION_REVIEW = {
    ("2026-04-02", 3, 35): {
        "baseline_reviewed_page": 329, "reviewed_pdf_pages": [3, 4],
        "scope": "specimen_general", "locator": "第2章第3部通則18",
        "visual_edits": ["insert", "delete"],
    },
    ("2026-04-02", 4, 19): {
        "baseline_reviewed_page": 402, "reviewed_pdf_pages": [4],
        "related_codes": ["D004-3"], "locator": "D026(6)", "visual_edits": ["insert"],
    },
    ("2026-05-01", 7, 29): {
        "baseline_reviewed_page": 330, "reviewed_pdf_pages": [7],
        "related_codes": ["D006", "D007", "D008", "D009"],
        "locator": "第2章第3部第1節第1款 外来迅速検体検査加算(2)例", "visual_edits": ["insert"],
    },
    ("2026-05-01", 7, 43): {
        "baseline_reviewed_page": 377, "reviewed_pdf_pages": [7, 8],
        "locator": "D012(52)", "visual_edits": ["insert"],
    },
    ("2026-05-29", 2, 18): {
        "baseline_reviewed_page": 14, "reviewed_pdf_pages": [2],
        "locator": "A001(8)ア", "visual_edits": ["insert", "delete"],
    },
    ("2026-10-07", 2, 18): {
        "baseline_reviewed_page": 413, "reviewed_pdf_pages": [2],
        "locator": "D218", "visual_edits": ["insert", "delete"],
    },
}

# 訂正箇所を含まない階層見出し。
SPECIMEN_HEADINGS = {
    ("2026-04-02", 4, 17), ("2026-04-02", 4, 18),
    ("2026-05-01", 7, 27), ("2026-05-01", 7, 28),
}


def correction_key(row: dict) -> tuple:
    return row["issued_on"], row["page"], row["line"]


def reviewed_correction(row: dict) -> dict:
    if row.get("visual_review"):
        return row
    key = correction_key(row)
    if key in SPECIMEN_HEADINGS and not any(row["evidence"]):
        return {**row, "incorporation": "heading_only", "visual_review": True,
                "basis": "同頁画像で訂正箇所を含まない階層見出しと確認"}
    if review := CORRECTION_REVIEW.get(key):
        return {**row, **review, "incorporation": "present", "confidence": "high",
                "visual_review": True, "applies_on_as_of": True,
                "underlying_notice_effective_from": "2026-06-01",
                "indexed_incorporation": row["incorporation"],
                "basis": "訂正PDFの挿入・取消を画像で区別し、登録版の該当箇所で反映を確認"}
    return row


def specimen_corrections(report: dict) -> dict:
    locations = [reviewed_correction(row) for document in report["corrections"]
                 for row in document["locations"] if row["attachment"] == "1"]
    relevant = [row for row in locations if SPECIMEN.fullmatch(row["code"] or "")
                or row.get("scope") == "specimen_general"
                or any(SPECIMEN.fullmatch(code) for code in row.get("related_codes", []))
                or correction_key(row) in SPECIMEN_HEADINGS
                or row.get("specimen_scope_candidate") and any(row["evidence"])]
    return {
        "confirmed": [row for row in relevant if row.get("visual_review")
                      and row["incorporation"] == "present"],
        "heading_only": [row for row in relevant if row["incorporation"] == "heading_only"],
        "unresolved": [row for row in relevant if not row.get("visual_review")],
    }


def load_revisions() -> dict | None:
    path = LOCAL / "inventory/notice-revisions.json"
    if path.resolve() != path:
        raise ValueError("改正・訂正索引のパスにシンボリックリンクがあります")
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    require_source(report["baseline"], NOTICE_SOURCE)
    if report["as_of"] != R08_AS_OF:
        raise ValueError("改正・訂正索引の基準日が異なります")
    return report


def revisions_for(code: str, report: dict | None) -> dict:
    result = {"as_of": R08_AS_OF, "amendments": [], "future_amendments": [], "corrections": []}
    if report is None:
        return {**result, "status": "index_missing", "message": "改正・訂正索引なし（tools.r08_inventory で生成）"}
    for document in report["amendments"]:
        if document["superseded"]:
            continue
        for row in document["changes"]:
            if row["code"] == code and row["target_attachment"] == 1:
                key = "amendments" if row["applies_on_as_of"] else "future_amendments"
                result[key].append({**row, "source": document["source"]})
    for document in report["corrections"]:
        for row in document["locations"]:
            if row["attachment"] != "1":
                continue
            row = reviewed_correction(row)
            if (row["code"] == code or code in row.get("related_codes", [])
                    or row.get("scope") == "specimen_general" and SPECIMEN.fullmatch(code)):
                result["corrections"].append({
                    "applies_on_as_of": None, **row, "source": document["source"],
                })
    for key in ("amendments", "future_amendments"):
        result[key].sort(key=lambda row: (row["effective_from"], row["issued_on"], row["directive"]))
    if any(result[key] for key in ("amendments", "future_amendments", "corrections")):
        return {**result, "status": "found", "message": "改正・訂正の該当箇所あり"}
    return {**result, "status": "not_found", "message": "取得済み資料の範囲では該当なし"}


def apply_amendments(paragraphs: list[dict], changes: list[dict]) -> tuple[list[dict], list[dict]]:
    """登録位置と改正差分を持つ段落を返す。対応が曖昧な指示は要確認に残す。"""
    rows = [{**p, "status": "baseline", "amendments": []} for p in paragraphs]
    unresolved = []
    for change in changes:
        if change["incorporation"] == "present":
            # 登録版の索引がすでに内容を含む。
            pass
        elif not apply_directive(rows, change):
            unresolved.append(change)
    return rows, unresolved


def apply_directive(rows: list[dict], change: dict) -> bool:
    if change["incorporation"] != "absent":
        return False
    anchor = PARAGRAPH.fullmatch(change["anchor"] or "")
    operation = change["operation"]
    active = [row for row in rows if row["status"] != "deleted"]
    if not anchor:
        replacements = change.get("replacement_paragraphs", [])
        if change["anchor"] != "" or operation != "change" or not replacements:
            return False
        # 区分全体の差替え。登録段落と同じ番号、又は本文が同じ無番号段落を引き継ぐ。
        prior = {row["number"]: row for row in active}
        if len(prior) != len(active):
            return False
        next_rows = []
        for replacement in replacements:
            number = replacement["number"]
            previous = prior.pop(number, None)
            if replacement.get("replaces_unnumbered") and previous is None:
                previous = prior.pop(None, None)
            next_rows.append({
                **(previous or {"start": None, "end": None}), "number": number,
                "status": "amended" if previous else "added", "children": [],
                "replacement": replacement["evidence"],
                "amendments": [*(previous or {}).get("amendments", []), change],
            })
        rows[:] = [row for row in rows if row["status"] == "deleted"] + next_rows + [
            {**row, "status": "deleted", "amendments": [*row["amendments"], change]}
            for row in prior.values()
        ]
        return True

    matches = [row for row in active if row["number"] == int(anchor[1])]
    if len(matches) != 1:
        return False
    row = matches[0]
    if operation == "add" and not anchor[2]:
        number = change["paragraph"]
        if number is None or any(p["number"] == number for p in active):
            return False
        rows.insert(rows.index(row) + 1, {
            "number": number, "status": "added", "start": None, "end": None,
            "children": [], "replacement": change["evidence"], "amendments": [change],
        })
    else:
        if operation not in {"add", "change", "delete"}:
            return False
        row["amendments"].append(change)
        if anchor[2]:
            # 親段落の登録位置を保存し、枝の操作順・位置と本文を差分として保持する。
            if row["status"] != "added":
                row["status"] = "amended"
        elif operation == "delete":
            row["status"] = "deleted"
        elif operation == "change":
            row.update(status="added" if row["status"] == "added" else "amended",
                       replacement=change["evidence"], children=[])
        else:
            return False
    return True


def amendment_counts(rows: list[dict]) -> dict:
    changed = {"amended", "added", "deleted"}
    counts = Counter(p["status"] for row in rows for p in row["notice_paragraph_records"])
    return {**{status: counts[status] for status in ("baseline", "amended", "added", "deleted")},
            "divisions": sum(any(p["status"] in changed for p in row["notice_paragraph_records"])
                             for row in rows)}


def effective_paragraph_records(paragraph: dict, pages: list[str]) -> list[dict] | None:
    """改正済み段落の抽出行を出典別に保持する。枝は登録版の物理位置で操作する。"""
    if paragraph["status"] == "deleted":
        return []
    records = []
    if paragraph["start"] and "replacement" not in paragraph:
        start, end = paragraph["start"], paragraph["end"]
        for number in range(start["page"], end["page"] + 1):
            first = start["line"] if number == start["page"] else 1
            last = end["line"] if number == end["page"] else None
            for line, text in enumerate(pages[number - 1].splitlines()[first - 1:last], first):
                if text.strip() and not re.fullmatch(r"\s*-\s*\d+\s*-\s*", text):
                    records.append({"page": number, "line": line, "text": text, "source": "baseline"})
    for change in paragraph["amendments"]:
        replacements = change.get("replacement_paragraphs")
        if replacements:
            new = next((p for p in replacements if p["number"] == paragraph["number"]), None)
            extracted = new["records"] if new else []
        else:
            extracted = change.get("records", [])
        new_records = [{**row, "source": change["document"]} for row in extracted]
        anchor = PARAGRAPH.fullmatch(change["anchor"] or "")
        if not anchor or not anchor[2]:
            if not new_records:
                return None
            records = new_records
            continue
        span = change.get("baseline_branch_span")
        if not span or (change["operation"] != "delete" and not new_records):
            return None
        page, first, last = span
        positions = [i for i, row in enumerate(records)
                     if row["source"] == "baseline" and row["page"] == page and first <= row["line"] <= last]
        if not positions or records[positions[0]]["line"] != first or records[positions[-1]]["line"] != last:
            return None
        start, end = positions[0], positions[-1] + 1
        if change["operation"] == "add":
            start = end
        records[start:end] = new_records
    return records

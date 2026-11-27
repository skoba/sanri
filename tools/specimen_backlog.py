"""通知参照を照合し、検体検査・検体採取の条項別の残作業を出力する。"""

from collections import Counter, defaultdict
import re

from .fee_coverage import clause_paths
from .fee_inventory import normalized, write_local
from .notice_inventory import KANA
from .fee_ledger import load_lean, read_index
from .local_pdf import verified_pdf_pages
from .notice_revisions import (amendment_counts, apply_amendments, effective_paragraph_records,
                               load_revisions, revisions_for, specimen_corrections)
from .pdf_sources import NOTICE_PDF, NOTICE_SOURCE, PRIMARY_SOURCE, R08_AS_OF, require_source


def matches_replacement(paragraph: dict, rules: list[dict]) -> bool:
    """枝差分を除き、確認済みの段落差替え・新設と同じ改正文書を指すかを調べる。"""
    if "replacement" not in paragraph or not paragraph.get("effective_records"):
        return False
    change = paragraph["amendments"][-1]
    url = change.get("source", {}).get("url")
    effective_from = change.get("effective_from")
    if not all(row["source"] == change["document"] for row in paragraph["effective_records"]):
        return False
    return bool(url and effective_from and any(
        rule.get("url") == url
        and rule.get("edition") == f"{effective_from}適用"
        and rule.get("verification") == "checkedAgainstSource"
        for rule in rules
    ))


def amendment_branch_matches(paragraph: dict, identifier: str, rules_by_path: dict) -> set[str]:
    """照合済み改正行の枝を、同じ文書・適用日を指すLean規則に対応付ける。"""
    matches = set()
    for change in paragraph["amendments"]:
        source = change.get("source", {})
        url, date = source.get("url"), change.get("effective_from")
        if not url or not date:
            continue
        nested = re.fullmatch(r"\(\d+\)([ァ-ヶ])(\d+)", change.get("anchor") or "")
        change_positions = {(row["page"], row["line"]) for row in change.get("records", [])}
        for row in paragraph.get("effective_records") or []:
            if row["source"] != change["document"]:
                continue
            # 差分は同じ文書内で別の指示もあり得るため、当該指示の行だけを対象にする。
            if "replacement" not in paragraph and (row["page"], row["line"]) not in change_positions:
                continue
            raw = normalized(row["text"].lstrip())
            marker = re.match(r"([ァ-ヶ])\s+", raw)
            ordinal = re.match(r"([1-9][0-9]*)\s+", raw)
            if marker and marker[1] in KANA:
                path = f"{identifier}/{KANA[marker[1]]}"
            elif nested and ordinal and nested[1] in KANA:
                path = f"{identifier}/{KANA[nested[1]]}/{ordinal[1]}"
            else:
                continue
            if any(rule.get("url") == url and rule.get("edition") == f"{date}適用"
                   and rule.get("verification") == "checkedAgainstSource"
                   for rule in rules_by_path.get(path, [])):
                matches.add(path)
    return matches


def nested_notice_paths(child: dict, identifier: str, pages: list[str]) -> list[str]:
    """登録版のカナ枝内にある括弧付きカナと丸数字を位置範囲内で照合する。"""
    nested_kana = {**KANA, "ロ": "ro", "リ": "ri", "ル": "ru", "ヲ": "wo", "ワ": "wa", "へ": "he"}
    paths = []
    parent = identifier
    start, end = child["start"], child["end"]
    for page in range(start["page"], end["page"] + 1):
        for line, raw in enumerate(pages[page - 1].splitlines(), 1):
            if (page, line) <= (start["page"], start["line"]) or (page, line) > (end["page"], end["line"]):
                continue
            label = raw.lstrip()
            kana = re.match(r"[（(]([ァ-ヶへ])[）)]\s+", label)
            ordinal = re.match(r"([①-⑳])\s+", label)
            if kana and kana[1] in nested_kana:
                parent = f"{identifier}/{nested_kana[kana[1]]}"
                paths.append(parent)
            elif ordinal:
                paths.append(f"{parent}/{ord(ordinal[1]) - ord('①') + 1}")
    return paths


def matches_nested_additions(paragraph: dict, identifier: str, rules_by_path: dict) -> bool:
    """登録版の段落と、適用済みの丸数字の追加をいずれも確認する。"""
    if "replacement" in paragraph or not paragraph.get("effective_records"):
        return False
    if not any(rule.get("verification") == "checkedAgainstSource"
               and rule.get("url") == NOTICE_SOURCE["url"]
               for rule in rules_by_path.get(identifier, [])):
        return False
    additions = paragraph["amendments"]
    expected = set()
    for change in additions:
        match = re.fullmatch(r"\(\d+\)([ァ-ヶ])\d+", change.get("anchor") or "")
        locator = change.get("new_locator") or ""
        if change["operation"] != "add" or not match or match[1] not in KANA or not locator.isdecimal():
            return False
        expected.add(f"{identifier}/{KANA[match[1]]}/{locator}")
    return len(expected) == len(additions) and bool(expected) and (
        expected == amendment_branch_matches(paragraph, identifier, rules_by_path))


def compare_clauses(fee: dict, notice: dict, rules: list[dict],
                    revisions: dict | None = None, notice_pages: list[str] | None = None
                    ) -> tuple[dict, dict]:
    rules_by_path = defaultdict(list)
    for rule in rules:
        for path in clause_paths(rule):
            rules_by_path["/".join(path)].append(rule)
    paths = {tuple(path.split("/")) for path in rules_by_path}
    expected = {"/".join(path) for path in paths if path[0] == "notice"}
    found = Counter()
    by_code = defaultdict(list)
    for block in notice["blocks"]:
        if block["kind"] == "deleted":
            continue
        for code in block["codes"]:
            by_code[block["chapter"], code].append(block)
            if block["chapter"] != (1 if code.startswith("A") else 2):
                continue
            for paragraph in block["paragraphs"]:
                number = paragraph["number"] if paragraph["number"] is not None else "unnumbered"
                identifier = f"notice/{code}/paragraph/{number}"
                found[identifier] += 1
                for child in paragraph["children"]:
                    if "id_suffix" in child:
                        child_id = f"{identifier}/{child['id_suffix']}"
                        found[child_id] += 1
                        if notice_pages is not None:
                            found.update(nested_notice_paths(child, child_id, notice_pages))

    check = {"checked": len(expected), "matched": sorted(key for key in expected if found[key] == 1),
             "missing": sorted(key for key in expected if not found[key]),
             "ambiguous": sorted(key for key in expected if found[key] > 1)}
    matches = set(check["matched"])
    rows = []
    replacement_matches = set()
    amendment_matches = set()
    for heading in fee["rows"]:
        chapter, code = heading["chapter"], heading["code"]
        if (heading["status"] != "listed" or chapter != 2 or heading["part"] != 3
                or not (heading["section"] == 1
                        or heading["section"] == 4 and code.startswith("D4"))):
            continue
        rules_here = {"/".join(path[2:]) for path in paths if path[1] == code and path[0] == "primary"}
        entries = heading["items"] + heading["notes"]
        # 枝への参照は部分対応として記録し、親の注全体の対応には数えない。
        primary_unmatched = [entry["path"] for entry in entries if entry["path"] not in rules_here]
        primary_complete = heading["item_note_paths"] is not None
        blocks = by_code[chapter, code]
        revision = revisions_for(code, revisions)
        records, unresolved = apply_amendments(
            [paragraph for block in blocks for paragraph in block["paragraphs"]], revision["amendments"])
        for paragraph in records:
            if notice_pages is not None and paragraph["status"] != "baseline":
                paragraph["effective_records"] = effective_paragraph_records(paragraph, notice_pages)
        paragraphs = [p for p in records if p["status"] != "deleted"]
        unmatched_notice = []
        for paragraph in paragraphs:
            number = paragraph["number"] if paragraph["number"] is not None else "unnumbered"
            identifier = f"notice/{code}/paragraph/{number}"
            if len(blocks) == 1 and not unresolved:
                amendment_matches.update(amendment_branch_matches(paragraph, identifier, rules_by_path))
            if paragraph["status"] == "baseline" and identifier in matches:
                continue
            if (len(blocks) == 1 and not unresolved
                    and matches_replacement(paragraph, rules_by_path.get(identifier, []))):
                replacement_matches.add(identifier)
            elif not (len(blocks) == 1 and not unresolved and identifier in matches
                      and matches_nested_additions(paragraph, identifier, rules_by_path)):
                unmatched_notice.append(paragraph)
        unchanged_numbers = {str(p["number"]) for p in paragraphs if p["status"] == "baseline"}
        matched_branches = [key for key in check["matched"] if key.startswith(f"notice/{code}/")
                            and key.count("/") == 4 and key.split("/")[3] in unchanged_numbers]
        child_count = sum(len(p["children"]) for p in paragraphs)
        revised_children = any(p["status"] != "baseline" for p in records)
        exact_primary = {entry["path"] for entry in entries} & rules_here
        primary_branches = sorted(rules_here & {
            child["path"] for note in heading["notes"] for child in note.get("children", [])
        })
        heading_matched = "heading" in rules_here
        if unresolved or any("effective_records" in p and p["effective_records"] is None for p in records):
            notice_status = "needs_review"
        elif len(blocks) > 1 or any(block["issues"] for block in blocks):
            notice_status = "needs_review"
        else:
            notice_status = "indexed" if blocks or records else "not_found"
        rows.append({
            "code": code, "section": heading["section"],
            "items": len(heading["items"]), "notes": len(heading["notes"]),
            "primary_status": "indexed" if primary_complete else "needs_review",
            "primary_matched": len(exact_primary),
            "primary_heading_matched": heading_matched,
            "source_backed_clauses": (len(exact_primary) + len(primary_branches) + int(heading_matched)
                                      + len(paragraphs) - len(unmatched_notice) + len(matched_branches)),
            "primary_unmatched": primary_unmatched,
            "primary_remaining": len(primary_unmatched) if primary_complete else None,
            "primary_branch_refs": primary_branches,
            "primary_other_refs": sorted(rules_here - exact_primary - set(primary_branches) - {"heading"}),
            "notice_status": notice_status,
            "notice_paragraph_records": records,
            "notice_amendments_unresolved": unresolved,
            "future_notice_amendments": revision["future_amendments"],
            "notice_paragraphs": len(paragraphs) if blocks or records else None,
            "notice_numbered": sum(p["number"] is not None for p in paragraphs) if blocks or records else None,
            "notice_matched": len(paragraphs) - len(unmatched_notice),
            "notice_unmatched": [{"number": p["number"], "start": p["start"], "status": p["status"]} for p in unmatched_notice],
            "notice_remaining": len(unmatched_notice) if notice_status == "indexed" else None,
            "notice_children": child_count if blocks and not revised_children else None,
            "notice_children_remaining": child_count - len(matched_branches) if notice_status == "indexed" and not revised_children else None,
            "notice_branch_refs": matched_branches,
        })

    revised_matches = replacement_matches | amendment_matches
    check["matched"] = sorted(matches | revised_matches)
    check["matched_from_amendments"] = sorted(revised_matches)
    check["missing"] = sorted(set(check["missing"]) - revised_matches)
    check["ambiguous"] = sorted(set(check["ambiguous"]) - revised_matches)

    summary = {
        "divisions": len(rows),
        "primary_incomplete": sum(row["primary_status"] != "indexed" for row in rows),
        "notice_not_found": sum(row["notice_status"] == "not_found" for row in rows),
        "notice_needs_review": sum(row["notice_status"] == "needs_review" for row in rows),
    }
    for key in ("items", "notes", "primary_matched", "primary_remaining", "notice_paragraphs",
                "notice_numbered", "notice_matched", "notice_remaining", "source_backed_clauses",
                "notice_children", "notice_children_remaining"):
        summary[key] = sum(row[key] for row in rows if row[key] is not None)
    return check, {"summary": summary, "rows": rows,
                   "revision_as_of": revisions["as_of"] if revisions is not None else None,
                   "amended_notice_summary": amendment_counts(rows) if revisions is not None else None,
                   "specimen_corrections": specimen_corrections(revisions) if revisions is not None else None}


def add_question_counts(backlog: dict, questions: dict | None) -> None:
    counts = Counter()
    if questions is not None:
        if questions["as_of"] != R08_AS_OF:
            raise ValueError("疑義解釈索引の基準日が異なります")
        for row in questions["questions"]:
            if (row["issue_relative_to_as_of"] != "after"
                    and not row["superseded_by_indexed_correction"]
                    and row["target"] and row["target"].startswith("医科")):
                counts.update(set(row["codes"]))
    for row in backlog["rows"]:
        row["clarification_questions"] = None if questions is None else counts[row["code"]]
    backlog["clarification_as_of"] = R08_AS_OF if questions is not None else None


def main() -> None:
    fee = read_index("fee-index.json")
    notice = read_index("notice-index.json")
    require_source(fee["source"], PRIMARY_SOURCE)
    require_source(notice["source"], NOTICE_SOURCE)
    require_source(notice["fee_source"], PRIMARY_SOURCE)
    if any(row["status"] == "listed" and "items" not in row for row in fee["rows"]):
        raise ValueError("本文索引を再生成してください")
    revisions = load_revisions()
    pages = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"]) if revisions is not None else None
    check, backlog = compare_clauses(fee, notice, load_lean()["rules"], revisions, pages)
    try:
        questions = read_index("clarification-index.json")
    except FileNotFoundError:
        questions = None
    add_question_counts(backlog, questions)
    sources = {"fee_source": fee["source"], "notice_source": notice["source"]}
    print(write_local({**sources, **check}, name="notice-ledger-check.json"))
    print(write_local({**sources, **backlog}, name="specimen-backlog.json"))
    print(f"通知ID {check['checked']}、未発見 {len(check['missing'])}、曖昧 {len(check['ambiguous'])}")
    print(backlog["summary"])


if __name__ == "__main__":
    main()

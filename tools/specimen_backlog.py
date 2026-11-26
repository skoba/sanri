"""通知参照を照合し、検体検査・検体採取の条項別の残作業を出力する。"""

from collections import Counter, defaultdict

from .fee_coverage import clause_paths
from .fee_inventory import write_local
from .fee_ledger import load_lean, read_index
from .pdf_sources import NOTICE_SOURCE, PRIMARY_SOURCE, require_source


def compare_clauses(fee: dict, notice: dict, rules: list[dict]) -> tuple[dict, dict]:
    paths = {path for rule in rules for path in clause_paths(rule)}
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
                if paragraph["number"] is None:
                    continue
                identifier = f"notice/{code}/paragraph/{paragraph['number']}"
                found[identifier] += 1
                for child in paragraph["children"]:
                    if "id_suffix" in child:
                        found[f"{identifier}/{child['id_suffix']}"] += 1

    check = {"checked": len(expected), "matched": sorted(key for key in expected if found[key] == 1),
             "missing": sorted(key for key in expected if not found[key]),
             "ambiguous": sorted(key for key in expected if found[key] > 1)}
    matches = set(check["matched"])
    rows = []
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
        paragraphs = [paragraph for block in blocks for paragraph in block["paragraphs"]]
        unmatched_notice = [p for p in paragraphs
                            if p["number"] is None or
                            f"notice/{code}/paragraph/{p['number']}" not in matches]
        matched_branches = [key for key in check["matched"] if key.startswith(f"notice/{code}/")
                            and key.count("/") == 4]
        child_count = sum(len(p["children"]) for p in paragraphs)
        exact_primary = {entry["path"] for entry in entries} & rules_here
        primary_branches = sorted(rules_here & {
            child["path"] for note in heading["notes"] for child in note.get("children", [])
        })
        heading_matched = "heading" in rules_here
        notice_status = "not_found" if not blocks else (
            "needs_review" if len(blocks) > 1 or any(block["issues"] for block in blocks) else "indexed"
        )
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
            "notice_paragraphs": len(paragraphs) if blocks else None,
            "notice_numbered": sum(p["number"] is not None for p in paragraphs) if blocks else None,
            "notice_matched": len(paragraphs) - len(unmatched_notice),
            "notice_unmatched": [{"number": p["number"], "start": p["start"]} for p in unmatched_notice],
            "notice_remaining": len(unmatched_notice) if notice_status == "indexed" else None,
            "notice_children": child_count if blocks else None,
            "notice_children_remaining": child_count - len(matched_branches) if notice_status == "indexed" else None,
            "notice_branch_refs": matched_branches,
        })

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
    return check, {"summary": summary, "rows": rows}


def main() -> None:
    fee = read_index("fee-index.json")
    notice = read_index("notice-index.json")
    require_source(fee["source"], PRIMARY_SOURCE)
    require_source(notice["source"], NOTICE_SOURCE)
    require_source(notice["fee_source"], PRIMARY_SOURCE)
    if any(row["status"] == "listed" and "items" not in row for row in fee["rows"]):
        raise ValueError("本文索引を再生成してください")
    check, backlog = compare_clauses(fee, notice, load_lean()["rules"])
    sources = {"fee_source": fee["source"], "notice_source": notice["source"]}
    print(write_local({**sources, **check}, name="notice-ledger-check.json"))
    print(write_local({**sources, **backlog}, name="specimen-backlog.json"))
    print(f"通知ID {check['checked']}、未発見 {len(check['missing'])}、曖昧 {len(check['ambiguous'])}")
    print(backlog["summary"])


if __name__ == "__main__":
    main()

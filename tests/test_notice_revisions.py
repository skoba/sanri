import unittest

from tools.draft_fee import revision_excerpt
from tools.notice_revisions import apply_amendments, effective_paragraph_records, revisions_for


def directive(operation, anchor, number, evidence=""):
    return {
        "operation": operation, "anchor": anchor, "paragraph": number,
        "incorporation": "absent", "evidence": evidence, "document": "sample.pdf",
        "records": [{"page": 1, "line": 2, "text": evidence}] if evidence else [],
    }


class NoticeRevisionTests(unittest.TestCase):
    def test_branch_edit_then_numbered_add_and_delete(self):
        baseline = [{"number": 1, "start": {"page": 1, "line": 1},
                     "end": {"page": 1, "line": 3}, "children": []}]
        branch = {**directive("change", "(1)イ", 1, "イ 変更後"), "baseline_branch_span": [1, 3, 3]}
        added = directive("add", "(1)", 2, "(2) 新設")
        deleted = directive("delete", "(2)", 2)
        rows, pending = apply_amendments(baseline, [branch, added, deleted])
        self.assertEqual(pending, [])
        self.assertEqual([(p["number"], p["status"]) for p in rows], [(1, "amended"), (2, "deleted")])
        records = effective_paragraph_records(rows[0], ["(1) 合成例\nア 既存\nイ 変更前"])
        self.assertEqual([(r["source"], r["text"]) for r in records],
                         [("baseline", "(1) 合成例"), ("baseline", "ア 既存"), ("sample.pdf", "イ 変更後")])
        self.assertEqual(effective_paragraph_records(rows[1], []), [])
        self.assertNotIn("status", baseline[0])

    def test_whole_division_replacement_relabels_and_adds(self):
        baseline = [{"number": None, "children": [], "start": None, "end": None}]
        change = {**directive("change", "", None), "replacement_paragraphs": [
            {"number": 1, "evidence": "(1) 合成例", "replaces_unnumbered": True, "records": [
                {"page": 2, "line": 3, "text": "(1) 合成例"},
            ]},
            {"number": 2, "evidence": "(2) 新設", "records": [{"page": 2, "line": 4, "text": "(2) 新設"}]},
        ]}
        rows, pending = apply_amendments(baseline, [change])
        self.assertEqual(pending, [])
        self.assertEqual([(p["number"], p["status"]) for p in rows], [(1, "amended"), (2, "added")])
        self.assertEqual(effective_paragraph_records(rows[1], [])[0]["text"], "(2) 新設")

    def test_unrecognized_anchor_is_left_pending(self):
        change = directive("add", "(9)ア", 9, "イ 合成例")
        self.assertEqual(apply_amendments([], [change]), ([], [change]))

    def test_revision_excerpt_excludes_superseded_and_labels_future(self):
        future = {
            **directive("add", "(1)", 2, "(2) 次回"), "code": "D800", "target_attachment": 1,
            "applies_on_as_of": False, "issued_on": "2026-10-30", "effective_from": "2026-11-01",
            "directive": 1, "page": 2, "line": 4,
        }
        report = {"amendments": [
            {"source": {}, "superseded": False, "changes": [future]},
            {"source": {}, "superseded": True, "changes": [{**future, "applies_on_as_of": True}]},
        ], "corrections": []}
        revision = revisions_for("D800", report)
        self.assertEqual(revision["amendments"], [])
        self.assertEqual(len(revision["future_amendments"]), 1)
        self.assertIn("基準日には未適用", revision_excerpt(revision))
        self.assertIn("取得済み資料の範囲では該当なし", revision_excerpt(revisions_for("D801", report)))

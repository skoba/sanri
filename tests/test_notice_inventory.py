"""架空のPDF抽出行と台帳による位置・不足・枝番号の検証。"""

import unittest

from tools.draft_fee import notice_excerpt
from tools.notice_inventory import build_notice
from tools.pdf_sources import NOTICE_SOURCE
from tools.specimen_backlog import (
    amendment_branch_matches, compare_clauses, matches_nested_additions, matches_replacement,
    nested_notice_paths,
)


class NoticeInventoryTests(unittest.TestCase):
    def test_replacement_requires_the_checked_effective_source(self):
        url = "https://example.test/replacement.pdf"
        change = {"document": "replacement.pdf", "effective_from": "2026-07-01",
                  "source": {"url": url}}
        paragraph = {"replacement": "合成段落", "amendments": [change],
                     "effective_records": [{"source": "replacement.pdf"}]}
        rule = {"url": url, "edition": "2026-07-01適用",
                "verification": "checkedAgainstSource"}
        self.assertTrue(matches_replacement(paragraph, [rule]))
        self.assertFalse(matches_replacement(paragraph, [{**rule, "url": "https://example.test/old.pdf"}]))
        self.assertFalse(matches_replacement(paragraph, [{**rule, "edition": "2026-08-01適用"}]))
        self.assertFalse(matches_replacement(paragraph, [{**rule, "verification": "transcribed"}]))
        combined = {**paragraph, "effective_records": [
            {"source": "baseline"}, {"source": "replacement.pdf"}]}
        self.assertFalse(matches_replacement(combined, [rule]))

    def test_added_branch_matches_only_the_effective_directive(self):
        url = "https://example.test/amendment.pdf"
        row = {"page": 2, "line": 5, "text": "    ３  合成枝", "source": "amendment.pdf"}
        change = {"document": "amendment.pdf", "effective_from": "2026-07-01",
                  "source": {"url": url}, "anchor": "(1)カ2", "records": [row]}
        paragraph = {"amendments": [change], "effective_records": [row]}
        rule = {"url": url, "edition": "2026-07-01適用", "verification": "checkedAgainstSource"}
        parent = "notice/D997/paragraph/1"
        path = f"{parent}/ka/3"
        self.assertEqual(amendment_branch_matches(paragraph, parent, {path: [rule]}), {path})
        self.assertEqual(amendment_branch_matches(
            {**paragraph, "effective_records": [{**row, "line": 6}]}, parent, {path: [rule]}
        ), set())
        self.assertEqual(amendment_branch_matches(
            paragraph, parent, {path: [{**rule, "edition": "2026-11-01適用"}]}
        ), set())

    def test_nested_kana_restarts_the_ordinal_scope(self):
        pages = [
            " ア  合成枝\n    (イ)  合成小枝\n      ①  合成項目\n",
            "    (ロ)  合成小枝\n      ①  合成項目\n    (ロ)の続き\n    イ  次の枝",
        ]
        child = {"start": {"page": 1, "line": 1}, "end": {"page": 2, "line": 3}}
        base = "notice/D997/paragraph/1/a"
        self.assertEqual(nested_notice_paths(child, base, pages),
                         [f"{base}/i", f"{base}/i/1", f"{base}/ro", f"{base}/ro/1"])

    def test_nested_additions_require_both_baseline_and_every_amendment(self):
        url = "https://example.test/addition.pdf"
        additions = [{"page": 2, "line": n, "text": f"    {n}  合成項目", "source": "addition.pdf"}
                     for n in (3, 4)]
        paragraph = {
            "amendments": [
                {"document": "addition.pdf", "operation": "add", "effective_from": "2026-07-01",
                 "anchor": f"(1)カ{n - 1}", "new_locator": str(n),
                 "records": [row], "source": {"url": url}}
                for n, row in zip((3, 4), additions)
            ],
            "effective_records": [{"source": "baseline"}, *additions],
        }
        base = "notice/D997/paragraph/1"
        amendment = {"url": url, "edition": "2026-07-01適用",
                     "verification": "checkedAgainstSource"}
        baseline = {"url": NOTICE_SOURCE["url"], "verification": "checkedAgainstSource"}
        rules = {base: [baseline], f"{base}/ka/3": [amendment], f"{base}/ka/4": [amendment]}
        self.assertTrue(matches_nested_additions(paragraph, base, rules))
        self.assertFalse(matches_nested_additions(paragraph, base, {**rules, base: []}))
        self.assertFalse(matches_nested_additions(paragraph, base, {**rules, f"{base}/ka/4": []}))

    def test_scope_spans_and_unresolved_references(self):
        pages = [
            "第２章  架空章\n第 ３ 部  架空部\n＜通則＞\n１  合成通則\n"
            "第１節  合成節\nＱ９００—１  不明な見出し\n"
            "Ｑ９０１  合成項目\n (１)  合成説明\n    ア  合成枝\n - 1 -\n",
            "        枝の続き\n    ウ  合成枝\n (３)  合成説明\n (３)  重複\n"
            "Ｑ９０２  合成項目\n  無番号の説明。\n別添１の２\nＱ９０１  別添の表",
        ]
        row = {"code": "Q901", "chapter": 2, "part": 3, "section": 1, "status": "listed",
               "items": [], "notes": [], "item_note_paths": []}
        fee = {"rows": [row, {**row, "code": "Q903"}]}
        notice = build_notice(pages, fee)
        first, second = notice["blocks"]
        self.assertEqual(first["start"], {"page": 1, "line": 7})
        self.assertEqual(first["paragraphs"][0]["children"][0]["end"], {"page": 2, "line": 1})
        self.assertEqual(first["issues"][0]["missing"], [2])
        self.assertEqual(first["issues"][0]["duplicates"], [3])
        self.assertEqual(first["issues"][1]["missing"], ["イ"])
        self.assertEqual(second["paragraphs"][0]["number"], None)
        self.assertEqual(second["end"], {"page": 2, "line": 6})
        self.assertEqual(notice["general"][2]["paragraphs"][0]["style"], "decimal")
        self.assertEqual(len(notice["issues"]), 1)
        self.assertEqual(notice["primary_only"], [{"chapter": 2, "code": "Q903"}])
        self.assertEqual(notice["notice_only"], [{"chapter": 2, "code": "Q902"}])

        rules = [{"id": f"notice/Q901/paragraph/{suffix}", "kind": "notification"}
                 for suffix in ("1/a", "1", "2", "3")]
        check, backlog = compare_clauses(fee, notice, rules)
        self.assertEqual(check["matched"], ["notice/Q901/paragraph/1", "notice/Q901/paragraph/1/a"])
        self.assertEqual(check["missing"], ["notice/Q901/paragraph/2"])
        self.assertEqual(check["ambiguous"], ["notice/Q901/paragraph/3"])
        self.assertIsNone(backlog["rows"][0]["notice_remaining"])
        self.assertIsNone(backlog["rows"][1]["notice_paragraphs"])

        notice["source"] = {}
        excerpt = notice_excerpt("Q901", notice, pages)
        self.assertEqual(excerpt["status"], "found")
        self.assertEqual(excerpt["blocks"][0]["records"][-1]["line"], 4)
        self.assertEqual(notice_excerpt("Q903", notice, pages)["status"], "not_found")

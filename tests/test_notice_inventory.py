"""架空のPDF抽出行と台帳による位置・不足・枝番号の検証。"""

import unittest

from tools.draft_fee import notice_excerpt
from tools.notice_inventory import build_notice
from tools.specimen_backlog import compare_clauses


class NoticeInventoryTests(unittest.TestCase):
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

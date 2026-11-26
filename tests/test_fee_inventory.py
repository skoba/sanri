import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tools.fee_inventory import build_inventory, write_local


# 独自の架空見出し。目次と本文の境界は同じ物理頁にもなり得る。
FIRST = "第１章 合成章"
PART = "第１部 合成部"
SECTION = "第１節 合成節"
THIRD = "第３章 無番号区分の合成章"
FOURTH = "第４章 続きの合成章"
TOC = [FIRST, PART, SECTION, THIRD, PART, FOURTH]


class InventoryTests(unittest.TestCase):
    def test_headings_and_scopes(self):
        pages = ["\n".join(TOC + [FIRST]), "\n".join([
            PART, SECTION, "  （合成小分類）", "通則", "１ この箇所は合成の通則。",
            "Ｑ９００－２－11 合成の区分", "    Ｑ９０９を参照する。",
            "Ｑ９０１     削除", "Ｑ９０２からＱ９０４－２まで  削除",
            "Ｑ９０５及びＱ９０７ 削除",
            THIRD, "無番号の章本文。", PART, "１ 架空の番号項", "    Ｑ９００を参照。",
            FOURTH, "１ 架空の経過項", "   Ｑ９０１に関する説明。",
        ])]
        report = build_inventory(pages)
        self.assertEqual([row["code"] for row in report["rows"]], [
            "Q900-2-11", "Q901", "Q902からQ904-2まで", "Q905及びQ907",
        ])
        self.assertEqual([row["status"] for row in report["rows"]],
                         ["listed", "deleted", "deleted_group", "deleted_group"])
        deletion = report["rows"][2]
        self.assertEqual((deletion["first_code"], deletion["last_code"]), ("Q902", "Q904-2"))
        self.assertEqual(report["rows"][0]["line"], 6)
        self.assertEqual(report["rows"][0]["page"], 2)
        self.assertEqual(report["rows"][0]["section"], 1)
        self.assertEqual(len(report["divisions"]), len(TOC))
        self.assertEqual([row["heading"] for row in report["general_rules"]], ["（合成小分類）"])
        self.assertEqual(report["general_rules"][0]["line"], 4)
        self.assertEqual([(row["chapter"], row["part"], row["section"], row["number"])
                          for row in report["noncode_rows"]], [(3, 1, None, 1), (4, None, None, 1)])

    def test_duplicate_codes_keep_distinct_locations(self):
        pages = ["\n".join([FIRST, THIRD, FIRST, "Ｑ９００ 合成項目", THIRD, "Ｑ９００ 別の合成項目"])]
        report = build_inventory(pages)
        self.assertEqual([(row["chapter"], row["code"]) for row in report["rows"]],
                         [(1, "Q900"), (3, "Q900")])

    def test_dropped_division_or_unrecognized_code_stops_inventory(self):
        with self.assertRaisesRegex(ValueError, "目次"):
            build_inventory(["\n".join([FIRST, PART, FIRST])])
        for ambiguous in ["Q900―2 合成", "  Q900 合成"]:
            with self.subTest(ambiguous=ambiguous), self.assertRaisesRegex(ValueError, "番号見出し"):
                build_inventory(["\n".join([FIRST, FIRST, ambiguous])])

    def test_clause_columns_across_pages_and_numbering_uncertainty(self):
        pages = ["\n".join([FIRST, FIRST, "Q900 合成区分",
                           "        １   架空項", "             注   項の条件"]),
                 "\n".join(["２   架空項", "注１   区分の条件", " ２   続きの注",
                            "Q901 別の区分", "        １   架空項", "        ３   飛び番号"])]
        first, second = build_inventory(pages)["rows"]
        self.assertEqual(first["item_note_paths"], ["item/1", "item/2", "item/1/note", "note/1", "note/2"])
        self.assertEqual(first["items"][1]["page"], 2)
        self.assertIsNone(second["item_note_paths"])
        self.assertEqual(second["clause_issues"][0]["kind"], "item_sequence")

    def test_local_report_can_be_regenerated(self):
        with TemporaryDirectory() as local:
            report = build_inventory(["\n".join([FIRST, FIRST, "Q900 合成"])])
            target = write_local(report, Path(local))
            self.assertEqual(json.loads(target.read_text(encoding="utf-8")), report)
            self.assertEqual(target, write_local(report, Path(local)))


if __name__ == "__main__":
    unittest.main()

"""架空の条項・点数による台帳の突合せテスト。"""

import unittest

from tools.fee_coverage import clause_paths
from tools.fee_ledger import clause_coverage, compare_points


class FeeLedgerTests(unittest.TestCase):
    def test_clause_paths_and_chapter(self):
        rule = {"id": "primary/Z001/item/2..3+primary/Z001/note/1",
                "kind": "primaryText", "module": "Sanri.Test"}
        headings = [
            {"code": "Z001", "chapter": 2, "status": "listed",
             "item_note_paths": ["item/2", "item/3", "item/4", "note/1"]},
            {"code": "Z001", "chapter": 3, "status": "listed"},
            {"code": "Z002", "chapter": 2, "status": "deleted"},
        ]
        report = clause_coverage({"rows": headings}, [rule])
        first, second = report["divisions"]
        self.assertEqual((first["item_note_matched"], first["item_note_total"]), (3, 4))
        self.assertEqual(second["status"], "未着手")
        self.assertIsNone(second["item_note_total"])
        self.assertEqual(report["divisions_with_item_note_total"], 1)
        with self.assertRaises(ValueError):
            clause_paths({**rule, "kind": "notification"})

    def test_point_groups(self):
        def lean(number, points, kind="base"):
            return {"division": "Z001", "number": number, "points": points, "kind": kind}

        def master(number, points, kind="1", ref="", usable="1"):
            return {"区分": "Z001", "項番": str(number), "新又は現点数": points,
                    "告示等識別区分1": kind, "告示等識別区分2": "1", "点数識別": "3",
                    "準用元区分": ref, "基準日に使用可能": usable}

        report = compare_points(
            [lean(1, 12), lean(2, 20), lean(3, 30), lean(1, 8, "note")],
            [master(1, "12.00"), master(1, "12"), master(2, "21"),
             master(4, "30"), master(1, "8", "7"), master(1, "99", "5", "Z001"),
             master(7, "17", usable="0")],
        )
        self.assertEqual(report["counts"], {
            "base": {"match": 1, "mismatch": 1, "lean_only": 1, "master_only": 1},
            "note": {"match": 1},
        })
        self.assertEqual(report["separate_counts"], {"master_reference": 1})

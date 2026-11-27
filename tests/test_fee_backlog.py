import unittest

from tools.fee_backlog import COLUMNS, backlog_rows, work_stage


class FeeBacklogTests(unittest.TestCase):
    def test_work_items_keep_legal_context_and_distinct_statuses(self):
        def anchor(chapter, part, line):
            return dict(chapter=chapter, part=part, section=None, subsection=None,
                        page=1, line=line, heading="合成見出し")

        inventory = {
            "rows": [
                dict(anchor(2, 3, 3), code="D026", status="listed"),
                dict(anchor(2, 3, 2), code="D025", status="listed"),
                dict(anchor(2, 10, 4), code="K999-999", status="listed"),
                dict(anchor(2, 10, 5), code="K998", status="deleted"),
                dict(anchor(2, 10, 6), code="K990からK997まで", status="deleted_group"),
            ],
            "general_rules": [anchor(2, 3, 1)],
            "divisions": [dict(anchor(3, None, 7), level="章")],
            "noncode_rows": [dict(anchor(3, 1, 8), number=1), dict(anchor(3, 2, 9), number=1),
                             dict(anchor(4, None, 10), number=1)],
        }
        rows = [dict(zip(COLUMNS, values)) for values in backlog_rows(inventory)]
        self.assertEqual([r["抽出行"] for r in rows], list(range(1, 11)))
        self.assertEqual([r["既存実装との対応"] for r in rows[1:6]],
                         ["参照のみ", "個別モデルあり", "新規", "削除表記", "削除表記"])
        self.assertEqual([r["識別子"] for r in rows[6:]],
                         ["第3章前文", "第3章第1部第1項", "第3章第2部第1項", "第4章第1項"])
        self.assertTrue(all(r["着手工程"] and r["残作業"] for r in rows))

    def test_inpatient_dependencies_and_unassigned_divisions(self):
        self.assertEqual(work_stage(1, 2), work_stage(2, 4, "E004"))
        self.assertNotEqual(work_stage(2, 4, "E004"), work_stage(2, 4, "E001"))
        with self.assertRaises(ValueError):
            work_stage(2, 15)

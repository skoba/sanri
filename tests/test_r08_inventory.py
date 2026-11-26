import unittest

from tools.r08_inventory import amendment_rows, question_index
from tools.specimen_backlog import add_question_counts


class R08InventoryTests(unittest.TestCase):
    def test_questions_keep_explicit_codes_and_ignore_cover_and_answers(self):
        source = {"path": "sample.pdf", "issued_on": "2026-10-28"}
        pages = [
            "問 9 について連絡する。",
            "(別添1)\n医科診療報酬点数表関係\n【Ｄ００１】\n問１ Ｄ００\n ２を参照。\n（答）Ｄ００３\n  問9 参考引用。\n"
            "【例】\n問２ 対象は何か。\n（答）Ｄ００４",
        ]
        first, second = question_index(pages, source)
        self.assertEqual((first["target"], first["attachment"]), ("医科", 1))
        self.assertEqual(first["codes"], ["D001", "D002"])
        self.assertEqual(first["issue_relative_to_as_of"], "after")
        self.assertEqual(second["division_status"], "区分未特定")

    def test_dpc_keeps_hyphenated_question_number(self):
        source = {"path": "sample.pdf", "issued_on": "2026-10-01"}
        rows = question_index(["表紙", "医科診療報酬点数表関係（DPC）\n問 3-2-1 Ｄ００１"], source)
        self.assertEqual((rows[0]["target"], rows[0]["number"]), ("医科（DPC）", "3-2-1"))

    def test_missing_new_paragraph_requires_known_anchor(self):
        pages = ["別添1\n1  別添1の第2章D001(1)の次に次を加える。\n (2) 合成例", "別添2"]
        source = {"path": "sample.pdf", "issued_on": "2026-06-01"}
        spans = [(1, 1, "(1)既存項目")]
        blocks = {"division": {"D001": spans}, "paragraph": {("D001", 1): spans}}
        rows, _ = amendment_rows(pages, source, 1, "2026-07-01", blocks)
        self.assertEqual(rows[0]["paragraph"], 2)
        self.assertEqual(rows[0]["incorporation"], "absent")
        blocks["paragraph"].clear()
        rows, _ = amendment_rows(pages, source, 1, "2026-07-01", blocks)
        self.assertEqual(rows[0]["incorporation"], "undetermined")

    def test_absent_index_keeps_question_count_unknown(self):
        backlog = {"rows": [{"code": "D001"}]}
        add_question_counts(backlog, None)
        self.assertIsNone(backlog["rows"][0]["clarification_questions"])

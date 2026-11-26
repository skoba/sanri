import unittest

from tools.fee_sections import SourceLine, select_section


class FeeSectionTests(unittest.TestCase):
    def test_exact_code_across_pages_with_source_positions(self):
        pages = ["Ｚ１２３  親\n区分番号Ｚ１２３－２に掲げる例。\n\nＺ１２３－２  合成例",
                 "    前頁の続き。\n    区分番号Ｚ１２４の例。\nＺ１２３－２０  別枝"]
        result = select_section(pages, "Z123-2")
        self.assertEqual(result.code, "Z123-2")
        self.assertEqual((result.start_page, result.end_page), (1, 2))
        self.assertEqual(result.lines, (
            SourceLine(1, 4, "Ｚ１２３－２  合成例"), SourceLine(2, 1, "    前頁の続き。"),
            SourceLine(2, 2, "    区分番号Ｚ１２４の例。"),
        ))

    def test_top_level_and_deleted_boundaries(self):
        for boundary in ["  第２部  次の部", " 通則", "区分", "Ｚ１２５からＺ１２９まで  削除"]:
            with self.subTest(boundary=boundary):
                lines = select_section(["Z124  例\n" + boundary + "\n後続の本文"], "Ｚ１２４").lines
                self.assertEqual([line.text for line in lines], ["Z124  例"])

    def test_next_group_caption_and_its_ruby_belong_to_next_group(self):
        lines = select_section(["Z124  第一群\n  第３節の参照。\n   ふ\n （追加検査（Ⅱ））\n"
                                "   よみ\nZ125  第二群"], "Z124").lines
        self.assertEqual([line.text for line in lines], ["Z124  第一群", "  第３節の参照。", "   ふ"])

    def test_hiragana_continuation_is_retained_as_evidence(self):
        lines = select_section(["Ｚ１２３  合成例\n  まで\nＺ１２４  続く例"], "Z123").lines
        self.assertEqual(lines[-1].text, "  まで")

    def test_unsupported_or_ambiguous_sections_raise(self):
        for pages in [
            ["Z123-20  他の枝\nZ124  例"], ["Z123-2  例\nZ123-2  再出\nZ124  次"],
            ["Z123-2  例\n続き"], ["Z123-2  例", "", "Z124  次"],
            ["Z123-2  例\n  Z999  不明な見出し\nZ125  次"],
            ["Z123-2  例\nZ124\n次の行に名称\nZ125  次"],
            ["Z123-2  例\nZ123 -3  位置が不明な枝\nZ125  次"],
            ["Z123-2  例\n（条件を満たす場合に限る。）\nZ125  次"],
        ]:
            with self.subTest(pages=pages), self.assertRaises(ValueError):
                select_section(pages, "Z123-2")

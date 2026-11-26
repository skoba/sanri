from pathlib import Path
import subprocess
import unittest

from tools.fee_lean_draft import build_draft
from tools.fee_sections import FeeSection, SourceLine


def synthetic(*lines, code="Q900-3", **metadata):
    section = FeeSection(code, tuple(SourceLine(8, i, line) for i, line in enumerate(lines, 9)))
    return build_draft(section, identifier="合成資料", edition="試作版", **metadata)


class DraftTests(unittest.TestCase):
    def test_scope_and_anchors(self):
        result = synthetic(
            "Ｑ９００－３　合成測定", "１　試験甲　３点", "２　試験乙　1,215点",
            "注　合成測定は、患者１人につき月４回に限り算定する。",
        )
        self.assertEqual([(r["page"], r["line"], r["kind"]) for r in result.records], [
            (8, 9, "heading"), (8, 10, "base_points"), (8, 11, "base_points"),
            (8, 12, "patient_monthly_cap"),
        ])
        self.assertIn("points = 1215", result.lean)
        self.assertIn("claims.length ≤ 4", result.lean)
        self.assertIn("Q900-3 PDF p.8 抽出行12", result.lean)
        self.assertIn("verification := .unchecked", result.lean)
        self.assertNotIn("合成測定", result.lean)

    def test_exception_or_other_subject_requires_review(self):
        cap = "注 合成測定は、患者1人につき月4回に限り算定する。"
        for notes in ([cap, "ただし、特例による。"], [cap.replace("合成測定", "項目甲")],
                      ["注1 他の条件", cap]):
            with self.subTest(notes=notes):
                result = synthetic("Q900-3 合成測定 382点", *notes)
                self.assertNotIn("def patientMonthlyCap", result.lean)
                self.assertTrue(all(row["kind"] == "unresolved" for row in result.records[1:]))
                self.assertIn("Q900-3 PDF p.8 抽出行10", result.lean)

    def test_malformed_fee_and_note_continuations_do_not_create_items(self):
        result = synthetic("Q900-3 標本", "１ 甲 １,２点", "２ 作業 ３点",
                           "注 本文", "１ 別の処理 101点")
        self.assertNotIn("BasePoints", result.lean)
        self.assertEqual([r["text"] for r in result.records[1:]], [
            "１ 甲 １,２点", "２ 作業 ３点", "注 本文", "１ 別の処理 101点",
        ])

    def test_conditional_or_derived_prices_remain_unresolved(self):
        for price in ("１ 甲の場合 22点", "１ 甲の点数に10点を加える",
                      "１ Ａ及びＢ 20点又は22点", "２ 甲 22点"):
            with self.subTest(price=price):
                draft = synthetic("Q900-3 標本", price)
                self.assertEqual(draft.records[1]["kind"], "unresolved")
                self.assertNotIn("BasePoints", draft.lean)

    def test_metadata_remains_inside_string_literals(self):
        draft = synthetic('Q900-3 標本 12点', url='a"\nend namespace\\b')
        self.assertIn(r'url := some "a\"\nend namespace\\b"', draft.lean)

    def test_item_rules_compose_for_a_selected_item(self):
        draft = synthetic("Q900-3 標本", "１ 試験甲 9点", "２ 試験乙 46点")
        proof = """
open Sanri.Draft.Q900_3 Sanri.Logic

example : Satisfies [item1BasePoints, item2BasePoints] (some 2) 46 := by
  intro rule hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [item1BasePoints, item2BasePoints]

example : ¬ Satisfies [item1BasePoints, item2BasePoints] (some 2) 9 := by
  intro h
  have wrong := h item2BasePoints (by simp)
  have : 9 = 46 := wrong rfl
  contradiction
"""
        root = Path(__file__).resolve().parents[1]
        subprocess.run(["lake", "build", "Sanri.Logic"], cwd=root, check=True, capture_output=True)
        checked = subprocess.run(["lake", "env", "lean", "--stdin"], input=draft.lean + proof,
                                 text=True, cwd=root, capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

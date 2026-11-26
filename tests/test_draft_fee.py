"""Local output and provenance checks, with synthetic input only."""

from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from tools import draft_fee
from tools.fee_sections import select_section


class DraftWorkflowTests(unittest.TestCase):
    def test_unregistered_pdf_is_rejected_before_extraction(self):
        with TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "example.pdf"
            pdf.write_bytes(b"unregistered edition")
            with patch.object(draft_fee, "extract_pages") as extract:
                with self.assertRaisesRegex(ValueError, "SHA-256"):
                    draft_fee.verified_pages(pdf)
                extract.assert_not_called()

    def test_typecheck_failure_publishes_no_bundle(self):
        section = select_section(["D800 架空検査 10点\nD801 次の検査 5点"], "D800")
        with TemporaryDirectory() as tmp:
            dest = Path(tmp)
            with patch.object(draft_fee.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "lean")):
                with self.assertRaises(subprocess.CalledProcessError):
                    draft_fee.save_draft(section, dest)
            self.assertEqual(list((dest / "drafts" / section.code).iterdir()), [])

    def test_edited_review_is_preserved(self):
        section = select_section(["D800 架空検査 10点\nD801 次の検査 5点"], "D800")
        with TemporaryDirectory() as tmp, patch.object(draft_fee.subprocess, "run"):
            result = draft_fee.save_draft(section, Path(tmp))
            folder, _, _ = result
            self.assertEqual(draft_fee.save_draft(section, Path(tmp)), result)
            edited = folder / "review.json"
            edited.write_text("review in progress", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "変更"):
                draft_fee.save_draft(section, Path(tmp))
            self.assertEqual(edited.read_text(encoding="utf-8"), "review in progress")

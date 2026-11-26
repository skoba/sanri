"""Check that page citations retain Poppler's physical page numbering."""

from pathlib import Path
from subprocess import CompletedProcess
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from tools.local_pdf import extract_pages


class PhysicalPagesTest(unittest.TestCase):
    def extract(self, poppler_output: bytes) -> list[str]:
        with TemporaryDirectory() as folder:
            pdf = Path(folder) / "fixture.pdf"
            pdf.touch()
            result = CompletedProcess([], 0, stdout=poppler_output, stderr=b"")
            with patch("tools.local_pdf._poppler", return_value=("pdftotext", None)), \
                 patch("tools.local_pdf.subprocess.run", return_value=result):
                return extract_pages(pdf)

    def test_blank_pages_keep_their_physical_numbers(self):
        self.assertEqual(self.extract(b"head\n\f\f  row\n\f\f"), ["head\n", "", "  row\n", ""])

    def test_no_text_layer_is_reported(self):
        with self.assertRaisesRegex(ValueError, "テキスト層"):
            self.extract(b"\f\f")

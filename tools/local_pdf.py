"""Extract physical PDF pages with Poppler (pdftotext), entirely offline.

Requires poppler-utils on PATH, or the copy shipped in the Ubuntu CUPS snap.
Layout mode keeps positions of the notice's headings, item numbers and points.
Text order, ruby and table layout still need comparison with the source PDF.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sysconfig


def _poppler() -> tuple[str, dict[str, str] | None]:
    binary = shutil.which("pdftotext")
    if binary:
        return binary, None

    # Ubuntu's CUPS snap bundles Poppler without exposing pdftotext on PATH.
    # The snap's matching shared libraries apply only to this subprocess.
    snap = Path("/snap/cups/current/usr")
    binary_path = snap / "bin/pdftotext"
    arch = sysconfig.get_config_var("MULTIARCH")
    if arch and os.access(binary_path, os.X_OK):
        lib = snap / "lib" / arch
        if lib.is_dir():
            paths = [str(lib)]
            if os.environ.get("LD_LIBRARY_PATH"):
                paths.append(os.environ["LD_LIBRARY_PATH"])
            return str(binary_path), {**os.environ, "LD_LIBRARY_PATH": os.pathsep.join(paths)}
    raise ValueError("PDFの抽出にはPopplerのpdftotextが必要です（Ubuntuではpoppler-utils）。")


def extract_pages(pdf: Path) -> list[str]:
    """Return one Unicode string per physical page, retaining empty pages."""
    if not pdf.is_file():
        raise ValueError(f"入力PDFが見つかりません: {pdf}")
    binary, env = _poppler()
    completed = subprocess.run(
        [binary, "-layout", "-enc", "UTF-8", "-eol", "unix", str(pdf.resolve()), "-"],
        env=env, capture_output=True,
    )
    if completed.returncode or b"Syntax Error" in completed.stderr:
        diagnostic = completed.stderr.decode("utf-8", errors="replace").strip()
        raise ValueError(f"PDFを抽出できません: {diagnostic or completed.returncode}")
    text = completed.stdout.decode("utf-8")
    pages = text.removesuffix("\f").split("\f")
    if not any(page.strip() for page in pages):
        raise ValueError("PDFから本文を抽出できません。テキスト層のある原本を指定してください。")
    return pages

"""Select a fee-code block from layout-preserving pages of the medical fee schedule."""

from dataclasses import dataclass
import re
import unicodedata


_CODE = r"[A-Z][0-9]{3}(?:-[0-9]+)*"
_HEADING = re.compile(rf"^({_CODE})[ \t]+[^\s-]")
_DELETED_RANGE = re.compile(rf"^{_CODE}(?:から{_CODE}まで|及び{_CODE})\s+削除$")
_DIVISION = re.compile(r"^第[0-9]+[章部節款][ \t]+\S")


def _normalized(text: str) -> str:
    return unicodedata.normalize("NFKC", text).replace("−", "-")


def normalize_code(code: str) -> str:
    normalized = _normalized(code).strip().upper()
    if not re.fullmatch(_CODE, normalized):
        raise ValueError("区分番号には A000 や D216-2 のように枝番号まで指定してください")
    return normalized


@dataclass(frozen=True)
class SourceLine:
    page: int
    number: int
    text: str


@dataclass(frozen=True)
class FeeSection:
    code: str
    lines: tuple[SourceLine, ...]

    @property
    def start_page(self) -> int:
        return self.lines[0].page

    @property
    def end_page(self) -> int:
        return self.lines[-1].page


def _trim_heading_prelude(lines: list[SourceLine]) -> None:
    """Look past possible ruby to recognise a separate group heading.

    A hiragana-only line might also be a real continuation. Keep it for review
    unless it occurs *after* an identifiable group boundary.
    """
    index = len(lines) - 1
    while index > 0 and re.fullmatch(r"[ \t]+[ぁ-ゖ \t]+", lines[index].text):
        index -= 1
    if index == 0:
        return
    label = _normalized(lines[index].text).strip()
    # A grouped test caption can immediately precede the next code (e.g. D007/D008).
    # Other parenthesised expressions may qualify a fee in this section. Do not guess
    # where an unfamiliar caption begins, or drop an amount or condition as a caption.
    if re.fullmatch(r"\([\w・、 ]*検査(?:等|\([IVX]+\))?\)", label):
        del lines[index:]
    elif label.startswith("(") and label.endswith(")"):
        raise ValueError(f"{lines[index].page}頁の末尾の括弧行は区分との境界を確認してください")


def select_section(pages: list[str], code: str) -> FeeSection:
    """Locate a unique, bounded heading in the layout used by the R8 primary PDF.

    Returned nonblank lines retain their source spelling, spacing and 1-based physical
    page/line numbers. Only left-margin fee codes followed by whitespace and a title
    count as headings. An explicit later heading must close the selected block.
    """
    code = normalize_code(code)
    lines: list[SourceLine] = []
    found = closed = False
    for page, content in enumerate(pages, start=1):
        if found and not closed and not content.strip():
            raise ValueError(f"{code} の途中または直後の{page}頁に抽出できた文字がありません")
        for number, raw in enumerate(content.splitlines(), start=1):
            text = _normalized(raw).rstrip()
            if not text:
                continue
            heading = _HEADING.match(text)
            if heading and heading[1] == code:
                if found:
                    raise ValueError(f"{code} の見出しが複数あります")
                found = True
            elif found and not closed:
                if (heading or _DELETED_RANGE.fullmatch(text)
                        or _DIVISION.match(text.lstrip()) or text.strip() in {"区分", "通則"}):
                    _trim_heading_prelude(lines)
                    closed = True
                elif re.match(_CODE, text) or _HEADING.match(text.lstrip()):
                    raise ValueError(f"{page}頁{number}行の区分番号と見出しの境界を確認してください")
            if found and not closed:
                lines.append(SourceLine(page, number, raw))
    if not found:
        raise ValueError(f"{code} の独立した見出しを特定できません")
    if not closed:
        raise ValueError(f"{code} を閉じる次の見出しを特定できません")
    return FeeSection(code, tuple(lines))

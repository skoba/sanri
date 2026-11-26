"""ローカルPDFと索引の登録版。"""

from pathlib import Path

LOCAL = Path(__file__).resolve().parents[1] / "tensuhyo"
PRIMARY_SOURCE = {
    "id": "令和8年厚生労働省告示第69号・別表第一",
    "edition": "令和8年度改定・2026-10-22取得版",
    "url": "https://www.mhlw.go.jp/content/12400000/001686842.pdf",
    "sha256": "1b72d3cc1d0006f0e8f91afd2c3a49f21272e3ba376b8d24a6dffda63092e2d6",
}


NOTICE_PDF = LOCAL / "mhlw/r08/ika-notification-20261007.pdf"
NOTICE_SOURCE = {
    "id": "保医発0305第6号・別添1",
    "edition": "令和8年度改定・2026-10-07訂正後",
    "url": "https://www.mhlw.go.jp/content/12400000/001757385.pdf",
    "sha256": "148e4b6d323e2697af8724bf5bf0bb504b39d1dce4e055195e5dddd79672f697",
}

def require_source(actual: dict, registered: dict) -> None:
    if any(actual.get(key) != value for key, value in registered.items()):
        raise ValueError(f"索引が登録版と異なります: {registered['id']}")

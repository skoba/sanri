"""ローカルPDFと索引の登録版。"""

import json
from pathlib import Path

LOCAL = Path(__file__).resolve().parents[1] / "tensuhyo"
R08_AS_OF = "2026-10-22"
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


# 2026-11-26取得の固定版。掲載情報と取得時刻はローカルのsources.jsonに保持。
R08_DOWNLOADS = {
    "amendments": {
        "amendment-20260430-0430-4.pdf": "35b0043ff187d08d8c77064d40195b7b3b4af43d4d418e28aa373325e0463927",
        "amendment-20260430-replacement-20260518.pdf": "e9f7cf07e0af05b59d12bdfc2b5325acf08c38ebcff1469bf45d1b71bedc8e9c",
        "amendment-20260529-0529-2.pdf": "00656838b738469ce2ed70601edb14d6e870cab516cff71dbc4b4575a77b4671",
        "amendment-20260630-0630-7.pdf": "0db1d9fc2e5572d332d0dbfdbaf660c49d213d38e91cf282e79f2dbd7a9ee9e1",
        "amendment-20260831-0831-1.pdf": "86eee8f6070347a0db72e0a529a9eed14b5cc21dec01612162bd06ddbf559cfa",
        "amendment-20260930-0930-2.pdf": "91599201a11cee5ca00f8664d126805421aaf6d99cdd1962e217718990308340",
        "amendment-20261030-1030-1.pdf": "1d60fb6c68dc0d77d609157fcdd57f53b55995801500d95bb479e3bedb79a308"
    },
    "clarifications": {
        "clarification-02-20260401.pdf": "ed77a81ff3e54688d3ea37ed9aa85672947838098c615b0e4b1825df0c65a554",
        "clarification-02-correction-20260409.pdf": "d4d07a6030a07d5d7c1887a6345dbb84fada9108a1990f5c06985afe6f778f3c",
        "clarification-03-20260420.pdf": "31591dcee239595ba43f1204cd6a00cd496c526a35d72c55be171ef737345488",
        "clarification-04-20260421.pdf": "02cdb6c907fe2b5796be8743935f179e43132490ff3a29e98a721ad065b48b38",
        "clarification-05-20260508.pdf": "cb7f2aff443a968dee6f34e475159e41b545321b055299441ddfd58861ca933f",
        "clarification-06-20260522.pdf": "d764d0d136d4e28352c99b111a9f8693f62c2469596e0916566e1e2927e62878",
        "clarification-07-20260529.pdf": "8817d6edc3df63b14bca0e6e3617da406dfd236676df1273d61056c65b383fb1",
        "clarification-08-20260617.pdf": "99a020fd31e75523f32514349ae44cd9df6f72fb68ffc95c2fb773bce46a881f",
        "clarification-09-20260626.pdf": "d9f6beb0859af9d17fa25cffc441e5e331917cfb3c0cfec696ff7c7301c5c190",
        "clarification-10-20260717.pdf": "747d2b64080c56ed9e153b9dfc9ed298e48bc15142d2c6bd834c248dbbd4b86f",
        "clarification-11-20260730.pdf": "c53a6fa2ae0749928a954e2ef7034318ab6442562f8b9ec6b5c24a488f933823",
        "clarification-12-20260902.pdf": "3a7fc8710cbe7e8473b79d2aba9c0738f31dbabfd3c809eadb64020793cc7026",
        "clarification-13-20260925.pdf": "0abbdc8253627b61aefd373fb675efb9f6b8a5bb81339de83e52a3fcdf2b0b5c",
        "clarification-14-20261028.pdf": "b9f58794d536ee00fabe46dadc58ce2cb7d54d671f44e0dc6a603c3555b688a9"
    },
    "corrections": {
        "correction-20260402.pdf": "57316f9df0d0c889b5bc57c04fbd99e1ab6fb7091c2e5a79c4f3a54b48f022d2",
        "correction-20260501.pdf": "886f21c87c8bf2357473454548cf88b397b920ea5b5f5fc54a779229702b8294",
        "correction-20260529.pdf": "a7420c7940317ca02ad17ccec52c93493e355ce444fbac728d9b881ca9f5a60d",
        "correction-20260619.pdf": "4b150751fdf9a53ea4efd70f6156cfc1096a290a37022648de7908e4567a97e3",
        "correction-20260730.pdf": "2681ff7383277541826a20bf3bbf16e54dbe844adf22e4c630138ddf02cfaf2c",
        "correction-20261007.pdf": "c6537fe103732b10547dbfbe2e8870d7096caac13995f62d6f5969fddc0c7127"
    },
    "facility": {
        "kihon-kokuji-70.pdf": "84986b79ab50475f4e7d5b18c373de3c1e2ded561d52d6e8d127002ff96bbeaa",
        "kihon-notification-0305-7.pdf": "9b63d170312634c1a855e5173c0ec9832505cd1870cdf22e3f43994a975012c8",
        "tokkei-kokuji-71.pdf": "905c0781f26fae561f513d4017ea6a3e6a928726cdd1a16d4833665c14f79852",
        "tokkei-notification-0305-8.pdf": "81303bed9600cf81681bbd44a72e1b7a9c8cd3b78e7baa26618be766622dc9ba"
    }
}
CLARIFICATION_01_SHA256 = "92ed2030276dae81a92d7be936de1d46ba2e77fa9acf568b5089d3ebe56af200"


def read_downloads(group: str) -> list[dict]:
    """取得時の掲載情報を読み、固定登録したPDFの一覧と照合する。"""
    directory = LOCAL / "mhlw/r08" / group
    manifest = directory / "sources.json"
    if manifest.resolve() != manifest:
        raise ValueError(f"登録先にシンボリックリンクがあります: {group}")
    listing = json.loads(manifest.read_text(encoding="utf-8"))
    downloads = listing["downloads"]
    registered = R08_DOWNLOADS[group]
    if (len(downloads) != len(registered)
            or {row["path"]: row["sha256"] for row in downloads} != registered):
        raise ValueError(f"取得一覧が登録版と異なります: {group}")
    return [{**row, "source_page": listing["source_page"], "downloaded_at": listing["downloaded_at"],
             "discovery": "listed_on_source_page", "acquisition": "downloaded",
             "content_at_registration": "unreviewed", "formalization_this_round": "not_started"}
            for row in downloads]

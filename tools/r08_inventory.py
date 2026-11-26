"""令和8年の改正・訂正・疑義解釈・施設基準のローカル索引を生成する。"""

from collections import Counter, defaultdict
import csv
from datetime import date
import re

from .fee_coverage import clause_paths
from .fee_inventory import CODE, normalized, write_local
from .fee_ledger import load_lean, read_index
from .local_pdf import verified_pdf_pages
from .notice_inventory import build_notice
from .pdf_sources import (CLARIFICATION_01_SHA256, LOCAL, NOTICE_PDF, NOTICE_SOURCE,
                          PRIMARY_SOURCE, R08_AS_OF, R08_DOWNLOADS, read_downloads, require_source)
from .procedure_master import INDEX_COLUMNS

AS_OF = R08_AS_OF
BASE = LOCAL / "mhlw/r08"
FOOTER = re.compile(r"(?:-\s*)?\d+(?:\s*-)?")
QUESTION = re.compile(r"^問\s*([0-9]+(?:\s*-\s*[0-9]+)*)(?![0-9-])")
TARGET = re.compile(r"(医科・歯科|医科|歯科|調剤)診療?報酬点数表関係(?:\s*\(DPC\))?|"
                    r"(調剤)報酬点数表関係|(訪問看護)療養費関係")
SHARED_TARGET = {
    "看護職員処遇改善評価料及びベースアップ評価料関係": "看護職員処遇改善・ベースアップ評価料",
    "掲示事項関係": "掲示事項",
}
DIRECTIVE = re.compile(r"^\s*(\d+)\s+別添\s*(\d+).*?(を次のように改める|の次に次を加える|を削る)。")
PAREN = re.compile(r"^\((\d+)\)")
ATTACHMENT = re.compile(r"^\s*(?:\(別添\s*(\d+)\)|別添\s*(\d+))\s*$", re.M)


def compact(text: str) -> str:
    return re.sub(r"\s+", "", normalized(text).translate(str.maketrans("‐‑‒–—―", "------")))


def numbered_lines(pages, first=1):
    for page, content in enumerate(pages, first):
        for line, raw in enumerate(normalized(content).splitlines(), 1):
            if raw.strip() and not FOOTER.fullmatch(raw.strip()):
                yield page, line, raw


def scope_headers(pages, parenthesized):
    for number, page in enumerate(pages, 1):
        lines = normalized(page).strip().splitlines()
        if lines and (match := ATTACHMENT.fullmatch(lines[0])):
            if bool(match[1]) == parenthesized:
                yield number, int(match[1] or match[2])


def question_index(pages, source, correction=False):
    questions = []
    target = "医科" if correction else None
    heading = None
    initial_attachments = {
        "医科": 1, "看護職員処遇改善・ベースアップ評価料": 2,
        "歯科": 3, "調剤": 4, "訪問看護": 5,
    }
    attachment = 1 if correction or source["path"].startswith("clarification-02-") else None
    current = None
    in_answer = False
    for page, line, raw in numbered_lines(pages[1:], 2):
        label = raw.strip()
        if annex := ATTACHMENT.fullmatch(label):
            attachment = int(annex[1] or annex[2])
        elif label in SHARED_TARGET:
            target = SHARED_TARGET[label]
            current = heading = None
        elif match := TARGET.fullmatch(label):
            target = next(group for group in match.groups() if group)
            if "(DPC)" in label:
                target += "（DPC）"
            current = heading = None
        if target and source["path"].startswith("clarification-01-"):
            attachment = initial_attachments.get(target, attachment)
        if re.fullmatch(r"【[^】]+】", label):
            heading, current = label, None
        elif match := QUESTION.match(raw):
            in_answer = False
            number = compact(match[1])
            current = {"number": int(number) if number.isdecimal() else number,
                       "target": target, "attachment": attachment, "page": page, "line": line,
                       "text": [heading or "", raw[match.end():]]}
            questions.append(current)
        elif label.startswith("(答"):
            in_answer = True
        elif current is not None and not in_answer:
            current["text"].append(label)
    corrections = {
        ("clarification-02-correction-20260409.pdf", 1): ("02", 1),
        ("clarification-05-20260508.pdf", 6): ("02", 1),
        ("clarification-06-20260522.pdf", 5): ("04", 1),
        ("clarification-07-20260529.pdf", 5): ("06", 3),
    }
    for row in questions:
        corrected = corrections.get((source["path"], row["attachment"]))
        if corrected:
            row["corrects"] = {"series": corrected[0], "attachment": corrected[1],
                               "number": row["number"]}
        # 頁・行をまたぐコードと全角桁の組版空白を復元する。
        codes = sorted(set(re.findall(rf"{CODE}(?![0-9-])", compact("".join(row.pop("text"))))))
        row.update(codes=codes, division_status="明示あり" if codes else "区分未特定",
                   document=source["path"], issued_on=source["issued_on"],
                   issue_relative_to_as_of=("after" if source["issued_on"] > AS_OF else
                                            "on" if source["issued_on"] == AS_OF else "before"),
                   correction=bool(corrected))
    return questions


def notice_blocks(pages, index):
    return {key: notice_spans(pages, index, key) for key in ("division", "paragraph")}


def notice_spans(pages, index, level):
    by_code = defaultdict(list)
    for block in index["blocks"]:
        entries = block["paragraphs"] if level == "paragraph" else [block]
        for entry in entries:
            start, end = entry["start"], entry["end"]
            span = [raw for page, line, raw in numbered_lines(
                pages[start["page"] - 1:end["page"]], start["page"]
            ) if (start["page"], start["line"]) <= (page, line) <= (end["page"], end["line"])]
            for code in block["codes"]:
                key = (code, entry["number"]) if level == "paragraph" else code
                by_code[key].append((start["page"], end["page"], compact("".join(span))))
    return by_code


def amendment_rows(pages, source, attachment, effective, blocks, *, current_edition=True):
    headers = list(scope_headers(pages, parenthesized=False))
    first, last = next((page, headers[i + 1][0] - 1)
                       for i, (page, number) in enumerate(headers[:-1]) if number == attachment)
    rows = []
    row = None
    for page, line, raw in numbered_lines(pages[first - 1:last], first):
        if match := DIRECTIVE.match(raw):
            locator = compact(raw[:match.start(3)])
            code_match = re.search(CODE, locator)
            code = code_match[0] if code_match else None
            anchor = locator[code_match.end():] if code else None
            row = {"page": page, "line": line, "code": code, "anchor": anchor,
                   "target_attachment": int(match[2]), "directive": int(match[1]),
                   "operation": {"を次のように改める": "change", "の次に次を加える": "add",
                                 "を削る": "delete"}[match[3]], "lines": []}
            rows.append(row)
        elif row is not None:
            row["lines"].append(raw)
    for row in rows:
        lines = row.pop("lines")
        new_text = compact("".join(lines))
        marker = re.match(r"\((\d+)\)|([ァ-ヶ])(?=\s)|([0-9]+)(?=\s)", lines[0].strip()) if lines else None
        new_locator = marker[0] if marker else None
        if not new_locator and lines and (kana := re.match(r"\([ァ-ヶ]\)", lines[0].strip())):
            new_locator = kana[0]
        row["new_locator"] = new_locator
        row["paragraph"] = None
        if row["anchor"] and (anchor := PAREN.match(row["anchor"])):
            row["paragraph"] = int(anchor[1])
            if row["operation"] == "add" and new_locator and (added := PAREN.match(new_locator)):
                row["paragraph"] = int(added[1])
        medical = current_edition and row["target_attachment"] == 1
        division_spans = blocks["division"].get(row["code"], []) if medical else []
        numbered = blocks["paragraph"].get((row["code"], row["paragraph"]), []) if medical else []
        candidates = numbered or division_spans
        hits = [(a, b) for a, b, body in candidates if new_text and new_text in body]
        # 新設番号を持つ段落は、直前の段落が索引にあって新番号がない場合に限る。
        anchor = PAREN.match(row["anchor"] or "")
        missing_number = (row["operation"] == "add" and new_locator and PAREN.match(new_locator)
                          and anchor and not numbered
                          and blocks["paragraph"].get((row["code"], int(anchor[1]))))
        # 同一段落内の枝追加・置換は、原文と登録版の位置を個別に確認した箇所。
        reviewed = {
            "20260430": {1: 336, 2: 336, 3: 348, 4: 382},
            "20260518": {1: 336, 2: 336, 3: 348, 4: 382},
            "20260529": {1: 223, 2: 224, 3: 336},
            "20260630": {1: 346},
            "20260831": {1: 155},
            "20260930": {2: 401},
            "20261030": {1: 336, 2: 348, 3: 715},
        }.get(source["issued_on"].replace("-", ""), {})
        reviewed_page = reviewed.get(row["directive"]) if medical else None
        row["amending_attachment"] = attachment
        status, confidence, basis = "undetermined", None, "要原文確認"
        if not medical:
            status, basis = "outside_baseline", "医科の登録版の対象外"
        elif len(hits) == 1:
            status, confidence, basis = "present", "high", "対象範囲で改正後文言が一致"
        elif missing_number:
            status, confidence, basis = "absent", "high", "直前段落あり、新設段落番号なし"
        elif reviewed_page:
            status, confidence, basis = "absent", "high", "原文で確認した枝・変更前文言と比較"
        row.update(document=source["path"], issued_on=source["issued_on"], effective_from=effective,
                   applies_on_as_of=effective <= AS_OF, evidence=new_text,
                   baseline_candidate_pages=[[a, b] for a, b, _ in candidates],
                   baseline_match_pages=hits, baseline_reviewed_page=reviewed_page,
                   incorporation=status, confidence=confidence, basis=basis)
    return rows, [first, last]


def correction_rows(pages, source, blocks):
    headers = dict((number, page) for page, number in scope_headers(pages, parenthesized=True))
    first, last = headers[1], headers[2] - 1
    # 訂正文は変更履歴の挿入・取消が同じテキスト層に出る。位置と一致する抜粋を残す。
    result = []
    entry = None
    attachment = None
    for page, line, raw in numbered_lines(pages[first - 1:last], first):
        label = raw.strip()
        heading = re.match(rf"({CODE})(?:\s{{2,}}|$)", label)
        if annex := re.fullmatch(r"別添\s*(\d+)(?:の\s*(\d+))?", label):
            attachment = annex[1] + ("-" + annex[2] if annex[2] else "")
        if heading or re.match(r"^(?:別添\s*\d|第\s*\d+\s*[章部節款])", label):
            entry = {"code": heading[1] if heading else None, "heading": label,
                     "page": page, "line": line, "attachment": attachment, "lines": []}
            result.append(entry)
        elif entry is not None:
            entry["lines"].append(label)
    reviewed = {
        ("2026-04-02", "D026", 6): 402,
        ("2026-05-29", "A001", 8): 14,
        ("2026-05-29", "D237", 5): 422,
        ("2026-06-19", "D237", 4): 422,
        ("2026-10-07", "D218", None): 413,
    }
    for entry in result:
        lines = entry.pop("lines")
        entry["paragraph_marker_candidates"] = [m[1] for line in lines if (m := PAREN.match(line))]
        entry["paragraphs"] = sorted({int(m) for m in entry["paragraph_marker_candidates"]})
        body = compact("".join(lines))
        candidates = blocks["division"].get(entry["code"], []) if entry["attachment"] == "1" else []
        hits = [(a, b) for a, b, text in candidates if len(body) >= 20 and body in text]
        reviewed_page = reviewed.get((source["issued_on"], entry["code"],
                                      next(iter(entry["paragraphs"]), None))) if candidates else None
        status, confidence, basis = "undetermined", None, "変更履歴の挿入・取消の分離が必要"
        if entry["attachment"] not in {None, "1", "1-2"}:
            status, basis = "outside_baseline", "医科の別添1・1の2の範囲外"
        elif reviewed_page:
            status, confidence, basis = "present", "high", "変更履歴の抽出文と登録版を個別比較"
        elif len(hits) == 1:
            status, confidence, basis = "present", "medium", "訂正資料の抽出範囲が対象区分内で一致"
        entry.update(baseline_candidate_pages=[[a, b] for a, b, _ in candidates],
                     baseline_match_pages=hits, baseline_reviewed_page=reviewed_page,
                     incorporation=status, confidence=confidence, basis=basis,
                     evidence=lines, document=source["path"], issued_on=source["issued_on"],
                     operation="correction")
    return result, [first, last]


def facility_index(pages):
    headings = []
    for page, line, raw in numbered_lines(pages):
        label = raw.strip()
        if re.match(r"^(?:別添\s*\d+(?:\s|$)|第\s*\d+(?:\s*の\s*\d+)*\s+[^条号項節の\s])", label):
            headings.append({"page": page, "line": line, "heading": label})
    for current, following in zip(headings, headings[1:]):
        current["through_page"] = (following["page"] - 1 if following["line"] == 1
                                   and following["page"] > current["page"] else following["page"])
    if headings:
        headings[-1]["through_page"] = len(pages)
    return {"page_count": len(pages), "heading_candidates": headings,
            "layout": "horizontal_heading_candidates" if headings else "heading_extraction_unavailable"}


def read_pdf(group, source):
    path = BASE / group / source["path"]
    if path.resolve() != path or path.stat().st_size != source["bytes"]:
        raise ValueError(f"PDFの配置またはバイト数が登録版と異なります: {path.name}")
    return verified_pdf_pages(path, source["sha256"])


def main():
    fee = read_index("fee-index.json")
    require_source(fee["source"], PRIMARY_SOURCE)
    baseline = verified_pdf_pages(NOTICE_PDF, NOTICE_SOURCE["sha256"])
    blocks = notice_blocks(baseline, build_notice(baseline, fee))
    groups = {group: read_downloads(group) for group in R08_DOWNLOADS}
    first = {"path": "clarification-01-20260323.pdf", "sha256": CLARIFICATION_01_SHA256,
             "issued_on": "2026-03-23", "bytes": 530690}
    questions = question_index(read_pdf("", first), first)
    for source in groups["clarifications"]:
        questions.extend(question_index(read_pdf("clarifications", source), source,
                                        correction="-correction-" in source["path"]))
    specimens = {row["code"] for row in fee["rows"]
                 if row["status"] == "listed" and row["chapter"] == 2
                 and row["part"] == 3 and row["section"] == 1}
    corrected_keys = {(q["corrects"]["series"], q["corrects"]["attachment"], q["corrects"]["number"])
                      for q in questions if q["correction"] and q["issued_on"] <= AS_OF}
    for row in questions:
        key = (row["document"].split("-")[1], row["attachment"], row["number"])
        row["superseded_by_indexed_correction"] = not row["correction"] and key in corrected_keys
    question_keys = Counter((q["document"], q["attachment"], q["number"]) for q in questions)
    issues = [{"document": document, "attachment": attachment, "number": number,
               "issue": "duplicate_question_marker"}
              for (document, attachment, number), count in question_keys.items() if count > 1]
    stats = Counter()
    for row in questions:
        stats["rows"] += 1
        stats["correction_rows"] += row["correction"]
        stats["medical"] += bool(row["target"] and row["target"].startswith("医科"))
        stats["identified"] += bool(row["codes"])
        stats["specimen"] += bool(row["target"] and row["target"].startswith("医科")
                                  and specimens.intersection(row["codes"]))
    print(write_local({"as_of": AS_OF, "sources": [first, *groups["clarifications"]],
                       "counts": dict(stats), "issues": issues, "questions": questions}, name="clarification-index.json"))

    facilities = []
    for source in groups["facility"]:
        facilities.append({"source": source, "review_scope": "page_count_and_heading_candidates", **facility_index(read_pdf("facility", source))})
    print(write_local({"documents": facilities}, name="facility-index.json"))

    amendments, corrections = [], []
    # 表紙の適用日と添付番号を原文で確認した登録順。
    editions = {
        "20260430-0430-4": (2, "2026-06-01", [(4, "R06"), (6, "R08"), (8, "R06"), (1, "R08"), (12, "R06"), (4, "R08")]),
        "20260430-replacement-20260518": (2, "2026-06-01", [(4, "R06"), (6, "R08"), (8, "R06"), (1, "R08"), (12, "R06"), (4, "R08")]),
        "20260529-0529-2": (1, "2026-06-01", [(6, "R08"), (1, "R08"), (2, "R08"), (4, "R08")]),
        "20260630-0630-7": (1, "2026-07-01", [(6, "R08"), (4, "R08")]),
        "20260831-0831-1": (1, "2026-09-01", [(6, "R08"), (1, "R08"), (2, "R08"), (4, "R08"), (3, "R08")]),
        "20260930-0930-2": (1, "2026-10-01", [(6, "R08"), (1, "R08"), (4, "R08")]),
        "20261030-1030-1": (1, "2026-11-01", [(6, "R08"), (4, "R08")]),
    }
    for source in groups["amendments"]:
        edition = source["path"].removeprefix("amendment-").removesuffix(".pdf")
        attachment, effective, targets = editions[edition]
        pages = read_pdf("amendments", source)
        rows, span = amendment_rows(pages, source, attachment, effective, blocks)
        older_rows, older_span = amendment_rows(
            pages, source, 1, "2026-05-01", blocks, current_edition=False
        ) if attachment == 2 else ([], None)
        tables = [(number, int(table[1])) for number, page in enumerate(pages, 1)
                  if (table := re.match(r"\s*\(別添\s*(\d+)参考\)", normalized(page)))]
        references = [number for number, annex in tables if annex == attachment]
        if references:
            beginning = references[0]
            ending = next((number - 1 for number, _ in tables if number > beginning), len(pages))
            table_lines = list(numbered_lines(pages[beginning - 1:ending], beginning))
            for row in rows:
                row["comparison_table_division_headings"] = [
                    {"page": page, "line": line}
                    for page, line, raw in table_lines
                    if re.match(rf"\s*{re.escape(row['code'] or '')}\s+\S", raw)
                ] if row["code"] else []
        amendments.append({"source": source, "review_scope": "cover_and_amending_directives",
                           "effective_from": effective, "pages": span,
                           "comparison_table_starts": references, "older_edition_pages": older_span,
                           "older_edition_changes": older_rows,
                           "superseded": edition == "20260430-0430-4", "changes": rows,
                           "targets": [{"attachment": i, "notice": f"{year} 保医発0305第{number}号",
                                        "effective_from": ("2026-05-01" if year == "R06" else effective)}
                                       for i, (number, year) in enumerate(targets, 1)]})
    for source in groups["corrections"]:
        rows, span = correction_rows(read_pdf("corrections", source), source, blocks)
        corrections.append({"source": source, "pages": span, "locations": rows})
    report = {"as_of": AS_OF, "baseline": NOTICE_SOURCE,
              "amendments": amendments, "corrections": corrections}
    applicable = [doc for doc in amendments
                  if not doc["superseded"] and doc["effective_from"] <= AS_OF]
    to_apply = [doc["source"]["path"] for doc in applicable
                if any(row["incorporation"] == "absent" for row in doc["changes"])]
    report["as_of_conclusion"] = {
        "baseline_alone_sufficient": False if to_apply else None,
        "amendments_to_apply": to_apply,
        "remaining": ["訂正箇所の挿入・取消の全件照合", "別添1の2・別表の照合", "取得資料外の改廃の探索"],
        "missing_for_original_origin": ["0305第6号別添1の当初版と中間訂正版"],
    }
    print(write_local(report, name="notice-revisions.json"))
    print(write_local(impact(report, blocks, specimens), name="notice-impact.json"))


def impact(report, blocks, specimens):
    ledger = read_index("clause-ledger.json")
    master_index = read_index("master-coverage.json")
    if master_index["as_of"] != AS_OF or ledger["master_source"] != master_index["source"]:
        raise ValueError("診療行為マスター索引が条項台帳と異なります")
    require_source(ledger["fee_source"], PRIMARY_SOURCE)
    if ledger["as_of"] != AS_OF:
        raise ValueError("条項台帳の基準日が異なります")
    modeled = {r["division"]: r for r in ledger["clauses"]["divisions"] if r["status"] != "未着手"}
    rules = [(rule, clause_paths(rule)) for rule in load_lean()["rules"]]
    changes = [row for document in report["amendments"] if not document["superseded"]
               for row in document["changes"] if row["applies_on_as_of"] and row["target_attachment"] == 1]
    changes += [row for document in report["corrections"] for row in document["locations"] if row["attachment"] == "1"]
    legacy_evidence = {
        ("2026-04-02", "D026", 6): {
            "definition": "Sanri/SpecimenJudgment.lean:geneRouting",
            "status": "confirmed_gap", "related_division": "D004-3",
            "reason": "登録版の振分け先を確認。旧来の固定判定にはD004-3の分岐がない。",
        },
        ("2026-05-01", "D012", 52): {
            "definition": "Sanri/SpecimenRules.lean:eligible", "item": 62,
            "status": "condition_not_encoded",
        },
        ("2026-05-18", "D014", 26): {
            "definition": "Sanri/SpecimenRules.lean:eligible", "item": 46,
            "status": "condition_not_encoded",
        },
        ("2026-05-29", "D023", 42): {
            "definition": "Sanri/SpecimenRules.lean:eligible", "item": 17,
            "status": "reference_candidate_for_review",
        },
        ("2026-09-30", "D023", 43): {
            "definition": "Sanri/SpecimenRules.lean:eligible", "item": 25,
            "status": "reference_candidate_for_review",
        },
        ("2026-10-07", "D218", None): {
            "definition": "Sanri/UltrasoundMonitoring.lean:eligible",
            "status": "condition_not_encoded",
        },
    }
    affected = []
    for row in changes:
        code = row["code"]
        if code not in modeled:
            continue
        paragraphs = row.get("paragraphs", [row.get("paragraph")])
        matches = sorted({rule["id"] for rule, paths in rules for path in paths
                          if path[:3] == ("notice", code, "paragraph") and int(path[3]) in paragraphs})
        legacy = [legacy_evidence[(row["issued_on"], code, paragraph)]
                  for paragraph in paragraphs or [None]
                  if (row["issued_on"], code, paragraph) in legacy_evidence]
        affected.append({"change": row, "implementation": modeled[code]["module"],
                         "rule_ids": matches, "legacy_review": legacy})
    references = []
    change_items = {
        ("2026-05-18", "D004-2", 1): ("D004-2", "1"),
        ("2026-05-18", "D004-2", 2): ("D004-2", "1"),
        ("2026-05-29", "D004-2", 3): ("D004-2", "1"),
        ("2026-05-29", "D023", 4): ("D023", "17"),
        ("2026-06-30", "D006-17", 1): ("D006-17", "0"),
        ("2026-09-30", "D004", 1): ("D004", "15"),
        ("2026-09-30", "D023", 2): ("D023", "25"),
        ("2026-10-30", "D004-2", 1): ("D004-2", "1"),
    }
    all_amendments = [row for doc in report["amendments"] if not doc["superseded"]
                      for row in doc["changes"] if row["target_attachment"] == 1]
    with (LOCAL / "inventory/master-index.tsv").open(encoding="utf-8", newline="") as stream:
        for master in csv.DictReader(stream, delimiter="	"):
            code = master["準用元区分"]
            if code not in specimens:
                continue
            number = str(int(master["準用元項番"]))
            name = compact(master["省略漢字名称"])
            # 名称の語順差を許容するが、確認した枝・項と変更年月日で範囲を限定する。
            tokens = [token for token in re.split(r"[()・]|及び", name) if len(token) >= 2]
            candidates = [row for row in all_amendments
                          if change_items.get((row["issued_on"], row["code"], row["directive"])) == (code, number)
                          and date.fromisoformat(row["effective_from"]).strftime("%Y%m%d") == master["変更年月日"]
                          and tokens and all(token in row["evidence"] for token in tokens)]
            # D004(15)の実点数は二項の合算で、マスターの準用元項番は単独の算定根拠ではない。
            baseline = [{"paragraph": paragraph, "pages": [a, b]}
                        for (division, paragraph), spans in blocks["paragraph"].items() if division == code
                        for a, b, body in spans
                        if name and name in body and ("「" + number + "」") in body and "準用" in body]
            if (code, number) == ("D004-2", "1") and len(tokens) == 2 and master["変更年月日"] == "20260601":
                # 段落(4)ウ・オ・ケの同一枝の中で、検査と対象の両方が確認できた候補。
                for a, b, body in blocks["paragraph"].get((code, 4), []):
                    sections = re.split(r"[アイウエオカキクケコ](?=[一-龯])", body)
                    if sum(all(token in part for token in tokens) for part in sections) == 1:
                        baseline.append({"paragraph": 4, "pages": [a, b], "origin": "baseline_probable"})
            status = ("amendment_item" if len(candidates) == 1 else
                      "baseline_item_candidate" if len(baseline) == 1 else "item_and_origin_unresolved")
            references.append({"master": master, "amendment_candidates": candidates,
                               "baseline_item_candidates": baseline, "status": status})
    return {"as_of": AS_OF, "affected_candidates": affected, "references": references,
            "exact_notice_rule_ids": sorted({rule for row in affected for rule in row["rule_ids"]}),
            "reference_counts": dict(Counter(row["status"] for row in references))}


if __name__ == "__main__":
    main()

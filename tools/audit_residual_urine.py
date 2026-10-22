#!/usr/bin/env python3
"""Audit a bounded projection of a local D216-2 table snapshot.

No official records are bundled. Codes, the textual limit and its reference are
caller inputs. A witness concerns only per-code frequency rows and exclusion
rows between the two supplied codes; it is not a claim that billing is allowed.
Requires Python 3.10+ and only the standard library.
"""

from __future__ import annotations

import argparse
import csv
from datetime import date, datetime, timedelta
import hashlib
import io
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
SUPPORTED_PUBLICATION = "2026-10-13"
FILES = {
    "auxiliary": ("01 補助マスターテーブル.csv", 27),
    "inclusion": ("02 包括テーブル.csv", 7),
    "exclusion_day": ("03-1 背反テーブル1.csv", 10),
    "exclusion_month": ("03-2 背反テーブル2.csv", 10),
    "exclusion_simultaneous": ("03-3 背反テーブル3.csv", 10),
    "exclusion_week": ("03-4 背反テーブル4.csv", 10),
    "inpatient": ("04 入院基本料テーブル.csv", 8),
    "frequency": ("05 算定回数テーブル.csv", 14),
}
CHANGES = {"0", "1", "3", "5", "9"}
CODE = re.compile(r"[0-9]{9}\Z")
NUMBER = re.compile(r"[0-9]+\Z")
GROUP = re.compile(r"[A-Z0-9]{7}\Z")


class AuditError(ValueError):
    """Invalid or unsupported input; never reinterpret it as permission."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def record_date(value: str, *, end: bool = False) -> date:
    if end and value == "99999999":
        return date.max
    require(bool(re.fullmatch(r"[0-9]{8}", value)), "invalid record date")
    try:
        return date(int(value[:4]), int(value[4:6]), int(value[6:]))
    except ValueError as error:
        raise AuditError("invalid calendar date") from error


def validate_row(kind: str, row: list[str]) -> None:
    require(row[0] in CHANGES, "unknown change category")
    start, end = record_date(row[-2]), record_date(row[-1], end=True)
    require(start <= end, "record validity ends before it starts")

    def enum(index: int, values: set[str]) -> None:
        require(row[index] in values, f"invalid enumeration at column {index + 1}")

    def number(index: int) -> None:
        require(bool(NUMBER.fullmatch(row[index])), f"invalid number at column {index + 1}")

    code_indexes = [2] if kind in {"inclusion", "inpatient"} else [1, 3] if kind.startswith("exclusion_") else [1]
    for index in code_indexes:
        require(bool(CODE.fullmatch(row[index])), f"invalid code at column {index + 1}")
    if kind == "auxiliary":
        for index in (3, 5, 7):
            enum(index, {"0", "1", "2", "3", "5", "6"})
            require((row[index + 1] == "0") if row[index] == "0" else bool(GROUP.fullmatch(row[index + 1])), "invalid inclusion group")
        for index in (9, 10, 11, 12, 20):
            enum(index, {"0", "1"})
        for index in (13, 14, 15, 17, 18, 21, 22, 23, 24):
            enum(index, {"0"})
        enum(16, {""})
        require(bool(re.fullmatch(r"[0-9]{3}", row[19])), "invalid inpatient group")
    elif kind == "inclusion":
        require(bool(GROUP.fullmatch(row[1])), "invalid inclusion group")
        enum(4, {"0", "1"})
    elif kind.startswith("exclusion_"):
        enum(5, {"1", "2", "3"})
        enum(6, {"0", "1"})
        enum(7, {"0"})
    elif kind == "inpatient":
        require(bool(re.fullmatch(r"[0-9]{3}", row[1])), "invalid inpatient group")
        number(4)
        enum(5, {"0"})
    elif kind == "frequency":
        number(3)  # Unit meanings other than day/month are not evaluated below.
        number(5)
        enum(6, {"0", "1"})
        for index in range(7, 12):
            enum(index, {"0"})


def active(row: list[str], on: date) -> bool:
    require(row[0] not in {"1", "9"}, "deletion/abolition change semantics are unsupported; record history cannot be inferred")
    return record_date(row[-2]) <= on <= record_date(row[-1], end=True)


def load_snapshot(snapshot: Path, codes: set[str], as_of: date) -> dict:
    """Validate all eight CSVs, retaining only evidence for the supplied codes."""
    snapshot = snapshot.resolve()
    manifest_path = snapshot / "sources.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    require(isinstance(manifest, dict), "manifest must be an object")
    require(manifest.get("table_published_on") == SUPPORTED_PUBLICATION, "unsupported snapshot publication/schema version")
    require(manifest.get("reference_encoding") == "utf-8", "unsupported reference encoding")
    require(manifest.get("reference_newline") == "LF", "unsupported reference newline")
    try:
        downloaded = datetime.fromisoformat(manifest["downloaded_at"])
        require(downloaded.tzinfo is not None, "downloaded_at requires an explicit timezone")
        published = date.fromisoformat(manifest["table_published_on"])
        date.fromisoformat(manifest["guide_published_on"])
    except (KeyError, TypeError, ValueError) as error:
        raise AuditError("invalid manifest date metadata") from error
    require(published <= as_of <= downloaded.date(), "as-of outside supported snapshot-to-download interval; historical/future rules are unknown")
    entries = manifest.get("extracted_files")
    require(isinstance(entries, list), "manifest extracted_files must be a list")
    by_path = {}
    for entry in entries:
        require(isinstance(entry, dict) and isinstance(entry.get("path"), str), "invalid manifest file entry")
        require(entry["path"] not in by_path, "duplicate manifest path")
        by_path[entry["path"]] = entry

    evidence: dict[str, list[dict]] = {kind: [] for kind in FILES}
    files = []
    for kind, (filename, width) in FILES.items():
        relative = f"tables/{filename}"
        require(relative in by_path, f"manifest missing {relative}")
        entry = by_path[relative]
        data = (snapshot / relative).read_bytes()
        require(len(data) == entry.get("bytes"), f"size mismatch: {relative}")
        require(digest(data) == entry.get("sha256"), f"SHA-256 mismatch: {relative}")
        require(entry.get("column_counts") == [width], f"manifest column count mismatch: {relative}")
        require(b"\r" not in data and b"\0" not in data, f"invalid newline/NUL: {relative}")
        reader = csv.reader(io.StringIO(data.decode("utf-8"), newline=""), strict=True)
        count = 0
        previous_line = 0
        try:
            for count, row in enumerate(reader, 1):
                line = previous_line + 1
                require(reader.line_num == line, f"multiline CSV records unsupported: {relative}:{line}")
                previous_line = reader.line_num
                require(len(row) == width, f"column count mismatch: {relative}:{line}")
                try:
                    validate_row(kind, row)
                except AuditError as error:
                    raise AuditError(f"{relative}:{line}: {error}") from error
                relevant = (
                    row[1] in codes if kind in {"auxiliary", "frequency"}
                    else row[1] in codes and row[3] in codes if kind.startswith("exclusion_")
                    else False
                )
                if relevant:
                    try:
                        is_active = active(row, as_of)
                    except AuditError as error:
                        raise AuditError(f"{relative}:{line}: {error}") from error
                    evidence[kind].append({"file": relative, "line": line, "fields": row, "active_as_of": is_active})
        except csv.Error as error:
            raise AuditError(f"invalid CSV: {relative}:{reader.line_num}: {error}") from error
        require(count == entry.get("rows"), f"row count mismatch: {relative}")
        files.append({"path": relative, "sha256": digest(data), "rows": count, "columns": width})
    return {
        "manifest_path": str(manifest_path),
        "manifest_sha256": digest(manifest_bytes),
        "table_published_on": manifest["table_published_on"],
        "downloaded_at": manifest["downloaded_at"],
        "source_page": manifest.get("source_page"),
        "files": files,
        "evidence": evidence,
    }


def projection_witness(snapshot: dict, ultrasound: str, catheter: str, limit: int, as_of: date) -> dict:
    """Search only mixed-method histories with limit+1 distinct service days."""
    codes = (ultrasound, catheter)
    evidence = snapshot["evidence"]
    unknowns = []
    aux = {code: [r for r in evidence["auxiliary"] if r["active_as_of"] and r["fields"][1] == code] for code in codes}
    frequency = [r for r in evidence["frequency"] if r["active_as_of"]]
    exclusions = [r for kind, rows in evidence.items() if kind.startswith("exclusion_") for r in rows if r["active_as_of"]]
    for code in codes:
        if len(aux[code]) != 1:
            unknowns.append(f"{code}: expected exactly one active auxiliary row")
        rows = [r for r in frequency if r["fields"][1] == code]
        if not rows or not any(r["fields"][3] == "131" for r in rows):
            unknowns.append(f"{code}: no explicit active monthly frequency constraint")
        if len(aux[code]) == 1 and aux[code][0]["fields"][20] != "1":
            unknowns.append(f"{code}: auxiliary frequency flag is inconsistent/unsupported")
        for r in rows:
            fields = r["fields"]
            if fields[6] != "0":
                unknowns.append(f"{r['file']}:{r['line']}: unresolved frequency exception")
            if int(fields[5]) == 0:
                unknowns.append(f"{r['file']}:{r['line']}: zero frequency semantics not established")
            if fields[3] not in {"121", "131"}:
                unknowns.append(f"{r['file']}:{r['line']}: unsupported frequency unit {fields[3]}")
            elif fields[4] != {"121": "日", "131": "月"}[fields[3]]:
                unknowns.append(f"{r['file']}:{r['line']}: unit code/name mismatch")
    for r in exclusions:
        fields = r["fields"]
        if fields[1] == fields[3]:
            unknowns.append(f"{r['file']}:{r['line']}: same-code exclusion semantics unsupported")
        scope_index = {f"tables/{FILES[kind][0]}": index for kind, index in (("exclusion_day", 9), ("exclusion_month", 10), ("exclusion_simultaneous", 11), ("exclusion_week", 12))}[r["file"]]
        for code in {fields[1], fields[3]}:
            if len(aux[code]) == 1 and aux[code][0]["fields"][scope_index] != "1":
                unknowns.append(f"{code}: auxiliary exclusion flag is inconsistent/unsupported")
        if fields[6] != "0":
            unknowns.append(f"{r['file']}:{r['line']}: unresolved exclusion exception")
        if r["file"] == f"tables/{FILES['exclusion_week'][0]}":
            unknowns.append(f"{r['file']}:{r['line']}: weekly exclusion/history semantics unsupported")
    # This first adapter only searches short, distinct-day histories in one month.
    size = limit + 1
    if size > 28 or size > as_of.day:
        unknowns.append("bounded search requires limit+1 distinct days no later than as-of within its month (at most 28)")
    result = {"status": "unknown", "unknown_reasons": unknowns, "search_total": size}
    if unknowns:
        return result

    dates = [as_of - timedelta(days=offset) for offset in reversed(range(size))]
    if dates[0] < date.fromisoformat(snapshot["table_published_on"]):
        result["unknown_reasons"].append("candidate history precedes snapshot publication; earlier editions not reconstructed")
        return result
    # Check *all* retained target rows, including rows inactive on as-of. A row
    # that expired yesterday may still constrain an event two days ago. This
    # adapter refuses to reconstruct changes rather than dropping old rules.
    relevant_rows = [row for rows in evidence.values() for row in rows]
    if any(any(active(row["fields"], day) != row["active_as_of"] for day in dates) for row in relevant_rows):
        result["unknown_reasons"].append("row validity changes inside candidate history; earlier rule history not reconstructed")
        return result

    attempts = []
    for ultrasound_count in range(size - 1, 0, -1):
        counts = {ultrasound: ultrasound_count, catheter: size - ultrasound_count}
        failures = []
        for row in frequency:
            fields = row["fields"]
            observed = counts[fields[1]] if fields[3] == "131" else 1
            if observed > int(fields[5]):
                failures.append({"file": row["file"], "line": row["line"], "observed": observed, "limit": int(fields[5])})
        for row in exclusions:
            # All events are on distinct dates/sessions; day/simultaneous pairs
            # never co-occur. Any monthly pair blocks the mixed-method history.
            if row["file"] == f"tables/{FILES['exclusion_month'][0]}":
                failures.append({"file": row["file"], "line": row["line"], "reason": "monthly exclusion pair present"})
        attempts.append({"counts": counts, "projection_violations": failures})
        if not failures:
            event_codes = [ultrasound] * ultrasound_count + [catheter] * counts[catheter]
            result.update({
                "status": "bounded_projection_witness",
                "events": [{"patient": "synthetic-patient", "date": day.isoformat(), "session": index + 1, "code": code} for index, (day, code) in enumerate(zip(dates, event_codes))],
                "per_code_month_counts": counts,
                "projection_constraints_satisfied": True,
                "caller_supplied_text_limit_satisfied": size <= limit,
                "text_total_count": size,
                "assumptions": [
                    "The two codes denote the two methods of the same caller-identified textual item; mapping is not independently verified.",
                    "All events concern one patient at one institution, on distinct days and sessions in one calendar month.",
                    "This is the complete synthetic history for the two codes in that month; no earlier claims or other billed services are assumed.",
                    "Only explicit per-code day/month caps and exclusions whose endpoints are the two supplied codes are interpreted.",
                ],
                "attempts": attempts,
            })
            return result
    result.update({"status": "no_witness_in_bounded_projection", "attempts": attempts})
    return result


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--snapshot", type=Path, default=ROOT / "tensuhyo/ika/2026-10-13")
    result.add_argument("--ultrasound-code", required=True)
    result.add_argument("--catheter-code", required=True)
    result.add_argument("--as-of", required=True, type=date.fromisoformat, help="explicit YYYY-MM-DD; historical rules are not reconstructed")
    result.add_argument("--text-monthly-limit", required=True, type=int, help="patient-level sum across both methods; a caller-supplied premise")
    result.add_argument("--text-reference", required=True, help="text edition and article/page locator; not fetched or verified by this tool")
    result.add_argument("--output", type=Path, default=ROOT / "tensuhyo/audits/residual-urine.json")
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        require(bool(CODE.fullmatch(args.ultrasound_code)) and bool(CODE.fullmatch(args.catheter_code)), "codes must be nine decimal digits")
        require(args.ultrasound_code != args.catheter_code, "method codes must differ")
        require(args.text_monthly_limit > 0, "text-monthly-limit must be positive")
        require(bool(args.text_reference.strip()), "text-reference must not be empty")
        output = args.output.resolve()
        local_root = (ROOT / "tensuhyo").resolve()
        require(output.is_relative_to(local_root) and output != local_root / "README.md", "report output must remain under the ignored local tensuhyo directory")
        require(output.suffix == ".json" and not output.is_relative_to(args.snapshot.resolve()), "report must be JSON outside the source snapshot directory")
        snapshot = load_snapshot(args.snapshot, {args.ultrasound_code, args.catheter_code}, args.as_of)
        report = {
            "report_schema": "sanri.residual-urine-audit.v1",
            "scope": "bounded comparison of a caller-supplied text premise with a projection of a local CSV snapshot",
            "as_of": args.as_of.isoformat(),
            "text_premise": {"reference": args.text_reference, "monthly_patient_total_limit": args.text_monthly_limit, "verification": "caller_supplied_not_independently_verified"},
            "method_codes": {"ultrasound": args.ultrasound_code, "catheter": args.catheter_code},
            "snapshot": snapshot,
            "comparison": projection_witness(snapshot, args.ultrasound_code, args.catheter_code, args.text_monthly_limit, args.as_of),
            "limitations": [
                "This is neither a proof of an error in the official master nor a determination of allowed billing.",
                "The source PDF, notices, Q&A, code-to-text mapping and all clinical/facility conditions remain outside this audit.",
                "Inclusion and inpatient tables are structurally validated but their billing semantics are not evaluated.",
                "Relations to other codes, shared limits supplied by external rules and unstated exception semantics are not inferred.",
                "Dates are record-validity checks in this fixed snapshot, not reconstruction of previous editions or assurance of current applicability.",
                "SHA-256 checks establish consistency with the local manifest, not independent authenticity or correctness of that manifest.",
                "The synthetic history assumes no other claims; this tool does not evaluate incomplete real patient histories.",
            ],
        }
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"status": report["comparison"]["status"], "report": str(output), "validated_files": len(snapshot["files"])}, ensure_ascii=False))
        return 0
    except (AuditError, OSError, UnicodeError, json.JSONDecodeError, TypeError, KeyError) as error:
        print(f"audit error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

from collections import Counter
from pathlib import Path
import csv
import json
import re
import sys


GAP_RE = re.compile(r"<!--\s*BEDC-GAP:\s*([A-Z][A-Z0-9_-]*)\s*-->")
BLOCKED = "blocked-on-bedc"
TOKEN = "BEDC_GATE_C_SYNC"


def fail(errors: list[str]) -> None:
    print(f"{TOKEN}: gap metadata is inconsistent", file=sys.stderr)
    for error in errors:
        print(f"  {error}", file=sys.stderr)
    raise SystemExit(1)


def split_markdown_row(line: str) -> list[str]:
    row = line.strip()
    if row.startswith("|"):
        row = row[1:]
    if row.endswith("|"):
        row = row[:-1]
    return [cell.strip() for cell in row.split("|")]


def is_separator_row(cells: list[str]) -> bool:
    return bool(cells) and all(re.fullmatch(r":?-{3,}:?", cell.strip()) for cell in cells)


def load_json_rows(path: Path) -> list[dict[str, object]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data.get("rows")
    if not isinstance(rows, list):
      fail(["matrix must contain a top-level `rows` array"])
    return rows


def load_csv_rows(path: Path) -> list[dict[str, object]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle))


def load_markdown_rows(path: Path) -> list[dict[str, object]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(lines):
        if not line.lstrip().startswith("|"):
            continue
        header = split_markdown_row(line)
        if index + 1 >= len(lines):
            continue
        sep = split_markdown_row(lines[index + 1])
        if not is_separator_row(sep):
            continue
        rows: list[dict[str, object]] = []
        for body in lines[index + 2:]:
            if not body.lstrip().startswith("|"):
                break
            cells = split_markdown_row(body)
            if len(cells) != len(header):
                continue
            rows.append(dict(zip(header, cells)))
        return rows
    return []


def load_rows(path: Path) -> list[dict[str, object]]:
    suffix = path.suffix.lower()
    if suffix == ".json":
        return load_json_rows(path)
    if suffix == ".csv":
        return load_csv_rows(path)
    if suffix in {".md", ".markdown"}:
        return load_markdown_rows(path)
    fail([f"unsupported matrix format: {path}"])


def coerce_gap_list(raw: object) -> tuple[list[str], str | None]:
    if raw is None:
        return [], None
    if isinstance(raw, list):
        if all(isinstance(item, str) for item in raw):
            return raw, None
        return [], "bedc_gaps list must contain only strings"
    if isinstance(raw, str):
        text = raw.strip()
        if not text or text in {"-", "[]"}:
            return [], None
        parts = [part.strip() for part in re.split(r"[,; ]+", text) if part.strip()]
        return parts, None
    return [], "bedc_gaps must be a string or string array"


def row_id(row: dict[str, object], index: int) -> str:
    for key in ("id", "ID", "bridge id", "mathlib target", "BEDC source"):
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return f"row-{index + 1}"


def row_status(row: dict[str, object]) -> str:
    for key in ("status", "bridge status"):
        value = row.get(key)
        if isinstance(value, str):
            return value.strip()
    return ""


def row_gaps(row: dict[str, object]) -> object:
    for key in ("bedc_gaps", "BEDC gaps", "gaps"):
        if key in row:
            return row[key]
    return None


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: check_gap_sync.py MISSING_IN_BEDC.md MATRIX")

    missing_path = Path(sys.argv[1])
    matrix_path = Path(sys.argv[2])
    markdown = missing_path.read_text(encoding="utf-8")
    missing_ids = GAP_RE.findall(markdown)

    errors: list[str] = []
    duplicates = sorted(gap for gap, count in Counter(missing_ids).items() if count > 1)
    if duplicates:
        errors.append(
            "duplicate BEDC-GAP markers in MISSING_IN_BEDC.md: " + ", ".join(duplicates)
        )

    rows = load_rows(matrix_path)
    blocked_ids: set[str] = set()
    for index, row in enumerate(rows):
        rid = row_id(row, index)
        gaps, gap_error = coerce_gap_list(row_gaps(row))
        if gap_error is not None:
            errors.append(f"{rid}: {gap_error}")
            continue
        if len(gaps) != len(set(gaps)):
            errors.append(f"{rid}: duplicate gap IDs inside row")
        if row_status(row) == BLOCKED:
            if not gaps:
                errors.append(f"{rid}: blocked-on-bedc row has no bedc_gaps")
            blocked_ids.update(gaps)
        elif gaps:
            errors.append(f"{rid}: non-blocked row still carries bedc_gaps")

    missing_set = set(missing_ids)
    absent_from_matrix = sorted(missing_set - blocked_ids)
    absent_from_missing = sorted(blocked_ids - missing_set)
    if absent_from_matrix:
        errors.append(
            "MISSING_IN_BEDC IDs unused by blocked matrix rows: "
            + ", ".join(absent_from_matrix)
        )
    if absent_from_missing:
        errors.append(
            "blocked matrix IDs absent from MISSING_IN_BEDC.md: "
            + ", ".join(absent_from_missing)
        )

    if errors:
        fail(errors)
    print("[gap-sync] PASS: BEDC gap markers match blocked matrix rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

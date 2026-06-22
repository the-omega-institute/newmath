from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import json
import re
from typing import Any


ROW_METADATA_RE = re.compile(r"<!--\s*bedc-bridge-row:\s*(\{.*?\})\s*-->")
DECL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


@dataclass
class MatrixRow:
    line_no: int
    cells: dict[str, str]
    metadata: dict[str, Any]


class MatrixMetadataError(Exception):
    pass


def split_markdown_row(line: str) -> list[str]:
    row = line.strip()
    if row.startswith("|"):
        row = row[1:]
    if row.endswith("|"):
        row = row[:-1]
    return [cell.strip() for cell in row.split("|")]


def is_separator_row(cells: list[str]) -> bool:
    return bool(cells) and all(re.fullmatch(r":?-{3,}:?", cell.strip()) for cell in cells)


def strip_metadata(text: str) -> str:
    return ROW_METADATA_RE.sub("", text).strip()


def parse_metadata(line: str, line_no: int) -> dict[str, Any]:
    matches = ROW_METADATA_RE.findall(line)
    if len(matches) != 1:
        raise MatrixMetadataError(
            f"line {line_no}: expected exactly one bedc-bridge-row metadata comment"
        )
    try:
        data = json.loads(matches[0])
    except json.JSONDecodeError as exc:
        raise MatrixMetadataError(f"line {line_no}: invalid row metadata JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise MatrixMetadataError(f"line {line_no}: row metadata must be a JSON object")
    return data


def load_markdown_rows(path: Path) -> list[MatrixRow]:
    lines = path.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(lines):
        if not line.lstrip().startswith("|"):
            continue
        header = [strip_metadata(cell) for cell in split_markdown_row(line)]
        if index + 1 >= len(lines):
            continue
        sep = split_markdown_row(lines[index + 1])
        if not is_separator_row(sep):
            continue
        if "row_id" not in header:
            raise MatrixMetadataError("MATRIX table must contain a row_id column")
        rows: list[MatrixRow] = []
        for line_no, body in enumerate(lines[index + 2 :], start=index + 3):
            if not body.lstrip().startswith("|"):
                break
            metadata = parse_metadata(body, line_no)
            cells = [strip_metadata(cell) for cell in split_markdown_row(body)]
            if len(cells) != len(header):
                raise MatrixMetadataError(
                    f"line {line_no}: row has {len(cells)} cells, expected {len(header)}"
                )
            row = MatrixRow(line_no=line_no, cells=dict(zip(header, cells)), metadata=metadata)
            validate_common_row(row)
            rows.append(row)
        return rows
    raise MatrixMetadataError("MATRIX table not found")


def validate_decl(value: Any, field: str, row: MatrixRow) -> str:
    if not isinstance(value, str) or not value.strip():
        raise MatrixMetadataError(f"line {row.line_no}: metadata field `{field}` must be non-empty")
    text = value.strip()
    if DECL_RE.fullmatch(text) is None:
        raise MatrixMetadataError(f"line {row.line_no}: `{field}` is not a Lean declaration name")
    return text


def validate_axioms(value: Any, row: MatrixRow) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata field `expected_axioms` must be a string array"
        )
    axioms = [item.strip() for item in value]
    if any(not item for item in axioms):
        raise MatrixMetadataError(f"line {row.line_no}: empty expected axiom name")
    for item in axioms:
        if DECL_RE.fullmatch(item) is None:
            raise MatrixMetadataError(f"line {row.line_no}: invalid expected axiom name `{item}`")
    if axioms != sorted(axioms):
        raise MatrixMetadataError(f"line {row.line_no}: expected_axioms must be sorted")
    dupes = sorted(name for name, count in Counter(axioms).items() if count > 1)
    if dupes:
        raise MatrixMetadataError(
            f"line {row.line_no}: duplicate expected axiom(s): {', '.join(dupes)}"
        )
    return axioms


def validate_common_row(row: MatrixRow) -> None:
    row_id = row.cells.get("row_id", "").strip()
    if not row_id:
        raise MatrixMetadataError(f"line {row.line_no}: row_id cell is empty")
    meta_row_id = row.metadata.get("row_id")
    if meta_row_id != row_id:
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata row_id `{meta_row_id}` does not match cell `{row_id}`"
        )
    kind = row.metadata.get("kind")
    allowed_kinds = {
        "exported_core",
        "subsumed_by_core",
        "measured_boundary",
        "out_of_scope_generic",
    }
    if kind not in allowed_kinds:
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata kind must be one of "
            + ", ".join(sorted(allowed_kinds))
        )
    status = row.cells.get("bridge status", "")
    if kind == "exported_core" and "adequacy" not in status:
        raise MatrixMetadataError(f"line {row.line_no}: exported_core row must have adequacy status")
    if kind == "measured_boundary" and "boundary fact" not in status:
        raise MatrixMetadataError(f"line {row.line_no}: boundary row must have boundary fact status")


def load_rows(path: Path) -> list[MatrixRow]:
    if path.suffix.lower() not in {".md", ".markdown"}:
        raise MatrixMetadataError(f"unsupported MATRIX format: {path}")
    rows = load_markdown_rows(path)
    row_ids = [row.cells["row_id"] for row in rows]
    dupes = sorted(row_id for row_id, count in Counter(row_ids).items() if count > 1)
    if dupes:
        raise MatrixMetadataError("duplicate row_id value(s): " + ", ".join(dupes))
    return rows


def classification_rows(path: Path) -> list[tuple[str, str, str, str]]:
    out: list[tuple[str, str, str, str]] = []
    for row in load_rows(path):
        classify = row.metadata.get("classification", True)
        if not isinstance(classify, bool):
            raise MatrixMetadataError(
                f"line {row.line_no}: metadata field `classification` must be boolean"
            )
        if not classify:
            continue
        mathlib_class = validate_decl(row.metadata.get("mathlib_class"), "mathlib_class", row)
        mathlib_instance = validate_decl(row.metadata.get("mathlib_instance"), "mathlib_instance", row)
        out.append((row.cells["row_id"], row.metadata["kind"], mathlib_class, mathlib_instance))
    return out


def export_rows(path: Path) -> list[tuple[str, str, str, str]]:
    out: list[tuple[str, str, str, str]] = []
    for row in load_rows(path):
        if row.metadata["kind"] != "exported_core":
            continue
        witness = validate_decl(row.metadata.get("export_witness"), "export_witness", row)
        mathlib_class = validate_decl(row.metadata.get("mathlib_class"), "mathlib_class", row)
        mathlib_instance = validate_decl(row.metadata.get("mathlib_instance"), "mathlib_instance", row)
        out.append((row.cells["row_id"], witness, mathlib_class, mathlib_instance))
    return out


def boundary_rows(path: Path) -> list[tuple[str, str, list[str], str, str]]:
    out: list[tuple[str, str, list[str], str, str]] = []
    for row in load_rows(path):
        if row.metadata["kind"] != "measured_boundary":
            continue
        decl = validate_decl(row.metadata.get("boundary_decl"), "boundary_decl", row)
        axioms = validate_axioms(row.metadata.get("expected_axioms"), row)
        mathlib_class = validate_decl(row.metadata.get("mathlib_class"), "mathlib_class", row)
        mathlib_instance = validate_decl(row.metadata.get("mathlib_instance"), "mathlib_instance", row)
        out.append((row.cells["row_id"], decl, axioms, mathlib_class, mathlib_instance))
    return out


def lean_string(value: str) -> str:
    return json.dumps(value)


def lean_name(value: str) -> str:
    if DECL_RE.fullmatch(value) is None:
        raise MatrixMetadataError(f"invalid Lean declaration name: {value}")
    return f"`{value}"

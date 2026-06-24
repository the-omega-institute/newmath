from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import json
import re
from typing import Any


ROW_METADATA_RE = re.compile(r"<!--\s*bedc-bridge-row:\s*(\{.*?\})\s*-->")
DECL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
PLACE_VALUES = {"finite_p", "infinite_archimedean", "object_base", "n_a"}
LOCATEDNESS_VALUES = {"located", "arbitrary", "n_a"}
QUOTIENT_STATUS_VALUES = {"structural_quotient", "quotient_free", "n_a"}
AXIOM_STATUS_VALUES = {
    "eliminated",
    "mathlib_intrinsic",
    "structural_quotient",
    "principled_irreducible",
    "unprobed",
}


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


def validate_axiom_list(value: Any, row: MatrixRow, field: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata field `{field}` must be a string array"
        )
    axioms = [item.strip() for item in value]
    if any(not item for item in axioms):
        raise MatrixMetadataError(f"line {row.line_no}: empty `{field}` axiom name")
    for item in axioms:
        if DECL_RE.fullmatch(item) is None:
            raise MatrixMetadataError(f"line {row.line_no}: invalid `{field}` axiom name `{item}`")
    if axioms != sorted(axioms):
        raise MatrixMetadataError(f"line {row.line_no}: `{field}` must be sorted")
    dupes = sorted(name for name, count in Counter(axioms).items() if count > 1)
    if dupes:
        raise MatrixMetadataError(
            f"line {row.line_no}: duplicate `{field}` axiom(s): {', '.join(dupes)}"
        )
    return axioms


def validate_axioms(value: Any, row: MatrixRow) -> list[str]:
    return validate_axiom_list(value, row, "expected_axioms")


def validate_axiom_status(value: Any, row: MatrixRow, footprint: list[str]) -> dict[str, str]:
    if value is None:
        raise MatrixMetadataError(
            f"BEDC_GATE_E_AXIOM_UNCLASSIFIED: line {row.line_no}: "
            "metadata field `axiom_status` is required for boundary footprints"
        )
    if not isinstance(value, dict):
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata field `axiom_status` must be an object"
        )
    out: dict[str, str] = {}
    for key, status in value.items():
        if not isinstance(key, str) or DECL_RE.fullmatch(key) is None:
            raise MatrixMetadataError(
                f"line {row.line_no}: invalid `axiom_status` axiom name `{key}`"
            )
        if not isinstance(status, str) or status not in AXIOM_STATUS_VALUES:
            raise MatrixMetadataError(
                f"line {row.line_no}: `axiom_status.{key}` must be one of "
                + ", ".join(sorted(AXIOM_STATUS_VALUES))
            )
        out[key] = status
    for axiom in footprint:
        status = out.get(axiom)
        if status is None or status == "unprobed":
            raise MatrixMetadataError(
                f"BEDC_GATE_E_AXIOM_UNCLASSIFIED: line {row.line_no}: "
                f"`{axiom}` in bedc_irreducible_footprint requires classified "
                "`axiom_status`"
            )
    return out


def validate_enum(value: Any, field: str, allowed: set[str], row: MatrixRow) -> str:
    if not isinstance(value, str) or value not in allowed:
        raise MatrixMetadataError(
            f"line {row.line_no}: metadata field `{field}` must be one of "
            + ", ".join(sorted(allowed))
        )
    return value


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
        "bedc_constructive_core",
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
        if row.metadata["kind"] not in {"exported_core", "bedc_constructive_core"}:
            continue
        witness = validate_decl(row.metadata.get("export_witness"), "export_witness", row)
        mathlib_class = validate_decl(row.metadata.get("mathlib_class"), "mathlib_class", row)
        mathlib_instance = validate_decl(row.metadata.get("mathlib_instance"), "mathlib_instance", row)
        out.append((row.cells["row_id"], witness, mathlib_class, mathlib_instance))
    return out


def optional_empty_string(value: Any, field: str, row: MatrixRow) -> str:
    if value is None:
        return ""
    if not isinstance(value, str):
        raise MatrixMetadataError(f"line {row.line_no}: metadata field `{field}` must be a string")
    return value.strip()


def correspondence_rows(path: Path) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for row in load_rows(path):
        kind = row.metadata["kind"]
        correspondence = optional_empty_string(
            row.metadata.get("mathlib_correspondence_decl"),
            "mathlib_correspondence_decl",
            row,
        )
        if kind == "bedc_constructive_core":
            if correspondence:
                raise MatrixMetadataError(
                    f"line {row.line_no}: bedc_constructive_core row must leave "
                    "`mathlib_correspondence_decl` empty"
                )
            continue
        if kind != "exported_core":
            continue
        if not correspondence:
            raise MatrixMetadataError(
                f"line {row.line_no}: exported_core row requires "
                "`mathlib_correspondence_decl`"
            )
        correspondence_decl = validate_decl(
            correspondence,
            "mathlib_correspondence_decl",
            row,
        )
        mathlib_decl = validate_decl(row.metadata.get("mathlib_decl"), "mathlib_decl", row)
        bedc_decl = validate_decl(
            row.metadata.get("bedc_irreducible_decl", row.metadata.get("export_witness")),
            "bedc_irreducible_decl",
            row,
        )
        out.append(
            {
                "row_id": row.cells["row_id"],
                "mathlib_correspondence_decl": correspondence_decl,
                "mathlib_decl": mathlib_decl,
                "bedc_irreducible_decl": bedc_decl,
            }
        )
    return out


def boundary_rows(path: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for row in load_rows(path):
        if row.metadata["kind"] != "measured_boundary":
            continue
        mathlib_decl = validate_decl(
            row.metadata.get("mathlib_decl", row.metadata.get("boundary_decl")),
            "mathlib_decl",
            row,
        )
        mathlib_footprint = validate_axiom_list(
            row.metadata.get("mathlib_footprint", row.metadata.get("expected_axioms")),
            row,
            "mathlib_footprint",
        )
        bedc_irreducible_decl = validate_decl(
            row.metadata.get("bedc_irreducible_decl", mathlib_decl),
            "bedc_irreducible_decl",
            row,
        )
        bedc_irreducible_footprint = validate_axiom_list(
            row.metadata.get(
                "bedc_irreducible_footprint",
                row.metadata.get("expected_axioms"),
            ),
            row,
            "bedc_irreducible_footprint",
        )
        choice_status = validate_enum(
            row.metadata.get("choice_status"),
            "choice_status",
            {"eliminated", "principled_irreducible", "unprobed"},
            row,
        )
        place = validate_enum(row.metadata.get("place", "n_a"), "place", PLACE_VALUES, row)
        locatedness = validate_enum(
            row.metadata.get("locatedness", "n_a"),
            "locatedness",
            LOCATEDNESS_VALUES,
            row,
        )
        quotient_status = validate_enum(
            row.metadata.get("quotient_status", "n_a"),
            "quotient_status",
            QUOTIENT_STATUS_VALUES,
            row,
        )
        probe_status = validate_enum(
            row.metadata.get("probe_status", "unprobed"),
            "probe_status",
            {"probed", "unprobed"},
            row,
        )
        if choice_status == "eliminated" and probe_status != "probed":
            raise MatrixMetadataError(
                f"line {row.line_no}: choice_status `eliminated` requires probe_status `probed`"
            )
        if choice_status == "unprobed" and probe_status != "unprobed":
            raise MatrixMetadataError(
                f"line {row.line_no}: choice_status `unprobed` requires probe_status `unprobed`"
            )
        axiom_status = validate_axiom_status(
            row.metadata.get("axiom_status"),
            row,
            bedc_irreducible_footprint,
        )
        mathlib_class = validate_decl(row.metadata.get("mathlib_class"), "mathlib_class", row)
        mathlib_instance = validate_decl(row.metadata.get("mathlib_instance"), "mathlib_instance", row)
        out.append(
            {
                "row_id": row.cells["row_id"],
                "mathlib_decl": mathlib_decl,
                "mathlib_footprint": mathlib_footprint,
                "bedc_irreducible_decl": bedc_irreducible_decl,
                "bedc_irreducible_footprint": bedc_irreducible_footprint,
                "choice_status": choice_status,
                "place": place,
                "locatedness": locatedness,
                "quotient_status": quotient_status,
                "probe_status": probe_status,
                "axiom_status": axiom_status,
                "mathlib_class": mathlib_class,
                "mathlib_instance": mathlib_instance,
            }
        )
    return out


def lean_string(value: str) -> str:
    return json.dumps(value)


def lean_name(value: str) -> str:
    if DECL_RE.fullmatch(value) is None:
        raise MatrixMetadataError(f"invalid Lean declaration name: {value}")
    return f"`{value}"

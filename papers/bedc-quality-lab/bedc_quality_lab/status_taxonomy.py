"""Public status-axis taxonomy for canonical report surfaces."""

from __future__ import annotations

from typing import Any, Mapping


REPORT_BUILD_STATUS = frozenset({"pass", "fail", "error", "skipped"})
SCIENTIFIC_CLAIM_STATUS = frozenset(
    {
        "pass",
        "fail",
        "bounded-negative",
        "scoped-boundary",
        "blocked",
        "ready",
        "not-applicable",
    }
)
HARDGATE_STATUS = frozenset({"pass", "fail", "not-applicable"})
LADDER_STATE = frozenset(
    {
        "open",
        "closed",
        "boundary",
        "blocked",
        "ready",
        "l1-scaling-blocked",
        "l1-bounded-negative",
        "l1-scaling-evidence-eligible",
        "not-applicable",
    }
)
DECISION_STATUS = frozenset(
    {
        "pass",
        "fail",
        "blocked",
        "bounded-negative",
        "scoped-boundary",
        "ready",
        "scaling-evidence-eligible",
        "not-applicable",
    }
)

STATUS_AXIS_DOMAINS = {
    "report_build_status": REPORT_BUILD_STATUS,
    "scientific_claim_status": SCIENTIFIC_CLAIM_STATUS,
    "hardgate_status": HARDGATE_STATUS,
    "ladder_state": LADDER_STATE,
    "decision_status": DECISION_STATUS,
}

HARDGATE_SCOPES = frozenset({"report-integrity", "owner-scientific", "not-applicable"})

PROMOTION_BLOCKING_VALUES = {
    "report_build_status": frozenset({"fail", "error", "skipped"}),
    "scientific_claim_status": frozenset({"fail", "bounded-negative", "scoped-boundary", "blocked"}),
    "hardgate_status": frozenset({"fail"}),
    "ladder_state": frozenset({"closed", "boundary", "blocked", "l1-scaling-blocked", "l1-bounded-negative"}),
    "decision_status": frozenset({"fail", "blocked", "bounded-negative", "scoped-boundary"}),
}


def _as_status(value: Any) -> str:
    if value is None:
        return "not-applicable"
    return str(value)


def status_cell(
    axis: str,
    value: Any,
    *,
    source_pointer: str | None = None,
    hardgate_scope: str | None = None,
) -> dict[str, Any]:
    """Build a renderable status cell for one public axis."""

    status_value = _as_status(value)
    scope = hardgate_scope
    if axis == "hardgate_status" and scope is None:
        scope = "not-applicable" if status_value == "not-applicable" else "owner-scientific"

    cell: dict[str, Any] = {
        "axis": axis,
        "value": status_value,
        "render": status_value,
        "blocks_report": axis == "report_build_status" and status_value != "pass",
        "blocks_promotion": status_value in PROMOTION_BLOCKING_VALUES.get(axis, frozenset()),
        "source_pointer": source_pointer,
    }
    if axis == "hardgate_status":
        cell["hardgate_scope"] = scope
        if status_value == "fail" and scope == "report-integrity":
            cell["blocks_report"] = True
        elif status_value == "fail" and scope == "owner-scientific":
            cell["blocks_report"] = False
            cell["blocks_promotion"] = True

    validation = validate_status_cell(cell)
    if validation["status"] != "pass":
        cell["blocks_report"] = True
        cell["blocks_promotion"] = True
    return cell


def validate_status_cell(cell: Mapping[str, Any]) -> dict[str, Any]:
    """Validate one public status cell against its declared axis."""

    errors: list[str] = []
    axis = cell.get("axis")
    value = cell.get("value")
    if axis not in STATUS_AXIS_DOMAINS:
        errors.append(f"unknown status axis: {axis}")
    elif value not in STATUS_AXIS_DOMAINS[axis]:
        errors.append(f"{value} is not valid for {axis}")
    if axis == "hardgate_status":
        scope = cell.get("hardgate_scope")
        if scope not in HARDGATE_SCOPES:
            errors.append(f"unknown hardgate scope: {scope}")
        if value in {"pass", "fail"} and scope == "not-applicable":
            errors.append("applicable hardgate status requires a hardgate scope")
    return {"status": "fail" if errors else "pass", "errors": errors}


def validate_status_cells(cells: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    """Validate a complete public status row."""

    errors: list[str] = []
    for axis in STATUS_AXIS_DOMAINS:
        cell = cells.get(axis)
        if not isinstance(cell, Mapping):
            errors.append(f"missing status cell: {axis}")
            continue
        validation = validate_status_cell(cell)
        errors.extend(str(error) for error in validation["errors"])
    return {"status": "fail" if errors else "pass", "errors": errors}


def render_status_cell(cell: Mapping[str, Any]) -> str:
    """Return the public display value for a status cell."""

    render = cell.get("render")
    return str(render if render is not None else cell.get("value", "not-applicable"))

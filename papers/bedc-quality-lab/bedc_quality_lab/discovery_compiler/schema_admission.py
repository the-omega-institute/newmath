"""Schema admission checks for canonical validation envelopes."""

from __future__ import annotations

from dataclasses import dataclass
import importlib
from typing import Any, Literal, Mapping, Sequence


SCHEMA_ADMISSION_HARDGATE_IDS = (
    "SCHEMA-MIN-HG1-primitive-basis",
    "SCHEMA-MIN-HG2-owner-pointer",
    "SCHEMA-MIN-HG3-validator-binding",
    "SCHEMA-MIN-HG4-downgrade-policy",
    "SCHEMA-MIN-HG5-public-pointer-only",
)

AdmissionStatus = Literal["pass", "fail"]


@dataclass(frozen=True)
class SchemaAdmissionRow:
    schema_id: str
    primitive_basis: bool
    owner_pointer: str
    validator_ref: str
    downgrade_policy: str
    status: AdmissionStatus
    reason: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema_id": self.schema_id,
            "primitive_basis": self.primitive_basis,
            "owner_pointer": self.owner_pointer,
            "validator_ref": self.validator_ref,
            "downgrade_policy": self.downgrade_policy,
            "status": self.status,
            "reason": self.reason,
        }


@dataclass(frozen=True)
class SchemaAdmissionResult:
    status: AdmissionStatus
    rows: tuple[SchemaAdmissionRow, ...]
    hardgates: Mapping[str, Mapping[str, Any]]

    def as_dict(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "rows": [row.as_dict() for row in self.rows],
            "hardgates": {gate_id: dict(gate) for gate_id, gate in self.hardgates.items()},
        }


def _text(value: Any) -> str:
    return value if isinstance(value, str) else ""


def _has_public_owner_pointer(value: str) -> bool:
    artifact, separator, pointer = value.partition(":")
    return artifact.startswith("reports/canonical/") and artifact.endswith(".json") and separator == ":" and pointer.startswith("$")


def _has_callable_validator_ref(value: str) -> bool:
    module_name, separator, callable_name = value.partition(":")
    if not separator:
        module_name, separator, callable_name = value.rpartition(".")
    if not module_name or not callable_name:
        return False
    try:
        current: Any = importlib.import_module(module_name)
        for part in callable_name.split("."):
            current = getattr(current, part)
    except (ImportError, AttributeError):
        return False
    return callable(current)


def _row_from_mapping(value: Mapping[str, Any]) -> SchemaAdmissionRow:
    schema_id = _text(value.get("schema_id"))
    primitive_basis = value.get("primitive_basis") is True
    owner_pointer = _text(value.get("owner_pointer"))
    validator_ref = _text(value.get("validator_ref"))
    downgrade_policy = _text(value.get("downgrade_policy"))
    checks = (
        bool(schema_id),
        primitive_basis,
        bool(owner_pointer),
        _has_callable_validator_ref(validator_ref),
        bool(downgrade_policy),
        _has_public_owner_pointer(owner_pointer),
    )
    status: AdmissionStatus = "pass" if all(checks) else "fail"
    reason = "schema admission fields are present" if status == "pass" else "schema admission fields are incomplete"
    return SchemaAdmissionRow(
        schema_id=schema_id,
        primitive_basis=primitive_basis,
        owner_pointer=owner_pointer,
        validator_ref=validator_ref,
        downgrade_policy=downgrade_policy,
        status=status,
        reason=reason,
    )


def _gate(gate_id: str, rows: Sequence[SchemaAdmissionRow]) -> dict[str, Any]:
    if gate_id == "SCHEMA-MIN-HG1-primitive-basis":
        failed = [index for index, row in enumerate(rows) if not row.primitive_basis]
        reason = "primitive_basis must be true"
    elif gate_id == "SCHEMA-MIN-HG2-owner-pointer":
        failed = [index for index, row in enumerate(rows) if not row.owner_pointer]
        reason = "owner_pointer must identify the owning public payload"
    elif gate_id == "SCHEMA-MIN-HG3-validator-binding":
        failed = [index for index, row in enumerate(rows) if not _has_callable_validator_ref(row.validator_ref)]
        reason = "validator_ref must name a callable validator"
    elif gate_id == "SCHEMA-MIN-HG4-downgrade-policy":
        failed = [index for index, row in enumerate(rows) if not row.downgrade_policy]
        reason = "downgrade_policy must be explicit"
    elif gate_id == "SCHEMA-MIN-HG5-public-pointer-only":
        failed = [index for index, row in enumerate(rows) if not _has_public_owner_pointer(row.owner_pointer)]
        reason = "owner_pointer must target a public canonical JSON payload"
    else:  # pragma: no cover - guarded by the constant tuple
        raise ValueError(f"unknown schema admission gate: {gate_id}")
    return {
        "status": "pass" if not failed else "fail",
        "reason": reason if failed else "pass",
        "row_indexes": failed,
    }


def validate_schema_admission(rows: Sequence[Mapping[str, Any]]) -> SchemaAdmissionResult:
    admitted_rows = tuple(_row_from_mapping(row) for row in rows)
    hardgates = {gate_id: _gate(gate_id, admitted_rows) for gate_id in SCHEMA_ADMISSION_HARDGATE_IDS}
    status: AdmissionStatus = "pass" if all(gate["status"] == "pass" for gate in hardgates.values()) else "fail"
    return SchemaAdmissionResult(status=status, rows=admitted_rows, hardgates=hardgates)


__all__ = [
    "SCHEMA_ADMISSION_HARDGATE_IDS",
    "SchemaAdmissionResult",
    "SchemaAdmissionRow",
    "validate_schema_admission",
]

"""Pointer-only DGT model card projection."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, NamedTuple, Sequence


SCHEMA_ID = "bedc-quality-lab:dgt-model-card"
CARD_ID = "bedc-quality-lab:dgt-model-card"
PRODUCER = "scripts/run_dgt_model_card.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-model-card.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-model-card.md"
DEFAULT_GENERATED_AT = "2026-06-12T00:00:00+08:00"
INDEX_EVIDENCE_PROVENANCE_POINTER = "reports/canonical/index.json:$.evidence_provenance"

REQUIRED_NOT_INTENDED_LITERALS = (
    "bounded BEDC prototype",
    "not production model",
    "not LLM replacement",
    "not global Transformer superiority",
    "current L1 evidence invalid as fair architecture comparison",
)

REQUIRED_KEYS = (
    "schema_id",
    "card_id",
    "source_artifacts",
    "intended_use",
    "not_intended_use",
    "known_failure_modes",
    "evaluation_boundaries",
    "training_facts",
    "upstream_status",
    "card_hardgates",
    "not_claimed",
)

SOURCE_POINTERS = {
    "dgt-l0-controls": {
        "owner_issue": "github:issue:1200",
        "pointer": "reports/canonical/dgt-l0-controls.json:$.l0_toy_projection",
    },
    "dgt-l1-controls": {
        "owner_issue": "github:issue:1212",
        "pointer": "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection",
    },
    "fair-l1-decision": {
        "owner_issue": "github:issue:1212",
        "pointer": "reports/canonical/fair-l1-decision.json:$.ladder_state_projection",
    },
    "dgt-base-undertraining-audit": {
        "owner_issue": "github:issue:1196",
        "pointer": "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit",
    },
    "dgt-ablation-null-decomposition": {
        "owner_issue": "github:issue:1206",
        "pointer": "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition",
    },
    "discovery-gated-transformer": {
        "owner_issue": "github:issue:1201",
        "pointer": "reports/canonical/discovery-gated-transformer.json:$",
    },
    "canonical-index-evidence-provenance": {
        "owner_issue": "canonical-index",
        "pointer": INDEX_EVIDENCE_PROVENANCE_POINTER,
    },
}

CONSTRUCT_VALIDITY_POINTERS = {
    "dgt-l0-controls": "reports/canonical/dgt-l0-controls.json:$.construct_validity_hardgates",
    "dgt-l1-controls": "reports/canonical/dgt-l1-controls.json:$.construct_validity_hardgates",
}


class OwnerProjectionTable(NamedTuple):
    path: str
    gate_id: str
    identity_keys: tuple[str, ...]
    value_keys: tuple[str, ...]


@dataclass(frozen=True)
class CardGateError:
    gate_id: str
    path: str
    message: str

    def as_dict(self) -> dict[str, str]:
        return {"gate_id": self.gate_id, "path": self.path, "message": self.message}


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _split_artifact_pointer(artifact_pointer: str) -> tuple[str, str]:
    if ":" not in artifact_pointer:
        raise ValueError(f"invalid artifact pointer: {artifact_pointer}")
    artifact, pointer = artifact_pointer.split(":", 1)
    if not artifact or not pointer:
        raise ValueError(f"invalid artifact pointer: {artifact_pointer}")
    return artifact, pointer


def _load_json(root: Path, artifact: str) -> tuple[str, dict[str, Any] | None, str | None]:
    path = root / artifact
    digest = _file_digest(path)
    if digest is None:
        return "missing", None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid", None, digest
    if not isinstance(payload, dict):
        return "invalid", None, digest
    return "resolved", payload, digest


def _pointer_value(payload: Any, pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        raise KeyError(pointer)
    cursor = payload
    for part in pointer[2:].split("."):
        if "[" in part and part.endswith("]"):
            name, index_text = part[:-1].split("[", 1)
            if name:
                if not isinstance(cursor, Mapping) or name not in cursor:
                    raise KeyError(pointer)
                cursor = cursor[name]
            if not isinstance(cursor, Sequence) or isinstance(cursor, (str, bytes)):
                raise KeyError(pointer)
            cursor = cursor[int(index_text)]
            continue
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
            continue
        raise KeyError(pointer)
    return cursor


def _resolve_artifact_pointer(root: Path, artifact_pointer: str) -> tuple[str, Any, str | None]:
    artifact, pointer = _split_artifact_pointer(artifact_pointer)
    status, payload, digest = _load_json(root, artifact)
    if status != "resolved" or payload is None:
        return status, None, digest
    try:
        return "resolved", _pointer_value(payload, pointer), digest
    except (KeyError, IndexError, ValueError):
        return "pointer-missing", None, digest


def _source_records(root: Path) -> tuple[list[dict[str, Any]], dict[str, Any], list[str]]:
    records: list[dict[str, Any]] = []
    resolved: dict[str, Any] = {}
    missing_refs: list[str] = []
    for owner, spec in SOURCE_POINTERS.items():
        artifact, pointer = _split_artifact_pointer(spec["pointer"])
        artifact_status, payload, digest = _load_json(root, artifact)
        pointer_status = artifact_status
        value = None
        if artifact_status == "resolved" and payload is not None:
            try:
                value = _pointer_value(payload, pointer)
                pointer_status = "resolved"
                if spec["pointer"] == INDEX_EVIDENCE_PROVENANCE_POINTER:
                    digest = _json_digest(value)
            except (KeyError, IndexError, ValueError):
                pointer_status = "pointer-missing"
                if spec["pointer"] == INDEX_EVIDENCE_PROVENANCE_POINTER:
                    digest = None
        if pointer_status != "resolved":
            missing_refs.append(spec["pointer"])
        else:
            resolved[owner] = value
        records.append(
            {
                "source_owner": owner,
                "owner_issue": spec["owner_issue"],
                "artifact": artifact,
                "pointer": pointer,
                "source_pointer": spec["pointer"],
                "status": pointer_status,
                "sha256": digest,
            }
        )
    return records, resolved, missing_refs


def _owner_status_cell(
    owner: str,
    artifact_pointer: str,
    status: Any,
    *,
    source_artifacts: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    artifact, pointer = _split_artifact_pointer(artifact_pointer)
    record = next((row for row in source_artifacts if row["artifact"] == artifact), None)
    digest = None if record is None else record.get("sha256")
    return {
        "source_owner": owner,
        "source_pointer": artifact_pointer,
        "source_digest": digest,
        "status": status,
    }


def _metric_cell(
    *,
    metric: str,
    value: Any,
    source_owner: str,
    source_pointer: str,
    interpretation: str,
) -> dict[str, Any]:
    return {
        "metric": metric,
        "value": value,
        "source_owner": source_owner,
        "source_pointer": source_pointer,
        "interpretation": interpretation,
    }


def _dig(mapping: Mapping[str, Any], path: Sequence[str], default: Any = None) -> Any:
    cursor: Any = mapping
    for key in path:
        if not isinstance(cursor, Mapping) or key not in cursor:
            return default
        cursor = cursor[key]
    return cursor


def _mapping_rows(value: Any) -> list[Mapping[str, Any]]:
    return [row for row in value if isinstance(row, Mapping)] if isinstance(value, list) else []


def _mapping_row_items(value: Any) -> list[tuple[int, Mapping[str, Any]]]:
    return [(index, row) for index, row in enumerate(value) if isinstance(row, Mapping)] if isinstance(value, list) else []


def _expected_source_status(root: Path, source_pointer: str) -> tuple[str, str | None]:
    artifact, pointer = _split_artifact_pointer(source_pointer)
    artifact_status, payload, digest = _load_json(root, artifact)
    if artifact_status != "resolved" or payload is None:
        return artifact_status, digest
    try:
        value = _pointer_value(payload, pointer)
    except (KeyError, IndexError, ValueError):
        if source_pointer == INDEX_EVIDENCE_PROVENANCE_POINTER:
            return "pointer-missing", None
        return "pointer-missing", digest
    if source_pointer == INDEX_EVIDENCE_PROVENANCE_POINTER:
        return "resolved", _json_digest(value)
    return "resolved", digest


def _projection_identity(row: Mapping[str, Any], keys: Sequence[str]) -> tuple[Any, ...]:
    return tuple(row.get(key) for key in keys)


def _validate_projection_rows(
    rows: Any,
    expected_rows: Sequence[Mapping[str, Any]],
    table: OwnerProjectionTable,
) -> list[CardGateError]:
    if not isinstance(rows, list):
        return [CardGateError(table.gate_id, table.path, "owner projection rows missing")]
    errors: list[CardGateError] = []
    expected_by_identity = {
        _projection_identity(row, table.identity_keys): row
        for row in expected_rows
        if isinstance(row, Mapping)
    }
    seen: set[tuple[Any, ...]] = set()
    for index, row in enumerate(rows):
        row_path = f"{table.path}[{index}]"
        if not isinstance(row, Mapping):
            errors.append(CardGateError(table.gate_id, row_path, "owner projection row invalid"))
            continue
        identity = _projection_identity(row, table.identity_keys)
        if identity in seen:
            errors.append(CardGateError(table.gate_id, row_path, "duplicate owner projection row"))
            continue
        seen.add(identity)
        expected = expected_by_identity.get(identity)
        if expected is None:
            errors.append(CardGateError(table.gate_id, row_path, "unexpected owner projection row"))
            continue
        for key in table.value_keys:
            if key in expected and row.get(key) != expected.get(key):
                errors.append(
                    CardGateError(
                        table.gate_id,
                        f"{row_path}.{key}",
                        "owner projection field differs from recomputed evidence",
                    )
                )
    for identity in expected_by_identity:
        if identity not in seen:
            errors.append(CardGateError(table.gate_id, table.path, "expected owner projection row missing"))
    return errors


def _validate_projection_mapping(
    row: Any,
    expected: Mapping[str, Any],
    *,
    path: str,
    gate_id: str,
    value_keys: Sequence[str],
) -> list[CardGateError]:
    if not isinstance(row, Mapping):
        return [CardGateError(gate_id, path, "owner projection row missing")]
    return [
        CardGateError(gate_id, f"{path}.{key}", "owner projection field differs from recomputed evidence")
        for key in value_keys
        if key in expected and row.get(key) != expected.get(key)
    ]


def _not_intended_use() -> list[dict[str, str]]:
    return [
        {
            "literal": literal,
            "source_owner": "maintainer-policy",
            "source_pointer": "github:issue:1220",
        }
        for literal in REQUIRED_NOT_INTENDED_LITERALS
    ]


def _intended_use(resolved: Mapping[str, Any]) -> list[dict[str, str]]:
    dgt = resolved.get("discovery-gated-transformer")
    model_pointer = "reports/canonical/discovery-gated-transformer.json:$.model_id"
    if not isinstance(dgt, Mapping) or "model_id" not in dgt:
        model_pointer = "reports/canonical/discovery-gated-transformer.json:$"
    return [
        {
            "scope": "bounded research card for the DGT canonical artifacts",
            "source_owner": "discovery-gated-transformer",
            "source_pointer": model_pointer,
        },
        {
            "scope": "pointer index for L0 and L1 review boundaries",
            "source_owner": "dgt-l0-controls",
            "source_pointer": "reports/canonical/dgt-l0-controls.json:$.l0_toy_projection",
        },
    ]


def _training_facts(resolved: Mapping[str, Any]) -> dict[str, Any]:
    l1 = resolved.get("dgt-l1-controls")
    base = resolved.get("dgt-base-undertraining-audit")
    index_provenance = resolved.get("canonical-index-evidence-provenance")
    facts: dict[str, Any] = {
        "protocol_pointers": [
            {
                "source_owner": "dgt-l1-controls",
                "source_pointer": "reports/canonical/dgt-l1-controls.json:$.task_spec",
                "fact": "bounded tiny-sequence task protocol",
            },
            {
                "source_owner": "dgt-l1-controls",
                "source_pointer": "reports/canonical/dgt-l1-controls.json:$.training_arms",
                "fact": "owner-local training arms",
            },
        ],
        "metric_cells": [],
        "evidence_provenance": {
            "status": "blocked",
            "source_owner": "canonical-index-evidence-provenance",
            "source_pointer": INDEX_EVIDENCE_PROVENANCE_POINTER,
        },
    }
    if isinstance(l1, Mapping):
        ood = l1.get("ood_boundary")
        if isinstance(ood, Mapping):
            if "dgt_ood_accuracy_ci95_low" in ood:
                facts["metric_cells"].append(
                    _metric_cell(
                        metric="dgt_ood_accuracy_ci95_low",
                        value=ood["dgt_ood_accuracy_ci95_low"],
                        source_owner="dgt-l1-controls",
                        source_pointer="reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.ood_boundary.dgt_ood_accuracy_ci95_low",
                        interpretation="boundary-only OOD cell",
                    )
                )
            if "chance_accuracy" in ood:
                facts["metric_cells"].append(
                    _metric_cell(
                        metric="chance_accuracy",
                        value=ood["chance_accuracy"],
                        source_owner="dgt-l1-controls",
                        source_pointer="reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.ood_boundary.chance_accuracy",
                        interpretation="boundary-only OOD baseline",
                    )
                )
    if isinstance(base, Mapping):
        construct = base.get("construct_validity")
        if isinstance(construct, Mapping) and "bayes_upper_bound_accuracy" in construct:
            facts["metric_cells"].append(
                _metric_cell(
                    metric="bayes_upper_bound_accuracy",
                    value=construct["bayes_upper_bound_accuracy"],
                    source_owner="dgt-base-undertraining-audit",
                    source_pointer="reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity.bayes_upper_bound_accuracy",
                    interpretation="construct-validity boundary",
                )
            )
    if isinstance(index_provenance, Mapping):
        facts["evidence_provenance"] = {
            "status": "resolved",
            "source_owner": "canonical-index-evidence-provenance",
            "source_pointer": INDEX_EVIDENCE_PROVENANCE_POINTER,
            "source_type": index_provenance.get("source_type"),
            "evidence_type": index_provenance.get("evidence_type"),
        }
    return facts


def _known_failure_modes(resolved: Mapping[str, Any]) -> list[dict[str, Any]]:
    base = resolved.get("dgt-base-undertraining-audit")
    fair = resolved.get("fair-l1-decision")
    null = resolved.get("dgt-ablation-null-decomposition")
    l1 = resolved.get("dgt-l1-controls")
    rows = [
        {
            "failure_mode": "construct-validity boundary",
            "status": _dig(base, ("construct_validity", "status"), "blocked"),
            "source_owner": "dgt-base-undertraining-audit",
            "source_pointer": "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity",
        },
        {
            "failure_mode": "fair comparison boundary",
            "status": _dig(fair, ("state",), "l1-scaling-blocked"),
            "source_owner": "fair-l1-decision",
            "source_pointer": "reports/canonical/fair-l1-decision.json:$.ladder_state_projection",
        },
        {
            "failure_mode": "ablation null decomposition",
            "status": _dig(null, ("verdict",), "blocked"),
            "source_owner": "dgt-ablation-null-decomposition",
            "source_pointer": "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition",
        },
        {
            "failure_mode": "OOD boundary",
            "status": _dig(l1, ("ood_generalization_claim",), "blocked"),
            "source_owner": "dgt-l1-controls",
            "source_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.ood_boundary",
        },
    ]
    return rows


def _evaluation_boundaries(resolved: Mapping[str, Any]) -> list[dict[str, Any]]:
    l0 = resolved.get("dgt-l0-controls")
    l1 = resolved.get("dgt-l1-controls")
    fair = resolved.get("fair-l1-decision")
    base = resolved.get("dgt-base-undertraining-audit")
    null = resolved.get("dgt-ablation-null-decomposition")
    return [
        {
            "boundary": "L0 review status",
            "status": _dig(l0, ("status",), "blocked"),
            "review_status": _dig(l0, ("review_status",), "blocked"),
            "source_owner": "dgt-l0-controls",
            "source_pointer": "reports/canonical/dgt-l0-controls.json:$.l0_toy_projection",
        },
        {
            "boundary": "L1 scoped review",
            "status": _dig(l1, ("status",), "blocked"),
            "review_status": _dig(l1, ("review_status",), "blocked"),
            "source_owner": "dgt-l1-controls",
            "source_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection",
        },
        {
            "boundary": "fair architecture comparison",
            "status": _dig(fair, ("decision_status",), "blocked"),
            "ladder_state": _dig(fair, ("state",), "l1-scaling-blocked"),
            "construct_validity_status": _dig(base, ("construct_validity", "status"), "blocked"),
            "source_owner": "fair-l1-decision",
            "source_pointer": "reports/canonical/fair-l1-decision.json:$.ladder_state_projection",
            "claim": "no architecture advantage",
        },
        {
            "boundary": "ablation null interpretation",
            "status": _dig(null, ("verdict",), "blocked"),
            "source_owner": "dgt-ablation-null-decomposition",
            "source_pointer": "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition",
        },
    ]


def _boolish(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        return value.strip().lower() in {"true", "yes", "pass", "present"}
    return bool(value)


def _construct_validity_boundary_rows(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for owner, source_pointer in CONSTRUCT_VALIDITY_POINTERS.items():
        status, source, _digest = _resolve_artifact_pointer(root, source_pointer)
        failed_gates: list[str] = []
        cv_status = "blocked"
        rule_abstraction_claim = False
        if status == "resolved" and isinstance(source, Mapping):
            cv_status = str(source.get("status") or "blocked")
            source_failed = source.get("failed_gates")
            if isinstance(source_failed, list):
                failed_gates = [str(gate_id) for gate_id in source_failed]
            finite_table = _dig(source, ("evidence", "finite_table"), {})
            if isinstance(finite_table, Mapping):
                rule_abstraction_claim = _boolish(finite_table.get("rule_abstraction_claim"))
        rows.append(
            {
                "boundary": f"{owner} construct validity",
                "status": cv_status,
                "failed_gates": failed_gates,
                "rule_abstraction_claim": rule_abstraction_claim,
                "rule_abstraction_status": "blocked" if "CV-HG3" in failed_gates else "not-claimed",
                "source_owner": owner,
                "source_pointer": source_pointer,
            }
        )
    return rows


def _not_claimed() -> list[str]:
    return [
        "No production deployment authority.",
        "No global model superiority claim.",
        "No LLM replacement claim.",
        "No fair architecture advantage claim.",
        "No OOD generalization claim.",
        "No component-causal closure claim.",
    ]


def _hardgate(gate_id: str, status: str, reason: str, pointers: Sequence[str]) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": status,
        "reason": reason,
        "input_pointers": list(pointers),
    }


def _card_hardgates(card: Mapping[str, Any], root: Path) -> dict[str, Any]:
    draft = dict(card)
    draft["card_hardgates"] = {"status": "pending", "gates": {}}
    errors = _validate_without_hardgate_refresh(draft, root)
    by_gate: dict[str, list[CardGateError]] = {}
    for error in errors:
        by_gate.setdefault(error.gate_id, []).append(error)
    gate_ids = tuple(f"CARD-HG{index}" for index in range(1, 10))
    gates = {
        gate_id: _hardgate(
            gate_id,
            "fail" if gate_id in by_gate else "pass",
            "; ".join(error.message for error in by_gate.get(gate_id, [])) or "ok",
            [error.path for error in by_gate.get(gate_id, [])],
        )
        for gate_id in gate_ids
    }
    return {
        "status": "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "blocked",
        "gates": gates,
    }


class DgtModelCardProjection:
    """Builds the public card by linking owner artifacts."""

    @staticmethod
    def build(root: Path, generated_at: str) -> dict[str, Any]:
        return build_dgt_model_card(root=root, generated_at=generated_at)


def build_dgt_model_card(root: Path, generated_at: str) -> dict[str, Any]:
    source_artifacts, resolved, missing_refs = _source_records(root)
    card: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "card_id": CARD_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "status": "blocked" if missing_refs else "pass",
        "missing_source_refs": missing_refs,
        "source_artifacts": source_artifacts,
        "intended_use": _intended_use(resolved),
        "not_intended_use": _not_intended_use(),
        "known_failure_modes": _known_failure_modes(resolved),
        "evaluation_boundaries": _evaluation_boundaries(resolved) + _construct_validity_boundary_rows(root),
        "training_facts": _training_facts(resolved),
        "upstream_status": [
            _owner_status_cell(
                row["source_owner"],
                row["source_pointer"],
                row["status"],
                source_artifacts=source_artifacts,
            )
            for row in source_artifacts
        ],
        "not_claimed": _not_claimed(),
    }
    card["card_hardgates"] = _card_hardgates(card, root)
    card["status"] = "pass" if card["card_hardgates"]["status"] == "pass" else "blocked"
    return card


def _literal_values(card: Mapping[str, Any]) -> list[str]:
    rows = card.get("not_intended_use")
    if not isinstance(rows, list):
        return []
    return [row.get("literal") for row in rows if isinstance(row, Mapping) and isinstance(row.get("literal"), str)]


def _iter_number_cells(value: Any, path: str = "$") -> Sequence[tuple[str, Any, Mapping[str, Any] | None]]:
    cells: list[tuple[str, Any, Mapping[str, Any] | None]] = []

    def walk(cell: Any, cell_path: str, owner: Mapping[str, Any] | None) -> None:
        current_owner = cell if isinstance(cell, Mapping) else owner
        if isinstance(cell, bool):
            return
        if isinstance(cell, (int, float)):
            cells.append((cell_path, cell, owner))
            return
        if isinstance(cell, Mapping):
            for key, nested in cell.items():
                walk(nested, f"{cell_path}.{key}", current_owner)
            return
        if isinstance(cell, list):
            for index, nested in enumerate(cell):
                walk(nested, f"{cell_path}[{index}]", current_owner)

    walk(value, path, None)
    return cells


def _validate_required_keys(card: Mapping[str, Any]) -> list[CardGateError]:
    return [
        CardGateError("CARD-HG1", f"$.{key}", "required key missing")
        for key in REQUIRED_KEYS
        if key not in card
    ]


def _validate_literals(card: Mapping[str, Any]) -> list[CardGateError]:
    literals = _literal_values(card)
    errors = [
        CardGateError("CARD-HG2", "$.not_intended_use", f"missing exact literal: {literal}")
        for literal in REQUIRED_NOT_INTENDED_LITERALS
        if literal not in literals
    ]
    extras = [literal for literal in literals if literal not in REQUIRED_NOT_INTENDED_LITERALS]
    if extras:
        errors.append(CardGateError("CARD-HG2", "$.not_intended_use", "unexpected not-intended literal"))
    return errors


def _validate_numeric_cells(card: Mapping[str, Any]) -> list[CardGateError]:
    errors: list[CardGateError] = []
    ignored_roots = ("$.source_artifacts[", "$.card_hardgates.")
    for path, _value, owner in _iter_number_cells(card):
        if path == "$.generated_at" or any(path.startswith(prefix) for prefix in ignored_roots):
            continue
        if owner is None or not owner.get("source_pointer") or not owner.get("source_owner"):
            errors.append(CardGateError("CARD-HG3", path, "numeric cell lacks source pointer and owner"))
    return errors


def _validate_l0_owner(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    errors: list[CardGateError] = []
    for index, row in enumerate(card.get("evaluation_boundaries", [])):
        if not isinstance(row, Mapping) or row.get("source_owner") != "dgt-l0-controls":
            continue
        status, source, _digest = _resolve_artifact_pointer(root, row["source_pointer"])
        if status != "resolved" or not isinstance(source, Mapping):
            errors.append(CardGateError("CARD-HG4", f"$.evaluation_boundaries[{index}]", "L0 source pointer does not resolve"))
            continue
        for key in ("status", "review_status"):
            if row.get(key) != source.get(key):
                errors.append(CardGateError("CARD-HG4", f"$.evaluation_boundaries[{index}].{key}", "L0 status differs from owner"))
    return errors


def _validate_l1_fair_boundary(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    rows = _mapping_row_items(card.get("evaluation_boundaries"))
    l1_pointer = "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection"
    l1_rows = [
        (index, row)
        for index, row in rows
        if row.get("source_owner") == "dgt-l1-controls"
        and row.get("source_pointer") == l1_pointer
    ]
    fair_rows = [(index, row) for index, row in rows if row.get("boundary") == "fair architecture comparison"]
    errors: list[CardGateError] = []
    if not l1_rows:
        errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", "L1 scoped review boundary missing"))
    for index, row in l1_rows:
        status, source, _digest = _resolve_artifact_pointer(root, l1_pointer)
        if status != "resolved" or not isinstance(source, Mapping):
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}]", "L1 source pointer does not resolve"))
            continue
        for key in ("status", "review_status"):
            if row.get(key) != source.get(key):
                errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}].{key}", "L1 status differs from owner"))
    if not fair_rows:
        errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", "fair comparison boundary missing"))
    fair_known_rows = [
        (index, row)
        for index, row in _mapping_row_items(card.get("known_failure_modes"))
        if row.get("failure_mode") == "fair comparison boundary"
    ]
    if not fair_known_rows:
        errors.append(CardGateError("CARD-HG5", "$.known_failure_modes", "fair comparison failure mode missing"))
    for index, row in fair_rows:
        fair_pointer = "reports/canonical/fair-l1-decision.json:$.ladder_state_projection"
        if row.get("source_owner") != "fair-l1-decision" or row.get("source_pointer") != fair_pointer:
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}].source_pointer", "fair comparison owner pointer differs from owner"))
            continue
        status, source, _digest = _resolve_artifact_pointer(root, fair_pointer)
        if status != "resolved" or not isinstance(source, Mapping):
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}]", "fair comparison source pointer does not resolve"))
            continue
        expected_status = source.get("decision_status")
        expected_ladder_state = source.get("state")
        base_status, base_source, _base_digest = _resolve_artifact_pointer(
            root,
            "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit",
        )
        expected_construct_status = _dig(base_source, ("construct_validity", "status"), "blocked") if base_status == "resolved" and isinstance(base_source, Mapping) else "blocked"
        if row.get("status") != expected_status:
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}].status", "fair comparison status differs from owner"))
        if row.get("ladder_state") != expected_ladder_state:
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}].ladder_state", "fair comparison ladder state differs from owner"))
        if row.get("construct_validity_status") != expected_construct_status:
            errors.append(CardGateError("CARD-HG5", f"$.evaluation_boundaries[{index}].construct_validity_status", "fair comparison construct-validity status differs from owner"))
        if row.get("construct_validity_status") != "construct-boundary":
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", "construct-validity boundary not preserved"))
        if row.get("claim") != "no architecture advantage":
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", "architecture advantage wording is not blocked"))
        for known_index, known_row in fair_known_rows:
            if known_row.get("source_owner") != "fair-l1-decision" or known_row.get("source_pointer") != fair_pointer:
                errors.append(CardGateError("CARD-HG5", f"$.known_failure_modes[{known_index}].source_pointer", "fair comparison failure mode owner pointer differs from owner"))
            if known_row.get("status") != expected_ladder_state:
                errors.append(CardGateError("CARD-HG5", f"$.known_failure_modes[{known_index}].status", "fair comparison failure mode status differs from owner"))
    serialized_intended = json.dumps(card.get("intended_use", []), sort_keys=True).lower()
    if "architecture advantage" in serialized_intended:
        errors.append(CardGateError("CARD-HG5", "$.intended_use", "architecture advantage entered intended use"))
    return errors


def _validate_construct_validity_boundaries(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    boundaries = card.get("evaluation_boundaries")
    rows = [row for row in boundaries if isinstance(row, Mapping)] if isinstance(boundaries, list) else []
    errors: list[CardGateError] = []
    for owner, source_pointer in CONSTRUCT_VALIDITY_POINTERS.items():
        row = next(
            (
                candidate
                for candidate in rows
                if candidate.get("source_owner") == owner and candidate.get("source_pointer") == source_pointer
            ),
            None,
        )
        if row is None:
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} construct-validity boundary missing"))
            continue
        status, source, _digest = _resolve_artifact_pointer(root, source_pointer)
        if status != "resolved" or not isinstance(source, Mapping):
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} construct-validity source missing"))
            continue
        failed_gates = source.get("failed_gates")
        expected_failed = [str(gate_id) for gate_id in failed_gates] if isinstance(failed_gates, list) else []
        if row.get("status") != source.get("status"):
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} construct-validity status differs from owner"))
        if row.get("failed_gates") != expected_failed:
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} construct-validity failed gates differ from owner"))
        gates = source.get("gates")
        if isinstance(gates, Mapping):
            for gate_id in expected_failed:
                gate = gates.get(gate_id)
                if not isinstance(gate, Mapping) or gate.get("status") == "pass":
                    errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} construct-validity gate state is not blocked"))
        finite_table = _dig(source, ("evidence", "finite_table"), {})
        rule_abstraction_claim = _boolish(finite_table.get("rule_abstraction_claim")) if isinstance(finite_table, Mapping) else False
        if row.get("rule_abstraction_claim") != rule_abstraction_claim:
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} rule-abstraction claim state differs from owner"))
        if "CV-HG3" in expected_failed and row.get("rule_abstraction_status") != "blocked":
            errors.append(CardGateError("CARD-HG5", "$.evaluation_boundaries", f"{owner} rule-abstraction boundary is not blocked"))
    return errors


def _validate_ablation_boundary(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    intended = json.dumps(card.get("intended_use", []), sort_keys=True).lower()
    if "ablation" in intended or "null" in intended:
        return [CardGateError("CARD-HG6", "$.intended_use", "ablation null row entered intended use")]
    errors: list[CardGateError] = []
    source_pointer = "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition"
    known_rows = _mapping_row_items(card.get("known_failure_modes"))
    known = next(
        (
            (index, row)
            for index, row in known_rows
            if row.get("source_owner") == "dgt-ablation-null-decomposition"
            and row.get("source_pointer") == source_pointer
        ),
        None,
    )
    boundary_rows = _mapping_row_items(card.get("evaluation_boundaries"))
    boundary = next(
        (
            (index, row)
            for index, row in boundary_rows
            if row.get("boundary") == "ablation null interpretation"
            and row.get("source_owner") == "dgt-ablation-null-decomposition"
            and row.get("source_pointer") == source_pointer
        ),
        None,
    )
    status, source, _digest = _resolve_artifact_pointer(root, source_pointer)
    if status != "resolved" or not isinstance(source, Mapping):
        errors.append(CardGateError("CARD-HG6", "$.known_failure_modes", "ablation null source missing"))
        return errors
    expected_status = source.get("verdict")
    if known is None:
        errors.append(CardGateError("CARD-HG6", "$.known_failure_modes", "ablation null boundary missing"))
    elif known[1].get("status") != expected_status:
        errors.append(CardGateError("CARD-HG6", f"$.known_failure_modes[{known[0]}].status", "ablation null status differs from owner"))
    if boundary is None:
        errors.append(CardGateError("CARD-HG6", "$.evaluation_boundaries", "ablation null evaluation boundary missing"))
    elif boundary[1].get("status") != expected_status:
        errors.append(CardGateError("CARD-HG6", f"$.evaluation_boundaries[{boundary[0]}].status", "ablation null evaluation status differs from owner"))
    return errors


def _validate_evidence_provenance(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    provenance = _dig(card, ("training_facts", "evidence_provenance"), {})
    if not isinstance(provenance, Mapping):
        return [CardGateError("CARD-HG7", "$.training_facts.evidence_provenance", "evidence provenance missing")]
    status, source, _digest = _resolve_artifact_pointer(root, INDEX_EVIDENCE_PROVENANCE_POINTER)
    if status != "resolved" or not isinstance(source, Mapping):
        if (
            provenance.get("status") == "blocked"
            and provenance.get("source_owner") == "canonical-index-evidence-provenance"
            and provenance.get("source_pointer") == INDEX_EVIDENCE_PROVENANCE_POINTER
            and not any(key in provenance for key in ("source_type", "evidence_type"))
        ):
            return []
        return [CardGateError("CARD-HG7", "$.training_facts.evidence_provenance", "index evidence provenance does not resolve")]
    if provenance.get("status") != "resolved":
        return [CardGateError("CARD-HG7", "$.training_facts.evidence_provenance.status", "provenance status differs from index owner")]
    for key in ("source_type", "evidence_type"):
        if provenance.get(key) != source.get(key):
            return [CardGateError("CARD-HG7", f"$.training_facts.evidence_provenance.{key}", "provenance differs from index owner")]
    return []


def _validate_source_freshness(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    errors: list[CardGateError] = []
    rows = card.get("source_artifacts")
    if not isinstance(rows, list):
        return [CardGateError("CARD-HG9", "$.source_artifacts", "source artifact rows missing")]
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            errors.append(CardGateError("CARD-HG9", f"$.source_artifacts[{index}]", "invalid source row"))
            continue
        source_pointer = row.get("source_pointer")
        if isinstance(source_pointer, str):
            expected_status, expected_digest = _expected_source_status(root, source_pointer)
            if row.get("status") != expected_status:
                errors.append(CardGateError("CARD-HG9", f"$.source_artifacts[{index}].status", "source row status differs from pointer resolution"))
            if row.get("sha256") != expected_digest:
                errors.append(CardGateError("CARD-HG9", f"$.source_artifacts[{index}].sha256", "source row digest differs from owner artifact"))
        else:
            digest = _file_digest(root / str(row.get("artifact", "")))
            if digest != row.get("sha256"):
                errors.append(CardGateError("CARD-HG9", f"$.source_artifacts[{index}].sha256", "source digest is stale"))
    return errors


def _validate_source_resolution(card: Mapping[str, Any]) -> list[CardGateError]:
    rows = card.get("source_artifacts")
    if not isinstance(rows, list):
        return []
    return [
        CardGateError("CARD-HG9", f"$.source_artifacts[{index}].status", "source pointer is not resolved")
        for index, row in enumerate(rows)
        if isinstance(row, Mapping) and row.get("status") != "resolved"
    ]


def _validate_upstream_status(card: Mapping[str, Any]) -> list[CardGateError]:
    source_rows = _mapping_rows(card.get("source_artifacts"))
    status_rows = card.get("upstream_status")
    if not isinstance(status_rows, list):
        return [CardGateError("CARD-HG9", "$.upstream_status", "upstream status rows missing")]
    errors: list[CardGateError] = []
    by_pointer = {row.get("source_pointer"): row for row in source_rows if isinstance(row.get("source_pointer"), str)}
    for index, row in enumerate(status_rows):
        if not isinstance(row, Mapping):
            errors.append(CardGateError("CARD-HG9", f"$.upstream_status[{index}]", "invalid upstream status row"))
            continue
        source_pointer = row.get("source_pointer")
        source = by_pointer.get(source_pointer)
        if source is None:
            errors.append(CardGateError("CARD-HG9", f"$.upstream_status[{index}].source_pointer", "upstream status source row missing"))
            continue
        if row.get("status") != source.get("status"):
            errors.append(CardGateError("CARD-HG9", f"$.upstream_status[{index}].status", "upstream status differs from source row"))
        if row.get("source_digest") != source.get("sha256"):
            errors.append(CardGateError("CARD-HG9", f"$.upstream_status[{index}].source_digest", "upstream digest differs from source row"))
    return errors


def _validate_owner_projection_fields(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    source_artifacts, resolved, _missing_refs = _source_records(root)
    facts = _training_facts(resolved)
    expected_boundaries = _evaluation_boundaries(resolved) + _construct_validity_boundary_rows(root)
    expected_upstream = [
        _owner_status_cell(
            row["source_owner"],
            row["source_pointer"],
            row["status"],
            source_artifacts=source_artifacts,
        )
        for row in source_artifacts
    ]
    errors: list[CardGateError] = []
    errors.extend(
        _validate_projection_rows(
            card.get("source_artifacts"),
            source_artifacts,
            OwnerProjectionTable(
                path="$.source_artifacts",
                gate_id="CARD-HG9",
                identity_keys=("source_owner", "source_pointer"),
                value_keys=("owner_issue", "artifact", "pointer", "status", "sha256"),
            ),
        )
    )
    errors.extend(
        _validate_projection_rows(
            card.get("upstream_status"),
            expected_upstream,
            OwnerProjectionTable(
                path="$.upstream_status",
                gate_id="CARD-HG9",
                identity_keys=("source_owner", "source_pointer"),
                value_keys=("status", "source_digest"),
            ),
        )
    )
    errors.extend(
        _validate_projection_rows(
            _dig(card, ("training_facts", "metric_cells"), []),
            facts.get("metric_cells", []),
            OwnerProjectionTable(
                path="$.training_facts.metric_cells",
                gate_id="CARD-HG3",
                identity_keys=("source_owner", "source_pointer", "metric"),
                value_keys=("value",),
            ),
        )
    )
    errors.extend(
        _validate_projection_mapping(
            _dig(card, ("training_facts", "evidence_provenance"), {}),
            facts.get("evidence_provenance", {}),
            path="$.training_facts.evidence_provenance",
            gate_id="CARD-HG7",
            value_keys=("status", "source_type", "evidence_type"),
        )
    )
    errors.extend(
        _validate_projection_rows(
            card.get("known_failure_modes"),
            _known_failure_modes(resolved),
            OwnerProjectionTable(
                path="$.known_failure_modes",
                gate_id="CARD-HG5",
                identity_keys=("source_owner", "source_pointer", "failure_mode"),
                value_keys=("status",),
            ),
        )
    )
    errors.extend(
        _validate_projection_rows(
            card.get("evaluation_boundaries"),
            expected_boundaries,
            OwnerProjectionTable(
                path="$.evaluation_boundaries",
                gate_id="CARD-HG5",
                identity_keys=("source_owner", "source_pointer", "boundary"),
                value_keys=(
                    "status",
                    "review_status",
                    "construct_validity_status",
                    "ladder_state",
                    "failed_gates",
                    "rule_abstraction_claim",
                    "rule_abstraction_status",
                ),
            ),
        )
    )
    return errors


def _validate_without_hardgate_refresh(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    errors: list[CardGateError] = []
    errors.extend(_validate_required_keys(card))
    errors.extend(_validate_literals(card))
    errors.extend(_validate_numeric_cells(card))
    errors.extend(_validate_owner_projection_fields(card, root))
    errors.extend(_validate_l0_owner(card, root))
    errors.extend(_validate_l1_fair_boundary(card, root))
    errors.extend(_validate_construct_validity_boundaries(card, root))
    errors.extend(_validate_ablation_boundary(card, root))
    errors.extend(_validate_evidence_provenance(card, root))
    errors.extend(_validate_source_resolution(card))
    errors.extend(_validate_source_freshness(card, root))
    errors.extend(_validate_upstream_status(card))
    return errors


def _validate_card_hardgate_projection(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    expected = _card_hardgates(card, root)
    expected_status = "pass" if expected["status"] == "pass" else "blocked"
    errors: list[CardGateError] = []
    if card.get("status") != expected_status:
        errors.append(CardGateError("CARD-HG8", "$.status", "top-level status differs from recomputed hardgates"))
    hardgates = card.get("card_hardgates")
    if not isinstance(hardgates, Mapping):
        errors.append(CardGateError("CARD-HG8", "$.card_hardgates", "card hardgates missing"))
        return errors
    if hardgates.get("status") != expected["status"]:
        errors.append(CardGateError("CARD-HG8", "$.card_hardgates.status", "card hardgate status differs from recomputed evidence"))
    gates = hardgates.get("gates")
    expected_gates = expected["gates"]
    if not isinstance(gates, Mapping):
        errors.append(CardGateError("CARD-HG8", "$.card_hardgates.gates", "card hardgate gates missing"))
        return errors
    submitted_ids = {str(gate_id) for gate_id in gates}
    expected_ids = set(expected_gates)
    for gate_id in sorted(expected_ids - submitted_ids):
        errors.append(CardGateError("CARD-HG8", f"$.card_hardgates.gates.{gate_id}", "card hardgate missing"))
    for gate_id in sorted(submitted_ids - expected_ids):
        errors.append(CardGateError("CARD-HG8", f"$.card_hardgates.gates.{gate_id}", "unexpected card hardgate"))
    for gate_id in sorted(expected_ids & submitted_ids):
        gate = gates.get(gate_id)
        if not isinstance(gate, Mapping):
            errors.append(CardGateError("CARD-HG8", f"$.card_hardgates.gates.{gate_id}", "card hardgate row invalid"))
            continue
        expected_gate = expected_gates[gate_id]
        for key in ("gate_id", "status", "reason", "input_pointers"):
            if gate.get(key) != expected_gate.get(key):
                errors.append(CardGateError("CARD-HG8", f"$.card_hardgates.gates.{gate_id}.{key}", "card hardgate differs from recomputed evidence"))
    return errors


def validate_dgt_model_card(card: Mapping[str, Any], root: Path) -> list[CardGateError]:
    errors = _validate_without_hardgate_refresh(card, root)
    errors.extend(_validate_card_hardgate_projection(card, root))
    return errors


def _markdown_digest(card: Mapping[str, Any]) -> str:
    return _json_digest(card)


def render_dgt_model_card_markdown(card: Mapping[str, Any]) -> str:
    errors = validate_dgt_model_card(card, Path.cwd())
    if errors and not all(error.gate_id == "CARD-HG9" for error in errors):
        pass
    hardgates = card.get("card_hardgates", {})
    lines = [
        f"<!-- payload-sha256: {_markdown_digest(card)} -->",
        "# DGT Model Card",
        "",
        f"- Schema: `{card.get('schema_id')}`",
        f"- Card: `{card.get('card_id')}`",
        f"- Status: `{card.get('status')}`",
        f"- Source pointer: `{CANONICAL_JSON_ARTIFACT}:$`",
        "",
        "## Intended Use",
        "",
    ]
    for row in card.get("intended_use", []):
        if isinstance(row, Mapping):
            lines.append(f"- {row.get('scope')} (`{row.get('source_pointer')}`)")
    lines.extend(["", "## Not Intended Use", ""])
    for row in card.get("not_intended_use", []):
        if isinstance(row, Mapping):
            lines.append(f"- {row.get('literal')}")
    lines.extend(["", "## Boundaries", ""])
    for row in card.get("evaluation_boundaries", []):
        if isinstance(row, Mapping):
            lines.append(f"- {row.get('boundary')}: `{row.get('status')}` (`{row.get('source_pointer')}`)")
    lines.extend(["", "## Known Failure Modes", ""])
    for row in card.get("known_failure_modes", []):
        if isinstance(row, Mapping):
            lines.append(f"- {row.get('failure_mode')}: `{row.get('status')}` (`{row.get('source_pointer')}`)")
    lines.extend(["", "## Hardgates", ""])
    gates = hardgates.get("gates") if isinstance(hardgates, Mapping) else {}
    if isinstance(gates, Mapping):
        for gate_id in sorted(gates):
            gate = gates[gate_id]
            if isinstance(gate, Mapping):
                lines.append(f"- {gate_id}: `{gate.get('status')}`")
    lines.extend(["", "## Not Claimed", ""])
    for row in card.get("not_claimed", []):
        lines.append(f"- {row}")
    lines.append("")
    return "\n".join(lines)


def validate_dgt_model_card_markdown(card: Mapping[str, Any], markdown: str) -> list[CardGateError]:
    expected = render_dgt_model_card_markdown(card)
    if markdown != expected:
        return [CardGateError("CARD-HG8", "$markdown", "markdown differs from JSON render")]
    return []


def write_dgt_model_card(root: Path, generated_at: str = DEFAULT_GENERATED_AT) -> dict[str, Any]:
    card = build_dgt_model_card(root=root, generated_at=generated_at)
    _write_json(root / CANONICAL_JSON_ARTIFACT, card)
    _write_text(root / CANONICAL_MARKDOWN_ARTIFACT, render_dgt_model_card_markdown(card))
    return card

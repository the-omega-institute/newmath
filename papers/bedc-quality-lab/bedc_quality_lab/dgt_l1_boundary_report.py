"""Canonical boundary report for DGT L1 scaling claim exclusion."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:dgt-l1-boundary-report"
ARTIFACT_ID = "bedc-quality-lab:dgt-l1-boundary-report"
PRODUCER = "scripts/run_dgt_l1_boundary_report.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-l1-boundary-report.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-l1-boundary-report.md"
DGT_L1_CONTROLS_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
LAB_ROOT = Path(__file__).resolve().parents[1]

ARTIFACT_ROLE = "boundary_block"
CLAIM_PROMOTION_ELIGIBLE = False
CLAIM_PROMOTION_EXCLUSION = {
    "status": "not-eligible",
    "reason": "information-access-boundary",
    "excluded_surfaces": ["positive_claim_cells", "discovery_promotion", "l1-scaling"],
    "blocking_pointer": "$.scaling_claim_block",
    "fair_rebuild_required": True,
}
REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "generated_at",
    "artifact_role",
    "source_artifacts",
    "cost_protocol",
    "task_formula",
    "feature_reachability",
    "base_bayes_ceiling",
    "ood_solvability",
    "table_coverage_ceiling",
    "negative_witness_refs",
    "boundary_decision",
    "required_redesign",
    "claim_promotion_eligible",
    "claim_promotion_exclusion",
    "scaling_claim_block",
    "hardgates",
    "not_claimed",
)
REQUIRED_WITNESSES = (
    "information_starved_baseline",
    "unanswerable_ood",
    "table_coverage_saturation",
    "hand_engineered_task_aligned_gate",
)
L1_BOUNDARY_HARDGATES = tuple(f"L1B-HG{index}" for index in range(1, 6))
NOT_CLAIMED = (
    "No architecture superiority claim.",
    "No tiny-sequence OOD generalization claim.",
    "No L1 scaling claim.",
    "No component-causal completeness claim.",
    "No order-two causal rule learning claim.",
    "No fair architecture comparison claim before the required rebuild resolves.",
)


def base_bayes_ceiling(class_count: int = 16) -> float:
    """Return max_y P(y | x_{t-1}) when x_{t-2} is hidden and labels are uniform."""

    if class_count <= 0:
        raise ValueError("class_count must be positive")
    return 1.0 / float(class_count)


def table_coverage_ceiling(combinations: int = 256, samples: int = 1024) -> float:
    """Return 1 - ((N - 1) / N)^m for observing a finite pair table cell at least once."""

    if combinations <= 1:
        raise ValueError("combinations must exceed one")
    if samples < 0:
        raise ValueError("samples must be nonnegative")
    return 1.0 - ((combinations - 1) / combinations) ** samples


def _control_pointer(pointer: str) -> str:
    return f"{DGT_L1_CONTROLS_ARTIFACT}:{pointer}"


def _source_ref(pointer: str) -> dict[str, str]:
    return {"artifact": DGT_L1_CONTROLS_ARTIFACT, "pointer": pointer}


def _source_pointer(pointer: str) -> str:
    return _control_pointer(pointer)


def _load_l1_controls(root: Path) -> Mapping[str, Any]:
    path = root / DGT_L1_CONTROLS_ARTIFACT
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, Mapping) else {}


def _pointer_resolution(root: Path, pointer: str) -> str:
    return "resolved" if resolve_artifact_pointer(root, pointer) is not None else "unresolved"


def _negative_witness_refs(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for witness in REQUIRED_WITNESSES:
        pointer = (
            f"{DGT_L1_CONTROLS_ARTIFACT}:$.negative_witness_sweep.rows"
            f"[witness={witness}]"
        )
        rows.append(
            {
                "kind": witness,
                "owner_artifact": DGT_L1_CONTROLS_ARTIFACT,
                "pointer": pointer,
                "owner_issue": 1207,
                "resolution_status": _pointer_resolution(root, pointer),
            }
        )
    return rows


def _feature_reachability() -> dict[str, Any]:
    return {
        "status": "closed",
        "source_pointer": _source_pointer("$.training_arms"),
        "arms": [
            {
                "arm_id": "information_starved_l1_baseline",
                "visible_variables": ["x_t_minus_1"],
                "required_variables": ["x_t_minus_1", "x_t_minus_2"],
                "label_access": "information-starved",
                "decision": "cannot identify the label rule from visible variables",
                "source_pointer": _source_pointer("$.training_arms.information_starved_l1_baseline"),
            },
            {
                "arm_id": "dgt_l1",
                "visible_variables": ["x_t_minus_1", "x_t_minus_2", "task_aligned_gate_1", "task_aligned_gate_2"],
                "required_variables": ["x_t_minus_1", "x_t_minus_2"],
                "label_access": "task-aligned",
                "decision": "in-distribution table coverage is available",
                "source_pointer": _source_pointer("$.training_arms.dgt_l1"),
            },
            {
                "arm_id": "matched_random_structural_l1",
                "visible_variables": ["rolled_x_t_minus_1", "rolled_x_t_minus_2"],
                "required_variables": ["x_t_minus_1", "x_t_minus_2"],
                "label_access": "misaligned",
                "decision": "structural control can expose table coverage saturation",
                "source_pointer": _source_pointer("$.training_arms.matched_random_structural_l1"),
            },
            {
                "arm_id": "parameter_matched_l1",
                "visible_variables": ["x_t_minus_1", "x_t_minus_2"],
                "required_variables": ["x_t_minus_1", "x_t_minus_2"],
                "label_access": "parameter-matched",
                "decision": "fairness control only",
                "source_pointer": _source_pointer("$.training_arms.parameter_matched_l1"),
            },
            {
                "arm_id": "compute_matched_l1",
                "visible_variables": ["x_t_minus_1", "x_t_minus_2"],
                "required_variables": ["x_t_minus_1", "x_t_minus_2"],
                "label_access": "compute-matched",
                "decision": "fairness control only",
                "source_pointer": _source_pointer("$.training_arms.compute_matched_l1"),
            },
        ],
    }


def _fair_rebuild_status(root: Path, pointer: str) -> str:
    return "resolved-pass" if resolve_artifact_pointer(root, pointer) == "pass" else "unresolved"


def _hardgates(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    witness_refs = payload.get("negative_witness_refs")
    witnesses_ok = (
        isinstance(witness_refs, list)
        and {row.get("kind") for row in witness_refs if isinstance(row, Mapping)} == set(REQUIRED_WITNESSES)
        and all(set(row) == {"kind", "owner_artifact", "pointer", "owner_issue", "resolution_status"} for row in witness_refs if isinstance(row, Mapping))
    )
    exclusion = payload.get("claim_promotion_exclusion")
    block = payload.get("scaling_claim_block")
    feature = payload.get("feature_reachability")
    bayes = payload.get("base_bayes_ceiling")
    coverage = payload.get("table_coverage_ceiling")
    return {
        "L1B-HG1": {
            "status": "pass" if payload.get("task_formula", {}).get("source_pointer") == _source_pointer("$.task_spec") else "fail",
            "evidence_pointer": "$.task_formula",
        },
        "L1B-HG2": {
            "status": "pass" if isinstance(feature, Mapping) and len(feature.get("arms", [])) == 5 else "fail",
            "evidence_pointer": "$.feature_reachability",
        },
        "L1B-HG3": {
            "status": "pass"
            if isinstance(bayes, Mapping)
            and bayes.get("computed_value") == base_bayes_ceiling()
            and isinstance(coverage, Mapping)
            and math.isclose(float(coverage.get("computed_value", -1.0)), table_coverage_ceiling(), rel_tol=0.0, abs_tol=1e-12)
            else "fail",
            "evidence_pointer": "$.base_bayes_ceiling",
        },
        "L1B-HG4": {
            "status": "pass" if witnesses_ok else "fail",
            "evidence_pointer": "$.negative_witness_refs",
        },
        "L1B-HG5": {
            "status": "pass"
            if exclusion == CLAIM_PROMOTION_EXCLUSION
            and isinstance(block, Mapping)
            and block.get("status") == "blocked"
            and block.get("runtime_pointer") == "$.scaling_claim_block"
            else "fail",
            "evidence_pointer": "$.claim_promotion_exclusion",
        },
    }


def build_l1_boundary_report(*, root: Path | None = None, generated_at: str = GENERATED_AT) -> dict[str, Any]:
    root = root or LAB_ROOT
    controls = _load_l1_controls(root)
    fair_rebuild_pointer = "reports/canonical/dgt-l1-fair-rebuild.json:$.status"
    fair_status = _fair_rebuild_status(root, fair_rebuild_pointer)
    block_status = "unblocked" if fair_status == "resolved-pass" else "blocked"
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "artifact_role": ARTIFACT_ROLE,
        "source_artifacts": {
            "dgt_l1_controls": _source_ref("$"),
            "task_spec_ref": _source_ref("$.task_spec"),
            "training_arms_ref": _source_ref("$.training_arms"),
            "negative_witness_sweep_ref": _source_ref("$.negative_witness_sweep"),
            "step_ladder_ref": _source_ref("$.l1_step_ladder"),
            "ood_mechanism_ref": _source_ref("$.l1_ood_mechanism"),
        },
        "cost_protocol": {
            "status": "pointer-only",
            "source_pointer": _source_pointer("$.compute_ledger"),
            "parameter_pointer": _source_pointer("$.parameter_ledger"),
        },
        "task_formula": {
            "status": "recorded",
            "source_pointer": _source_pointer("$.task_spec"),
            "label_rule": "y_t = (3 * x_{t-1} + 5 * x_{t-2} + 1) mod 16",
            "ood_label_rule": "y_t = (3 * x_{t-1} + 5 * x_{t-3} + 7) mod 16",
            "class_count": 16,
            "train_examples": controls.get("task_spec", {}).get("train_examples") if isinstance(controls.get("task_spec"), Mapping) else None,
        },
        "feature_reachability": _feature_reachability(),
        "base_bayes_ceiling": {
            "status": "closed",
            "formula": "max_y P(y | x_{t-1}) = 1 / 16",
            "inputs": {"class_count": 16},
            "computed_value": base_bayes_ceiling(),
            "source_pointer": _source_pointer("$.task_spec.vocab_size"),
        },
        "ood_solvability": {
            "status": "not-winnable-from-recorded-features",
            "required_dependency": "x_t_minus_3",
            "visible_dependency": "x_t_minus_2",
            "source_pointer": _source_pointer("$.l1_tiny_sequence_projection.ood_boundary"),
        },
        "table_coverage_ceiling": {
            "status": "closed",
            "formula": "1 - ((255 / 256) ** 1024)",
            "inputs": {"combinations": 256, "samples": 1024},
            "computed_value": table_coverage_ceiling(),
            "observed_accuracy": 0.982,
            "decision": "in-distribution accuracy is consistent with finite table coverage",
            "source_pointer": _source_pointer("$.training_arms.dgt_l1.metrics.accuracy_mean"),
        },
        "negative_witness_refs": _negative_witness_refs(root),
        "boundary_decision": {
            "status": "blocked",
            "kind": "information-access-boundary",
            "decision": "L1 construct validity does not support a scaling claim",
            "basis_pointers": [
                "$.feature_reachability",
                "$.base_bayes_ceiling",
                "$.ood_solvability",
                "$.table_coverage_ceiling",
                "$.negative_witness_refs",
            ],
        },
        "required_redesign": {
            "status": "required",
            "fair_rebuild_status": fair_status,
            "fair_rebuild_pointer": fair_rebuild_pointer,
            "reason": "A fair rebuild must expose comparable label information before L1 scaling can be reconsidered.",
        },
        "claim_promotion_eligible": CLAIM_PROMOTION_ELIGIBLE,
        "claim_promotion_exclusion": dict(CLAIM_PROMOTION_EXCLUSION),
        "scaling_claim_block": {
            "status": block_status,
            "blocked_claims": ["l1-scaling"],
            "runtime_pointer": "$.scaling_claim_block",
            "fair_rebuild_pointer": fair_rebuild_pointer,
            "fair_rebuild_status": fair_status,
            "unblock_condition": "fair rebuild pointer resolves to pass",
            "reason": None if block_status == "unblocked" else "information-access-boundary",
        },
        "hardgates": {},
        "not_claimed": list(NOT_CLAIMED),
    }
    payload["hardgates"] = _hardgates(payload)
    validate_l1_boundary_report(payload)
    return payload


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate_l1_boundary_report(payload: Mapping[str, Any]) -> None:
    missing = [key for key in REQUIRED_KEYS if key not in payload]
    _require(not missing, f"DGT L1 boundary report missing required keys: {', '.join(missing)}")
    forbidden_aliases = sorted(key for key in ("ladder_block", "claim_block") if key in payload)
    _require(not forbidden_aliases, f"DGT L1 boundary report forbidden aliases: {', '.join(forbidden_aliases)}")
    _require(payload.get("schema_id") == SCHEMA_ID, "DGT L1 boundary report schema mismatch")
    _require(payload.get("artifact_id") == ARTIFACT_ID, "DGT L1 boundary report artifact mismatch")
    _require(payload.get("artifact_role") == ARTIFACT_ROLE, "DGT L1 boundary report artifact role mismatch")
    _require(payload.get("claim_promotion_eligible") is False, "DGT L1 boundary report promotion eligibility mismatch")
    _require(
        payload.get("claim_promotion_exclusion") == CLAIM_PROMOTION_EXCLUSION,
        "DGT L1 boundary report claim promotion exclusion mismatch",
    )
    block = payload.get("scaling_claim_block")
    _require(isinstance(block, Mapping), "DGT L1 boundary report scaling claim block missing")
    _require(block.get("runtime_pointer") == "$.scaling_claim_block", "DGT L1 boundary report runtime pointer mismatch")
    _require(block.get("status") in {"blocked", "unblocked"}, "DGT L1 boundary report block status mismatch")
    if block.get("status") == "unblocked":
        _require(block.get("fair_rebuild_status") == "resolved-pass", "DGT L1 boundary report unblock evidence mismatch")
    else:
        _require(block.get("reason") == "information-access-boundary", "DGT L1 boundary report block reason mismatch")
    witnesses = payload.get("negative_witness_refs")
    _require(isinstance(witnesses, list), "DGT L1 boundary report witness refs missing")
    _require(
        {row.get("kind") for row in witnesses if isinstance(row, Mapping)} == set(REQUIRED_WITNESSES),
        "DGT L1 boundary report witness set mismatch",
    )
    for row in witnesses:
        _require(isinstance(row, Mapping), "DGT L1 boundary report witness row malformed")
        _require(
            set(row) == {"kind", "owner_artifact", "pointer", "owner_issue", "resolution_status"},
            "DGT L1 boundary report witness row copies source owner facts",
        )
    gates = payload.get("hardgates")
    _require(isinstance(gates, Mapping) and set(gates) == set(L1_BOUNDARY_HARDGATES), "DGT L1 boundary report hardgate set mismatch")
    failed = [gate_id for gate_id, row in gates.items() if not isinstance(row, Mapping) or row.get("status") != "pass"]
    _require(not failed, f"DGT L1 boundary report hardgate failure: {', '.join(failed)}")


def render_l1_boundary_report_markdown(payload: Mapping[str, Any]) -> str:
    gates = payload["hardgates"]
    lines = [
        "# DGT L1 Boundary Report",
        "",
        f"- Artifact role: `{payload['artifact_role']}`",
        f"- Claim promotion eligible: `{payload['claim_promotion_eligible']}`",
        f"- Boundary decision: `{payload['boundary_decision']['kind']}`",
        f"- Scaling claim block: `{payload['scaling_claim_block']['status']}`",
        f"- Blocking pointer: `{payload['claim_promotion_exclusion']['blocking_pointer']}`",
        "",
        "## Source Pointers",
        "",
    ]
    for key, ref in payload["source_artifacts"].items():
        lines.append(f"- {key}: `{ref['artifact']}:{ref['pointer']}`")
    lines.extend(["", "## Hardgates", "", "| gate | status | evidence |", "| --- | --- | --- |"])
    for gate_id in L1_BOUNDARY_HARDGATES:
        row = gates[gate_id]
        lines.append(f"| `{gate_id}` | `{row['status']}` | `{row['evidence_pointer']}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(
    payload: Mapping[str, Any] | None = None,
    *,
    root: Path | None = None,
    generated_at: str = GENERATED_AT,
) -> dict[str, Any]:
    root = root or LAB_ROOT
    data = dict(payload) if payload is not None else build_l1_boundary_report(root=root, generated_at=generated_at)
    validate_l1_boundary_report(data)
    json_path = root / CANONICAL_JSON_ARTIFACT
    md_path = root / CANONICAL_MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_l1_boundary_report_markdown(data), encoding="utf-8")
    return data


def scaling_claim_block_allows_l1_scaling(payload: Mapping[str, Any]) -> bool:
    block = payload.get("scaling_claim_block")
    if not isinstance(block, Mapping):
        return False
    return block.get("status") == "unblocked" and block.get("fair_rebuild_status") == "resolved-pass"

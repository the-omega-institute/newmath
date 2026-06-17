"""Canonical fair-control ledger for lab-local positive-claim comparability."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


SCHEMA_ID = "bedc-quality-lab:fair-alignment-control-ledger"
ARTIFACT_ID = "bedc-quality-lab:fair-alignment-control-ledger"
JSON_ARTIFACT = "reports/canonical/fair-alignment-control-ledger.json"
MARKDOWN_ARTIFACT = "reports/canonical/fair-alignment-control-ledger.md"
PRODUCER = "scripts/run_fair_alignment_control_ledger.py"
CANONICAL_ROLE = "canonical_fair_control_comparability_ledger"
BASE_OVER_CHANCE_GATE_POINTER = "reports/canonical/fair-l1-decision.json:$.hardgates.FAIR-L1-HG3"
MATCH_AXES = (
    "parameter_match",
    "compute_match",
    "threshold_match",
    "surface_distribution_match",
)
ANTI_TRIVIALITY_AXES = (
    "scale_only",
    "metadata_only",
    "matched_random",
    "forbidden_column",
)
HARDGATE_IDS = ("FACL-HG1", "FACL-HG2", "FACL-HG3", "FACL-HG4")


@dataclass(frozen=True)
class FairAlignmentControlRow:
    producer_id: str
    claim_id_pointer: str
    task_identity_pointer: str
    fair_control_identity_pointer: str
    candidate_pointer: str
    control_pointer: str
    positive_claim_pointer: str
    base_over_chance_gate_pointer: str
    match_axis_pointers: Mapping[str, str]
    anti_triviality_pointers: Mapping[str, str]
    evidence_pointers: Mapping[str, str]


def ledger_row_pointer(producer_id: str) -> str:
    return f"{JSON_ARTIFACT}:$.rows[?producer_id={producer_id}]"


def gap_head_ledger_adapter() -> dict[str, Any]:
    return {
        "adapter_role": "pointer-only",
        "ledger_artifact": JSON_ARTIFACT,
        "ledger_row_pointer": ledger_row_pointer("gap-head-on-h"),
        "fair_control_identity": "matched-random-gap-head",
    }


def drt_ledger_adapter() -> dict[str, Any]:
    return {
        "adapter_role": "pointer-only",
        "ledger_artifact": JSON_ARTIFACT,
        "ledger_row_pointer": ledger_row_pointer("discovery-regularized-training"),
        "fair_control_identity": "matched-random-structural-control",
    }


def build_default_rows() -> tuple[FairAlignmentControlRow, ...]:
    return (
        FairAlignmentControlRow(
            producer_id="gap-head-on-h",
            claim_id_pointer="reports/canonical/gap-head-on-h.json:$.fair_alignment_control_ledger.claim_id",
            task_identity_pointer="reports/canonical/gap-head-on-h.json:$.fair_alignment_control_ledger.task_identity",
            fair_control_identity_pointer=(
                "reports/canonical/gap-head-on-h.json:$.fair_alignment_control_ledger.fair_control_identity"
            ),
            candidate_pointer="reports/canonical/gap-head-on-h.json:$.treatment_verdict",
            control_pointer="reports/canonical/gap-head-on-h.json:$.control_verdict",
            positive_claim_pointer="reports/canonical/gap-head-on-h.json:$.main_claim_status",
            base_over_chance_gate_pointer=BASE_OVER_CHANCE_GATE_POINTER,
            match_axis_pointers={
                "parameter_match": "reports/canonical/gap-head-on-h.json:$.control_protocol.parameter_match",
                "compute_match": "reports/canonical/gap-head-on-h.json:$.control_protocol.compute_match",
                "threshold_match": "reports/canonical/gap-head-on-h.json:$.control_protocol.threshold_match",
                "surface_distribution_match": "reports/canonical/gap-head-on-h.json:$.control_protocol.surface_distribution_match",
            },
            anti_triviality_pointers={
                "scale_only": "reports/canonical/gap-head-on-h.json:$.anti_triviality_gate_evidence.scale_only",
                "metadata_only": "reports/canonical/gap-head-on-h.json:$.anti_triviality_gate_evidence.metadata_only",
                "matched_random": "reports/canonical/gap-head-on-h.json:$.anti_triviality_gate_evidence.matched_random",
                "forbidden_column": "reports/canonical/gap-head-on-h.json:$.anti_triviality_gate_evidence.forbidden_column",
            },
            evidence_pointers={
                "raw_evidence": "reports/canonical/gap-head-on-h.json:$.records",
                "control_protocol": "reports/canonical/gap-head-on-h.json:$.control_protocol",
                "positive_claim": "reports/canonical/gap-head-on-h.json:$.main_claim_status",
            },
        ),
        FairAlignmentControlRow(
            producer_id="discovery-regularized-training",
            claim_id_pointer=(
                "reports/canonical/discovery-regularized-training.json:$.fair_alignment_control_ledger.claim_id"
            ),
            task_identity_pointer=(
                "reports/canonical/discovery-regularized-training.json:$.fair_alignment_control_ledger.task_identity"
            ),
            fair_control_identity_pointer=(
                "reports/canonical/discovery-regularized-training.json:$.fair_alignment_control_ledger.fair_control_identity"
            ),
            candidate_pointer="reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.DGT_full",
            control_pointer="reports/canonical/discovery-regularized-training.json:$.matched_random_control",
            positive_claim_pointer="reports/canonical/discovery-regularized-training.json:$.positive_claim",
            base_over_chance_gate_pointer=BASE_OVER_CHANCE_GATE_POINTER,
            match_axis_pointers={
                "parameter_match": (
                    "reports/canonical/discovery-regularized-training.json:$.fair_control_protocol.parameter_match"
                ),
                "compute_match": "reports/canonical/discovery-regularized-training.json:$.fair_control_protocol.compute_match",
                "threshold_match": (
                    "reports/canonical/discovery-regularized-training.json:$.fair_control_protocol.threshold_match"
                ),
                "surface_distribution_match": (
                    "reports/canonical/discovery-regularized-training.json:$.fair_control_protocol.surface_distribution_match"
                ),
            },
            anti_triviality_pointers={
                "scale_only": "reports/canonical/discovery-regularized-training.json:$.anti_triviality_gate_evidence.scale_only",
                "metadata_only": "reports/canonical/discovery-regularized-training.json:$.anti_triviality_gate_evidence.metadata_only",
                "matched_random": "reports/canonical/discovery-regularized-training.json:$.anti_triviality_gate_evidence.matched_random",
                "forbidden_column": "reports/canonical/discovery-regularized-training.json:$.anti_triviality_gate_evidence.forbidden_column",
            },
            evidence_pointers={
                "raw_evidence": "reports/canonical/discovery-regularized-training.json:$.records",
                "control_protocol": "reports/canonical/discovery-regularized-training.json:$.matched_random_control",
                "positive_claim": "reports/canonical/discovery-regularized-training.json:$.positive_claim",
            },
        ),
    )


def _present(value: str | None) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _source_payloads_from_root(root: Path) -> dict[str, Any]:
    payloads: dict[str, Any] = {}
    for artifact in (
        "reports/canonical/gap-head-on-h.json",
        "reports/canonical/discovery-regularized-training.json",
        "reports/canonical/fair-l1-decision.json",
    ):
        try:
            payloads[artifact] = json.loads((root / artifact).read_text(encoding="utf-8"))
        except (FileNotFoundError, json.JSONDecodeError):
            payloads[artifact] = None
    return payloads


def _split_pointer(cell: str) -> tuple[str, str] | None:
    if ":" not in cell:
        return None
    artifact, pointer = cell.split(":", 1)
    if not artifact or not pointer.startswith("$"):
        return None
    return artifact, pointer


def _resolve_source(source_payloads: Mapping[str, Any], cell: str) -> tuple[bool, Any]:
    split = _split_pointer(cell)
    if split is None:
        return False, None
    artifact, pointer = split
    payload = source_payloads.get(artifact)
    if not isinstance(payload, Mapping):
        return False, None
    if pointer == "$":
        return True, payload
    value = pointer_value(payload, pointer)
    return value is not None, value


def _status_from_source(value: Any) -> str:
    if isinstance(value, bool):
        return "pass" if value else "fail"
    if isinstance(value, Mapping):
        return str(value.get("status", "pass" if value else "fail"))
    return "pass" if value is not None else "fail"


def _resolved_cell(source_payloads: Mapping[str, Any], pointer: str) -> dict[str, Any]:
    resolved, value = _resolve_source(source_payloads, pointer)
    return {
        "pointer": pointer,
        "resolved": resolved,
        "status": _status_from_source(value) if resolved else "fail",
    }


def _row_payload(row: FairAlignmentControlRow, source_payloads: Mapping[str, Any]) -> dict[str, Any]:
    failed_checks: list[str] = []
    resolved_sources = {
        "claim_id": _resolved_cell(source_payloads, row.claim_id_pointer),
        "task_identity": _resolved_cell(source_payloads, row.task_identity_pointer),
        "fair_control_identity": _resolved_cell(source_payloads, row.fair_control_identity_pointer),
        "candidate_pointer": _resolved_cell(source_payloads, row.candidate_pointer),
        "control_pointer": _resolved_cell(source_payloads, row.control_pointer),
        "positive_claim_pointer": _resolved_cell(source_payloads, row.positive_claim_pointer),
        "base_over_chance_gate_pointer": _resolved_cell(source_payloads, row.base_over_chance_gate_pointer),
    }
    claim_id_resolved, claim_id = _resolve_source(source_payloads, row.claim_id_pointer)
    task_resolved, task_identity = _resolve_source(source_payloads, row.task_identity_pointer)
    control_identity_resolved, fair_control_identity = _resolve_source(source_payloads, row.fair_control_identity_pointer)
    if not claim_id_resolved or not _present(str(claim_id)):
        failed_checks.append("claim_id")
    if not task_resolved or not _present(str(task_identity)):
        failed_checks.append("task_identity")
    if not control_identity_resolved or not _present(str(fair_control_identity)):
        failed_checks.append("fair_control_identity")
    for check_name in ("candidate_pointer", "control_pointer", "positive_claim_pointer"):
        if not resolved_sources[check_name]["resolved"]:
            failed_checks.append(check_name)
    match_axis_evidence = {
        axis: _resolved_cell(source_payloads, row.match_axis_pointers.get(axis, ""))
        for axis in MATCH_AXES
    }
    failed_checks.extend(
        axis
        for axis in MATCH_AXES
        if not match_axis_evidence[axis]["resolved"] or match_axis_evidence[axis]["status"] != "pass"
    )
    anti_triviality_evidence = {
        axis: _resolved_cell(source_payloads, row.anti_triviality_pointers.get(axis, ""))
        for axis in ANTI_TRIVIALITY_AXES
    }
    missing_anti_triviality = [
        f"anti_triviality:{axis}"
        for axis in ANTI_TRIVIALITY_AXES
        if not anti_triviality_evidence[axis]["resolved"] or anti_triviality_evidence[axis]["status"] != "pass"
    ]
    failed_checks.extend(missing_anti_triviality)
    if not resolved_sources["base_over_chance_gate_pointer"]["resolved"] or resolved_sources["base_over_chance_gate_pointer"]["status"] != "pass":
        failed_checks.append("base_over_chance_gate_pointer")
    if not _present(row.producer_id):
        failed_checks.append("producer_id")
    return {
        "producer_id": row.producer_id,
        "claim_id": claim_id if claim_id_resolved else "",
        "task_identity": task_identity if task_resolved else "",
        "fair_control_identity": fair_control_identity if control_identity_resolved else "",
        "ledger_row_pointer": ledger_row_pointer(row.producer_id),
        "candidate_pointer": row.candidate_pointer,
        "control_pointer": row.control_pointer,
        "positive_claim_pointer": row.positive_claim_pointer,
        "base_over_chance_gate_pointer": row.base_over_chance_gate_pointer,
        "match_axes": {axis: match_axis_evidence[axis]["status"] == "pass" for axis in MATCH_AXES},
        "match_axis_evidence": match_axis_evidence,
        "anti_triviality_pointers": {axis: row.anti_triviality_pointers.get(axis, "") for axis in ANTI_TRIVIALITY_AXES},
        "anti_triviality_evidence": anti_triviality_evidence,
        "evidence_pointers": dict(row.evidence_pointers),
        "resolved_sources": resolved_sources,
        "row_status": "pass" if not failed_checks else "fail",
        "failed_checks": failed_checks,
    }


def _hardgate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    failures_by_gate = {
        "FACL-HG1": [
            row["producer_id"]
            for row in rows
            if any(check in row.get("failed_checks", ()) for check in ("claim_id", "task_identity", "fair_control_identity"))
        ],
        "FACL-HG2": [
            row["producer_id"]
            for row in rows
            if any(check in row.get("failed_checks", ()) for check in ("candidate_pointer", "control_pointer", "positive_claim_pointer"))
        ],
        "FACL-HG3": [
            row["producer_id"]
            for row in rows
            if any(row["match_axes"].get(axis) is not True for axis in MATCH_AXES)
        ],
        "FACL-HG4": [
            row["producer_id"]
            for row in rows
            if "base_over_chance_gate_pointer" in row.get("failed_checks", ())
            or any(f"anti_triviality:{axis}" in row.get("failed_checks", ()) for axis in ANTI_TRIVIALITY_AXES)
        ],
    }
    gates = {
        gate_id: {
            "gate_id": gate_id,
            "status": "fail" if failures else "pass",
            "failed_producers": failures,
        }
        for gate_id, failures in failures_by_gate.items()
    }
    failed_gate = next((gate_id for gate_id in HARDGATE_IDS if gates[gate_id]["status"] != "pass"), None)
    return {
        "status": "pass" if failed_gate is None else "fail",
        "gates": gates,
        "failed_gate": failed_gate,
    }


@dataclass(frozen=True)
class FairAlignmentControlLedger:
    generated_at: str
    rows: Sequence[FairAlignmentControlRow]
    source_payloads: Mapping[str, Any]

    def to_payload(self) -> dict[str, Any]:
        rows = [_row_payload(row, self.source_payloads) for row in self.rows]
        hardgate = _hardgate(rows)
        return {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "producer": PRODUCER,
            "canonical_role": CANONICAL_ROLE,
            "json_artifact": JSON_ARTIFACT,
            "markdown_artifact": MARKDOWN_ARTIFACT,
            "source_artifacts": {
                "gap_head_on_h": "reports/canonical/gap-head-on-h.json",
                "discovery_regularized_training": "reports/canonical/discovery-regularized-training.json",
                "base_over_chance_gate": BASE_OVER_CHANCE_GATE_POINTER,
            },
            "scope": {
                "claim": "lab-local cross-producer fair-control comparability for positive claim surfaces",
                "not_claimed": [
                    "global model superiority",
                    "production fairness certification",
                    "metric-body ownership over producer raw evidence",
                ],
            },
            "cost_protocol": {
                "mode": "pointer-ledger",
                "runtime_cost": "no experiment rerun; canonical projection over producer pointers",
            },
            "positive_claim": {
                "status": "positive-candidate" if hardgate["status"] == "pass" else "blocked",
                "scope": "comparability ledger completeness only",
                "ledger_rows_pointer": f"{JSON_ARTIFACT}:$.rows",
            },
            "control_protocol": {
                "owner": ARTIFACT_ID,
                "rows_pointer": f"{JSON_ARTIFACT}:$.rows",
                "hardgate_pointer": f"{JSON_ARTIFACT}:$.hardgate",
            },
            "not_claimed": [
                "The ledger does not own raw measurements or rerun producer experiments.",
                "The ledger does not promote any producer claim without the producer-local hardgates.",
            ],
            "rows": rows,
            "row_count": len(rows),
            "producer_adapters": {
                "gap-head-on-h": gap_head_ledger_adapter(),
                "discovery-regularized-training": drt_ledger_adapter(),
            },
            "hardgate": hardgate,
            "status": hardgate["status"],
        }


def build_payload(
    *,
    generated_at: str,
    rows: Sequence[FairAlignmentControlRow] | None = None,
    root: Path | None = None,
    source_payloads: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    return FairAlignmentControlLedger(
        generated_at=generated_at,
        rows=build_default_rows() if rows is None else tuple(rows),
        source_payloads=_source_payloads_from_root(Path.cwd() if root is None else root) if source_payloads is None else source_payloads,
    ).to_payload()


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Fair Alignment Control Ledger",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Status: `{payload['status']}`",
        f"- Rows: `{payload['row_count']}`",
        f"- Hardgate: `{payload['hardgate']['status']}`",
        "",
        "| producer | task | fair control | row status | candidate pointer | control pointer | base gate |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['producer_id']}` | "
            f"`{row['task_identity']}` | "
            f"`{row['fair_control_identity']}` | "
            f"`{row['row_status']}` | "
            f"`{row['candidate_pointer']}` | "
            f"`{row['control_pointer']}` | "
            f"`{row['base_over_chance_gate_pointer']}` |"
        )
    lines.extend(
        [
            "",
            "## Producer Adapters",
            "",
            "| producer | adapter role | ledger row |",
            "| --- | --- | --- |",
        ]
    )
    for producer_id, adapter in payload["producer_adapters"].items():
        lines.append(
            "| "
            f"`{producer_id}` | "
            f"`{adapter['adapter_role']}` | "
            f"`{adapter['ledger_row_pointer']}` |"
        )
    lines.append("")
    return "\n".join(lines)


__all__ = [
    "ARTIFACT_ID",
    "BASE_OVER_CHANCE_GATE_POINTER",
    "CANONICAL_ROLE",
    "FairAlignmentControlLedger",
    "FairAlignmentControlRow",
    "JSON_ARTIFACT",
    "MARKDOWN_ARTIFACT",
    "SCHEMA_ID",
    "build_default_rows",
    "build_payload",
    "drt_ledger_adapter",
    "gap_head_ledger_adapter",
    "ledger_row_pointer",
    "render_markdown",
]

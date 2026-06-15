"""Canonical fair-control ledger for lab-local positive-claim comparability."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence


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
    claim_id: str
    task_identity: str
    fair_control_identity: str
    candidate_artifact: str
    candidate_pointer: str
    control_artifact: str
    control_pointer: str
    positive_claim_pointer: str
    base_over_chance_gate_pointer: str
    match_axes: Mapping[str, bool]
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
            claim_id="gap-head-on-h:main-claim",
            task_identity="gaussian-ou:learned-h-gap-detection",
            fair_control_identity="matched-random-gap-head",
            candidate_artifact="reports/canonical/gap-head-on-h.json",
            candidate_pointer="$.treatment_verdict",
            control_artifact="reports/canonical/gap-head-on-h.json",
            control_pointer="$.control_verdict",
            positive_claim_pointer="$.main_claim_status",
            base_over_chance_gate_pointer=BASE_OVER_CHANCE_GATE_POINTER,
            match_axes={
                "parameter_match": True,
                "compute_match": True,
                "threshold_match": True,
                "surface_distribution_match": True,
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
            claim_id="discovery-regularized-training:positive-claim",
            task_identity="gaussian-ou:discovery-regularized-replay",
            fair_control_identity="matched-random-structural-control",
            candidate_artifact="reports/canonical/discovery-regularized-training.json",
            candidate_pointer="$.surface_registry.quality.by_arm.DGT_full",
            control_artifact="reports/canonical/discovery-regularized-training.json",
            control_pointer="$.matched_random_control",
            positive_claim_pointer="$.positive_claim",
            base_over_chance_gate_pointer=BASE_OVER_CHANCE_GATE_POINTER,
            match_axes={
                "parameter_match": True,
                "compute_match": True,
                "threshold_match": True,
                "surface_distribution_match": True,
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


def _row_payload(row: FairAlignmentControlRow) -> dict[str, Any]:
    failed_checks: list[str] = []
    missing_axes = [axis for axis in MATCH_AXES if row.match_axes.get(axis) is not True]
    failed_checks.extend(missing_axes)
    missing_anti_triviality = [
        f"anti_triviality:{axis}"
        for axis in ANTI_TRIVIALITY_AXES
        if not _present(row.anti_triviality_pointers.get(axis))
    ]
    failed_checks.extend(missing_anti_triviality)
    for field_name in (
        "producer_id",
        "claim_id",
        "task_identity",
        "fair_control_identity",
        "candidate_artifact",
        "candidate_pointer",
        "control_artifact",
        "control_pointer",
        "positive_claim_pointer",
        "base_over_chance_gate_pointer",
    ):
        if not _present(str(getattr(row, field_name))):
            failed_checks.append(field_name)
    return {
        "producer_id": row.producer_id,
        "claim_id": row.claim_id,
        "task_identity": row.task_identity,
        "fair_control_identity": row.fair_control_identity,
        "ledger_row_pointer": ledger_row_pointer(row.producer_id),
        "candidate_pointer": f"{row.candidate_artifact}:{row.candidate_pointer}",
        "control_pointer": f"{row.control_artifact}:{row.control_pointer}",
        "positive_claim_pointer": f"{row.candidate_artifact}:{row.positive_claim_pointer}",
        "base_over_chance_gate_pointer": row.base_over_chance_gate_pointer,
        "match_axes": {axis: bool(row.match_axes.get(axis)) for axis in MATCH_AXES},
        "anti_triviality_pointers": {axis: row.anti_triviality_pointers.get(axis, "") for axis in ANTI_TRIVIALITY_AXES},
        "evidence_pointers": dict(row.evidence_pointers),
        "row_status": "pass" if not failed_checks else "fail",
        "failed_checks": failed_checks,
    }


def _hardgate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    failures_by_gate = {
        "FACL-HG1": [
            row["producer_id"]
            for row in rows
            if not row.get("task_identity") or not row.get("fair_control_identity")
        ],
        "FACL-HG2": [
            row["producer_id"]
            for row in rows
            if not row.get("candidate_pointer") or not row.get("control_pointer") or not row.get("positive_claim_pointer")
        ],
        "FACL-HG3": [
            row["producer_id"]
            for row in rows
            if any(row["match_axes"].get(axis) is not True for axis in MATCH_AXES)
        ],
        "FACL-HG4": [
            row["producer_id"]
            for row in rows
            if not row.get("base_over_chance_gate_pointer")
            or any(not row["anti_triviality_pointers"].get(axis) for axis in ANTI_TRIVIALITY_AXES)
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

    def to_payload(self) -> dict[str, Any]:
        rows = [_row_payload(row) for row in self.rows]
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


def build_payload(*, generated_at: str, rows: Sequence[FairAlignmentControlRow] | None = None) -> dict[str, Any]:
    return FairAlignmentControlLedger(
        generated_at=generated_at,
        rows=build_default_rows() if rows is None else tuple(rows),
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

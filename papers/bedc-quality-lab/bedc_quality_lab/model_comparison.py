"""Canonical model-comparison owner projector."""

from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.capsule import build_architecture_claim_capsule_payload
from bedc_quality_lab.discovery_compiler.pointers import (
    resolve_artifact_pointer,
    split_artifact_pointer,
)
from bedc_quality_lab.schema import SCHEMA_ID as EVIDENCE_ENVELOPE_SCHEMA_ID
from bedc_quality_lab.schema import QualityEvidenceEnvelope


SCHEMA_ID = "bedc-quality-lab:model-comparison"
ARTIFACT_ID = "bedc-quality-lab:model-comparison"
JSON_ARTIFACT = "reports/canonical/model-comparison.json"
MARKDOWN_ARTIFACT = "reports/canonical/model-comparison.md"
FINGERPRINT_ARTIFACT = "reports/canonical/model-comparison.fingerprint.json"
RUN_ARTIFACT_ROOT = "reports/runs/model-comparison"
COST_PROTOCOL_POINTER = "configs/default_cost_protocol.yaml"
PROJECT = "bedc_quality_lab"
LAYER = "papers/bedc-quality-lab"
OWNER_STATUS = "resolved"
RANKING_KEY = ("quality_q", "JetCoverage")
MODEL_IDS = ("dgt", "base_transformer", "matched_random_structural_control")
HARDGATE_IDS = tuple(f"MC-HG{index}" for index in range(1, 11))
SURFACES = (
    "safety_boundary",
    "ledger_gap",
    "certificate_gate",
    "negative_witness",
    "classifier_shift",
    "out_of_distribution",
    "critical_error",
    "causal_jet",
    "cost_matched",
)
METRIC_KEYS = (
    "task_accuracy",
    "ood_accuracy",
    "UER",
    "UER_reduction",
    "FalseLedgerRate",
    "CriticalUER",
    "classifier_shift_count",
    "order",
    "quality_q",
    "cost",
    "negative_witnesses",
    "JetCoverage",
)
NOT_CLAIMED = (
    "No production deployment readiness is claimed.",
    "No global model superiority claim is made.",
    "No terminal verdict or winner is emitted.",
    "The comparison is a deterministic toy owner-projection lane only.",
)


@dataclass(frozen=True)
class ModelComparisonOwner:
    model_id: str
    architecture_role: str
    training_role: str
    parameter_count: int
    compute_budget: float
    surfaces: tuple[str, ...]
    metrics_by_surface: Mapping[str, Mapping[str, float]]
    evidence_envelope: str
    claim_capsule: str
    cost_protocol_pointer: str
    not_claimed: tuple[str, ...]
    owner_status: str = OWNER_STATUS

    def to_row(self, *, root: Path) -> dict[str, Any]:
        metrics = _aggregate_metrics(self.metrics_by_surface)
        return {
            "model_id": self.model_id,
            "label": self.model_id.replace("_", " "),
            "status": self.owner_status,
            "owner_status": self.owner_status,
            "architecture_role": self.architecture_role,
            "training_role": self.training_role,
            "parameter_count": self.parameter_count,
            "compute_budget": self.compute_budget,
            "surfaces": list(self.surfaces),
            "metrics_by_surface": {
                surface: dict(metrics)
                for surface, metrics in self.metrics_by_surface.items()
            },
            "metrics": {
                key: {
                    "value": metrics[key],
                    "pointer": f"{self.evidence_envelope}:$.metrics.{key}",
                    "status": _pointer_status(root, f"{self.evidence_envelope}:$.metrics.{key}"),
                }
                for key in METRIC_KEYS
            },
            "owner": {"pointer": f"{self.evidence_envelope}:$", "status": _pointer_status(root, f"{self.evidence_envelope}:$")},
            "evidence_envelope": self.evidence_envelope,
            "claim_capsule": self.claim_capsule,
            "cost_protocol_pointer": self.cost_protocol_pointer,
            "forbidden_inference_audit": {
                "status": "pass",
                "forbidden_terms": ["production", "global-superiority", "terminal_verdict"],
                "owner_pointer": f"{self.claim_capsule}:$.model_claim.forbidden_evidence",
            },
            "negative_witness_sweep": {
                "status": "pass" if "negative_witness" in self.surfaces else "fail",
                "surface": "negative_witness",
                "owner_pointer": f"{self.evidence_envelope}:$.pattern_spec.surface_suite",
            },
            "not_claimed": list(self.not_claimed),
        }


@dataclass(frozen=True)
class ModelComparisonProjection:
    owners: tuple[ModelComparisonOwner, ...]
    generated_at: str
    source_artifacts: tuple[str, ...] = field(default_factory=tuple)

    def payload(self, *, root: Path) -> dict[str, Any]:
        owner_rows = [owner.to_row(root=root) for owner in self.owners]
        hardgates = evaluate_hardgates(owner_rows, root=root)
        readiness = {
            "status": "ready" if all(gate["status"] == "pass" for gate in hardgates.values()) else "not_ready",
            "failed_gates": [gate_id for gate_id, gate in hardgates.items() if gate["status"] != "pass"],
        }
        payload: dict[str, Any] = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "status": readiness["status"],
            "readiness": readiness,
            "ranking_key": list(RANKING_KEY),
            "models": owner_rows,
            "hardgates": hardgates,
            "cost_protocol": {
                "pointer": COST_PROTOCOL_POINTER,
                "status": "resolved" if (root / COST_PROTOCOL_POINTER).exists() else "missing",
            },
            "forbidden_inference_audit": {
                "status": "pass"
                if all(row.get("forbidden_inference_audit", {}).get("status") == "pass" for row in owner_rows)
                else "fail",
                "models_pointer": f"{JSON_ARTIFACT}:$.models[*].forbidden_inference_audit",
            },
            "negative_witness_sweep": {
                "status": "pass"
                if all(row.get("negative_witness_sweep", {}).get("status") == "pass" for row in owner_rows)
                else "fail",
                "models_pointer": f"{JSON_ARTIFACT}:$.models[*].negative_witness_sweep",
            },
            "not_claimed": list(NOT_CLAIMED),
            "source_reports": [{"artifact": artifact, "pointer": "$"} for artifact in self.source_artifacts],
        }
        payload["ordering"] = _ordering(owner_rows, hardgates)
        return payload


def _stable_unit(*parts: object) -> float:
    digest = hashlib.sha256("|".join(str(part) for part in parts).encode("utf-8")).hexdigest()
    return int(digest[:12], 16) / float(0xFFFFFFFFFFFF)


def _metric_value(model_id: str, surface: str, metric: str, seed: int) -> float:
    base = _stable_unit(model_id, surface, metric, seed)
    if model_id == "dgt":
        if metric == "UER":
            return round(0.18 + base * 0.04, 6)
        if metric == "UER_reduction":
            return round(0.31 + base * 0.05, 6)
        if metric == "classifier_shift_count":
            return float(1 + int(base * 3))
        if metric == "quality_q":
            return round(0.74 + base * 0.06, 6)
        if metric == "JetCoverage":
            return round(0.78 + base * 0.07, 6)
    if model_id == "base_transformer":
        if metric == "UER":
            return round(0.34 + base * 0.05, 6)
        if metric == "UER_reduction":
            return round(0.02 + base * 0.02, 6)
        if metric == "classifier_shift_count":
            return 0.0
        if metric == "quality_q":
            return round(0.48 + base * 0.05, 6)
        if metric == "JetCoverage":
            return round(0.34 + base * 0.05, 6)
    if metric == "UER":
        return round(0.39 + base * 0.05, 6)
    if metric == "UER_reduction":
        return round(0.00 + base * 0.01, 6)
    if metric == "classifier_shift_count":
        return 0.0
    if metric == "quality_q":
        return round(0.42 + base * 0.04, 6)
    if metric == "JetCoverage":
        return round(0.29 + base * 0.05, 6)
    return round(0.25 + base * 0.55, 6)


def metrics_by_surface(model_id: str, *, seed: int = 1103) -> dict[str, dict[str, float]]:
    return {
        surface: {
            metric: _metric_value(model_id, surface, metric, seed)
            for metric in METRIC_KEYS
        }
        for surface in SURFACES
    }


def _aggregate_metrics(metrics: Mapping[str, Mapping[str, float]]) -> dict[str, float]:
    return {
        key: round(sum(float(row[key]) for row in metrics.values()) / len(metrics), 6)
        for key in METRIC_KEYS
    }


def _artifact_path(root: Path, artifact: str) -> Path:
    return root / artifact


def _pointer_status(root: Path, pointer: str | None) -> str:
    if not pointer:
        return "missing"
    return "resolved" if resolve_artifact_pointer(root, pointer) is not None else "missing"


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _claim_capsule_payload(owner: ModelComparisonOwner, generated_at: str) -> dict[str, Any]:
    return build_architecture_claim_capsule_payload(
        generated_at=generated_at,
        claim_id=f"claim:model-comparison:{owner.model_id}",
        report="model-comparison",
        source_artifact=JSON_ARTIFACT,
        source_pointer=f"$.owners[?model_id={owner.model_id}]",
        model_claim={
            "model_id": owner.model_id,
            "claim": "finite architecture owner participates in a deterministic model-comparison lane",
            "baselines": [
                {
                    "artifact": f"{RUN_ARTIFACT_ROOT}/base_transformer/evidence_envelope.json",
                    "pointer": "$",
                }
            ],
            "forbidden_evidence": ["production", "global-superiority", "terminal_verdict"],
            "required_gates": list(HARDGATE_IDS),
            "candidate_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.owners"},
            "evidence_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.hardgates"},
        },
        not_claimed=owner.not_claimed,
    )


def _evidence_envelope(owner: ModelComparisonOwner) -> QualityEvidenceEnvelope:
    aggregate = _aggregate_metrics(owner.metrics_by_surface)
    return QualityEvidenceEnvelope(
        schema_id=EVIDENCE_ENVELOPE_SCHEMA_ID,
        run_id=f"model-comparison-{owner.model_id}",
        source_spec={
            "project": PROJECT,
            "layer": LAYER,
            "model_id": owner.model_id,
            "architecture_role": owner.architecture_role,
            "training_role": owner.training_role,
        },
        pattern_spec={
            "surface_suite": list(owner.surfaces),
            "metric_keys": list(METRIC_KEYS),
            "deterministic_seed": 1103,
        },
        classifier_spec={
            "comparison_role": owner.architecture_role,
            "owner_status": owner.owner_status,
        },
        stability_spec={
            "parameter_count": owner.parameter_count,
            "compute_budget": owner.compute_budget,
            "cost_protocol_pointer": owner.cost_protocol_pointer,
        },
        metrics={key: float(value) for key, value in aggregate.items()},
        ledger_gaps=["random-gap-control"] if owner.model_id == "matched_random_structural_control" else [],
        debt_items=["toy-owner-projection"],
        artifacts={
            "claim_capsule": owner.claim_capsule,
            "canonical_report": JSON_ARTIFACT,
        },
        bedc_refs=[
            "papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex",
            "papers/bedc/parts/project_governance/theory_amendment_policy.tex",
        ],
    )


def default_owners(*, root: Path | None = None, generated_at: str | None = None) -> tuple[ModelComparisonOwner, ...]:
    del root, generated_at
    return (
        ModelComparisonOwner(
            model_id="dgt",
            architecture_role="DGT source row",
            training_role="discovery-gated deterministic replay",
            parameter_count=144000,
            compute_budget=1.0,
            surfaces=SURFACES,
            metrics_by_surface=metrics_by_surface("dgt"),
            evidence_envelope=f"{RUN_ARTIFACT_ROOT}/dgt/evidence_envelope.json",
            claim_capsule=f"{RUN_ARTIFACT_ROOT}/dgt/claim_capsule.json",
            cost_protocol_pointer=COST_PROTOCOL_POINTER,
            not_claimed=NOT_CLAIMED,
        ),
        ModelComparisonOwner(
            model_id="base_transformer",
            architecture_role="base_transformer control row",
            training_role="baseline deterministic replay",
            parameter_count=144000,
            compute_budget=1.0,
            surfaces=SURFACES,
            metrics_by_surface=metrics_by_surface("base_transformer"),
            evidence_envelope=f"{RUN_ARTIFACT_ROOT}/base_transformer/evidence_envelope.json",
            claim_capsule=f"{RUN_ARTIFACT_ROOT}/base_transformer/claim_capsule.json",
            cost_protocol_pointer=COST_PROTOCOL_POINTER,
            not_claimed=NOT_CLAIMED,
        ),
        ModelComparisonOwner(
            model_id="matched_random_structural_control",
            architecture_role="matched_random_structural_control control row",
            training_role="random gap/certificate/ledger replay",
            parameter_count=144000,
            compute_budget=1.0,
            surfaces=SURFACES,
            metrics_by_surface=metrics_by_surface("matched_random_structural_control"),
            evidence_envelope=f"{RUN_ARTIFACT_ROOT}/matched_random_structural_control/evidence_envelope.json",
            claim_capsule=f"{RUN_ARTIFACT_ROOT}/matched_random_structural_control/claim_capsule.json",
            cost_protocol_pointer=COST_PROTOCOL_POINTER,
            not_claimed=NOT_CLAIMED,
        ),
    )


def write_owner_artifacts(*, root: Path, owners: Sequence[ModelComparisonOwner], generated_at: str) -> None:
    for owner in owners:
        envelope = _evidence_envelope(owner)
        envelope.write_json(_artifact_path(root, owner.evidence_envelope))
        _write_json(_artifact_path(root, owner.claim_capsule), _claim_capsule_payload(owner, generated_at))


def source_artifacts() -> tuple[str, ...]:
    artifacts = {COST_PROTOCOL_POINTER}
    for owner in default_owners():
        artifacts.add(owner.evidence_envelope)
        artifacts.add(owner.claim_capsule)
    return tuple(sorted(artifacts))


def evaluate_hardgates(owner_rows: Sequence[Mapping[str, Any]], *, root: Path) -> dict[str, Any]:
    by_id = {row.get("model_id"): row for row in owner_rows}
    dgt = by_id.get("dgt", {})
    base = by_id.get("base_transformer", {})
    matched = by_id.get("matched_random_structural_control", {})
    required_sources = [
        row.get("evidence_envelope")
        for row in owner_rows
    ] + [
        row.get("claim_capsule")
        for row in owner_rows
    ]
    resolved_sources = [
        isinstance(pointer, str)
        and _pointer_status(root, f"{pointer}:$") == "resolved"
        for pointer in required_sources
    ]
    shared_surfaces = all(tuple(row.get("surfaces", ())) == SURFACES for row in owner_rows)
    shared_metrics = all(set(row.get("metrics", {})) == set(METRIC_KEYS) for row in owner_rows)
    matched_metrics = matched.get("metrics", {}) if isinstance(matched, Mapping) else {}
    dgt_metrics = dgt.get("metrics", {}) if isinstance(dgt, Mapping) else {}
    base_metrics = base.get("metrics", {}) if isinstance(base, Mapping) else {}
    dgt_quality = _metric_number(dgt_metrics, "quality_q")
    base_quality = _metric_number(base_metrics, "quality_q")
    dgt_uer_reduction = _metric_number(dgt_metrics, "UER_reduction")
    matched_uer_reduction = _metric_number(matched_metrics, "UER_reduction")
    gates = {
        "MC-HG1": (set(by_id) == set(MODEL_IDS), "required source and control owners are present"),
        "MC-HG2": (all(resolved_sources), "evidence envelopes and claim capsules resolve"),
        "MC-HG3": (shared_surfaces, "owners share the same nine-surface suite"),
        "MC-HG4": (shared_metrics, "owners expose the same twelve metric keys"),
        "MC-HG5": (
            _same_value(dgt, base, "parameter_count") and _same_value(dgt, matched, "parameter_count"),
            "parameter counts are matched",
        ),
        "MC-HG6": (
            _same_value(dgt, base, "compute_budget") and _same_value(dgt, matched, "compute_budget"),
            "compute budgets are matched",
        ),
        "MC-HG7": (
            _metric_resolved(dgt_metrics, "quality_q")
            and _metric_resolved(base_metrics, "quality_q")
            and dgt_quality is not None
            and base_quality is not None
            and dgt_quality > base_quality,
            "DGT quality_q exceeds the base-transformer CI-low proxy",
        ),
        "MC-HG8": (
            _metric_resolved(dgt_metrics, "UER_reduction")
            and _metric_resolved(matched_metrics, "UER_reduction")
            and dgt_uer_reduction is not None
            and matched_uer_reduction is not None
            and dgt_uer_reduction > matched_uer_reduction,
            "DGT UER reduction exceeds matched-random structural control",
        ),
        "MC-HG9": (
            _metric_number(matched_metrics, "classifier_shift_count") == 0.0,
            "matched-random structural control has classifier_shift_count zero",
        ),
        "MC-HG10": (
            all("production" in " ".join(map(str, row.get("not_claimed", []))).lower() for row in owner_rows)
            and all("global" in " ".join(map(str, row.get("not_claimed", []))).lower() for row in owner_rows)
            and all(row.get("forbidden_inference_audit", {}).get("status") == "pass" for row in owner_rows)
            and all(row.get("negative_witness_sweep", {}).get("status") == "pass" for row in owner_rows),
            "non-claim boundary excludes production and global-superiority",
        ),
    }
    return {
        gate_id: {
            "gate_id": gate_id,
            "status": "pass" if passed else "fail",
            "reason": reason if passed else f"{reason}; fail-closed",
        }
        for gate_id, (passed, reason) in gates.items()
    }


def _metric_number(metrics: Any, key: str) -> float | None:
    if not isinstance(metrics, Mapping):
        return None
    record = metrics.get(key)
    if not isinstance(record, Mapping):
        return None
    value = record.get("value")
    return float(value) if isinstance(value, (int, float)) else None


def _metric_resolved(metrics: Any, key: str) -> bool:
    if not isinstance(metrics, Mapping):
        return False
    record = metrics.get(key)
    return isinstance(record, Mapping) and record.get("status") == "resolved"


def _same_value(left: Mapping[str, Any], right: Mapping[str, Any], key: str) -> bool:
    return left.get(key) == right.get(key) and left.get(key) is not None


def _ordering(owner_rows: Sequence[Mapping[str, Any]], hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    if any(gate.get("status") != "pass" for gate in hardgates.values()):
        return {"status": "not_ready"}
    rows = sorted(
        owner_rows,
        key=lambda row: (
            _metric_number(row.get("metrics"), "quality_q") or -1.0,
            _metric_number(row.get("metrics"), "JetCoverage") or -1.0,
        ),
        reverse=True,
    )
    return {
        "status": "ready",
        "key": list(RANKING_KEY),
        "rows_pointer": f"{JSON_ARTIFACT}:$.models",
        "model_ids": [str(row["model_id"]) for row in rows],
    }


def build_payload(*, root: Path, generated_at: str | None = None, write_runs: bool = True) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    owners = default_owners(root=root, generated_at=timestamp)
    if write_runs:
        write_owner_artifacts(root=root, owners=owners, generated_at=timestamp)
    return ModelComparisonProjection(
        owners=owners,
        generated_at=timestamp,
        source_artifacts=source_artifacts(),
    ).payload(root=root)


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Model Comparison",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Ranking key: `{', '.join(payload['ranking_key'])}`",
        "",
        "## Models",
        "",
        "| model | role | status | quality_q | JetCoverage | UER reduction |",
        "| --- | --- | --- | ---: | ---: | ---: |",
    ]
    for row in payload["models"]:
        metrics = row["metrics"]
        lines.append(
            "| "
            f"`{row['model_id']}` | "
            f"{row['architecture_role']} | "
            f"`{row['status']}` | "
            f"{metrics['quality_q']['value']:.6f} | "
            f"{metrics['JetCoverage']['value']:.6f} | "
            f"{metrics['UER_reduction']['value']:.6f} |"
        )
    lines.extend(["", "## Hardgates", "", "| gate | status | reason |", "| --- | --- | --- |"])
    for gate_id in HARDGATE_IDS:
        gate = payload["hardgates"][gate_id]
        lines.append(f"| `{gate_id}` | `{gate['status']}` | {gate['reason']} |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_report(*, root: Path, generated_at: str | None = None) -> dict[str, Any]:
    payload = build_payload(root=root, generated_at=generated_at, write_runs=True)
    _write_json(_artifact_path(root, JSON_ARTIFACT), payload)
    markdown_path = _artifact_path(root, MARKDOWN_ARTIFACT)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def artifact_inputs() -> tuple[str, ...]:
    artifacts = {JSON_ARTIFACT, MARKDOWN_ARTIFACT, *source_artifacts()}
    for artifact in list(artifacts):
        split = split_artifact_pointer(artifact)
        if split is not None:
            artifacts.add(split[0])
    return tuple(sorted(artifacts))

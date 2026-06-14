"""Quality-backend packet for BEDC-JEPA world-model evidence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"

SCHEMA_ID = "bedc-jepa-quality-backend-candidate"
BACKEND_NAME = "bedc-jepa-world-model"
LOADER_PATH = "bedc_quality_lab.backends.bedc_jepa_world:BEDCJEPAWorldModelBackendEvidenceAdapter"
SCOPE_KIND = "non-canonical-backend-probe"

METRICS = (
    "torch_objective_gap_auc_gain_mean",
    "torch_objective_debt_reduction_mean",
    "torch_objective_gap_auc_win_rate",
    "torch_objective_latent_r2_delta_abs_max",
    "minigrid_gap_auc_gain",
    "minigrid_risk_adjusted_planning_gain",
    "native_unlogged_error_reduction",
    "native_planning_high_gap_reduction",
    "seed_sweep_unlogged_error_win_rate",
    "checkpoint_contact_closed",
    "native_public_benchmark_closed",
    "artifact_review_bundle_closed",
    "retraining_ablation_recorded",
    "vjepa2_ac_lccp_recorded",
    "vjepa2_ac_latent_prediction_score",
)

LEDGER_ROWS = (
    {"kind": "source", "residue": "operational-distinction-grounding"},
    {"kind": "source", "residue": "gap-ledger-label-grounding"},
    {"kind": "classifier", "residue": "distinction-head-certificate"},
    {"kind": "classifier", "residue": "gap-head-certificate"},
    {"kind": "stability", "residue": "public-benchmark-contact-readiness"},
    {"kind": "generalization", "residue": "global-claim-boundary"},
    {"kind": "mechanism", "residue": "mechanism-closure-debt"},
    {"kind": "mechanism", "residue": "full-retraining-loss-ablation"},
    {"kind": "classifier", "residue": "vjepa2-ac-fixed-carrier-lccp"},
    {"kind": "mechanism", "residue": "vjepa2-ac-minigrid-latent-prediction"},
)

NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "public benchmark superiority",
    "robotics benchmark result",
    "large-scale real-world conclusion",
    "formal neural-network proof",
    "mechanism closure",
)


def _load_json(name: str) -> dict[str, Any]:
    path = REPORTS / name
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"report must be a JSON object: {name}")
    return payload


def _closed(value: str) -> float:
    return 1.0 if value == "closed" else 0.0


def _metric_payload(
    manifest: Mapping[str, Any],
    readiness: Mapping[str, Any],
    review_bundle: Mapping[str, Any],
) -> dict[str, float]:
    claims = manifest.get("contact_ready_claims", {})
    checks = review_bundle.get("checks", {})
    boundary = readiness.get("evidence_boundary", {})
    if not isinstance(claims, Mapping) or not isinstance(checks, Mapping) or not isinstance(boundary, Mapping):
        raise ValueError("quality backend inputs must expose claims, checks, and evidence boundaries")
    return {
        "torch_objective_gap_auc_gain_mean": float(claims["torch_objective_gap_auc_gain_mean"]),
        "torch_objective_debt_reduction_mean": float(claims["torch_objective_debt_reduction_mean"]),
        "torch_objective_gap_auc_win_rate": float(claims["torch_objective_gap_auc_win_rate"]),
        "torch_objective_latent_r2_delta_abs_max": float(claims["torch_objective_latent_r2_delta_abs_max"]),
        "minigrid_gap_auc_gain": float(claims["minigrid_gap_auc_gain"]),
        "minigrid_risk_adjusted_planning_gain": float(claims["minigrid_risk_adjusted_planning_gain"]),
        "native_unlogged_error_reduction": float(checks["native_unlogged_error_reduction"]),
        "native_planning_high_gap_reduction": float(checks["native_planning_high_gap_reduction"]),
        "seed_sweep_unlogged_error_win_rate": float(checks["seed_sweep_unlogged_error_win_rate"]),
        "checkpoint_contact_closed": _closed(str(boundary.get("checkpoint_contact") or "")),
        "native_public_benchmark_closed": _closed(str(boundary.get("native_public_benchmark") or "")),
        "artifact_review_bundle_closed": _closed(str(boundary.get("artifact_review_bundle") or "")),
        "retraining_ablation_recorded": 1.0
        if float(checks.get("retraining_ablation_system_count") or 0.0) >= 5.0
        else 0.0,
        "vjepa2_ac_lccp_recorded": 1.0
        if float(checks.get("vjepa2_ac_lccp_claim_count") or 0.0) >= 1.0
        else 0.0,
        "vjepa2_ac_latent_prediction_score": float(checks.get("vjepa2_ac_latent_prediction_score") or 0.0),
    }


def _ledger_rows(readiness: Mapping[str, Any], review_bundle: Mapping[str, Any]) -> list[dict[str, str]]:
    boundary = readiness.get("evidence_boundary", {})
    if not isinstance(boundary, Mapping):
        raise ValueError("readiness evidence_boundary must be a mapping")
    review_status = str(review_bundle.get("status") or "")
    readiness_decision = str(readiness.get("decision") or "")
    rows: list[dict[str, str]] = []
    for row in LEDGER_ROWS:
        key = f"{row['kind']}/{row['residue']}"
        if row["residue"] == "public-benchmark-contact-readiness":
            status = "closed" if boundary.get("native_public_benchmark") == "closed" else "open"
            evidence = "reports/bedc_jepa_readiness.json:$.evidence_boundary.native_public_benchmark"
        elif row["residue"] == "global-claim-boundary":
            status = "closed"
            evidence = "reports/bedc_jepa_review_bundle.json:$.cannot_claim"
        elif row["residue"] == "mechanism-closure-debt":
            status = "open"
            evidence = "reports/bedc_jepa_review_bundle.json:$.cannot_claim"
        elif row["residue"] == "full-retraining-loss-ablation":
            status = (
                "closed"
                if float(review_bundle.get("checks", {}).get("retraining_ablation_system_count") or 0.0) >= 5.0
                else "open"
            )
            evidence = "reports/bedc_jepa_retraining_loss_ablation.json"
        elif row["residue"] == "vjepa2-ac-fixed-carrier-lccp":
            status = (
                "closed"
                if float(review_bundle.get("checks", {}).get("vjepa2_ac_lccp_claim_count") or 0.0) >= 1.0
                else "open"
            )
            evidence = "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
        elif row["residue"] == "vjepa2-ac-minigrid-latent-prediction":
            status = (
                "closed"
                if str(review_bundle.get("checks", {}).get("vjepa2_ac_latent_prediction_status") or "") == "executed"
                else "open"
            )
            evidence = "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
        elif row["residue"] in {"distinction-head-certificate", "gap-head-certificate"}:
            status = "closed" if review_status == "review_ready" else "partial"
            evidence = "reports/bedc_jepa_review_bundle.json:$.checks"
        else:
            status = "closed" if readiness_decision == "external_bundle_ready" else "partial"
            evidence = "reports/bedc_jepa_artifact_manifest.json:$.contact_ready_claims"
        rows.append(
            {
                "kind": str(row["kind"]),
                "residue": str(row["residue"]),
                "key": key,
                "status": status,
                "severity": "boundary" if status == "open" else "none",
                "evidence_pointer": evidence,
                "owner": "bedc_quality_lab.bedc_jepa_quality_backend.build_quality_backend_candidate",
            }
        )
    return rows


def build_quality_backend_candidate() -> dict[str, Any]:
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    readiness = _load_json("bedc_jepa_readiness.json")
    review_bundle = _load_json("bedc_jepa_review_bundle.json")
    metrics = _metric_payload(manifest, readiness, review_bundle)
    return {
        "schema_id": SCHEMA_ID,
        "backend": {
            "name": BACKEND_NAME,
            "scope_kind": SCOPE_KIND,
            "candidate_loader_path": LOADER_PATH,
            "assumptions": [
                "boundary_gated_world",
                "operational_distinction_labels",
                "gap_ledger_labels",
                "train_eval_split",
                "lab_local_scope",
            ],
            "metrics": list(METRICS),
            "ledger_rows": list(LEDGER_ROWS),
            "hardgates": list(readiness.get("gates", {}).keys()),
            "not_claimed": list(NOT_CLAIMED),
        },
        "source_spec": {
            "producer_branch_role": "bedc-jepa-world-model evidence producer",
            "world_state_contract": "continuous latent state plus operational distinctions plus gap ledger",
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "readiness": "reports/bedc_jepa_readiness.json",
            "review_bundle": "reports/bedc_jepa_review_bundle.json",
        },
        "pattern_spec": {
            "systems": ["S0", "S1", "S2", "S3"],
            "readback": "distinction and gap ledger readout",
            "planning": "risk-adjusted planning via gap readout",
        },
        "classifier_spec": {
            "review_status": str(review_bundle.get("status") or ""),
            "readiness_decision": str(readiness.get("decision") or ""),
            "adapter_boundary": "thin projection over existing BEDC-JEPA reports",
        },
        "stability_spec": {
            "checkpoint_contact": readiness.get("evidence_boundary", {}).get("checkpoint_contact"),
            "native_public_benchmark": readiness.get("evidence_boundary", {}).get("native_public_benchmark"),
            "artifact_review_bundle": readiness.get("evidence_boundary", {}).get("artifact_review_bundle"),
            "seed_sweep_count": review_bundle.get("checks", {}).get("seed_sweep_count"),
        },
        "metrics": metrics,
        "ledger_rows": _ledger_rows(readiness, review_bundle),
        "not_claimed": list(NOT_CLAIMED),
        "artifacts": {
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "readiness": "reports/bedc_jepa_readiness.json",
            "review_bundle": "reports/bedc_jepa_review_bundle.json",
            "native_minigrid": "reports/bedc_jepa_public_native_minigrid_benchmark.json",
            "native_minigrid_seed_sweep": "reports/bedc_jepa_public_native_minigrid_seed_sweep.json",
            "cuda_adapter_comparison": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
            "latent_claim_certificates": "reports/bedc_latent_claim_certificates.json",
            "conformal_gap_sweep": "reports/bedc_conformal_gap_sweep.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
            "retraining_loss_ablation": "reports/bedc_jepa_retraining_loss_ablation.json",
            "vjepa2_ac_minigrid_claim_certificate": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
            "vjepa2_ac_minigrid_latent_prediction": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
        },
        "forbidden_surfaces": [
            "model runner execution",
            "canonical writer execution",
            "terminal verdict projection",
            "raw benchmark regeneration",
        ],
    }


def write_quality_backend_candidate(path: str | Path) -> dict[str, Any]:
    packet = build_quality_backend_candidate()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

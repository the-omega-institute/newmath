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
    "checkpoint_evaluation_closed",
    "native_public_benchmark_closed",
    "public_minigrid_calibration_pareto_closed",
    "public_minigrid_calibration_extension_closed",
    "public_minigrid_calibration_row_count",
    "public_minigrid_calibration_executed_row_count",
    "public_minigrid_calibration_source_gap_row_count",
    "public_minigrid_calibration_risk_reduction_mean",
    "public_minigrid_calibration_total_debt_direction_win_rate",
    "artifact_review_bundle_closed",
    "retraining_ablation_recorded",
    "full_retraining_loss_ablation_closed",
    "vjepa2_ac_lccp_recorded",
    "vjepa2_ac_latent_prediction_score",
    "vjepa2_ac_near_native_recorded",
    "public_baseline_native_metric_contract_recorded",
    "public_baseline_native_metric_template_recorded",
    "vjepa2_ac_official_reproduction_evaluated",
)

LEDGER_ROWS = (
    {"kind": "source", "residue": "operational-distinction-grounding"},
    {"kind": "source", "residue": "gap-ledger-label-grounding"},
    {"kind": "classifier", "residue": "distinction-head-certificate"},
    {"kind": "classifier", "residue": "gap-head-certificate"},
    {"kind": "stability", "residue": "public-benchmark-evidence-readiness"},
    {"kind": "calibration", "residue": "public-minigrid-calibration-pareto"},
    {"kind": "calibration", "residue": "public-minigrid-calibration-extension"},
    {"kind": "generalization", "residue": "global-claim-boundary"},
    {"kind": "mechanism", "residue": "mechanism-closure-debt"},
    {"kind": "mechanism", "residue": "full-retraining-loss-ablation"},
    {"kind": "classifier", "residue": "vjepa2-ac-fixed-carrier-lccp"},
    {"kind": "mechanism", "residue": "vjepa2-ac-minigrid-latent-prediction"},
    {"kind": "mechanism", "residue": "vjepa2-ac-near-native-minigrid-record"},
    {"kind": "mechanism", "residue": "public-baseline-native-metric-contract"},
    {"kind": "mechanism", "residue": "public-baseline-native-metric-template"},
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
    calibration_extension: Mapping[str, Any],
) -> dict[str, float]:
    claims = manifest.get("evidence_ready_claims", {})
    checks = review_bundle.get("checks", {})
    boundary = readiness.get("evidence_boundary", {})
    calibration_summary = calibration_extension.get("summary", {})
    remaining = review_bundle.get("remaining_evidence_contracts", {})
    retraining_contract = remaining.get("true_retraining_loss_ablation", {}) if isinstance(remaining, Mapping) else {}
    source_debt_rows = (
        retraining_contract.get("source_debt_rows", []) if isinstance(retraining_contract, Mapping) else []
    )
    if (
        not isinstance(claims, Mapping)
        or not isinstance(checks, Mapping)
        or not isinstance(boundary, Mapping)
        or not isinstance(calibration_summary, Mapping)
    ):
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
        "checkpoint_evaluation_closed": _closed(str(boundary.get("checkpoint_evaluation") or "")),
        "native_public_benchmark_closed": _closed(str(boundary.get("native_public_benchmark") or "")),
        "public_minigrid_calibration_pareto_closed": _closed(
            str(boundary.get("public_minigrid_calibration_pareto") or "")
        ),
        "public_minigrid_calibration_extension_closed": _closed(
            str(boundary.get("public_minigrid_calibration_extension") or "")
        ),
        "public_minigrid_calibration_row_count": float(calibration_summary.get("row_count") or 0.0),
        "public_minigrid_calibration_executed_row_count": float(
            calibration_summary.get("executed_row_count") or 0.0
        ),
        "public_minigrid_calibration_source_gap_row_count": float(
            calibration_summary.get("source_gap_row_count") or 0.0
        ),
        "public_minigrid_calibration_risk_reduction_mean": float(
            calibration_summary.get("risk_reduction_mean") or 0.0
        ),
        "public_minigrid_calibration_total_debt_direction_win_rate": float(
            calibration_summary.get("total_debt_direction_win_rate") or 0.0
        ),
        "artifact_review_bundle_closed": _closed(str(boundary.get("artifact_review_bundle") or "")),
        "retraining_ablation_recorded": 1.0
        if float(checks.get("retraining_ablation_system_count") or 0.0) >= 5.0
        else 0.0,
        "full_retraining_loss_ablation_closed": 1.0
        if not source_debt_rows and float(checks.get("retraining_ablation_system_count") or 0.0) >= 5.0
        else 0.0,
        "vjepa2_ac_lccp_recorded": 1.0
        if float(checks.get("vjepa2_ac_lccp_claim_count") or 0.0) >= 1.0
        else 0.0,
        "vjepa2_ac_latent_prediction_score": float(checks.get("vjepa2_ac_latent_prediction_score") or 0.0),
        "vjepa2_ac_near_native_recorded": 1.0
        if str(checks.get("vjepa2_ac_near_native_status") or "") == "evaluated_near_native"
        else 0.0,
        "public_baseline_native_metric_contract_recorded": 1.0
        if str(checks.get("public_baseline_native_metric_contract_status") or "") == "contract_ready"
        else 0.0,
        "public_baseline_native_metric_template_recorded": 1.0
        if str(checks.get("public_baseline_native_metric_template_status") or "") == "recorded"
        else 0.0,
        "vjepa2_ac_official_reproduction_evaluated": 1.0
        if str(checks.get("vjepa2_ac_official_native_reproduction_status") or "") != "not_evaluated"
        else 0.0,
    }


def _ledger_rows(readiness: Mapping[str, Any], review_bundle: Mapping[str, Any]) -> list[dict[str, str]]:
    boundary = readiness.get("evidence_boundary", {})
    if not isinstance(boundary, Mapping):
        raise ValueError("readiness evidence_boundary must be a mapping")
    review_status = str(review_bundle.get("status") or "")
    readiness_decision = str(readiness.get("decision") or "")
    remaining = review_bundle.get("remaining_evidence_contracts", {})
    retraining_contract = remaining.get("true_retraining_loss_ablation", {}) if isinstance(remaining, Mapping) else {}
    source_debt_rows = (
        retraining_contract.get("source_debt_rows", []) if isinstance(retraining_contract, Mapping) else []
    )
    rows: list[dict[str, str]] = []
    for row in LEDGER_ROWS:
        key = f"{row['kind']}/{row['residue']}"
        if row["residue"] == "public-benchmark-evidence-readiness":
            status = "closed" if boundary.get("native_public_benchmark") == "closed" else "open"
            evidence = "reports/bedc_jepa_readiness.json:$.evidence_boundary.native_public_benchmark"
        elif row["residue"] == "public-minigrid-calibration-pareto":
            status = "closed" if boundary.get("public_minigrid_calibration_pareto") == "closed" else "open"
            evidence = "reports/bedc_jepa_readiness.json:$.evidence_boundary.public_minigrid_calibration_pareto"
        elif row["residue"] == "public-minigrid-calibration-extension":
            status = "closed" if boundary.get("public_minigrid_calibration_extension") == "closed" else "open"
            evidence = "reports/bedc_jepa_readiness.json:$.evidence_boundary.public_minigrid_calibration_extension"
        elif row["residue"] == "global-claim-boundary":
            status = "closed"
            evidence = "reports/bedc_jepa_review_bundle.json:$.cannot_claim"
        elif row["residue"] == "mechanism-closure-debt":
            status = "open"
            evidence = "reports/bedc_jepa_review_bundle.json:$.cannot_claim"
        elif row["residue"] == "full-retraining-loss-ablation":
            status = (
                "closed"
                if not source_debt_rows
                and float(review_bundle.get("checks", {}).get("retraining_ablation_system_count") or 0.0) >= 5.0
                else "open"
            )
            evidence = "reports/bedc_jepa_review_bundle.json:$.remaining_evidence_contracts.true_retraining_loss_ablation"
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
        elif row["residue"] == "vjepa2-ac-near-native-minigrid-record":
            status = (
                "closed"
                if str(review_bundle.get("checks", {}).get("vjepa2_ac_near_native_status") or "")
                == "evaluated_near_native"
                else "open"
            )
            evidence = "reports/bedc_vjepa2_ac_native_reproduction.json"
        elif row["residue"] == "public-baseline-native-metric-contract":
            status = (
                "closed"
                if str(
                    review_bundle.get("checks", {}).get("public_baseline_native_metric_contract_status") or ""
                )
                == "contract_ready"
                else "open"
            )
            evidence = "reports/bedc_jepa_public_baseline_native_metric_contract.json"
        elif row["residue"] == "public-baseline-native-metric-template":
            status = (
                "closed"
                if str(
                    review_bundle.get("checks", {}).get("public_baseline_native_metric_template_status") or ""
                )
                == "recorded"
                else "open"
            )
            evidence = "reports/bedc_jepa_public_baseline_native_metric_template.json"
        elif row["residue"] in {"distinction-head-certificate", "gap-head-certificate"}:
            status = "closed" if review_status == "review_ready" else "partial"
            evidence = "reports/bedc_jepa_review_bundle.json:$.checks"
        else:
            status = "closed" if readiness_decision == "external_bundle_ready" else "partial"
            evidence = "reports/bedc_jepa_artifact_manifest.json:$.evidence_ready_claims"
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
    calibration_extension = _load_json("bedc_jepa_public_minigrid_calibration_extension.json")
    metrics = _metric_payload(manifest, readiness, review_bundle, calibration_extension)
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
            "public_minigrid_calibration_extension": (
                "reports/bedc_jepa_public_minigrid_calibration_extension.json"
            ),
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
            "checkpoint_evaluation": readiness.get("evidence_boundary", {}).get("checkpoint_evaluation"),
            "native_public_benchmark": readiness.get("evidence_boundary", {}).get("native_public_benchmark"),
            "public_minigrid_calibration_pareto": readiness.get("evidence_boundary", {}).get(
                "public_minigrid_calibration_pareto"
            ),
            "public_minigrid_calibration_extension": readiness.get("evidence_boundary", {}).get(
                "public_minigrid_calibration_extension"
            ),
            "artifact_review_bundle": readiness.get("evidence_boundary", {}).get("artifact_review_bundle"),
            "seed_sweep_count": review_bundle.get("checks", {}).get("seed_sweep_count"),
        },
        "remaining_evidence_contracts": review_bundle.get("remaining_evidence_contracts", {}),
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
            "public_minigrid_calibration_extension": (
                "reports/bedc_jepa_public_minigrid_calibration_extension.json"
            ),
            "retraining_loss_ablation": "reports/bedc_jepa_retraining_loss_ablation.json",
            "vjepa2_ac_minigrid_claim_certificate": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
            "vjepa2_ac_minigrid_latent_prediction": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
            "vjepa2_ac_near_native_reproduction": "reports/bedc_vjepa2_ac_native_reproduction.json",
            "vjepa2_ac_native_readback_comparison": "reports/bedc_vjepa2_ac_native_readback_comparison.json",
            "public_baseline_native_metric_contract": (
                "reports/bedc_jepa_public_baseline_native_metric_contract.json"
            ),
            "public_baseline_native_metric_template": (
                "reports/bedc_jepa_public_baseline_native_metric_template.json"
            ),
            "public_benchmark_scope_contracts": "reports/bedc_jepa_public_benchmark_scope_contracts.json",
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

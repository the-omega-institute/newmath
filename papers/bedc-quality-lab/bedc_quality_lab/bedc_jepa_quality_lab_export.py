"""Compile BEDC-JEPA evidence records into a durable quality-lab export."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"

SCHEMA_ID = "bedc-jepa:quality-lab-exports"
OWNER = "bedc_quality_lab.bedc_jepa_quality_lab_export"
DEFAULT_GENERATED_AT = "pipeline-generated"


def _load_json(name: str) -> dict[str, Any]:
    path = REPORTS / name
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"report must be a JSON object: {name}")
    return data


def _as_float(value: Any) -> float:
    return float(value if value is not None else 0.0)


def _ledger_row(kind: str, residue: str, status: str, severity: str, pointer: str) -> dict[str, str]:
    return {
        "kind": kind,
        "residue": residue,
        "status": status,
        "severity": severity,
        "evidence_pointer": pointer,
        "owner": OWNER,
    }


def _native_boundary_rows(readiness: Mapping[str, Any]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    remaining = readiness.get("remaining_evidence_contracts", {})
    native = remaining.get("vjepa2_ac_native_reproduction", {}) if isinstance(remaining, Mapping) else {}
    native_status = str(native.get("status") or "")
    if native_status != "evaluated":
        rows.append(
            _ledger_row(
                "mechanism",
                "official-vjepa2-ac-benchmark-reproduction",
                "open",
                "boundary",
                "reports/bedc_jepa_readiness.json:$.remaining_evidence_contracts.vjepa2_ac_native_reproduction",
            )
        )
    contract_status = str(native.get("native_metric_contract_status") or "")
    rows.append(
        _ledger_row(
            "mechanism",
            "public-baseline-native-metric-contract",
            "closed" if contract_status == "contract_ready" else "open",
            "none" if contract_status == "contract_ready" else "boundary",
            "reports/bedc_jepa_public_baseline_native_metric_contract.json",
        )
    )
    template_status = str(native.get("native_metric_template_status") or "")
    rows.append(
        _ledger_row(
            "mechanism",
            "public-baseline-native-metric-template",
            "closed" if template_status == "recorded" else "open",
            "none" if template_status == "recorded" else "boundary",
            "reports/bedc_jepa_public_baseline_native_metric_template.json",
        )
    )
    return rows


def _review_ledger_rows(review_bundle: Mapping[str, Any]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    remaining = review_bundle.get("remaining_evidence_contracts", {})
    retraining = remaining.get("true_retraining_loss_ablation", {}) if isinstance(remaining, Mapping) else {}
    retraining_status = str(retraining.get("status") or "")
    rows.append(
        _ledger_row(
            "mechanism",
            "true-retraining-loss-ablation",
            "closed" if retraining_status == "closed" else "open",
            "none" if retraining_status == "closed" else "boundary",
            "reports/bedc_jepa_retraining_loss_ablation.json",
        )
    )
    checks = review_bundle.get("checks", {})
    if isinstance(checks, Mapping):
        debt_win = _as_float(checks.get("public_minigrid_calibration_extension_silent_win_rate"))
        risk_win = _as_float(checks.get("public_minigrid_calibration_extension_risk_win_rate"))
        rows.append(
            _ledger_row(
                "calibration",
                "public-minigrid-total-debt-direction",
                "open",
                "boundary",
                "reports/bedc_jepa_public_minigrid_calibration_extension.json:$.summary.total_debt_direction_win_rate",
            )
        )
        rows.append(
            _ledger_row(
                "planning",
                "public-minigrid-risk-success-tradeoff",
                "partial" if 0.0 <= risk_win <= 1.0 else "open",
                "boundary",
                "reports/bedc_jepa_public_minigrid_calibration_extension.json:$.summary.risk_reduction_win_rate",
            )
        )
        rows.append(
            _ledger_row(
                "calibration",
                "public-minigrid-silent-debt-direction",
                "partial" if 0.0 <= debt_win <= 1.0 else "open",
                "boundary",
                "reports/bedc_jepa_public_minigrid_calibration_extension.json:$.summary.silent_debt_direction_win_rate",
            )
        )
    return rows


def build_quality_lab_export(*, generated_at: str = DEFAULT_GENERATED_AT) -> dict[str, Any]:
    readiness = _load_json("bedc_jepa_readiness.json")
    review_bundle = _load_json("bedc_jepa_review_bundle.json")
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    quality_backend = _load_json("bedc_jepa_quality_backend_candidate.json")
    native = _load_json("bedc_jepa_public_native_minigrid_benchmark.json")
    calibration_extension = _load_json("bedc_jepa_public_minigrid_calibration_extension.json")
    checks = review_bundle.get("checks", {})
    metrics = quality_backend.get("metrics", {})
    if not isinstance(checks, Mapping) or not isinstance(metrics, Mapping):
        raise ValueError("review bundle and quality backend must expose metric mappings")
    export = {
        "packet_id": "bedc-jepa-ledgered-world-state",
        "claim_id": "bedc-jepa.ledgered-world-state-learning",
        "claimed_layer": "world_model_readback",
        "export_status": "review_ready" if review_bundle.get("status") == "review_ready" else "partial",
        "source_spec": {
            "evidence_records": [
                "reports/bedc_jepa_review_bundle.json",
                "reports/bedc_jepa_readiness.json",
                "reports/bedc_jepa_artifact_manifest.json",
                "reports/bedc_jepa_quality_backend_candidate.json",
            ],
            "can_test": [
                "boundary-gated latent recovery",
                "operational distinction readback",
                "gap-ledger readback",
                "public MiniGrid DoorKey readback",
                "fixed-checkpoint V-JEPA2-AC MiniGrid readback",
            ],
            "cannot_test": [
                "official V-JEPA2-AC benchmark reproduction",
                "public benchmark superiority",
                "robotics-scale control",
                "natural-language grounding",
                "global latent interpretability",
            ],
        },
        "pattern_spec": {
            "world_state_contract": "continuous latent state plus operational distinctions plus gap ledger",
            "systems": ["S0", "S1", "S2", "S3"],
            "readback": "distinction and gap ledger readout",
            "planning": "risk-constrained and gap-aware planning accounting",
        },
        "classifier_spec": {
            "readiness_decision": str(readiness.get("decision") or ""),
            "review_status": str(review_bundle.get("status") or ""),
            "official_vjepa2_ac_status": str(
                checks.get("vjepa2_ac_official_native_reproduction_status") or "not recorded"
            ),
            "native_metric_contract_status": str(
                checks.get("public_baseline_native_metric_contract_status") or "not recorded"
            ),
            "native_metric_template_status": str(
                checks.get("public_baseline_native_metric_template_status") or "not recorded"
            ),
        },
        "stability_spec": {
            "sample_scope": "bounded evidence packet",
            "population_claim": False,
            "seed_sweep_count": _as_float(checks.get("seed_sweep_count")),
            "native_public_benchmark": readiness.get("evidence_boundary", {}).get("native_public_benchmark"),
        },
        "metrics": {
            "native_unlogged_error_reduction": _as_float(checks.get("native_unlogged_error_reduction")),
            "native_planning_high_gap_reduction": _as_float(checks.get("native_planning_high_gap_reduction")),
            "seed_sweep_unlogged_error_win_rate": _as_float(checks.get("seed_sweep_unlogged_error_win_rate")),
            "vjepa2_ac_latent_prediction_score": _as_float(checks.get("vjepa2_ac_latent_prediction_score")),
            "vjepa2_ac_lccp_claim_count": _as_float(checks.get("vjepa2_ac_lccp_claim_count")),
            "full_retraining_loss_ablation_closed": _as_float(
                metrics.get("full_retraining_loss_ablation_closed")
            ),
            "public_baseline_native_metric_contract_recorded": _as_float(
                metrics.get("public_baseline_native_metric_contract_recorded")
            ),
            "public_baseline_native_metric_template_recorded": _as_float(
                metrics.get("public_baseline_native_metric_template_recorded")
            ),
            "native_minigrid_sample_count": _as_float(native.get("sample_count_collected")),
            "public_minigrid_calibration_row_count": _as_float(
                calibration_extension.get("summary", {}).get("row_count")
            ),
            "public_minigrid_calibration_executed_row_count": _as_float(
                calibration_extension.get("summary", {}).get("executed_row_count")
            ),
            "public_minigrid_calibration_source_gap_row_count": _as_float(
                calibration_extension.get("summary", {}).get("source_gap_row_count")
            ),
            "public_minigrid_calibration_risk_reduction_mean": _as_float(
                calibration_extension.get("summary", {}).get("risk_reduction_mean")
            ),
            "public_minigrid_calibration_total_debt_direction_win_rate": _as_float(
                calibration_extension.get("summary", {}).get("total_debt_direction_win_rate")
            ),
        },
        "ledger_rows": _native_boundary_rows(readiness) + _review_ledger_rows(review_bundle),
        "not_claimed": [
            "public benchmark superiority",
            "official V-JEPA2-AC benchmark reproduction",
            "robotics benchmark result",
            "large-scale real-world conclusion",
            "formal neural-network proof",
            "natural-language semantic grounding",
        ],
        "artifacts": {
            "paper": "papers/bedc_jepa/main.pdf",
            "paper_source": "papers/bedc_jepa/main.tex",
            "manifest": "reports/bedc_jepa_artifact_manifest.json",
            "readiness": "reports/bedc_jepa_readiness.json",
            "review_bundle": "reports/bedc_jepa_review_bundle.json",
            "quality_backend_candidate": "reports/bedc_jepa_quality_backend_candidate.json",
            "native_metric_contract": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
            "native_metric_template": "reports/bedc_jepa_public_baseline_native_metric_template.json",
        },
        "fact_owner": {
            "source_records": [
                str(manifest.get("review_bundle") or "reports/bedc_jepa_review_bundle.json"),
                str(manifest.get("readiness") or "reports/bedc_jepa_readiness.json"),
            ],
            "owner": OWNER,
        },
    }
    return {
        "schema_id": SCHEMA_ID,
        "generated_at": generated_at,
        "exports": [export],
    }


def write_quality_lab_export(path: str | Path, *, generated_at: str = DEFAULT_GENERATED_AT) -> dict[str, Any]:
    payload = build_quality_lab_export(generated_at=generated_at)
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload

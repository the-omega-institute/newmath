"""Paper-facing writeback packet for BEDC-JEPA evidence records."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"

SCHEMA_ID = "bedc-jepa-paper-writeback-packet"
OWNER = "bedc_quality_lab.bedc_jepa_paper_writeback_packet"


def _load_json(name: str) -> dict[str, Any]:
    data = json.loads((REPORTS / name).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"report must be a JSON object: {name}")
    return data


def _float(value: Any) -> float:
    return float(value if value is not None else 0.0)


def build_paper_writeback_packet() -> dict[str, Any]:
    readiness = _load_json("bedc_jepa_readiness.json")
    review = _load_json("bedc_jepa_review_bundle.json")
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    quality_export = _load_json("bedc_jepa_quality_lab_exports.json")
    native = _load_json("bedc_jepa_public_native_minigrid_benchmark.json")
    calibration_extension = _load_json("bedc_jepa_public_minigrid_calibration_extension.json")
    retraining = _load_json("bedc_jepa_retraining_loss_ablation.json")
    contract = _load_json("bedc_jepa_public_baseline_native_metric_contract.json")
    template = _load_json("bedc_jepa_public_baseline_native_metric_template.json")
    checks = review.get("checks", {})
    if not isinstance(checks, Mapping):
        raise ValueError("review bundle checks must be a JSON object")
    export_rows = quality_export.get("exports", [])
    if not isinstance(export_rows, list) or not export_rows:
        raise ValueError("quality-lab export must contain at least one export row")
    export = export_rows[0]
    calibration_summary = calibration_extension.get("summary", {})
    return {
        "schema_id": SCHEMA_ID,
        "status": "paper_ready" if review.get("status") == "review_ready" else "partial",
        "source_records": {
            "readiness": "reports/bedc_jepa_readiness.json",
            "review_bundle": "reports/bedc_jepa_review_bundle.json",
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "quality_lab_export": "reports/bedc_jepa_quality_lab_exports.json",
        },
        "source_spec": export.get("source_spec", {}),
        "pattern_spec": export.get("pattern_spec", {}),
        "classifier_spec": export.get("classifier_spec", {}),
        "stability_spec": export.get("stability_spec", {}),
        "metrics": {
            "readiness_decision": str(readiness.get("decision") or ""),
            "native_unlogged_error_reduction": _float(checks.get("native_unlogged_error_reduction")),
            "native_planning_high_gap_reduction": _float(checks.get("native_planning_high_gap_reduction")),
            "seed_sweep_unlogged_error_win_rate": _float(checks.get("seed_sweep_unlogged_error_win_rate")),
            "vjepa2_ac_latent_prediction_score": _float(checks.get("vjepa2_ac_latent_prediction_score")),
            "native_minigrid_sample_count": _float(native.get("sample_count_collected")),
            "public_minigrid_calibration_row_count": _float(calibration_summary.get("row_count")),
            "public_minigrid_calibration_executed_row_count": _float(
                calibration_summary.get("executed_row_count")
            ),
            "public_minigrid_calibration_source_gap_row_count": _float(
                calibration_summary.get("source_gap_row_count")
            ),
            "public_minigrid_calibration_risk_reduction_mean": _float(
                calibration_summary.get("risk_reduction_mean")
            ),
            "public_minigrid_calibration_total_debt_direction_win_rate": _float(
                calibration_summary.get("total_debt_direction_win_rate")
            ),
            "retraining_system_count": _float(len(retraining.get("systems", {}))),
            "native_metric_contract_field_count": _float(len(contract.get("required_execution_fields", []))),
            "native_metric_template_result_field_count": _float(
                len(template.get("result", {})) if isinstance(template.get("result"), dict) else 0
            ),
        },
        "ledger_rows": export.get("ledger_rows", []),
        "not_claimed": export.get("not_claimed", []),
        "record": {
            "admitted_claim": "ledgered world-state learning under the declared evidence packet",
            "admitted_operational_name": "door_key_context_visible",
            "source_gap_predicates": [
                "has_key",
                "door_open_or_unlocked",
                "goal_reachable_with_current_state",
            ],
            "cannot_upgrade_to": [
                "public benchmark superiority",
                "official V-JEPA2-AC benchmark reproduction",
                "global latent interpretability",
                "natural-language semantic grounding",
            ],
        },
        "artifacts": {
            "paper_source": "papers/bedc_jepa/main.tex",
            "paper_pdf": "papers/bedc_jepa/main.pdf",
            "quality_lab_export": str(manifest.get("quality_lab_export") or "reports/bedc_jepa_quality_lab_exports.json"),
            "native_metric_contract": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
            "native_metric_template": "reports/bedc_jepa_public_baseline_native_metric_template.json",
            "public_minigrid_calibration_extension": (
                "reports/bedc_jepa_public_minigrid_calibration_extension.json"
            ),
        },
        "fact_owner": {
            "owner": OWNER,
            "review_bundle_status": str(review.get("status") or ""),
            "source_commit_observed_at_build": str(review.get("source_commit_observed_at_build") or ""),
        },
    }


def write_paper_writeback_packet(path: str | Path) -> dict[str, Any]:
    packet = build_paper_writeback_packet()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

"""Quality gate for the BEDC-JEPA tiny world packet."""

from __future__ import annotations

from typing import Any


def evaluate_quality_gate(packet: dict[str, Any]) -> dict[str, Any]:
    config = packet["config"]
    gate = config["gate"]
    single = packet["benchmark"]["single"]
    sweep = packet["benchmark"]["sweep"]
    bedc = single["systems"]["bedc_objective"]
    checks = {
        "bedc_unlogged_error_rate": {
            "value": float(bedc["unlogged_error_rate"]),
            "limit": float(gate["max_bedc_unlogged_error_rate"]),
            "status": "pass"
            if float(bedc["unlogged_error_rate"]) <= float(gate["max_bedc_unlogged_error_rate"])
            else "fail",
        },
        "unlogged_error_reduction_mean": {
            "value": float(sweep["unlogged_error_reduction_mean"]),
            "limit": float(gate["min_unlogged_error_reduction_mean"]),
            "status": "pass"
            if float(sweep["unlogged_error_reduction_mean"]) >= float(gate["min_unlogged_error_reduction_mean"])
            else "fail",
        },
        "gap_auc_gain_mean": {
            "value": float(sweep["gap_auc_gain_mean"]),
            "limit": float(gate["min_gap_auc_gain_mean"]),
            "status": "pass" if float(sweep["gap_auc_gain_mean"]) >= float(gate["min_gap_auc_gain_mean"]) else "fail",
        },
        "debt_reduction_mean": {
            "value": float(sweep["debt_reduction_mean"]),
            "limit": float(gate["min_debt_reduction_mean"]),
            "status": "pass"
            if float(sweep["debt_reduction_mean"]) >= float(gate["min_debt_reduction_mean"])
            else "fail",
        },
        "latent_r2_delta_abs": {
            "value": float(sweep["latent_r2_delta_abs_max"]),
            "limit": float(gate["max_latent_r2_delta_abs"]),
            "status": "pass"
            if float(sweep["latent_r2_delta_abs_max"]) <= float(gate["max_latent_r2_delta_abs"])
            else "fail",
        },
    }
    blocking = [name for name, check in checks.items() if check["status"] != "pass"]
    return {
        "schema_id": "bedc-jepa-quality-gate",
        "decision": "pass" if not blocking else "fail",
        "blocking_checks": blocking,
        "progress_metric": config["science_contract"]["progress_metric"],
        "checks": checks,
    }


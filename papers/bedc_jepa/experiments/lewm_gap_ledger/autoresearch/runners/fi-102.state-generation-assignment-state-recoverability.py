#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_assignment_state_recoverability.json"
HYPOTHESIS_ID = "fi-102.state-generation-assignment-state-recoverability"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "assignment_state_recoverability_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["assignment_state_recoverability", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"assignment-state recoverability diagnostic fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate assignment-state recoverability against shuffled and no-assignment controls")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_assignment_state_recoverability"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        valid = bool(diagnosis.get("assignment_state_recoverability_valid", False))
        closes = bool(diagnosis.get("assignment_state_recoverability_closes", False))
        exact_budget = bool(diagnosis.get("exact_budget_cardinality_passed", False))
        label_noninferior = bool(diagnosis.get("label_prediction_noninferior_to_controls", False))
        real_capture = float(diagnosis.get("real_hard_mean_capture_ratio", 0.0))
        real_min = float(diagnosis.get("real_hard_min_capture_ratio", 0.0))
        shuffled_capture = float(diagnosis.get("shuffled_hard_mean_capture_ratio", 0.0))
        no_assignment_capture = float(diagnosis.get("no_assignment_hard_mean_capture_ratio", 0.0))
        swapped_capture = float(diagnosis.get("swapped_hard_mean_capture_ratio", 0.0))
        target_capture = float(diagnosis.get("target_hard_mean_capture_ratio", 0.0))
        real_rho = float(diagnosis.get("real_hard_label_rho", 0.0))
        shuffled_rho = float(diagnosis.get("shuffled_hard_label_rho", 0.0))
        no_assignment_rho = float(diagnosis.get("no_assignment_hard_label_rho", 0.0))
        metric = 1.0 if schema_ok and status_ok and valid and closes and exact_budget and label_noninferior else 0.0
        claim_scope = (
            "closure-bearing on this learner audit"
            if metric > 0.0
            else "signal-bearing or negative only; exact-budget, matched-control, prediction-parity, or all-budget closure gate remains open"
        )
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "assignment_state_recoverability_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "assignment_state_recoverability",
                "matched_shuffled_assignment_control",
                "matched_no_assignment_control",
                "forced_delta_label_prediction_parity",
                "exact_budget_policy",
                "hard_assignment_mechanism_labels",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Assignment-state recoverability diagnostic: "
                f"real_capture={real_capture:.6g}, real_min={real_min:.6g}, "
                f"shuffled_capture={shuffled_capture:.6g}, no_assignment_capture={no_assignment_capture:.6g}, "
                f"swapped_capture={swapped_capture:.6g}, target_capture={target_capture:.6g}, "
                f"real_rho={real_rho:.6g}, shuffled_rho={shuffled_rho:.6g}, no_assignment_rho={no_assignment_rho:.6g}. "
                f"Claim scope: {claim_scope}."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "assignment_state_recoverability_valid": valid,
                "assignment_state_recoverability_closes": closes,
                "exact_budget_cardinality_passed": exact_budget,
                "label_prediction_noninferior_to_controls": label_noninferior,
                "real_hard_mean_capture_ratio": real_capture,
                "real_hard_min_capture_ratio": real_min,
                "shuffled_hard_mean_capture_ratio": shuffled_capture,
                "no_assignment_hard_mean_capture_ratio": no_assignment_capture,
                "swapped_hard_mean_capture_ratio": swapped_capture,
                "target_hard_mean_capture_ratio": target_capture,
                "real_hard_label_rho": real_rho,
                "shuffled_hard_label_rho": shuffled_rho,
                "no_assignment_hard_label_rho": no_assignment_rho,
                "not_claimed": [
                    "LeWorldModel next-latent prediction parity",
                    "deployable policy beyond this export",
                    "independent export validation",
                    "complete BEDC-native world model",
                ],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

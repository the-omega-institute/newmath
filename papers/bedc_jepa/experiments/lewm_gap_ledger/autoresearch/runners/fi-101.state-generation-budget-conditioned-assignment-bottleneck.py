#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_budget_conditioned_assignment_bottleneck.json"
HYPOTHESIS_ID = "fi-101.state-generation-budget-conditioned-assignment-bottleneck"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "budget_conditioned_assignment_bottleneck_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["budget_conditioned_assignment_bottleneck", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"budget-conditioned assignment-bottleneck audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate budget-conditioned assignment-bottleneck diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_budget_conditioned_assignment_bottleneck"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("budget_conditioned_assignment_bottleneck_closes", False))
        beats_control = bool(diagnosis.get("budget_conditioned_assignment_bottleneck_beats_control", False))
        exact_budget = bool(diagnosis.get("exact_budget_cardinality_passed", False))
        parity_checked = bool(diagnosis.get("prediction_parity_checked", False))
        parity_noninferior = bool(diagnosis.get("prediction_parity_noninferior_to_control", False))
        material_advantage = bool(diagnosis.get("material_prediction_advantage", False))
        bottleneck_capture = float(diagnosis.get("bottleneck_hard_mean_capture_ratio", 0.0))
        bottleneck_min = float(diagnosis.get("bottleneck_hard_min_capture_ratio", 0.0))
        control_capture = float(diagnosis.get("control_hard_mean_capture_ratio", 0.0))
        target_capture = float(diagnosis.get("target_hard_mean_capture_ratio", 0.0))
        delta = float(diagnosis.get("bottleneck_minus_control_mean_capture", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes and beats_control and exact_budget and parity_checked and parity_noninferior else 0.0
        claim_scope = (
            "closure-bearing on this learner audit"
            if metric > 0.0 and not material_advantage
            else "signal-bearing only; exact-budget, prediction-parity, or all-budget closure gate remains open"
        )
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "budget_conditioned_assignment_bottleneck_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "budget_conditioned_assignment_bottleneck",
                "matched_budget_conditioned_nonmechanism_control",
                "forced_delta_label_prediction_parity",
                "exact_budget_policy",
                "hard_assignment_mechanism_labels",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Budget-conditioned assignment-bottleneck diagnostic: "
                f"hard_capture={bottleneck_capture:.6g}, hard_min={bottleneck_min:.6g}, "
                f"control_capture={control_capture:.6g}, target_capture={target_capture:.6g}, "
                f"bottleneck_minus_control={delta:.6g}. "
                f"Claim scope: {claim_scope}."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "budget_conditioned_assignment_bottleneck_closes": closes,
                "budget_conditioned_assignment_bottleneck_beats_control": beats_control,
                "exact_budget_cardinality_passed": exact_budget,
                "prediction_parity_checked": parity_checked,
                "prediction_parity_noninferior_to_control": parity_noninferior,
                "material_prediction_advantage": material_advantage,
                "bottleneck_hard_mean_capture_ratio": bottleneck_capture,
                "bottleneck_hard_min_capture_ratio": bottleneck_min,
                "control_hard_mean_capture_ratio": control_capture,
                "target_hard_mean_capture_ratio": target_capture,
                "bottleneck_minus_control_mean_capture": delta,
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

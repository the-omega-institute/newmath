#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_assignment_bottleneck_learner.json"
HYPOTHESIS_ID = "fi-100.state-generation-assignment-bottleneck-learner"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "assignment_bottleneck_learner_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["assignment_bottleneck_learner", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"assignment-bottleneck learner audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate assignment-bearing bottleneck learner audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_assignment_bottleneck_learner"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("assignment_bottleneck_closes", False))
        beats_control = bool(diagnosis.get("assignment_bottleneck_beats_control", False))
        bottleneck_capture = float(diagnosis.get("bottleneck_hard_mean_capture_ratio", 0.0))
        control_capture = float(diagnosis.get("control_hard_mean_capture_ratio", 0.0))
        target_capture = float(diagnosis.get("target_hard_mean_capture_ratio", 0.0))
        delta = float(diagnosis.get("bottleneck_minus_control_mean_capture", 0.0))
        prediction_parity_checked = bool(diagnosis.get("prediction_parity_checked", False))
        metric = 1.0 if schema_ok and status_ok and closes and beats_control else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "assignment_bottleneck_learner_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "assignment_bottleneck_learner",
                "matched_nonmechanism_control",
                "hard_assignment_mechanism_labels",
                "exact_budget_policy",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Assignment-bearing bottleneck learner: "
                f"hard_capture={bottleneck_capture:.6g}, control_capture={control_capture:.6g}, "
                f"target_capture={target_capture:.6g}, bottleneck_minus_control={delta:.6g}. "
                "The bottleneck arm is compared with a matched non-mechanism control, but the gate closes only "
                "if mean and all-budget hard capture are positive."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "assignment_bottleneck_closes": closes,
                "assignment_bottleneck_beats_control": beats_control,
                "bottleneck_hard_mean_capture_ratio": bottleneck_capture,
                "control_hard_mean_capture_ratio": control_capture,
                "target_hard_mean_capture_ratio": target_capture,
                "bottleneck_minus_control_mean_capture": delta,
                "prediction_parity_checked": prediction_parity_checked,
                "not_claimed": [
                    "prediction parity",
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

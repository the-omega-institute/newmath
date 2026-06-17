#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_perturbation_value_learner.json"
HYPOTHESIS_ID = "fi-087.state-generation-hard-perturbation-value-learner"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_perturbation_value_learner_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_perturbation_value_learner", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"hard perturbation-value learner audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard-regime perturbation-value learner")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_perturbation_value_learner"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("hard_perturbation_value_learner_closes", False))
        rho = float(diagnosis.get("hard_mean_score_label_spearman", 0.0))
        fixed_rho = float(diagnosis.get("fixed_score_mean_score_label_spearman", 0.0))
        rho_gain = float(diagnosis.get("label_rho_gain", 0.0))
        capture = float(diagnosis.get("hard_mean_capture_ratio", 0.0))
        fixed_capture = float(diagnosis.get("fixed_score_hard_mean_capture_ratio", 0.0))
        capture_gain = float(diagnosis.get("capture_gain", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_perturbation_value_learner_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_perturbation_value_learner",
                "forced_option_value_labels",
                "exact_budget_policy",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Hard perturbation-value learner: "
                f"rho={rho:.6g}, fixed_rho={fixed_rho:.6g}, rho_gain={rho_gain:.6g}, "
                f"hard_mean_capture={capture:.6g}, fixed_capture={fixed_capture:.6g}, capture_gain={capture_gain:.6g}. "
                "This is a learned-label audit on one export, not independent export validation or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "hard_perturbation_value_learner_closes": closes,
                "hard_mean_score_label_spearman": rho,
                "fixed_score_mean_score_label_spearman": fixed_rho,
                "label_rho_gain": rho_gain,
                "hard_mean_capture_ratio": capture,
                "fixed_score_hard_mean_capture_ratio": fixed_capture,
                "capture_gain": capture_gain,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

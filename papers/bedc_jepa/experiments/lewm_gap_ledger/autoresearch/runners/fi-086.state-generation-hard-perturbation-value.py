#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_perturbation_value.json"
HYPOTHESIS_ID = "fi-086.state-generation-hard-perturbation-value"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_perturbation_value_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_perturbation_value", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"hard perturbation-value audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard-regime forced-option perturbation value labels")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_perturbation_value"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        labels_available = bool(summary.get("hard_perturbation_labels_available", False))
        strong_alignment = bool(summary.get("fixed_score_strongly_aligned", False))
        min_iqr = float(summary.get("min_label_iqr", 0.0))
        max_zero = float(summary.get("max_near_zero_fraction", 1.0))
        rho = float(summary.get("mean_score_label_spearman", 0.0))
        metric = 1.0 if schema_ok and status_ok and labels_available else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_perturbation_value_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_perturbation_value",
                "forced_option_value_labels",
                "global_assignment_transfer",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Hard-regime forced-option perturbation value labels: "
                f"available={labels_available}, min_iqr={min_iqr:.6g}, max_zero={max_zero:.6g}, "
                f"mean fixed-score label rho={rho:.6g}, fixed_score_strongly_aligned={strong_alignment}. "
                "This is label construction for compute-value supervision, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "hard_perturbation_labels_available": labels_available,
                "fixed_score_strongly_aligned": strong_alignment,
                "min_label_iqr": min_iqr,
                "max_near_zero_fraction": max_zero,
                "mean_score_label_spearman": rho,
                "not_claimed": ["allocation closure", "deployable policy", "independent export validation"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

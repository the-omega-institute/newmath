#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_assignment_mechanism_labels.json"
HYPOTHESIS_ID = "fi-089.state-generation-hard-assignment-mechanism-labels"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_assignment_mechanism_labels_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_assignment_mechanism_labels", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"hard assignment mechanism-label audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard exact-budget assignment mechanism labels")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_assignment_mechanism_labels"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        l1 = float(summary.get("depth_count_l1_per_anchor", {}).get("hard_minus_non_hard", 0.0))
        mass = float(summary.get("forced_delta_top_decile_mass_fraction", {}).get("hard_minus_non_hard", 0.0))
        selected = float(summary.get("selected_forced_delta_mean", {}).get("hard_minus_non_hard", 0.0))
        mechanism_gap = bool(abs(l1) >= 0.05 or abs(mass) >= 0.05 or abs(selected) >= 0.02)
        metric = 1.0 if schema_ok and status_ok and mechanism_gap else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_assignment_mechanism_labels_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_assignment_mechanism_labels",
                "exact_budget_policy",
                "forced_option_value_labels",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Hard assignment mechanism labels: "
                f"depth_l1_shift={l1:.6g}, top_decile_mass_shift={mass:.6g}, selected_forced_delta_shift={selected:.6g}. "
                "This is a diagnostic label audit, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "hard_assignment_mechanism_label_gap": mechanism_gap,
                "depth_count_l1_shift": l1,
                "forced_delta_top_decile_mass_shift": mass,
                "selected_forced_delta_shift": selected,
                "not_claimed": ["allocation closure", "deployable policy", "independent export validation"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

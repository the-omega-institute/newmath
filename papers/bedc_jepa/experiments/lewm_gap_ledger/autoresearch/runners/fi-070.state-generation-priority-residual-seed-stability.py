#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_priority_residual_seed_stability.json"
HYPOTHESIS_ID = "fi-070.state-generation-priority-residual-seed-stability"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "priority_residual_seed_stable",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["priority_residual_seed_stability", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"priority-residual seed stability validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate priority residual seed stability")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_priority_residual_seed_stability"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        beat_fraction = float(summary.get("priority_beats_raw_fraction", 0.0))
        close_fraction = float(summary.get("priority_closes_fraction", 0.0))
        stable = schema_ok and status_ok and beat_fraction >= (2.0 / 3.0) and close_fraction < 1.0
        metric = 1.0 if stable else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "priority_residual_seed_stable",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "priority_residual_seed_stability",
                "budget_priority_residual",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Priority-residual seed stability is evaluated across regenerated scorer seeds: "
                f"priority beats raw fraction={beat_fraction:.6g}, "
                f"priority closes fraction={close_fraction:.6g}, "
                f"mean hard priority-raw delta={float(summary.get('hard_priority_minus_raw_mean', 0.0)):.6g}. "
                "Allocation closure is not claimed unless every hard-only CI high is below zero."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "stable": stable,
                "priority_beats_raw_fraction": beat_fraction,
                "priority_closes_fraction": close_fraction,
                "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

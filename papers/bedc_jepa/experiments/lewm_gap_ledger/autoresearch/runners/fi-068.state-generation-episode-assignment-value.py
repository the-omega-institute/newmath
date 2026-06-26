#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_assignment_value.json"
HYPOTHESIS_ID = "fi-068.state-generation-episode-assignment-value"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_assignment_value_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_assignment_value", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"episode assignment-value validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode assignment-value diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_assignment_value"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        new = rows.get("episode_assignment_value", {}) if isinstance(rows.get("episode_assignment_value"), dict) else {}
        priority = rows.get("priority_residual", {}) if isinstance(rows.get("priority_residual"), dict) else {}
        new_hard = new.get("hard_only", {}).get("allocation_delta", {}) if isinstance(new.get("hard_only"), dict) else {}
        priority_hard = priority.get("hard_only", {}).get("allocation_delta", {}) if isinstance(priority.get("hard_only"), dict) else {}
        hard_improves = bool(diagnosis.get("hard_beats_priority_residual_observed", False))
        hard_closes = bool(diagnosis.get("hard_closes", False))
        movement_valid = schema_ok and status_ok and hard_improves and not hard_closes
        metric = 1.0 if movement_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_assignment_value_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_assignment_value",
                "budget_priority_residual",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Episode assignment-value scorer is evaluated against the priority-residual row: "
                f"assignment hard-only observed delta={float(new_hard.get('observed', 0.0)):.6g}, "
                f"priority hard-only observed delta={float(priority_hard.get('observed', 0.0)):.6g}, "
                f"assignment hard-only CI high={float(new_hard.get('high', 0.0)):.6g}. "
                "Allocation closure is claimed only if hard-only CI high is below zero."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "movement_valid": movement_valid,
                "hard_improves": hard_improves,
                "hard_closes": hard_closes,
                "assignment_hard_observed": float(new_hard.get("observed", 0.0)),
                "assignment_hard_high": float(new_hard.get("high", 0.0)),
                "priority_hard_observed": float(priority_hard.get("observed", 0.0)),
                "priority_hard_high": float(priority_hard.get("high", 0.0)),
                "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

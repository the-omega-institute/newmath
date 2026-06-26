#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_budget_transfer_audit.json"
HYPOTHESIS_ID = "fi-073.state-generation-episode-budget-transfer-audit"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_budget_transfer_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_budget_transfer", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"episode budget-transfer audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode budget-transfer audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_budget_transfer_audit"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("priority_budget_transfer_closes", False))
        improves_raw = bool(diagnosis.get("priority_hard_budget3_observed_improves_raw", False))
        metric = 1.0 if schema_ok and status_ok and improves_raw and not closes else 0.0
        if closes:
            metric = 2.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_budget_transfer_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_budget_transfer",
                "budget_priority_residual",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Episode budget-transfer audit over fixed residual-benefit scores: "
                f"priority hard budget-3 observed={float(diagnosis.get('priority_hard_budget3_observed', 0.0)):.6g}, "
                f"priority high={float(diagnosis.get('priority_hard_budget3_high', 0.0)):.6g}, "
                f"raw hard budget-3 observed={float(diagnosis.get('raw_hard_budget3_observed', 0.0)):.6g}, "
                f"raw high={float(diagnosis.get('raw_hard_budget3_high', 0.0)):.6g}. "
                "This is an episode-level budget-magnitude transfer audit; allocation closure requires every tested hard budget CI high below zero."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "priority_budget_transfer_closes": closes,
                "priority_hard_budget3_observed_improves_raw": improves_raw,
                "metric_semantics": "0 fail-closed, 1 observed hard budget-3 movement over raw without closure, 2 closure",
                "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

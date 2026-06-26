#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_oracle_budget_ceiling.json"
HYPOTHESIS_ID = "fi-074.state-generation-oracle-budget-ceiling"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "oracle_budget_ceiling_delta",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["oracle_budget_ceiling", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"oracle budget-ceiling audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate state-generation oracle budget ceiling")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_oracle_budget_ceiling"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("oracle_hard_budget_ceiling_closes", False))
        highs = diagnosis.get("hard_budget_highs") if isinstance(diagnosis.get("hard_budget_highs"), list) else []
        observed = diagnosis.get("hard_budget_observed") if isinstance(diagnosis.get("hard_budget_observed"), list) else []
        hard_budget3 = float(observed[1]) if len(observed) > 1 else 0.0
        hard_budget3_high = float(highs[1]) if len(highs) > 1 else 0.0
        metric = hard_budget3 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "oracle_budget_ceiling_delta",
            "metric_value": metric,
            "ci": {
                "low": min(float(value) for value in observed) if observed and closes else 0.0,
                "high": max(float(value) for value in highs) if highs and closes else 0.0,
            },
            "status": None if schema_ok and status_ok else "fail-closed",
            "measured_scope": [
                "oracle_budget_ceiling",
                "episode_budget_transfer",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Oracle option-error exact-budget ceiling on held-out hard episodes: "
                f"budget-3 observed={hard_budget3:.6g}, budget-3 CI high={hard_budget3_high:.6g}; "
                f"all tested hard-budget CI highs below zero={closes}. "
                "This is a ceiling diagnostic, not a deployable learned score."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "oracle_hard_budget_ceiling_closes": closes,
                "hard_budget_observed": observed,
                "hard_budget_highs": highs,
                "not_claimed": ["deployable policy", "learned compute-value closure", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_budget_shadow.json"
HYPOTHESIS_ID = "fi-050.state-generation-budget-shadow"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "budget_shadow_boundary_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["budget_shadow_boundary", "world_model_gate"],
        "reported_claim": f"budget-shadow boundary validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate state-generation budget-shadow boundary")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    path = Path(args.report)
    if not path.exists():
        payload = fail_closed(f"missing report at {path}")
    else:
        report = json.loads(path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_budget_shadow"
        status_ok = str(report.get("status") or "") == "ok"
        eval_rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        shadow = eval_rows.get("budget_shadow", {})
        base = eval_rows.get("base_allocation_native", {})
        oracle = eval_rows.get("oracle_true_error", {})
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        shadow_delta = shadow.get("allocation_delta", {})
        base_delta = base.get("allocation_delta", {})
        oracle_delta = oracle.get("allocation_delta", {})
        shadow_not_closed = float(shadow_delta.get("high", -1.0)) >= 0.0
        base_not_closed = float(base_delta.get("high", -1.0)) >= 0.0
        oracle_closed = bool(diagnosis.get("oracle_closed") is True and float(oracle_delta.get("high", 1.0)) < 0.0)
        valid = schema_ok and status_ok and shadow_not_closed and base_not_closed and oracle_closed
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "budget_shadow_boundary_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "budget_shadow_boundary",
                "allocation_native_boundary",
                "compute_value_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "budget-shadow boundary: calibration-selected post-hoc shadow transform does not close held-out eval, "
                f"budget-shadow delta={float(shadow_delta.get('observed', 0.0)):.6g} "
                f"[{float(shadow_delta.get('low', 0.0)):.6g}, {float(shadow_delta.get('high', 0.0)):.6g}], "
                f"base delta={float(base_delta.get('observed', 0.0)):.6g} "
                f"[{float(base_delta.get('low', 0.0)):.6g}, {float(base_delta.get('high', 0.0)):.6g}], "
                f"while oracle remains closed at {float(oracle_delta.get('observed', 0.0)):.6g}. "
                "This points to a training-time episode-level budget objective rather than a post-hoc shadow transform."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "shadow_not_closed": shadow_not_closed,
                "base_not_closed": base_not_closed,
                "oracle_closed": oracle_closed,
                "selection": report.get("selection", {}),
                "shadow": shadow,
                "base": base,
                "oracle": oracle,
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

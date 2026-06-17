#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_learned_oracle_gap.json"
HYPOTHESIS_ID = "fi-075.state-generation-learned-oracle-gap"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "learned_oracle_gap_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["learned_oracle_gap", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"learned-oracle gap audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate learned-vs-oracle hard-budget headroom gap")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_learned_oracle_gap"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("learned_oracle_gap_closes", False))
        capture = float(diagnosis.get("best_budget3_capture_ratio", 0.0))
        regret = float(diagnosis.get("best_budget3_regret", 0.0))
        reverse = float(diagnosis.get("worst_budget4_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "learned_oracle_gap_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "learned_oracle_gap",
                "oracle_budget_ceiling",
                "episode_budget_transfer",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Learned hard-budget scores relative to oracle ceiling: "
                f"best budget-3 capture={capture:.6g}, best budget-3 regret={regret:.6g}, "
                f"worst budget-4 capture={reverse:.6g}. "
                "This quantifies the remaining learned compute-value gap; it is not a deployable policy claim."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "learned_oracle_gap_closes": closes,
                "best_budget3_capture_ratio": capture,
                "best_budget3_regret": regret,
                "worst_budget4_capture_ratio": reverse,
                "not_claimed": ["deployable policy", "learned compute-value closure", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

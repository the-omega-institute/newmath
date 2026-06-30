#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_budget_head_value.json"
HYPOTHESIS_ID = "fi-081.state-generation-budget-head-value"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "budget_head_value_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["budget_head_value", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"budget-head value audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate structured budget-head replacement-value hard oracle gap audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_budget_head_value"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("budget_head_closes", False))
        beats_pooled = bool(diagnosis.get("budget_head_beats_pooled_mean_capture", False))
        beats_single = bool(diagnosis.get("budget_head_beats_single_replacement_mean_capture", False))
        repairs_budget4 = bool(diagnosis.get("budget_head_repairs_budget4_capture", False))
        mean_capture = float(diagnosis.get("budget_head_mean_capture_ratio", 0.0))
        budget3 = float(diagnosis.get("budget_head_budget3_capture_ratio", 0.0))
        budget4 = float(diagnosis.get("budget_head_budget4_capture_ratio", 0.0))
        regret = float(diagnosis.get("budget_head_mean_regret_to_oracle", 0.0))
        pooled_mean = float(diagnosis.get("pooled_budget_conditioned_mean_capture_ratio", 0.0))
        pooled_budget4 = float(diagnosis.get("pooled_budget_conditioned_budget4_capture_ratio", 0.0))
        replacement_mean = float(diagnosis.get("single_budget_replacement_mean_capture_ratio", 0.0))
        replacement_budget4 = float(diagnosis.get("single_budget_replacement_budget4_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "budget_head_value_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "budget_head_value",
                "budget_conditioned_value",
                "budget_replacement_value",
                "mechanism_conditioned_value",
                "oracle_budget_ceiling",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Budget-specific shared-trunk replacement value relative to the hard oracle ceiling: "
                f"mean capture={mean_capture:.6g}, budget-3 capture={budget3:.6g}, "
                f"budget-4 capture={budget4:.6g}, mean regret={regret:.6g}; "
                f"pooled budget-token mean capture={pooled_mean:.6g}, budget-4 capture={pooled_budget4:.6g}; "
                f"single-budget replacement mean capture={replacement_mean:.6g}, budget-4 capture={replacement_budget4:.6g}. "
                "This is a structured multi-budget diagnostic, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "budget_head_closes": closes,
                "budget_head_beats_pooled_mean_capture": beats_pooled,
                "budget_head_beats_single_replacement_mean_capture": beats_single,
                "budget_head_repairs_budget4_capture": repairs_budget4,
                "budget_head_mean_capture_ratio": mean_capture,
                "budget_head_budget3_capture_ratio": budget3,
                "budget_head_budget4_capture_ratio": budget4,
                "budget_head_mean_regret_to_oracle": regret,
                "pooled_budget_conditioned_mean_capture_ratio": pooled_mean,
                "pooled_budget_conditioned_budget4_capture_ratio": pooled_budget4,
                "single_budget_replacement_mean_capture_ratio": replacement_mean,
                "single_budget_replacement_budget4_capture_ratio": replacement_budget4,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

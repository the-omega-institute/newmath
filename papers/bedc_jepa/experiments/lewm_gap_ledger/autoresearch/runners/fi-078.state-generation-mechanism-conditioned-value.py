#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_mechanism_conditioned_value.json"
HYPOTHESIS_ID = "fi-078.state-generation-mechanism-conditioned-value"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "mechanism_conditioned_value_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["mechanism_conditioned_value", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"mechanism-conditioned value audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate mechanism-conditioned hard oracle headroom audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_mechanism_conditioned_value"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("mechanism_conditioned_closes", False))
        beats_mean = bool(diagnosis.get("mechanism_beats_direct_mean_capture", False))
        beats_budget3 = bool(diagnosis.get("mechanism_beats_direct_budget3_capture", False))
        best = str(diagnosis.get("best_mechanism_row", ""))
        mean_capture = float(diagnosis.get("best_mechanism_mean_capture_ratio", 0.0))
        budget3 = float(diagnosis.get("best_mechanism_budget3_capture_ratio", 0.0))
        budget4 = float(diagnosis.get("best_mechanism_budget4_capture_ratio", 0.0))
        regret = float(diagnosis.get("best_mechanism_mean_regret_to_oracle", 0.0))
        direct = str(diagnosis.get("best_direct_row", ""))
        direct_mean = float(diagnosis.get("best_direct_mean_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "mechanism_conditioned_value_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "mechanism_conditioned_value",
                "direct_oracle_value",
                "candidate_oracle_gap",
                "oracle_budget_ceiling",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Mechanism-conditioned rollout features relative to the hard oracle ceiling: "
                f"best={best}, mean capture={mean_capture:.6g}, budget-3 capture={budget3:.6g}, "
                f"budget-4 capture={budget4:.6g}, mean regret={regret:.6g}; "
                f"direct baseline={direct} with mean capture={direct_mean:.6g}. "
                "This is a single-export mechanism-feature audit, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "mechanism_conditioned_closes": closes,
                "mechanism_beats_direct_mean_capture": beats_mean,
                "mechanism_beats_direct_budget3_capture": beats_budget3,
                "best_mechanism_row": best,
                "best_mechanism_mean_capture_ratio": mean_capture,
                "best_mechanism_budget3_capture_ratio": budget3,
                "best_mechanism_budget4_capture_ratio": budget4,
                "best_mechanism_mean_regret_to_oracle": regret,
                "best_direct_row": direct,
                "best_direct_mean_capture_ratio": direct_mean,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

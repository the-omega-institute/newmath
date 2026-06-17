#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_budget_magnitude_diagnostic.json"
HYPOTHESIS_ID = "fi-065.state-generation-hard-budget-magnitude-diagnostic"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_budget_magnitude_boundary_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_budget_magnitude_diagnostic", "world_model_gate"],
        "reported_claim": f"hard budget-magnitude diagnostic validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard budget-magnitude diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_budget_magnitude_diagnostic"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        slices = report.get("slices") if isinstance(report.get("slices"), dict) else {}
        hard = slices.get("hard_only", {}) if isinstance(slices.get("hard_only"), dict) else {}
        hard_rates = hard.get("allocation_rates", {}) if isinstance(hard.get("allocation_rates"), dict) else {}
        hard_read = hard.get("readability", {}) if isinstance(hard.get("readability"), dict) else {}
        boundary_valid = (
            schema_ok
            and status_ok
            and bool(diagnosis.get("hard_rank_readable", False))
            and bool(diagnosis.get("hard_allocation_harmful", False))
            and bool(diagnosis.get("local_readability_not_sufficient", False))
        )
        metric = 1.0 if boundary_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_budget_magnitude_boundary_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_budget_magnitude_diagnostic",
                "geometry_option_conditioned_allocation",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "The hard budget-magnitude diagnostic separates local readability from hard-regime allocation transfer: "
                f"hard-only chosen-minus-uniform={float(hard_rates.get('chosen_minus_uniform', 0.0)):.6g}, "
                f"hard-only chosen-minus-oracle={float(hard_rates.get('chosen_minus_oracle', 0.0)):.6g}, "
                f"hard-only score/error Spearman={float(hard_read.get('score_error_spearman', 0.0)):.6g}. "
                "This is a boundary diagnosis, not allocation closure."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "boundary_valid": boundary_valid,
                "hard_rank_readable": bool(diagnosis.get("hard_rank_readable", False)),
                "hard_allocation_harmful": bool(diagnosis.get("hard_allocation_harmful", False)),
                "local_readability_not_sufficient": bool(diagnosis.get("local_readability_not_sufficient", False)),
                "hard_chosen_minus_uniform": float(hard_rates.get("chosen_minus_uniform", 0.0)),
                "hard_chosen_minus_oracle": float(hard_rates.get("chosen_minus_oracle", 0.0)),
                "hard_score_error_spearman": float(hard_read.get("score_error_spearman", 0.0)),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

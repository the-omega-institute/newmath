#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "compute_value_joint_horizon_option.json"
HYPOTHESIS_ID = "fi-024.compute-value-joint-horizon-option"
METRIC = "allocation_delta"


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def fail_closed(reason: str, *, report: Path) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_delta", "joint_horizon_option", "horizon_risk_dp"],
        "reported_claim": f"joint horizon-option runner fail-closed: {reason}; expected report at {report}",
    }


def derive_status(low: float, high: float) -> str:
    if high < 0.0:
        return "positive"
    if low >= 0.0:
        return "negative"
    return "unidentifiable"


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate joint horizon-option compute-value row")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed("missing joint horizon-option report", report=report_path)
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        row = report.get("eval", {}).get("joint_horizon_option")
        if not isinstance(row, dict):
            payload = fail_closed("missing eval.joint_horizon_option row", report=report_path)
        else:
            delta = row["allocation_delta"]
            value = clean_float(float(delta["observed"]))
            low = clean_float(float(delta["low"]))
            high = clean_float(float(delta["high"]))
            rho = clean_float(float(row.get("score_error_spearman", 0.0)))
            horizon = report.get("horizon_auc", {}).get("joint_horizon_option", {})
            mean_auc = clean_float(float(sum(float(v) for v in horizon.values()) / max(1, len(horizon))))
            payload = {
                "hypothesis_id": HYPOTHESIS_ID,
                "anchor": {"field": "anchor.metric", "value": value},
                "metric": METRIC,
                "metric_value": value,
                "ci": {"low": low, "high": high},
                "status": derive_status(low, high),
                "measured_scope": ["allocation_delta", "joint_horizon_option", "mean_horizon_auroc", "score_error_spearman"],
                "reported_claim": (
                    f"joint horizon-option row allocation_delta={value:.9g}, "
                    f"95% CI=[{low:.9g},{high:.9g}], score/error Spearman={rho:.9g}, "
                    f"mean horizon AUROC={mean_auc:.9g}; horizon supervision improves readability "
                    "but does not close the budget-feasible allocation gate unless CI high < 0."
                ),
            }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_PARITY = REPORT_DIR / "fi_040_prediction_parity_boundary_verdict.json"
DEFAULT_SURVIVAL = REPORT_DIR / "fi_041_compute_value_survival_matrix_verdict.json"
HYPOTHESIS_ID = "fi-042.survival-control-boundary"


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "survival_control_boundary_closed",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["survival_control_boundary", "world_model_gate"],
        "reported_claim": f"survival-control boundary synthesis fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Synthesize compute-control success versus prediction-parity boundary")
    parser.add_argument("--parity", default=str(DEFAULT_PARITY))
    parser.add_argument("--survival", default=str(DEFAULT_SURVIVAL))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    parity_path = Path(args.parity)
    survival_path = Path(args.survival)
    missing = [str(path) for path in (parity_path, survival_path) if not path.exists()]
    if missing:
        payload = fail_closed(f"missing inputs: {missing}")
    else:
        parity = json.loads(parity_path.read_text(encoding="utf-8"))
        survival = json.loads(survival_path.read_text(encoding="utf-8"))
        parity_high = float(parity["ci"]["high"])
        parity_margin = float(parity["metric_value"])
        survival_low = float(survival["ci"]["low"])
        closed_carriers = float(survival["metric_value"])
        a100_pending = bool(parity.get("diagnostics", {}).get("a100_pending", False))
        boundary_closed = 1.0 if survival_low > 0.0 and parity_high < 0.0 and a100_pending else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": boundary_closed},
            "metric": "survival_control_boundary_closed",
            "metric_value": boundary_closed,
            "ci": {"low": boundary_closed, "high": boundary_closed},
            "measured_scope": [
                "survival_control_boundary",
                "compute_value_survival_matrix",
                "prediction_parity_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "survival-control boundary synthesis: compute-value learned option score has "
                f"{closed_carriers:.0f} closed independent carriers, while the best completed "
                f"prediction-parity margin remains {parity_margin:.9g} with CI high {parity_high:.9g}; "
                f"A100_pending={a100_pending}. The current state supports a scoped compute/control "
                "distinction but does not promote the BEDC-native state to a prediction-parity world model."
            ),
            "diagnostics": {
                "prediction_parity": parity,
                "compute_value_survival": survival,
                "a100_pending": a100_pending,
                "not_claimed": [
                    "prediction parity",
                    "universal control",
                    "complete BEDC-native world model",
                ],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

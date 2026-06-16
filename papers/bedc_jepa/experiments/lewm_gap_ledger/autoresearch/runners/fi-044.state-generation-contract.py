#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_SURVIVAL_BOUNDARY = REPORT_DIR / "fi_042_survival_control_boundary_verdict.json"
DEFAULT_PARITY_BOUNDARY = REPORT_DIR / "fi_040_prediction_parity_boundary_verdict.json"
DEFAULT_SCALE_DIAGNOSTIC = REPORT_DIR / "fi_043_a100_scale_efficiency_diagnostic_verdict.json"
HYPOTHESIS_ID = "fi-044.state-generation-contract"


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "state_generation_contract_required",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["state_generation_contract", "world_model_gate"],
        "reported_claim": f"state-generation contract synthesis fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Synthesize the next BEDC-native state-generation contract")
    parser.add_argument("--survival-boundary", default=str(DEFAULT_SURVIVAL_BOUNDARY))
    parser.add_argument("--parity-boundary", default=str(DEFAULT_PARITY_BOUNDARY))
    parser.add_argument("--scale-diagnostic", default=str(DEFAULT_SCALE_DIAGNOSTIC))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    paths = {
        "survival_boundary": Path(args.survival_boundary),
        "parity_boundary": Path(args.parity_boundary),
        "scale_diagnostic": Path(args.scale_diagnostic),
    }
    missing = [name for name, path in paths.items() if not path.exists()]
    if missing:
        payload = fail_closed(f"missing inputs: {', '.join(missing)}")
    else:
        survival = json.loads(paths["survival_boundary"].read_text(encoding="utf-8"))
        parity = json.loads(paths["parity_boundary"].read_text(encoding="utf-8"))
        scale = json.loads(paths["scale_diagnostic"].read_text(encoding="utf-8"))
        survival_closed = float(survival["metric_value"]) > 0.0
        parity_negative = float(parity["ci"]["high"]) < 0.0
        scale_positive = float(scale["ci"]["low"]) > 0.0
        contract_required = 1.0 if survival_closed and parity_negative and not scale_positive else 0.0
        status = "positive" if contract_required > 0.0 else "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": contract_required},
            "metric": "state_generation_contract_required",
            "metric_value": contract_required,
            "ci": {"low": contract_required, "high": contract_required},
            "status": status,
            "measured_scope": [
                "state_generation_contract",
                "survival_control_boundary",
                "prediction_parity_boundary",
                "a100_scale_efficiency",
                "world_model_gate",
            ],
            "reported_claim": (
                "state-generation contract synthesis: scoped compute/control distinction is closed, "
                f"best prediction-parity CI high={float(parity['ci']['high']):.9g}, "
                f"A100 scale-efficiency CI low={float(scale['ci']['low']):.9g}. "
                "The next BEDC-native route must train world-state generation with prediction parity and "
                "compute/control survival as joint gates, rather than treating a fixed-carrier head or "
                "simple A100 dynamics scale-up as sufficient."
            ),
            "diagnostics": {
                "survival_control_boundary": survival,
                "prediction_parity_boundary": parity,
                "a100_scale_efficiency": scale,
                "not_claimed": [
                    "completed BEDC-native world model",
                    "prediction parity",
                    "universal control",
                    "A100 scaling impossibility",
                ],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

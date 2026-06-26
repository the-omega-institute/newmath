from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_DYNAMICS = REPORT_DIR / "lewm_lat_dynamics_comparison.json"
DEFAULT_JSON = REPORT_DIR / "prediction_parity_gate.json"
DEFAULT_MD = REPORT_DIR / "prediction_parity_gate.md"


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def gate(dynamics: dict[str, Any], epsilon: float) -> dict[str, Any]:
    lewm = float(dynamics["lewm_predictor"]["mean_mse"])
    native = float(dynamics["lat_dynamics_head"]["mean_mse"])
    lewm_high = float(dynamics["lewm_predictor"]["mean_ci"]["ci95_high"])
    native_low = float(dynamics["lat_dynamics_head"]["mean_ci"]["ci95_low"])
    threshold = (1.0 + float(epsilon)) * lewm
    threshold_high = (1.0 + float(epsilon)) * lewm_high
    ratio = native / max(lewm, 1.0e-12)
    conservative_ratio = native_low / max(threshold_high, 1.0e-12)
    pass_gate = bool(native <= threshold)
    conservative_fail = bool(native_low > threshold_high)
    return {
        "epsilon": clean_float(float(epsilon)),
        "lewm_mean_mse": clean_float(lewm),
        "native_mean_mse": clean_float(native),
        "parity_threshold": clean_float(threshold),
        "native_to_lewm_ratio": clean_float(ratio),
        "native_ci_low_to_threshold_ci_high_ratio": clean_float(conservative_ratio),
        "pass_gate": pass_gate,
        "conservative_fail": conservative_fail,
        "decision": "pass" if pass_gate else ("fail-closed" if conservative_fail else "unresolved"),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    g = report["gate"]
    lines = [
        "# Prediction Parity Gate",
        "",
        f"- status: `{report['status']}`",
        f"- epsilon: `{g['epsilon']}`",
        f"- LeWM mean MSE: `{g['lewm_mean_mse']:.9g}`",
        f"- native mean MSE: `{g['native_mean_mse']:.9g}`",
        f"- parity threshold: `{g['parity_threshold']:.9g}`",
        f"- native / LeWM ratio: `{g['native_to_lewm_ratio']:.9g}`",
        f"- decision: `{g['decision']}`",
        "",
        "A BEDC-native state that fails this gate is a monitor or diagnostic ledger, not a world model.",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Check the BEDC-native prediction-parity world-model gate")
    parser.add_argument("--dynamics", default=str(DEFAULT_DYNAMICS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--epsilon", type=float, default=0.10)
    args = parser.parse_args()
    dynamics_path = Path(args.dynamics)
    dynamics = load_json(dynamics_path)
    g = gate(dynamics, float(args.epsilon))
    report = {
        "status": g["decision"],
        "schema_id": "bedc_jepa.prediction_parity_gate",
        "inputs": {"dynamics": str(dynamics_path)},
        "gate": g,
        "contract": {
            "world_model_requirement": "PredLoss_BEDC <= (1 + epsilon) PredLoss_LeWM on the same target scale and evaluation transitions",
            "failure_interpretation": "if the gate fails, detection/survival/allocation rows describe a monitor or diagnostic ledger rather than a BEDC-native world model",
            "scale_guard": "rows with different prediction-loss definitions are not mixed into this gate",
        },
        "source_scope": dynamics.get("honest_scope", []),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"status": report["status"], "gate": report["gate"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

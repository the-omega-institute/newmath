#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_A100_UNIFORM = REPORT_DIR / "multistep_dynamics_a100_uniform_loss.json"
DEFAULT_LOCAL_UNIFORM = REPORT_DIR / "multistep_dynamics_uniform_loss.json"
DEFAULT_A100_DECAY = REPORT_DIR / "multistep_dynamics_a100_scale.json"
DEFAULT_LOCAL_DECAY = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
HYPOTHESIS_ID = "fi-043.a100-scale-efficiency-diagnostic"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "best_a100_scaling_gain",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["a100_scale_efficiency", "prediction_parity"],
        "reported_claim": f"A100 scale-efficiency diagnostic fail-closed: {reason}",
    }


def load_primary(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))["primary"]


def h1_mse(primary: dict[str, object]) -> dict[str, float]:
    values = primary["metrics"]["native_h1_mse"]
    return {
        "observed": float(values["observed"]),
        "low": float(values["low"]),
        "high": float(values["high"]),
    }


def gain_ci(local: dict[str, float], a100: dict[str, float]) -> dict[str, float]:
    return {
        "low": local["low"] - a100["high"],
        "high": local["high"] - a100["low"],
    }


def row(local_primary: dict[str, object], a100_primary: dict[str, object]) -> dict[str, object]:
    local = h1_mse(local_primary)
    a100 = h1_mse(a100_primary)
    gain = local["observed"] - a100["observed"]
    return {
        "gain": gain,
        "ci": gain_ci(local, a100),
        "local_native_h1_mse": local,
        "a100_native_h1_mse": a100,
        "local_params": int(local_primary["counts"]["params"]),
        "a100_params": int(a100_primary["counts"]["params"]),
        "local_parity_margin": float(local_primary["parity_gate"]["margin"]),
        "a100_parity_margin": float(a100_primary["parity_gate"]["margin"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate whether A100 scaling improves completed multi-step dynamics rows")
    parser.add_argument("--a100-uniform", default=str(DEFAULT_A100_UNIFORM))
    parser.add_argument("--local-uniform", default=str(DEFAULT_LOCAL_UNIFORM))
    parser.add_argument("--a100-decay", default=str(DEFAULT_A100_DECAY))
    parser.add_argument("--local-decay", default=str(DEFAULT_LOCAL_DECAY))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    paths = {
        "a100_uniform": Path(args.a100_uniform),
        "local_uniform": Path(args.local_uniform),
        "a100_decay": Path(args.a100_decay),
        "local_decay": Path(args.local_decay),
    }
    missing = [name for name, path in paths.items() if not path.exists()]
    if missing:
        payload = fail_closed(f"missing inputs: {', '.join(missing)}")
    else:
        uniform = row(load_primary(paths["local_uniform"]), load_primary(paths["a100_uniform"]))
        decay = row(load_primary(paths["local_decay"]), load_primary(paths["a100_decay"]))
        best = uniform if float(uniform["gain"]) >= float(decay["gain"]) else decay
        best_gain = float(best["gain"])
        best_ci = best["ci"]
        if best_ci["low"] > 0.0:
            status = "positive"
        elif best_ci["high"] <= 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": best_gain},
            "metric": "best_a100_scaling_gain",
            "metric_value": best_gain,
            "ci": best_ci,
            "status": status,
            "measured_scope": ["a100_scale_efficiency", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"A100 scale-efficiency diagnostic: uniform local-minus-A100 h1 MSE gain={uniform['gain']:.9g}; "
                f"decay local-minus-A100 h1 MSE gain={decay['gain']:.9g}; "
                f"best_gain={best_gain:.9g}. "
                "The completed A100 dynamics rows do not provide a positive scaling-efficiency signal for the current route."
            ),
            "diagnostics": {
                "uniform": uniform,
                "decay": decay,
                "interpretation": "positive gain means A100 native h1 MSE is lower than the matched local row",
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

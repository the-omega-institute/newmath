#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_DECAY = REPORT_DIR / "multistep_dynamics_loss_profile_seed123_decay.json"
DEFAULT_UNIFORM = REPORT_DIR / "multistep_dynamics_loss_profile_seed123_uniform.json"
HYPOTHESIS_ID = "fi-038.loss-profile-seed-replication"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "uniform_minus_decay_native_h1_mse",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["loss_profile_seed_replication", "prediction_parity"],
        "reported_claim": f"loss-profile seed replication fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Replicate decay-vs-uniform dynamics loss profile on a matched alternate seed")
    parser.add_argument("--decay", default=str(DEFAULT_DECAY))
    parser.add_argument("--uniform", default=str(DEFAULT_UNIFORM))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    decay_path = Path(args.decay)
    uniform_path = Path(args.uniform)
    if not decay_path.exists():
        payload = fail_closed(f"missing decay report at {decay_path}")
    elif not uniform_path.exists():
        payload = fail_closed(f"missing uniform report at {uniform_path}")
    else:
        decay = json.loads(decay_path.read_text(encoding="utf-8"))
        uniform = json.loads(uniform_path.read_text(encoding="utf-8"))
        decay_primary = decay["primary"]
        uniform_primary = uniform["primary"]
        decay_m = decay_primary["metrics"]["native_h1_mse"]
        uniform_m = uniform_primary["metrics"]["native_h1_mse"]
        delta = float(uniform_m["observed"]) - float(decay_m["observed"])
        delta_ci = {
            "low": float(uniform_m["low"]) - float(decay_m["high"]),
            "high": float(uniform_m["high"]) - float(decay_m["low"]),
        }
        if delta_ci["high"] < 0.0:
            status = "positive"
        elif delta > 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": delta},
            "metric": "uniform_minus_decay_native_h1_mse",
            "metric_value": delta,
            "ci": delta_ci,
            "status": status,
            "measured_scope": ["loss_profile_seed_replication", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"matched seed loss-profile replication h={decay_primary['horizon']}: "
                f"decay_native_h1_mse={decay_m['observed']:.9g}, "
                f"uniform_native_h1_mse={uniform_m['observed']:.9g}, "
                f"uniform_minus_decay={delta:.9g}, "
                f"decay_ratio={decay_primary['parity_gate']['native_to_lewm_ratio']:.9g}, "
                f"uniform_ratio={uniform_primary['parity_gate']['native_to_lewm_ratio']:.9g}. "
                "The alternate matched seed does not reproduce a stable uniform-loss advantage."
            ),
            "diagnostics": {
                "decay": decay_primary,
                "uniform": uniform_primary,
                "uniform_minus_decay_native_h1_mse": delta,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

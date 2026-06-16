#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_LOCAL = REPORT_DIR / "multistep_dynamics_uniform_loss.json"
DEFAULT_TRANSITION = REPORT_DIR / "multistep_dynamics_transition_upper_bound.json"
DEFAULT_LOSS_SYNTH = REPORT_DIR / "fi_039_loss_profile_synthesis_verdict.json"
DEFAULT_A100_DECAY = REPORT_DIR / "fi_037_a100_decay_loss_dynamics_verdict.json"
DEFAULT_A100_UNIFORM = REPORT_DIR / "fi_036_a100_uniform_loss_dynamics_verdict.json"
HYPOTHESIS_ID = "fi-040.prediction-parity-boundary"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "best_completed_prediction_parity_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["prediction_parity_boundary", "world_model_gate"],
        "reported_claim": f"prediction parity boundary synthesis fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Synthesize current prediction-parity boundary evidence")
    parser.add_argument("--local", default=str(DEFAULT_LOCAL))
    parser.add_argument("--transition", default=str(DEFAULT_TRANSITION))
    parser.add_argument("--loss-synthesis", default=str(DEFAULT_LOSS_SYNTH))
    parser.add_argument("--a100-decay", default=str(DEFAULT_A100_DECAY))
    parser.add_argument("--a100-uniform", default=str(DEFAULT_A100_UNIFORM))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    paths = {
        "local": Path(args.local),
        "transition": Path(args.transition),
        "loss_synthesis": Path(args.loss_synthesis),
        "a100_decay": Path(args.a100_decay),
        "a100_uniform": Path(args.a100_uniform),
    }
    missing = [name for name, path in paths.items() if not path.exists()]
    if missing:
        payload = fail_closed(f"missing inputs: {', '.join(missing)}")
    else:
        local = json.loads(paths["local"].read_text(encoding="utf-8"))["primary"]
        transition = json.loads(paths["transition"].read_text(encoding="utf-8"))["primary"]
        loss_synthesis = json.loads(paths["loss_synthesis"].read_text(encoding="utf-8"))
        a100_decay = json.loads(paths["a100_decay"].read_text(encoding="utf-8"))
        a100_uniform = json.loads(paths["a100_uniform"].read_text(encoding="utf-8"))
        local_margin = float(local["parity_gate"]["margin"])
        transition_margin = float(transition["parity_gate"]["margin"])
        transition_threshold = float(transition["parity_gate"]["threshold"])
        transition_native = transition["metrics"]["native_h1_mse"]
        transition_margin_ci = {
            "low": transition_threshold - float(transition_native["high"]),
            "high": transition_threshold - float(transition_native["low"]),
        }
        local_pass = bool(local["parity_gate"]["pass"])
        transition_pass = bool(transition["parity_gate"]["pass"])
        a100_pending = a100_decay.get("status") == "fail-closed" and a100_uniform.get("status") == "fail-closed"
        a100_decay_margin = float(a100_decay["metric_value"])
        a100_uniform_margin = float(a100_uniform["metric_value"])
        a100_clause = (
            "A100 rows remain pending rather than completed evidence."
            if a100_pending
            else (
                f"A100 rows are completed negative evidence: uniform margin={a100_uniform_margin:.9g}; "
                f"decay margin={a100_decay_margin:.9g}."
            )
        )
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": transition_margin},
            "metric": "best_completed_prediction_parity_margin",
            "metric_value": transition_margin,
            "ci": transition_margin_ci,
            "measured_scope": ["prediction_parity_boundary", "next_latent_mse", "world_model_gate"],
            "reported_claim": (
                f"prediction-parity boundary synthesis: best local episode-heldout margin={local_margin:.9g}; "
                f"transition upper-bound margin={transition_margin:.9g}; "
                f"stable_uniform_advantage={loss_synthesis['metric_value']}; "
                f"A100_pending={a100_pending}. "
                "The current local evidence bounds ordinary loss-profile and local scaling sweeps away from the LeWM parity gate; "
                f"{a100_clause}"
            ),
            "diagnostics": {
                "best_local_episode_heldout": local,
                "transition_upper_bound": transition,
                "loss_profile_synthesis": loss_synthesis,
                "a100_decay": a100_decay,
                "a100_uniform": a100_uniform,
                "a100_pending": a100_pending,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

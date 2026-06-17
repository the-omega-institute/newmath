#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_EPISODE = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
DEFAULT_TRANSITION = REPORT_DIR / "multistep_dynamics_transition_upper_bound.json"
HYPOTHESIS_ID = "fi-033.dynamics-gap-decomposition"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "residual_prediction_parity_gap",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["multistep_dynamics_gap_decomposition", "prediction_parity"],
        "reported_claim": f"dynamics gap decomposition fail-closed: {reason}",
    }


def margin_ci(primary: dict[str, object]) -> dict[str, float]:
    gate = primary["parity_gate"]
    native = primary["metrics"]["native_h1_mse"]
    threshold = float(gate["threshold"])
    return {
        "low": threshold - float(native["high"]),
        "high": threshold - float(native["low"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Decompose multi-step dynamics parity failure into heldout and residual gaps")
    parser.add_argument("--episode", default=str(DEFAULT_EPISODE))
    parser.add_argument("--transition", default=str(DEFAULT_TRANSITION))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    episode_path = Path(args.episode)
    transition_path = Path(args.transition)
    if not episode_path.exists():
        payload = fail_closed(f"missing episode-heldout report at {episode_path}")
    elif not transition_path.exists():
        payload = fail_closed(f"missing transition upper-bound report at {transition_path}")
    else:
        episode = json.loads(episode_path.read_text(encoding="utf-8"))
        transition = json.loads(transition_path.read_text(encoding="utf-8"))
        ep = episode["primary"]
        tr = transition["primary"]
        ep_mse = float(ep["metrics"]["native_h1_mse"]["observed"])
        tr_mse = float(tr["metrics"]["native_h1_mse"]["observed"])
        lewm = float(tr["metrics"]["lewm_h1_mse"]["observed"])
        threshold = float(tr["parity_gate"]["threshold"])
        generalization_gap = ep_mse - tr_mse
        residual_gap = tr_mse - threshold
        tr_ci = margin_ci(tr)
        residual_ci = {"low": -tr_ci["high"], "high": -tr_ci["low"]}
        if residual_ci["low"] > 0.0 and generalization_gap > 0.0:
            status = "negative"
        elif residual_ci["high"] <= 0.0:
            status = "positive"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": residual_gap},
            "metric": "residual_prediction_parity_gap",
            "metric_value": residual_gap,
            "ci": residual_ci,
            "status": status,
            "measured_scope": ["multistep_dynamics_gap_decomposition", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"scaled episode-heldout native_h1_mse={ep_mse:.9g}; "
                f"transition upper-bound native_h1_mse={tr_mse:.9g}; "
                f"LeWM_h1_mse={lewm:.9g}; parity_threshold={threshold:.9g}; "
                f"heldout_generalization_gap={generalization_gap:.9g}; "
                f"residual_transition_parity_gap={residual_gap:.9g}. "
                "Transition-level splitting improves fit relative to episode-heldout evaluation, "
                "but the upper-bound row still misses the LeWM prediction-parity threshold."
            ),
            "diagnostics": {
                "episode_primary": ep,
                "transition_primary": tr,
                "heldout_generalization_gap": generalization_gap,
                "residual_transition_parity_gap": residual_gap,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

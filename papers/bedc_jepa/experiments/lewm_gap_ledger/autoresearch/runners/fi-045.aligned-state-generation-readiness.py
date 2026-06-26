#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_COMPUTE = REPORT_DIR / "compute_value_structured_assignment_predictions.npz"
DEFAULT_DYNAMICS = REPORT_DIR / "multistep_dynamics_uniform_loss_predictions.npz"
HYPOTHESIS_ID = "fi-045.aligned-state-generation-readiness"


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "aligned_state_generation_ready",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["aligned_state_generation_readiness", "world_model_gate"],
        "reported_claim": f"aligned state-generation readiness fail-closed: {reason}",
    }


def ridge_fit(x: np.ndarray, y: np.ndarray, lam: float = 1e-6) -> np.ndarray:
    eye = np.eye(x.shape[1], dtype=np.float64)
    eye[0, 0] = 0.0
    return np.linalg.solve(x.T @ x + lam * eye, x.T @ y)


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit whether existing compute-value and dynamics artifacts form an aligned state-generation training export")
    parser.add_argument("--compute", default=str(DEFAULT_COMPUTE))
    parser.add_argument("--dynamics", default=str(DEFAULT_DYNAMICS))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    compute_path = Path(args.compute)
    dynamics_path = Path(args.dynamics)
    if not compute_path.exists():
        payload = fail_closed(f"missing compute-value predictions at {compute_path}")
    elif not dynamics_path.exists():
        payload = fail_closed(f"missing dynamics predictions at {dynamics_path}")
    else:
        compute = np.load(compute_path, allow_pickle=False)
        dynamics = np.load(dynamics_path, allow_pickle=False)
        compute_keys = [tuple(item) for item in compute["anchor_ep_t0"]]
        dynamics_keys = list(zip(dynamics["h5_episode"].tolist(), dynamics["h5_t"].tolist()))
        overlap = sorted(set(compute_keys) & set(dynamics_keys))
        idx_compute = {key: idx for idx, key in enumerate(compute_keys)}
        idx_dynamics = {key: idx for idx, key in enumerate(dynamics_keys)}
        episodes = sorted({int(ep) for ep, _ in overlap})
        if len(overlap) < 200 or len(episodes) < 12:
            reason = f"overlap anchors={len(overlap)} episodes={len(episodes)} below aligned-export threshold"
            payload = fail_closed(reason)
            payload["diagnostics"] = {
                "overlap_anchors": len(overlap),
                "overlap_episodes": len(episodes),
                "required_anchors": 200,
                "required_episodes": 12,
            }
        else:
            rows_base: list[list[float]] = []
            rows_full: list[list[float]] = []
            targets: list[float] = []
            row_episodes: list[int] = []
            scores = compute["predicted_option_score"]
            for key in overlap:
                ci = idx_compute[key]
                di = idx_dynamics[key]
                episode = int(key[0])
                t0 = float(compute["t0"][ci])
                score = scores[ci].astype(np.float64)
                rows_base.append([1.0, t0])
                rows_full.append([1.0, t0, float(score.min()), float(score.mean()), float(score.std()), float(compute["chosen_depth"][ci])])
                targets.append(float(dynamics["h5_native_h1_mse"][di]))
                row_episodes.append(episode)
            x_base = np.asarray(rows_base, dtype=np.float64)
            x_full = np.asarray(rows_full, dtype=np.float64)
            y = np.asarray(targets, dtype=np.float64)
            row_episodes_arr = np.asarray(row_episodes)
            base_pred = np.zeros_like(y)
            full_pred = np.zeros_like(y)
            for heldout in episodes:
                test = row_episodes_arr == heldout
                train = ~test
                base_coef = ridge_fit(x_base[train], y[train])
                full_coef = ridge_fit(x_full[train], y[train])
                base_pred[test] = x_base[test] @ base_coef
                full_pred[test] = x_full[test] @ full_coef
            base_mse = float(np.mean((y - base_pred) ** 2))
            full_mse = float(np.mean((y - full_pred) ** 2))
            survival = base_mse - full_mse
            status = "positive" if survival > 0.0 else "negative"
            payload = {
                "hypothesis_id": HYPOTHESIS_ID,
                "anchor": {"field": "anchor.metric", "value": survival},
                "metric": "aligned_state_generation_ready",
                "metric_value": survival,
                "ci": {"low": survival, "high": survival},
                "status": status,
                "measured_scope": [
                    "aligned_state_generation_readiness",
                    "compute_value_survival",
                    "prediction_parity_boundary",
                    "world_model_gate",
                ],
                "reported_claim": (
                    f"aligned state-generation readiness: overlap anchors={len(overlap)}, episodes={len(episodes)}, "
                    f"episode-heldout dynamics-error survival={survival:.9g}. "
                    "This is only a readiness audit for aligned exports, not a trained BEDC-native world model."
                ),
                "diagnostics": {
                    "overlap_anchors": len(overlap),
                    "overlap_episodes": len(episodes),
                    "base_mse": base_mse,
                    "full_mse": full_mse,
                    "not_claimed": [
                        "prediction parity",
                        "state-generation model training",
                        "universal control",
                    ],
                },
            }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

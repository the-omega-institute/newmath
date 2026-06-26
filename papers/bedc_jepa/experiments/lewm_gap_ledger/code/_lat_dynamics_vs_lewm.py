"""Prediction-quality comparison: the native LAT's dynamics head vs the
LeWM predictor itself, on the same eval transitions and the same metric.

Both models predict the next latent. LeWM's per-transition rollout error is
recomputed here from the exported `pred` and `emb` arrays (and asserted to
match the export's `prediction_mse`), so the metric is identical by
construction: mean squared error over the 192 latent dimensions, raw space.

Honest scope: the LAT was trained on the train split of this one export
(~3k transitions); LeWM's predictor was trained by its authors at full scale.
This is a like-for-like *evaluation*, not a like-for-like training budget.
"""

from __future__ import annotations

import json

import numpy as np
import torch

from _phase1c_gap_ledger import auroc_rank
from _lat_lewm_port import (
    DYNAMICS_WEIGHT,
    NPZ_PATH,
    PYTHON_SEED,
    REPORT_DIR,
    build_windows,
    split_episodes,
    train_arm,
)

JSON_PATH = REPORT_DIR / "lewm_lat_dynamics_comparison.json"
PORT_JSON = REPORT_DIR / "lewm_ledger_aware_transformer.json"
BOOTSTRAPS = 500
BOOTSTRAP_SEED = 314159


def main() -> None:
    np.random.seed(PYTHON_SEED)
    data = dict(np.load(NPZ_PATH))
    win_rows = build_windows(data)
    splits = split_episodes(data["emb"].shape[0])
    train_mask = np.isin(win_rows["episode"], splits["train"])
    eval_mask = np.isin(win_rows["episode"], splits["eval"])
    tau = float(np.percentile(win_rows["mse"][train_mask], 75))
    y = (win_rows["mse"] > tau).astype(np.int8)

    # LeWM per-transition next-latent error, recomputed to pin the metric.
    tm = data["transition_mask"].astype(bool)
    ep_idx, t_idx = np.where(tm)
    lewm_pred = data["pred"][ep_idx, t_idx].astype(np.float64)
    target = data["emb"][ep_idx, t_idx + 1].astype(np.float64)
    lewm_mse_recomputed = np.mean((lewm_pred - target) ** 2, axis=1)
    exported = data["prediction_mse"][ep_idx, t_idx].astype(np.float64)
    assert np.max(np.abs(lewm_mse_recomputed - exported)) < 1e-5, "metric definition mismatch"

    # Align with the (finite-filtered) window rows by (episode, t).
    key_to_pos = {(int(e), int(t)): i for i, (e, t) in enumerate(zip(ep_idx, t_idx))}
    row_pos = np.array([key_to_pos[(int(e), int(t))] for e, t in zip(win_rows["episode"], win_rows["t"])])
    lewm_mse = lewm_mse_recomputed[row_pos]

    scores, _, model, (emb_mean, emb_std) = train_arm(
        win_rows, train_mask, y, seed=PYTHON_SEED, dynamics_weight=DYNAMICS_WEIGHT,
        label_permutation_seed=None, return_artifacts=True,
    )
    port = json.loads(PORT_JSON.read_text(encoding="utf-8"))
    committed = port["arms"]["lat_learned"]["metrics_eval_episode_bootstrap"]["failure_detection_auroc"]["observed"]
    got = auroc_rank(y[eval_mask], scores[eval_mask])
    assert abs(got - committed) < 1e-9, "clean anchor mismatch"

    # LAT dynamics-head next-latent prediction in raw space, eval split.
    idx = np.where(eval_mask)[0]
    lat_mse = np.empty(len(idx), dtype=np.float64)
    model.eval()
    with torch.no_grad():
        for start in range(0, len(idx), 1024):
            sl = idx[start : start + 1024]
            normed = ((win_rows["win_emb"][sl] - emb_mean) / emb_std).astype(np.float32)
            _, dyn = model(torch.from_numpy(normed), torch.from_numpy(win_rows["win_act"][sl]))
            pred_raw = dyn.numpy().astype(np.float64) * emb_std + emb_mean
            lat_mse[start : start + len(sl)] = np.mean(
                (pred_raw - win_rows["next_emb"][sl].astype(np.float64)) ** 2, axis=1
            )

    lewm_eval = lewm_mse[eval_mask]
    episodes = win_rows["episode"][eval_mask]
    diff = lat_mse - lewm_eval
    win = (lat_mse < lewm_eval).astype(np.float64)

    rng = np.random.default_rng(BOOTSTRAP_SEED)
    unique_ep = np.unique(episodes)
    by_ep = [np.where(episodes == e)[0] for e in unique_ep]
    boots = {"mean_diff": [], "win_rate": [], "lat_mean": [], "lewm_mean": []}
    for _ in range(BOOTSTRAPS):
        sample = rng.integers(0, len(by_ep), size=len(by_ep))
        ii = np.concatenate([by_ep[i] for i in sample])
        boots["mean_diff"].append(float(np.mean(diff[ii])))
        boots["win_rate"].append(float(np.mean(win[ii])))
        boots["lat_mean"].append(float(np.mean(lat_mse[ii])))
        boots["lewm_mean"].append(float(np.mean(lewm_eval[ii])))

    def ci(key: str) -> dict[str, float]:
        arr = np.asarray(boots[key])
        return {"ci95_low": float(np.percentile(arr, 2.5)), "ci95_high": float(np.percentile(arr, 97.5))}

    report = {
        "schema_id": "lewm.lat_dynamics_vs_lewm_predictor",
        "metric": "per-transition next-latent MSE over 192 dims, raw space, identical for both models (LeWM side recomputed from exported pred/emb and asserted against prediction_mse)",
        "eval_transitions": int(len(idx)),
        "lewm_predictor": {
            "mean_mse": float(np.mean(lewm_eval)),
            "median_mse": float(np.median(lewm_eval)),
            "mean_ci": ci("lewm_mean"),
        },
        "lat_dynamics_head": {
            "mean_mse": float(np.mean(lat_mse)),
            "median_mse": float(np.median(lat_mse)),
            "mean_ci": ci("lat_mean"),
        },
        "lat_minus_lewm_mean_diff": {"observed": float(np.mean(diff)), **ci("mean_diff")},
        "lat_win_rate_per_transition": {"observed": float(np.mean(win)), **ci("win_rate")},
        "honest_scope": [
            "LAT trained on ~3k transitions of this single export; LeWM predictor trained at full scale by its authors",
            "single checkpoint, single export, episode bootstrap",
            "next-step latent prediction only; no rollout-horizon or control comparison",
        ],
    }
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({k: report[k] for k in ("lewm_predictor", "lat_dynamics_head", "lat_minus_lewm_mean_diff", "lat_win_rate_per_transition")}, indent=2))


if __name__ == "__main__":
    main()

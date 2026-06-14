#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
import math
import os
import random
import sys
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LATENTS = ROOT / "tworooms_latent_large.npz"
DEFAULT_SCORE_DUMP = REPORT_DIR / "g2n_integrated_a100_scores.npz"
DEFAULT_OUT = REPORT_DIR / "g2n_integrated_a100_strongest_paired.json"
PHASE1C_PATH = ROOT / "_phase1c_gap_ledger.py"

SPLIT_SEED = 1701
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
PRIMARY_H = 1
PRIMARY_Q = 75
EXPECTED_PHASE1C_CAMPAIGN_AUROC = 0.7313653225855256
PHASE1C_ANCHOR_TOL = 1.0e-9


def load_phase1c() -> Any:
    spec = importlib.util.spec_from_file_location("_phase1c_gap_ledger", PHASE1C_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load Phase1c helper: {PHASE1C_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[str(spec.name)] = module
    spec.loader.exec_module(module)
    return module


phase1c = load_phase1c()


def configure(seed: int) -> None:
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    np.random.seed(seed)


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite JSON float: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, np.integer):
        return int(value)
    if isinstance(value, np.floating):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def pair_to_row_index(rows: dict[str, np.ndarray]) -> dict[tuple[int, int], int]:
    return {(int(ep), int(t)): i for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"]))}


def fit_phase1c_campaign_scores(data: dict[str, np.ndarray], rows: dict[str, np.ndarray]) -> dict[str, Any]:
    splits_ep = phase1c.split_episodes(data["emb"].shape[0])
    split_masks = {name: np.isin(rows["episode"], eps) for name, eps in splits_ep.items()}
    train_mask = split_masks["train"]
    eval_mask = split_masks["eval"]

    near_threshold = float(np.median(rows["distance_to_target"][train_mask]))
    y_dist = phase1c.distinction_truth(rows, near_threshold, prefix="")
    probe_prob_cols: list[np.ndarray] = []
    probe_logit_cols: list[np.ndarray] = []
    probe_pred_cols: list[np.ndarray] = []
    for j, _name in enumerate(phase1c.DISTINCTIONS):
        head, _info = phase1c.fit_logistic_head(
            rows["emb"][train_mask],
            y_dist[train_mask, j],
            steps=700,
            lr=0.18,
            l2=1.0e-4,
        )
        p_all, logit_all = phase1c.predict_logistic_head(head, rows["emb"])
        probe_prob_cols.append(p_all)
        probe_logit_cols.append(logit_all)
        probe_pred_cols.append((p_all >= 0.5).astype(np.float64))

    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)
    quality_feature, _quality_report = phase1c.fit_linear_r2_quality(
        rows["emb"][train_mask],
        rows["observation"][train_mask],
        rows["emb"][eval_mask],
        rows["observation"][eval_mask],
    )
    x_b, _ = phase1c.build_gap_features(
        rows["emb"],
        probe_prob,
        probe_logit,
        probe_pred,
        quality_feature,
        phase1c.FEATURE_VARIANTS["B_denoised_agent_room_only"],
    )

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    y_prediction_error = (rows["mse"] > tau_err).astype(np.int8)
    head, fit_info = phase1c.fit_logistic_head(
        x_b[train_mask],
        y_prediction_error[train_mask],
        steps=500,
        lr=0.14,
        l2=1.0e-4,
    )
    score_all, _ = phase1c.predict_logistic_head(head, x_b)
    campaign_eval_auroc = float(phase1c.auroc_rank(y_prediction_error[eval_mask], score_all[eval_mask]))
    return {
        "score_all": score_all.astype(np.float64),
        "y_all": y_prediction_error.astype(np.int8),
        "fit": fit_info,
        "tau_err": tau_err,
        "campaign_eval_auroc": campaign_eval_auroc,
    }


def metric_stat(observed: float, samples: np.ndarray) -> dict[str, float]:
    arr = np.asarray(samples, dtype=np.float64)
    return {
        "observed": float(observed),
        "low": float(np.percentile(arr, 2.5)),
        "high": float(np.percentile(arr, 97.5)),
    }


def paired_episode_bootstrap(
    y: np.ndarray,
    native_score: np.ndarray,
    posthoc_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
) -> dict[str, Any]:
    y = y.astype(np.int8)
    native_score = native_score.astype(np.float64)
    posthoc_score = posthoc_score.astype(np.float64)
    episode = episode.astype(np.int64)
    if not (len(y) == len(native_score) == len(posthoc_score) == len(episode)):
        raise RuntimeError("paired arrays have inconsistent lengths")
    if np.unique(y).size < 2:
        raise RuntimeError("paired truth is single-class")

    native_obs = float(phase1c.auroc_rank(y, native_score))
    posthoc_obs = float(phase1c.auroc_rank(y, posthoc_score))
    by_ep = [np.where(episode == ep)[0] for ep in np.unique(episode)]
    rng = np.random.default_rng(seed)
    delta_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    native_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    posthoc_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        picked = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in picked])
        if np.unique(y[idx]).size < 2:
            delta_samples[i] = 0.0
            native_samples[i] = 0.5
            posthoc_samples[i] = 0.5
            continue
        n_auc = float(phase1c.auroc_rank(y[idx], native_score[idx]))
        p_auc = float(phase1c.auroc_rank(y[idx], posthoc_score[idx]))
        native_samples[i] = n_auc
        posthoc_samples[i] = p_auc
        delta_samples[i] = n_auc - p_auc
    return {
        "delta": metric_stat(native_obs - posthoc_obs, delta_samples),
        "native": metric_stat(native_obs, native_samples),
        "strongest_posthoc": metric_stat(posthoc_obs, posthoc_samples),
        "eval_rows": int(len(y)),
        "eval_episodes": int(len(np.unique(episode))),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


def fail_payload(reason: str) -> dict[str, Any]:
    return {
        "status": "fail-closed",
        "metric": "native_minus_strongest_posthoc_auroc",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "reported_claim": f"fail-closed: {reason}; no direct strongest-probe superiority claim is admitted.",
    }


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    configure(int(args.seed))
    latent_path = Path(args.latents)
    score_path = Path(args.score_dump)
    if not latent_path.exists():
        return fail_payload(f"missing latent input: {latent_path}")
    if not score_path.exists():
        return fail_payload(f"missing G2N score dump: {score_path}")

    data = load_npz(latent_path)
    dump = load_npz(score_path)
    rows = phase1c.flatten_transition_rows(data)
    pair_row = pair_to_row_index(rows)
    posthoc = fit_phase1c_campaign_scores(data, rows)
    campaign_anchor_delta = abs(float(posthoc["campaign_eval_auroc"]) - EXPECTED_PHASE1C_CAMPAIGN_AUROC)
    if campaign_anchor_delta > PHASE1C_ANCHOR_TOL:
        return fail_payload(
            "Phase1c campaign logistic gap head anchor mismatch: "
            f"observed={float(posthoc['campaign_eval_auroc']):.17g}, "
            f"expected={EXPECTED_PHASE1C_CAMPAIGN_AUROC:.17g}"
        )

    target_horizons = [int(x) for x in dump["target_horizons"].reshape(-1)]
    quantiles = [int(x) for x in dump["quantiles"].reshape(-1)]
    h_pos = target_horizons.index(PRIMARY_H)
    q_pos = quantiles.index(PRIMARY_Q)
    valid = dump["eval_valid_target"][:, h_pos].astype(bool)
    y = dump["eval_y_target"][valid, h_pos, q_pos].astype(np.int8)
    anchors = dump["eval_anchor_ep_t0"][valid].astype(np.int64)
    native_score = dump["eval_horizon_logits"][valid, h_pos, q_pos].astype(np.float64)
    row_idx = np.asarray([pair_row[(int(ep), int(t))] for ep, t in anchors], dtype=np.int64)
    posthoc_score = posthoc["score_all"][row_idx].astype(np.float64)
    posthoc_y = posthoc["y_all"][row_idx].astype(np.int8)
    if not np.array_equal(y, posthoc_y):
        return fail_payload("eval_h1 anchor alignment failed between G2N dump and Phase1c rows")

    paired = paired_episode_bootstrap(
        y,
        native_score,
        posthoc_score,
        anchors[:, 0].astype(np.int64),
        seed=int(args.seed) + BOOTSTRAP_SEED_OFFSET,
    )
    delta = paired["delta"]
    if float(delta["low"]) > 0.0:
        conclusion = "positive: CI low>0 for the direct paired strongest-probe comparison"
        status = "positive"
    elif float(delta["high"]) < 0.0:
        conclusion = "negative: CI high<0 for the direct paired strongest-probe comparison"
        status = "negative"
    else:
        conclusion = "unidentifiable: CI crosses 0 for the direct paired strongest-probe comparison"
        status = "fail-closed"
    claim = (
        f"G2N h1 native AUROC={paired['native']['observed']:.9g}; "
        f"strongest post-hoc AUROC={paired['strongest_posthoc']['observed']:.9g}; "
        f"delta={delta['observed']:.9g}, 95% CI=[{delta['low']:.9g},{delta['high']:.9g}]; "
        f"paired rows={paired['eval_rows']}, episodes={paired['eval_episodes']}; "
        f"Phase1c campaign anchor={float(posthoc['campaign_eval_auroc']):.9g}; {conclusion}."
    )
    return {
        "status": status,
        "metric": "native_minus_strongest_posthoc_auroc",
        "metric_value": float(delta["observed"]),
        "ci": {"low": float(delta["low"]), "high": float(delta["high"])},
        "paired": paired,
        "reported_claim": claim,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--score-dump", default=str(DEFAULT_SCORE_DUMP))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    payload = clean_json(build_payload(args))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

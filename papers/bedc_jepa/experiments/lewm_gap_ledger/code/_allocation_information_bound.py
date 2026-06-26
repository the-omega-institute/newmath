from __future__ import annotations

import json
import math
import os
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch
torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
import torch.nn as nn
from sklearn.ensemble import ExtraTreesClassifier, ExtraTreesRegressor, RandomForestClassifier, RandomForestRegressor
from sklearn.ensemble import HistGradientBoostingClassifier, HistGradientBoostingRegressor
from sklearn.linear_model import ElasticNet, LogisticRegression, Ridge
from sklearn.metrics import log_loss
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler

import _g2n_native_ledger as g2n
from _allocation_bridge import (
    ANCHOR_TOL,
    BOOTSTRAPS,
    BOOTSTRAP_SEED,
    CLEAN_LABELS,
    E_H1_AUROC_TARGET,
    PYTHON_SEED,
    SPLIT_SEED,
    TARGET_H,
    TARGET_H_INDEX,
    TORCH_SEED,
    budget_eval_for_score,
    pairwise_logistic_loss,
    rank_average,
    spearman_one,
    tensorize_examples,
    within_episode_spearman,
)
from _allocation_bridge import ScalarLedgerTransformer
from _lat_lewm_port import NPZ_PATH, REPORT_DIR
from _ledger_gated_rollout import HIGH_H, LOW_H, MID_H, UNIFORM_H, allocation_uniform, summarize_allocation
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
JSON_PATH = REPORT_DIR / "lewm_allocation_information_bound.json"
MD_PATH = REPORT_DIR / "lewm_allocation_information_bound.md"

REQUIRED = (
    REPORT_DIR / "g2n_labels_clean.npz",
    REPORT_DIR / "lewm_allocation_bridge.json",
    REPORT_DIR / "lewm_allocation_rho_threshold.json",
    REPORT_DIR / "lewm_allocation_rho_robust.json",
    REPORT_DIR / "lewm_alloc_tail_target.json",
    REPORT_DIR / "lewm_alloc_rich_input.json",
    ROOT / "_allocation_bridge.py",
    ROOT / "_allocation_rho_threshold.py",
)

ORACLE_DELTA_ANCHOR = -0.015867561326231905
ORACLE_RHO_MIN = 0.999999
PERMUTATION_RHO_ABS_MAX = 0.15
K_FOLDS = 5
RHO_NOISE_SEEDS = 150
BLEND_GRID = np.round(np.arange(0.0, 1.0000001, 0.02), 2)
STEP1_NOISE_SEED_BASE = 2026061300
MI_SIM_SEED = 271828


def require_inputs() -> None:
    missing = [p for p in REQUIRED if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def finite_json(v: Any) -> Any:
    return clean_json(v)


def fit_norm(x: np.ndarray) -> dict[str, np.ndarray]:
    mean = x.mean(axis=0).astype(np.float32)
    std = x.std(axis=0).astype(np.float32)
    std[std < 1e-6] = 1.0
    return {"mean": mean, "std": std}


def apply_norm(x: np.ndarray, norm: dict[str, np.ndarray]) -> np.ndarray:
    return ((x - norm["mean"]) / norm["std"]).astype(np.float32)


def sigmoid_np(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def rank_z_within_episode(values: np.ndarray, anchors_by_ep: dict[int, list[int]]) -> np.ndarray:
    out = np.zeros(len(values), dtype=np.float64)
    for idxs in anchors_by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        r = rank_average(values[idx].astype(np.float64))
        out[idx] = (r - r.mean()) / (r.std() + 1e-12) if len(r) > 1 else 0.0
    return out


def precompute_truth_ranks(y: np.ndarray, anchors_by_ep: dict[int, list[int]]) -> dict[int, tuple[np.ndarray, np.ndarray]]:
    out: dict[int, tuple[np.ndarray, np.ndarray]] = {}
    for ep, idxs in anchors_by_ep.items():
        idx = np.asarray(idxs, dtype=np.int64)
        yr = rank_average(y[idx].astype(np.float64))
        out[int(ep)] = (idx, yr)
    return out


def fast_episode_spearman_mean(score: np.ndarray, truth_ranks: dict[int, tuple[np.ndarray, np.ndarray]]) -> float:
    vals = []
    for idx, yr in truth_ranks.values():
        sr = rank_average(score[idx].astype(np.float64))
        if len(sr) < 2 or float(np.std(sr)) == 0.0 or float(np.std(yr)) == 0.0:
            continue
        vals.append(float(np.corrcoef(sr, yr)[0, 1]))
    return float(np.mean(vals)) if vals else float("nan")


def anchors_from_eval(
    clean_eval_ex: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
) -> tuple[list[dict[str, Any]], dict[int, list[int]], np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    valid_h5 = clean["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    errors_h5 = clean["eval_err_at_h"][valid_h5, :TARGET_H].astype(np.float64)
    true_mean_h5 = clean["eval_mean_err_to_h"][valid_h5, TARGET_H_INDEX].astype(np.float64)
    anchors_arr = clean_eval_ex["anchor_ep_t0"][valid_h5]
    anchors = [
        {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
        for i, (ep, t) in enumerate(anchors_arr)
    ]
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    uniform_h = allocation_uniform(anchors_by_ep)
    uniform_alloc = summarize_allocation("uniform", uniform_h, errors_h5, anchors)
    return anchors, anchors_by_ep, errors_h5, true_mean_h5, valid_h5, uniform_alloc


def episode_spearman_bootstrap(
    score: np.ndarray,
    truth: np.ndarray,
    anchors: list[dict[str, Any]],
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, Any]:
    by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        by_ep[int(anchor["episode"])].append(i)
    eps = sorted(by_ep)
    ep_rho = []
    ep_n = []
    for ep in eps:
        idx = np.asarray(by_ep[ep], dtype=np.int64)
        rho = spearman_one(score[idx], truth[idx])
        if np.isfinite(rho):
            ep_rho.append(float(rho))
            ep_n.append(int(len(idx)))
    ep_rho_arr = np.asarray(ep_rho, dtype=np.float64)
    ep_n_arr = np.asarray(ep_n, dtype=np.float64)
    observed = float(np.mean(ep_rho_arr)) if len(ep_rho_arr) else float("nan")
    weighted = float(np.sum(ep_rho_arr * ep_n_arr) / np.sum(ep_n_arr)) if len(ep_rho_arr) else float("nan")
    rng = np.random.default_rng(seed)
    samples = np.zeros(n_boot, dtype=np.float64)
    for b in range(n_boot):
        pick = rng.integers(0, len(ep_rho_arr), size=len(ep_rho_arr))
        samples[b] = float(np.mean(ep_rho_arr[pick]))
    return {
        "observed": observed,
        "bootstrap_mean": float(np.mean(samples)),
        "ci95_low": float(np.percentile(samples, 2.5)),
        "ci95_high": float(np.percentile(samples, 97.5)),
        "anchor_weighted_mean": weighted,
        "episodes_used": int(len(ep_rho_arr)),
        "episodes_total": int(len(eps)),
        "seed": seed,
        "resamples": n_boot,
        "definition": "within-episode Spearman(score, true mean_err_to_5), episode-mean with episode bootstrap",
    }


def episode_metric_bootstrap(
    per_episode_values: dict[int, float],
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, float]:
    eps = sorted(per_episode_values)
    values = np.asarray([per_episode_values[ep] for ep in eps], dtype=np.float64)
    obs = float(np.mean(values))
    rng = np.random.default_rng(seed)
    samples = np.zeros(n_boot, dtype=np.float64)
    for b in range(n_boot):
        pick = rng.integers(0, len(values), size=len(values))
        samples[b] = float(np.mean(values[pick]))
    return {
        "observed": obs,
        "bootstrap_mean": float(np.mean(samples)),
        "ci95_low": float(np.percentile(samples, 2.5)),
        "ci95_high": float(np.percentile(samples, 97.5)),
        "seed": seed,
        "resamples": n_boot,
    }


def make_fast_allocation_context(
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    errors_h5: np.ndarray,
) -> dict[str, Any]:
    eps = sorted(anchors_by_ep)
    ep_pos = {ep: i for i, ep in enumerate(eps)}
    cum = np.cumsum(errors_h5.astype(np.float64), axis=1)
    anchor_error_by_h = {
        1: cum[:, 0],
        3: cum[:, 2],
        5: cum[:, 4],
    }
    uniform_ep_error = np.zeros(len(eps), dtype=np.float64)
    uniform_ep_steps = np.zeros(len(eps), dtype=np.float64)
    t0 = np.asarray([int(a["t0"]) for a in anchors], dtype=np.int64)
    row_idx = np.asarray([int(a["row_idx"]) for a in anchors], dtype=np.int64)
    for ep, idxs in anchors_by_ep.items():
        pos = ep_pos[ep]
        idx = np.asarray(idxs, dtype=np.int64)
        uniform_ep_error[pos] = float(anchor_error_by_h[UNIFORM_H][idx].sum())
        uniform_ep_steps[pos] = float(UNIFORM_H * len(idx))
    rng = np.random.default_rng(BOOTSTRAP_SEED)
    boot_idx = rng.integers(0, len(eps), size=(BOOTSTRAPS, len(eps)))
    return {
        "eps": eps,
        "ep_pos": ep_pos,
        "anchors_by_ep": anchors_by_ep,
        "anchor_error_by_h": anchor_error_by_h,
        "uniform_ep_error": uniform_ep_error,
        "uniform_ep_steps": uniform_ep_steps,
        "t0": t0,
        "row_idx": row_idx,
        "boot_idx": boot_idx,
    }


def fast_delta_for_score(score: np.ndarray, ctx: dict[str, Any]) -> dict[str, float]:
    eps = ctx["eps"]
    ledger_ep_error = np.zeros(len(eps), dtype=np.float64)
    ledger_ep_steps = np.zeros(len(eps), dtype=np.float64)
    h_values = np.zeros(len(score), dtype=np.int64)
    for ep, idxs in ctx["anchors_by_ep"].items():
        idx = np.asarray(idxs, dtype=np.int64)
        order_local = np.lexsort((ctx["row_idx"][idx], ctx["t0"][idx], score[idx]))
        ordered = idx[order_local]
        n = len(ordered)
        half = n // 2
        low = ordered[:half]
        high = ordered[n - half :]
        h_values[low] = LOW_H
        h_values[high] = HIGH_H
        if n % 2:
            h_values[ordered[half]] = MID_H
        pos = ctx["ep_pos"][ep]
        ledger_ep_error[pos] = (
            ctx["anchor_error_by_h"][LOW_H][low].sum()
            + ctx["anchor_error_by_h"][HIGH_H][high].sum()
            + (ctx["anchor_error_by_h"][MID_H][ordered[half]] if n % 2 else 0.0)
        )
        ledger_ep_steps[pos] = float(UNIFORM_H * n)
    uniform_ep_error = ctx["uniform_ep_error"]
    uniform_ep_steps = ctx["uniform_ep_steps"]
    observed = float(ledger_ep_error.sum() / ledger_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum())
    bi = ctx["boot_idx"]
    samples = ledger_ep_error[bi].sum(axis=1) / ledger_ep_steps[bi].sum(axis=1) - uniform_ep_error[bi].sum(axis=1) / uniform_ep_steps[bi].sum(axis=1)
    diff_ep = ledger_ep_error - uniform_ep_error
    return {
        "observed": observed,
        "episode_total_error_difference_mean": float(diff_ep.mean()),
        "bootstrap_mean": float(np.mean(samples)),
        "ci95_low": float(np.percentile(samples, 2.5)),
        "ci95_high": float(np.percentile(samples, 97.5)),
        "seed": BOOTSTRAP_SEED,
        "resamples": BOOTSTRAPS,
    }


def basic_feature_blocks(ex: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    n = len(ex["episode"])
    past = np.concatenate([ex["past_z"].reshape(n, -1), ex["past_a"].reshape(n, -1)], axis=1).astype(np.float32)
    pred = ex["future_z"].reshape(n, -1).astype(np.float32)
    future_delta = ex["future_delta"].reshape(n, -1).astype(np.float32)
    future_avail = ex["future_avail"].astype(np.float32)
    drift = np.linalg.norm(ex["future_delta"], axis=2).astype(np.float32)
    past_state = np.concatenate(
        [
            ex["past_z"][:, -1, :].astype(np.float32),
            (ex["past_z"][:, -1, :] - ex["past_z"][:, 0, :]).astype(np.float32),
            ex["past_a"][:, -1, :].astype(np.float32),
        ],
        axis=1,
    )
    state_proxy = np.concatenate(
        [
            ex["t_scalar"][:, None].astype(np.float32),
            np.linalg.norm(ex["past_z"][:, -1, :], axis=1, keepdims=True).astype(np.float32),
            np.linalg.norm(ex["past_z"][:, -1, :] - ex["past_z"][:, 0, :], axis=1, keepdims=True).astype(np.float32),
            np.linalg.norm(ex["past_a"][:, -1, :], axis=1, keepdims=True).astype(np.float32),
            drift.mean(axis=1, keepdims=True).astype(np.float32),
            drift.max(axis=1, keepdims=True).astype(np.float32),
        ],
        axis=1,
    )
    return {
        "past_emb_action_window": past,
        "pred_z": pred,
        "future_delta": future_delta,
        "future_avail": future_avail,
        "future_drift_norms": drift,
        "last_state_proxy": past_state,
        "episode_time_state_proxy": state_proxy,
    }


def compose_raw_feature(blocks: dict[str, np.ndarray]) -> np.ndarray:
    keys = (
        "past_emb_action_window",
        "pred_z",
        "future_delta",
        "future_avail",
        "future_drift_norms",
        "last_state_proxy",
        "episode_time_state_proxy",
    )
    return np.concatenate([blocks[k] for k in keys], axis=1).astype(np.float32)


def predict_native_logits() -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    print("[anchor] train frozen G2N E logits", flush=True)
    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    clean = np.load(CLEAN_LABELS)
    train_ex = g2n.build_clean_examples(data, clean, "train", None)
    eval_ex = g2n.build_clean_examples(data, clean, "eval", None)
    model, info, norm = g2n.train_arm(
        "E",
        train_ex,
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    train_logits = g2n.predict_logits(model, train_ex, norm)
    eval_logits = g2n.predict_logits(model, eval_ex, norm)
    e_eval = g2n.evaluate_clean(eval_logits, eval_ex)
    e_h1 = float(e_eval["h1_q75"]["failure_detection_auroc"]["observed"])
    e_delta = abs(e_h1 - E_H1_AUROC_TARGET)
    if e_delta > ANCHOR_TOL:
        stopped = {
            "status": "stopped_e_anchor_failed",
            "reason": "frozen E h=1 AUROC anchor failed",
            "observed_h1_auroc": e_h1,
            "target_h1_auroc": E_H1_AUROC_TARGET,
            "abs_delta": e_delta,
            "tolerance": ANCHOR_TOL,
        }
        REPORT_DIR.mkdir(exist_ok=True)
        JSON_PATH.write_text(json.dumps(finite_json(stopped), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text(
            "# Allocation Information Bound\n\n"
            f"Stopped: E anchor failed. observed `{e_h1:.17g}`, target `{E_H1_AUROC_TARGET:.17g}`.\n",
            encoding="utf-8",
        )
        raise SystemExit(f"E anchor failed: observed={e_h1:.17g}, target={E_H1_AUROC_TARGET:.17g}")
    return train_logits, eval_logits, {
        "status": "passed",
        "observed_h1_auroc": e_h1,
        "target_h1_auroc": E_H1_AUROC_TARGET,
        "abs_delta": e_delta,
        "tolerance": ANCHOR_TOL,
        "info": info,
    }


class SmallMLP(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(nn.Linear(in_dim, 96), nn.ReLU(), nn.Linear(96, 32), nn.ReLU(), nn.Linear(32, 1))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def train_torch_mlp_regressor(
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_test: np.ndarray,
    *,
    seed: int,
    epochs: int = 30,
    lr: float = 1e-3,
) -> np.ndarray:
    torch.manual_seed(seed)
    norm = fit_norm(x_train)
    xt = torch.from_numpy(apply_norm(x_train, norm))
    yt_np = np.log(y_train.astype(np.float64) + 1e-8).astype(np.float32)
    yt = torch.from_numpy(yt_np)
    model = SmallMLP(xt.shape[1])
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    g = torch.Generator().manual_seed(seed)
    n = len(yt)
    model.train()
    for _ in range(epochs):
        order = torch.randperm(n, generator=g)
        for start in range(0, n, 128):
            idx = order[start : start + 128]
            pred = model(xt[idx])
            loss = nn.functional.mse_loss(pred, yt[idx])
            if not torch.isfinite(loss):
                raise RuntimeError("non-finite small MLP regression loss")
            opt.zero_grad()
            loss.backward()
            opt.step()
    model.eval()
    out = np.zeros(len(x_test), dtype=np.float64)
    xte = apply_norm(x_test, norm)
    with torch.no_grad():
        for start in range(0, len(out), 512):
            sl = slice(start, min(start + 512, len(out)))
            out[sl] = model(torch.from_numpy(xte[sl])).detach().cpu().numpy().astype(np.float64)
    return out


def train_torch_ranknet(
    x_train: np.ndarray,
    y_train: np.ndarray,
    ep_train: np.ndarray,
    x_test: np.ndarray,
    *,
    seed: int,
    epochs: int = 35,
    lr: float = 1e-3,
) -> np.ndarray:
    torch.manual_seed(seed)
    norm = fit_norm(x_train)
    xt = torch.from_numpy(apply_norm(x_train, norm))
    yt = torch.from_numpy(y_train.astype(np.float32))
    ept = torch.from_numpy(ep_train.astype(np.int64))
    model = SmallMLP(xt.shape[1])
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    g = torch.Generator().manual_seed(seed)
    n = len(yt)
    model.train()
    for _ in range(epochs):
        order = torch.randperm(n, generator=g)
        for start in range(0, n, 128):
            idx = order[start : start + 128]
            score = model(xt[idx])
            maybe_loss = pairwise_logistic_loss(score, yt[idx], ept[idx])
            if maybe_loss is None:
                continue
            if not torch.isfinite(maybe_loss):
                raise RuntimeError("non-finite RankNet loss")
            opt.zero_grad()
            maybe_loss.backward()
            opt.step()
    model.eval()
    out = np.zeros(len(x_test), dtype=np.float64)
    xte = apply_norm(x_test, norm)
    with torch.no_grad():
        for start in range(0, len(out), 512):
            sl = slice(start, min(start + 512, len(out)))
            out[sl] = model(torch.from_numpy(xte[sl])).detach().cpu().numpy().astype(np.float64)
    return out


def train_scalar_auxiliary_scores(
    train_x: np.ndarray,
    eval_x: np.ndarray,
    clean: np.lib.npyio.NpzFile,
) -> tuple[np.ndarray, list[dict[str, Any]]]:
    valid = clean["train_valid"][:, TARGET_H_INDEX].astype(bool)
    y = clean["train_mean_err_to_h"][valid, TARGET_H_INDEX].astype(np.float64)
    ep = clean["train_anchor_ep_t0"][valid, 0].astype(np.int64)
    x = train_x[valid].astype(np.float32)
    out = []
    info = []

    print("[features] train train-split scalar auxiliary scores", flush=True)
    ridge = make_pipeline(StandardScaler(), Ridge(alpha=10.0))
    ridge.fit(x, np.log(y + 1e-8))
    out.append(ridge.predict(eval_x).astype(np.float64))
    info.append({"name": "aux_ridge_log_mean_err", "fit_split": "train", "target": "log mean_err_to_5"})

    et = ExtraTreesRegressor(n_estimators=80, max_depth=6, min_samples_leaf=4, random_state=PYTHON_SEED, n_jobs=1)
    et.fit(x, y)
    out.append(et.predict(eval_x).astype(np.float64))
    info.append({"name": "aux_extratrees_mean_err", "fit_split": "train", "target": "mean_err_to_5"})

    rank_score = train_torch_ranknet(x, y, ep, eval_x, seed=TORCH_SEED + 900, epochs=25)
    out.append(rank_score)
    info.append({"name": "aux_ranknet_train_split", "fit_split": "train", "target": "within-episode mean_err_to_5 rank"})

    return np.vstack(out).T.astype(np.float32), info


def train_posthoc_logistic_scores(
    train_x: np.ndarray,
    eval_x: np.ndarray,
    clean: np.lib.npyio.NpzFile,
) -> tuple[np.ndarray, list[dict[str, Any]]]:
    cols = [(h, q, g2n.H_TO_LABEL_IDX[h], g2n.Q_TO_IDX[q]) for h in g2n.HORIZONS for q in g2n.QUANTILES]
    y_all = np.stack([clean["train_y"][:, h_idx, q_idx] for _, _, h_idx, q_idx in cols], axis=1)
    valid_all = np.stack([clean["train_valid"][:, h_idx] for _, _, h_idx, _ in cols], axis=1)
    scores = np.zeros((len(eval_x), len(cols)), dtype=np.float32)
    infos = []
    print("[features] train post-hoc logistic scores", flush=True)
    for j, (h, q, _, _) in enumerate(cols):
        m = valid_all[:, j].astype(bool)
        y = y_all[m, j].astype(np.int8)
        if len(y) == 0 or np.unique(y).size < 2:
            p = float(np.clip(y.mean() if len(y) else 0.5, 1e-6, 1.0 - 1e-6))
            logit = math.log(p / (1.0 - p))
            scores[:, j] = logit
            infos.append({"col": int(j), "h": int(h), "q": int(q), "status": "constant", "label_rate": p})
            continue
        clf = make_pipeline(
            StandardScaler(),
            LogisticRegression(C=0.5, max_iter=500, solver="lbfgs", random_state=PYTHON_SEED),
        )
        clf.fit(train_x[m], y)
        scores[:, j] = clf.decision_function(eval_x).astype(np.float32)
        infos.append(
            {
                "col": int(j),
                "h": int(h),
                "q": int(q),
                "status": "fit",
                "label_rate": float(np.mean(y)),
                "train_rows": int(len(y)),
            }
        )
    return scores, infos


def cheap_posthoc_scores_from_logits(eval_logits: np.ndarray) -> tuple[np.ndarray, list[dict[str, Any]]]:
    probs = sigmoid_np(eval_logits).astype(np.float32)
    entropy = (-(probs * np.log(probs + 1e-8) + (1.0 - probs) * np.log(1.0 - probs + 1e-8))).astype(np.float32)
    margin = np.abs(probs - 0.5).astype(np.float32)
    scores = np.concatenate([eval_logits.astype(np.float32), probs, entropy, margin], axis=1).astype(np.float32)
    infos = [
        {
            "name": "cheap_posthoc_from_frozen_E",
            "status": "derived",
            "input": "12 frozen E logits",
            "outputs": "logits, sigmoid probabilities, Bernoulli entropy, absolute margin",
            "dim": int(scores.shape[1]),
        }
    ]
    return scores, infos


def build_full_feature_matrix(
    data: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    e_train_logits: np.ndarray,
    e_eval_logits: np.ndarray,
    valid_h5: np.ndarray,
) -> tuple[np.ndarray, dict[str, Any]]:
    train_ex = g2n.build_clean_examples(data, clean, "train", None)
    eval_ex = g2n.build_clean_examples(data, clean, "eval", None)
    train_raw = compose_raw_feature(basic_feature_blocks(train_ex))
    eval_raw = compose_raw_feature(basic_feature_blocks(eval_ex))
    aux_scores, aux_info = train_scalar_auxiliary_scores(train_raw, eval_raw, clean)
    posthoc, posthoc_info = cheap_posthoc_scores_from_logits(e_eval_logits)

    blocks = basic_feature_blocks(eval_ex)
    selected = {
        **blocks,
        "frozen_E_12_logits": e_eval_logits.astype(np.float32),
        "frozen_E_12_probs": sigmoid_np(e_eval_logits).astype(np.float32),
        "scalar_regression_rank_scores": aux_scores,
        "posthoc_logistic_scores": posthoc,
    }
    ordered = [
        "past_emb_action_window",
        "pred_z",
        "future_delta",
        "future_avail",
        "future_drift_norms",
        "last_state_proxy",
        "episode_time_state_proxy",
        "frozen_E_12_logits",
        "frozen_E_12_probs",
        "scalar_regression_rank_scores",
        "posthoc_logistic_scores",
    ]
    x_all = np.concatenate([selected[k] for k in ordered], axis=1).astype(np.float32)
    x = x_all[valid_h5]
    finite = np.isfinite(x)
    if not bool(finite.all()):
        col_mean = np.nanmean(np.where(finite, x, np.nan), axis=0)
        col_mean[~np.isfinite(col_mean)] = 0.0
        bad = ~finite
        x[bad] = np.take(col_mean, np.where(bad)[1])
    feature_info = {
        "blocks": {k: int(selected[k].shape[1]) for k in ordered},
        "total_dim": int(x.shape[1]),
        "eval_rows_h5_valid": int(x.shape[0]),
        "auxiliary_scalar_scores": aux_info,
        "posthoc_logistic_scores": posthoc_info,
        "note": "auxiliary scores are trained on the original train split; Step 2 readers are separately cross-fitted within eval episodes",
    }
    return x.astype(np.float32), feature_info


def episode_folds(episodes: np.ndarray) -> list[np.ndarray]:
    unique = np.unique(episodes)
    rng = np.random.default_rng(BOOTSTRAP_SEED)
    shuffled = unique.copy()
    rng.shuffle(shuffled)
    parts = np.array_split(shuffled, K_FOLDS)
    return [np.isin(episodes, part) for part in parts]


def fit_predict_sklearn_regressor(name: str, x_train: np.ndarray, y_train: np.ndarray, x_test: np.ndarray) -> np.ndarray:
    if name == "Ridge":
        model = make_pipeline(StandardScaler(), Ridge(alpha=10.0))
        target = np.log(y_train + 1e-8)
    elif name == "ElasticNet":
        model = make_pipeline(StandardScaler(), ElasticNet(alpha=0.001, l1_ratio=0.15, max_iter=5000, random_state=PYTHON_SEED))
        target = np.log(y_train + 1e-8)
    elif name == "RandomForest_shallow":
        model = RandomForestRegressor(
            n_estimators=60,
            max_depth=4,
            min_samples_leaf=4,
            max_features="sqrt",
            random_state=PYTHON_SEED,
            n_jobs=1,
        )
        target = y_train
    elif name == "ExtraTrees":
        model = ExtraTreesRegressor(
            n_estimators=80,
            max_depth=5,
            min_samples_leaf=3,
            max_features="sqrt",
            random_state=PYTHON_SEED,
            n_jobs=1,
        )
        target = y_train
    elif name == "HistGradientBoosting":
        model = HistGradientBoostingRegressor(
            max_iter=70,
            max_leaf_nodes=11,
            learning_rate=0.04,
            l2_regularization=0.1,
            random_state=PYTHON_SEED,
        )
        target = y_train
    else:
        raise ValueError(name)
    model.fit(x_train, target)
    return np.asarray(model.predict(x_test), dtype=np.float64)


def crossfit_reader_scores(
    x: np.ndarray,
    y: np.ndarray,
    episodes: np.ndarray,
    *,
    permutation: bool = False,
    reader_names: list[str] | None = None,
) -> dict[str, np.ndarray]:
    if reader_names is None:
        reader_names = ["Ridge", "ElasticNet", "RandomForest_shallow", "ExtraTrees", "HistGradientBoosting", "small_MLP", "pairwise_RankNet"]
    scores = {name: np.zeros(len(y), dtype=np.float64) for name in reader_names}
    folds = episode_folds(episodes)
    for fold_i, test_mask in enumerate(folds):
        train_mask = ~test_mask
        x_train = x[train_mask]
        y_train = y[train_mask].copy()
        ep_train = episodes[train_mask]
        if permutation:
            rng = np.random.default_rng(PYTHON_SEED + 1000 + fold_i)
            y_train = y_train[rng.permutation(len(y_train))]
        x_test = x[test_mask]
        print(
            f"[crossfit] {'permutation ' if permutation else ''}fold {fold_i + 1}/{K_FOLDS} "
            f"train={int(train_mask.sum())} test={int(test_mask.sum())}",
            flush=True,
        )
        for name in ("Ridge", "ElasticNet", "RandomForest_shallow", "ExtraTrees", "HistGradientBoosting"):
            if name in scores:
                scores[name][test_mask] = fit_predict_sklearn_regressor(name, x_train, y_train, x_test)
        if "small_MLP" in scores:
            scores["small_MLP"][test_mask] = train_torch_mlp_regressor(
                x_train,
                y_train,
                x_test,
                seed=TORCH_SEED + 10 * fold_i + (500 if permutation else 0),
                epochs=25,
            )
        if "pairwise_RankNet" in scores:
            scores["pairwise_RankNet"][test_mask] = train_torch_ranknet(
                x_train,
                y_train,
                ep_train,
                x_test,
                seed=TORCH_SEED + 100 + 10 * fold_i + (500 if permutation else 0),
                epochs=30,
            )
    return scores


def evaluate_reader_scores(
    scores: dict[str, np.ndarray],
    true_mean_h5: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    errors_h5: np.ndarray,
    uniform_alloc: dict[str, Any],
) -> dict[str, Any]:
    out = {}
    for name, score in scores.items():
        budget = budget_eval_for_score(name, score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
        out[name] = {
            "spearman": episode_spearman_bootstrap(score, true_mean_h5, anchors),
            "allocation": budget["allocation"],
            "delta_vs_uniform": budget["delta_vs_uniform"],
        }
    return out


def step1_oracle_blend_thresholds(
    true_mean_h5: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    errors_h5: np.ndarray,
    uniform_alloc: dict[str, Any],
) -> dict[str, Any]:
    print("[step1] oracle-blend rho curve: 150 noise seeds x 51 blend weights", flush=True)
    oracle = budget_eval_for_score("oracle", true_mean_h5.copy(), anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_delta = float(oracle["delta_vs_uniform"]["observed"])
    if abs(oracle_delta - ORACLE_DELTA_ANCHOR) > ANCHOR_TOL:
        raise SystemExit(f"oracle allocation anchor failed: observed={oracle_delta:.17g}, target={ORACLE_DELTA_ANCHOR:.17g}")

    oracle_rank_z = rank_z_within_episode(true_mean_h5, anchors_by_ep)
    fast_ctx = make_fast_allocation_context(anchors, anchors_by_ep, errors_h5)
    truth_ranks = precompute_truth_ranks(true_mean_h5, anchors_by_ep)
    seed_rows = []
    curve_accum: dict[float, list[dict[str, float]]] = {float(w): [] for w in BLEND_GRID}
    for s in range(RHO_NOISE_SEEDS):
        if s == 0 or (s + 1) % 25 == 0:
            print(f"[step1] noise seed {s + 1}/{RHO_NOISE_SEEDS}", flush=True)
        rng = np.random.default_rng(STEP1_NOISE_SEED_BASE + s)
        noise_rank_z = rank_z_within_episode(rng.standard_normal(len(true_mean_h5)), anchors_by_ep)
        rows = []
        for w in BLEND_GRID:
            score = float(w) * oracle_rank_z + (1.0 - float(w)) * noise_rank_z
            d = fast_delta_for_score(score, fast_ctx)
            row = {
                "blend_w": float(w),
                "rho": fast_episode_spearman_mean(score, truth_ranks),
                "delta": float(d["observed"]),
                "ci95_low": float(d["ci95_low"]),
                "ci95_high": float(d["ci95_high"]),
            }
            rows.append(row)
            curve_accum[float(w)].append(row)

        obs_threshold = None
        obs_bracket = None
        ci_threshold = None
        ci_bracket = None
        prev = rows[0]
        for row in rows:
            if obs_threshold is None and row["delta"] < 0.0:
                obs_threshold = row["rho"]
                obs_bracket = [prev, row] if row is not prev else [row, row]
            if ci_threshold is None and row["ci95_high"] < 0.0:
                ci_threshold = row["rho"]
                ci_bracket = [prev, row] if row is not prev else [row, row]
            prev = row
        if obs_threshold is None:
            obs_threshold = rows[-1]["rho"]
        if ci_threshold is None:
            ci_threshold = None
        seed_rows.append(
            {
                "noise_seed": int(STEP1_NOISE_SEED_BASE + s),
                "rho_star_obs_first_negative_observed": obs_threshold,
                "rho_star_ci_first_ci_below_zero": ci_threshold,
                "observed_crossing_bracket": obs_bracket,
                "ci_below_zero_bracket": ci_bracket,
            }
        )

    obs_arr = np.asarray([r["rho_star_obs_first_negative_observed"] for r in seed_rows], dtype=np.float64)
    ci_vals = [r["rho_star_ci_first_ci_below_zero"] for r in seed_rows if r["rho_star_ci_first_ci_below_zero"] is not None]
    ci_arr = np.asarray(ci_vals, dtype=np.float64)
    mean_curve = []
    for w in BLEND_GRID:
        rows = curve_accum[float(w)]
        mean_curve.append(
            {
                "blend_w": float(w),
                "rho_mean": float(np.mean([r["rho"] for r in rows])),
                "rho_p05": float(np.percentile([r["rho"] for r in rows], 5)),
                "rho_p95": float(np.percentile([r["rho"] for r in rows], 95)),
                "delta_mean": float(np.mean([r["delta"] for r in rows])),
                "delta_p05": float(np.percentile([r["delta"] for r in rows], 5)),
                "delta_p95": float(np.percentile([r["delta"] for r in rows], 95)),
                "ci95_high_mean": float(np.mean([r["ci95_high"] for r in rows])),
            }
        )
    return {
        "oracle_delta_anchor": oracle_delta,
        "noise_seed_count": RHO_NOISE_SEEDS,
        "blend_grid": [float(w) for w in BLEND_GRID],
        "rho_star_obs_distribution": {
            "n": int(len(obs_arr)),
            "mean": float(np.mean(obs_arr)),
            "p05": float(np.percentile(obs_arr, 5)),
            "p50": float(np.percentile(obs_arr, 50)),
            "p95": float(np.percentile(obs_arr, 95)),
            "min": float(np.min(obs_arr)),
            "max": float(np.max(obs_arr)),
        },
        "rho_star_ci_distribution": {
            "n_finite": int(len(ci_arr)),
            "n_missing": int(RHO_NOISE_SEEDS - len(ci_arr)),
            "mean": None if len(ci_arr) == 0 else float(np.mean(ci_arr)),
            "p05": None if len(ci_arr) == 0 else float(np.percentile(ci_arr, 5)),
            "p50": None if len(ci_arr) == 0 else float(np.percentile(ci_arr, 50)),
            "p95": None if len(ci_arr) == 0 else float(np.percentile(ci_arr, 95)),
        },
        "seed_thresholds": seed_rows,
        "mean_curve_by_blend_w": mean_curve,
    }


def rank_buckets_within_episode(y: np.ndarray, anchors_by_ep: dict[int, list[int]], n_buckets: int) -> np.ndarray:
    labels = np.zeros(len(y), dtype=np.int64)
    for idxs in anchors_by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        order = np.argsort(y[idx], kind="mergesort")
        local = np.zeros(len(idx), dtype=np.int64)
        for r, pos in enumerate(order):
            local[pos] = min(n_buckets - 1, int(math.floor(r * n_buckets / len(idx))))
        labels[idx] = local
    return labels


def episode_prior_probs(labels: np.ndarray, anchors_by_ep: dict[int, list[int]], n_classes: int) -> np.ndarray:
    probs = np.zeros((len(labels), n_classes), dtype=np.float64)
    for idxs in anchors_by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        counts = np.bincount(labels[idx], minlength=n_classes).astype(np.float64)
        p = (counts + 1e-6) / (counts.sum() + 1e-6 * n_classes)
        probs[idx] = p
    return probs


def fit_predict_classifier_probs(name: str, x_train: np.ndarray, y_train: np.ndarray, x_test: np.ndarray, n_classes: int) -> np.ndarray:
    present = np.unique(y_train)
    if len(present) < 2:
        p = np.full((len(x_test), n_classes), 1e-6, dtype=np.float64)
        p[:, int(present[0])] = 1.0 - 1e-6 * (n_classes - 1)
        return p / p.sum(axis=1, keepdims=True)
    if name == "LogisticRegression":
        clf = make_pipeline(
            StandardScaler(),
            LogisticRegression(C=0.5, max_iter=700, solver="lbfgs", multi_class="auto", random_state=PYTHON_SEED),
        )
    elif name == "RandomForest":
        clf = RandomForestClassifier(
            n_estimators=60,
            max_depth=4,
            min_samples_leaf=4,
            max_features="sqrt",
            random_state=PYTHON_SEED,
            n_jobs=1,
        )
    elif name == "ExtraTrees":
        clf = ExtraTreesClassifier(
            n_estimators=80,
            max_depth=5,
            min_samples_leaf=3,
            max_features="sqrt",
            random_state=PYTHON_SEED,
            n_jobs=1,
        )
    elif name == "HistGradientBoosting":
        clf = HistGradientBoostingClassifier(
            max_iter=70,
            max_leaf_nodes=11,
            learning_rate=0.04,
            l2_regularization=0.1,
            random_state=PYTHON_SEED,
        )
    else:
        raise ValueError(name)
    clf.fit(x_train, y_train)
    raw = clf.predict_proba(x_test)
    out = np.full((len(x_test), n_classes), 1e-9, dtype=np.float64)
    if hasattr(clf, "classes_"):
        classes = clf.classes_
    else:
        classes = clf.steps[-1][1].classes_
    for j, cls in enumerate(classes):
        out[:, int(cls)] = raw[:, j]
    out /= out.sum(axis=1, keepdims=True)
    return out


def crossfit_mi_for_bucket_count(
    x: np.ndarray,
    y: np.ndarray,
    episodes: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    n_classes: int,
) -> dict[str, Any]:
    labels = rank_buckets_within_episode(y, anchors_by_ep, n_classes)
    prior = episode_prior_probs(labels, anchors_by_ep, n_classes)
    classifier_names = ["LogisticRegression", "RandomForest", "ExtraTrees", "HistGradientBoosting"]
    folds = episode_folds(episodes)
    class_out = {}
    for name in classifier_names:
        probs = np.zeros((len(y), n_classes), dtype=np.float64)
        for fold_i, test_mask in enumerate(folds):
            train_mask = ~test_mask
            probs[test_mask] = fit_predict_classifier_probs(name, x[train_mask], labels[train_mask], x[test_mask], n_classes)
        eps = sorted(anchors_by_ep)
        improve_by_ep = {}
        for ep in eps:
            idx = np.asarray(anchors_by_ep[ep], dtype=np.int64)
            base = log_loss(labels[idx], prior[idx], labels=list(range(n_classes)))
            pred = log_loss(labels[idx], probs[idx], labels=list(range(n_classes)))
            improve_by_ep[int(ep)] = float(base - pred)
        mi = episode_metric_bootstrap(improve_by_ep)
        score = probs @ np.arange(n_classes, dtype=np.float64)
        class_out[name] = {
            "mi_hat_nats": mi,
            "spearman_bucket_score_to_mean_err": episode_spearman_bootstrap(score, y, anchors),
            "oof_logloss": float(log_loss(labels, probs, labels=list(range(n_classes)))),
            "episode_local_prior_logloss": float(log_loss(labels, prior, labels=list(range(n_classes)))),
        }
    best_name = max(class_out, key=lambda n: class_out[n]["mi_hat_nats"]["observed"])
    return {
        "n_buckets": int(n_classes),
        "labels": labels,
        "episode_local_prior_logloss": float(log_loss(labels, prior, labels=list(range(n_classes)))),
        "classifiers": class_out,
        "best_classifier": best_name,
        "best_mi_hat_nats": class_out[best_name]["mi_hat_nats"],
    }


def empirical_mi_of_channel(y_labels: np.ndarray, z_labels: np.ndarray, anchors_by_ep: dict[int, list[int]], n_classes: int) -> float:
    total_weight = 0.0
    total = 0.0
    for idxs in anchors_by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        y = y_labels[idx]
        z = z_labels[idx]
        py = np.bincount(y, minlength=n_classes).astype(np.float64)
        py = py / py.sum()
        hy = -float(np.sum(py[py > 0] * np.log(py[py > 0])))
        cond = 0.0
        for zc in range(n_classes):
            m = z == zc
            if not bool(m.any()):
                continue
            pz = float(np.mean(m))
            yz = np.bincount(y[m], minlength=n_classes).astype(np.float64)
            yz = yz / yz.sum()
            cond += pz * (-float(np.sum(yz[yz > 0] * np.log(yz[yz > 0]))))
        total += float(len(idx)) * max(0.0, hy - cond)
        total_weight += float(len(idx))
    return float(total / total_weight)


def calibrate_rho_max_from_mi(
    y: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    labels: np.ndarray,
    n_classes: int,
    mi_limit: float,
) -> dict[str, Any]:
    rng = np.random.default_rng(MI_SIM_SEED + n_classes)
    q_grid = np.round(np.linspace(0.0, 1.0, 41), 3)
    truth_ranks = precompute_truth_ranks(y, anchors_by_ep)
    rows = []
    accepted_rhos = []
    for q in q_grid:
        for rep in range(80):
            z = labels.copy()
            flip = rng.random(len(labels)) > float(q)
            z[flip] = rng.integers(0, n_classes, size=int(flip.sum()))
            jitter = rng.normal(0.0, 0.05, size=len(labels))
            score = z.astype(np.float64) + jitter
            mi = empirical_mi_of_channel(labels, z, anchors_by_ep, n_classes)
            rho = fast_episode_spearman_mean(score, truth_ranks)
            row = {"correct_channel_probability": float(q), "rep": int(rep), "mi_nats": float(mi), "rho": float(rho)}
            rows.append(row)
            if mi <= mi_limit + 1e-12:
                accepted_rhos.append(float(rho))
    if not accepted_rhos:
        accepted_rhos = [0.0]
    accepted = np.asarray(accepted_rhos, dtype=np.float64)
    return {
        "mi_limit_nats": float(mi_limit),
        "rho_max_observed_under_limit": float(np.max(accepted)),
        "rho_max_ci95_high_empirical": float(np.percentile(accepted, 97.5)),
        "rho_max_ci95_low_empirical": float(np.percentile(accepted, 2.5)),
        "accepted_simulations": int(len(accepted)),
        "total_simulations": int(len(rows)),
        "channel": "within-episode rank bucket revealed correctly with probability q, otherwise random bucket; score=bucket+jitter",
        "not_a_theorem": True,
        "calibration_rows": rows,
    }


def step3_mi_bound(
    x: np.ndarray,
    y: np.ndarray,
    episodes: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
) -> dict[str, Any]:
    print("[step3] cross-fit MI/log-loss and empirical rho calibration", flush=True)
    bucket_reports = {}
    rho_max_candidates = []
    for n_classes in (3, 5):
        mi_report = crossfit_mi_for_bucket_count(x, y, episodes, anchors, anchors_by_ep, n_classes)
        mi_limit = max(0.0, float(mi_report["best_mi_hat_nats"]["ci95_high"]))
        cal = calibrate_rho_max_from_mi(y, anchors, anchors_by_ep, mi_report["labels"], n_classes, mi_limit)
        mi_report_public = {k: v for k, v in mi_report.items() if k != "labels"}
        mi_report_public["empirical_rho_calibration"] = cal
        bucket_reports[f"{n_classes}_buckets"] = mi_report_public
        rho_max_candidates.append(cal["rho_max_ci95_high_empirical"])
    return {
        "bucket_reports": bucket_reports,
        "rho_max_MI_ci95_high": float(max(rho_max_candidates)),
        "definition": "empirical information bound, not a mathematical theorem",
    }


def write_markdown(report: dict[str, Any]) -> None:
    step1 = report["step1_oracle_blend"]
    step2 = report["step2_crossfit_readers"]
    step3 = report["step3_mi_ordinal_bound"]
    strongest = step2["strongest_reader"]
    strong_row = step2["readers"][strongest]
    lines = [
        "# Allocation Information Bound",
        "",
        f"- status: `{report['status']}`",
        f"- bound decision: `{report['bound_decision']['verdict']}`",
        f"- rho*_obs 5th percentile: `{step1['rho_star_obs_distribution']['p05']:.6f}`",
        f"- strongest cross-fit reader: `{strongest}` with Spearman "
        f"`{strong_row['spearman']['observed']:.6f}` "
        f"[`{strong_row['spearman']['ci95_low']:.6f}`, `{strong_row['spearman']['ci95_high']:.6f}`]",
        f"- rho_max_MI CI95_high: `{step3['rho_max_MI_ci95_high']:.6f}`",
        "",
        "## Step 1 - Oracle-Blend Thresholds",
        "",
        f"- noise seeds: `{step1['noise_seed_count']}`",
        f"- blend grid: `0..1 step 0.02`",
        f"- rho*_obs distribution: p05 `{step1['rho_star_obs_distribution']['p05']:.6f}`, "
        f"median `{step1['rho_star_obs_distribution']['p50']:.6f}`, "
        f"p95 `{step1['rho_star_obs_distribution']['p95']:.6f}`",
        f"- rho*_ci finite count: `{step1['rho_star_ci_distribution']['n_finite']}` "
        f"(missing `{step1['rho_star_ci_distribution']['n_missing']}`)",
        "",
        "## Step 2 - Cross-Fit Readers",
        "",
        "| reader | Spearman | 95% CI | delta vs uniform | delta 95% CI | wins uniform? |",
        "|---|---:|---:|---:|---:|:--:|",
    ]
    for name, row in step2["readers"].items():
        sp = row["spearman"]
        d = row["delta_vs_uniform"]
        lines.append(
            f"| `{name}` | {sp['observed']:.6f} | [{sp['ci95_low']:.6f}, {sp['ci95_high']:.6f}] | "
            f"{d['observed']:.9f} | [{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | "
            f"{'yes' if d['ci95_high'] < 0 else 'no'} |"
        )
    lines.extend(
        [
            "",
            "## Step 3 - MI / Ordinal Sanity",
            "",
            "| bucket | best classifier | MI hat nats | 95% CI | empirical rho_max CI95_high |",
            "|---|---|---:|---:|---:|",
        ]
    )
    for key, row in step3["bucket_reports"].items():
        mi = row["best_mi_hat_nats"]
        cal = row["empirical_rho_calibration"]
        lines.append(
            f"| `{key}` | `{row['best_classifier']}` | {mi['observed']:.6f} | "
            f"[{mi['ci95_low']:.6f}, {mi['ci95_high']:.6f}] | {cal['rho_max_ci95_high_empirical']:.6f} |"
        )
    lines.extend(
        [
            "",
            "## Sanity Controls",
            "",
            f"- permutation max abs Spearman: `{step2['permutation_control']['max_abs_spearman_observed']:.6f}` "
            f"(pass `{step2['permutation_control']['passed']}`)",
            f"- oracle Spearman: `{step2['oracle_sanity']['spearman']['observed']:.6f}` "
            f"[`{step2['oracle_sanity']['spearman']['ci95_low']:.6f}`, "
            f"`{step2['oracle_sanity']['spearman']['ci95_high']:.6f}`] "
            f"(pass `{step2['oracle_sanity']['passed']}`)",
            "",
            "## Bound Decision",
            "",
        ]
    )
    for item in report["bound_decision"]["criteria"]:
        lines.append(f"- {item['name']}: `{item['passed']}` - {item['detail']}")
    lines.extend(["", "## Not Claimed", ""])
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    REPORT_DIR.mkdir(exist_ok=True)
    t0 = time.perf_counter()

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    splits = g2n.split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")
    clean = np.load(CLEAN_LABELS)
    clean_eval_ex = g2n.build_clean_examples(data, clean, "eval", None)
    anchors, anchors_by_ep, errors_h5, true_mean_h5, valid_h5, uniform_alloc = anchors_from_eval(clean_eval_ex, clean)
    episodes = np.asarray([a["episode"] for a in anchors], dtype=np.int64)

    e_train_logits, e_eval_logits, e_anchor = predict_native_logits()

    step1 = step1_oracle_blend_thresholds(true_mean_h5, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    rho_star_obs_p05 = float(step1["rho_star_obs_distribution"]["p05"])

    print("[features] build full finite CPU-readable latent feature matrix", flush=True)
    x, feature_info = build_full_feature_matrix(data, clean, e_train_logits, e_eval_logits, valid_h5)

    print("[step2] cross-fit reader collection", flush=True)
    scores = crossfit_reader_scores(x, true_mean_h5, episodes, permutation=False)
    reader_results = evaluate_reader_scores(scores, true_mean_h5, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    strongest = max(reader_results, key=lambda n: reader_results[n]["spearman"]["observed"])

    print("[step2] permutation-label controls", flush=True)
    perm_reader_names = ["Ridge", "ExtraTrees", "pairwise_RankNet"]
    perm_scores = crossfit_reader_scores(x, true_mean_h5, episodes, permutation=True, reader_names=perm_reader_names)
    perm_results = evaluate_reader_scores(perm_scores, true_mean_h5, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    perm_abs = {name: abs(float(row["spearman"]["observed"])) for name, row in perm_results.items()}
    perm_passed = bool(max(perm_abs.values()) <= PERMUTATION_RHO_ABS_MAX)

    oracle_budget = budget_eval_for_score("oracle", true_mean_h5.copy(), anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_spearman = episode_spearman_bootstrap(true_mean_h5.copy(), true_mean_h5, anchors)
    oracle_passed = bool(float(oracle_spearman["observed"]) >= ORACLE_RHO_MIN and abs(float(oracle_budget["delta_vs_uniform"]["observed"]) - ORACLE_DELTA_ANCHOR) <= ANCHOR_TOL)

    if not perm_passed or not oracle_passed:
        stopped = {
            "status": "stopped_sanity_failed",
            "reason": "permutation control or oracle sanity failed",
            "permutation_control": {
                "passed": perm_passed,
                "max_abs_spearman_observed": max(perm_abs.values()),
                "per_reader": perm_results,
                "threshold_abs": PERMUTATION_RHO_ABS_MAX,
            },
            "oracle_sanity": {
                "passed": oracle_passed,
                "spearman": oracle_spearman,
                "delta_vs_uniform": oracle_budget["delta_vs_uniform"],
            },
        }
        JSON_PATH.write_text(json.dumps(finite_json(stopped), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text(
            "# Allocation Information Bound\n\n"
            "Stopped: sanity control failed. See JSON for permutation/oracle diagnostics.\n",
            encoding="utf-8",
        )
        raise SystemExit("sanity control failed; stopped report written")

    step3 = step3_mi_bound(x, true_mean_h5, episodes, anchors, anchors_by_ep)

    strongest_high = float(reader_results[strongest]["spearman"]["ci95_high"])
    reader_rho_pass = strongest_high < rho_star_obs_p05
    deltas_pass = all(float(row["delta_vs_uniform"]["ci95_high"]) >= 0.0 for row in reader_results.values())
    mi_pass = float(step3["rho_max_MI_ci95_high"]) < rho_star_obs_p05
    bound_established = bool(reader_rho_pass and deltas_pass and mi_pass)

    criteria = [
        {
            "name": "strongest cross-fit reader Spearman CI95_high below rho*_obs p05",
            "passed": bool(reader_rho_pass),
            "detail": f"{strongest} CI95_high={strongest_high:.6f} vs rho*_obs_p05={rho_star_obs_p05:.6f}",
        },
        {
            "name": "all reader allocation delta CI95_high >= 0",
            "passed": bool(deltas_pass),
            "detail": "no cross-fit reader beats uniform allocation by the paired episode bootstrap",
        },
        {
            "name": "rho_max_MI CI95_high below rho*_obs p05",
            "passed": bool(mi_pass),
            "detail": f"rho_max_MI_CI95_high={step3['rho_max_MI_ci95_high']:.6f} vs rho*_obs_p05={rho_star_obs_p05:.6f}",
        },
    ]
    verdict = "bound_established" if bound_established else "bound_not_established"
    status = "ok_bound_established" if bound_established else "ok_bound_not_established"

    report = {
        "status": status,
        "schema_id": "lewm.allocation_information_bound",
        "question": "Can allocation ranking information be audited as bounded near rho~0.5 under the frozen negative-terminal protocol?",
        "protocol": {
            "seeds": {
                "numpy": PYTHON_SEED,
                "torch": TORCH_SEED,
                "split": SPLIT_SEED,
                "bootstrap": BOOTSTRAP_SEED,
                "step1_noise_seed_base": STEP1_NOISE_SEED_BASE,
                "mi_sim": MI_SIM_SEED,
            },
            "bootstrap_resamples": BOOTSTRAPS,
            "bootstrap_unit": "episode",
            "crossfit": f"{K_FOLDS}-fold by eval episode",
            "target": "eval split true mean_err_to_h[:, h=5]",
            "ranking_metric": "within-episode Spearman, episode-mean",
            "allocation_rule": {
                "uniform": f"h={UNIFORM_H} for every anchor",
                "score_sorted": f"within episode low score half h={LOW_H}, high score half h={HIGH_H}, odd median h={MID_H}",
                "oracle": "same rule, sorted by true h=5 mean error",
            },
            "eval": {
                "anchors": int(len(anchors)),
                "episodes": int(len(anchors_by_ep)),
                "episode_split": "eval",
            },
        },
        "precursors": {str(p.name): str(p) for p in REQUIRED},
        "anchors": {
            "frozen_E_h1_auroc": e_anchor,
            "oracle_delta": {
                "observed": float(oracle_budget["delta_vs_uniform"]["observed"]),
                "target": ORACLE_DELTA_ANCHOR,
                "abs_delta": abs(float(oracle_budget["delta_vs_uniform"]["observed"]) - ORACLE_DELTA_ANCHOR),
                "tolerance": ANCHOR_TOL,
                "status": "passed",
            },
        },
        "features": feature_info,
        "step1_oracle_blend": step1,
        "step2_crossfit_readers": {
            "readers": reader_results,
            "strongest_reader": strongest,
            "permutation_control": {
                "passed": perm_passed,
                "max_abs_spearman_observed": float(max(perm_abs.values())),
                "threshold_abs": PERMUTATION_RHO_ABS_MAX,
                "reader_subset": perm_reader_names,
                "per_reader": perm_results,
            },
            "oracle_sanity": {
                "passed": oracle_passed,
                "spearman": oracle_spearman,
                "delta_vs_uniform": oracle_budget["delta_vs_uniform"],
            },
        },
        "step3_mi_ordinal_bound": step3,
        "bound_decision": {
            "verdict": verdict,
            "established": bool(bound_established),
            "criteria": criteria,
            "required_wording_if_used": "under the current latent export, finite CPU-readable feature family, and fixed 5/1/3 allocation rule",
        },
        "runtime_seconds": round(time.perf_counter() - t0, 2),
        "not_claimed": [
            "not a theorem that the world model contains no allocation information",
            "not a claim about all possible models or all possible feature families",
            "not a claim beyond the current latent export, finite CPU-readable feature family, and fixed 5/1/3 allocation rule",
            "MI/ordinal bound is an empirical information bound, not a mathematical theorem",
            "single tworooms checkpoint/export and eval split only",
        ],
    }
    clean_report = finite_json(report)
    JSON_PATH.write_text(json.dumps(clean_report, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_report)
    print(
        json.dumps(
            finite_json(
                {
                    "status": status,
                    "verdict": verdict,
                    "rho_star_obs_p05": rho_star_obs_p05,
                    "strongest_reader": strongest,
                    "strongest_spearman": reader_results[strongest]["spearman"],
                    "rho_max_MI_ci95_high": step3["rho_max_MI_ci95_high"],
                    "criteria": criteria,
                }
            ),
            indent=2,
            ensure_ascii=False,
        ),
        flush=True,
    )
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

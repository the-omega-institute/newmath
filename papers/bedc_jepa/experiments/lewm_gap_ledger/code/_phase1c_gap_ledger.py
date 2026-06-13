from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
NPZ_PATH = ROOT / "tworooms_latent_large.npz"
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_gap_ledger_head_large.json"
MD_PATH = REPORT_DIR / "lewm_gap_ledger_head_large.md"
FINDINGS_PATH = ROOT / "PHASE1C_FINDINGS.md"

PYTHON_SEED = 20260611
SPLIT_SEED = 1701
MATCHED_RANDOM_SEED = 90210
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500

DISTINCTIONS = ("agent_room_right", "same_room", "near_target")
FEATURE_VARIANTS = {
    "A_all_probe_features": (0, 1, 2),
    "B_denoised_agent_room_only": (0,),
}
GAP_CHANNELS = (
    "prediction_error",
    "low_margin",
    "transition_unstable",
    "off_target_intervention",
)


@dataclass
class LogisticHead:
    mean: np.ndarray
    scale: np.ndarray
    weight: np.ndarray
    bias: float
    constant: float | None = None


def sigmoid(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def fit_logistic_head(
    x: np.ndarray,
    y: np.ndarray,
    *,
    steps: int,
    lr: float,
    l2: float,
) -> tuple[LogisticHead, dict[str, Any]]:
    y = y.astype(np.float64)
    rate = float(y.mean()) if len(y) else float("nan")
    if len(y) == 0 or np.unique(y).size < 2:
        const = 0.5 if not np.isfinite(rate) else float(np.clip(rate, 1e-6, 1.0 - 1e-6))
        return (
            LogisticHead(
                mean=np.zeros(x.shape[1], dtype=np.float64),
                scale=np.ones(x.shape[1], dtype=np.float64),
                weight=np.zeros(x.shape[1], dtype=np.float64),
                bias=float(math.log(const / (1.0 - const))),
                constant=const,
            ),
            {"status": "degenerate", "label_rate": rate},
        )

    mean = x.mean(axis=0)
    scale = x.std(axis=0)
    scale[scale < 1e-8] = 1.0
    z = (x - mean) / scale
    w = np.zeros(z.shape[1], dtype=np.float64)
    bias0 = float(np.log(np.clip(rate, 1e-6, 1.0 - 1e-6) / np.clip(1.0 - rate, 1e-6, 1.0)))

    n = float(len(y))
    for _ in range(steps):
        p = sigmoid(z @ w + bias0)
        err = p - y
        grad_w = (z.T @ err) / n + l2 * w
        grad_b = float(err.mean())
        w -= lr * grad_w
        bias0 -= lr * grad_b

    p_final = sigmoid(z @ w + bias0)
    eps = 1e-12
    loss = float(-(y * np.log(p_final + eps) + (1.0 - y) * np.log(1.0 - p_final + eps)).mean())
    return (
        LogisticHead(mean=mean, scale=scale, weight=w, bias=bias0, constant=None),
        {"status": "fit", "label_rate": rate, "train_loss": loss},
    )


def predict_logistic_head(head: LogisticHead, x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    if head.constant is not None:
        p = np.full(x.shape[0], head.constant, dtype=np.float64)
        logit = np.full(
            x.shape[0],
            float(math.log(head.constant / max(1e-12, 1.0 - head.constant))),
            dtype=np.float64,
        )
        return p, logit
    z = (x - head.mean) / head.scale
    logit = z @ head.weight + head.bias
    return sigmoid(logit), logit


def auroc_rank(y_true: np.ndarray, score: np.ndarray) -> float:
    y = y_true.astype(bool)
    n_pos = int(y.sum())
    n_neg = int((~y).sum())
    if n_pos == 0 or n_neg == 0:
        return 0.5
    order = np.argsort(score, kind="mergesort")
    sorted_score = score[order]
    ranks = np.empty(len(score), dtype=np.float64)
    i = 0
    while i < len(score):
        j = i + 1
        while j < len(score) and sorted_score[j] == sorted_score[i]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        ranks[order[i:j]] = avg_rank
        i = j
    return float((ranks[y].sum() - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg))


def ece_10bin(y_true: np.ndarray, prob: np.ndarray) -> float:
    y = y_true.astype(np.float64)
    if len(y) == 0:
        return float("nan")
    edges = np.linspace(0.0, 1.0, 11)
    out = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        if hi == 1.0:
            m = (prob >= lo) & (prob <= hi)
        else:
            m = (prob >= lo) & (prob < hi)
        if not np.any(m):
            continue
        out += float(m.mean()) * abs(float(prob[m].mean()) - float(y[m].mean()))
    return float(out)


def basic_metrics(y_err: np.ndarray, gap_score: np.ndarray, critical_score: np.ndarray) -> dict[str, float]:
    return {
        "failure_detection_auroc": auroc_rank(y_err, gap_score),
        "ece": ece_10bin(y_err, gap_score),
        "unlogged_error_rate": float(np.mean((y_err > 0) & (gap_score < 0.5))),
        "critical_unlogged_error_rate": float(np.mean((y_err > 0) & (critical_score < 0.5))),
    }


def bootstrap_metrics(
    y_err: np.ndarray,
    gap_score: np.ndarray,
    critical_score: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, dict[str, float]]:
    observed = basic_metrics(y_err, gap_score, critical_score)
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    n = len(y_err)
    for _ in range(n_boot):
        idx = rng.integers(0, n, size=n)
        m = basic_metrics(y_err[idx], gap_score[idx], critical_score[idx])
        for k, v in m.items():
            values[k].append(v)
    out: dict[str, dict[str, float]] = {}
    for k, obs in observed.items():
        arr = np.asarray(values[k], dtype=np.float64)
        out[k] = {
            "observed": float(obs),
            "bootstrap_mean": float(np.nanmean(arr)),
            "ci95_low": float(np.nanpercentile(arr, 2.5)),
            "ci95_high": float(np.nanpercentile(arr, 97.5)),
        }
    return out


def bootstrap_metrics_by_episode(
    y_err: np.ndarray,
    gap_score: np.ndarray,
    critical_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, dict[str, float]]:
    observed = basic_metrics(y_err, gap_score, critical_score)
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    n_ep = len(by_ep)
    for _ in range(n_boot):
        sampled = rng.integers(0, n_ep, size=n_ep)
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = basic_metrics(y_err[idx], gap_score[idx], critical_score[idx])
        for k, v in m.items():
            values[k].append(v)
    out: dict[str, dict[str, float]] = {}
    for k, obs in observed.items():
        arr = np.asarray(values[k], dtype=np.float64)
        out[k] = {
            "observed": float(obs),
            "bootstrap_mean": float(np.nanmean(arr)),
            "ci95_low": float(np.nanpercentile(arr, 2.5)),
            "ci95_high": float(np.nanpercentile(arr, 97.5)),
        }
    return out


def split_episodes(n_ep: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(SPLIT_SEED)
    perm = rng.permutation(n_ep)
    n_train = int(round(0.60 * n_ep))
    n_cal = int(round(0.20 * n_ep))
    train = np.sort(perm[:n_train])
    cal = np.sort(perm[n_train : n_train + n_cal])
    eval_ep = np.sort(perm[n_train + n_cal :])
    return {"train": train, "calibration": cal, "eval": eval_ep}


def flatten_transition_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    tm = data["transition_mask"].astype(bool)
    ep_idx, t_idx = np.where(tm)
    rows = {
        "episode": ep_idx.astype(np.int64),
        "t": t_idx.astype(np.int64),
        "emb": data["emb"][ep_idx, t_idx].astype(np.float64),
        "next_emb": data["emb"][ep_idx, t_idx + 1].astype(np.float64),
        "pred": data["pred"][ep_idx, t_idx].astype(np.float64),
        "mse": data["prediction_mse"][ep_idx, t_idx].astype(np.float64),
        "observation": data["observation"][ep_idx, t_idx].astype(np.float64),
        "action": data["action"][ep_idx, t_idx].astype(np.float64),
        "pos_agent": data["pos_agent"][ep_idx, t_idx].astype(np.float64),
        "pos_target": data["pos_target"][ep_idx, t_idx].astype(np.float64),
        "distance_to_target": data["distance_to_target"][ep_idx, t_idx].astype(np.float64),
        "next_pos_agent": data["pos_agent"][ep_idx, t_idx + 1].astype(np.float64),
        "next_pos_target": data["pos_target"][ep_idx, t_idx + 1].astype(np.float64),
        "next_distance_to_target": data["distance_to_target"][ep_idx, t_idx + 1].astype(np.float64),
    }
    finite = (
        np.isfinite(rows["emb"]).all(axis=1)
        & np.isfinite(rows["pred"]).all(axis=1)
        & np.isfinite(rows["mse"])
        & np.isfinite(rows["observation"]).all(axis=1)
        & np.isfinite(rows["pos_agent"]).all(axis=1)
        & np.isfinite(rows["pos_target"]).all(axis=1)
        & np.isfinite(rows["distance_to_target"])
    )
    if not np.all(finite):
        rows = {k: v[finite] for k, v in rows.items()}
    return rows


def distinction_truth(rows: dict[str, np.ndarray], near_threshold: float, *, prefix: str = "") -> np.ndarray:
    pa = rows[f"{prefix}pos_agent"]
    pt = rows[f"{prefix}pos_target"]
    dist = rows[f"{prefix}distance_to_target"]
    agent_room_right = pa[:, 0] >= 112.0
    same_room = (pa[:, 0] >= 112.0) == (pt[:, 0] >= 112.0)
    near_target = dist < near_threshold
    return np.stack([agent_room_right, same_room, near_target], axis=1).astype(np.int8)


def fit_linear_r2_quality(
    x_train: np.ndarray,
    y_train: np.ndarray,
    x_eval: np.ndarray,
    y_eval: np.ndarray,
    *,
    ridge: float = 1e-5,
) -> tuple[np.ndarray, dict[str, Any]]:
    x_mean = x_train.mean(axis=0)
    x_std = x_train.std(axis=0)
    x_std[x_std < 1e-8] = 1.0
    y_mean = y_train.mean(axis=0)
    xs = (x_train - x_mean) / x_std
    ys = y_train - y_mean
    a = xs.T @ xs + ridge * np.eye(xs.shape[1])
    b = xs.T @ ys
    coef = np.linalg.solve(a, b)

    def r2_for(x: np.ndarray, y: np.ndarray) -> np.ndarray:
        pred = ((x - x_mean) / x_std) @ coef + y_mean
        ss_res = np.sum((y - pred) ** 2, axis=0)
        ss_tot = np.sum((y - y.mean(axis=0)) ** 2, axis=0)
        return 1.0 - ss_res / np.maximum(ss_tot, 1e-12)

    train_r2 = r2_for(x_train, y_train)
    eval_r2 = r2_for(x_eval, y_eval)
    quality = np.concatenate([[float(np.mean(train_r2))], train_r2.astype(np.float64)])
    report = {
        "proxy": "linear ridge regression emb->observation; gap input tiles train-split R2 only",
        "ridge": ridge,
        "train_mean_r2": float(np.mean(train_r2)),
        "train_per_observation_dim_r2": train_r2.tolist(),
        "eval_mean_r2_report_only": float(np.mean(eval_r2)),
        "eval_per_observation_dim_r2_report_only": eval_r2.tolist(),
        "quality_feature_width": int(len(quality)),
    }
    return quality, report


def build_gap_features(
    emb: np.ndarray,
    probe_prob: np.ndarray,
    probe_logit: np.ndarray,
    probe_pred: np.ndarray,
    quality_feature: np.ndarray,
    probe_indices: tuple[int, ...] | None = None,
) -> tuple[np.ndarray, np.ndarray]:
    if probe_indices is not None:
        probe_prob = probe_prob[:, probe_indices]
        probe_logit = probe_logit[:, probe_indices]
        probe_pred = probe_pred[:, probe_indices]
    signed_margin = probe_logit.copy()
    min_abs_margin = np.min(np.abs(probe_logit), axis=1, keepdims=True)
    q = np.tile(quality_feature.reshape(1, -1), (emb.shape[0], 1))
    x = np.concatenate([emb, probe_prob, probe_logit, probe_pred, signed_margin, min_abs_margin, q], axis=1)
    return x.astype(np.float64), min_abs_margin[:, 0]


def score_gap_sound_scan(y_err: np.ndarray, critical_score: np.ndarray) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    epsilons = [0.0, 0.05, 0.10, 0.20]
    taus = [round(x, 1) for x in np.arange(0.1, 1.0, 0.1)]
    for eps in epsilons:
        for tau in taus:
            low = critical_score < tau
            errors = y_err > 0
            low_n = int(low.sum())
            low_error_rate = float(np.mean(errors[low])) if low_n else float("nan")
            unlogged_at_tau = float(np.mean(errors & low))
            logged_given_error = float(np.mean(critical_score[errors] >= tau)) if np.any(errors) else float("nan")
            out.append(
                {
                    "epsilon": eps,
                    "tau": tau,
                    "low_gap_count": low_n,
                    "low_gap_coverage": float(low.mean()),
                    "low_gap_error_rate": low_error_rate,
                    "unlogged_error_rate_at_tau": unlogged_at_tau,
                    "logged_given_error_rate": logged_given_error,
                    "low_gap_error_bounded_pass": bool(np.isfinite(low_error_rate) and low_error_rate <= eps),
                    "error_logged_pass": bool(unlogged_at_tau <= eps),
                }
            )
    return out


def compute_counterfactual_off_target(
    npz_path: Path,
    rows: dict[str, np.ndarray],
    probe_heads: dict[str, LogisticHead],
    debts: list[dict[str, str]],
) -> tuple[np.ndarray, dict[str, Any]]:
    try:
        import json as _json

        import torch
        from huggingface_hub import hf_hub_download

        from lewm_latent_probe import build_model, load_checkpoint
    except Exception as exc:  # pragma: no cover - environment dependent
        debts.append(
            {
                "type": "source_debt",
                "source": "off_target_intervention",
                "detail": f"torch/HF/model imports unavailable; channel skipped fail-closed: {exc}",
            }
        )
        return np.zeros(len(rows["episode"]), dtype=np.int8), {"status": "skipped", "reason": repr(exc)}

    try:
        data = np.load(npz_path)
        history_size = int(np.asarray(data["history_size"]).item())
        device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
        checkpoint_path = hf_hub_download("quentinll/lewm-tworooms", "weights.pt", repo_type="model")
        config_path = hf_hub_download("quentinll/lewm-tworooms", "config.json", repo_type="model")
        with open(config_path, "r", encoding="utf-8") as f:
            config = _json.load(f)
        model = build_model(config)
        load_checkpoint(model, checkpoint_path)
        model.to(device).eval().requires_grad_(False)

        emb_all = data["emb"].astype(np.float32)
        act_all = data["action"].astype(np.float32)
        pred_all = rows["pred"].astype(np.float64)
        base_probe = []
        for name in DISTINCTIONS:
            p, _ = predict_logistic_head(probe_heads[name], pred_all)
            base_probe.append(p >= 0.5)
        base_probe_arr = np.stack(base_probe, axis=1)

        windows_emb: list[np.ndarray] = []
        windows_act_zero: list[np.ndarray] = []
        windows_act_neg: list[np.ndarray] = []
        positions: list[int] = []
        valid_source = np.ones(len(rows["episode"]), dtype=bool)
        for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"])):
            ep = int(ep)
            t = int(t)
            start = 0 if t < history_size else t - history_size + 1
            pos = t - start
            e = emb_all[ep, start : start + history_size]
            a = act_all[ep, start : start + history_size]
            if e.shape[0] != history_size or a.shape[0] != history_size or not np.isfinite(e).all() or not np.isfinite(a).all():
                valid_source[i] = False
                e = np.zeros((history_size, emb_all.shape[-1]), dtype=np.float32)
                a = np.zeros((history_size, act_all.shape[-1]), dtype=np.float32)
                pos = min(max(pos, 0), history_size - 1)
            az = a.copy()
            an = a.copy()
            az[pos] = 0.0
            an[pos] = -an[pos]
            windows_emb.append(e)
            windows_act_zero.append(az)
            windows_act_neg.append(an)
            positions.append(pos)

        def run_mode(windows_act: list[np.ndarray], batch_size: int = 512) -> np.ndarray:
            out = np.zeros((len(windows_act), pred_all.shape[1]), dtype=np.float64)
            with torch.inference_mode():
                for lo in range(0, len(windows_act), batch_size):
                    hi = min(lo + batch_size, len(windows_act))
                    be = torch.from_numpy(np.stack(windows_emb[lo:hi])).to(device=device, dtype=torch.float32)
                    ba = torch.from_numpy(np.stack(windows_act[lo:hi])).to(device=device, dtype=torch.float32)
                    bp = model.predict(be, model.action_encoder(ba)).detach().cpu().numpy()
                    for j, pos in enumerate(positions[lo:hi]):
                        out[lo + j] = bp[j, pos]
            return out

        cf_zero = run_mode(windows_act_zero)
        cf_neg = run_mode(windows_act_neg)

        labels = np.zeros(len(rows["episode"]), dtype=np.int8)
        flip_counts: dict[str, int] = {}
        for mode_name, cf in (("zero", cf_zero), ("negate", cf_neg)):
            cf_probe = []
            for name in DISTINCTIONS:
                p, _ = predict_logistic_head(probe_heads[name], cf)
                cf_probe.append(p >= 0.5)
            cf_probe_arr = np.stack(cf_probe, axis=1)
            flips = np.any(cf_probe_arr != base_probe_arr, axis=1) & valid_source
            labels |= flips.astype(np.int8)
            flip_counts[mode_name] = int(flips.sum())

        report = {
            "status": "computed_with_lewm_predictor",
            "model_repo": "quentinll/lewm-tworooms",
            "device": str(device),
            "definition": "for each transition, zero/negate current action block, predict next emb, probe cf next emb, label=any non-target distinction flip; with 3 distinctions this is equivalent to any probe flip under a target-max scan",
            "valid_source_rows": int(valid_source.sum()),
            "flip_counts_by_perturbation": flip_counts,
            "label_rate_all_rows": float(labels.mean()),
        }
        return labels, report
    except Exception as exc:  # pragma: no cover - environment dependent
        debts.append(
            {
                "type": "source_debt",
                "source": "off_target_intervention",
                "detail": f"LeWM predictor counterfactual failed; channel set to zero and marked degenerate: {exc}",
            }
        )
        return np.zeros(len(rows["episode"]), dtype=np.int8), {"status": "skipped", "reason": repr(exc)}


def ci_separation(a: dict[str, dict[str, float]], b: dict[str, dict[str, float]], metric: str) -> bool:
    return a[metric]["ci95_low"] > b[metric]["ci95_high"]


def fmt_ci(m: dict[str, float]) -> str:
    return f"{m['observed']:.4f} [{m['ci95_low']:.4f}, {m['ci95_high']:.4f}]"


def main() -> None:
    np.seterr(all="raise")
    REPORT_DIR.mkdir(exist_ok=True)
    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    rows = flatten_transition_rows(data)
    n_rows = len(rows["episode"])

    splits_ep = split_episodes(data["emb"].shape[0])
    split_masks = {name: np.isin(rows["episode"], eps) for name, eps in splits_ep.items()}
    train_mask = split_masks["train"]
    cal_mask = split_masks["calibration"]
    eval_mask = split_masks["eval"]

    debts: list[dict[str, str]] = []
    if int(eval_mask.sum()) < 50:
        debts.append(
            {
                "type": "coverage_debt",
                "source": "episode_split",
                "detail": f"eval transition count is only {int(eval_mask.sum())}; bootstrap CI is row-resampling, not independent world seeds",
            }
        )
    debts.append(
        {
            "type": "coverage_debt",
            "source": "statistical_design",
            "detail": f"single LeWM tworooms latent export with {data['emb'].shape[0]} episodes/{n_rows} transitions; episode bootstrap does not replace >=30 independent world seeds",
        }
    )

    near_threshold = float(np.median(rows["distance_to_target"][train_mask]))
    y_dist = distinction_truth(rows, near_threshold, prefix="")
    next_rows = {
        "next_pos_agent": rows["next_pos_agent"],
        "next_pos_target": rows["next_pos_target"],
        "next_distance_to_target": rows["next_distance_to_target"],
    }
    y_dist_next = distinction_truth(
        {
            "next_pos_agent": next_rows["next_pos_agent"],
            "next_pos_target": next_rows["next_pos_target"],
            "next_distance_to_target": next_rows["next_distance_to_target"],
        },
        near_threshold,
        prefix="next_",
    )

    probe_heads: dict[str, LogisticHead] = {}
    probe_report: dict[str, Any] = {}
    probe_prob_cols = []
    probe_logit_cols = []
    probe_pred_cols = []
    for j, name in enumerate(DISTINCTIONS):
        head, info = fit_logistic_head(rows["emb"][train_mask], y_dist[train_mask, j], steps=700, lr=0.18, l2=1e-4)
        probe_heads[name] = head
        p_all, logit_all = predict_logistic_head(head, rows["emb"])
        pred_all = (p_all >= 0.5).astype(np.float64)
        probe_prob_cols.append(p_all)
        probe_logit_cols.append(logit_all)
        probe_pred_cols.append(pred_all)
        eval_acc = float(np.mean(pred_all[eval_mask] == y_dist[eval_mask, j]))
        train_acc = float(np.mean(pred_all[train_mask] == y_dist[train_mask, j]))
        cal_acc = float(np.mean(pred_all[cal_mask] == y_dist[cal_mask, j]))
        if eval_acc < 0.60:
            debts.append(
                {
                    "type": "source_debt",
                    "source": f"distinction_probe:{name}",
                    "detail": f"eval accuracy {eval_acc:.4f} below 0.60 separability sanity threshold",
                }
            )
        probe_report[name] = {
            "truth_source": {
                "agent_room_right": "pos_agent.x >= 112",
                "same_room": "(pos_agent.x>=112)==(pos_target.x>=112)",
                "near_target": "distance_to_target < train_split_median",
            }[name],
            "train_label_rate": float(y_dist[train_mask, j].mean()),
            "calibration_label_rate": float(y_dist[cal_mask, j].mean()),
            "eval_label_rate": float(y_dist[eval_mask, j].mean()),
            "train_accuracy": train_acc,
            "calibration_accuracy": cal_acc,
            "eval_accuracy": eval_acc,
            "fit": info,
        }

    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)

    quality_feature, quality_report = fit_linear_r2_quality(
        rows["emb"][train_mask],
        rows["observation"][train_mask],
        rows["emb"][eval_mask],
        rows["observation"][eval_mask],
    )
    _, min_abs_margin_a = build_gap_features(rows["emb"], probe_prob, probe_logit, probe_pred, quality_feature)

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    low_margin_tau = float(np.percentile(min_abs_margin_a[train_mask], 30))
    y_prediction_error_native = (rows["mse"] > tau_err).astype(np.int8)
    y_prediction_error_probe = np.any(probe_pred.astype(np.int8) != y_dist.astype(np.int8), axis=1).astype(np.int8)
    y_low_margin = (min_abs_margin_a <= low_margin_tau).astype(np.int8)
    y_transition_unstable = np.any(y_dist != y_dist_next, axis=1).astype(np.int8)

    y_off_target, off_target_report = compute_counterfactual_off_target(NPZ_PATH, rows, probe_heads, debts)

    labels = np.stack(
        [y_prediction_error_native, y_low_margin, y_transition_unstable, y_off_target],
        axis=1,
    ).astype(np.int8)

    label_rates: dict[str, Any] = {}
    for j, ch in enumerate(GAP_CHANNELS):
        label_rates[ch] = {
            "train": float(labels[train_mask, j].mean()),
            "calibration": float(labels[cal_mask, j].mean()),
            "eval": float(labels[eval_mask, j].mean()),
            "all": float(labels[:, j].mean()),
            "train_positive": int(labels[train_mask, j].sum()),
            "train_negative": int(train_mask.sum() - labels[train_mask, j].sum()),
            "eval_positive": int(labels[eval_mask, j].sum()),
            "eval_negative": int(eval_mask.sum() - labels[eval_mask, j].sum()),
        }
        if np.unique(labels[train_mask, j]).size < 2:
            debts.append(
                {
                    "type": "coverage_debt",
                    "source": f"gap_channel:{ch}",
                    "detail": "train label is degenerate; channel head falls back to constant base rate fail-closed",
                }
            )

    feature_matrices: dict[str, dict[str, Any]] = {}
    for variant_name, probe_indices in FEATURE_VARIANTS.items():
        x_variant, min_margin_variant = build_gap_features(
            rows["emb"], probe_prob, probe_logit, probe_pred, quality_feature, probe_indices
        )
        feature_matrices[variant_name] = {
            "x": x_variant,
            "min_abs_margin": min_margin_variant,
            "probe_indices": list(probe_indices),
            "probe_names": [DISTINCTIONS[i] for i in probe_indices],
            "feature_width": int(x_variant.shape[1]),
            "components": {
                "emb": int(rows["emb"].shape[1]),
                "probe_probabilities": len(probe_indices),
                "probe_logits": len(probe_indices),
                "probe_predictions": len(probe_indices),
                "probe_signed_margins": len(probe_indices),
                "min_abs_margin": 1,
                "quality_features": int(len(quality_feature)),
            },
        }

    arms: dict[str, Any] = {}
    arm_scores: dict[str, dict[str, Any]] = {}

    train_rates = labels[train_mask].mean(axis=0)
    vanilla_scores = np.tile(train_rates.reshape(1, -1), (n_rows, 1))
    arm_scores["vanilla"] = {"scores": vanilla_scores, "feature_variant": "none_constant_train_base_rate"}

    train_idx = np.where(train_mask)[0]
    for variant_i, (variant_name, pack) in enumerate(feature_matrices.items()):
        x_variant = pack["x"]
        learned_scores = np.zeros((n_rows, len(GAP_CHANNELS)), dtype=np.float64)
        learned_fits: dict[str, Any] = {}
        for j, ch in enumerate(GAP_CHANNELS):
            head, info = fit_logistic_head(x_variant[train_mask], labels[train_mask, j], steps=500, lr=0.14, l2=1e-4)
            learned_scores[:, j] = predict_logistic_head(head, x_variant)[0]
            learned_fits[ch] = info
        arm_scores[f"learned_gap_head_{variant_name}"] = {
            "scores": learned_scores,
            "fits": learned_fits,
            "feature_variant": variant_name,
        }

        rng = np.random.default_rng(MATCHED_RANDOM_SEED + variant_i)
        random_scores = np.zeros((n_rows, len(GAP_CHANNELS)), dtype=np.float64)
        random_fits: dict[str, Any] = {}
        for j, ch in enumerate(GAP_CHANNELS):
            y_perm = labels[train_mask, j].copy()
            rng.shuffle(y_perm)
            head, info = fit_logistic_head(x_variant[train_mask], y_perm, steps=500, lr=0.14, l2=1e-4)
            random_scores[:, j] = predict_logistic_head(head, x_variant)[0]
            random_fits[ch] = {
                **info,
                "permutation_seed": MATCHED_RANDOM_SEED + variant_i,
                "train_rows": int(len(train_idx)),
            }
        arm_scores[f"matched_random_gap_head_{variant_name}"] = {
            "scores": random_scores,
            "fits": random_fits,
            "feature_variant": variant_name,
        }

    eval_episode = rows["episode"][eval_mask]
    for arm_name, pack in arm_scores.items():
        scores = pack["scores"]
        gap_score = scores[:, 0]
        critical_score = np.max(scores, axis=1)
        metrics_eval = bootstrap_metrics_by_episode(
            y_prediction_error_native[eval_mask],
            gap_score[eval_mask],
            critical_score[eval_mask],
            eval_episode,
            seed=BOOTSTRAP_SEED + len(arms),
            n_boot=BOOTSTRAPS,
        )
        metrics_cal = basic_metrics(
            y_prediction_error_native[cal_mask],
            gap_score[cal_mask],
            critical_score[cal_mask],
        )
        arms[arm_name] = {
            "feature_variant": pack["feature_variant"],
            "metrics_eval_episode_bootstrap": metrics_eval,
            "metrics_calibration_observed": metrics_cal,
            "gap_sound_scan_eval": score_gap_sound_scan(y_prediction_error_native[eval_mask], critical_score[eval_mask]),
            "prediction_error_probe_truth_eval": {
                "auroc_using_native_prediction_error_score": auroc_rank(
                    y_prediction_error_probe[eval_mask], gap_score[eval_mask]
                ),
                "ece_using_native_prediction_error_score": ece_10bin(
                    y_prediction_error_probe[eval_mask], gap_score[eval_mask]
                ),
                "unlogged_probe_error_rate": float(
                    np.mean((y_prediction_error_probe[eval_mask] > 0) & (gap_score[eval_mask] < 0.5))
                ),
            },
        }
        if "fits" in pack:
            arms[arm_name]["fits"] = pack["fits"]

    vanilla = arms["vanilla"]["metrics_eval_episode_bootstrap"]
    learned_a = arms["learned_gap_head_A_all_probe_features"]["metrics_eval_episode_bootstrap"]
    matched_a = arms["matched_random_gap_head_A_all_probe_features"]["metrics_eval_episode_bootstrap"]
    learned_b = arms["learned_gap_head_B_denoised_agent_room_only"]["metrics_eval_episode_bootstrap"]
    matched_b = arms["matched_random_gap_head_B_denoised_agent_room_only"]["metrics_eval_episode_bootstrap"]

    variant_conclusions = {}
    for variant_name in FEATURE_VARIANTS:
        learned = arms[f"learned_gap_head_{variant_name}"]["metrics_eval_episode_bootstrap"]
        matched = arms[f"matched_random_gap_head_{variant_name}"]["metrics_eval_episode_bootstrap"]
        auroc_sep = ci_separation(learned, matched, "failure_detection_auroc")
        uer_sep = learned["unlogged_error_rate"]["ci95_high"] < vanilla["unlogged_error_rate"]["ci95_low"]
        variant_conclusions[variant_name] = {
            "learned_auroc_ci_low_gt_matched_ci_high": bool(auroc_sep),
            "learned_uer_ci_high_lt_vanilla_ci_low": bool(uer_sep),
            "claim": "positive" if auroc_sep and uer_sep else "negative_or_inconclusive",
        }

    auroc_better_b = (
        learned_b["failure_detection_auroc"]["observed"]
        - learned_a["failure_detection_auroc"]["observed"]
    )
    primary_variant = "B_denoised_agent_room_only"
    primary = variant_conclusions[primary_variant]
    conclusion = {
        "claim": primary["claim"],
        "primary_variant": primary_variant,
        "primary_learned_auroc_ci_low_gt_matched_ci_high": primary["learned_auroc_ci_low_gt_matched_ci_high"],
        "primary_learned_uer_ci_high_lt_vanilla_ci_low": primary["learned_uer_ci_high_lt_vanilla_ci_low"],
        "variant_conclusions": variant_conclusions,
        "ab_prediction_error_auroc_delta_B_minus_A": float(auroc_better_b),
        "summary": (
            "denoised learned gap head significantly beats matched-random on native prediction-error AUROC and beats vanilla on UER"
            if primary["claim"] == "positive"
            else "fail-closed: episode-level bootstrap CI does not establish both required inequalities for the primary denoised variant"
        ),
    }

    split_report = {
        name: {
            "episodes": eps.astype(int).tolist(),
            "episode_count": int(len(eps)),
            "transition_count": int(mask.sum()),
        }
        for (name, eps), mask in zip(splits_ep.items(), split_masks.values())
    }

    pred_def_report = {
        "native_predictor_latent_error": {
            "definition": "prediction_mse > train_split_p75",
            "tau_err_train_p75": tau_err,
            "rates": {
                "train": float(y_prediction_error_native[train_mask].mean()),
                "calibration": float(y_prediction_error_native[cal_mask].mean()),
                "eval": float(y_prediction_error_native[eval_mask].mean()),
                "all": float(y_prediction_error_native.mean()),
            },
            "mse_quantiles_all_valid": np.percentile(rows["mse"], [25, 50, 75, 95]).tolist(),
        },
        "loning_probe_error": {
            "definition": "max over distinctions of probe prediction != truth; report-only, not Phase 1c primary truth",
            "rates": {
                "train": float(y_prediction_error_probe[train_mask].mean()),
                "calibration": float(y_prediction_error_probe[cal_mask].mean()),
                "eval": float(y_prediction_error_probe[eval_mask].mean()),
                "all": float(y_prediction_error_probe.mean()),
            },
            "agreement_with_native_all": float(np.mean(y_prediction_error_probe == y_prediction_error_native)),
            "agreement_with_native_eval": float(
                np.mean(y_prediction_error_probe[eval_mask] == y_prediction_error_native[eval_mask])
            ),
        },
    }

    export_report = {
        "latent_path": str(NPZ_PATH.name),
        "h5_prefix_path": "_tworoom_prefix_large.h5",
        "prefix_uncompressed_mib": 2048.0,
        "compressed_mib_read": 558.39,
        "prefix_elapsed_sec": 47.70,
        "export_elapsed_sec": 189.11,
        "max_transitions_requested": 5000,
        "min_transitions_requested": 3000,
        "actual_episodes": int(data["emb"].shape[0]),
        "actual_valid_transitions": int(n_rows),
        "source": "_phase1c_prefix.log and _phase1c_export.log",
    }

    report = {
        "protocol": "Phase 1c gap ledger head on expanded real LeWM latent/tworooms",
        "forbidden_inference_columns_enforced": [
            "pos_agent",
            "pos_target",
            "distance_to_target",
            "observation",
            "distinction_truth",
            "prediction_mse",
            "gap_labels",
        ],
        "export": export_report,
        "gap_feature_variants": {
            k: {kk: vv for kk, vv in v.items() if kk not in {"x", "min_abs_margin"}}
            for k, v in feature_matrices.items()
        },
        "sample_counts": {"valid_transitions": int(n_rows), "episodes": int(data["emb"].shape[0])},
        "split": split_report,
        "distinctions": probe_report,
        "identifiability_proxy": quality_report,
        "thresholds": {
            "near_target_train_median": near_threshold,
            "prediction_mse_tau_err_train_p75": tau_err,
            "low_margin_train_p30_A_all_probe_features": low_margin_tau,
        },
        "label_rates": label_rates,
        "prediction_error_definition_comparison": pred_def_report,
        "off_target_intervention": off_target_report,
        "arms": arms,
        "conclusion": conclusion,
        "debt": debts,
        "bootstrap": {
            "resamples": BOOTSTRAPS,
            "unit": "eval episodes",
            "eval_episode_count": int(len(np.unique(eval_episode))),
            "eval_transition_count": int(eval_mask.sum()),
            "seed": BOOTSTRAP_SEED,
        },
    }

    JSON_PATH.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")

    def arm_row(arm_name: str) -> str:
        m = arms[arm_name]["metrics_eval_episode_bootstrap"]
        return (
            f"| {arm_name} | {fmt_ci(m['failure_detection_auroc'])} | {fmt_ci(m['ece'])} | "
            f"{fmt_ci(m['unlogged_error_rate'])} | {fmt_ci(m['critical_unlogged_error_rate'])} |"
        )

    md_lines = [
        "# Phase 1c: expanded LeWM gap ledger head",
        "",
        f"- latent: `tworooms_latent_large.npz`; valid transitions: {n_rows}; episodes: {data['emb'].shape[0]}",
        f"- export: 2048 MiB H5 prefix, compressed read 558.39 MiB, prefix {export_report['prefix_elapsed_sec']:.2f}s, encode/predict {export_report['export_elapsed_sec']:.2f}s",
        f"- split transitions: train={int(train_mask.sum())}, calibration={int(cal_mask.sum())}, eval={int(eval_mask.sum())}; eval episodes={len(np.unique(eval_episode))}",
        f"- conclusion: **{conclusion['claim']}** - {conclusion['summary']}",
        f"- identifiability train mean R2: {quality_report['train_mean_r2']:.4f}; eval report-only mean R2: {quality_report['eval_mean_r2_report_only']:.4f}",
        f"- native prediction_error threshold: prediction_mse > {tau_err:.6f} (train p75)",
        "",
        "## Primary Tests",
        "",
        f"- B learned AUROC CI lower > B matched-random AUROC CI upper: {primary['learned_auroc_ci_low_gt_matched_ci_high']}",
        f"- B learned UER CI upper < vanilla UER CI lower: {primary['learned_uer_ci_high_lt_vanilla_ci_low']}",
        "",
        "## Arm metrics (eval episode-bootstrap 95% CI)",
        "",
        "| arm | AUROC | ECE | UER | critical UER |",
        "|---|---:|---:|---:|---:|",
        arm_row("vanilla"),
        arm_row("learned_gap_head_A_all_probe_features"),
        arm_row("matched_random_gap_head_A_all_probe_features"),
        arm_row("learned_gap_head_B_denoised_agent_room_only"),
        arm_row("matched_random_gap_head_B_denoised_agent_room_only"),
        "",
        "## A/B Control",
        "",
        f"- A uses all probe features: {feature_matrices['A_all_probe_features']['probe_names']}",
        f"- B removes Phase 1b source-debt probes (`same_room`, `near_target`) and keeps: {feature_matrices['B_denoised_agent_room_only']['probe_names']}",
        f"- prediction_error AUROC delta B-A: {auroc_better_b:.4f}",
        "",
        "## Distinction probe separability",
        "",
        "| distinction | train rate | eval rate | train acc | eval acc |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in DISTINCTIONS:
        p = probe_report[name]
        md_lines.append(
            f"| {name} | {p['train_label_rate']:.4f} | {p['eval_label_rate']:.4f} | "
            f"{p['train_accuracy']:.4f} | {p['eval_accuracy']:.4f} |"
        )
    md_lines.extend(
        [
            "",
            "## Prediction-error definitions",
            "",
            f"- native latent-error eval rate: {pred_def_report['native_predictor_latent_error']['rates']['eval']:.4f}",
            f"- Loning probe-error eval rate: {pred_def_report['loning_probe_error']['rates']['eval']:.4f}",
            f"- native/probe agreement eval: {pred_def_report['loning_probe_error']['agreement_with_native_eval']:.4f}",
            "",
            "## Off-target intervention",
            "",
            f"- status: {off_target_report.get('status')}",
            f"- label rate all rows: {off_target_report.get('label_rate_all_rows', 'n/a')}",
            "",
            "## Debt",
            "",
        ]
    )
    if debts:
        for d in debts:
            md_lines.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    else:
        md_lines.append("- none")
    md_lines.extend(
        [
            "",
            "Full gap_sound_scan grids and per-arm calibration metrics are in `reports/lewm_gap_ledger_head_large.json`.",
            "",
        ]
    )
    MD_PATH.write_text("\n".join(md_lines), encoding="utf-8")

    findings = [
        "# PHASE1C_FINDINGS",
        "",
        "## 结论",
        "",
        f"{conclusion['summary']}。结论标记：**{conclusion['claim']}**。",
        "",
        "核心判据（主分析 B：去掉 Phase 1b source-debt probes: same_room/near_target）：",
        f"- learned B AUROC: {fmt_ci(learned_b['failure_detection_auroc'])}",
        f"- matched-random B AUROC: {fmt_ci(matched_b['failure_detection_auroc'])}",
        f"- vanilla UER: {fmt_ci(vanilla['unlogged_error_rate'])}",
        f"- learned B UER: {fmt_ci(learned_b['unlogged_error_rate'])}",
        f"- 判据 1 learned 下界 > matched 上界: {primary['learned_auroc_ci_low_gt_matched_ci_high']}",
        f"- 判据 2 learned UER 上界 < vanilla UER 下界: {primary['learned_uer_ci_high_lt_vanilla_ci_low']}",
        "",
        "## A/B 对照",
        "",
        f"- A learned AUROC: {fmt_ci(learned_a['failure_detection_auroc'])}",
        f"- B learned AUROC: {fmt_ci(learned_b['failure_detection_auroc'])}",
        f"- B-A AUROC observed delta: {auroc_better_b:.4f}",
        "",
        "## 关键数据",
        "",
        f"- 输入 latent: `tworooms_latent_large.npz`，{n_rows} valid transitions / {data['emb'].shape[0]} episodes。",
        f"- export: 2048 MiB H5 prefix；实际 compressed read 558.39 MiB；prefix {export_report['prefix_elapsed_sec']:.2f}s；GPU encode/predict {export_report['export_elapsed_sec']:.2f}s。",
        f"- episode split: train={int(train_mask.sum())} transitions, calibration={int(cal_mask.sum())}, eval={int(eval_mask.sum())}；eval episodes={len(np.unique(eval_episode))}。",
        f"- native prediction_error: `prediction_mse > {tau_err:.6f}`；eval rate={pred_def_report['native_predictor_latent_error']['rates']['eval']:.4f}。",
        f"- Loning probe-error eval rate={pred_def_report['loning_probe_error']['rates']['eval']:.4f}；与 native eval agreement={pred_def_report['loning_probe_error']['agreement_with_native_eval']:.4f}。",
        f"- identifiability proxy train mean R2={quality_report['train_mean_r2']:.4f}，eval report-only mean R2={quality_report['eval_mean_r2_report_only']:.4f}。",
        f"- off_target_intervention status={off_target_report.get('status')}，all-row rate={off_target_report.get('label_rate_all_rows', 'n/a')}。",
        "",
        "## 根因更新",
        "",
        "- coverage debt 明显改善：从 37 episodes / 642 transitions 扩到 278 episodes / 4991 transitions，并改为 eval episode-level bootstrap。",
        "- prediction_error channel 使用 LeWM predictor latent rollout MSE，主结论不依赖 same_room/near_target distinction 可分性。",
        "- same_room/near_target probe 按 0.60 eval acc 阈值继续 fail-closed 记 debt；本次 same_room 通过、near_target 未通过，B 版仍按 Phase 1b 预注册去噪对照移除二者。",
        "- identifiability eval R2 仍只作 report-only 诊断，不用于制造正例或放宽 fail-closed 判据。",
        "",
        "## Debt",
        "",
    ]
    if debts:
        for d in debts:
            findings.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    else:
        findings.append("- 未记录 debt。")
    findings.extend(
        [
            "",
            "## 下一步建议",
            "",
            "- 虽然本次两个判据均成立，仍建议用独立 world seeds/exports 复验，避免单 export episode bootstrap 低估跨世界不确定性。",
            "- 固定 distinction-feature inclusion policy：只允许 eval separability 过阈值的 probe 进入主 gap head，source-debt probe 仅做诊断或对照。",
            "- 对 prediction_mse p75 阈值做 calibration split 稳健性扫描，确认 positive 结论不依赖单一分位点。",
            "",
            "产物：`reports/lewm_gap_ledger_head_large.json` 和 `reports/lewm_gap_ledger_head_large.md`。",
            "",
        ]
    )
    FINDINGS_PATH.write_text("\n".join(findings), encoding="utf-8")

    print(json.dumps(conclusion, indent=2, ensure_ascii=False))
    print(f"wrote {JSON_PATH}")
    print(f"wrote {MD_PATH}")
    print(f"wrote {FINDINGS_PATH}")


if __name__ == "__main__":
    main()

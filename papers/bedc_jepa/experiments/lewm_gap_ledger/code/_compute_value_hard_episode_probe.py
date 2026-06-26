from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_model as cvm
import _compute_value_policy as cvp


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_LABELS = cvm.DEFAULT_LABELS
DEFAULT_LATENTS = cvm.DEFAULT_LATENTS
DEFAULT_DECOMP = REPORT_DIR / "compute_value_episode_decomposition.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_hard_episode_probe.json"
DEFAULT_MD = REPORT_DIR / "compute_value_hard_episode_probe.md"
DEFAULT_NPZ = REPORT_DIR / "compute_value_hard_episode_probe_predictions.npz"


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
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def sigmoid(x: np.ndarray) -> np.ndarray:
    return 1.0 / (1.0 + np.exp(-np.clip(x, -60.0, 60.0)))


def episode_groups(payload: dict[str, np.ndarray]) -> list[np.ndarray]:
    return cvm.episode_groups(payload["episode"].astype(np.int64))


def oracle_episode_gain(payload: dict[str, np.ndarray]) -> dict[int, float]:
    oracle_score = cvp.rank_target(payload)
    chosen, _ = cvm.balanced_depth_choice(payload["episode"], cvp.scalar_to_predicted_mv(oracle_score))
    chosen_error = payload["option_error"][np.arange(len(chosen)), chosen]
    chosen_steps = cvm.OPTION_DEPTHS[chosen].astype(np.float64)
    uniform_error = payload["uniform_error"]
    uniform_steps = np.full(len(chosen), cvm.UNIFORM_DEPTH, dtype=np.float64)
    gains: dict[int, float] = {}
    for idxs in episode_groups(payload):
        ep = int(payload["episode"][idxs[0]])
        chosen_rate = float(np.sum(chosen_error[idxs]) / np.sum(chosen_steps[idxs]))
        uniform_rate = float(np.sum(uniform_error[idxs]) / np.sum(uniform_steps[idxs]))
        gains[ep] = uniform_rate - chosen_rate
    return gains


def load_decomposition(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def hard_episode_set_from_decomposition(path: Path, *, top_k: int) -> set[int]:
    data = load_decomposition(path)
    episode = data["episode"].astype(np.int64)
    missed = data["missed_oracle"].astype(np.float64)
    order = np.argsort(missed)[::-1]
    return {int(ep) for ep in episode[order[:top_k]]}


def make_episode_dataset(payload: dict[str, np.ndarray], hard_episodes: set[int] | None, *, gain_quantile: float) -> dict[str, np.ndarray]:
    groups = episode_groups(payload)
    gains = oracle_episode_gain(payload)
    if hard_episodes is None:
        values = np.asarray(list(gains.values()), dtype=np.float64)
        threshold = float(np.quantile(values, gain_quantile))
        hard_episodes = {ep for ep, gain in gains.items() if gain >= threshold}
    features = []
    labels = []
    episodes = []
    gains_out = []
    for idxs in groups:
        ep = int(payload["episode"][idxs[0]])
        x = payload["x"][idxs].astype(np.float64)
        mean = np.mean(x, axis=0)
        std = np.std(x, axis=0)
        q90 = np.quantile(x, 0.90, axis=0)
        features.append(np.concatenate([mean, std, q90], axis=0))
        labels.append(1.0 if ep in hard_episodes else 0.0)
        episodes.append(ep)
        gains_out.append(float(gains[ep]))
    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "x": np.asarray(features, dtype=np.float64),
        "y": np.asarray(labels, dtype=np.float64),
        "oracle_gain": np.asarray(gains_out, dtype=np.float64),
    }


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x, axis=0)
    scale = np.std(x, axis=0)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def standardize(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return (x - mean) / scale


def train_logistic(x: np.ndarray, y: np.ndarray, *, seed: int, steps: int, lr: float, l2: float) -> tuple[np.ndarray, float, list[float]]:
    rng = np.random.default_rng(seed)
    w = rng.normal(0.0, 0.01, size=x.shape[1])
    b = 0.0
    pos = float(np.sum(y > 0.5))
    neg = float(len(y) - pos)
    pos_weight = neg / max(pos, 1.0)
    history = []
    for _ in range(steps):
        logits = x @ w + b
        p = sigmoid(logits)
        weights = np.where(y > 0.5, pos_weight, 1.0)
        grad = (p - y) * weights
        w -= lr * (x.T @ grad / len(y) + l2 * w)
        b -= lr * float(np.mean(grad))
        if len(history) < 5 or (_ + 1) == steps:
            loss = -np.mean(weights * (y * np.log(p + 1.0e-9) + (1.0 - y) * np.log(1.0 - p + 1.0e-9)))
            history.append(clean_float(float(loss)))
    return w, clean_float(b), history


def rankdata(values: np.ndarray) -> np.ndarray:
    return cvm.rankdata(values.astype(np.float64))


def auroc(y: np.ndarray, score: np.ndarray) -> float:
    y = y.astype(bool)
    if np.sum(y) == 0 or np.sum(~y) == 0:
        return 0.5
    ranks = rankdata(score)
    n_pos = float(np.sum(y))
    n_neg = float(np.sum(~y))
    rank_sum = float(np.sum(ranks[y]))
    return clean_float((rank_sum - n_pos * (n_pos - 1.0) / 2.0) / (n_pos * n_neg))


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    return cvm.spearman(x.astype(np.float64), y.astype(np.float64))


def summarize_scores(dataset: dict[str, np.ndarray], score: np.ndarray, hard_eval: set[int] | None = None) -> dict[str, Any]:
    y = dataset["y"].astype(np.float64)
    hard_mask = y > 0.5
    out = {
        "episodes": int(len(y)),
        "positive": int(np.sum(hard_mask)),
        "auroc": auroc(y, score),
        "spearman_with_oracle_gain": spearman(score, dataset["oracle_gain"]),
        "mean_score_positive": clean_float(float(np.mean(score[hard_mask])) if np.any(hard_mask) else 0.0),
        "mean_score_negative": clean_float(float(np.mean(score[~hard_mask])) if np.any(~hard_mask) else 0.0),
    }
    if hard_eval is not None:
        top_mask = np.asarray([int(ep) in hard_eval for ep in dataset["episode"]], dtype=bool)
        out["top_missed_episode_mean_score"] = clean_float(float(np.mean(score[top_mask])) if np.any(top_mask) else 0.0)
        out["non_top_missed_episode_mean_score"] = clean_float(float(np.mean(score[~top_mask])) if np.any(~top_mask) else 0.0)
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    eval_row = report["eval"]
    lines = [
        "# Compute-Value Hard-Episode Probe",
        "",
        f"- train positives: `{report['train']['positive']}` / `{report['train']['episodes']}`",
        f"- calibration AUROC: `{report['calibration']['auroc']:.9g}`",
        f"- eval AUROC against top missed episodes: `{eval_row['auroc']:.9g}`",
        f"- eval Spearman with oracle gain: `{eval_row['spearman_with_oracle_gain']:.9g}`",
        f"- top missed mean score: `{eval_row['top_missed_episode_mean_score']:.9g}`",
        f"- non-top missed mean score: `{eval_row['non_top_missed_episode_mean_score']:.9g}`",
        "",
        "The probe uses train-split oracle-gain tail labels for fitting and calibration labels for model selection.",
        "Eval top-missed labels come from the already recorded episode decomposition and are used only after scores are produced.",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Probe whether hard allocation episodes are readable from rollout features")
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(DEFAULT_LATENTS))
    parser.add_argument("--decomposition", default=str(DEFAULT_DECOMP))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    parser.add_argument("--gain-quantile", type=float, default=0.80)
    parser.add_argument("--eval-top-k", type=int, default=8)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--lr", type=float, default=0.02)
    parser.add_argument("--l2", type=float, default=1.0e-3)
    args = parser.parse_args()

    labels = cvm.load_npz(cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS]))
    latents = cvm.load_npz(cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS]))
    train_payload = cvm.split_payload(labels, latents, "train")
    cal_payload = cvm.split_payload(labels, latents, "calibration")
    eval_payload = cvm.split_payload(labels, latents, "eval")
    hard_eval = hard_episode_set_from_decomposition(Path(args.decomposition), top_k=int(args.eval_top_k))
    train_data = make_episode_dataset(train_payload, None, gain_quantile=float(args.gain_quantile))
    cal_data = make_episode_dataset(cal_payload, None, gain_quantile=float(args.gain_quantile))
    eval_data = make_episode_dataset(eval_payload, hard_eval, gain_quantile=float(args.gain_quantile))
    mean, scale = fit_standardizer(train_data["x"])
    x_train = standardize(train_data["x"], mean, scale)
    x_cal = standardize(cal_data["x"], mean, scale)
    x_eval = standardize(eval_data["x"], mean, scale)
    w, b, history = train_logistic(
        x_train,
        train_data["y"],
        seed=int(args.seed),
        steps=int(args.steps),
        lr=float(args.lr),
        l2=float(args.l2),
    )
    train_score = x_train @ w + b
    cal_score = x_cal @ w + b
    eval_score = x_eval @ w + b
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_hard_episode_probe",
        "inputs": {"decomposition": str(args.decomposition)},
        "settings": {
            "gain_quantile": float(args.gain_quantile),
            "eval_top_k": int(args.eval_top_k),
            "steps": int(args.steps),
            "lr": float(args.lr),
            "l2": float(args.l2),
        },
        "train": summarize_scores(train_data, train_score),
        "calibration": summarize_scores(cal_data, cal_score),
        "eval": summarize_scores(eval_data, eval_score, hard_eval=hard_eval),
        "eval_top_missed_episodes": sorted(int(ep) for ep in hard_eval),
        "training_loss_trace": history,
        "leakage_attestation": {
            "train_labels": "train split oracle-gain tail labels only",
            "calibration_labels": "calibration split oracle-gain tail labels only",
            "eval_labels": "top missed episodes from precomputed eval decomposition, used only after scores are produced",
            "model": "linear logistic probe over episode-aggregated rollout features",
            "slurm_or_ssh": "not used",
        },
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(
        args.npz,
        train_episode=train_data["episode"].astype(np.int64),
        train_score=train_score.astype(np.float64),
        train_label=train_data["y"].astype(np.float64),
        calibration_episode=cal_data["episode"].astype(np.int64),
        calibration_score=cal_score.astype(np.float64),
        calibration_label=cal_data["y"].astype(np.float64),
        eval_episode=eval_data["episode"].astype(np.int64),
        eval_score=eval_score.astype(np.float64),
        eval_label=eval_data["y"].astype(np.float64),
        eval_oracle_gain=eval_data["oracle_gain"].astype(np.float64),
    )
    print(json.dumps(clean_json({"calibration": report["calibration"], "eval": report["eval"]}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

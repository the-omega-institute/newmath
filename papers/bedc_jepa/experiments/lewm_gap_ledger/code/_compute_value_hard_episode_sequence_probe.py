from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_hard_episode_probe as hep
import _compute_value_model as cvm
import _compute_value_policy as cvp


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_DECOMP = REPORT_DIR / "compute_value_episode_decomposition.npz"
DEFAULT_POLICY = REPORT_DIR / "compute_value_policy_stability_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_hard_episode_sequence_probe.json"
DEFAULT_MD = REPORT_DIR / "compute_value_hard_episode_sequence_probe.md"
DEFAULT_NPZ = REPORT_DIR / "compute_value_hard_episode_sequence_probe_predictions.npz"


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


def load_policy_scores(path: Path) -> dict[tuple[int, int], float]:
    with np.load(path, allow_pickle=False) as data:
        anchors = data["anchor_ep_t0"].astype(np.int64)
        if "policy_score" in data.files:
            score = data["policy_score"].astype(np.float64)
        else:
            predicted = data["predicted_mv"].astype(np.float64)
            low = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
            high = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
            score = predicted[:, high] - predicted[:, low]
    return {(int(ep), int(t0)): float(s) for (ep, t0), s in zip(anchors, score)}


def attach_policy_score(payload: dict[str, np.ndarray], score_map: dict[tuple[int, int], float] | None) -> np.ndarray:
    if score_map is None:
        return cvp.rank_target(payload)
    out = np.zeros(len(payload["episode"]), dtype=np.float64)
    for i, (ep, t0) in enumerate(payload["anchor_ep_t0"]):
        out[i] = score_map.get((int(ep), int(t0)), 0.0)
    return out


def episode_features(
    payload: dict[str, np.ndarray],
    hard_episodes: set[int] | None,
    *,
    gain_quantile: float,
    score_map: dict[tuple[int, int], float] | None,
) -> dict[str, np.ndarray]:
    groups = cvm.episode_groups(payload["episode"].astype(np.int64))
    gains = hep.oracle_episode_gain(payload)
    if hard_episodes is None:
        values = np.asarray(list(gains.values()), dtype=np.float64)
        threshold = float(np.quantile(values, gain_quantile))
        hard_episodes = {ep for ep, gain in gains.items() if gain >= threshold}
    low = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    true_score = cvp.rank_target(payload)
    policy_score = attach_policy_score(payload, score_map)
    features = []
    labels = []
    episodes = []
    gains_out = []
    for idxs in groups:
        ep = int(payload["episode"][idxs[0]])
        order = idxs[np.argsort(payload["t0"][idxs], kind="mergesort")]
        x = payload["x"][order].astype(np.float64)
        true_s = true_score[order].astype(np.float64)
        pol_s = policy_score[order].astype(np.float64)
        gap = true_s - pol_s
        option_gap = payload["option_error"][order, high] / float(cvm.OPTION_DEPTHS[high]) - payload["option_error"][order, low] / float(cvm.OPTION_DEPTHS[low])
        blocks = [
            np.mean(x, axis=0),
            np.std(x, axis=0),
            np.quantile(x, 0.10, axis=0),
            np.quantile(x, 0.50, axis=0),
            np.quantile(x, 0.90, axis=0),
        ]
        if len(order) >= 2:
            dx = np.diff(x, axis=0)
            blocks.extend([np.mean(np.abs(dx), axis=0), np.quantile(np.abs(dx), 0.90, axis=0)])
        else:
            blocks.extend([np.zeros(x.shape[1]), np.zeros(x.shape[1])])
        score_stats = []
        for arr in (true_s, pol_s, gap, option_gap):
            score_stats.extend(
                [
                    float(np.mean(arr)),
                    float(np.std(arr)),
                    float(np.min(arr)),
                    float(np.median(arr)),
                    float(np.max(arr)),
                    float(np.quantile(arr, 0.90)),
                ]
            )
        features.append(np.concatenate([*blocks, np.asarray(score_stats, dtype=np.float64)], axis=0))
        labels.append(1.0 if ep in hard_episodes else 0.0)
        episodes.append(ep)
        gains_out.append(float(gains[ep]))
    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "x": np.asarray(features, dtype=np.float64),
        "y": np.asarray(labels, dtype=np.float64),
        "oracle_gain": np.asarray(gains_out, dtype=np.float64),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Hard-Episode Sequence Probe",
        "",
        f"- train positives: `{report['train']['positive']}` / `{report['train']['episodes']}`",
        f"- calibration AUROC: `{report['calibration']['auroc']:.9g}`",
        f"- eval AUROC against top missed episodes: `{report['eval']['auroc']:.9g}`",
        f"- eval Spearman with oracle gain: `{report['eval']['spearman_with_oracle_gain']:.9g}`",
        f"- top missed mean score: `{report['eval']['top_missed_episode_mean_score']:.9g}`",
        f"- non-top missed mean score: `{report['eval']['non_top_missed_episode_mean_score']:.9g}`",
        "",
        "This probe augments aggregate rollout features with per-episode quantiles, adjacent-change summaries, and score-distribution summaries.",
        "",
    ]
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Probe hard episodes with sequence and score-distribution features")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--decomposition", default=str(DEFAULT_DECOMP))
    parser.add_argument("--policy", default=str(DEFAULT_POLICY))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    parser.add_argument("--gain-quantile", type=float, default=0.80)
    parser.add_argument("--eval-top-k", type=int, default=8)
    parser.add_argument("--seed", type=int, default=23)
    parser.add_argument("--steps", type=int, default=5000)
    parser.add_argument("--lr", type=float, default=0.015)
    parser.add_argument("--l2", type=float, default=2.0e-3)
    args = parser.parse_args()

    labels = cvm.load_npz(cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS]))
    latents = cvm.load_npz(cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS]))
    train_payload = cvm.split_payload(labels, latents, "train")
    cal_payload = cvm.split_payload(labels, latents, "calibration")
    eval_payload = cvm.split_payload(labels, latents, "eval")
    eval_hard = hep.hard_episode_set_from_decomposition(Path(args.decomposition), top_k=int(args.eval_top_k))
    eval_scores = load_policy_scores(Path(args.policy))
    train_data = episode_features(train_payload, None, gain_quantile=float(args.gain_quantile), score_map=None)
    cal_data = episode_features(cal_payload, None, gain_quantile=float(args.gain_quantile), score_map=None)
    eval_data = episode_features(eval_payload, eval_hard, gain_quantile=float(args.gain_quantile), score_map=eval_scores)
    mean, scale = hep.fit_standardizer(train_data["x"])
    x_train = hep.standardize(train_data["x"], mean, scale)
    x_cal = hep.standardize(cal_data["x"], mean, scale)
    x_eval = hep.standardize(eval_data["x"], mean, scale)
    w, b, history = hep.train_logistic(
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
        "schema_id": "bedc_jepa.compute_value_hard_episode_sequence_probe",
        "inputs": {"decomposition": str(args.decomposition), "policy": str(args.policy)},
        "settings": {
            "gain_quantile": float(args.gain_quantile),
            "eval_top_k": int(args.eval_top_k),
            "steps": int(args.steps),
            "lr": float(args.lr),
            "l2": float(args.l2),
        },
        "feature_view": "episode quantiles plus adjacent-change summaries and score-distribution summaries",
        "train": hep.summarize_scores(train_data, train_score),
        "calibration": hep.summarize_scores(cal_data, cal_score),
        "eval": hep.summarize_scores(eval_data, eval_score, hard_eval=eval_hard),
        "eval_top_missed_episodes": sorted(int(ep) for ep in eval_hard),
        "training_loss_trace": history,
        "leakage_attestation": {
            "train_labels": "train split oracle-gain tail labels only",
            "calibration_labels": "calibration split oracle-gain tail labels only",
            "eval_labels": "top missed episodes from precomputed eval decomposition, used only after scores are produced",
            "policy_scores": "eval policy scores are precomputed predictions and used as features only for the post-hoc eval diagnostic",
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

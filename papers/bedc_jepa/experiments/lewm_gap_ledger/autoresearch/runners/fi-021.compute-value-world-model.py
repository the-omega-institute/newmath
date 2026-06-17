#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_LABELS = REPORT_DIR / "compute_value_labels.npz"

HYPOTHESIS_ID = "fi-021.compute-value-world-model"
METRIC = "allocation_delta"
BOOTSTRAPS = 1000


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def fail_closed(reason: str, *, labels: Path) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_delta", "marginal_value_schema"],
        "reported_claim": (
            "compute-value world-model runner fail-closed: "
            f"{reason}; expected option-level marginal-value labels at {labels}"
        ),
    }


def read_step_vector(arrays: dict[str, np.ndarray], key: str, fallback: np.ndarray) -> np.ndarray:
    if key not in arrays:
        return fallback.astype(np.float64)
    return np.asarray(arrays[key], dtype=np.float64).reshape(-1)


def validate_arrays(arrays: dict[str, np.ndarray]) -> str | None:
    required = ("episode", "option_error", "uniform_error", "predicted_mv")
    missing = [key for key in required if key not in arrays]
    if missing:
        return "missing required arrays " + ",".join(missing)
    episode = np.asarray(arrays["episode"]).reshape(-1)
    option_error = np.asarray(arrays["option_error"], dtype=np.float64)
    uniform_error = np.asarray(arrays["uniform_error"], dtype=np.float64).reshape(-1)
    predicted_mv = np.asarray(arrays["predicted_mv"], dtype=np.float64)
    if option_error.ndim != 2 or predicted_mv.ndim != 2:
        return "option_error and predicted_mv must be rank-2 arrays shaped anchors x options"
    if option_error.shape != predicted_mv.shape:
        return "option_error and predicted_mv shapes differ"
    if len(episode) != option_error.shape[0] or len(uniform_error) != option_error.shape[0]:
        return "episode, uniform_error, and option_error anchor counts differ"
    if option_error.shape[1] < 2:
        return "at least two compute options are required"
    finite = [
        np.isfinite(episode.astype(np.float64)).all(),
        np.isfinite(option_error).all(),
        np.isfinite(uniform_error).all(),
        np.isfinite(predicted_mv).all(),
    ]
    if not all(bool(item) for item in finite):
        return "arrays contain non-finite values"
    if len(np.unique(episode)) < 2:
        return "episode bootstrap requires at least two episodes"
    return None


def rankdata(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values, kind="mergesort")
    ranks = np.empty(len(values), dtype=np.float64)
    sorted_values = values[order]
    i = 0
    while i < len(values):
        j = i + 1
        while j < len(values) and sorted_values[j] == sorted_values[i]:
            j += 1
        ranks[order[i:j]] = 0.5 * (i + j - 1)
        i = j
    return ranks


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return 0.0
    rx = rankdata(np.asarray(x, dtype=np.float64))
    ry = rankdata(np.asarray(y, dtype=np.float64))
    rx = rx - float(rx.mean())
    ry = ry - float(ry.mean())
    denom = math.sqrt(float(np.dot(rx, rx)) * float(np.dot(ry, ry)))
    if denom <= 0:
        return 0.0
    return clean_float(float(np.dot(rx, ry) / denom))


def bootstrap_ci(values: list[float]) -> dict[str, float]:
    arr = np.asarray(values, dtype=np.float64)
    return {
        "low": clean_float(float(np.percentile(arr, 2.5))),
        "high": clean_float(float(np.percentile(arr, 97.5))),
    }


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0] for ep in np.unique(episode)]


def balanced_depth_choice(
    episode: np.ndarray,
    predicted_mv: np.ndarray,
    option_steps: np.ndarray,
    *,
    uniform_step: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    low_candidates = np.where(option_steps < uniform_step)[0]
    mid_candidates = np.where(option_steps == uniform_step)[0]
    high_candidates = np.where(option_steps > uniform_step)[0]
    if len(low_candidates) == 0 or len(mid_candidates) == 0 or len(high_candidates) == 0:
        raise ValueError("balanced policy requires option steps below, equal to, and above uniform step")
    low = int(low_candidates[np.argmin(option_steps[low_candidates])])
    mid = int(mid_candidates[0])
    high = int(high_candidates[np.argmax(option_steps[high_candidates])])
    score = predicted_mv[:, high] - predicted_mv[:, low]
    chosen = np.full(len(episode), mid, dtype=np.int64)
    for idxs in episode_groups(episode):
        ordered = sorted((int(i) for i in idxs), key=lambda i: (float(score[i]), int(i)))
        n = len(ordered)
        half = n // 2
        chosen[np.asarray(ordered[:half], dtype=np.int64)] = low
        chosen[np.asarray(ordered[n - half :], dtype=np.int64)] = high
        if n % 2:
            chosen[ordered[half]] = mid
        selected_steps = option_steps[chosen]
        target = uniform_step * n
        got = float(np.sum(selected_steps[np.asarray(ordered, dtype=np.int64)]))
        if abs(got - target) > 1.0e-9:
            raise RuntimeError("balanced compute-value allocation budget mismatch")
    return chosen, score, np.asarray([low, mid, high], dtype=np.int64)


def paired_per_step_delta(
    episode: np.ndarray,
    chosen_error: np.ndarray,
    chosen_steps: np.ndarray,
    uniform_error: np.ndarray,
    uniform_steps: np.ndarray,
    *,
    seed: int,
) -> tuple[float, dict[str, float], list[float]]:
    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(chosen_error[idx])) for idx in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(chosen_steps[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idx])) for idx in groups], dtype=np.float64)
    observed = clean_float(float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum()))
    rng = np.random.default_rng(seed)
    samples: list[float] = []
    for _ in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        samples.append(
            float(
                selected_ep_error[pick].sum() / selected_ep_steps[pick].sum()
                - uniform_ep_error[pick].sum() / uniform_ep_steps[pick].sum()
            )
        )
    return observed, bootstrap_ci(samples), samples


def evaluate(arrays: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    episode = np.asarray(arrays["episode"]).reshape(-1).astype(np.int64)
    option_error = np.asarray(arrays["option_error"], dtype=np.float64)
    uniform_error = np.asarray(arrays["uniform_error"], dtype=np.float64).reshape(-1)
    predicted_mv = np.asarray(arrays["predicted_mv"], dtype=np.float64)
    option_steps = read_step_vector(arrays, "option_steps", np.ones(option_error.shape[1], dtype=np.float64))
    uniform_steps = read_step_vector(arrays, "uniform_steps", np.ones(option_error.shape[0], dtype=np.float64))
    if len(uniform_steps) == 1:
        uniform_steps = np.full(len(episode), float(uniform_steps[0]), dtype=np.float64)
    if option_steps.shape[0] == option_error.shape[1]:
        true_mv = uniform_error[:, None] / uniform_steps[:, None] - option_error / option_steps[None, :]
    else:
        true_mv = uniform_error[:, None] - option_error
    policy = "argmax_variable_budget"
    chosen: np.ndarray
    rank_score: np.ndarray
    policy_options: list[int] | None = None
    try:
        uniform_step = float(uniform_steps[0])
        if np.all(uniform_steps == uniform_step) and option_steps.shape[0] == option_error.shape[1]:
            chosen, rank_score, selected_options = balanced_depth_choice(
                episode,
                predicted_mv,
                option_steps,
                uniform_step=uniform_step,
            )
            policy = "balanced_depth_episode_budget"
            policy_options = [int(item) for item in selected_options.tolist()]
        else:
            chosen = np.argmax(predicted_mv, axis=1)
            rank_score = predicted_mv[np.arange(option_error.shape[0]), chosen]
    except ValueError:
        chosen = np.argmax(predicted_mv, axis=1)
        rank_score = predicted_mv[np.arange(option_error.shape[0]), chosen]
    chosen_error = option_error[np.arange(option_error.shape[0]), chosen]
    chosen_steps = option_steps[chosen] if option_steps.shape[0] == option_error.shape[1] else np.ones_like(chosen_error)
    observed_delta, delta_ci, _ = paired_per_step_delta(
        episode,
        chosen_error,
        chosen_steps,
        uniform_error,
        uniform_steps,
        seed=seed,
    )
    if policy == "balanced_depth_episode_budget" and policy_options is not None:
        low, _mid, high = policy_options
        true_rank_score = true_mv[:, high] - true_mv[:, low]
    else:
        true_rank_score = true_mv[np.arange(option_error.shape[0]), chosen]
    observed_rho = spearman(rank_score, true_rank_score)

    by_episode = episode_groups(episode)
    rng = np.random.default_rng(seed + 1)
    rhos: list[float] = []
    for _ in range(BOOTSTRAPS):
        sample = rng.integers(0, len(by_episode), size=len(by_episode))
        idx = np.concatenate([by_episode[int(item)] for item in sample])
        rhos.append(spearman(rank_score[idx], true_rank_score[idx]))
    rho_ci = bootstrap_ci(rhos)
    status = "positive" if delta_ci["high"] < 0.0 else ("negative" if delta_ci["low"] >= 0.0 else "unidentifiable")
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": observed_delta},
        "metric": METRIC,
        "metric_value": observed_delta,
        "ci": delta_ci,
        "status": status,
        "measured_scope": ["allocation_delta", "mv_spearman", "marginal_value_schema"],
        "reported_claim": (
            f"compute-value allocation_delta={observed_delta:.9g}, "
            f"95% CI=[{delta_ci['low']:.9g},{delta_ci['high']:.9g}], "
            f"MV Spearman={observed_rho:.9g} "
            f"[{rho_ci['low']:.9g},{rho_ci['high']:.9g}]; "
            f"policy={policy}; failure probability is not used as the allocation target"
        ),
        "diagnostics": {
            "anchors": int(option_error.shape[0]),
            "options": int(option_error.shape[1]),
            "episodes": int(len(np.unique(episode))),
            "policy": policy,
            "policy_options": policy_options,
            "option_steps": [float(item) for item in option_steps.tolist()],
            "uniform_steps_mean": float(np.mean(uniform_steps)),
            "mv_spearman": {
                "observed": observed_rho,
                "low": rho_ci["low"],
                "high": rho_ci["high"],
            },
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate BEDC-native option-conditioned compute-value labels")
    parser.add_argument("--labels", default=str(DEFAULT_LABELS))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    labels = Path(args.labels)
    if not labels.exists():
        payload = fail_closed("missing compute-value label artifact", labels=labels)
    else:
        arrays = load_npz(labels)
        reason = validate_arrays(arrays)
        payload = fail_closed(reason, labels=labels) if reason else evaluate(arrays, seed=int(args.seed))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

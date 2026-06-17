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
DEFAULT_ARTIFACT = REPORT_DIR / "compute_value_structured_assignment_predictions.npz"
HYPOTHESIS_ID = "fi-022.compute-value-structured-assignment"
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


def fail_closed(reason: str, *, artifact: Path) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": METRIC,
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_delta", "structured_exact_budget_assignment"],
        "reported_claim": (
            "structured compute-value assignment runner fail-closed: "
            f"{reason}; expected structured artifact at {artifact}"
        ),
    }


def validate(arrays: dict[str, np.ndarray]) -> str | None:
    required = ("episode", "option_depths", "option_error", "uniform_error", "predicted_option_score")
    missing = [key for key in required if key not in arrays]
    if missing:
        return "missing required arrays " + ",".join(missing)
    episode = np.asarray(arrays["episode"]).reshape(-1)
    depths = np.asarray(arrays["option_depths"]).reshape(-1)
    option_error = np.asarray(arrays["option_error"], dtype=np.float64)
    uniform_error = np.asarray(arrays["uniform_error"], dtype=np.float64).reshape(-1)
    score = np.asarray(arrays["predicted_option_score"], dtype=np.float64)
    if option_error.ndim != 2 or score.ndim != 2:
        return "option_error and predicted_option_score must be rank-2 arrays"
    if option_error.shape != score.shape:
        return "option_error and predicted_option_score shapes differ"
    if len(episode) != option_error.shape[0] or len(uniform_error) != option_error.shape[0]:
        return "episode, uniform_error, and option_error anchor counts differ"
    if len(depths) != option_error.shape[1]:
        return "option_depths length does not match option columns"
    if 3 not in {int(item) for item in depths.tolist()}:
        return "exact-budget runner requires uniform depth 3 in option_depths"
    if len(np.unique(episode)) < 2:
        return "episode bootstrap requires at least two episodes"
    finite = [
        np.isfinite(episode.astype(np.float64)).all(),
        np.isfinite(depths.astype(np.float64)).all(),
        np.isfinite(option_error).all(),
        np.isfinite(uniform_error).all(),
        np.isfinite(score).all(),
    ]
    if not all(bool(item) for item in finite):
        return "arrays contain non-finite values"
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
    rx -= float(rx.mean())
    ry -= float(ry.mean())
    denom = math.sqrt(float(np.dot(rx, rx)) * float(np.dot(ry, ry)))
    if denom <= 0.0:
        return 0.0
    return clean_float(float(np.dot(rx, ry) / denom))


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0] for ep in np.unique(episode)]


def exact_budget_choice(episode: np.ndarray, score: np.ndarray, depths: np.ndarray) -> np.ndarray:
    chosen = np.zeros(len(episode), dtype=np.int64)
    for idxs in episode_groups(episode):
        idxs = idxs.astype(np.int64)
        n = len(idxs)
        target = int(3 * n)
        dp = np.full((n + 1, target + 1), np.inf, dtype=np.float64)
        prev_budget = np.full((n + 1, target + 1), -1, dtype=np.int64)
        prev_choice = np.full((n + 1, target + 1), -1, dtype=np.int64)
        dp[0, 0] = 0.0
        for row, item in enumerate(idxs):
            for budget in range(target + 1):
                base = dp[row, budget]
                if not math.isfinite(float(base)):
                    continue
                for col, depth in enumerate(depths):
                    new_budget = budget + int(depth)
                    if new_budget <= target:
                        value = base + float(score[item, col])
                        if value < dp[row + 1, new_budget]:
                            dp[row + 1, new_budget] = value
                            prev_budget[row + 1, new_budget] = budget
                            prev_choice[row + 1, new_budget] = col
        if not math.isfinite(float(dp[n, target])):
            raise RuntimeError("exact budget assignment is infeasible")
        budget = target
        for row in range(n, 0, -1):
            col = int(prev_choice[row, budget])
            if col < 0:
                raise RuntimeError("broken exact budget traceback")
            chosen[idxs[row - 1]] = col
            budget = int(prev_budget[row, budget])
    return chosen


def bootstrap_ci(samples: np.ndarray) -> dict[str, float]:
    return {
        "low": clean_float(float(np.percentile(samples, 2.5))),
        "high": clean_float(float(np.percentile(samples, 97.5))),
    }


def evaluate(arrays: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    episode = np.asarray(arrays["episode"]).reshape(-1).astype(np.int64)
    depths = np.asarray(arrays["option_depths"]).reshape(-1).astype(np.int64)
    option_error = np.asarray(arrays["option_error"], dtype=np.float64)
    uniform_error = np.asarray(arrays["uniform_error"], dtype=np.float64).reshape(-1)
    score = np.asarray(arrays["predicted_option_score"], dtype=np.float64)
    mid = int(np.where(depths == 3)[0][0])
    chosen = exact_budget_choice(episode, score, depths)
    chosen_error = option_error[np.arange(len(chosen)), chosen]
    chosen_steps = depths[chosen].astype(np.float64)
    uniform_steps = np.full(len(chosen), 3.0, dtype=np.float64)
    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(chosen_error[idx])) for idx in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(chosen_steps[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idx])) for idx in groups], dtype=np.float64)
    observed = clean_float(float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum()))
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        samples[i] = float(
            selected_ep_error[pick].sum() / selected_ep_steps[pick].sum()
            - uniform_ep_error[pick].sum() / uniform_ep_steps[pick].sum()
        )
    ci = bootstrap_ci(samples)
    rho = spearman(score.reshape(-1), option_error.reshape(-1))
    status = "positive" if ci["high"] < 0.0 else ("negative" if ci["low"] >= 0.0 else "unidentifiable")
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": observed},
        "metric": METRIC,
        "metric_value": observed,
        "ci": ci,
        "status": status,
        "measured_scope": ["allocation_delta", "structured_exact_budget_assignment", "score_error_spearman"],
        "reported_claim": (
            f"structured exact-budget compute-value allocation_delta={observed:.9g}, "
            f"95% CI=[{ci['low']:.9g},{ci['high']:.9g}], score/error Spearman={rho:.9g}; "
            "lower predicted option score is selected by per-episode exact-budget DP"
        ),
        "diagnostics": {
            "anchors": int(len(episode)),
            "episodes": int(len(np.unique(episode))),
            "option_depths": [int(item) for item in depths.tolist()],
            "chosen_depth_counts": {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))},
            "uniform_depth_column": mid,
            "score_error_spearman": rho,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate structured exact-budget compute-value assignment")
    parser.add_argument("--artifact", default=str(DEFAULT_ARTIFACT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    artifact = Path(args.artifact)
    if not artifact.exists():
        payload = fail_closed("missing structured assignment artifact", artifact=artifact)
    else:
        arrays = load_npz(artifact)
        reason = validate(arrays)
        payload = fail_closed(reason, artifact=artifact) if reason else evaluate(arrays, seed=int(args.seed))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

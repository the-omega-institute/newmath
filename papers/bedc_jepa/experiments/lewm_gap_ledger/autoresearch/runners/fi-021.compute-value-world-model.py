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


def evaluate(arrays: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    episode = np.asarray(arrays["episode"]).reshape(-1).astype(np.int64)
    option_error = np.asarray(arrays["option_error"], dtype=np.float64)
    uniform_error = np.asarray(arrays["uniform_error"], dtype=np.float64).reshape(-1)
    predicted_mv = np.asarray(arrays["predicted_mv"], dtype=np.float64)
    true_mv = uniform_error[:, None] - option_error
    chosen = np.argmax(predicted_mv, axis=1)
    chosen_error = option_error[np.arange(option_error.shape[0]), chosen]
    observed_delta = clean_float(float(np.mean(chosen_error - uniform_error)))
    per_anchor_true_mv = true_mv[np.arange(option_error.shape[0]), chosen]
    per_anchor_pred_mv = predicted_mv[np.arange(option_error.shape[0]), chosen]
    observed_rho = spearman(per_anchor_pred_mv, per_anchor_true_mv)

    episodes = np.unique(episode)
    by_episode = [np.where(episode == ep)[0] for ep in episodes]
    rng = np.random.default_rng(seed)
    deltas: list[float] = []
    rhos: list[float] = []
    for _ in range(BOOTSTRAPS):
        sample = rng.integers(0, len(by_episode), size=len(by_episode))
        idx = np.concatenate([by_episode[int(item)] for item in sample])
        deltas.append(float(np.mean(chosen_error[idx] - uniform_error[idx])))
        rhos.append(spearman(per_anchor_pred_mv[idx], per_anchor_true_mv[idx]))
    delta_ci = bootstrap_ci(deltas)
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
            "failure probability is not used as the allocation target"
        ),
        "diagnostics": {
            "anchors": int(option_error.shape[0]),
            "options": int(option_error.shape[1]),
            "episodes": int(len(episodes)),
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

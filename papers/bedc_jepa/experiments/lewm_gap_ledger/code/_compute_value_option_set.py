from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_model as cvm


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_POLICY = REPORT_DIR / "compute_value_policy_stability_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_option_set.json"
DEFAULT_MD = REPORT_DIR / "compute_value_option_set.md"
DEFAULT_NPZ = REPORT_DIR / "compute_value_option_set.npz"
BOOTSTRAPS = 1000


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


def load_policy_artifact(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        payload = {
            "episode": data["episode"].astype(np.int64),
            "t0": data["t0"].astype(np.int64),
            "anchor_ep_t0": data["anchor_ep_t0"].astype(np.int64),
            "true_mv": data["true_mv"].astype(np.float64),
        }
        if "policy_score" in data.files:
            payload["policy_score"] = data["policy_score"].astype(np.float64)
        else:
            predicted = data["predicted_mv"].astype(np.float64)
            old_depths = data["option_depths"].astype(np.int64)
            low = int(np.where(old_depths < 3)[0][0])
            high = int(np.where(old_depths > 3)[0][-1])
            payload["policy_score"] = predicted[:, high] - predicted[:, low]
    return payload


def load_eval_labels(labels_path: str) -> dict[str, np.ndarray]:
    labels = cvm.load_npz(cvm.resolve_path(labels_path, [cvm.DEFAULT_LABELS, cvm.ALT_LABELS]))
    return labels


def horizon_indices(labels: dict[str, np.ndarray], depths: np.ndarray) -> list[int]:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    return [horizons.index(int(depth)) for depth in depths]


def option_errors(labels: dict[str, np.ndarray], depths: np.ndarray) -> np.ndarray:
    indices = horizon_indices(labels, depths)
    valid = labels["eval_valid"][:, indices].all(axis=1)
    err_at_h = labels["eval_err_at_h"][valid].astype(np.float64)
    out = np.zeros((err_at_h.shape[0], len(depths)), dtype=np.float64)
    for col, depth in enumerate(depths):
        out[:, col] = np.sum(err_at_h[:, : int(depth)], axis=1)
    return out


def aligned_option_errors(policy_payload: dict[str, np.ndarray], labels: dict[str, np.ndarray], depths: np.ndarray) -> np.ndarray:
    # The policy artifact is already the h=5-valid eval subset. Reconstruct the
    # same subset from labels and rely on identical eval ordering.
    all_errors = option_errors(labels, depths)
    if len(all_errors) != len(policy_payload["episode"]):
        raise RuntimeError(f"eval subset mismatch: {len(all_errors)} vs {len(policy_payload['episode'])}")
    return all_errors


def rankdata(values: np.ndarray) -> np.ndarray:
    return cvm.rankdata(values.astype(np.float64))


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    return cvm.spearman(x.astype(np.float64), y.astype(np.float64))


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return cvm.episode_groups(episode.astype(np.int64))


def balanced_choice(episode: np.ndarray, score: np.ndarray, depths: np.ndarray) -> np.ndarray:
    if len(depths) % 2 == 0:
        raise ValueError("depth grid must have odd length")
    mid_col = int(np.where(depths == 3)[0][0])
    chosen = np.full(len(score), mid_col, dtype=np.int64)
    side = min(np.sum(depths < 3), np.sum(depths > 3))
    for idxs in episode_groups(episode):
        ordered = np.asarray(sorted((int(i) for i in idxs), key=lambda i: (float(score[i]), int(i))), dtype=np.int64)
        n = len(ordered)
        if n < 2:
            continue
        bucket = n // (2 * side + 1)
        if bucket == 0:
            half = n // 2
            chosen[ordered[:half]] = int(np.where(depths < 3)[0][0])
            chosen[ordered[n - half :]] = int(np.where(depths > 3)[0][-1])
            continue
        cursor_low = 0
        cursor_high = n
        low_cols = list(np.where(depths < 3)[0])
        high_cols = list(np.where(depths > 3)[0])
        for low_col, high_col in zip(low_cols, reversed(high_cols)):
            low_slice = ordered[cursor_low : cursor_low + bucket]
            high_slice = ordered[cursor_high - bucket : cursor_high]
            chosen[low_slice] = int(low_col)
            chosen[high_slice] = int(high_col)
            cursor_low += bucket
            cursor_high -= bucket
        chosen[ordered[cursor_low:cursor_high]] = mid_col
        selected_steps = depths[chosen[ordered]]
        target = 3 * n
        diff = int(np.sum(selected_steps) - target)
        if diff != 0:
            # Repair rare remainder imbalance by moving boundary items to depth 3.
            repair_order = ordered[np.argsort(np.abs(score[ordered] - np.median(score[ordered])), kind="mergesort")]
            for item in repair_order:
                if diff == 0:
                    break
                current = int(depths[chosen[item]])
                if diff > 0 and current > 3:
                    diff -= current - 3
                    chosen[item] = mid_col
                elif diff < 0 and current < 3:
                    diff += 3 - current
                    chosen[item] = mid_col
            if diff != 0:
                raise RuntimeError("failed to repair balanced option-set budget")
    return chosen


def oracle_choice(option_error: np.ndarray, depths: np.ndarray) -> np.ndarray:
    per_step = option_error / depths[None, :].astype(np.float64)
    return np.argmin(per_step, axis=1).astype(np.int64)


def evaluate(
    episode: np.ndarray,
    option_error: np.ndarray,
    depths: np.ndarray,
    chosen: np.ndarray,
    *,
    seed: int,
) -> dict[str, Any]:
    mid = int(np.where(depths == 3)[0][0])
    selected_error = option_error[np.arange(len(chosen)), chosen]
    selected_steps = depths[chosen].astype(np.float64)
    uniform_error = option_error[:, mid]
    uniform_steps = np.full(len(chosen), 3.0, dtype=np.float64)
    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(selected_error[idx])) for idx in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(selected_steps[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idx])) for idx in groups], dtype=np.float64)
    observed = float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum())
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        samples[i] = float(
            selected_ep_error[pick].sum() / selected_ep_steps[pick].sum()
            - uniform_ep_error[pick].sum() / uniform_ep_steps[pick].sum()
        )
    return {
        "allocation_delta": {
            "observed": clean_float(observed),
            "low": clean_float(float(np.percentile(samples, 2.5))),
            "high": clean_float(float(np.percentile(samples, 97.5))),
        },
        "chosen_depth_counts": {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))},
    }


def target_score(option_error: np.ndarray, depths: np.ndarray) -> np.ndarray:
    low = int(np.where(depths < 3)[0][0])
    high = int(np.where(depths > 3)[0][-1])
    return option_error[:, low] / float(depths[low]) - option_error[:, high] / float(depths[high])


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Option Set",
        "",
        f"- anchors: `{report['counts']['anchors']}`",
        f"- episodes: `{report['counts']['episodes']}`",
        "",
        "| option set | oracle delta | policy-score delta | score Spearman |",
        "|---|---:|---:|---:|",
    ]
    for name in ["depths_1_3_5", "depths_1_2_3_4_5"]:
        row = report["option_sets"][name]
        oracle = row["oracle"]["allocation_delta"]
        policy = row["policy_rank"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {oracle['observed']:.9g} [{oracle['low']:.9g}, {oracle['high']:.9g}] | "
            f"{policy['observed']:.9g} [{policy['low']:.9g}, {policy['high']:.9g}] | {row['policy_score_spearman']:.9g} |"
        )
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Compare compute-value option-set granularity")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--policy", default=str(DEFAULT_POLICY))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    args = parser.parse_args()

    policy = load_policy_artifact(Path(args.policy))
    labels = load_eval_labels(str(args.labels))
    episode = policy["episode"].astype(np.int64)
    score = policy["policy_score"].astype(np.float64)
    option_sets = {
        "depths_1_3_5": np.asarray([1, 3, 5], dtype=np.int64),
        "depths_1_2_3_4_5": np.asarray([1, 2, 3, 4, 5], dtype=np.int64),
    }
    report_sets: dict[str, Any] = {}
    npz_payload: dict[str, np.ndarray] = {"episode": episode, "policy_score": score}
    for idx, (name, depths) in enumerate(option_sets.items()):
        errors = aligned_option_errors(policy, labels, depths)
        oracle = oracle_choice(errors, depths)
        policy_choice = balanced_choice(episode, score, depths)
        target = target_score(errors, depths)
        report_sets[name] = {
            "depths": depths.tolist(),
            "oracle": evaluate(episode, errors, depths, oracle, seed=3001 + idx),
            "policy_rank": evaluate(episode, errors, depths, policy_choice, seed=3011 + idx),
            "policy_score_spearman": spearman(score, target),
            "target_score_summary": {
                "mean": clean_float(float(np.mean(target))),
                "std": clean_float(float(np.std(target))),
                "p10": clean_float(float(np.quantile(target, 0.10))),
                "p50": clean_float(float(np.quantile(target, 0.50))),
                "p90": clean_float(float(np.quantile(target, 0.90))),
            },
        }
        safe = name.replace("depths_", "d")
        npz_payload[f"{safe}_option_error"] = errors.astype(np.float64)
        npz_payload[f"{safe}_oracle_choice"] = oracle.astype(np.int64)
        npz_payload[f"{safe}_policy_choice"] = policy_choice.astype(np.int64)
        npz_payload[f"{safe}_target_score"] = target.astype(np.float64)
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_option_set",
        "inputs": {"labels": str(args.labels), "policy": str(args.policy)},
        "counts": {"anchors": int(len(episode)), "episodes": int(len(np.unique(episode)))},
        "option_sets": report_sets,
        "leakage_attestation": {
            "policy_score": "precomputed eval policy score; no training here",
            "eval_truth_usage": "option errors used only for oracle and diagnostic gates",
            "slurm_or_ssh": "not used",
        },
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(args.npz, **npz_payload)
    print(json.dumps(clean_json(report["option_sets"]), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

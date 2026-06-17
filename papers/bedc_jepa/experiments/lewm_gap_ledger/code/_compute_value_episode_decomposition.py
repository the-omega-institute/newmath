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
DEFAULT_POLICY = REPORT_DIR / "compute_value_policy_stability_predictions.npz"
DEFAULT_BASELINE = REPORT_DIR / "compute_value_model_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_episode_decomposition.json"
DEFAULT_MD = REPORT_DIR / "compute_value_episode_decomposition.md"
DEFAULT_NPZ = REPORT_DIR / "compute_value_episode_decomposition.npz"


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


def load_eval_payload(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {
            "episode": data["episode"].astype(np.int64),
            "t0": data["t0"].astype(np.int64),
            "anchor_ep_t0": data["anchor_ep_t0"].astype(np.int64),
            "option_error": data["option_error"].astype(np.float64),
            "uniform_error": data["uniform_error"].astype(np.float64),
            "true_mv": data["true_mv"].astype(np.float64),
            "uniform_steps": data["uniform_steps"].astype(np.float64),
        }


def policy_score(path: Path) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        if "policy_score" in data.files:
            return data["policy_score"].astype(np.float64)
        predicted = data["predicted_mv"].astype(np.float64)
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return predicted[:, high_idx] - predicted[:, low_idx]


def aligned_baseline_score(path: Path, payload: dict[str, np.ndarray]) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        anchors = data["anchor_ep_t0"].astype(np.int64)
        predicted = data["predicted_mv"].astype(np.float64)
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    score = predicted[:, high_idx] - predicted[:, low_idx]
    key_to_score = {(int(ep), int(t0)): float(s) for (ep, t0), s in zip(anchors, score)}
    out = np.zeros(len(payload["episode"]), dtype=np.float64)
    for i, (ep, t0) in enumerate(payload["anchor_ep_t0"]):
        out[i] = key_to_score[(int(ep), int(t0))]
    return out


def true_score(payload: dict[str, np.ndarray]) -> np.ndarray:
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return payload["true_mv"][:, high_idx] - payload["true_mv"][:, low_idx]


def choice_from_score(payload: dict[str, np.ndarray], score: np.ndarray) -> np.ndarray:
    predicted_mv = cvp.scalar_to_predicted_mv(score.astype(np.float64))
    chosen, _ = cvm.balanced_depth_choice(payload["episode"], predicted_mv)
    return chosen


def per_episode(payload: dict[str, np.ndarray], score: np.ndarray) -> dict[str, np.ndarray]:
    chosen = choice_from_score(payload, score)
    chosen_error = payload["option_error"][np.arange(len(chosen)), chosen]
    chosen_steps = cvm.OPTION_DEPTHS[chosen].astype(np.float64)
    uniform_error = payload["uniform_error"]
    uniform_steps = np.full(len(chosen), cvm.UNIFORM_DEPTH, dtype=np.float64)
    groups = cvm.episode_groups(payload["episode"])
    episodes = np.asarray([int(payload["episode"][idxs[0]]) for idxs in groups], dtype=np.int64)
    selected_rate = np.asarray([float(np.sum(chosen_error[idxs]) / np.sum(chosen_steps[idxs])) for idxs in groups], dtype=np.float64)
    uniform_rate = np.asarray([float(np.sum(uniform_error[idxs]) / np.sum(uniform_steps[idxs])) for idxs in groups], dtype=np.float64)
    delta = selected_rate - uniform_rate
    counts = np.asarray([len(idxs) for idxs in groups], dtype=np.int64)
    return {
        "episode": episodes,
        "count": counts,
        "delta": delta,
        "selected_rate": selected_rate,
        "uniform_rate": uniform_rate,
    }


def summarize_delta(delta: np.ndarray) -> dict[str, Any]:
    return {
        "mean": clean_float(float(np.mean(delta))),
        "median": clean_float(float(np.median(delta))),
        "min": clean_float(float(np.min(delta))),
        "max": clean_float(float(np.max(delta))),
        "positive_count": int(np.sum(delta > 0.0)),
        "negative_count": int(np.sum(delta < 0.0)),
        "zero_count": int(np.sum(delta == 0.0)),
    }


def top_rows(episodes: np.ndarray, values: np.ndarray, count: np.ndarray, *, largest: bool, k: int) -> list[dict[str, Any]]:
    order = np.argsort(values)
    if largest:
        order = order[::-1]
    rows = []
    for idx in order[:k]:
        rows.append({"episode": int(episodes[idx]), "count": int(count[idx]), "value": clean_float(float(values[idx]))})
    return rows


def concentration(values: np.ndarray) -> dict[str, Any]:
    positive = np.maximum(values.astype(np.float64), 0.0)
    total = float(np.sum(positive))
    if total <= 0.0:
        return {"total_positive": 0.0, "top1_share": 0.0, "top5_share": 0.0, "top10_share": 0.0}
    ordered = np.sort(positive)[::-1]
    return {
        "total_positive": clean_float(total),
        "top1_share": clean_float(float(np.sum(ordered[:1]) / total)),
        "top5_share": clean_float(float(np.sum(ordered[:5]) / total)),
        "top10_share": clean_float(float(np.sum(ordered[:10]) / total)),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Episode Decomposition",
        "",
        f"- episodes: `{report['counts']['episodes']}`",
        f"- anchors: `{report['counts']['anchors']}`",
        f"- policy mean episode delta: `{report['summaries']['policy']['mean']:.9g}`",
        f"- scalar RankNet mean episode delta: `{report['summaries']['scalar_ranknet']['mean']:.9g}`",
        f"- oracle mean episode delta: `{report['summaries']['oracle']['mean']:.9g}`",
        f"- missed oracle top5 share: `{report['missed_oracle_concentration']['top5_share']:.9g}`",
        "",
        "| scorer | mean | median | positive episodes | negative episodes |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in ["policy", "scalar_ranknet", "oracle", "random_reference"]:
        row = report["summaries"][name]
        lines.append(
            f"| `{name}` | {row['mean']:.9g} | {row['median']:.9g} | {row['positive_count']} | {row['negative_count']} |"
        )
    lines.extend(["", "Worst missed-oracle episodes:", ""])
    for row in report["worst_missed_oracle_episodes"]:
        lines.append(f"- episode `{row['episode']}`: missed `{row['value']:.9g}` over `{row['count']}` anchors")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Decompose compute-value allocation by episode")
    parser.add_argument("--policy", default=str(DEFAULT_POLICY))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--npz", default=str(DEFAULT_NPZ))
    parser.add_argument("--random-seed", type=int, default=101)
    args = parser.parse_args()

    policy_path = Path(args.policy)
    baseline_path = Path(args.baseline)
    payload = load_eval_payload(policy_path)
    policy = per_episode(payload, policy_score(policy_path))
    scalar_ranknet = per_episode(payload, aligned_baseline_score(baseline_path, payload))
    oracle = per_episode(payload, true_score(payload))
    rng = np.random.default_rng(int(args.random_seed))
    random_ref = per_episode(payload, rng.standard_normal(len(payload["episode"])))

    episodes = policy["episode"]
    if not np.array_equal(episodes, oracle["episode"]):
        raise RuntimeError("episode alignment failed")
    missed_oracle = policy["delta"] - oracle["delta"]
    policy_minus_ranknet = policy["delta"] - scalar_ranknet["delta"]
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_episode_decomposition",
        "inputs": {"policy": str(policy_path), "baseline": str(baseline_path)},
        "counts": {"anchors": int(len(payload["episode"])), "episodes": int(len(episodes))},
        "summaries": {
            "policy": summarize_delta(policy["delta"]),
            "scalar_ranknet": summarize_delta(scalar_ranknet["delta"]),
            "oracle": summarize_delta(oracle["delta"]),
            "random_reference": summarize_delta(random_ref["delta"]),
            "policy_minus_scalar_ranknet": summarize_delta(policy_minus_ranknet),
            "missed_oracle": summarize_delta(missed_oracle),
        },
        "missed_oracle_concentration": concentration(missed_oracle),
        "policy_harm_concentration": concentration(policy["delta"]),
        "worst_policy_harm_episodes": top_rows(episodes, policy["delta"], policy["count"], largest=True, k=8),
        "best_policy_gain_episodes": top_rows(episodes, policy["delta"], policy["count"], largest=False, k=8),
        "worst_missed_oracle_episodes": top_rows(episodes, missed_oracle, policy["count"], largest=True, k=8),
        "best_policy_over_ranknet_episodes": top_rows(episodes, policy_minus_ranknet, policy["count"], largest=False, k=8),
        "leakage_attestation": {
            "policy_scores": "loaded from precomputed policy prediction artifact",
            "eval_truth_usage": "option errors are used only for post-hoc decomposition",
            "training": "none in this script",
            "slurm_or_ssh": "not used",
        },
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(
        args.npz,
        episode=episodes.astype(np.int64),
        count=policy["count"].astype(np.int64),
        policy_delta=policy["delta"].astype(np.float64),
        scalar_ranknet_delta=scalar_ranknet["delta"].astype(np.float64),
        oracle_delta=oracle["delta"].astype(np.float64),
        random_delta=random_ref["delta"].astype(np.float64),
        missed_oracle=missed_oracle.astype(np.float64),
        policy_minus_scalar_ranknet=policy_minus_ranknet.astype(np.float64),
    )
    print(
        json.dumps(
            clean_json(
                {
                    "policy": report["summaries"]["policy"],
                    "scalar_ranknet": report["summaries"]["scalar_ranknet"],
                    "oracle": report["summaries"]["oracle"],
                    "missed_oracle_concentration": report["missed_oracle_concentration"],
                }
            ),
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

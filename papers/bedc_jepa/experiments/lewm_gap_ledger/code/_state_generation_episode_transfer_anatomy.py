from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_model as cvm
import _compute_value_structured_assignment as structured


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_transfer_anatomy.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_transfer_anatomy.md"


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


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return cvm.episode_groups(episode.astype(np.int64))


def depth_counts(depths: np.ndarray, chosen: np.ndarray) -> dict[str, int]:
    return {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))}


def row_anatomy(base: dict[str, np.ndarray], score: np.ndarray) -> dict[str, Any]:
    episode = base["episode"].astype(np.int64)
    depths = base["option_depths"].astype(np.int64)
    option_error = base["option_error"].astype(np.float64)
    mid = int(np.where(depths == 3)[0][0])
    chosen = structured.exact_budget_choice(episode, score.astype(np.float64), structured.DEPTHS).astype(np.int64)
    oracle = base["oracle_choice"].astype(np.int64)
    groups = episode_groups(episode)
    selected_error = option_error[np.arange(len(chosen)), chosen]
    uniform_error = option_error[:, mid]
    oracle_error = option_error[np.arange(len(oracle)), oracle]
    selected_steps = depths[chosen].astype(np.float64)
    episode_rows: list[dict[str, Any]] = []
    for idxs in groups:
        idxs = idxs.astype(np.int64)
        ep = int(episode[idxs[0]])
        selected_sum = float(np.sum(selected_error[idxs]))
        uniform_sum = float(np.sum(uniform_error[idxs]))
        oracle_sum = float(np.sum(oracle_error[idxs]))
        selected_step_sum = float(np.sum(selected_steps[idxs]))
        uniform_step_sum = float(3 * len(idxs))
        delta = selected_sum / selected_step_sum - uniform_sum / uniform_step_sum
        oracle_delta = oracle_sum / uniform_step_sum - uniform_sum / uniform_step_sum
        regret_to_oracle = selected_sum / selected_step_sum - oracle_sum / uniform_step_sum
        oracle_match = float(np.mean(chosen[idxs] == oracle[idxs]))
        episode_rows.append(
            {
                "episode": ep,
                "anchors": int(len(idxs)),
                "delta": clean_float(delta),
                "oracle_delta": clean_float(oracle_delta),
                "regret_to_oracle": clean_float(regret_to_oracle),
                "oracle_match": clean_float(oracle_match),
                "mean_depth": clean_float(float(np.mean(depths[chosen[idxs]].astype(np.float64)))),
                "chosen_depth_counts": depth_counts(depths, chosen[idxs]),
            }
        )
    deltas = np.asarray([row["delta"] for row in episode_rows], dtype=np.float64)
    regrets = np.asarray([row["regret_to_oracle"] for row in episode_rows], dtype=np.float64)
    harmful = [row for row in sorted(episode_rows, key=lambda item: float(item["delta"]), reverse=True) if float(row["delta"]) > 0.0]
    helpful = [row for row in sorted(episode_rows, key=lambda item: float(item["delta"])) if float(row["delta"]) < 0.0]
    top_k = max(1, min(10, len(episode_rows)))
    top_harm = harmful[:top_k]
    top_help = helpful[:top_k]
    return {
        "chosen": chosen,
        "episode_rows": episode_rows,
        "summary": {
            "episode_count": int(len(episode_rows)),
            "harmful_episode_count": int(np.sum(deltas > 0.0)),
            "helpful_episode_count": int(np.sum(deltas < 0.0)),
            "delta_mean": clean_float(float(np.mean(deltas))),
            "delta_median": clean_float(float(np.median(deltas))),
            "delta_p90": clean_float(float(np.percentile(deltas, 90))),
            "delta_p10": clean_float(float(np.percentile(deltas, 10))),
            "regret_to_oracle_mean": clean_float(float(np.mean(regrets))),
            "regret_to_oracle_p90": clean_float(float(np.percentile(regrets, 90))),
            "top_harm_episode_share": clean_float(float(np.sum([row["delta"] for row in top_harm]) / max(1.0e-12, np.sum(np.maximum(deltas, 0.0))))),
            "top_harm_episodes": top_harm[:5],
            "top_help_episodes": top_help[:5],
        },
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Episode Transfer Anatomy",
        "",
        f"- rows: `{list(report['rows'].keys())}`",
        f"- shared top-harm episodes: `{report['cross_row']['shared_top_harm_episode_count']}`",
        "",
        "| row | harmful episodes | delta mean | delta p90 | regret mean | top-harm share |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name, row in report["rows"].items():
        s = row["summary"]
        lines.append(
            f"| `{name}` | {s['harmful_episode_count']} | {s['delta_mean']:.6g} | "
            f"{s['delta_p90']:.6g} | {s['regret_to_oracle_mean']:.6g} | {s['top_harm_episode_share']:.6g} |"
        )
    lines.extend(["", "## Top Harm Episodes", ""])
    for name, row in report["rows"].items():
        eps = [item["episode"] for item in row["summary"]["top_harm_episodes"]]
        lines.append(f"- `{name}`: `{eps}`")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Decompose held-out allocation transfer error by episode")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    args = parser.parse_args()
    best_seed = load_npz(REPORT_DIR / "state_generation_episode_allocation_seed_617_predictions.npz")
    rows: dict[str, np.ndarray] = {
        "episode_best_seed": best_seed["episode_allocation_score"].astype(np.float64),
        "episode_objective": load_npz(REPORT_DIR / "state_generation_episode_allocation_predictions.npz")["episode_allocation_score"].astype(np.float64),
        "seed_mean": load_npz(REPORT_DIR / "state_generation_episode_seed_ensemble_predictions.npz")["mean_score"].astype(np.float64),
        "episode_balanced": load_npz(REPORT_DIR / "state_generation_episode_balanced_predictions.npz")["episode_balanced_score"].astype(np.float64),
        "episode_regret": load_npz(REPORT_DIR / "state_generation_episode_regret_predictions.npz")["episode_regret_score"].astype(np.float64),
        "episode_dual_price": load_npz(REPORT_DIR / "state_generation_episode_dual_price_predictions.npz")["dual_price_score"].astype(np.float64),
    }
    anatomy = {name: row_anatomy(best_seed, score) for name, score in rows.items()}
    top_sets = {
        name: {int(item["episode"]) for item in row["summary"]["top_harm_episodes"]}
        for name, row in anatomy.items()
    }
    shared = set.intersection(*top_sets.values()) if top_sets else set()
    union = set.union(*top_sets.values()) if top_sets else set()
    row_payload = {
        name: {
            "summary": row["summary"],
        }
        for name, row in anatomy.items()
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_transfer_anatomy",
        "rows": row_payload,
        "cross_row": {
            "shared_top_harm_episode_count": int(len(shared)),
            "shared_top_harm_episodes": sorted(int(x) for x in shared),
            "top_harm_union_count": int(len(union)),
            "top_harm_union_episodes": sorted(int(x) for x in union),
        },
        "leakage_attestation": {
            "features": "held-out eval predictions only; no retraining",
            "selection": "diagnostic decomposition only",
            "slurm_or_ssh": "not used",
            "targets": "eval option_error used only after fixed score generation for per-episode diagnostics",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

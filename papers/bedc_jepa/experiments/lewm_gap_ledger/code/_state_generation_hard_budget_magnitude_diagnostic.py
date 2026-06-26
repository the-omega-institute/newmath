from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_conditioned_allocation as geometry_alloc
import _state_generation_geometry_option_conditioned_allocation as option_geom


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_PRED = REPORT_DIR / "state_generation_geometry_option_conditioned_allocation_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_budget_magnitude_diagnostic.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_budget_magnitude_diagnostic.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"


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


def pair_accuracy(score: np.ndarray, truth: np.ndarray) -> float:
    good = 0
    total = 0
    for i in range(score.shape[1]):
        for j in range(i + 1, score.shape[1]):
            td = truth[:, i] - truth[:, j]
            sd = score[:, i] - score[:, j]
            mask = np.abs(td) > 1.0e-9
            good += int(np.sum(np.sign(td[mask]) == np.sign(sd[mask])))
            total += int(np.sum(mask))
    return clean_float(float(good / total)) if total else 0.0


def pearson(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return 0.0
    xx = x.astype(np.float64) - float(np.mean(x.astype(np.float64)))
    yy = y.astype(np.float64) - float(np.mean(y.astype(np.float64)))
    denom = math.sqrt(float(np.dot(xx, xx)) * float(np.dot(yy, yy)))
    return clean_float(float(np.dot(xx, yy) / denom)) if denom > 0.0 else 0.0


def linear_slope(x: np.ndarray, y: np.ndarray) -> float:
    xx = x.astype(np.float64) - float(np.mean(x.astype(np.float64)))
    yy = y.astype(np.float64) - float(np.mean(y.astype(np.float64)))
    denom = float(np.dot(xx, xx))
    return clean_float(float(np.dot(xx, yy) / denom)) if denom > 0.0 else 0.0


def confusion(chosen: np.ndarray, oracle: np.ndarray, depths: np.ndarray) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for true_col, true_depth in enumerate(depths):
        row: dict[str, int] = {}
        mask = oracle == true_col
        for chosen_col, chosen_depth in enumerate(depths):
            row[str(int(chosen_depth))] = int(np.sum(mask & (chosen == chosen_col)))
        out[str(int(true_depth))] = row
    return out


def selected_error(option_error: np.ndarray, chosen: np.ndarray) -> np.ndarray:
    return option_error[np.arange(len(chosen)), chosen.astype(np.int64)].astype(np.float64)


def episode_table(
    episode: np.ndarray,
    option_error: np.ndarray,
    score: np.ndarray,
    chosen: np.ndarray,
    oracle: np.ndarray,
    depths: np.ndarray,
) -> list[dict[str, Any]]:
    mid = int(np.where(depths == 3)[0][0])
    selected = selected_error(option_error, chosen)
    oracle_error = selected_error(option_error, oracle)
    uniform_error = option_error[:, mid].astype(np.float64)
    selected_steps = depths[chosen].astype(np.float64)
    oracle_steps = depths[oracle].astype(np.float64)
    uniform_steps = np.full(len(chosen), 3.0, dtype=np.float64)
    rows: list[dict[str, Any]] = []
    for ep in np.unique(episode.astype(np.int64)):
        idx = np.where(episode.astype(np.int64) == int(ep))[0]
        selected_rate = float(np.sum(selected[idx]) / np.sum(selected_steps[idx]))
        oracle_rate = float(np.sum(oracle_error[idx]) / np.sum(oracle_steps[idx]))
        uniform_rate = float(np.sum(uniform_error[idx]) / np.sum(uniform_steps[idx]))
        rows.append(
            {
                "episode": int(ep),
                "anchors": int(len(idx)),
                "selected_minus_uniform": clean_float(selected_rate - uniform_rate),
                "oracle_minus_uniform": clean_float(oracle_rate - uniform_rate),
                "selected_minus_oracle": clean_float(selected_rate - oracle_rate),
                "score_std": clean_float(float(np.std(score[idx].reshape(-1)))),
                "true_std": clean_float(float(np.std(option_error[idx].reshape(-1)))),
                "chosen_depth_counts": {
                    str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen[idx]], return_counts=True))
                },
                "oracle_depth_counts": {
                    str(int(k)): int(v) for k, v in zip(*np.unique(depths[oracle[idx]], return_counts=True))
                },
            }
        )
    rows.sort(key=lambda item: float(item["selected_minus_uniform"]), reverse=True)
    return rows


def slice_payload(split: dict[str, np.ndarray], mask: np.ndarray) -> dict[str, np.ndarray]:
    return geometry_alloc.slice_eval(split, mask.astype(bool))


def analyze_slice(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    hard_mask: np.ndarray,
    slice_name: str,
    mask: np.ndarray,
) -> dict[str, Any]:
    local = slice_payload(split, mask)
    local_score = score[mask.astype(bool)].astype(np.float64)
    chosen = structured.exact_budget_choice(local["episode"], local_score, structured.DEPTHS)
    oracle = structured.exact_budget_choice(local["episode"], local["option_error"], structured.DEPTHS)
    mid = int(np.where(structured.DEPTHS == 3)[0][0])
    chosen_error = selected_error(local["option_error"], chosen)
    oracle_error = selected_error(local["option_error"], oracle)
    uniform_error = local["option_error"][:, mid].astype(np.float64)
    chosen_steps = structured.DEPTHS[chosen].astype(np.float64)
    oracle_steps = structured.DEPTHS[oracle].astype(np.float64)
    uniform_steps = np.full(len(chosen), 3.0, dtype=np.float64)
    chosen_rate = float(np.sum(chosen_error) / np.sum(chosen_steps))
    oracle_rate = float(np.sum(oracle_error) / np.sum(oracle_steps))
    uniform_rate = float(np.sum(uniform_error) / np.sum(uniform_steps))
    score_gap = (local_score - local_score[:, [mid]]).reshape(-1)
    true_gap = (local["option_error"] - local["option_error"][:, [mid]]).reshape(-1)
    per_episode = episode_table(
        local["episode"],
        local["option_error"],
        local_score,
        chosen,
        oracle,
        structured.DEPTHS,
    )
    harmful = [row for row in per_episode if float(row["selected_minus_uniform"]) > 0.0]
    return {
        "slice": slice_name,
        "anchor_count": int(len(chosen)),
        "episode_count": int(len(np.unique(local["episode"]))),
        "allocation_rates": {
            "chosen": clean_float(chosen_rate),
            "uniform": clean_float(uniform_rate),
            "oracle": clean_float(oracle_rate),
            "chosen_minus_uniform": clean_float(chosen_rate - uniform_rate),
            "oracle_minus_uniform": clean_float(oracle_rate - uniform_rate),
            "chosen_minus_oracle": clean_float(chosen_rate - oracle_rate),
        },
        "readability": {
            "score_error_spearman": clean_float(structured.cvm.spearman(local_score.reshape(-1), local["option_error"].reshape(-1))),
            "score_error_pearson": pearson(local_score.reshape(-1), local["option_error"].reshape(-1)),
            "pair_accuracy": pair_accuracy(local_score, local["option_error"]),
            "oracle_match": clean_float(float(np.mean(chosen.astype(np.int64) == oracle.astype(np.int64)))),
        },
        "gap_calibration": {
            "score_gap_std": clean_float(float(np.std(score_gap))),
            "true_gap_std": clean_float(float(np.std(true_gap))),
            "true_gap_on_score_gap_slope": linear_slope(score_gap, true_gap),
            "gap_pearson": pearson(score_gap, true_gap),
        },
        "depth_counts": {
            "chosen": {str(int(k)): int(v) for k, v in zip(*np.unique(structured.DEPTHS[chosen], return_counts=True))},
            "oracle": {str(int(k)): int(v) for k, v in zip(*np.unique(structured.DEPTHS[oracle], return_counts=True))},
        },
        "depth_confusion_oracle_rows": confusion(chosen, oracle, structured.DEPTHS),
        "harmful_episode_count": int(len(harmful)),
        "top_harmful_episodes": harmful[:7],
        "top_all_episodes": per_episode[:7],
        "hard_mask_fraction": clean_float(float(np.mean(hard_mask[mask.astype(bool)]))) if len(chosen) else 0.0,
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard Budget-Magnitude Diagnostic",
        "",
        "| slice | chosen-uniform | oracle-uniform | chosen-oracle | rho | pair acc | oracle match |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    for name in ["full", "non_hard", "hard_only"]:
        row = report["slices"][name]
        rates = row["allocation_rates"]
        read = row["readability"]
        lines.append(
            f"| `{name}` | {rates['chosen_minus_uniform']:.6g} | {rates['oracle_minus_uniform']:.6g} | "
            f"{rates['chosen_minus_oracle']:.6g} | {read['score_error_spearman']:.6g} | "
            f"{read['pair_accuracy']:.6g} | {read['oracle_match']:.6g} |"
        )
    lines.extend(["", "## Hard-Slice Depth Counts", ""])
    hard = report["slices"]["hard_only"]
    lines.append(f"- chosen: `{hard['depth_counts']['chosen']}`")
    lines.append(f"- oracle: `{hard['depth_counts']['oracle']}`")
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose hard-regime budget magnitude calibration")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--predictions", default=str(DEFAULT_PRED))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    pred = load_npz(Path(args.predictions))
    eval_split = episode_alloc.load_split(data, "eval")
    score = pred["geometry_option_conditioned_score"].astype(np.float64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    slices = {name: analyze_slice(eval_split, score, hard_mask, name, mask) for name, mask in masks.items()}
    hard = slices["hard_only"]
    non_hard = slices["non_hard"]
    rank_high = float(hard["readability"]["score_error_spearman"]) > 0.80
    hard_bad = float(hard["allocation_rates"]["chosen_minus_uniform"]) > 0.0
    non_hard_good = float(non_hard["allocation_rates"]["chosen_minus_uniform"]) < 0.0
    if rank_high and hard_bad and non_hard_good:
        verdict = (
            "The hard-slice failure is not ordinary local option-error unreadability: hard-only score/error Spearman "
            "is high, non-hard allocation improves over uniform, but hard-only exact-budget allocation remains harmful."
        )
    elif hard_bad:
        verdict = "The hard-only allocation slice remains harmful, but the diagnostic does not isolate it from local readability."
    else:
        verdict = "The hard-only allocation slice is not harmful under this diagnostic."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_budget_magnitude_diagnostic",
        "source_predictions": str(Path(args.predictions)),
        "hard_episode_union": hard_episodes,
        "slices": slices,
        "diagnosis": {
            "hard_rank_readable": bool(rank_high),
            "hard_allocation_harmful": bool(hard_bad),
            "non_hard_allocation_beneficial": bool(non_hard_good),
            "local_readability_not_sufficient": bool(rank_high and hard_bad),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "inputs": "fixed fi-064 eval option scores, eval episodes, and eval option_error for post-hoc diagnostics only",
            "training": "no model training is performed",
            "hard_ids": "held-out hard episode ids are used only for diagnostic slicing after fixed score generation",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

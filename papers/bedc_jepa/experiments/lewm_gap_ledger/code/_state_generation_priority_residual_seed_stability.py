from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured
import _state_generation_budget_priority_residual as priority_residual
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_assignment_value as episode_value
import _state_generation_geometry_conditioned_allocation as geometry_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_priority_residual_seed_stability.json"
DEFAULT_MD = REPORT_DIR / "state_generation_priority_residual_seed_stability.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_priority_residual_seed_stability_predictions.npz"
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


def slice_eval(split: dict[str, np.ndarray], score: np.ndarray, mask: np.ndarray, *, seed: int) -> dict[str, Any]:
    local = geometry_alloc.slice_eval(split, mask.astype(bool))
    local_score = score[mask.astype(bool)].astype(np.float64)
    out = structured.evaluate_scores(local, local_score, seed=seed)
    out["pair_accuracy"] = episode_alloc.pair_accuracy(local_score, local["option_error"])
    out["oracle_match"] = episode_alloc.oracle_match(local_score, episode_alloc.oracle_choice(local))
    return out


def eval_slices(eval_split: dict[str, np.ndarray], score: np.ndarray, hard_episodes: list[int], *, seed: int) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    return {name: slice_eval(eval_split, score, mask, seed=seed + idx * 17) for idx, (name, mask) in enumerate(masks.items())}


def one_seed(
    data: dict[str, np.ndarray],
    latents: dict[str, np.ndarray],
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    hard_episodes: list[int],
    *,
    scorer_seed: int,
    scorer_epochs: int,
    eval_seed: int,
) -> tuple[dict[str, Any], np.ndarray, np.ndarray]:
    train_raw, cal_raw, eval_raw, raw_selection, _feature_dims = priority_residual.regenerate_geometry_option_scores(
        data,
        latents,
        train,
        cal,
        eval_split,
        seed=int(scorer_seed),
        epochs=int(scorer_epochs),
        hidden=384,
        depth=2,
        batch=512,
        lr=6.0e-4,
    )
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env = geometry_alloc.env_feature_matrix(data, latents, "eval")
    _train_priority, _cal_priority, eval_priority, priority_selected = episode_value.priority_scores(
        train,
        cal,
        eval_split,
        train_raw,
        cal_raw,
        eval_raw,
        train_env,
        cal_env,
        eval_env,
        alpha=25.0,
        seed=eval_seed + scorer_seed,
    )
    raw_eval = eval_slices(eval_split, eval_raw, hard_episodes, seed=eval_seed + 100)
    priority_eval = eval_slices(eval_split, eval_priority, hard_episodes, seed=eval_seed + 200)
    hard_priority = priority_eval["hard_only"]["allocation_delta"]
    hard_raw = raw_eval["hard_only"]["allocation_delta"]
    row = {
        "scorer_seed": int(scorer_seed),
        "scorer_epochs": int(scorer_epochs),
        "raw_model_selection": raw_selection,
        "priority_selection": priority_selected,
        "raw": raw_eval,
        "priority_residual": priority_eval,
        "hard_priority_minus_raw_observed": clean_float(float(hard_priority["observed"]) - float(hard_raw["observed"])),
        "hard_priority_beats_raw_observed": bool(float(hard_priority["observed"]) < float(hard_raw["observed"])),
        "hard_priority_closes": bool(float(hard_priority["high"]) < 0.0),
    }
    return row, eval_raw.astype(np.float64), eval_priority.astype(np.float64)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Priority Residual Seed Stability",
        "",
        "| seed | raw hard | priority hard | priority-raw | priority hard CI high | selection |",
        "|---:|---:|---:|---:|---:|---|",
    ]
    for row in report["rows"]:
        raw = row["raw"]["hard_only"]["allocation_delta"]
        priority = row["priority_residual"]["hard_only"]["allocation_delta"]
        lines.append(
            f"| {row['scorer_seed']} | {raw['observed']:.6g} | {priority['observed']:.6g} | "
            f"{row['hard_priority_minus_raw_observed']:.6g} | {priority['high']:.6g} | `{row['priority_selection']}` |"
        )
    summary = report["summary"]
    lines.extend(
        [
            "",
            "## Summary",
            "",
            f"- priority beats raw fraction: `{summary['priority_beats_raw_fraction']:.6g}`",
            f"- priority closes fraction: `{summary['priority_closes_fraction']:.6g}`",
            "",
            "## Verdict",
            "",
            report["verdict"],
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Replicate priority-residual movement across scorer seeds")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", default="659,761,863")
    parser.add_argument("--scorer-epochs", type=int, default=60)
    parser.add_argument("--eval-seed", type=int, default=701)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    seeds = [int(part.strip()) for part in str(args.seeds).split(",") if part.strip()]
    rows: list[dict[str, Any]] = []
    raw_scores: list[np.ndarray] = []
    priority_scores: list[np.ndarray] = []
    for idx, seed in enumerate(seeds):
        row, raw_score, priority_score = one_seed(
            data,
            latents,
            train,
            cal,
            eval_split,
            hard_episodes,
            scorer_seed=seed,
            scorer_epochs=int(args.scorer_epochs),
            eval_seed=int(args.eval_seed) + idx * 1000,
        )
        rows.append(row)
        raw_scores.append(raw_score)
        priority_scores.append(priority_score)
    beats = [bool(row["hard_priority_beats_raw_observed"]) for row in rows]
    closes = [bool(row["hard_priority_closes"]) for row in rows]
    hard_priority = np.asarray([float(row["priority_residual"]["hard_only"]["allocation_delta"]["observed"]) for row in rows], dtype=np.float64)
    hard_raw = np.asarray([float(row["raw"]["hard_only"]["allocation_delta"]["observed"]) for row in rows], dtype=np.float64)
    summary = {
        "seed_count": int(len(rows)),
        "priority_beats_raw_fraction": clean_float(float(np.mean(beats))) if rows else 0.0,
        "priority_closes_fraction": clean_float(float(np.mean(closes))) if rows else 0.0,
        "hard_priority_observed_mean": clean_float(float(np.mean(hard_priority))) if rows else 0.0,
        "hard_raw_observed_mean": clean_float(float(np.mean(hard_raw))) if rows else 0.0,
        "hard_priority_minus_raw_mean": clean_float(float(np.mean(hard_priority - hard_raw))) if rows else 0.0,
    }
    if summary["priority_closes_fraction"] >= 1.0:
        verdict = "Priority residual closes the hard-only slice across all scorer seeds under this diagnostic; independent export validation is required."
    elif summary["priority_beats_raw_fraction"] >= 2.0 / 3.0:
        verdict = "Priority residual movement is seed-replicated by observed hard-only improvement, but hard intervals remain open."
    else:
        verdict = "Priority residual hard-only movement is not seed-stable relative to raw geometry-option scores."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_priority_residual_seed_stability",
        "config": {"seeds": seeds, "scorer_epochs": int(args.scorer_epochs), "eval_seed": int(args.eval_seed)},
        "rows": rows,
        "summary": summary,
        "verdict": verdict,
        "leakage_attestation": {
            "raw_score": "fi-064 geometry-option scorer is regenerated independently per seed",
            "priority_score": "budget-priority residual is trained on train targets and selected on calibration exact-budget allocation per seed",
            "eval_targets": "eval option_error is used only after each score is fixed",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        raw_scores=np.stack(raw_scores, axis=0).astype(np.float64),
        priority_scores=np.stack(priority_scores, axis=0).astype(np.float64),
        scorer_seeds=np.asarray(seeds, dtype=np.int64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

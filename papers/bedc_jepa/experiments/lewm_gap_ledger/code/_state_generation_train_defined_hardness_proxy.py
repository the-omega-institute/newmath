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
DEFAULT_JSON = REPORT_DIR / "state_generation_train_defined_hardness_proxy.json"
DEFAULT_MD = REPORT_DIR / "state_generation_train_defined_hardness_proxy.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_train_defined_hardness_proxy_predictions.npz"
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


def masks_from_train(train_env: np.ndarray, env: np.ndarray, score: np.ndarray, train_score: np.ndarray) -> dict[str, np.ndarray]:
    y_low = float(np.quantile(train_env[:, 3].astype(np.float64), 0.30))
    y_high = float(np.quantile(train_env[:, 3].astype(np.float64), 0.70))
    spread_hi = float(np.quantile(np.std(train_score.astype(np.float64), axis=1), 0.70))
    spread_lo = float(np.quantile(np.std(train_score.astype(np.float64), axis=1), 0.30))
    env_y = env[:, 3].astype(np.float64)
    diff_room = env[:, 9].astype(np.float64) >= 0.5
    spread = np.std(score.astype(np.float64), axis=1)
    return {
        "low_y": env_y <= y_low,
        "high_y": env_y >= y_high,
        "different_room": diff_room,
        "low_y_different_room": (env_y <= y_low) & diff_room,
        "low_spread": spread <= spread_lo,
        "high_spread": spread >= spread_hi,
    }


def mix_by_mask(raw: np.ndarray, priority: np.ndarray, mask: np.ndarray, use_priority_inside: bool) -> np.ndarray:
    out = raw.astype(np.float64).copy()
    mask = mask.astype(bool)
    if use_priority_inside:
        out[mask] = priority[mask]
    else:
        out[:] = priority.astype(np.float64)
        out[mask] = raw[mask]
    return out


def make_candidates(
    train_env: np.ndarray,
    cal_env: np.ndarray,
    eval_env: np.ndarray,
    train_raw: np.ndarray,
    cal_raw: np.ndarray,
    cal_priority: np.ndarray,
    eval_raw: np.ndarray,
    eval_priority: np.ndarray,
) -> list[tuple[str, np.ndarray, np.ndarray]]:
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [
        ("raw_geometry_option", cal_raw, eval_raw),
        ("priority_residual", cal_priority, eval_priority),
    ]
    cal_masks = masks_from_train(train_env, cal_env, cal_priority, train_raw)
    eval_masks = masks_from_train(train_env, eval_env, eval_priority, train_raw)
    for name in sorted(cal_masks):
        candidates.append(
            (
                f"priority_inside_{name}",
                mix_by_mask(cal_raw, cal_priority, cal_masks[name], True),
                mix_by_mask(eval_raw, eval_priority, eval_masks[name], True),
            )
        )
        candidates.append(
            (
                f"raw_inside_{name}",
                mix_by_mask(cal_raw, cal_priority, cal_masks[name], False),
                mix_by_mask(eval_raw, eval_priority, eval_masks[name], False),
            )
        )
    return candidates


def select_candidate(cal_split: dict[str, np.ndarray], candidates: list[tuple[str, np.ndarray, np.ndarray]], *, seed: int) -> tuple[str, np.ndarray, dict[str, Any]]:
    best_name = ""
    best_eval: np.ndarray | None = None
    best_key = (float("inf"), float("inf"))
    rows: dict[str, Any] = {}
    for idx, (name, cal_score, eval_score) in enumerate(candidates):
        metrics = episode_alloc.evaluate(cal_split, cal_score.astype(np.float64), seed=seed + idx)
        rows[name] = metrics
        delta = metrics["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        if key < best_key:
            best_key = key
            best_name = name
            best_eval = eval_score.astype(np.float64)
    if best_eval is None:
        raise RuntimeError("no candidate selected")
    return best_name, best_eval, {"selection_key": list(best_key), "calibration": rows}


def slice_eval(split: dict[str, np.ndarray], score: np.ndarray, mask: np.ndarray, *, seed: int) -> dict[str, Any]:
    local = geometry_alloc.slice_eval(split, mask.astype(bool))
    local_score = score[mask.astype(bool)].astype(np.float64)
    out = structured.evaluate_scores(local, local_score, seed=seed)
    out["pair_accuracy"] = episode_alloc.pair_accuracy(local_score, local["option_error"])
    out["oracle_match"] = episode_alloc.oracle_match(local_score, episode_alloc.oracle_choice(local))
    return out


def evaluate_rows(eval_split: dict[str, np.ndarray], rows: dict[str, np.ndarray], hard_episodes: list[int], *, seed: int) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    out: dict[str, Any] = {}
    for row_idx, (name, score) in enumerate(rows.items()):
        out[name] = {
            slice_name: slice_eval(eval_split, score, mask, seed=seed + 101 * row_idx + 17 * slice_idx)
            for slice_idx, (slice_name, mask) in enumerate(masks.items())
        }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Train-Defined Hardness Proxy",
        "",
        f"- selected proxy: `{report['selection']['selected']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in ["selected_proxy", "priority_residual", "raw_geometry_option"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | {hard['observed']:.6g} | {hard['high']:.6g} |")
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate train-defined hardness proxies for choosing raw vs priority residual scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=711)
    parser.add_argument("--scorer-seed", type=int, default=659)
    parser.add_argument("--scorer-epochs", type=int, default=60)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    train_raw, cal_raw, eval_raw, raw_selection, raw_feature_dims = priority_residual.regenerate_geometry_option_scores(
        data,
        latents,
        train,
        cal,
        eval_split,
        seed=int(args.scorer_seed),
        epochs=int(args.scorer_epochs),
        hidden=384,
        depth=2,
        batch=512,
        lr=6.0e-4,
    )
    train_env = geometry_alloc.env_feature_matrix(data, latents, "train")
    cal_env = geometry_alloc.env_feature_matrix(data, latents, "calibration")
    eval_env = geometry_alloc.env_feature_matrix(data, latents, "eval")
    _train_priority, cal_priority, eval_priority, priority_selected = episode_value.priority_scores(
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
        seed=int(args.seed) + 1000,
    )
    candidates = make_candidates(train_env, cal_env, eval_env, train_raw, cal_raw, cal_priority, eval_raw, eval_priority)
    selected, selected_eval, selection = select_candidate(cal, candidates, seed=int(args.seed) + 2000)
    rows = {
        "selected_proxy": selected_eval.astype(np.float64),
        "priority_residual": eval_priority.astype(np.float64),
        "raw_geometry_option": eval_raw.astype(np.float64),
    }
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 3000)
    hard_selected = eval_rows["selected_proxy"]["hard_only"]["allocation_delta"]
    hard_priority = eval_rows["priority_residual"]["hard_only"]["allocation_delta"]
    hard_raw = eval_rows["raw_geometry_option"]["hard_only"]["allocation_delta"]
    beats_priority = float(hard_selected["observed"]) < float(hard_priority["observed"])
    beats_raw = float(hard_selected["observed"]) < float(hard_raw["observed"])
    hard_closes = float(hard_selected["high"]) < 0.0
    if hard_closes:
        verdict = "Train-defined hardness proxy closes the hard-only allocation slice under this diagnostic; independent validation is required."
    elif beats_priority:
        verdict = "Train-defined hardness proxy improves over the priority-residual hard-only movement, but the hard interval remains open."
    elif beats_raw:
        verdict = "Train-defined hardness proxy improves over raw geometry-option scores but does not beat priority residual."
    else:
        verdict = "Train-defined hardness proxy does not improve the hard-only allocation boundary over raw geometry-option scores."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_train_defined_hardness_proxy",
        "config": {"seed": int(args.seed), "scorer_seed": int(args.scorer_seed), "scorer_epochs": int(args.scorer_epochs), "candidate_count": int(len(candidates))},
        "raw_model_selection": raw_selection,
        "raw_feature_dims": raw_feature_dims,
        "priority_selection": priority_selected,
        "selection": {"selected": selected, **selection},
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_priority_residual_observed": bool(beats_priority),
            "hard_beats_raw_geometry_option_observed": bool(beats_raw),
            "hard_closes": bool(hard_closes),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "raw_score": "fi-064 geometry-option scorer is regenerated deterministically",
            "priority_score": "budget-priority residual is trained on train targets and selected on calibration exact-budget allocation",
            "proxy_selection": "raw-vs-priority proxy is selected on calibration exact-budget allocation only",
            "proxy_definitions": "thresholds are defined from train environment/score statistics, not held-out hard ids",
            "eval_targets": "eval option_error is used only after all scores are fixed",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure unless hard CI high < 0", "deployable policy", "independent export validation"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        selected_proxy_score=selected_eval.astype(np.float64),
        priority_residual_score=eval_priority.astype(np.float64),
        raw_geometry_option_score=eval_raw.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

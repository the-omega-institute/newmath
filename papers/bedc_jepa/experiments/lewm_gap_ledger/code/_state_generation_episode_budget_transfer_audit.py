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


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_PRED = REPORT_DIR / "state_generation_residual_benefit_selector_predictions.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_budget_transfer_audit.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_budget_transfer_audit.md"
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


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    out: list[np.ndarray] = []
    for ep in np.unique(episode.astype(np.int64)):
        out.append(np.flatnonzero(episode.astype(np.int64) == int(ep)).astype(np.int64))
    return out


def selected_error(option_error: np.ndarray, choice: np.ndarray) -> np.ndarray:
    return option_error[np.arange(len(choice)), choice.astype(np.int64)].astype(np.float64)


def exact_budget_choice_at_multiplier(
    episode: np.ndarray,
    option_score: np.ndarray,
    depths: np.ndarray,
    multiplier: int,
) -> np.ndarray:
    chosen = np.zeros(len(episode), dtype=np.int64)
    for idxs in episode_groups(episode.astype(np.int64)):
        idxs = idxs.astype(np.int64)
        n = len(idxs)
        target = int(multiplier * n)
        dp = np.full((n + 1, target + 1), np.inf, dtype=np.float64)
        prev_budget = np.full((n + 1, target + 1), -1, dtype=np.int64)
        prev_choice = np.full((n + 1, target + 1), -1, dtype=np.int64)
        dp[0, 0] = 0.0
        for row, item in enumerate(idxs):
            for budget in range(target + 1):
                base = dp[row, budget]
                if not math.isfinite(float(base)):
                    continue
                for col, depth in enumerate(depths.astype(np.int64)):
                    new_budget = budget + int(depth)
                    if new_budget > target:
                        continue
                    value = base + float(option_score[item, col])
                    if value < dp[row + 1, new_budget]:
                        dp[row + 1, new_budget] = value
                        prev_budget[row + 1, new_budget] = budget
                        prev_choice[row + 1, new_budget] = col
        if not math.isfinite(float(dp[n, target])):
            raise RuntimeError(f"exact budget assignment is infeasible for multiplier {multiplier}")
        budget = target
        for row in range(n, 0, -1):
            col = int(prev_choice[row, budget])
            if col < 0:
                raise RuntimeError("broken exact budget traceback")
            chosen[idxs[row - 1]] = col
            budget = int(prev_budget[row, budget])
    return chosen


def episode_rows(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    mask: np.ndarray,
    multiplier: int,
) -> list[dict[str, Any]]:
    local_episode = split["episode"].astype(np.int64)[mask.astype(bool)]
    option_error = split["option_error"].astype(np.float64)[mask.astype(bool)]
    local_score = score.astype(np.float64)[mask.astype(bool)]
    depths = structured.DEPTHS.astype(np.int64)
    uniform_col = int(np.where(depths == int(multiplier))[0][0])
    chosen = exact_budget_choice_at_multiplier(local_episode, local_score, depths, int(multiplier))
    chosen_error = selected_error(option_error, chosen)
    uniform_error = option_error[:, uniform_col].astype(np.float64)
    chosen_depth = depths[chosen].astype(np.float64)
    rows: list[dict[str, Any]] = []
    for ep in np.unique(local_episode):
        idx = np.flatnonzero(local_episode == int(ep))
        selected_rate = float(np.sum(chosen_error[idx]) / np.sum(chosen_depth[idx]))
        uniform_rate = float(np.sum(uniform_error[idx]) / (float(multiplier) * len(idx)))
        rows.append(
            {
                "episode": int(ep),
                "anchors": int(len(idx)),
                "selected_minus_uniform": clean_float(selected_rate - uniform_rate),
                "selected_rate": clean_float(selected_rate),
                "uniform_rate": clean_float(uniform_rate),
                "chosen_depth_counts": {
                    str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen[idx]], return_counts=True))
                },
            }
        )
    rows.sort(key=lambda item: int(item["episode"]))
    return rows


def bootstrap_episode_mean(rows: list[dict[str, Any]], *, seed: int, samples: int) -> dict[str, Any]:
    values = np.asarray([float(row["selected_minus_uniform"]) for row in rows], dtype=np.float64)
    if len(values) == 0:
        return {"observed": 0.0, "low": 0.0, "high": 0.0, "samples": 0}
    observed = float(np.mean(values))
    rng = np.random.default_rng(int(seed))
    boot = np.zeros(int(samples), dtype=np.float64)
    for i in range(int(samples)):
        idx = rng.integers(0, len(values), size=len(values))
        boot[i] = float(np.mean(values[idx]))
    return {
        "observed": clean_float(observed),
        "low": clean_float(float(np.quantile(boot, 0.025))),
        "high": clean_float(float(np.quantile(boot, 0.975))),
        "samples": int(samples),
        "episode_count": int(len(values)),
        "positive_episode_fraction": clean_float(float(np.mean(values > 0.0))),
    }


def summarize_row(
    split: dict[str, np.ndarray],
    score: np.ndarray,
    masks: dict[str, np.ndarray],
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for multiplier in (2, 3, 4):
        budget_key = f"budget_{multiplier}"
        out[budget_key] = {}
        for slice_index, (slice_name, mask) in enumerate(masks.items()):
            rows = episode_rows(split, score, mask, multiplier)
            ci = bootstrap_episode_mean(rows, seed=seed + 1009 * multiplier + 37 * slice_index, samples=samples)
            worst = sorted(rows, key=lambda item: float(item["selected_minus_uniform"]), reverse=True)[:5]
            out[budget_key][slice_name] = {
                "episode_bootstrap_delta": ci,
                "top_harmful_episodes": worst,
            }
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Episode Budget-Transfer Audit",
        "",
        "| scorer | budget | hard observed | hard CI high | hard positive episode fraction | non-hard observed |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for scorer in ["benefit_selector", "priority_residual", "raw_geometry_option"]:
        for budget in ["budget_2", "budget_3", "budget_4"]:
            row = report["rows"][scorer][budget]
            hard = row["hard_only"]["episode_bootstrap_delta"]
            non_hard = row["non_hard"]["episode_bootstrap_delta"]
            lines.append(
                f"| `{scorer}` | `{budget}` | {hard['observed']:.6g} | {hard['high']:.6g} | "
                f"{hard['positive_episode_fraction']:.6g} | {non_hard['observed']:.6g} |"
            )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit episode-level budget-magnitude transfer for fixed allocation scores")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--predictions", default=str(DEFAULT_PRED))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=733)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    pred = load_npz(Path(args.predictions))
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    score_fields = {
        "benefit_selector": "benefit_selector_score",
        "priority_residual": "priority_residual_score",
        "raw_geometry_option": "raw_geometry_option_score",
    }
    rows = {
        name: summarize_row(
            eval_split,
            pred[field].astype(np.float64),
            masks,
            seed=int(args.seed) + index * 10000,
            samples=int(args.bootstrap_samples),
        )
        for index, (name, field) in enumerate(score_fields.items())
    }
    priority_hard_b3 = rows["priority_residual"]["budget_3"]["hard_only"]["episode_bootstrap_delta"]
    raw_hard_b3 = rows["raw_geometry_option"]["budget_3"]["hard_only"]["episode_bootstrap_delta"]
    benefit_hard_b3 = rows["benefit_selector"]["budget_3"]["hard_only"]["episode_bootstrap_delta"]
    priority_budget_closed = all(
        float(rows["priority_residual"][f"budget_{budget}"]["hard_only"]["episode_bootstrap_delta"]["high"]) < 0.0
        for budget in (2, 3, 4)
    )
    priority_observed_improves_raw_b3 = float(priority_hard_b3["observed"]) < float(raw_hard_b3["observed"])
    benefit_observed_improves_priority_b3 = float(benefit_hard_b3["observed"]) < float(priority_hard_b3["observed"])
    if priority_budget_closed:
        verdict = "Priority-residual score closes the hard episode-level budget-transfer audit across tested budget magnitudes; independent export validation is required."
    elif priority_observed_improves_raw_b3:
        verdict = "Priority-residual score improves the hard budget-3 episode mean over raw scores, but episode-level budget-transfer intervals remain open."
    else:
        verdict = "Priority-residual score does not improve the hard budget-3 episode mean over raw scores under this episode-level audit."
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_budget_transfer_audit",
        "config": {
            "seed": int(args.seed),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": [2, 3, 4],
            "score_source": str(Path(args.predictions)),
        },
        "hard_episode_union": hard_episodes,
        "rows": rows,
        "diagnosis": {
            "priority_budget_transfer_closes": bool(priority_budget_closed),
            "priority_hard_budget3_observed_improves_raw": bool(priority_observed_improves_raw_b3),
            "benefit_hard_budget3_observed_improves_priority": bool(benefit_observed_improves_priority_b3),
            "priority_hard_budget3_observed": clean_float(float(priority_hard_b3["observed"])),
            "priority_hard_budget3_high": clean_float(float(priority_hard_b3["high"])),
            "raw_hard_budget3_observed": clean_float(float(raw_hard_b3["observed"])),
            "raw_hard_budget3_high": clean_float(float(raw_hard_b3["high"])),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "scores": "fixed eval scores from residual-benefit selector artifact are consumed without retraining",
            "budget_stress": "budget multipliers are fixed before evaluation",
            "eval_targets": "eval option_error is used only for post-hoc episode bootstrap metrics",
            "hard_ids": "held-out hard episode ids are used only for final diagnostic slicing",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure unless every tested hard budget CI high < 0", "deployable policy", "independent export validation"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

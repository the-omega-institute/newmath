from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_regime_descriptors.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_regime_descriptors.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BOOTSTRAPS = 5000


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
    return [np.where(episode == ep)[0].astype(np.int64) for ep in np.unique(episode.astype(np.int64))]


def read_hard_episodes(path: Path) -> list[int]:
    report = json.loads(path.read_text(encoding="utf-8"))
    episodes = report.get("hard_episode_union", [])
    if not isinstance(episodes, list) or not episodes:
        raise RuntimeError("missing hard episode union")
    return [int(item) for item in episodes]


def load_score_rows() -> tuple[dict[str, np.ndarray], dict[str, np.ndarray]]:
    best_seed = load_npz(REPORT_DIR / "state_generation_episode_allocation_seed_617_predictions.npz")
    rows: dict[str, np.ndarray] = {
        "episode_best_seed": best_seed["episode_allocation_score"].astype(np.float64),
        "episode_objective": load_npz(REPORT_DIR / "state_generation_episode_allocation_predictions.npz")[
            "episode_allocation_score"
        ].astype(np.float64),
        "seed_mean": load_npz(REPORT_DIR / "state_generation_episode_seed_ensemble_predictions.npz")[
            "mean_score"
        ].astype(np.float64),
        "episode_balanced": load_npz(REPORT_DIR / "state_generation_episode_balanced_predictions.npz")[
            "episode_balanced_score"
        ].astype(np.float64),
        "episode_regret": load_npz(REPORT_DIR / "state_generation_episode_regret_predictions.npz")[
            "episode_regret_score"
        ].astype(np.float64),
        "episode_dual_price": load_npz(REPORT_DIR / "state_generation_episode_dual_price_predictions.npz")[
            "dual_price_score"
        ].astype(np.float64),
    }
    return best_seed, rows


def score_margin(score: np.ndarray) -> np.ndarray:
    ordered = np.sort(score.astype(np.float64), axis=1)
    return (ordered[:, 1] - ordered[:, 0]).astype(np.float64)


def score_entropy(score: np.ndarray) -> np.ndarray:
    shifted = -(score.astype(np.float64) - np.min(score.astype(np.float64), axis=1, keepdims=True))
    shifted -= np.max(shifted, axis=1, keepdims=True)
    prob = np.exp(shifted)
    prob /= np.sum(prob, axis=1, keepdims=True)
    return (-np.sum(prob * np.log(np.maximum(prob, 1.0e-12)), axis=1)).astype(np.float64)


def score_spread(score: np.ndarray) -> np.ndarray:
    return np.std(score.astype(np.float64), axis=1).astype(np.float64)


def pair_disagreement(rows: dict[str, np.ndarray]) -> tuple[np.ndarray, np.ndarray]:
    choices = np.vstack([np.argmin(score.astype(np.float64), axis=1) for score in rows.values()]).T.astype(np.int64)
    exact = np.zeros(len(choices), dtype=np.float64)
    majority = np.zeros(len(choices), dtype=np.float64)
    for i, local in enumerate(choices):
        _, counts = np.unique(local, return_counts=True)
        majority[i] = 1.0 - float(np.max(counts)) / float(len(local))
        disagree = 0
        total = 0
        for a in range(len(local)):
            for b in range(a + 1, len(local)):
                disagree += int(local[a] != local[b])
                total += 1
        exact[i] = float(disagree) / float(total)
    return exact, majority


def assignment_flip_rate(base: dict[str, np.ndarray], rows: dict[str, np.ndarray]) -> np.ndarray:
    choices = []
    episode = base["episode"].astype(np.int64)
    for score in rows.values():
        choices.append(structured.exact_budget_choice(episode, score.astype(np.float64), structured.DEPTHS).astype(np.int64))
    matrix = np.vstack(choices).T.astype(np.int64)
    flip = np.zeros(len(matrix), dtype=np.float64)
    for i, local in enumerate(matrix):
        _, counts = np.unique(local, return_counts=True)
        flip[i] = 1.0 - float(np.max(counts)) / float(len(local))
    return flip


def rollout_descriptors(pred_z: np.ndarray, valid: np.ndarray) -> dict[str, np.ndarray]:
    z = pred_z.astype(np.float64)
    mask = valid.astype(bool)
    step = np.diff(z, axis=1)
    step_norm = np.linalg.norm(step, axis=2)
    step_valid = mask[:, 1:] & mask[:, :-1]
    accel = np.diff(step, axis=1)
    accel_norm = np.linalg.norm(accel, axis=2)
    accel_valid = step_valid[:, 1:] & step_valid[:, :-1]
    def masked_mean(values: np.ndarray, local_mask: np.ndarray) -> np.ndarray:
        denom = np.maximum(1, np.sum(local_mask, axis=1))
        return np.sum(np.where(local_mask, values, 0.0), axis=1) / denom
    def masked_max(values: np.ndarray, local_mask: np.ndarray) -> np.ndarray:
        return np.max(np.where(local_mask, values, 0.0), axis=1)
    return {
        "rollout_step_norm_mean": masked_mean(step_norm, step_valid),
        "rollout_step_norm_max": masked_max(step_norm, step_valid),
        "rollout_curvature_mean": masked_mean(accel_norm, accel_valid),
        "rollout_curvature_max": masked_max(accel_norm, accel_valid),
        "rollout_valid_fraction": np.mean(mask.astype(np.float64), axis=1),
    }


def episode_mean(values: np.ndarray, episode: np.ndarray) -> dict[int, float]:
    out: dict[int, float] = {}
    for idxs in episode_groups(episode):
        out[int(episode[idxs[0]])] = clean_float(float(np.mean(values[idxs].astype(np.float64))))
    return out


def episode_quantile(values: np.ndarray, episode: np.ndarray, q: float) -> dict[int, float]:
    out: dict[int, float] = {}
    for idxs in episode_groups(episode):
        out[int(episode[idxs[0]])] = clean_float(float(np.percentile(values[idxs].astype(np.float64), q)))
    return out


def episode_descriptor_table(
    data: dict[str, np.ndarray],
    base: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
) -> dict[str, dict[int, float]]:
    episode = base["episode"].astype(np.int64)
    best = rows["episode_best_seed"].astype(np.float64)
    exact_disagree, majority_disagree = pair_disagreement(rows)
    flip = assignment_flip_rate(base, rows)
    rollout = rollout_descriptors(data["eval_pred_z"], data["eval_pred_z_valid"])
    descriptors: dict[str, np.ndarray] = {
        "best_seed_score_margin_mean": score_margin(best),
        "best_seed_score_entropy_mean": score_entropy(best),
        "best_seed_score_spread_mean": score_spread(best),
        "row_argmin_pair_disagreement_mean": exact_disagree,
        "row_argmin_majority_disagreement_mean": majority_disagree,
        "exact_budget_assignment_flip_mean": flip,
    }
    descriptors.update(rollout)
    table: dict[str, dict[int, float]] = {}
    for name, values in descriptors.items():
        table[name] = episode_mean(values, episode)
    table["best_seed_margin_p10"] = episode_quantile(score_margin(best), episode, 10)
    table["assignment_flip_p90"] = episode_quantile(flip, episode, 90)
    return table


def percentile_rank(samples: np.ndarray, observed: float, *, higher: bool) -> float:
    if higher:
        return clean_float(float((np.sum(samples >= observed) + 1.0) / (len(samples) + 1.0)))
    return clean_float(float((np.sum(samples <= observed) + 1.0) / (len(samples) + 1.0)))


def hard_gap_test(
    descriptor: dict[int, float],
    hard: set[int],
    *,
    seed: int,
    higher: bool,
) -> dict[str, Any]:
    eps = np.asarray(sorted(descriptor), dtype=np.int64)
    values = np.asarray([descriptor[int(ep)] for ep in eps], dtype=np.float64)
    hard_mask = np.asarray([int(ep) in hard for ep in eps], dtype=bool)
    observed = clean_float(float(np.mean(values[hard_mask]) - np.mean(values[~hard_mask])))
    rng = np.random.default_rng(seed)
    n_hard = int(np.sum(hard_mask))
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    all_idx = np.arange(len(eps))
    for i in range(BOOTSTRAPS):
        pick = rng.choice(all_idx, size=n_hard, replace=False)
        mask = np.zeros(len(eps), dtype=bool)
        mask[pick] = True
        samples[i] = float(np.mean(values[mask]) - np.mean(values[~mask]))
    return {
        "hard_mean": clean_float(float(np.mean(values[hard_mask]))),
        "non_hard_mean": clean_float(float(np.mean(values[~hard_mask]))),
        "hard_minus_non_hard": observed,
        "permutation_p": percentile_rank(samples, observed, higher=higher),
        "direction": "higher" if higher else "lower",
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard-Regime Descriptors",
        "",
        f"- hard episodes: `{report['hard_episode_union']}`",
        f"- strongest descriptor: `{report['summary']['strongest_descriptor']}`",
        f"- strongest p: `{report['summary']['strongest_permutation_p']:.6g}`",
        "",
        "| descriptor | direction | hard mean | non-hard mean | gap | p |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for name, row in report["descriptor_tests"].items():
        lines.append(
            f"| `{name}` | {row['direction']} | {row['hard_mean']:.6g} | {row['non_hard_mean']:.6g} | "
            f"{row['hard_minus_non_hard']:.6g} | {row['permutation_p']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose hard episodes using fixed scorer and rollout regime descriptors")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--seed", type=int, default=9060)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    base, rows = load_score_rows()
    hard_episodes = read_hard_episodes(Path(args.hard_diagnostic))
    hard = set(hard_episodes)
    descriptors = episode_descriptor_table(data, base, rows)
    directions = {
        "best_seed_score_margin_mean": False,
        "best_seed_margin_p10": False,
        "best_seed_score_entropy_mean": True,
        "best_seed_score_spread_mean": True,
        "row_argmin_pair_disagreement_mean": True,
        "row_argmin_majority_disagreement_mean": True,
        "exact_budget_assignment_flip_mean": True,
        "assignment_flip_p90": True,
        "rollout_step_norm_mean": True,
        "rollout_step_norm_max": True,
        "rollout_curvature_mean": True,
        "rollout_curvature_max": True,
        "rollout_valid_fraction": False,
    }
    tests = {
        name: hard_gap_test(values, hard, seed=args.seed + idx * 17, higher=directions[name])
        for idx, (name, values) in enumerate(descriptors.items())
    }
    strongest_name = min(tests, key=lambda name: float(tests[name]["permutation_p"]))
    strongest = tests[strongest_name]
    decision_boundary_names = [
        "best_seed_score_margin_mean",
        "best_seed_margin_p10",
        "row_argmin_pair_disagreement_mean",
        "exact_budget_assignment_flip_mean",
        "assignment_flip_p90",
    ]
    boundary_hits = [
        name
        for name in decision_boundary_names
        if float(tests[name]["permutation_p"]) <= 0.10
    ]
    verdict = (
        "Fixed scorer decision-boundary descriptors separate the recurring hard episodes at diagnostic strength; "
        "this supports perturbation or margin-aware regime objectives rather than simple coverage reweighting."
        if boundary_hits
        else "The tested fixed scorer and rollout descriptors do not strongly separate the recurring hard episodes; "
        "the next route needs richer causal perturbations or environment-state descriptors."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_regime_descriptors",
        "hard_episode_union": hard_episodes,
        "descriptor_tests": tests,
        "summary": {
            "strongest_descriptor": strongest_name,
            "strongest_permutation_p": strongest["permutation_p"],
            "decision_boundary_hit_count": int(len(boundary_hits)),
            "decision_boundary_hits": boundary_hits,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "descriptor_features": "fixed scorer outputs, scorer disagreement, exact-budget assignment disagreement, and predicted rollout geometry",
            "descriptor_fit": "no descriptor is fit to hard episode ids; hard ids are used only after descriptor construction for diagnostic permutation tests",
            "targets_not_used_for_descriptor": ["option_error", "true_mv", "horizon_y", "next_target"],
            "diagnostic_labels": "option_error is used only inside already-fixed exact-budget assignments and not to construct descriptor thresholds",
        },
        "not_claimed": ["allocation closure", "deployable policy", "hard-regime training result"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_global_assignment_transfer as global_transfer
import _state_generation_hard_regime_descriptors as regime_desc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_transfer_mechanism.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_transfer_mechanism.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
TRANSFER_JSON = REPORT_DIR / "state_generation_global_assignment_transfer.json"
TRANSFER_PRED = REPORT_DIR / "state_generation_global_assignment_transfer_predictions.npz"
BUDGETS = np.asarray([2, 3, 4], dtype=np.int64)


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


def selected_minus_oracle_by_episode(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], depths: np.ndarray) -> dict[int, float]:
    episode = split["episode"].astype(np.int64)
    option_error = split["option_error"].astype(np.float64)
    out: dict[int, list[float]] = {int(ep): [] for ep in np.unique(episode)}
    for budget in BUDGETS.astype(np.int64):
        chosen = budget_audit.exact_budget_choice_at_multiplier(episode, scores[int(budget)], depths, int(budget))
        oracle = budget_audit.exact_budget_choice_at_multiplier(episode, option_error, depths, int(budget))
        chosen_error = option_error[np.arange(len(chosen)), chosen]
        oracle_error = option_error[np.arange(len(oracle)), oracle]
        chosen_steps = depths[chosen].astype(np.float64)
        oracle_steps = depths[oracle].astype(np.float64)
        for idxs in episode_groups(episode):
            ep = int(episode[idxs[0]])
            selected_rate = float(np.sum(chosen_error[idxs]) / np.sum(chosen_steps[idxs]))
            oracle_rate = float(np.sum(oracle_error[idxs]) / np.sum(oracle_steps[idxs]))
            out[ep].append(selected_rate - oracle_rate)
    return {ep: clean_float(float(np.mean(values))) for ep, values in out.items()}


def merge_descriptors(data: dict[str, np.ndarray], split: dict[str, np.ndarray], scores: dict[int, np.ndarray]) -> dict[str, dict[int, float]]:
    rows = {
        "episode_best_seed": scores[3],
        "selected_budget2": scores[2],
        "selected_budget3": scores[3],
        "selected_budget4": scores[4],
    }
    table = regime_desc.episode_descriptor_table(data, {
        "episode": split["episode"],
        "option_error": split["option_error"],
    }, rows)
    latents = load_npz(env_desc.DEFAULT_LATENTS)
    env_rows = env_desc.anchor_env_rows(data, latents, "eval")
    env_table = env_desc.build_episode_descriptors(env_rows)
    out = {f"score_{name}": value for name, value in table.items()}
    out.update({f"env_{name}": value for name, value in env_table.items()})
    return out


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    def rank(v: np.ndarray) -> np.ndarray:
        order = np.argsort(v, kind="mergesort")
        ranks = np.zeros(len(v), dtype=np.float64)
        ranks[order] = np.arange(len(v), dtype=np.float64)
        return ranks
    rx = rank(x.astype(np.float64))
    ry = rank(y.astype(np.float64))
    if float(np.std(rx)) <= 1.0e-12 or float(np.std(ry)) <= 1.0e-12:
        return 0.0
    return clean_float(float(np.corrcoef(rx, ry)[0, 1]))


def descriptor_regret_tests(
    descriptors: dict[str, dict[int, float]],
    regret: dict[int, float],
    hard: set[int],
) -> dict[str, Any]:
    eps = np.asarray(sorted(regret), dtype=np.int64)
    y = np.asarray([regret[int(ep)] for ep in eps], dtype=np.float64)
    hard_mask = np.asarray([int(ep) in hard for ep in eps], dtype=bool)
    rows: dict[str, Any] = {}
    for name, descriptor in descriptors.items():
        x = np.asarray([descriptor[int(ep)] for ep in eps], dtype=np.float64)
        rho_all = spearman(x, y)
        rho_hard = spearman(x[hard_mask], y[hard_mask]) if int(np.sum(hard_mask)) >= 3 else 0.0
        q80 = float(np.quantile(x[~hard_mask], 0.80))
        q20 = float(np.quantile(x[~hard_mask], 0.20))
        high_mask = x >= q80
        low_mask = x <= q20
        high_regret = float(np.mean(y[high_mask])) if np.any(high_mask) else 0.0
        low_regret = float(np.mean(y[low_mask])) if np.any(low_mask) else 0.0
        rows[name] = {
            "spearman_all": clean_float(rho_all),
            "spearman_hard": clean_float(rho_hard),
            "high_minus_low_regret": clean_float(high_regret - low_regret),
            "hard_mean_descriptor": clean_float(float(np.mean(x[hard_mask]))),
            "non_hard_mean_descriptor": clean_float(float(np.mean(x[~hard_mask]))),
        }
    return rows


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard Transfer Mechanism",
        "",
        f"- selected transfer score: `{report['selected_candidate']}`",
        f"- strongest regret descriptor: `{report['summary']['strongest_regret_descriptor']}`",
        f"- strongest absolute rho: `{report['summary']['strongest_abs_spearman_all']:.6g}`",
        "",
        "| descriptor | rho all | rho hard | high-low regret | hard mean | non-hard mean |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in report["summary"]["top_descriptors"]:
        row = report["descriptor_regret_tests"][name]
        lines.append(
            f"| `{name}` | {row['spearman_all']:.6g} | {row['spearman_hard']:.6g} | "
            f"{row['high_minus_low_regret']:.6g} | {row['hard_mean_descriptor']:.6g} | {row['non_hard_mean_descriptor']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Explain global-assignment hard transfer failure using fixed non-label descriptors")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--transfer-json", default=str(TRANSFER_JSON))
    parser.add_argument("--transfer-pred", default=str(TRANSFER_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard = set(int(ep) for ep in hard_episodes)
    transfer = json.loads(Path(args.transfer_json).read_text(encoding="utf-8"))
    pred = load_npz(Path(args.transfer_pred))
    scores = {int(budget): pred[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    regret = selected_minus_oracle_by_episode(split, scores, depths)
    descriptors = merge_descriptors(data, split, scores)
    tests = descriptor_regret_tests(descriptors, regret, hard)
    ranking = sorted(tests, key=lambda name: -abs(float(tests[name]["spearman_all"])))
    strongest = ranking[0]
    top = ranking[:12]
    explanatory = bool(abs(float(tests[strongest]["spearman_all"])) >= 0.50)
    verdict = (
        "Fixed non-label descriptors show a strong association with selected-vs-oracle transfer regret; "
        "the next route should train hard-regime-aware compute-value rules on this mechanism family."
        if explanatory
        else "Fixed non-label descriptors do not strongly explain the selected-vs-oracle hard transfer regret; "
        "the next route needs richer perturbation labels rather than descriptor reweighting."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_transfer_mechanism",
        "selected_candidate": transfer["diagnosis"]["selected_candidate"],
        "hard_episode_union": hard_episodes,
        "episode_regret": regret,
        "descriptor_regret_tests": tests,
        "summary": {
            "strongest_regret_descriptor": strongest,
            "strongest_abs_spearman_all": clean_float(abs(float(tests[strongest]["spearman_all"]))),
            "strongest_spearman_all": tests[strongest]["spearman_all"],
            "top_descriptors": top,
            "descriptor_count": int(len(tests)),
            "has_strong_descriptor_explanation": explanatory,
        },
        "verdict": verdict,
        "leakage_attestation": {
            "descriptors": "fixed score geometry, score disagreement, predicted rollout geometry, and two-rooms environment state descriptors",
            "selection": "uses the already fixed fi-084 selected score; no candidate is selected with hard descriptor tests",
            "oracle_scope": "eval option_error is used only to compute selected-vs-oracle episode regret after fixed scores are generated",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "independent export validation"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

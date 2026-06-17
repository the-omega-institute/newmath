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
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_episode_diagnostic.md"
ANATOMY_JSON = REPORT_DIR / "state_generation_episode_transfer_anatomy.json"
BOOTSTRAPS = 2000


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


def depth_counts(depths: np.ndarray, chosen: np.ndarray) -> dict[str, int]:
    return {str(int(k)): int(v) for k, v in zip(*np.unique(depths[chosen], return_counts=True))}


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0].astype(np.int64) for ep in np.unique(episode.astype(np.int64))]


def slice_payload(base: dict[str, np.ndarray], mask: np.ndarray) -> dict[str, np.ndarray]:
    rows = np.where(mask.astype(bool))[0].astype(np.int64)
    return {
        "episode": base["episode"][rows].astype(np.int64),
        "option_error": base["option_error"][rows].astype(np.float64),
        "oracle_choice": base["oracle_choice"][rows].astype(np.int64),
        "option_depths": base["option_depths"].astype(np.int64),
    }


def evaluate_choice(payload: dict[str, np.ndarray], chosen: np.ndarray, *, seed: int) -> dict[str, Any]:
    depths = payload["option_depths"].astype(np.int64)
    option_error = payload["option_error"].astype(np.float64)
    episode = payload["episode"].astype(np.int64)
    mid = int(np.where(depths == 3)[0][0])
    selected_error = option_error[np.arange(len(chosen)), chosen]
    uniform_error = option_error[:, mid]
    selected_steps = depths[chosen].astype(np.float64)
    uniform_steps = np.full(len(chosen), 3.0, dtype=np.float64)
    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(selected_error[idxs])) for idxs in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(selected_steps[idxs])) for idxs in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idxs])) for idxs in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idxs])) for idxs in groups], dtype=np.float64)
    per_episode_delta = selected_ep_error / selected_ep_steps - uniform_ep_error / uniform_ep_steps
    observed = clean_float(
        float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum())
    )
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
            "observed": observed,
            "low": clean_float(float(np.percentile(samples, 2.5))),
            "high": clean_float(float(np.percentile(samples, 97.5))),
        },
        "episode_count": int(len(groups)),
        "anchor_count": int(len(chosen)),
        "positive_episode_count": int(np.sum(per_episode_delta > 0.0)),
        "negative_episode_count": int(np.sum(per_episode_delta < 0.0)),
        "mean_episode_delta": clean_float(float(np.mean(per_episode_delta))),
        "depth_counts": depth_counts(depths, chosen.astype(np.int64)),
    }


def evaluate_score_slice(
    base: dict[str, np.ndarray],
    score: np.ndarray,
    mask: np.ndarray,
    *,
    seed: int,
) -> dict[str, Any]:
    payload = slice_payload(base, mask)
    local_score = score[mask.astype(bool)].astype(np.float64)
    chosen = structured.exact_budget_choice(payload["episode"], local_score, structured.DEPTHS).astype(np.int64)
    oracle = payload["oracle_choice"].astype(np.int64)
    observed = evaluate_choice(payload, chosen, seed=seed)
    oracle_eval = evaluate_choice(payload, oracle, seed=seed + 17)
    observed["oracle_delta"] = oracle_eval["allocation_delta"]
    observed["oracle_match"] = clean_float(float(np.mean(chosen == oracle)))
    return observed


def load_rows() -> tuple[dict[str, np.ndarray], dict[str, np.ndarray]]:
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


def read_hard_episodes(path: Path) -> list[int]:
    report = json.loads(path.read_text(encoding="utf-8"))
    cross = report.get("cross_row", {}) if isinstance(report.get("cross_row"), dict) else {}
    episodes = cross.get("top_harm_union_episodes", [])
    if not isinstance(episodes, list) or not episodes:
        raise RuntimeError("missing top-harm union episodes")
    return [int(item) for item in episodes]


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard-Episode Diagnostic",
        "",
        f"- hard episode union: `{report['hard_episode_union']}`",
        f"- hard episode count: `{report['hard_episode_count']}`",
        "",
        "| row | full delta | non-hard delta | hard-only delta | non-hard CI high | hard-only CI high |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name, row in report["rows"].items():
        full = row["slices"]["full"]["allocation_delta"]
        non_hard = row["slices"]["non_hard"]["allocation_delta"]
        hard_only = row["slices"]["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard_only['observed']:.6g} | {non_hard['high']:.6g} | {hard_only['high']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Quantify allocation boundary contribution from recurring hard episodes")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--anatomy", default=str(ANATOMY_JSON))
    parser.add_argument("--seed", type=int, default=8058)
    args = parser.parse_args()
    base, rows = load_rows()
    hard_episodes = read_hard_episodes(Path(args.anatomy))
    episode = base["episode"].astype(np.int64)
    hard_mask = np.isin(episode, np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(episode), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    payload_rows: dict[str, Any] = {}
    for idx, (name, score) in enumerate(rows.items()):
        slices = {
            slice_name: evaluate_score_slice(base, score, mask, seed=args.seed + idx * 101 + slice_idx * 11)
            for slice_idx, (slice_name, mask) in enumerate(masks.items())
        }
        full_obs = float(slices["full"]["allocation_delta"]["observed"])
        non_hard_obs = float(slices["non_hard"]["allocation_delta"]["observed"])
        hard_obs = float(slices["hard_only"]["allocation_delta"]["observed"])
        payload_rows[name] = {
            "slices": slices,
            "hard_minus_non_hard_delta": clean_float(hard_obs - non_hard_obs),
            "non_hard_closes_ci": bool(float(slices["non_hard"]["allocation_delta"]["high"]) < 0.0),
            "hard_only_harmful": bool(hard_obs > 0.0),
            "full_to_non_hard_shift": clean_float(non_hard_obs - full_obs),
        }
    non_hard_closures = [bool(row["non_hard_closes_ci"]) for row in payload_rows.values()]
    hard_harm = [bool(row["hard_only_harmful"]) for row in payload_rows.values()]
    verdict = (
        "Removing the recurring hard episode union does not establish allocation closure for every row; "
        "the diagnostic supports a concentrated transfer-boundary hypothesis rather than a deployable allocator."
        if not all(non_hard_closures)
        else "The non-hard slice closes for every row under this diagnostic, while the hard-only slice remains the boundary."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_episode_diagnostic",
        "hard_episode_union": hard_episodes,
        "hard_episode_count": int(len(hard_episodes)),
        "hard_anchor_count": int(np.sum(hard_mask)),
        "non_hard_anchor_count": int(np.sum(~hard_mask)),
        "rows": payload_rows,
        "summary": {
            "row_count": int(len(payload_rows)),
            "non_hard_closure_count": int(sum(non_hard_closures)),
            "hard_only_harmful_count": int(sum(hard_harm)),
            "minimum_hard_minus_non_hard_delta": clean_float(
                float(min(row["hard_minus_non_hard_delta"] for row in payload_rows.values()))
            ),
            "maximum_full_to_non_hard_shift": clean_float(
                float(max(row["full_to_non_hard_shift"] for row in payload_rows.values()))
            ),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "held-out eval predictions and fixed episode identifiers from the prior anatomy report",
            "selection": "diagnostic slicing only; no training or model selection",
            "slurm_or_ssh": "not used",
            "targets": "eval option_error used only after fixed score generation for allocation accounting",
        },
        "not_claimed": ["allocation closure", "deployable policy", "hard episode training result"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

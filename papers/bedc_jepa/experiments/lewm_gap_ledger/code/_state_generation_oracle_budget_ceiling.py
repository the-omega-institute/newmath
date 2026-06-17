from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_episode_budget_transfer_audit as budget_audit


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_oracle_budget_ceiling.json"
DEFAULT_MD = REPORT_DIR / "state_generation_oracle_budget_ceiling.md"
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


def summarize_oracle(
    split: dict[str, np.ndarray],
    masks: dict[str, np.ndarray],
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    rows: dict[str, Any] = {}
    option_error = split["option_error"].astype(np.float64)
    for budget_index, multiplier in enumerate((2, 3, 4)):
        budget_key = f"budget_{multiplier}"
        rows[budget_key] = {}
        for slice_index, (slice_name, mask) in enumerate(masks.items()):
            episode_rows = budget_audit.episode_rows(split, option_error, mask.astype(bool), multiplier)
            ci = budget_audit.bootstrap_episode_mean(
                episode_rows,
                seed=seed + 1009 * budget_index + 37 * slice_index,
                samples=samples,
            )
            rows[budget_key][slice_name] = {
                "episode_bootstrap_delta": ci,
                "top_harmful_episodes": sorted(
                    episode_rows,
                    key=lambda item: float(item["selected_minus_uniform"]),
                    reverse=True,
                )[:5],
                "top_beneficial_episodes": sorted(
                    episode_rows,
                    key=lambda item: float(item["selected_minus_uniform"]),
                )[:5],
            }
    return rows


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Oracle Budget Ceiling",
        "",
        "| budget | hard observed | hard CI high | full observed | non-hard observed |",
        "|---|---:|---:|---:|---:|",
    ]
    for budget in ["budget_2", "budget_3", "budget_4"]:
        row = report["rows"][budget]
        hard = row["hard_only"]["episode_bootstrap_delta"]
        full = row["full"]["episode_bootstrap_delta"]
        non_hard = row["non_hard"]["episode_bootstrap_delta"]
        lines.append(
            f"| `{budget}` | {hard['observed']:.6g} | {hard['high']:.6g} | "
            f"{full['observed']:.6g} | {non_hard['observed']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Measure exact-budget oracle allocation headroom")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=947)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()
    start_time = time.time()
    data = load_npz(Path(args.export))
    eval_split = episode_alloc.load_split(data, "eval")
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    rows = summarize_oracle(eval_split, masks, seed=int(args.seed), samples=int(args.bootstrap_samples))
    hard_budget_highs = [
        float(rows[f"budget_{budget}"]["hard_only"]["episode_bootstrap_delta"]["high"])
        for budget in (2, 3, 4)
    ]
    hard_budget_observed = [
        float(rows[f"budget_{budget}"]["hard_only"]["episode_bootstrap_delta"]["observed"])
        for budget in (2, 3, 4)
    ]
    closes = all(high < 0.0 for high in hard_budget_highs)
    if closes:
        verdict = (
            "Under the same exact episode-budget constraints, the oracle option-error score has hard-slice "
            "headroom at every tested budget magnitude. The allocation mechanism is therefore not vacuous; "
            "the current failure is a learned compute-value scoring boundary."
        )
    else:
        verdict = (
            "The oracle option-error score does not close hard-slice exact-budget allocation across every "
            "tested budget magnitude, so the budget mechanism itself remains suspect."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_oracle_budget_ceiling",
        "config": {
            "seed": int(args.seed),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budget_multipliers": [2, 3, 4],
            "score_source": "eval option_error oracle used only as a ceiling diagnostic",
        },
        "hard_episode_union": hard_episodes,
        "rows": rows,
        "diagnosis": {
            "oracle_hard_budget_ceiling_closes": bool(closes),
            "hard_budget_observed": [clean_float(value) for value in hard_budget_observed],
            "hard_budget_highs": [clean_float(value) for value in hard_budget_highs],
        },
        "verdict": verdict,
        "leakage_attestation": {
            "oracle_scope": "eval option_error is used as an oracle ceiling only, not as a trainable or deployable score",
            "budget_stress": "budget multipliers are fixed before evaluation",
            "hard_ids": "held-out hard episode ids are used only for diagnostic slicing",
            "training": "no model training is performed",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "learned compute-value closure",
            "independent export validation",
            "complete BEDC-native world model",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(
        json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

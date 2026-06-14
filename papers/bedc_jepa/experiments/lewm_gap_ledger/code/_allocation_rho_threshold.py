"""How good must a ranker be to beat uniform allocation? A ρ→Δ phase curve.

The allocation bridge established that learned rankers reach within-episode
Spearman ρ≈0.43–0.51 against the true h=5 error and do not beat uniform, while
the oracle (ρ=1.0) does (Δ=−0.0159). This pins the exact threshold: synthesize
scores whose within-episode Spearman to the true error is dialed across [0,1]
(by blending the oracle ranking with episode-local noise), and measure the
allocation Δ-vs-uniform at each level. The crossing point is the ranking
quality a detector must reach for the allocation lever to pay off — turning
"ρ≈0.5 is not enough" into "you need ρ ≥ ρ*".

Protocol is reused verbatim from `_allocation_bridge`: same eval anchors, same
5/1 episode split of rollout depth, same matched budget, same uniform and
oracle definitions, same paired episode bootstrap (500, seed 314159). No model
training — fully deterministic given the blend seed grid.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import numpy as np

import _g2n_native_ledger as g2n
from _phase1c_gap_ledger import flatten_transition_rows
from _allocation_bridge import (
    BOOTSTRAP_SEED,
    CLEAN_LABELS,
    NPZ_PATH,
    PYTHON_SEED,
    SPLIT_SEED,
    TARGET_H,
    TARGET_H_INDEX,
    allocation_uniform,
    budget_eval_for_score,
    summarize_allocation,
    within_episode_spearman,
)

REPORT_DIR = Path("reports")
JSON_PATH = REPORT_DIR / "lewm_allocation_rho_threshold.json"
MD_PATH = REPORT_DIR / "lewm_allocation_rho_threshold.md"

# Noise blend grid: score = oracle_rank_z * w + noise_z * (1-w), per episode.
# Sweeping w in [0,1] traces achieved within-episode Spearman from ~0 to 1.
BLEND_GRID = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 1.0]
NOISE_SEED = 20260613


def rank_z_within_episode(values: np.ndarray, anchors_by_ep: dict[int, list[int]]) -> np.ndarray:
    """Per-episode rank, z-scored within episode (ties broken by index order)."""
    out = np.zeros(len(values), dtype=np.float64)
    for idxs in anchors_by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        v = values[idx]
        order = np.argsort(v, kind="mergesort")
        r = np.empty(len(idx), dtype=np.float64)
        r[order] = np.arange(len(idx), dtype=np.float64)
        if len(idx) > 1:
            r = (r - r.mean()) / (r.std() + 1e-12)
        out[idx] = r
    return out


def main() -> None:
    np.random.seed(PYTHON_SEED)
    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    rows = flatten_transition_rows(data)
    splits = g2n.split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(CLEAN_LABELS)
    clean_eval_ex = g2n.build_clean_examples(data, clean, "eval", None)

    valid_h5 = clean["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    errors_h5 = clean["eval_err_at_h"][valid_h5, :TARGET_H].astype(np.float64)
    true_mean_h5 = clean["eval_mean_err_to_h"][valid_h5, TARGET_H_INDEX].astype(np.float64)
    anchors_arr = clean_eval_ex["anchor_ep_t0"][valid_h5]
    anchors = [
        {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
        for i, (ep, t) in enumerate(anchors_arr)
    ]
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, a in enumerate(anchors):
        anchors_by_ep[int(a["episode"])].append(i)

    uniform_h = allocation_uniform(anchors_by_ep)
    uniform_alloc = summarize_allocation("uniform", uniform_h, errors_h5, anchors)

    # Oracle anchor: must reproduce the bridge's oracle delta.
    oracle = budget_eval_for_score("oracle", true_mean_h5.copy(), anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_delta = float(oracle["delta_vs_uniform"]["observed"])
    assert abs(oracle_delta - (-0.015867561326231905)) < 1e-9, f"oracle anchor mismatch: {oracle_delta}"

    oracle_rank_z = rank_z_within_episode(true_mean_h5, anchors_by_ep)
    rng = np.random.default_rng(NOISE_SEED)
    noise = rng.standard_normal(len(true_mean_h5))
    noise_rank_z = rank_z_within_episode(noise, anchors_by_ep)

    rows_out = []
    crossing = None
    prev = None
    for w in BLEND_GRID:
        score = w * oracle_rank_z + (1.0 - w) * noise_rank_z
        be = budget_eval_for_score(f"blend_{w:g}", score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
        sp = within_episode_spearman(score, true_mean_h5, anchors)
        d = be["delta_vs_uniform"]
        row = {
            "blend_w": float(w),
            "within_episode_spearman": sp["episode_mean"],
            "delta_vs_uniform": {
                "observed": float(d["observed"]),
                "ci95_low": float(d["ci95_low"]),
                "ci95_high": float(d["ci95_high"]),
            },
            "beats_uniform": bool(float(d["ci95_high"]) < 0.0),
        }
        rows_out.append(row)
        # crossing of observed delta from >0 to <0
        if prev is not None and prev["delta_vs_uniform"]["observed"] >= 0.0 > row["delta_vs_uniform"]["observed"]:
            crossing = {
                "between_spearman": [prev["within_episode_spearman"], row["within_episode_spearman"]],
                "between_blend_w": [prev["blend_w"], row["blend_w"]],
            }
        prev = row

    ci_positive = [r for r in rows_out if r["beats_uniform"]]
    rho_star_ci = min((r["within_episode_spearman"] for r in ci_positive), default=None)
    rho_star_point = None
    for r in rows_out:
        if r["delta_vs_uniform"]["observed"] < 0.0:
            rho_star_point = r["within_episode_spearman"]
            break

    learned_band = [0.432, 0.508]
    report = {
        "schema_id": "lewm.allocation_rho_threshold",
        "question": "what within-episode ranking quality (Spearman to true h=5 error) lets a ranker beat uniform allocation?",
        "protocol": {
            "reused_from": "_allocation_bridge (same anchors, 5/1 depth split, matched budget, uniform/oracle, paired bootstrap)",
            "bootstrap_seed": BOOTSTRAP_SEED,
            "noise_seed": NOISE_SEED,
            "blend": "score = w * oracle_rank_z + (1-w) * noise_rank_z, per episode",
            "oracle_delta_anchor": oracle_delta,
        },
        "curve": rows_out,
        "thresholds": {
            "rho_star_point_estimate_first_negative_observed": rho_star_point,
            "rho_star_ci_first_interval_below_zero": rho_star_ci,
            "observed_crossing_bracket": crossing,
        },
        "context": {
            "learned_ranker_spearman_band": learned_band,
            "learned_rankers_beat_uniform": False,
            "oracle_spearman": 1.0,
            "oracle_delta": oracle_delta,
        },
        "not_claimed": [
            "single checkpoint (tworooms), single export",
            "prediction-budget allocation, not planning/control",
            "the blend is a synthetic ranking-quality dial, not an achievable model",
        ],
    }
    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")

    lines = [
        "# Allocation ρ threshold: how good must a ranker be to beat uniform?",
        "",
        f"- oracle delta anchor: `{oracle_delta:.9f}` (reproduces allocation bridge)",
        f"- learned rankers sit at Spearman {learned_band} and do NOT beat uniform",
        f"- ρ* (first blend with observed Δ < 0): `{rho_star_point}`",
        f"- ρ* (first blend with CI entirely < 0): `{rho_star_ci}`",
        "",
        "| within-ep Spearman | blend w | Δ vs uniform | 95% CI | beats uniform |",
        "|---:|---:|---:|---:|:--:|",
    ]
    for r in rows_out:
        d = r["delta_vs_uniform"]
        lines.append(
            f"| {r['within_episode_spearman']:.3f} | {r['blend_w']:g} | {d['observed']:.6f} "
            f"| [{d['ci95_low']:.6f}, {d['ci95_high']:.6f}] | {'yes' if r['beats_uniform'] else 'no'} |"
        )
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"rho_star_point": rho_star_point, "rho_star_ci": rho_star_ci, "crossing": crossing}, indent=2))
    print(MD_PATH)


if __name__ == "__main__":
    main()

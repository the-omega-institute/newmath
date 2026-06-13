"""Robustness of the allocation ρ-threshold across noise seeds.

The ρ→Δ phase curve uses one noise realization to dial ranking quality. This
checks the crossing point ρ* is structural, not an artifact of that draw:
re-run the blend over several noise seeds and report the spread of (a) the
Spearman at which observed Δ first goes negative and (b) the Δ at the learned
band (ρ≈0.5). Same anchors / budget / bootstrap as the main curve.
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

import numpy as np

import _g2n_native_ledger as g2n
from _allocation_bridge import (
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
from _allocation_rho_threshold import BLEND_GRID, rank_z_within_episode

REPORT_DIR = Path("reports")
JSON_PATH = REPORT_DIR / "lewm_allocation_rho_robust.json"
MD_PATH = REPORT_DIR / "lewm_allocation_rho_robust.md"
NOISE_SEEDS = [20260613, 11, 101, 1701, 90210, 314159, 2718, 4060]


def main() -> None:
    np.random.seed(PYTHON_SEED)
    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
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
    oracle_rank_z = rank_z_within_episode(true_mean_h5, anchors_by_ep)

    per_seed = []
    for seed in NOISE_SEEDS:
        rng = np.random.default_rng(seed)
        noise_rank_z = rank_z_within_episode(rng.standard_normal(len(true_mean_h5)), anchors_by_ep)
        prev_rho = prev_delta = None
        first_neg_rho = None
        delta_at_half = None
        for w in BLEND_GRID:
            score = w * oracle_rank_z + (1.0 - w) * noise_rank_z
            d = float(budget_eval_for_score(f"b{w:g}", score, anchors, anchors_by_ep, errors_h5, uniform_alloc)["delta_vs_uniform"]["observed"])
            rho = within_episode_spearman(score, true_mean_h5, anchors)["episode_mean"]
            if 0.45 <= rho <= 0.55 and delta_at_half is None:
                delta_at_half = {"spearman": rho, "delta": d}
            if first_neg_rho is None and prev_delta is not None and prev_delta >= 0.0 > d:
                # linear interpolate the crossing in Spearman
                frac = prev_delta / (prev_delta - d)
                first_neg_rho = prev_rho + frac * (rho - prev_rho)
            prev_rho, prev_delta = rho, d
        per_seed.append({"noise_seed": seed, "rho_star_interp": first_neg_rho, "near_half": delta_at_half})

    rho_stars = [r["rho_star_interp"] for r in per_seed if r["rho_star_interp"] is not None]
    report = {
        "schema_id": "lewm.allocation_rho_robust",
        "question": "is the allocation ρ* threshold stable across noise realizations?",
        "noise_seeds": NOISE_SEEDS,
        "per_seed": per_seed,
        "rho_star_interpolated": {
            "mean": float(np.mean(rho_stars)),
            "min": float(np.min(rho_stars)),
            "max": float(np.max(rho_stars)),
            "std": float(np.std(rho_stars)),
        },
        "interpretation": "crossing where observed Δ goes negative, linearly interpolated in within-episode Spearman",
        "not_claimed": ["single checkpoint/export", "synthetic ranking-quality dial, not an achievable model"],
    }
    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")

    lines = [
        "# Allocation ρ* robustness across noise seeds",
        "",
        f"- ρ* interpolated: mean `{report['rho_star_interpolated']['mean']:.4f}`, "
        f"range [`{report['rho_star_interpolated']['min']:.4f}`, `{report['rho_star_interpolated']['max']:.4f}`], "
        f"std `{report['rho_star_interpolated']['std']:.4f}`",
        "",
        "| noise seed | ρ* (interp) | Δ near ρ≈0.5 |",
        "|---:|---:|---:|",
    ]
    for r in per_seed:
        nh = r["near_half"]
        nh_s = f"{nh['delta']:.6f} @ρ={nh['spearman']:.3f}" if nh else "n/a"
        rs = f"{r['rho_star_interp']:.4f}" if r["rho_star_interp"] is not None else "n/a"
        lines.append(f"| {r['noise_seed']} | {rs} | {nh_s} |")
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(report["rho_star_interpolated"], indent=2))
    print(MD_PATH)


if __name__ == "__main__":
    main()

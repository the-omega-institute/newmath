#!/usr/bin/env python3
"""Target-side P_Q permutation ceiling for the B*_Q6 readout dictionary."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
import time
from collections import Counter, defaultdict
from typing import Any

import run_b_star_q6_minimal_dictionary_compression_powered as minimal_dictionary
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import matrix_column
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM


EXPERIMENT_ID = "b_star_q6_pq_target_permutation_dictionary_ceiling_powered"
CLAIM_ID = "h3.cross_layer_relation.target_noise_ceiling.b_star_q6_pq_target_permutation_dictionary_ceiling_powered"

TARGET_PERMUTATION_COUNT = 200
SEED = 70651
ABUNDANCE_BINS = 10
CDS_LENGTH_BINS = 5
GC3_BINS = 5
TARGET_ORGANISM_KEYS = {"saccharomyces_cerevisiae"}
EPS = 1e-12


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def round_float(value: object, digits: int = 9) -> object:
    if finite_number(value):
        return round(float(value), digits)
    return value


def quantile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = hashlib.sha256(f"{material}|seed={SEED}|index={index}|n={n}".encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def bin_assignments(values_by_id: dict[str, float], bin_count: int) -> dict[str, int]:
    if not values_by_id:
        return {}
    ordered = sorted(values_by_id.items(), key=lambda item: (item[1], item[0]))
    n = len(ordered)
    out: dict[str, int] = {}
    for rank, (protein_id, _value) in enumerate(ordered):
        out[protein_id] = min(bin_count - 1, (rank * bin_count) // n)
    return out


def row_metric(row: dict[str, object], key: str) -> float:
    if key == "abundance":
        values = row.get("p")
        if isinstance(values, list) and values:
            return float(values[0])
    if key == "log_cds_length":
        values = row.get("z")
        if isinstance(values, list) and len(values) >= 2:
            return float(values[1])
    if key == "gc3":
        values = row.get("z")
        if isinstance(values, list) and len(values) >= 3:
            return float(values[-3])
    raise ValueError(f"row lacks finite {key}")


def strata_labels(rows: dict[str, dict[str, object]], base_ids: list[str]) -> tuple[dict[str, tuple[int, int, int]], dict[str, object]]:
    abundance = {protein_id: row_metric(rows[protein_id], "abundance") for protein_id in base_ids}
    log_len = {protein_id: row_metric(rows[protein_id], "log_cds_length") for protein_id in base_ids}
    gc3 = {protein_id: row_metric(rows[protein_id], "gc3") for protein_id in base_ids}
    abundance_bin = bin_assignments(abundance, ABUNDANCE_BINS)
    length_bin = bin_assignments(log_len, CDS_LENGTH_BINS)
    gc3_bin = bin_assignments(gc3, GC3_BINS)
    labels = {
        protein_id: (abundance_bin[protein_id], length_bin[protein_id], gc3_bin[protein_id])
        for protein_id in base_ids
    }
    counts = Counter(labels.values())
    sizes = sorted(counts.values())
    movable = sum(size for size in sizes if size >= 2)
    summary = {
        "matched_axes": ["protein_abundance_decile", "cds_length_quantile_bin", "gc3_quantile_bin"],
        "bin_counts": {
            "protein_abundance_decile": ABUNDANCE_BINS,
            "cds_length_bin": CDS_LENGTH_BINS,
            "gc3_bin": GC3_BINS,
        },
        "base_n": len(base_ids),
        "strata_n": len(counts),
        "singleton_strata_n": sum(1 for size in sizes if size == 1),
        "movable_rows_n": movable,
        "movable_rows_fraction": movable / len(base_ids) if base_ids else 0.0,
        "min_stratum_size": sizes[0] if sizes else 0,
        "median_stratum_size": sizes[len(sizes) // 2] if sizes else 0,
        "max_stratum_size": sizes[-1] if sizes else 0,
    }
    return labels, summary


def groups_for_row_ids(row_ids: list[str], label_by_id: dict[str, tuple[int, int, int]]) -> list[list[int]]:
    grouped: dict[tuple[int, int, int], list[int]] = defaultdict(list)
    for index, protein_id in enumerate(row_ids):
        grouped[label_by_id[protein_id]].append(index)
    return [grouped[key] for key in sorted(grouped)]


def permuted_target(target: list[float], groups: list[list[int]], material: str) -> tuple[list[float], int]:
    out = list(target)
    changed = 0
    for group_index, positions in enumerate(groups):
        if len(positions) < 2:
            continue
        order = deterministic_permutation(len(positions), f"{material}|stratum={group_index}")
        for dest_local, src_local in enumerate(order):
            dest = positions[dest_local]
            src = positions[src_local]
            out[dest] = target[src]
            if dest != src:
                changed += 1
    return out, changed


def absorption_for_target(basis: list[list[float]], target: list[float], target_norm2: float) -> float:
    if target_norm2 <= EPS or not basis:
        return 0.0
    energy = 0.0
    for q_vector in basis:
        coeff = 0.0
        for q_value, target_value in zip(q_vector, target):
            coeff += q_value * target_value
        energy += coeff * coeff
    if energy > target_norm2 and energy <= target_norm2 + 1e-8:
        energy = target_norm2
    return minimal_dictionary.bounded_unit(max(0.0, energy) / target_norm2)


def base_r2_qp(rows: dict[str, dict[str, object]], row_ids: list[str], state: dict[str, object]) -> float:
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_basis = state.get("z_basis")
    p_q_norm2 = state.get("P_Q_norm2")
    if not isinstance(z_basis, list) or not finite_number(p_q_norm2):
        return 0.0
    p_e = minimal_dictionary.residualize_with_basis(minimal_dictionary.matrix_rows(selected_rows, "p"), z_basis)
    p_norm2 = vector_norm2(matrix_column(p_e, 0))
    if p_norm2 <= EPS:
        return 0.0
    return minimal_dictionary.bounded_unit(float(p_q_norm2) / p_norm2)


def clean_candidate(item: dict[str, object]) -> dict[str, object]:
    null = item.get("null")
    null95 = 0.0
    if isinstance(null, dict) and finite_number(null.get("null95_coverage")):
        null95 = float(null["null95_coverage"])
    return {
        "D_o": item.get("D_o", []),
        "n_join": item.get("n_join"),
        "coverage": round_float(item.get("coverage")),
        "BEDC_score": round_float(item.get("BEDC_score")),
        "cost": round_float(item.get("cost")),
        "null95_coverage": round_float(null95),
    }


def observed_selection(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    organism = str(config["key"])
    built = residual_dictionary.base_rows(repo=repo, context=context, config=config)
    if built.get("status") != "computed":
        return {
            "organism": config.get("label"),
            "organism_key": organism,
            "status": "needs_data",
            "reason": built.get("reason"),
            "data_summary": built,
        }
    rows = built.get("rows")
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    attached = residual_dictionary.attach_h_readouts(repo, organism, rows)  # type: ignore[arg-type]
    base_ids = sorted(str(protein_id) for protein_id in rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "organism": config.get("label"),
            "organism_key": organism,
            "status": "needs_data",
            "reason": f"base P/Q/T/S join yielded n={len(base_ids)}, below gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "data_summary": built.get("summary"),
            "H_source_summaries": attached.get("source_summaries"),
        }
    readouts = minimal_dictionary.available_readouts(config, rows, base_ids)  # type: ignore[arg-type]
    join_cache: dict[tuple[str, ...], dict[str, object]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
    preliminary = [
        minimal_dictionary.evaluate_subset_cached(
            organism=organism,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            subset=subset,
            compute_null=False,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in minimal_dictionary.all_subsets(readouts)
    ]
    candidate_subsets = minimal_dictionary.frontier_subsets(preliminary)
    evaluated = [
        minimal_dictionary.evaluate_subset_cached(
            organism=organism,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            subset=subset,
            compute_null=True,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in candidate_subsets
    ]
    computed = [item for item in evaluated if item.get("status") == "computed"]
    if not computed:
        return {
            "organism": config.get("label"),
            "organism_key": organism,
            "status": "needs_data",
            "reason": "no readout subset passed the join gate",
            "available_readouts": readouts,
            "data_summary": built.get("summary"),
            "H_source_summaries": attached.get("source_summaries"),
        }
    best = max(computed, key=lambda item: float(item["BEDC_score"]))
    return {
        "organism": config.get("label"),
        "organism_key": organism,
        "domain": config.get("domain"),
        "status": "computed",
        "rows": rows,
        "base_ids": base_ids,
        "available_readouts": readouts,
        "preliminary_subset_count": len(preliminary),
        "matched_null_subset_count": len(computed),
        "candidate_subsets": candidate_subsets,
        "evaluated": computed,
        "best": best,
        "data_summary": built.get("summary"),
        "H_source_summaries": attached.get("source_summaries"),
        "dropped_readouts": attached.get("dropped"),
    }


def candidate_plans(
    evaluated: list[dict[str, object]],
    label_by_id: dict[str, tuple[int, int, int]],
) -> list[dict[str, object]]:
    plans: list[dict[str, object]] = []
    for item in evaluated:
        state = item.get("state")
        row_ids = item.get("row_ids")
        if not isinstance(state, dict) or not isinstance(row_ids, list):
            continue
        target = state.get("P_Q")
        target_norm2 = state.get("P_Q_norm2")
        basis = state.get("design_basis")
        if not isinstance(target, list) or not isinstance(basis, list) or not finite_number(target_norm2):
            continue
        plans.append(
            {
                "subset": tuple(str(readout) for readout in item.get("D_o", [])),
                "row_ids": [str(protein_id) for protein_id in row_ids],
                "target": [float(value) for value in target],
                "target_norm2": float(target_norm2),
                "basis": basis,
                "cost": float(item["cost"]),
                "observed_score": float(item["BEDC_score"]),
                "observed_coverage": float(item["coverage"]),
                "groups": groups_for_row_ids([str(protein_id) for protein_id in row_ids], label_by_id),
            }
        )
    return plans


def target_null_distribution(plans: list[dict[str, object]], organism_key: str) -> tuple[list[dict[str, object]], dict[str, int]]:
    values: list[dict[str, object]] = []
    selected = Counter()
    for trial in range(TARGET_PERMUTATION_COUNT):
        best_score = -1.0e100
        best_coverage = 0.0
        best_subset: tuple[str, ...] = ()
        total_changed = 0
        total_rows = 0
        for plan in plans:
            subset = plan["subset"]
            target = plan["target"]
            groups = plan["groups"]
            if not isinstance(subset, tuple) or not isinstance(target, list) or not isinstance(groups, list):
                raise ValueError("candidate plan malformed")
            material = f"{EXPERIMENT_ID}|{organism_key}|trial={trial}|subset={','.join(subset)}"
            target_pi, changed = permuted_target(target, groups, material)
            total_changed += changed
            total_rows += len(target)
            coverage = absorption_for_target(plan["basis"], target_pi, float(plan["target_norm2"]))  # type: ignore[arg-type]
            score = coverage - minimal_dictionary.LAMBDA * float(plan["cost"])
            if score > best_score:
                best_score = score
                best_coverage = coverage
                best_subset = subset
        selected[",".join(best_subset) if best_subset else "(empty)"] += 1
        values.append(
            {
                "trial": trial,
                "C_star": best_score,
                "coverage": best_coverage,
                "D_o_star": list(best_subset),
                "changed_fraction": total_changed / total_rows if total_rows else 0.0,
            }
        )
    return values, dict(sorted(selected.items(), key=lambda item: (-item[1], item[0])))


def verdict_for(c_obs: float, n95: float, p_target: float, reconstruction_ok: bool) -> str:
    if not reconstruction_ok:
        return "needs_data"
    if c_obs > n95 and p_target <= 0.05:
        return "crosses_boundary"
    return "composition_artifact"


def cannot_claim() -> list[str]:
    return [
        "观测性投影实验不是因果扰动实验，不能推出 readout dictionary 对蛋白丰度有因果调控。",
        "target-permutation 的 matched strata 只控制蛋白丰度 decile、CDS length bin、GC3 bin，未控制更细的 join、platform、condition 或 annotation 结构。",
        "C* 使用 minimal_dictionary 的 lambda_DL、join penalty 与 readout-side null penalty；penalty 参数没有在本 gate 中重新调参。",
        "为满足运行预算，target permutation 重抽 P_Q 并重新选择 dictionary，但每个候选 dictionary 的 readout-side null penalty沿用 observed minimal_dictionary 候选值。",
        "本 gate 只判定 P_Q 可压缩性是否超过 target-side model-class ceiling，不判定具体生物机制。",
        "通过本 gate 不等于 U 全部是 hidden biology；仍需 observation、proteostasis、PTM、chaperone 等后续分解模块。",
    ]


def analyze_organism(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    organism_key = str(config["key"])
    observed = observed_selection(repo, context, config)
    if observed.get("status") != "computed":
        return {
            "organism": observed.get("organism"),
            "organism_key": organism_key,
            "status": "needs_data",
            "verdict": "needs_data",
            "reason": observed.get("reason"),
        }
    rows = observed["rows"]
    base_ids = observed["base_ids"]
    best = observed["best"]
    evaluated = observed["evaluated"]
    if not isinstance(rows, dict) or not isinstance(base_ids, list) or not isinstance(best, dict) or not isinstance(evaluated, list):
        raise ValueError("observed selection malformed")
    label_by_id, strata_summary = strata_labels(rows, [str(protein_id) for protein_id in base_ids])  # type: ignore[arg-type]
    plans = candidate_plans(evaluated, label_by_id)
    if not plans:
        return {
            "organism": observed.get("organism"),
            "organism_key": organism_key,
            "status": "needs_data",
            "verdict": "needs_data",
            "reason": "no computed candidate plans for target permutation",
        }
    target_null, selected_counts = target_null_distribution(plans, organism_key)
    null_scores = [float(item["C_star"]) for item in target_null]
    null_coverages = [float(item["coverage"]) for item in target_null]
    c_obs = float(best["BEDC_score"])
    coverage_obs = float(best["coverage"])
    n95 = quantile_nearest_rank(null_scores, 0.95)
    p_target = (1 + sum(1 for value in null_scores if value >= c_obs)) / (1 + len(null_scores))
    best_state = best.get("state")
    best_row_ids = best.get("row_ids")
    if not isinstance(best_state, dict) or not isinstance(best_row_ids, list):
        raise ValueError("best state malformed")
    r2_qp = base_r2_qp(rows, [str(protein_id) for protein_id in best_row_ids], best_state)  # type: ignore[arg-type]
    reconstruction_ok = bool(0.25 <= r2_qp <= 0.34) if organism_key == "saccharomyces_cerevisiae" else r2_qp > 0.0
    verdict = verdict_for(c_obs, n95, p_target, reconstruction_ok)
    changed_fractions = [float(item["changed_fraction"]) for item in target_null]
    return {
        "organism": observed.get("organism"),
        "organism_key": organism_key,
        "status": "computed",
        "verdict": verdict,
        "n": int(best["n_join"]),
        "base_n": len(base_ids),
        "base_R2_QP": r2_qp,
        "C_star_obs": c_obs,
        "coverage_obs": coverage_obs,
        "D_o_star_obs": best.get("D_o"),
        "N_target_95": n95,
        "null_mean": mean(null_scores),
        "null_max": max(null_scores) if null_scores else 0.0,
        "null_coverage_mean": mean(null_coverages),
        "null_coverage_95": quantile_nearest_rank(null_coverages, 0.95),
        "p_target": p_target,
        "B": len(target_null),
        "strata_def": strata_summary,
        "target_permutation_changed_fraction_mean": mean(changed_fractions),
        "target_permutation_changed_fraction_min": min(changed_fractions) if changed_fractions else 0.0,
        "available_readouts": observed.get("available_readouts"),
        "preliminary_subset_count": observed.get("preliminary_subset_count"),
        "matched_null_subset_count": observed.get("matched_null_subset_count"),
        "target_selection_scope": "minimal_dictionary observed matched-null candidate frontier; every target permutation recomputes argmax_D over that frontier",
        "score_definition": {
            "C_star": "BEDC_score = coverage(D; P_Q_target) - lambda * fixed_minimal_dictionary_cost(D)",
            "lambda": minimal_dictionary.LAMBDA,
            "rho_join": minimal_dictionary.RHO_JOIN,
            "readout_null_penalty": "fixed per candidate from minimal_dictionary observed readout-side matched-null scan",
        },
        "target_null_selected_D_counts": selected_counts,
        "top_observed_candidates": [
            clean_candidate(item)
            for item in sorted(evaluated, key=lambda candidate: float(candidate.get("BEDC_score", -1.0e100)), reverse=True)[:10]
        ],
    }


def overall_verdict(per_organism: dict[str, dict[str, object]]) -> str:
    computed = [item for item in per_organism.values() if item.get("status") == "computed"]
    if not computed:
        return "needs_data"
    yeast = per_organism.get("saccharomyces_cerevisiae")
    if isinstance(yeast, dict) and yeast.get("status") == "computed":
        return str(yeast.get("verdict"))
    if any(item.get("verdict") == "composition_artifact" for item in computed):
        return "composition_artifact"
    if all(item.get("verdict") == "crosses_boundary" for item in computed):
        return "crosses_boundary"
    return "needs_data"


def conclusion_for(verdict: str) -> str:
    if verdict == "crosses_boundary":
        return "24.5% 在 target-permutation 下是真结构：observed C* 超过 matched target-null 95% ceiling。"
    if verdict == "composition_artifact":
        return "24.5% 在 target-permutation 下不是真结构：observed C* 未超过 matched target-null ceiling，不该继续 source-side local context lift。"
    return "target-permutation gate 未获得足够数据，不能判定 24.5% 是否是真结构。"


def main() -> None:
    started = time.time()
    repo = pathlib.Path(__file__).resolve().parents[3]
    context = residual_dictionary.q6_context(repo)
    per_organism: dict[str, dict[str, object]] = {}
    for config in residual_dictionary.ORGANISMS:
        organism_key = str(config["key"])
        if organism_key not in TARGET_ORGANISM_KEYS:
            continue
        per_organism[organism_key] = analyze_organism(repo, context, config)
    verdict = overall_verdict(per_organism)
    yeast = per_organism.get("saccharomyces_cerevisiae", {})
    computed = [item for item in per_organism.values() if item.get("status") == "computed"]
    checks = {
        "pq_reconstruction_validated": bool(
            yeast.get("status") == "computed" and finite_number(yeast.get("base_R2_QP")) and 0.25 <= float(yeast["base_R2_QP"]) <= 0.34
        ),
        "target_permutation_matched_strata": bool(
            computed
            and all(isinstance(item.get("strata_def"), dict) for item in computed)
            and all(float(item.get("target_permutation_changed_fraction_mean", 0.0)) > 0.0 for item in computed)
        ),
        "actual_B": bool(computed and all(int(item.get("B", 0)) >= TARGET_PERMUTATION_COUNT for item in computed)),
        "c_star_obs_reported": bool(computed and all(finite_number(item.get("C_star_obs")) for item in computed)),
        "n_target_95_reported": bool(computed and all(finite_number(item.get("N_target_95")) for item in computed)),
        "p_target_reported": bool(computed and all(finite_number(item.get("p_target")) for item in computed)),
        "target_ceiling_verdict": verdict,
    }
    status = "passed" if verdict in {"crosses_boundary", "composition_artifact"} else "needs_data"
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": {
            "overall_verdict": verdict,
            "conclusion": conclusion_for(verdict),
            "per_organism": per_organism,
            "actual_B": TARGET_PERMUTATION_COUNT,
            "deterministic_seed": f"sha256:{EXPERIMENT_ID}|seed={SEED}|organism|trial|subset|stratum",
            "organism_scope": sorted(TARGET_ORGANISM_KEYS),
            "runtime_sec": time.time() - started,
            "cannot_claim": cannot_claim(),
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if status == "passed" else 3)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"runtime_exception": True},
            "verdict": "needs_data",
            "result": {
                "cannot_claim": ["运行时异常，不能作科学结论。"],
                "error": str(exc),
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

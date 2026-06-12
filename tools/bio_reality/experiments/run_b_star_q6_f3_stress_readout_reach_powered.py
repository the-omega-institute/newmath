#!/usr/bin/env python3
"""Readout reachability of the dominant B*_Q6 f3_stress abundance component."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_b_star_q6_irreducibility_certificate_powered as routea
import run_b_star_q6_minimal_dictionary_compression_powered as compression
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot
from run_b_star_q6_translation_survival_powered import Q9_FAMILIES, q_vectors


EXPERIMENT_ID = "b_star_q6_f3_stress_readout_reach_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_stress_readout_reach.b_star_q6_dominant_coordinate_powered"

ORGANISM = "saccharomyces_cerevisiae"
F3_COORDINATE = "f3_stress"
BASE_READOUTS = ("measured_te", "mrna_stability", "turnover")
FULL_INDEPENDENT_READOUTS = (
    "measured_te",
    "mrna_stability",
    "turnover",
    "localization",
    "ptm_density",
    "complex_member",
    "tm_count",
    "domain_count",
    "mrna_abundance",
)
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_f3_stress_readout_reach_powered:deterministic"
EPS = 1e-12
BASE_SANITY_EXPECTED = 0.190
BASE_SANITY_TOL = 0.035


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def project_vector(design: list[list[float]], target: list[float]) -> tuple[list[float], float, int, list[list[float]]]:
    basis = orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected), len(basis), basis


def projection_from_basis(basis: list[list[float]], target: list[float]) -> tuple[list[float], float]:
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected)


def absorption_for_basis(basis: list[list[float]], target: list[float]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS or not basis:
        return 0.0
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    return bounded_unit(max(0.0, energy) / target_norm)


def absorption_for_permuted_target(basis: list[list[float]], target: list[float], permutation: list[int]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS or not basis:
        return 0.0
    energy = 0.0
    for q in basis:
        dot = 0.0
        for index, target_index in enumerate(permutation):
            dot += target[target_index] * q[index]
        energy += dot * dot
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    return bounded_unit(max(0.0, energy) / target_norm)


def candidate_key(subset: tuple[str, ...]) -> str:
    return ",".join(subset) if subset else "<empty>"


def public_candidate(item: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in item.items() if key not in {"state", "row_ids"}}


def readout_design(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    subset: tuple[str, ...],
) -> list[list[float]]:
    design: list[list[float]] = []
    for protein_id in row_ids:
        values: list[float] = []
        for readout in subset:
            values.extend(compression.readout_values(rows[protein_id], readout))
        design.append(values)
    return design


def f3_state_for_subset(
    *,
    rows: dict[str, dict[str, object]],
    selected_by_id: dict[str, dict[str, object]],
    base_ids: list[str],
    q_names: list[str],
    subset: tuple[str, ...],
    join_cache: dict[tuple[str, ...], dict[str, object]],
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]],
) -> dict[str, object]:
    row_ids = [
        protein_id
        for protein_id in base_ids
        if all(compression.row_has_readout(rows[protein_id], readout) for readout in subset)
    ]
    if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "D_o": list(subset),
            "status": "needs_data",
            "n_join": len(row_ids),
            "reason": f"join below honest gate n_join={len(row_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
        }

    join_key = tuple(row_ids)
    join_state = join_cache.get(join_key)
    if join_state is None:
        active_rows = [selected_by_id[protein_id] for protein_id in row_ids]
        z_basis = orthonormal_basis_from_columns(matrix_rows(active_rows, "z"))
        x_e = residual_dictionary.residualize_with_basis(matrix_rows(active_rows, "x"), z_basis)
        p_e = residual_dictionary.residualize_with_basis(matrix_rows(active_rows, "p"), z_basis)
        target = matrix_column(p_e, 0)
        f3_index = q_names.index(F3_COORDINATE)
        f3_design = [[row[f3_index]] for row in x_e]
        p_f3, p_f3_energy, rank_f3, f3_basis = project_vector(f3_design, target)
        if p_f3_energy <= EPS:
            return {
                "D_o": list(subset),
                "status": "needs_data",
                "n_join": len(row_ids),
                "reason": "P_f3 has zero residual energy on active join",
            }
        target_norm2 = vector_norm2(target)
        join_state = {
            "row_ids": row_ids,
            "z_basis": z_basis,
            "target": target,
            "target_norm2": target_norm2,
            "x_e": x_e,
            "P_f3": p_f3,
            "P_f3_norm2": p_f3_energy,
            "P_f3_fraction_of_target": bounded_unit(p_f3_energy / target_norm2) if target_norm2 > EPS else 0.0,
            "rank_f3": rank_f3,
            "f3_basis": f3_basis,
        }
        join_cache[join_key] = join_state

    z_basis = join_state["z_basis"]
    p_f3 = join_state["P_f3"]
    p_f3_energy = join_state["P_f3_norm2"]
    if not isinstance(z_basis, list) or not isinstance(p_f3, list) or not isinstance(p_f3_energy, float):
        raise ValueError("f3 join state malformed")

    if subset:
        residualized_by_readout: dict[str, list[list[float]]] = {}
        for readout in subset:
            cache_key = (join_key, readout)
            cached = readout_cache.get(cache_key)
            if cached is None:
                raw = [compression.readout_values(rows[protein_id], readout) for protein_id in row_ids]
                cached = residual_dictionary.residualize_with_basis(raw, z_basis)
                readout_cache[cache_key] = cached
            residualized_by_readout[readout] = cached
        design: list[list[float]] = []
        for local_index, _protein_id in enumerate(row_ids):
            values: list[float] = []
            for readout in subset:
                values.extend(residualized_by_readout[readout][local_index])
            design.append(values)
        design_basis = orthonormal_basis_from_columns(design)
        projected, projected_norm2 = projection_from_basis(design_basis, p_f3)
    else:
        design_basis = []
        projected = [0.0 for _ in p_f3]
        projected_norm2 = 0.0

    residual = subtract_vectors(p_f3, projected)
    return {
        "D_o": list(subset),
        "status": "computed",
        "n_join": len(row_ids),
        "base_n": len(base_ids),
        "coverage": bounded_unit(projected_norm2 / p_f3_energy),
        "unexplained": bounded_unit(vector_norm2(residual) / p_f3_energy),
        "P_f3_norm2": p_f3_energy,
        "P_f3_fraction_of_target": join_state["P_f3_fraction_of_target"],
        "projected_norm2": projected_norm2,
        "rank_D_e": len(design_basis),
        "rank_f3": join_state["rank_f3"],
        "join_shift": abs(len(row_ids) - len(base_ids)) / len(base_ids) if base_ids else 1.0,
        "DL": sum(compression.readout_dimensions(rows, readout) for readout in subset),
        "row_ids": row_ids,
        "state": {
            "P_f3": p_f3,
            "P_f3_norm2": p_f3_energy,
            "design_basis": design_basis,
            "z_basis_rank": len(z_basis),
        },
    }


def naive_fixed_subset_null(*, subset: tuple[str, ...], basis: list[list[float]], target: list[float]) -> dict[str, object]:
    if not subset or not basis:
        return {
            "permutation_count": 0,
            "null95_coverage": 0.0,
            "null_mean_coverage": 0.0,
            "null_model": "empty dictionary has zero fixed-subset null coverage",
        }
    values: list[float] = []
    label = candidate_key(subset)
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(target), f"{SEED}|naive-fixed-subset|subset={label}|trial={trial}")
        values.append(absorption_for_permuted_target(basis, target, permutation))
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_coverage": percentile_nearest_rank(values, 0.95),
        "null_mean_coverage": mean(values),
        "deterministic_seed": f"{SEED}|naive-fixed-subset|subset|trial|index|n",
        "null_model": "naive fixed-subset deterministic row-label permutation of P_f3; selection over candidate subsets is not replayed",
    }


def selection_aware_null(candidate_items: list[dict[str, object]]) -> dict[str, object]:
    values: list[float] = []
    selected_subsets: list[list[str]] = []
    for trial in range(PERMUTATION_COUNT):
        best_coverage = -1.0
        best_subset: list[str] = []
        permutation_cache: dict[int, list[int]] = {}
        for item in candidate_items:
            state = item.get("state")
            if not isinstance(state, dict):
                raise ValueError("candidate state malformed")
            target = state.get("P_f3")
            basis = state.get("design_basis")
            subset = tuple(str(readout) for readout in item.get("D_o", []))
            if not isinstance(target, list) or not isinstance(basis, list):
                raise ValueError("candidate target/basis malformed")
            if not subset or not basis:
                coverage = 0.0
            else:
                n = len(target)
                permutation = permutation_cache.get(n)
                if permutation is None:
                    permutation = deterministic_permutation(
                        n,
                        f"{SEED}|selection-aware-target-permutation|trial={trial}|n={n}",
                    )
                    permutation_cache[n] = permutation
                coverage = absorption_for_permuted_target(basis, target, permutation)
            if coverage > best_coverage:
                best_coverage = coverage
                best_subset = list(subset)
        values.append(max(0.0, best_coverage))
        selected_subsets.append(best_subset)

    counts: dict[str, int] = {}
    for subset in selected_subsets:
        key = candidate_key(tuple(subset))
        counts[key] = counts.get(key, 0) + 1
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_coverage": percentile_nearest_rank(values, 0.95),
        "null_mean_coverage": mean(values),
        "null_max_coverage": max(values) if values else 0.0,
        "selected_subset_counts_top10": [
            {"D_o": [] if key == "<empty>" else key.split(","), "count": count}
            for key, count in sorted(counts.items(), key=lambda pair: (-pair[1], pair[0]))[:10]
        ],
        "deterministic_seed": f"{SEED}|selection-aware-target-permutation|trial|n|index|n",
        "null_model": "selection-aware null: each trial permutes P_f3 rows and redoes best-coverage selection over the same readout-subset family",
    }


def all_subsets(readouts: tuple[str, ...]) -> list[tuple[str, ...]]:
    subsets: list[tuple[str, ...]] = [()]
    for size in range(1, len(readouts) + 1):
        subsets.extend(tuple(item) for item in __import__("itertools").combinations(readouts, size))
    return subsets


def f3_definition(context: dict[str, object]) -> dict[str, object]:
    codons = context["codons"]
    q_projected = context["q_projected"]
    if not isinstance(codons, list) or not isinstance(q_projected, dict):
        raise ValueError("q6 context malformed")
    raw = q_vectors([str(codon) for codon in codons])[F3_COORDINATE]
    projected = q_projected[F3_COORDINATE]
    if not isinstance(projected, dict):
        raise ValueError("f3 projected vector malformed")
    raw_nonzero = {codon: value for codon, value in raw.items() if abs(value) > EPS}
    projected_nonzero = {
        str(codon): float(value)
        for codon, value in sorted(projected.items())
        if isinstance(value, (int, float)) and abs(float(value)) > 1e-10
    }
    return {
        "coordinate": F3_COORDINATE,
        "coordinate_index": None,
        "raw_rule": "for each Q9_FAMILIES synonymous block, add +1 to the first listed RNA codon and -1 to the last listed RNA codon; then project within amino-acid synonymous fibers",
        "raw_families": Q9_FAMILIES,
        "raw_nonzero_weights": raw_nonzero,
        "synonymous_projected_nonzero_weights": projected_nonzero,
        "normalization": "per-gene coordinate is dot(codon_frequency, synonymous_projected_f3_stress) divided by the projected vector norm, then residualized against sibling Z controls",
    }


def run_readout_reach(join: dict[str, object]) -> dict[str, object]:
    rows = join["rows"]
    selected_ids = join["selected_ids"]
    selected_rows = join["selected_rows"]
    context = join["context"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(selected_rows, list):
        raise ValueError("unified yeast join malformed")
    if not isinstance(context, dict) or not isinstance(context.get("q_names"), list):
        raise ValueError("unified yeast join lacks B*_Q6 coordinate names")
    q_names = [str(name) for name in context["q_names"]]
    if F3_COORDINATE not in q_names:
        raise ValueError("B*_Q6 context lacks f3_stress coordinate")

    base_ids = [str(item) for item in selected_ids]
    selected_by_id = {protein_id: selected_rows[index] for index, protein_id in enumerate(base_ids)}
    available = compression.available_readouts(join["yeast_config"], rows, base_ids)  # type: ignore[arg-type]
    missing_requested = [readout for readout in FULL_INDEPENDENT_READOUTS if readout not in available]
    if missing_requested:
        return {
            "status": "needs_data",
            "reason": "one or more requested independent readouts are unavailable on the yeast context join",
            "available_readouts": available,
            "missing_requested_readouts": missing_requested,
            "base_n": len(base_ids),
        }

    join_cache: dict[tuple[str, ...], dict[str, object]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
    subsets = all_subsets(FULL_INDEPENDENT_READOUTS)
    candidates = [
        f3_state_for_subset(
            rows=rows,  # type: ignore[arg-type]
            selected_by_id=selected_by_id,
            base_ids=base_ids,
            q_names=q_names,
            subset=subset,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in subsets
    ]
    computed = [item for item in candidates if item.get("status") == "computed"]
    if not computed:
        return {
            "status": "needs_data",
            "reason": "no readout subset passed the join gate",
            "available_readouts": available,
            "candidate_subset_count": len(subsets),
            "base_n": len(base_ids),
        }

    base_item = next(
        (
            item
            for item in computed
            if tuple(str(readout) for readout in item.get("D_o", [])) == BASE_READOUTS
        ),
        None,
    )
    full_item = next(
        (
            item
            for item in computed
            if tuple(str(readout) for readout in item.get("D_o", [])) == FULL_INDEPENDENT_READOUTS
        ),
        None,
    )
    if base_item is None:
        return {
            "status": "needs_data",
            "reason": "base readout dictionary did not pass the join gate",
            "available_readouts": available,
            "base_readouts": list(BASE_READOUTS),
            "base_n": len(base_ids),
        }
    if full_item is None:
        return {
            "status": "needs_data",
            "reason": "full independent readout dictionary did not pass the join gate",
            "available_readouts": available,
            "full_readouts": list(FULL_INDEPENDENT_READOUTS),
            "base_n": len(base_ids),
        }

    best_item = max(computed, key=lambda item: float(item["coverage"]))
    best_state = best_item.get("state")
    if not isinstance(best_state, dict):
        raise ValueError("best f3 state malformed")
    best_basis = best_state.get("design_basis")
    best_target = best_state.get("P_f3")
    if not isinstance(best_basis, list) or not isinstance(best_target, list):
        raise ValueError("best f3 target/basis malformed")

    base_coverage = float(base_item["coverage"])
    best_coverage = float(best_item["coverage"])
    full_coverage = float(full_item["coverage"])
    increment = best_coverage - base_coverage
    selection_null = selection_aware_null(computed)
    naive_null = naive_fixed_subset_null(
        subset=tuple(str(readout) for readout in best_item.get("D_o", [])),
        basis=best_basis,
        target=best_target,
    )
    selection_null95 = float(selection_null["null95_coverage"])
    naive_null95 = float(naive_null["null95_coverage"])

    top_subsets = sorted(
        (
            {
                "D_o": item.get("D_o"),
                "n_dict": len(item.get("D_o", [])) if isinstance(item.get("D_o"), list) else None,
                "n_join": item.get("n_join"),
                "coverage": item.get("coverage"),
                "unexplained": item.get("unexplained"),
                "P_f3_fraction_of_target": item.get("P_f3_fraction_of_target"),
                "rank_D_e": item.get("rank_D_e"),
                "join_shift": item.get("join_shift"),
            }
            for item in computed
        ),
        key=lambda item: float(item["coverage"]) if item["coverage"] is not None else -1e100,
        reverse=True,
    )[:12]

    definition = f3_definition(context)
    definition["coordinate_index"] = q_names.index(F3_COORDINATE)
    base_sanity_passed = abs(base_coverage - BASE_SANITY_EXPECTED) <= BASE_SANITY_TOL
    reach_passed = best_coverage > selection_null95 and increment > EPS
    checks = [
        {
            "name": "f3_target_computed",
            "passed": float(base_item["P_f3_norm2"]) > EPS,
            "P_f3_norm2": base_item["P_f3_norm2"],
            "P_f3_fraction_of_target": base_item["P_f3_fraction_of_target"],
            "coordinate": F3_COORDINATE,
            "coordinate_index": q_names.index(F3_COORDINATE),
            "n_join": base_item["n_join"],
        },
        {
            "name": "full_readout_reach_selection_aware",
            "passed": reach_passed,
            "best_coverage": best_coverage,
            "selection_aware_null95": selection_null95,
            "base_coverage": base_coverage,
            "increment_over_base": increment,
            "rule": "passed iff best_coverage > selection_aware_null95 and best_coverage - base_coverage > 0",
        },
        {
            "name": "base_coverage_reproduced",
            "passed": base_sanity_passed,
            "base_coverage": base_coverage,
            "expected_approx": BASE_SANITY_EXPECTED,
            "tolerance": BASE_SANITY_TOL,
            "base_readouts": list(BASE_READOUTS),
        },
    ]

    status = "passed" if all(bool(check["passed"]) for check in checks) else "failed"
    return {
        "status": status,
        "checks": checks,
        "best_coverage": best_coverage,
        "selection_aware_null95": selection_null95,
        "selection_aware_null_mean": selection_null["null_mean_coverage"],
        "selection_aware_null_max": selection_null["null_max_coverage"],
        "naive_null95": naive_null95,
        "naive_null_mean": naive_null["null_mean_coverage"],
        "base_coverage": base_coverage,
        "full_coverage": full_coverage,
        "increment_over_base": increment,
        "unexplained_after_full": bounded_unit(1.0 - best_coverage),
        "D_o_best": best_item["D_o"],
        "D_o_full": list(FULL_INDEPENDENT_READOUTS),
        "D_o_base": list(BASE_READOUTS),
        "n_join_best": best_item["n_join"],
        "n_join_full": full_item["n_join"],
        "n_join_base": base_item["n_join"],
        "rank_D_e_best": best_item["rank_D_e"],
        "rank_D_e_full": full_item["rank_D_e"],
        "rank_D_e_base": base_item["rank_D_e"],
        "P_f3_norm2_base": base_item["P_f3_norm2"],
        "P_f3_fraction_of_target_base": base_item["P_f3_fraction_of_target"],
        "P_f3_norm2_best": best_item["P_f3_norm2"],
        "P_f3_fraction_of_target_best": best_item["P_f3_fraction_of_target"],
        "f3_definition": definition,
        "available_readouts": available,
        "candidate_subset_count": len(subsets),
        "computed_candidate_subset_count": len(computed),
        "candidate_subset_selection": "all subsets of the nine requested independent readouts, including the empty subset",
        "selection_aware_null": selection_null,
        "naive_fixed_subset_null": naive_null,
        "top_coverage_subsets": top_subsets,
        "best_public": public_candidate(best_item),
        "full_public": public_candidate(full_item),
        "base_public": public_candidate(base_item),
        "permutation_count": PERMUTATION_COUNT,
        "fold_count": FOLD_COUNT,
        "seed": SEED,
        "coverage_metric": "orthogonal projection coverage of P_f3 = Proj_{x_f3_stress}(Z-residualized log10 protein abundance) by Z-residualized independent readout subsets",
        "null_model": "selection-aware deterministic row-label permutation of P_f3 with best-subset selection replayed on every trial",
        "organism": "Saccharomyces cerevisiae",
        "organism_key": ORGANISM,
        "base_n": len(base_ids),
        "z_basis_rank_unified": join.get("z_basis_rank"),
        "data_summary": join.get("data_summary"),
        "ordered_cds_summary": join.get("ordered_cds_summary"),
        "context_summary": {key: value for key, value in join.get("context_summary", {}).items() if key != "q2_feature_names"}
        if isinstance(join.get("context_summary"), dict)
        else join.get("context_summary"),
        "H_source_summaries": join.get("H_source_summaries"),
        "cannot_claim": [
            "projection coverage is descriptive reachability, not causal mediation proof",
            "selection-aware significance is restricted to the tested independent readout subset family",
            "readouts derived from codon usage such as tAI are intentionally excluded to avoid tautological recovery of a codon coordinate",
            "failed status means no positive reachability certificate under these local readouts, not that no future measurement can explain f3_stress",
        ],
        "verdict": (
            "f3_stress 的丰度分量对更全独立测量集部分可达：best subset 超过 selection-aware Null95，且相对 base 字典有正增量。"
            if status == "passed"
            else "f3_stress 对当前可用独立测量未给出超出 base 的 selection-aware 可达性证书；剩余分量应作为需要新数据或新机制的 frontier。"
        ),
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    join = routea.build_unified_yeast_join(repo)
    if join.get("status") != "computed":
        emit(
            "needs_data",
            reason=join.get("reason", "unified yeast join unavailable"),
            checks=[],
            **{key: value for key, value in join.items() if key not in {"status", "reason"}},
        )

    result = run_readout_reach(join)
    status = str(result.pop("status"))
    emit(status, **result)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        emit("failed", error=str(exc), reason="f3_stress readout reach experiment could not be computed", checks=[])

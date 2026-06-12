#!/usr/bin/env python3
"""Minimal B*_Q6 readout dictionary compression and boundary response."""

from __future__ import annotations

import hashlib
import itertools
import json
import math
import pathlib
import random
import sys
from collections import defaultdict
from typing import Any

import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
import run_b_star_q6_wobble_dwell_coupling_powered as wobble_dwell
from run_b_star_q6_h_candidate_ranking_table_powered import FEATURE_CANDIDATES
from run_b_star_q6_joint_te_stability_mediation_powered import yeast_join_keys
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot


EXPERIMENT_ID = "b_star_q6_minimal_dictionary_compression_powered"
CLAIM_ID = "h3.cross_layer_relation.minimal_dictionary_compression.b_star_q6_readout_boundary_response_powered"

PERMUTATION_COUNT = 50
BOUNDARY_PERMUTATION_COUNT = 100
BOUNDARY_GENE_SUBSAMPLE_N = 1800
LAMBDA = residual_dictionary.LAMBDA_DL
RHO_JOIN = residual_dictionary.RHO_JOIN
EPS = 1e-12
MODEL_DF = 2
MIN_BOUNDARY_ROWS = 200
MIN_BOUNDARY_ROWS_PER_WINDOW = 40
MIN_BOUNDARY_BIN_ROWS = 4

OCCUPANCY_PATH = "tools/bio_reality/data/riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
POSITIONAL_PROFILE_PATH = "tools/bio_reality/data/cds_positional_codon_profile_saccharomyces_cerevisiae.json"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    return residual_dictionary.residualize_with_basis(matrix, basis)


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


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        material = f"{material_prefix}|index={index}|n={n}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def permute_basis_rows(basis: list[list[float]], permutation: list[int]) -> list[list[float]]:
    return [[q[permutation[index]] for index in range(len(permutation))] for q in basis]


def absorption_for_basis(basis: list[list[float]], target: list[float]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS:
        return 0.0
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    return bounded_unit(max(0.0, energy) / target_norm)


def projection_from_basis(basis: list[list[float]], target: list[float]) -> tuple[list[float], float, int]:
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected), len(basis)


def readout_dimensions(rows: dict[str, dict[str, object]], readout: str) -> int:
    for row in rows.values():
        if readout == "measured_te":
            return len(row["t"])  # type: ignore[arg-type]
        if readout == "mrna_stability":
            values = row.get("s")
            return len(values) if isinstance(values, list) else 0
        h_map = row.get("h")
        if isinstance(h_map, dict) and readout in h_map:
            return len(h_map[readout])  # type: ignore[arg-type]
    return 0


def row_has_readout(row: dict[str, object], readout: str) -> bool:
    if readout == "measured_te":
        return isinstance(row.get("t"), list)
    if readout == "mrna_stability":
        return isinstance(row.get("s"), list)
    h_map = row.get("h")
    return isinstance(h_map, dict) and readout in h_map


def readout_values(row: dict[str, object], readout: str) -> list[float]:
    if readout == "measured_te":
        return list(row["t"])  # type: ignore[arg-type]
    if readout == "mrna_stability":
        return list(row["s"])  # type: ignore[arg-type]
    h_map = row["h"]
    if not isinstance(h_map, dict):
        raise ValueError("row h map malformed")
    return list(h_map[readout])  # type: ignore[arg-type]


def available_readouts(config: dict[str, object], rows: dict[str, dict[str, object]], base_ids: list[str]) -> list[str]:
    readouts = ["measured_te"]
    if config.get("has_stability") and all(isinstance(rows[protein_id].get("s"), list) for protein_id in base_ids):
        readouts.append("mrna_stability")
    for candidate in residual_dictionary.H_CANDIDATES:
        join_count = sum(1 for protein_id in base_ids if row_has_readout(rows[protein_id], candidate))
        if join_count >= MIN_PROTEINS_PER_ORGANISM:
            readouts.append(candidate)
    return readouts


def compression_state(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    subset: tuple[str, ...],
) -> dict[str, object]:
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q, _basis_q = project_vector(x_e, p_col)
    if p_q_energy <= EPS:
        raise ValueError("P_Q has zero residual energy")

    design: list[list[float]] = []
    for row in selected_rows:
        values: list[float] = []
        for readout in subset:
            values.extend(readout_values(row, readout))
        design.append(values)
    if subset:
        projected, projected_energy, rank_d, design_basis = project_vector(residualize_with_basis(design, z_basis), p_q)
    else:
        projected = [0.0 for _ in p_q]
        projected_energy = 0.0
        rank_d = 0
        design_basis = []
    residual = subtract_vectors(p_q, projected)
    return {
        "row_ids": row_ids,
        "z_basis": z_basis,
        "x_e": x_e,
        "P_Q": p_q,
        "P_Q_norm2": p_q_energy,
        "rank_Q_e": rank_q,
        "projected": projected,
        "projected_norm2": projected_energy,
        "coverage": bounded_unit(projected_energy / p_q_energy),
        "unexplained": bounded_unit(vector_norm2(residual) / p_q_energy),
        "residual": residual,
        "rank_D_e": rank_d,
        "design_basis": design_basis,
    }


def compression_join_state(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    cache: dict[tuple[str, ...], dict[str, object]],
) -> dict[str, object]:
    key = tuple(row_ids)
    cached = cache.get(key)
    if cached is not None:
        return cached
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q, _basis_q = project_vector(x_e, p_col)
    if p_q_energy <= EPS:
        raise ValueError("P_Q has zero residual energy")
    state = {
        "z_basis": z_basis,
        "x_e": x_e,
        "P_Q": p_q,
        "P_Q_norm2": p_q_energy,
        "rank_Q_e": rank_q,
    }
    cache[key] = state
    return state


def residualized_readout_for_join(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    readout: str,
    z_basis: list[list[float]],
    cache: dict[tuple[tuple[str, ...], str], list[list[float]]],
) -> list[list[float]]:
    key = (tuple(row_ids), readout)
    cached = cache.get(key)
    if cached is not None:
        return cached
    design = [readout_values(rows[protein_id], readout) for protein_id in row_ids]
    residualized = residualize_with_basis(design, z_basis)
    cache[key] = residualized
    return residualized


def compression_state_cached(
    *,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    subset: tuple[str, ...],
    join_cache: dict[tuple[str, ...], dict[str, object]],
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]],
) -> dict[str, object]:
    if subset:
        row_ids = [protein_id for protein_id in base_ids if all(row_has_readout(rows[protein_id], readout) for readout in subset)]
    else:
        row_ids = list(base_ids)
    join_state = compression_join_state(rows=rows, row_ids=row_ids, cache=join_cache)
    z_basis = join_state["z_basis"]
    x_e = join_state["x_e"]
    p_q = join_state["P_Q"]
    p_q_energy = join_state["P_Q_norm2"]
    if not isinstance(z_basis, list) or not isinstance(x_e, list) or not isinstance(p_q, list) or not isinstance(p_q_energy, float):
        raise ValueError("compression join state malformed")
    if subset:
        residualized_by_readout = {
            readout: residualized_readout_for_join(
                rows=rows,
                row_ids=row_ids,
                readout=readout,
                z_basis=z_basis,
                cache=readout_cache,
            )
            for readout in subset
        }
        design: list[list[float]] = []
        for local_index, _protein_id in enumerate(row_ids):
            values: list[float] = []
            for readout in subset:
                values.extend(residualized_by_readout[readout][local_index])
            design.append(values)
        design_basis = orthonormal_basis_from_columns(design)
        projected, projected_energy, rank_d = projection_from_basis(design_basis, p_q)
    else:
        projected = [0.0 for _ in p_q]
        projected_energy = 0.0
        rank_d = 0
        design_basis = []
    residual = subtract_vectors(p_q, projected)
    return {
        "row_ids": row_ids,
        "z_basis": z_basis,
        "x_e": x_e,
        "P_Q": p_q,
        "P_Q_norm2": p_q_energy,
        "rank_Q_e": join_state["rank_Q_e"],
        "projected": projected,
        "projected_norm2": projected_energy,
        "coverage": bounded_unit(projected_energy / p_q_energy),
        "unexplained": bounded_unit(vector_norm2(residual) / p_q_energy),
        "residual": residual,
        "rank_D_e": rank_d,
        "design_basis": design_basis,
    }


def subset_null95(
    *,
    organism: str,
    subset: tuple[str, ...],
    basis: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    if not subset or not basis:
        return {
            "permutation_count": 0,
            "null95_coverage": 0.0,
            "null_mean_coverage": 0.0,
            "null_model": "empty dictionary has zero null coverage",
        }
    values: list[float] = []
    subset_label = ",".join(subset)
    for trial in range(PERMUTATION_COUNT):
        prefix = f"{EXPERIMENT_ID}|{organism}|subset={subset_label}|trial={trial}"
        permuted = permute_basis_rows(basis, deterministic_permutation(len(target), prefix))
        values.append(absorption_for_basis(permuted, target))
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_coverage": percentile_nearest_rank(values, 0.95),
        "null_mean_coverage": mean(values),
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|organism|subset|trial|index|n",
        "null_model": "matched deterministic label permutation of the Z-residualized readout subspace rows on the active join",
    }


def subset_null_skipped(reason: str) -> dict[str, object]:
    return {
        "permutation_count": 0,
        "null95_coverage": 0.0,
        "null_mean_coverage": 0.0,
        "null_model": reason,
    }


def scaled_cost(dl: int, join_shift: float, null95: float) -> tuple[float, dict[str, float]]:
    parts = {
        "DL": float(dl),
        "JoinPenalty": (RHO_JOIN / LAMBDA) * join_shift,
        "NullPenalty": null95 / LAMBDA,
    }
    return sum(parts.values()), parts


def evaluate_subset(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    subset: tuple[str, ...],
    compute_null: bool,
) -> dict[str, object]:
    row_ids = [protein_id for protein_id in base_ids if all(row_has_readout(rows[protein_id], readout) for readout in subset)]
    if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "D_o": list(subset),
            "status": "needs_data",
            "n_join": len(row_ids),
            "reason": f"join below honest gate n_join={len(row_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
        }
    state = compression_state(rows=rows, row_ids=row_ids, subset=subset)
    target = state["P_Q"]
    basis = state["design_basis"]
    if not isinstance(target, list) or not isinstance(basis, list):
        raise ValueError("compression state malformed")
    null = (
        subset_null95(organism=organism, subset=subset, basis=basis, target=target)
        if compute_null
        else subset_null_skipped("preliminary exact-coverage scan; matched null is computed on the candidate frontier before selecting D_o_star")
    )
    null95 = float(null["null95_coverage"])
    dl = sum(readout_dimensions(rows, readout) for readout in subset)
    join_shift = abs(len(row_ids) - len(base_ids)) / len(base_ids) if base_ids else 1.0
    cost, cost_parts = scaled_cost(dl, join_shift, null95)
    coverage = float(state["coverage"])
    score = coverage - LAMBDA * cost
    return {
        "D_o": list(subset),
        "status": "computed",
        "n_join": len(row_ids),
        "base_n": len(base_ids),
        "coverage": coverage,
        "unexplained": state["unexplained"],
        "P_Q_norm2": state["P_Q_norm2"],
        "projected_norm2": state["projected_norm2"],
        "rank_D_e": state["rank_D_e"],
        "rank_Q_e": state["rank_Q_e"],
        "DL": dl,
        "join_shift": join_shift,
        "lambda": LAMBDA,
        "rho_join": RHO_JOIN,
        "cost": cost,
        "cost_parts": cost_parts,
        "BEDC_score": score,
        "coverage_above_null95": coverage > null95,
        "null": null,
        "matched_null_computed": compute_null,
        "row_ids": row_ids,
        "state": state,
    }


def evaluate_subset_cached(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    subset: tuple[str, ...],
    compute_null: bool,
    join_cache: dict[tuple[str, ...], dict[str, object]],
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]],
) -> dict[str, object]:
    row_ids = [protein_id for protein_id in base_ids if all(row_has_readout(rows[protein_id], readout) for readout in subset)]
    if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "D_o": list(subset),
            "status": "needs_data",
            "n_join": len(row_ids),
            "reason": f"join below honest gate n_join={len(row_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
        }
    state = compression_state_cached(
        rows=rows,
        base_ids=base_ids,
        subset=subset,
        join_cache=join_cache,
        readout_cache=readout_cache,
    )
    target = state["P_Q"]
    basis = state["design_basis"]
    if not isinstance(target, list) or not isinstance(basis, list):
        raise ValueError("compression state malformed")
    null = (
        subset_null95(organism=organism, subset=subset, basis=basis, target=target)
        if compute_null
        else subset_null_skipped("preliminary exact-coverage scan; matched null is computed on the candidate frontier before selecting D_o_star")
    )
    null95 = float(null["null95_coverage"])
    dl = sum(readout_dimensions(rows, readout) for readout in subset)
    join_shift = abs(len(row_ids) - len(base_ids)) / len(base_ids) if base_ids else 1.0
    cost, cost_parts = scaled_cost(dl, join_shift, null95)
    coverage = float(state["coverage"])
    score = coverage - LAMBDA * cost
    return {
        "D_o": list(subset),
        "status": "computed",
        "n_join": len(row_ids),
        "base_n": len(base_ids),
        "coverage": coverage,
        "unexplained": state["unexplained"],
        "P_Q_norm2": state["P_Q_norm2"],
        "projected_norm2": state["projected_norm2"],
        "rank_D_e": state["rank_D_e"],
        "rank_Q_e": state["rank_Q_e"],
        "DL": dl,
        "join_shift": join_shift,
        "lambda": LAMBDA,
        "rho_join": RHO_JOIN,
        "cost": cost,
        "cost_parts": cost_parts,
        "BEDC_score": score,
        "coverage_above_null95": coverage > null95,
        "null": null,
        "matched_null_computed": compute_null,
        "row_ids": row_ids,
        "state": state,
    }


def all_subsets(readouts: list[str]) -> list[tuple[str, ...]]:
    subsets: list[tuple[str, ...]] = [()]
    for size in range(1, len(readouts) + 1):
        subsets.extend(tuple(item) for item in itertools.combinations(readouts, size))
    return subsets


def frontier_subsets(preliminary: list[dict[str, object]]) -> list[tuple[str, ...]]:
    computed = [item for item in preliminary if item.get("status") == "computed"]
    selected: set[tuple[str, ...]] = {()}
    for item in computed:
        subset = tuple(str(readout) for readout in item.get("D_o", []))
        if len(subset) <= 2:
            selected.add(subset)
    by_size: dict[int, list[dict[str, object]]] = defaultdict(list)
    for item in computed:
        subset = item.get("D_o")
        if isinstance(subset, list):
            by_size[len(subset)].append(item)
    for items in by_size.values():
        items.sort(key=lambda item: float(item.get("BEDC_score", -1e100)), reverse=True)
        for item in items[:4]:
            selected.add(tuple(str(readout) for readout in item.get("D_o", [])))
    computed.sort(key=lambda item: float(item.get("BEDC_score", -1e100)), reverse=True)
    for item in computed[:24]:
        selected.add(tuple(str(readout) for readout in item.get("D_o", [])))
    return sorted(selected, key=lambda subset: (len(subset), subset))


def dominant_residual_q(state: dict[str, object], context: dict[str, object]) -> dict[str, object]:
    x_e = state["x_e"]
    residual = state["residual"]
    q_names = context["q_names"]
    if not isinstance(x_e, list) or not isinstance(residual, list) or not isinstance(q_names, list):
        raise ValueError("dominant residual state malformed")
    coeffs = solve_regularized_normal_equation(x_e, residual)
    entries = [
        {"q": str(name), "coefficient": coeffs[index], "abs_coefficient": abs(coeffs[index])}
        for index, name in enumerate(q_names)
    ]
    entries.sort(key=lambda item: float(item["abs_coefficient"]), reverse=True)
    return entries[0] if entries else {"q": None, "coefficient": 0.0, "abs_coefficient": 0.0}


def build_organism_compression(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    organism = str(config["key"])
    built = residual_dictionary.base_rows(repo=repo, context=context, config=config)
    if built.get("status") != "computed":
        return {
            "organism": config["label"],
            "organism_key": organism,
            "status": "needs_data",
            "reason": built.get("reason"),
            "data_summary": built,
        }
    rows = built["rows"]
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    attached = residual_dictionary.attach_h_readouts(repo, organism, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "organism": config["label"],
            "organism_key": organism,
            "status": "needs_data",
            "reason": f"base P/Q/T/S join yielded n={len(base_ids)}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "data_summary": built["summary"],
            "H_source_summaries": attached["source_summaries"],
        }
    readouts = available_readouts(config, rows, base_ids)  # type: ignore[arg-type]
    join_cache: dict[tuple[str, ...], dict[str, object]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
    preliminary = [
        evaluate_subset_cached(
            organism=organism,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            subset=subset,
            compute_null=False,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in all_subsets(readouts)
    ]
    candidate_subsets = frontier_subsets(preliminary)
    evaluated = [
        evaluate_subset_cached(
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
            "organism": config["label"],
            "organism_key": organism,
            "status": "needs_data",
            "reason": "no readout subset passed the join gate",
            "available_readouts": readouts,
            "data_summary": built["summary"],
            "H_source_summaries": attached["source_summaries"],
        }
    best = max(computed, key=lambda item: float(item["BEDC_score"]))
    best_state = best["state"]
    if not isinstance(best_state, dict):
        raise ValueError("best compression state malformed")
    top_subsets = sorted(
        (
            {
                "D_o": item["D_o"],
                "n_dict": len(item["D_o"]),  # type: ignore[arg-type]
                "coverage": item["coverage"],
                "cost": item["cost"],
                "unexplained": item["unexplained"],
                "BEDC_score": item["BEDC_score"],
                "coverage_above_null95": item["coverage_above_null95"],
                "null95_coverage": item["null"]["null95_coverage"],  # type: ignore[index]
            }
            for item in computed
        ),
        key=lambda item: float(item["BEDC_score"]),
        reverse=True,
    )[:10]
    best_public = {key: value for key, value in best.items() if key not in {"state", "row_ids"}}
    return {
        "organism": config["label"],
        "organism_key": organism,
        "domain": config["domain"],
        "status": "computed",
        "rows": rows,
        "base_ids": base_ids,
        "available_readouts": readouts,
        "best": best,
        "best_public": best_public,
        "top_scoring_subsets": top_subsets,
        "preliminary_subset_count": len(preliminary),
        "matched_null_subset_count": len(evaluated),
        "matched_null_subset_selection": "all empty/single/double readout subsets plus each cardinality frontier and top preliminary exact-coverage candidates",
        "dominant_residual_q": dominant_residual_q(best_state, context),
        "data_summary": built["summary"],
        "H_source_summaries": attached["source_summaries"],
        "dropped_readouts": attached["dropped"],
        "controls_used": residual_dictionary.controls_used(context["aa_order"]),  # type: ignore[arg-type]
    }


def yeast_protein_to_orf(repo: pathlib.Path, rows: dict[str, dict[str, object]]) -> dict[str, str]:
    payload = load_json(repo / "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json")
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("yeast CDS abundance payload must contain joined list")
    out: dict[str, str] = {}
    for protein_id in rows:
        if protein_id.startswith("4932."):
            orf = protein_id.split(".", 1)[1]
            if orf:
                out[protein_id] = orf
    for item in joined:
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or protein_id not in rows:
            continue
        _pid, orf, error = yeast_join_keys(item)
        if not error and isinstance(orf, str) and orf:
            out[protein_id] = orf
    return out


def component_vectors(
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    h_readouts: list[str],
    has_stability: bool,
) -> dict[str, object]:
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, _rank_q, _basis_q = project_vector(x_e, p_col)
    t_e = residualize_with_basis(matrix_rows(selected_rows, "t"), z_basis)
    p_qt, t_energy, _rank_t, _basis_t = project_vector(t_e, p_q)
    residual = subtract_vectors(p_q, p_qt)
    out: dict[str, object] = {
        "P_Q_norm2": p_q_energy,
        "P_QT": {"vector": p_qt, "fraction": bounded_unit(t_energy / p_q_energy)},
    }
    if has_stability:
        s_e = residualize_with_basis(matrix_rows(selected_rows, "s"), z_basis)
        p_qs, s_energy, _rank_s, _basis_s = project_vector(s_e, residual)
        residual = subtract_vectors(residual, p_qs)
        out["P_QS"] = {"vector": p_qs, "fraction": bounded_unit(s_energy / p_q_energy)}
    else:
        out["P_QS"] = {"status": "needs_data", "reason": "no local mRNA-stability payload"}
    if h_readouts:
        h_design: list[list[float]] = []
        for row in selected_rows:
            values: list[float] = []
            for readout in h_readouts:
                values.extend(readout_values(row, readout))
            h_design.append(values)
        h_e = residualize_with_basis(h_design, z_basis)
        p_qh, h_energy, _rank_h, _basis_h = project_vector(h_e, residual)
        out["P_QH"] = {"vector": p_qh, "fraction": bounded_unit(h_energy / p_q_energy), "readouts": h_readouts}
    else:
        out["P_QH"] = {"vector": [0.0 for _ in row_ids], "fraction": 0.0, "readouts": []}
    out["row_ids"] = row_ids
    return out


def component_by_gene(
    repo: pathlib.Path,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    vector: list[float],
) -> dict[str, float]:
    protein_to_orf = yeast_protein_to_orf(repo, rows)
    out: dict[str, float] = {}
    for index, protein_id in enumerate(row_ids):
        orf = protein_to_orf.get(protein_id)
        if orf is not None:
            out[orf] = float(vector[index])
    return out


def schema_summary(repo: pathlib.Path) -> dict[str, object]:
    occupancy = load_json(repo / OCCUPANCY_PATH)
    ordered_cds = load_json(repo / ORDERED_CDS_PATH)
    positional_profile = load_json(repo / POSITIONAL_PROFILE_PATH)
    if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict) or not isinstance(positional_profile, dict):
        raise ValueError("positional schema files must contain JSON objects")
    genes = occupancy.get("genes")
    cds = ordered_cds.get("cds")
    sample_gene = next(iter(genes.values())) if isinstance(genes, dict) and genes else {}
    sample_cds = cds[0] if isinstance(cds, list) and cds else {}
    return {
        "verified_by_python_schema_probe": True,
        "occupancy_path": OCCUPANCY_PATH,
        "occupancy_top_keys": list(occupancy.keys())[:20],
        "occupancy_genes_type": type(genes).__name__,
        "occupancy_gene_count": len(genes) if isinstance(genes, dict) else 0,
        "occupancy_sample_gene_keys": list(sample_gene.keys()) if isinstance(sample_gene, dict) else [],
        "occupancy_file_provided_5prime_lengths": sorted(
            {len(item.get("rel_occupancy_5prime", [])) for item in genes.values() if isinstance(item, dict) and isinstance(item.get("rel_occupancy_5prime"), list)}
        ) if isinstance(genes, dict) else [],
        "occupancy_file_provided_3prime_lengths": sorted(
            {len(item.get("rel_occupancy_3prime", [])) for item in genes.values() if isinstance(item, dict) and isinstance(item.get("rel_occupancy_3prime"), list)}
        ) if isinstance(genes, dict) else [],
        "ordered_cds_path": ORDERED_CDS_PATH,
        "ordered_cds_top_keys": list(ordered_cds.keys())[:20],
        "ordered_cds_list_type": type(cds).__name__,
        "ordered_cds_count": len(cds) if isinstance(cds, list) else 0,
        "ordered_cds_sample_keys": list(sample_cds.keys()) if isinstance(sample_cds, dict) else [],
        "positional_profile_path": POSITIONAL_PROFILE_PATH,
        "positional_profile_top_keys": list(positional_profile.keys())[:20],
        "positional_profile_note": "summary profile only; component boundary fitting uses occupancy genes joined to ordered CDS positions",
    }


def boundary_rows_for_component(
    *,
    joined: dict[str, dict[str, object]],
    support_map: dict[str, list[tuple[str, float]]],
    aa_by_codon: dict[str, str],
    component: dict[str, float],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for gene_id, item in joined.items():
        component_value = component.get(gene_id)
        if component_value is None:
            continue
        for row in wobble_dwell.iter_gene_windows(gene_id, item):
            codon = row.get("codon")
            if not isinstance(codon, str) or len(codon) != 3:
                continue
            hits = support_map.get(codon)
            aa = aa_by_codon.get(codon)
            if not hits or not isinstance(aa, str):
                continue
            codon_index = row.get("codon_index")
            raw_gene = item.get("occupancy")
            n_codons = raw_gene.get("n_codons") if isinstance(raw_gene, dict) else None
            if not isinstance(codon_index, int) or not isinstance(n_codons, int) or n_codons <= 1:
                continue
            occupancy = row.get("occupancy")
            if not isinstance(occupancy, (int, float)) or isinstance(occupancy, bool) or not math.isfinite(float(occupancy)):
                continue
            rho = codon_index / (n_codons - 1)
            for coordinate, q_value in hits:
                response = component_value * float(occupancy)
                rows.append(
                    {
                        "gene_id": gene_id,
                        "window": row["window"],
                        "position_bin": row["position_bin"],
                        "comparison_bin": f"{row['position_bin']}|aa:{aa}",
                        "codon": codon,
                        "amino_acid": aa,
                        "rho": rho,
                        "q_coordinate": coordinate,
                        "q_value": q_value,
                        "occupancy": float(occupancy),
                        "component_value": component_value,
                        "response": response,
                    }
                )
    return rows


def deterministic_boundary_gene_subsample(joined: dict[str, dict[str, object]]) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    total = len(joined)
    if total <= BOUNDARY_GENE_SUBSAMPLE_N:
        return dict(joined), {
            "boundary_genes_subsampled": total,
            "boundary_gene_population": total,
            "boundary_gene_subsampling_method": "not applied; joined gene count is at or below threshold",
        }
    scored = sorted(
        (
            (
                hashlib.sha256(f"{EXPERIMENT_ID}|boundary_gene_subsample|{gene_id}".encode("utf-8")).hexdigest(),
                gene_id,
            )
            for gene_id in joined
        ),
        key=lambda item: (item[0], item[1]),
    )
    selected = {gene_id for _score, gene_id in scored[:BOUNDARY_GENE_SUBSAMPLE_N]}
    return {gene_id: joined[gene_id] for gene_id in sorted(selected)}, {
        "boundary_genes_subsampled": len(selected),
        "boundary_gene_population": total,
        "boundary_gene_subsampling_method": (
            f"deterministic sha256 order on '{EXPERIMENT_ID}|boundary_gene_subsample|gene_id', "
            f"taking the first {BOUNDARY_GENE_SUBSAMPLE_N} joined genes"
        ),
    }


def demean_boundary_rows(rows: list[dict[str, object]]) -> list[dict[str, float | str]]:
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bins[str(row["comparison_bin"])].append(row)
    out: list[dict[str, float | str]] = []
    for bin_rows in bins.values():
        y_mean = mean([float(row["response"]) for row in bin_rows])
        x1_values = [float(row["q_value"]) * float(row["rho"]) for row in bin_rows]
        x2_values = [float(row["q_value"]) * float(row["rho"]) * float(row["rho"]) for row in bin_rows]
        x1_mean = mean(x1_values)
        x2_mean = mean(x2_values)
        for row, x1, x2 in zip(bin_rows, x1_values, x2_values):
            out.append(
                {
                    "window": str(row["window"]),
                    "bin": str(row["comparison_bin"]),
                    "y": float(row["response"]) - y_mean,
                    "x1": x1 - x1_mean,
                    "x2": x2 - x2_mean,
                }
            )
    return out


def prepare_boundary_bins(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bins[str(row["comparison_bin"])].append(row)
    prepared: list[dict[str, object]] = []
    for bin_id, bin_rows in bins.items():
        if len(bin_rows) < MIN_BOUNDARY_BIN_ROWS:
            continue
        y_values = [float(row["response"]) for row in bin_rows]
        rho_values = [float(row["rho"]) for row in bin_rows]
        q_values = [float(row["q_value"]) for row in bin_rows]
        x1_values = [q * rho for q, rho in zip(q_values, rho_values)]
        x2_values = [q * rho * rho for q, rho in zip(q_values, rho_values)]
        windows = [str(row["window"]) for row in bin_rows]
        y_mean = mean(y_values)
        x1_mean = mean(x1_values)
        x2_mean = mean(x2_values)
        prepared.append(
            {
                "bin": bin_id,
                "n": len(bin_rows),
                "windows": windows,
                "y": [value - y_mean for value in y_values],
                "rho": rho_values,
                "q": q_values,
                "x1": [value - x1_mean for value in x1_values],
                "x2": [value - x2_mean for value in x2_values],
            }
        )
    return prepared


def solve_two_parameter_sums(a: float, b: float, c: float, d: float, e: float) -> tuple[float, float]:
    det = a * c - b * b
    ridge = 1e-9 * max(1.0, a + c)
    if abs(det) <= EPS:
        a += ridge
        c += ridge
        det = a * c - b * b
    if abs(det) <= EPS:
        return 0.0, 0.0
    return (d * c - b * e) / det, (a * e - b * d) / det


def boundary_stats_from_prepared(prepared_bins: list[dict[str, object]], c1: float | None = None, c2: float | None = None) -> tuple[float, float, float, dict[str, float], float, float]:
    a = b = c = d = e = 0.0
    y_norm2 = 0.0
    for item in prepared_bins:
        y_values = item["y"]
        x1_values = item["x1"]
        x2_values = item["x2"]
        if not isinstance(y_values, list) or not isinstance(x1_values, list) or not isinstance(x2_values, list):
            raise ValueError("prepared boundary bin malformed")
        for y_raw, x1_raw, x2_raw in zip(y_values, x1_values, x2_values):
            y = float(y_raw)
            x1 = float(x1_raw)
            x2 = float(x2_raw)
            a += x1 * x1
            b += x1 * x2
            c += x2 * x2
            d += x1 * y
            e += x2 * y
            y_norm2 += y * y
    if c1 is None or c2 is None:
        c1, c2 = solve_two_parameter_sums(a, b, c, d, e)
    pred_norm2 = c1 * c1 * a + 2.0 * c1 * c2 * b + c2 * c2 * c
    dot = c1 * d + c2 * e
    if y_norm2 <= EPS:
        return 0.0, 0.0, 0.0, {"5prime": 0.0, "3prime": 0.0}, c1, c2
    r2 = max(0.0, min(1.0, (dot * dot) / (y_norm2 * pred_norm2))) if pred_norm2 > EPS else 0.0
    c_h = max(-1.0, min(1.0, dot / math.sqrt(y_norm2 * pred_norm2))) if pred_norm2 > EPS else 0.0
    epsilon = math.sqrt(max(0.0, pred_norm2 / y_norm2))
    by_window = {"5prime": 0.0, "3prime": 0.0}
    for item in prepared_bins:
        windows = item["windows"]
        y_values = item["y"]
        x1_values = item["x1"]
        x2_values = item["x2"]
        if not isinstance(windows, list) or not isinstance(y_values, list) or not isinstance(x1_values, list) or not isinstance(x2_values, list):
            raise ValueError("prepared boundary bin malformed")
        for window, y_raw, x1_raw, x2_raw in zip(windows, y_values, x1_values, x2_values):
            window_id = str(window)
            if window_id in by_window:
                by_window[window_id] += float(y_raw) * (c1 * float(x1_raw) + c2 * float(x2_raw))
    return r2, c_h, epsilon, by_window, c1, c2


def permuted_boundary_stats(prepared_bins: list[dict[str, object]], component_name: str, trial: int) -> float:
    permuted_bins: list[dict[str, object]] = []
    for item in prepared_bins:
        bin_id = str(item["bin"])
        q_values = item["q"]
        rho_values = item["rho"]
        y_values = item["y"]
        windows = item["windows"]
        if not isinstance(q_values, list) or not isinstance(rho_values, list) or not isinstance(y_values, list) or not isinstance(windows, list):
            raise ValueError("prepared boundary bin malformed")
        q_shuffled = list(q_values)
        seed_material = f"{EXPERIMENT_ID}|{component_name}|boundary_null|trial={trial}|bin={bin_id}|n={len(q_shuffled)}"
        seed = int.from_bytes(hashlib.sha256(seed_material.encode("utf-8")).digest()[:8], "big")
        rng = random.Random(seed)
        rng.shuffle(q_shuffled)
        x1_values = [float(q) * float(rho) for q, rho in zip(q_shuffled, rho_values)]
        x2_values = [float(q) * float(rho) * float(rho) for q, rho in zip(q_shuffled, rho_values)]
        x1_mean = mean(x1_values)
        x2_mean = mean(x2_values)
        permuted_bins.append(
            {
                "bin": bin_id,
                "n": len(q_shuffled),
                "windows": windows,
                "y": y_values,
                "rho": rho_values,
                "q": q_shuffled,
                "x1": [value - x1_mean for value in x1_values],
                "x2": [value - x2_mean for value in x2_values],
            }
        )
    r2, _c_h, _epsilon, _by_window, _c1, _c2 = boundary_stats_from_prepared(permuted_bins)
    return r2


def solve_two_parameter(rows: list[dict[str, float | str]]) -> tuple[float, float]:
    a = sum(float(row["x1"]) * float(row["x1"]) for row in rows)
    b = sum(float(row["x1"]) * float(row["x2"]) for row in rows)
    c = sum(float(row["x2"]) * float(row["x2"]) for row in rows)
    d = sum(float(row["x1"]) * float(row["y"]) for row in rows)
    e = sum(float(row["x2"]) * float(row["y"]) for row in rows)
    det = a * c - b * b
    ridge = 1e-9 * max(1.0, a + c)
    if abs(det) <= EPS:
        a += ridge
        c += ridge
        det = a * c - b * b
    if abs(det) <= EPS:
        return 0.0, 0.0
    return (d * c - b * e) / det, (a * e - b * d) / det


def boundary_r2(rows: list[dict[str, float | str]], c1: float, c2: float) -> tuple[float, float, float, dict[str, float]]:
    y_values = [float(row["y"]) for row in rows]
    predictions = [c1 * float(row["x1"]) + c2 * float(row["x2"]) for row in rows]
    y_norm2 = sum(value * value for value in y_values)
    pred_norm2 = sum(value * value for value in predictions)
    dot = sum(y * p for y, p in zip(y_values, predictions))
    if y_norm2 <= EPS:
        return 0.0, 0.0, 0.0, {"5prime": 0.0, "3prime": 0.0}
    r2 = max(0.0, min(1.0, (dot * dot) / (y_norm2 * pred_norm2))) if pred_norm2 > EPS else 0.0
    c_h = max(-1.0, min(1.0, dot / math.sqrt(y_norm2 * pred_norm2))) if pred_norm2 > EPS else 0.0
    epsilon = math.sqrt(max(0.0, pred_norm2 / y_norm2))
    by_window: dict[str, float] = {}
    for window in ["5prime", "3prime"]:
        by_window[window] = sum(
            float(row["y"]) * (c1 * float(row["x1"]) + c2 * float(row["x2"]))
            for row in rows
            if row["window"] == window
        )
    return r2, c_h, epsilon, by_window


def shuffle_q_within_bins(rows: list[dict[str, object]], component_name: str, trial: int) -> list[dict[str, object]]:
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bins[str(row["comparison_bin"])].append(row)
    out: list[dict[str, object]] = []
    for bin_id, bin_rows in bins.items():
        q_values = [float(row["q_value"]) for row in bin_rows]
        seed_material = f"{EXPERIMENT_ID}|{component_name}|boundary_null|trial={trial}|bin={bin_id}|n={len(bin_rows)}"
        seed = int.from_bytes(hashlib.sha256(seed_material.encode("utf-8")).digest()[:8], "big")
        rng = random.Random(seed)
        shuffled = list(q_values)
        rng.shuffle(shuffled)
        for row, q_value in zip(bin_rows, shuffled):
            item = dict(row)
            item["q_value"] = q_value
            out.append(item)
    return out


def boundary_null95(rows: list[dict[str, object]], component_name: str, prepared_bins: list[dict[str, object]] | None = None) -> dict[str, object]:
    if prepared_bins is not None:
        values = [permuted_boundary_stats(prepared_bins, component_name, trial) for trial in range(BOUNDARY_PERMUTATION_COUNT)]
        return {
            "permutation_count": BOUNDARY_PERMUTATION_COUNT,
            "null95_boundary_r2": percentile_nearest_rank(values, 0.95),
            "null_mean_boundary_r2": mean(values),
            "deterministic_seed": f"sha256:{EXPERIMENT_ID}|component|boundary_null|trial|position-aa-bin|n",
            "null_model": "within exact file-provided position-bin and amino-acid bin, shuffle B*_Q6 q-values against fixed component-weighted occupancy responses",
        }
    values: list[float] = []
    for trial in range(BOUNDARY_PERMUTATION_COUNT):
        demeaned = demean_boundary_rows(shuffle_q_within_bins(rows, component_name, trial))
        c1, c2 = solve_two_parameter(demeaned)
        r2, _c_h, _epsilon, _by_window = boundary_r2(demeaned, c1, c2)
        values.append(r2)
    return {
        "permutation_count": BOUNDARY_PERMUTATION_COUNT,
        "null95_boundary_r2": percentile_nearest_rank(values, 0.95),
        "null_mean_boundary_r2": mean(values),
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|component|boundary_null|trial|position-aa-bin|n",
        "null_model": "within exact file-provided position-bin and amino-acid bin, shuffle B*_Q6 q-values against fixed component-weighted occupancy responses",
    }


def analyze_boundary_component(component_name: str, rows: list[dict[str, object]]) -> dict[str, object]:
    window_counts = {
        "5prime": sum(1 for row in rows if row.get("window") == "5prime"),
        "3prime": sum(1 for row in rows if row.get("window") == "3prime"),
    }
    base = {
        "component": component_name,
        "n_rows": len(rows),
        "window_counts": window_counts,
        "model": "response = component_value * relative_occupancy; after exact position-bin x amino-acid demeaning, fit response_adj = c1*q*rho_adj + c2*q*rho^2_adj",
    }
    if len(rows) < MIN_BOUNDARY_ROWS:
        return {**base, "status": "needs_data", "reason": f"boundary rows below {MIN_BOUNDARY_ROWS}", "gate_pass": False}
    if min(window_counts.values()) < MIN_BOUNDARY_ROWS_PER_WINDOW:
        return {**base, "status": "needs_data", "reason": f"one window below {MIN_BOUNDARY_ROWS_PER_WINDOW}", "gate_pass": False}
    prepared_bins = prepare_boundary_bins(rows)
    prepared_rows = sum(int(item["n"]) for item in prepared_bins)
    if prepared_rows < MIN_BOUNDARY_ROWS:
        return {
            **base,
            "status": "needs_data",
            "reason": f"boundary rows after position-aa bin sample-size filter below {MIN_BOUNDARY_ROWS}",
            "gate_pass": False,
            "position_amino_acid_bins_kept": len(prepared_bins),
            "rows_after_bin_filter": prepared_rows,
            "min_boundary_bin_rows": MIN_BOUNDARY_BIN_ROWS,
        }
    r2, c_h, epsilon, by_window, c1, c2 = boundary_stats_from_prepared(prepared_bins)
    null = boundary_null95(rows, component_name, prepared_bins)
    null95 = float(null["null95_boundary_r2"])
    score = r2 - null95 - LAMBDA * MODEL_DF
    five = by_window.get("5prime", 0.0)
    three = by_window.get("3prime", 0.0)
    concordant = abs(five) > EPS and abs(three) > EPS and ((five > 0.0 and three > 0.0) or (five < 0.0 and three < 0.0))
    gate_pass = score > 0.0 and c_h > 0.0 and concordant
    return {
        **base,
        "status": "computed",
        "base": mean([float(row["response"]) for row in rows]),
        "position_amino_acid_bins_kept": len(prepared_bins),
        "rows_after_bin_filter": prepared_rows,
        "min_boundary_bin_rows": MIN_BOUNDARY_BIN_ROWS,
        "epsilon": epsilon,
        "c1": c1,
        "c2": c2,
        "boundary_r2": r2,
        "C_H": c_h,
        "Null95": null95,
        "lambda_DL": LAMBDA,
        "DL": MODEL_DF,
        "description_length_penalized_score": score,
        "permutation_null": null,
        "window_signed_alignment": by_window,
        "5p3p_concordant": concordant,
        "gate_pass": gate_pass,
        "interpretation": (
            "low-dimensional boundary kernel passes only if both file-provided 5prime and 3prime windows carry the same signed fitted alignment"
            if gate_pass
            else "not promoted to a boundary kernel because Null95, DL, C_H, or 5prime/3prime concordance failed"
        ),
    }


def kernel_shape_sharing(component_boundary: dict[str, dict[str, object]]) -> dict[str, object]:
    computed = {
        name: value
        for name, value in component_boundary.items()
        if value.get("status") == "computed"
    }
    pairs: list[dict[str, object]] = []
    for left, right in itertools.combinations(sorted(computed), 2):
        l_item = computed[left]
        r_item = computed[right]
        lv = [float(l_item.get("c1", 0.0)), float(l_item.get("c2", 0.0))]
        rv = [float(r_item.get("c1", 0.0)), float(r_item.get("c2", 0.0))]
        denom = math.sqrt(sum(x * x for x in lv) * sum(x * x for x in rv))
        cosine = sum(a * b for a, b in zip(lv, rv)) / denom if denom > EPS else 0.0
        pairs.append({"components": [left, right], "shape_cosine_c1_c2": cosine})
    return {
        "definition": "kernel-shape sharing is the cosine between fitted (c1,c2) coefficient vectors; it is descriptive and not a mechanism claim",
        "pairs": pairs,
    }


def yeast_boundary_response(repo: pathlib.Path, context: dict[str, object], yeast_result: dict[str, object]) -> dict[str, object] | str:
    if yeast_result.get("status") != "computed":
        return "needs_data"
    for path in [OCCUPANCY_PATH, ORDERED_CDS_PATH, POSITIONAL_PROFILE_PATH]:
        if not (repo / path).exists():
            return "needs_data"
    rows = yeast_result["rows"]
    best = yeast_result["best"]
    if not isinstance(rows, dict) or not isinstance(best, dict):
        raise ValueError("yeast compression result malformed")
    row_ids = best.get("row_ids")
    d_o = best.get("D_o")
    if not isinstance(row_ids, list) or not isinstance(d_o, list):
        raise ValueError("yeast best dictionary malformed")
    h_readouts = [str(readout) for readout in d_o if str(readout) in residual_dictionary.H_CANDIDATES]
    components = component_vectors(
        rows=rows,  # type: ignore[arg-type]
        row_ids=[str(item) for item in row_ids],
        h_readouts=h_readouts,
        has_stability=True,
    )
    occupancy = load_json(repo / OCCUPANCY_PATH)
    ordered_cds = load_json(repo / ORDERED_CDS_PATH)
    if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict):
        raise ValueError("yeast position files must contain JSON objects")
    joined, join_schema = wobble_dwell.schema_and_join(occupancy, ordered_cds)
    joined, boundary_subsample = deterministic_boundary_gene_subsample(joined)
    w_context = wobble_dwell.q6_context(repo)
    support_map = w_context["support_map"]
    aa_by_codon = w_context["aa_by_codon"]
    if not isinstance(support_map, dict) or not isinstance(aa_by_codon, dict):
        raise ValueError("wobble q6 context malformed")
    component_boundary: dict[str, dict[str, object]] = {}
    for component_name in ["P_QT", "P_QS", "P_QH"]:
        component = components.get(component_name)
        if not isinstance(component, dict) or not isinstance(component.get("vector"), list):
            component_boundary[component_name] = {"component": component_name, "status": "needs_data", "reason": "component vector unavailable", "gate_pass": False}
            continue
        gene_values = component_by_gene(repo, rows, [str(item) for item in row_ids], component["vector"])  # type: ignore[arg-type]
        b_rows = boundary_rows_for_component(
            joined=joined,
            support_map=support_map,  # type: ignore[arg-type]
            aa_by_codon=aa_by_codon,  # type: ignore[arg-type]
            component=gene_values,
        )
        analyzed = analyze_boundary_component(component_name, b_rows)
        analyzed["component_fraction_of_P_Q"] = component.get("fraction")
        if component_name == "P_QH":
            analyzed["H_readouts"] = component.get("readouts")
        component_boundary[component_name] = analyzed
    return {
        "organism": "Saccharomyces cerevisiae",
        "organism_key": "saccharomyces_cerevisiae",
        "status": "computed",
        "position_data_scope": "yeast only; other organisms in this experiment have no local positional occupancy payload",
        "schema_and_gene_id_join": join_schema,
        "boundary_sampling": boundary_subsample,
        "component_boundary_response": component_boundary,
        "kernel_shape_sharing": kernel_shape_sharing(component_boundary),
        "position_confound_controlled": {
            "controlled": True,
            "method": "exact file-provided 5prime/3prime offset crossed with amino-acid identity; response and q-polynomial regressors are demeaned within that bin; null shuffles q-values only inside the same bin",
            "does_not_use_preset_window_constants": True,
        },
    }


def public_organism_result(result: dict[str, object], boundary_response: object) -> dict[str, object]:
    if result.get("status") != "computed":
        return {
            "organism": result.get("organism"),
            "organism_key": result.get("organism_key"),
            "status": result.get("status"),
            "D_o_star": [],
            "coverage": None,
            "cost": None,
            "unexplained": None,
            "dominant_residual_q": None,
            "n_dict": 0,
            "compression_bound_le_3": False,
            "boundary_response": boundary_response,
            "reason": result.get("reason"),
        }
    best = result["best"]
    if not isinstance(best, dict):
        raise ValueError("best result malformed")
    d_o = best["D_o"]
    if not isinstance(d_o, list):
        raise ValueError("D_o malformed")
    return {
        "organism": result["organism"],
        "organism_key": result["organism_key"],
        "D_o_star": d_o,
        "coverage": best["coverage"],
        "cost": best["cost"],
        "unexplained": best["unexplained"],
        "dominant_residual_q": result["dominant_residual_q"],
        "n_dict": len(d_o),
        "compression_bound_le_3": len(d_o) <= 3,
        "coverage_above_null95": best["coverage_above_null95"],
        "null95_coverage": best["null"]["null95_coverage"],
        "BEDC_score": best["BEDC_score"],
        "boundary_response": boundary_response,
    }


def compression_definition() -> dict[str, object]:
    return {
        "Coverage(D_o)": "1 - ||P_Q - Pi_{D_o} P_Q||^2 / ||P_Q||^2, after local controls and active joins",
        "Cost(D_o)": "DL(D_o) + JoinPenalty(D_o) + NullPenalty(D_o)",
        "BEDC_score": "B(D_o) = Coverage(D_o) - lambda * Cost(D_o)",
        "lambda": LAMBDA,
        "cost_scaling": {
            "DL": "number of readout columns in D_o",
            "JoinPenalty": "(rho_join / lambda) * abs(n_join - n_base) / n_base",
            "NullPenalty": "matched label-permutation Null95 coverage / lambda",
            "equivalent_unscaled_score": "Coverage - Null95 - lambda*DL - rho_join*join_shift",
        },
        "D_o_star": "argmax over all available measured_te, mrna_stability where present, and H-candidate readout subsets, including the empty subset",
        "matched_null": f"{PERMUTATION_COUNT} deterministic row-label permutations of the residualized readout subspace on the same active join",
        "search_procedure": "all available subsets are scanned for exact coverage; matched null penalties are then computed for all empty/single/double subsets, each cardinality frontier, and the top preliminary candidates before selecting D_o_star",
    }


def cannot_claim() -> list[str]:
    return [
        "descriptive projection compression, not causal regulation or a biochemical mechanism",
        "occupancy is relative ribosome occupancy, not direct dwell-time measurement",
        "component boundary response is component-weighted occupancy association, not a perturbation result",
        "position data are available only for yeast in this local payload; human, zebrafish, and E. coli boundary responses are needs_data",
        "correlation and projection energy do not imply mechanism",
        "negative or absent kernels are reported directly and are not rescued by 5prime-only ramp signals",
        "readout availability differs by organism, so D_o_star compares local measured dictionaries rather than a universal inventory",
    ]


def checks_for(table: list[dict[str, object]], yeast_boundary: object) -> list[dict[str, object]]:
    computed = [row for row in table if row.get("coverage") is not None]
    compressed = [row for row in computed if row.get("compression_bound_le_3")]
    above_null = [row for row in computed if row.get("coverage_above_null95")]
    boundary_pass: list[str] = []
    if isinstance(yeast_boundary, dict):
        components = yeast_boundary.get("component_boundary_response")
        if isinstance(components, dict):
            boundary_pass = [name for name, item in components.items() if isinstance(item, dict) and item.get("gate_pass")]
    return [
        {
            "name": "compression_dictionary_computed",
            "passed": bool(computed),
            "actual": [{"organism_key": row.get("organism_key"), "n_dict": row.get("n_dict"), "coverage": row.get("coverage")} for row in computed],
            "expected": "at least one organism has a finite P_Q compression scan",
        },
        {
            "name": "coverage_exceeds_matched_null",
            "passed": len(above_null) == len(computed) and bool(computed),
            "actual": [{"organism_key": row.get("organism_key"), "coverage": row.get("coverage"), "null95": row.get("null95_coverage")} for row in computed],
            "expected": "D_o_star coverage is above the matched readout-label Null95 for every computed organism",
        },
        {
            "name": "minimal_dictionary_bound",
            "passed": len(compressed) >= math.ceil(len(computed) / 2) if computed else False,
            "actual": [{"organism_key": row.get("organism_key"), "D_o_star": row.get("D_o_star"), "n_dict": row.get("n_dict"), "le_3": row.get("compression_bound_le_3")} for row in computed],
            "expected": "the falsifiable bound |D_o_star| <= 3 holds for a majority of computed organisms",
        },
        {
            "name": "component_boundary_response",
            "passed": bool(boundary_pass) or yeast_boundary == "needs_data",
            "actual": {"yeast_boundary_components_passing": boundary_pass, "yeast_boundary_status": yeast_boundary if isinstance(yeast_boundary, str) else "computed"},
            "expected": "at least one yeast component passes Null95 + lambda_DL + C_H + 5prime/3prime concordance when position data are available",
        },
    ]


def main() -> None:
    try:
        repo = pathlib.Path(__file__).resolve().parents[3]
        context = residual_dictionary.q6_context(repo)
        schema = schema_summary(repo)
        organism_results: dict[str, dict[str, object]] = {}
        for config in residual_dictionary.ORGANISMS:
            result = build_organism_compression(repo, context, config)
            organism_results[str(config["key"])] = result

        yeast_boundary = yeast_boundary_response(repo, context, organism_results.get("saccharomyces_cerevisiae", {}))
        table: list[dict[str, object]] = []
        for key, result in organism_results.items():
            boundary = yeast_boundary if key == "saccharomyces_cerevisiae" else "needs_data"
            table.append(public_organism_result(result, boundary))
        checks = checks_for(table, yeast_boundary)
        computed = [row for row in table if row.get("coverage") is not None]
        compressed = [row for row in computed if row.get("compression_bound_le_3")]
        boundary_pass = []
        component_boundary = "needs_data"
        if isinstance(yeast_boundary, dict):
            component_boundary = yeast_boundary["component_boundary_response"]  # type: ignore[index]
            if isinstance(component_boundary, dict):
                boundary_pass = [name for name, item in component_boundary.items() if isinstance(item, dict) and item.get("gate_pass")]
        if not computed:
            status = "needs_data"
            verdict = "No organism had enough joined readout data to compute the compression scan."
        elif len(compressed) >= math.ceil(len(computed) / 2) and (boundary_pass or yeast_boundary == "needs_data"):
            status = "passed"
            verdict = "The minimal readout compression bound holds for a majority of computed organisms, and the yeast boundary response gate is satisfied where positional data permit."
        else:
            status = "failed"
            verdict = "The compression or boundary-response gate failed under the matched-null, description-length, join, C_H, and 5prime/3prime-concordance rules."
        public_details = {
            key: {
                item_key: item_value
                for item_key, item_value in result.items()
                if item_key not in {"rows", "base_ids", "best"}
            }
            for key, result in organism_results.items()
        }
        emit(
            status,
            checks=checks,
            compression_definition=compression_definition(),
            schema_verification=schema,
            organism_dictionary_compression_table=table,
            component_boundary_response=component_boundary,
            organism_details=public_details,
            verdict=verdict,
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit("failed", error=str(exc), reason="minimal dictionary compression experiment could not be computed")


if __name__ == "__main__":
    main()

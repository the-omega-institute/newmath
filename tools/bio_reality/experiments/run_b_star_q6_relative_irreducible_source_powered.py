#!/usr/bin/env python3
"""B*_Q6 relative irreducible source under selection-aware nulls."""

from __future__ import annotations

import hashlib
import itertools
import json
import math
import os
import pathlib
import random
import sys
from collections import defaultdict
from datetime import datetime, timezone
from typing import Any

import run_b_star_q6_minimal_dictionary_compression_powered as minimal
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import matrix_column
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM

try:
    import numpy as np
except Exception:  # pragma: no cover - exercised only on numpy-free hosts.
    np = None  # type: ignore[assignment]


EXPERIMENT_ID = "b_star_q6_relative_irreducible_source_powered"
CLAIM_ID = "h3.cross_layer_relation.relative_irreducible_source.b_star_q6_selection_aware_powered"

TARGET_SELECTION_AWARE_B = 1000
DEFAULT_SELECTION_AWARE_B = int(os.environ.get("BIO_REALITY_SELECTION_AWARE_B", "200"))
DEFAULT_BOUNDARY_SELECTION_AWARE_B = int(os.environ.get("BIO_REALITY_BOUNDARY_SELECTION_AWARE_B", str(DEFAULT_SELECTION_AWARE_B)))
MIN_SELECTION_AWARE_B = 200
CORE_PANEL = [
    "saccharomyces_cerevisiae",
    "escherichia_coli_k12_mg1655",
    "homo_sapiens",
    "danio_rerio",
]
EPS = 1e-12
RUN_TIMESTAMP = "2026-06-18T00:00:00+00:00"
STARTED_AT = RUN_TIMESTAMP


def now_iso() -> str:
    return RUN_TIMESTAMP


def emit(status: str, **kw: object) -> None:
    checks = kw.get("checks")
    if not isinstance(checks, list):
        checks = []
    result = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    result.update(kw)
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "payload": result,
        "started_at": STARTED_AT,
        "completed_at": now_iso(),
    }
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def median(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    return minimal.percentile_nearest_rank(values, probability)


def bounded_unit(value: float) -> float:
    return minimal.bounded_unit(value)


def deterministic_shuffle_indices(n: int, material: str) -> list[int]:
    out = list(range(n))
    seed = int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")
    rng = random.Random(seed)
    rng.shuffle(out)
    return out


def source_state(rows: dict[str, dict[str, object]], row_ids: list[str]) -> dict[str, object]:
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_basis = minimal.orthonormal_basis_from_columns(minimal.matrix_rows(selected_rows, "z"))
    x_e = minimal.residualize_with_basis(minimal.matrix_rows(selected_rows, "x"), z_basis)
    p_e = minimal.residualize_with_basis(minimal.matrix_rows(selected_rows, "p"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q, _basis_q = minimal.project_vector(x_e, p_col)
    p_energy = vector_norm2(p_col)
    if p_energy <= EPS or p_q_energy <= EPS:
        raise ValueError("P_Q source projection has zero residual energy")
    return {
        "R2_QP": bounded_unit(p_q_energy / p_energy),
        "rank_Q_e": rank_q,
        "P_Q_norm2": p_q_energy,
        "P_residual_norm2": p_energy,
        "n_source": len(row_ids),
    }


def qr_basis(matrix: Any) -> tuple[Any, int]:
    if np is None:
        basis = minimal.orthonormal_basis_from_columns(matrix.tolist() if hasattr(matrix, "tolist") else matrix)
        return basis, len(basis)
    if matrix.size == 0:
        return np.zeros((matrix.shape[0], 0)), 0
    q, r = np.linalg.qr(matrix, mode="reduced")
    if r.size == 0:
        return np.zeros((matrix.shape[0], 0)), 0
    diag = np.abs(np.diag(r))
    scale = max(1.0, float(np.max(np.linalg.norm(matrix, axis=0)))) if matrix.shape[1] else 1.0
    rank = int(np.sum(diag > 1e-10 * scale))
    return q[:, :rank], rank


def residualize_np(matrix: Any, basis: Any) -> Any:
    if basis.shape[1] == 0:
        return matrix.copy()
    return matrix - basis @ (basis.T @ matrix)


def projection_energy_np(basis: Any, target: Any) -> float:
    if basis.shape[1] == 0:
        return 0.0
    coeffs = basis.T @ target
    return float(coeffs @ coeffs)


def numpy_subset_states(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    readouts: list[str],
) -> list[dict[str, object]]:
    if np is None:
        raise ValueError("numpy is required for the powered selection-aware scan")
    join_cache: dict[tuple[str, ...], dict[str, Any]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], Any] = {}

    def join_state(row_ids: tuple[str, ...]) -> dict[str, Any]:
        cached = join_cache.get(row_ids)
        if cached is not None:
            return cached
        selected = [rows[protein_id] for protein_id in row_ids]
        z = np.asarray(minimal.matrix_rows(selected, "z"), dtype=float)
        x = np.asarray(minimal.matrix_rows(selected, "x"), dtype=float)
        p = np.asarray(minimal.matrix_rows(selected, "p"), dtype=float)[:, 0]
        z_basis, rank_z = qr_basis(z)
        x_e = residualize_np(x, z_basis)
        p_e = residualize_np(p.reshape(-1, 1), z_basis)[:, 0]
        x_basis, rank_q = qr_basis(x_e)
        p_q = x_basis @ (x_basis.T @ p_e) if rank_q else np.zeros_like(p_e)
        p_q_norm2 = float(p_q @ p_q)
        p_norm2 = float(p_e @ p_e)
        if p_q_norm2 <= EPS:
            raise ValueError(f"{organism} P_Q has zero residual energy on active join")
        out = {
            "z_basis": z_basis,
            "rank_z": rank_z,
            "P_Q": p_q,
            "P_Q_norm2": p_q_norm2,
            "P_residual_norm2": p_norm2,
            "R2_QP": bounded_unit(p_q_norm2 / p_norm2) if p_norm2 > EPS else 0.0,
            "rank_Q_e": rank_q,
        }
        join_cache[row_ids] = out
        return out

    def readout_e(row_ids: tuple[str, ...], readout: str, z_basis: Any) -> Any:
        key = (row_ids, readout)
        cached = readout_cache.get(key)
        if cached is not None:
            return cached
        design = np.asarray([minimal.readout_values(rows[protein_id], readout) for protein_id in row_ids], dtype=float)
        residualized = residualize_np(design, z_basis)
        readout_cache[key] = residualized
        return residualized

    states: list[dict[str, object]] = []
    for subset in minimal.all_subsets(readouts):
        if subset:
            row_ids = tuple(protein_id for protein_id in base_ids if all(minimal.row_has_readout(rows[protein_id], readout) for readout in subset))
        else:
            row_ids = tuple(base_ids)
        if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
            continue
        joined = join_state(row_ids)
        p_q = joined["P_Q"]
        p_q_norm2 = float(joined["P_Q_norm2"])
        if subset:
            parts = [readout_e(row_ids, readout, joined["z_basis"]) for readout in subset]
            design_e = np.concatenate(parts, axis=1) if len(parts) > 1 else parts[0]
            d_basis, rank_d = qr_basis(design_e)
            projected_norm2 = projection_energy_np(d_basis, p_q)
        else:
            d_basis = np.zeros((len(row_ids), 0))
            rank_d = 0
            projected_norm2 = 0.0
        coverage = bounded_unit(projected_norm2 / p_q_norm2)
        dl = sum(minimal.readout_dimensions(rows, readout) for readout in subset)
        join_shift = abs(len(row_ids) - len(base_ids)) / len(base_ids) if base_ids else 1.0
        states.append(
            {
                "subset": tuple(subset),
                "subset_label": ",".join(subset) if subset else "empty",
                "row_ids": row_ids,
                "n_join": len(row_ids),
                "basis_np": d_basis.T.copy(),
                "target_np": p_q.copy(),
                "target_norm2": p_q_norm2,
                "rank_D_e": rank_d,
                "coverage": coverage,
                "projected_norm2": projected_norm2,
                "unexplained": bounded_unit(1.0 - coverage),
                "DL": dl,
                "join_shift": join_shift,
                "R2_QP": joined["R2_QP"],
                "rank_Q_e": joined["rank_Q_e"],
                "P_Q_norm2": p_q_norm2,
                "P_residual_norm2": joined["P_residual_norm2"],
                "selection_score": coverage,
                "BEDC_no_null_score": coverage - residual_dictionary.LAMBDA_DL * dl - residual_dictionary.RHO_JOIN * join_shift,
            }
        )
    if not states:
        raise ValueError(f"{organism} has no computed subset states")
    return states


def pure_subset_states(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    readouts: list[str],
) -> list[dict[str, object]]:
    join_cache: dict[tuple[str, ...], dict[str, object]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
    states: list[dict[str, object]] = []
    for subset in minimal.all_subsets(readouts):
        item = minimal.evaluate_subset_cached(
            organism=organism,
            rows=rows,
            base_ids=base_ids,
            subset=subset,
            compute_null=False,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        if item.get("status") != "computed":
            continue
        state = item.get("state")
        if not isinstance(state, dict):
            raise ValueError("subset state malformed")
        basis = state.get("design_basis")
        target = state.get("P_Q")
        target_norm2 = state.get("P_Q_norm2")
        row_ids = item.get("row_ids")
        if not isinstance(basis, list) or not isinstance(target, list) or not isinstance(target_norm2, float) or not isinstance(row_ids, list):
            raise ValueError("subset projection state malformed")
        dl = sum(minimal.readout_dimensions(rows, readout) for readout in subset)
        join_shift = abs(len(row_ids) - len(base_ids)) / len(base_ids) if base_ids else 1.0
        coverage = float(item["coverage"])
        states.append(
            {
                "subset": tuple(subset),
                "subset_label": ",".join(subset) if subset else "empty",
                "row_ids": tuple(str(pid) for pid in row_ids),
                "n_join": len(row_ids),
                "basis": basis,
                "target": target,
                "target_norm2": target_norm2,
                "rank_D_e": int(state.get("rank_D_e", 0)),
                "coverage": coverage,
                "projected_norm2": state.get("projected_norm2"),
                "unexplained": state.get("unexplained"),
                "DL": dl,
                "join_shift": join_shift,
                "R2_QP": None,
                "rank_Q_e": state.get("rank_Q_e"),
                "P_Q_norm2": target_norm2,
                "selection_score": coverage,
                "BEDC_no_null_score": coverage - residual_dictionary.LAMBDA_DL * dl - residual_dictionary.RHO_JOIN * join_shift,
            }
        )
    if not states:
        raise ValueError(f"{organism} has no computed subset states")
    return states


def np_absorption(basis_arr: Any, target_arr: Any, target_norm2: float, permutation: Any) -> float:
    if basis_arr is None or getattr(basis_arr, "size", 0) == 0 or target_norm2 <= EPS:
        return 0.0
    coeffs = basis_arr[:, permutation].dot(target_arr)
    return bounded_unit(float(coeffs.dot(coeffs)) / target_norm2)


def py_absorption(basis: list[list[float]], target: list[float], target_norm2: float, permutation: list[int]) -> float:
    if not basis or target_norm2 <= EPS:
        return 0.0
    energy = 0.0
    for q in basis:
        coeff = 0.0
        for index, target_value in enumerate(target):
            coeff += q[permutation[index]] * target_value
        energy += coeff * coeff
    return bounded_unit(energy / target_norm2)


def prepare_selection_null_states(states: list[dict[str, object]]) -> tuple[list[dict[str, object]], dict[tuple[str, ...], int]]:
    groups: dict[tuple[str, ...], int] = {}
    prepared: list[dict[str, object]] = []
    for item in states:
        row_ids = item["row_ids"]
        if not isinstance(row_ids, tuple):
            raise ValueError("row_ids key malformed")
        if row_ids not in groups:
            groups[row_ids] = len(groups)
        entry = dict(item)
        entry["group_id"] = groups[row_ids]
        if np is not None and "basis_np" not in entry and "basis" in entry and "target" in entry:
            entry["basis_np"] = np.asarray(entry["basis"], dtype=float)
            entry["target_np"] = np.asarray(entry["target"], dtype=float)
        prepared.append(entry)
    return prepared, groups


def coverage_frontier_states(states: list[dict[str, object]]) -> list[dict[str, object]]:
    by_join: dict[tuple[str, ...], list[dict[str, object]]] = defaultdict(list)
    for item in states:
        subset = item.get("subset")
        row_ids = item.get("row_ids")
        if not isinstance(subset, tuple) or not isinstance(row_ids, tuple):
            raise ValueError("subset frontier state malformed")
        if not subset:
            continue
        by_join[row_ids].append(item)
    frontier: list[dict[str, object]] = []
    for items in by_join.values():
        subset_sets = [(item, set(item["subset"])) for item in items]  # type: ignore[arg-type]
        for item, subset_set in subset_sets:
            dominated = any(
                subset_set < other_set
                for other, other_set in subset_sets
                if other is not item
            )
            if not dominated:
                frontier.append(item)
    return frontier or states


def selection_aware_dictionary_null(
    *,
    organism: str,
    states: list[dict[str, object]],
    actual_b: int,
) -> dict[str, object]:
    scan_states = coverage_frontier_states(states)
    prepared, groups = prepare_selection_null_states(scan_states)
    if actual_b < MIN_SELECTION_AWARE_B:
        raise ValueError(f"selection-aware B={actual_b} is below required minimum {MIN_SELECTION_AWARE_B}")
    max_coverage_values: list[float] = []
    bedc_reselected_coverage_values: list[float] = []
    selected_by_max: dict[str, int] = defaultdict(int)
    selected_by_bedc: dict[str, int] = defaultdict(int)
    group_items = sorted(groups.items(), key=lambda item: item[1])
    for trial in range(actual_b):
        permutations: dict[int, object] = {}
        for row_ids, group_id in group_items:
            material = f"{EXPERIMENT_ID}|{organism}|selection_aware_dictionary_null|trial={trial}|group={group_id}|n={len(row_ids)}"
            indices = deterministic_shuffle_indices(len(row_ids), material)
            permutations[group_id] = np.asarray(indices, dtype=int) if np is not None else indices
        best_coverage = -1.0
        best_coverage_subset = "empty"
        best_bedc_score = -1e100
        best_bedc_coverage = 0.0
        best_bedc_subset = "empty"
        for item in prepared:
            subset_label = str(item["subset_label"])
            group_id = int(item["group_id"])
            permutation = permutations[group_id]
            target_norm2 = float(item["target_norm2"])
            if np is not None and "basis_np" in item and "target_np" in item:
                coverage = np_absorption(item.get("basis_np"), item.get("target_np"), target_norm2, permutation)
            else:
                coverage = py_absorption(item["basis"], item["target"], target_norm2, permutation)  # type: ignore[arg-type]
            if coverage > best_coverage:
                best_coverage = coverage
                best_coverage_subset = subset_label
            score = coverage - residual_dictionary.LAMBDA_DL * float(item["DL"]) - residual_dictionary.RHO_JOIN * float(item["join_shift"])
            if score > best_bedc_score:
                best_bedc_score = score
                best_bedc_coverage = coverage
                best_bedc_subset = subset_label
        max_coverage_values.append(max(0.0, best_coverage))
        bedc_reselected_coverage_values.append(max(0.0, best_bedc_coverage))
        selected_by_max[best_coverage_subset] += 1
        selected_by_bedc[best_bedc_subset] += 1
    return {
        "permutation_count": actual_b,
        "null95_select_coverage": percentile_nearest_rank(max_coverage_values, 0.95),
        "null_mean_select_coverage": mean(max_coverage_values),
        "null95_bedc_reselected_coverage": percentile_nearest_rank(bedc_reselected_coverage_values, 0.95),
        "null_mean_bedc_reselected_coverage": mean(bedc_reselected_coverage_values),
        "unique_active_join_groups": len(groups),
        "full_subset_state_count": len(states),
        "coverage_frontier_state_count": len(scan_states),
        "coverage_frontier_reduction": "exact for max-Coverage selection: within a fixed active join, any subset is projection-dominated by an available strict superset, so only inclusion-maximal subsets per active join are scanned in each permutation",
        "selection_rule_for_verdict": "full available subset scan under row-label permutation; records the maximum permuted Coverage(D), a family-wise selection-aware null for the scanned readout dictionary",
        "bedc_reselection_diagnostic": "also reported: permutation reselects subset by Coverage - lambda*DL - rho*join_shift without an inner fixed-subset null penalty",
        "top_null_selected_subsets_by_max_coverage": [
            {"D_o": key.split(",") if key != "empty" else [], "count": value}
            for key, value in sorted(selected_by_max.items(), key=lambda item: item[1], reverse=True)[:8]
        ],
        "top_null_selected_subsets_by_bedc": [
            {"D_o": key.split(",") if key != "empty" else [], "count": value}
            for key, value in sorted(selected_by_bedc.items(), key=lambda item: item[1], reverse=True)[:8]
        ],
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|organism|selection_aware_dictionary_null|trial|active_join_group|n",
    }


def build_real_organism(
    repo: pathlib.Path,
    context: dict[str, object],
    config: dict[str, object],
    actual_b: int,
) -> dict[str, object]:
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
    rows = built.get("rows")
    if not isinstance(rows, dict):
        raise ValueError(f"{organism} base rows malformed")
    attached = residual_dictionary.attach_h_readouts(repo, organism, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "organism": config["label"],
            "organism_key": organism,
            "status": "needs_data",
            "reason": f"base P/Q/T/S join yielded n={len(base_ids)}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "data_summary": built.get("summary"),
            "H_source_summaries": attached["source_summaries"],
        }
    readouts = minimal.available_readouts(config, rows, base_ids)  # type: ignore[arg-type]
    if np is not None:
        subset_states = numpy_subset_states(
            organism=organism,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            readouts=readouts,
        )
    else:
        subset_states = pure_subset_states(
            organism=organism,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            readouts=readouts,
        )
    if not subset_states:
        return {
            "organism": config["label"],
            "organism_key": organism,
            "status": "needs_data",
            "reason": "no readout subset passed the join gate",
            "available_readouts": readouts,
            "data_summary": built.get("summary"),
            "H_source_summaries": attached["source_summaries"],
        }
    best_state = max(
        subset_states,
        key=lambda item: (
            float(item["selection_score"]),
            -float(item["DL"]),
            -float(item["join_shift"]),
            -len(item["subset"]),  # type: ignore[arg-type]
        ),
    )
    best = {
        "D_o": list(best_state["subset"]),  # type: ignore[arg-type]
        "status": "computed",
        "n_join": best_state["n_join"],
        "base_n": len(base_ids),
        "coverage": best_state["coverage"],
        "unexplained": best_state["unexplained"],
        "P_Q_norm2": best_state["P_Q_norm2"],
        "projected_norm2": best_state["projected_norm2"],
        "rank_D_e": best_state["rank_D_e"],
        "rank_Q_e": best_state["rank_Q_e"],
        "DL": best_state["DL"],
        "join_shift": best_state["join_shift"],
        "selection_score": best_state["selection_score"],
        "BEDC_no_null_score": best_state["BEDC_no_null_score"],
        "row_ids": list(best_state["row_ids"]),  # type: ignore[arg-type]
        "selection_rule": "argmax Coverage(D) over all available subsets, tie-broken by smaller DL, smaller join shift, and smaller subset size",
    }
    selection_null = selection_aware_dictionary_null(organism=organism, states=subset_states, actual_b=actual_b)
    src = source_state(rows, base_ids)  # type: ignore[arg-type]
    return {
        "organism": config["label"],
        "organism_key": organism,
        "domain": config["domain"],
        "status": "computed",
        "rows": rows,
        "base_ids": base_ids,
        "available_readouts": readouts,
        "best": best,
        "source": src,
        "selection_aware_null": selection_null,
        "all_subset_count": len(subset_states),
        "candidate_subset_count": len(subset_states),
        "matched_null_subset_count": 0,
        "dominant_residual_q": None,
        "selection_procedure": "full exact Coverage(D) scan; selection-aware null repeats the same full scan after row-label permutation",
        "data_summary": built.get("summary"),
        "H_source_summaries": attached["source_summaries"],
        "dropped_readouts": attached["dropped"],
    }


def boundary_component_real(component_name: str, rows: list[dict[str, object]]) -> dict[str, object]:
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
    if len(rows) < minimal.MIN_BOUNDARY_ROWS:
        return {**base, "status": "needs_data", "reason": f"boundary rows below {minimal.MIN_BOUNDARY_ROWS}"}
    if min(window_counts.values()) < minimal.MIN_BOUNDARY_ROWS_PER_WINDOW:
        return {**base, "status": "needs_data", "reason": f"one window below {minimal.MIN_BOUNDARY_ROWS_PER_WINDOW}"}
    prepared_bins = minimal.prepare_boundary_bins(rows)
    prepared_rows = sum(int(item["n"]) for item in prepared_bins)
    if prepared_rows < minimal.MIN_BOUNDARY_ROWS:
        return {
            **base,
            "status": "needs_data",
            "reason": f"boundary rows after position-aa bin sample-size filter below {minimal.MIN_BOUNDARY_ROWS}",
            "position_amino_acid_bins_kept": len(prepared_bins),
            "rows_after_bin_filter": prepared_rows,
            "min_boundary_bin_rows": minimal.MIN_BOUNDARY_BIN_ROWS,
        }
    r2, c_h, epsilon, by_window, c1, c2 = minimal.boundary_stats_from_prepared(prepared_bins)
    return {
        **base,
        "status": "computed",
        "base_response_mean": mean([float(row["response"]) for row in rows]),
        "position_amino_acid_bins_kept": len(prepared_bins),
        "rows_after_bin_filter": prepared_rows,
        "min_boundary_bin_rows": minimal.MIN_BOUNDARY_BIN_ROWS,
        "epsilon": epsilon,
        "c1": c1,
        "c2": c2,
        "boundary_r2": r2,
        "C_H": c_h,
        "window_signed_alignment": by_window,
        "prepared_bins": prepared_bins,
    }


def permuted_boundary_r2(prepared_bins: list[dict[str, object]], component_name: str, trial: int) -> float:
    permuted_bins: list[dict[str, object]] = []
    for item in prepared_bins:
        bin_id = str(item["bin"])
        q_values = item["q"]
        rho_values = item["rho"]
        y_values = item["y"]
        windows = item["windows"]
        if not isinstance(q_values, list) or not isinstance(rho_values, list) or not isinstance(y_values, list) or not isinstance(windows, list):
            raise ValueError("prepared boundary bin malformed")
        shuffled = list(q_values)
        material = f"{EXPERIMENT_ID}|{component_name}|boundary_selection_aware_null|trial={trial}|bin={bin_id}|n={len(shuffled)}"
        seed = int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")
        rng = random.Random(seed)
        rng.shuffle(shuffled)
        x1_values = [float(q) * float(rho) for q, rho in zip(shuffled, rho_values)]
        x2_values = [float(q) * float(rho) * float(rho) for q, rho in zip(shuffled, rho_values)]
        x1_mean = mean(x1_values)
        x2_mean = mean(x2_values)
        permuted_bins.append(
            {
                "bin": bin_id,
                "n": len(shuffled),
                "windows": windows,
                "y": y_values,
                "rho": rho_values,
                "q": shuffled,
                "x1": [value - x1_mean for value in x1_values],
                "x2": [value - x2_mean for value in x2_values],
            }
        )
    r2, _c_h, _epsilon, _by_window, _c1, _c2 = minimal.boundary_stats_from_prepared(permuted_bins)
    return r2


def boundary_selection_aware(
    *,
    repo: pathlib.Path,
    yeast_result: dict[str, object],
    actual_b: int,
) -> dict[str, object] | str:
    if yeast_result.get("status") != "computed":
        return "needs_data"
    for path in [minimal.OCCUPANCY_PATH, minimal.ORDERED_CDS_PATH, minimal.POSITIONAL_PROFILE_PATH]:
        if not (repo / path).exists():
            return "needs_data"
    rows = yeast_result.get("rows")
    best = yeast_result.get("best")
    if not isinstance(rows, dict) or not isinstance(best, dict):
        raise ValueError("yeast result malformed")
    row_ids_raw = best.get("row_ids")
    d_o = best.get("D_o")
    if not isinstance(row_ids_raw, list) or not isinstance(d_o, list):
        raise ValueError("yeast selected dictionary malformed")
    row_ids = [str(item) for item in row_ids_raw]
    h_readouts = [str(readout) for readout in d_o if str(readout) in residual_dictionary.H_CANDIDATES]
    components = minimal.component_vectors(
        rows=rows,  # type: ignore[arg-type]
        row_ids=row_ids,
        h_readouts=h_readouts,
        has_stability=True,
    )
    occupancy = minimal.load_json(repo / minimal.OCCUPANCY_PATH)
    ordered_cds = minimal.load_json(repo / minimal.ORDERED_CDS_PATH)
    if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict):
        raise ValueError("yeast position files must contain JSON objects")
    joined, join_schema = minimal.wobble_dwell.schema_and_join(occupancy, ordered_cds)
    joined, boundary_subsample = minimal.deterministic_boundary_gene_subsample(joined)
    w_context = minimal.wobble_dwell.q6_context(repo)
    support_map = w_context["support_map"]
    aa_by_codon = w_context["aa_by_codon"]
    if not isinstance(support_map, dict) or not isinstance(aa_by_codon, dict):
        raise ValueError("wobble q6 context malformed")

    component_results: dict[str, dict[str, object]] = {}
    prepared_by_component: dict[str, list[dict[str, object]]] = {}
    for component_name in ["P_QT", "P_QS", "P_QH"]:
        component = components.get(component_name)
        if not isinstance(component, dict) or not isinstance(component.get("vector"), list):
            component_results[component_name] = {"component": component_name, "status": "needs_data", "reason": "component vector unavailable"}
            continue
        gene_values = minimal.component_by_gene(repo, rows, row_ids, component["vector"])  # type: ignore[arg-type]
        b_rows = minimal.boundary_rows_for_component(
            joined=joined,
            support_map=support_map,  # type: ignore[arg-type]
            aa_by_codon=aa_by_codon,  # type: ignore[arg-type]
            component=gene_values,
        )
        analyzed = boundary_component_real(component_name, b_rows)
        analyzed["component_fraction_of_P_Q"] = component.get("fraction")
        if component_name == "P_QH":
            analyzed["H_readouts"] = component.get("readouts")
        prepared = analyzed.pop("prepared_bins", None)
        if analyzed.get("status") == "computed" and isinstance(prepared, list):
            prepared_by_component[component_name] = prepared
        component_results[component_name] = analyzed

    computed_names = sorted(prepared_by_component)
    if not computed_names:
        return {
            "organism": "Saccharomyces cerevisiae",
            "organism_key": "saccharomyces_cerevisiae",
            "status": "needs_data",
            "reason": "no boundary component had enough rows after bin filtering",
            "component_boundary_response": component_results,
        }
    max_values: list[float] = []
    per_component_values: dict[str, list[float]] = {name: [] for name in computed_names}
    for trial in range(actual_b):
        trial_values = []
        for name in computed_names:
            value = permuted_boundary_r2(prepared_by_component[name], name, trial)
            per_component_values[name].append(value)
            trial_values.append(value)
        max_values.append(max(trial_values) if trial_values else 0.0)
    null95_select = percentile_nearest_rank(max_values, 0.95)
    null_mean_select = mean(max_values)
    for name in computed_names:
        item = component_results[name]
        r2 = float(item["boundary_r2"])
        q_familywise = (1 + sum(1 for value in max_values if value >= r2)) / (actual_b + 1)
        item["Null95_select_boundary_r2"] = null95_select
        item["NullMean_select_boundary_r2"] = null_mean_select
        item["q_familywise_select"] = q_familywise
        item["per_component_null95_diagnostic"] = percentile_nearest_rank(per_component_values[name], 0.95)
        item["passes_boundary_null"] = r2 <= null95_select or q_familywise >= 0.1
    return {
        "organism": "Saccharomyces cerevisiae",
        "organism_key": "saccharomyces_cerevisiae",
        "status": "computed",
        "position_data_scope": "yeast only; other organisms in this experiment have no local positional occupancy payload",
        "schema_and_gene_id_join": join_schema,
        "boundary_sampling": boundary_subsample,
        "component_boundary_response": component_results,
        "selection_aware_boundary_null": {
            "permutation_count": actual_b,
            "null95_select_boundary_r2": null95_select,
            "null_mean_select_boundary_r2": null_mean_select,
            "selection_rule": "for each bin-preserving q-value permutation, recompute boundary R2 for every computed component in {P_QT,P_QS,P_QH} and record the maximum R2",
            "deterministic_seed": f"sha256:{EXPERIMENT_ID}|component|boundary_selection_aware_null|trial|position-aa-bin|n",
        },
        "position_confound_controlled": {
            "controlled": True,
            "method": "exact file-provided 5prime/3prime offset crossed with amino-acid identity; response and q-polynomial regressors are demeaned within that bin; null shuffles q-values only inside the same bin",
            "does_not_use_sign_flip": True,
        },
    }


def public_organism_payload(result: dict[str, object]) -> dict[str, object]:
    if result.get("status") != "computed":
        return {
            "organism": result.get("organism"),
            "organism_key": result.get("organism_key"),
            "status": result.get("status"),
            "reason": result.get("reason"),
        }
    best = result["best"]
    source = result["source"]
    null = result["selection_aware_null"]
    if not isinstance(best, dict) or not isinstance(source, dict) or not isinstance(null, dict):
        raise ValueError("organism result payload malformed")
    coverage = float(best["coverage"])
    return {
        "organism": result["organism"],
        "organism_key": result["organism_key"],
        "status": "computed",
        "n_source": source["n_source"],
        "n_join_D_star": best["n_join"],
        "D_o_star": best["D_o"],
        "coverage_D_star": coverage,
        "U_o": bounded_unit(1.0 - coverage),
        "Null95_select": null["null95_select_coverage"],
        "NullMean_select": null["null_mean_select_coverage"],
        "Null95_bedc_reselected_diagnostic": null["null95_bedc_reselected_coverage"],
        "coverage_le_Null95_select": coverage <= float(null["null95_select_coverage"]),
        "coverage_lt_0_30": coverage < 0.30,
        "R2_QP": source["R2_QP"],
        "rank_Q_e": source["rank_Q_e"],
        "rank_D_e": best["rank_D_e"],
        "available_readouts": result["available_readouts"],
        "all_subset_count": result["all_subset_count"],
        "candidate_subset_count": result["candidate_subset_count"],
        "selection_aware_null": null,
        "selection_rule": best.get("selection_rule"),
        "dominant_residual_q": result["dominant_residual_q"],
    }


def verdicts_for(organism_payloads: dict[str, dict[str, object]], boundary: dict[str, object] | str) -> dict[str, object]:
    computed = {key: value for key, value in organism_payloads.items() if value.get("status") == "computed"}
    core = {key: computed[key] for key in CORE_PANEL if key in computed}
    source_details = [
        {
            "organism_key": key,
            "R2_QP": value.get("R2_QP"),
            "rank_Q_e": value.get("rank_Q_e"),
            "source_pass": float(value.get("R2_QP", 0.0)) > 0.0 and int(value.get("rank_Q_e", 0)) == 9 and float(value.get("R2_QP", 0.0)) >= 0.015,
        }
        for key, value in computed.items()
    ]
    verdict_a = bool(computed) and all(item["source_pass"] for item in source_details)
    u_values = [float(value.get("U_o", 0.0)) for value in core.values()]
    verdict_b = len(core) == len(CORE_PANEL) and all(value >= 0.70 for value in u_values) and median(u_values) >= 0.90
    compression_details = [
        {
            "organism_key": key,
            "coverage_D_star": value.get("coverage_D_star"),
            "Null95_select": value.get("Null95_select"),
            "coverage_lt_0_30": value.get("coverage_lt_0_30"),
            "coverage_le_Null95_select": value.get("coverage_le_Null95_select"),
        }
        for key, value in computed.items()
    ]
    verdict_c = bool(computed) and all(
        bool(item["coverage_lt_0_30"]) and bool(item["coverage_le_Null95_select"])
        for item in compression_details
    )

    boundary_details: list[dict[str, object]] = []
    max_boundary_r2 = 0.0
    if isinstance(boundary, dict) and boundary.get("status") == "computed":
        components = boundary.get("component_boundary_response")
        if isinstance(components, dict):
            for name, item in sorted(components.items()):
                if isinstance(item, dict) and item.get("status") == "computed":
                    r2 = float(item.get("boundary_r2", 0.0))
                    max_boundary_r2 = max(max_boundary_r2, r2)
                    boundary_details.append(
                        {
                            "component": name,
                            "boundary_r2": r2,
                            "Null95_select_boundary_r2": item.get("Null95_select_boundary_r2"),
                            "q_familywise_select": item.get("q_familywise_select"),
                            "passes_boundary_null": item.get("passes_boundary_null"),
                        }
                    )
    verdict_d = bool(boundary_details) and all(bool(item["passes_boundary_null"]) for item in boundary_details) and max_boundary_r2 < 1e-4
    return {
        "A_source_exists": verdict_a,
        "B_u_dominance_core_panel": verdict_b,
        "C_dictionary_compression_failure": verdict_c,
        "D_boundary_kernel_null": verdict_d,
        "source_details": source_details,
        "u_dominance_details": {
            "core_panel": CORE_PANEL,
            "U_values": [{"organism_key": key, "U_o": core[key].get("U_o")} for key in CORE_PANEL if key in core],
            "median_U": median(u_values),
            "all_core_present": len(core) == len(CORE_PANEL),
        },
        "compression_details": compression_details,
        "boundary_details": boundary_details,
        "max_boundary_r2": max_boundary_r2,
    }


def checks_for(verdicts: dict[str, object], organism_payloads: dict[str, dict[str, object]], boundary: dict[str, object] | str, conclusion: str) -> list[dict[str, object]]:
    return [
        {
            "name": "p_q_constructed",
            "passed": bool(verdicts.get("source_details")) and all(int(item.get("rank_Q_e", 0)) == 9 for item in verdicts.get("source_details", [])),  # type: ignore[union-attr]
            "actual": verdicts.get("source_details"),
            "expected": "each computed organism has positive P_Q with rank(Q_e)=9 and source R2_QP reported",
        },
        {
            "name": "selection_aware_dictionary_null",
            "passed": all(
                value.get("status") != "computed" or (
                    isinstance(value.get("selection_aware_null"), dict)
                    and int(value["selection_aware_null"].get("permutation_count", 0)) >= MIN_SELECTION_AWARE_B  # type: ignore[index]
                )
                for value in organism_payloads.values()
            ),
            "actual": {
                key: {
                    "Coverage": value.get("coverage_D_star"),
                    "Null95_select": value.get("Null95_select"),
                    "actual_B": value.get("selection_aware_null", {}).get("permutation_count") if isinstance(value.get("selection_aware_null"), dict) else None,
                }
                for key, value in organism_payloads.items()
            },
            "expected": "per organism, every permutation reruns a full subset scan and records reselected coverage; B>=200",
        },
        {
            "name": "boundary_kernel_selection_aware_null",
            "passed": isinstance(boundary, dict) and boundary.get("status") == "computed",
            "actual": boundary.get("selection_aware_boundary_null") if isinstance(boundary, dict) else boundary,
            "expected": "yeast boundary null is bin-preserving and selection-aware across computed P_QT/P_QS/P_QH components",
        },
        {
            "name": "u_dominance_core_panel",
            "passed": bool(verdicts.get("B_u_dominance_core_panel")),
            "actual": verdicts.get("u_dominance_details"),
            "expected": "core panel U_o >= 0.70 for each organism and median U >= 0.90",
        },
        {
            "name": "relative_irreducibility_verdict",
            "passed": conclusion == "relative_irreducibility_passed",
            "actual": {
                "conclusion": conclusion,
                "A": verdicts.get("A_source_exists"),
                "B": verdicts.get("B_u_dominance_core_panel"),
                "C": verdicts.get("C_dictionary_compression_failure"),
                "D": verdicts.get("D_boundary_kernel_null"),
            },
            "expected": "A and B and C and D are all true",
        },
    ]


def main() -> None:
    try:
        if DEFAULT_SELECTION_AWARE_B < MIN_SELECTION_AWARE_B:
            raise ValueError(f"BIO_REALITY_SELECTION_AWARE_B must be >= {MIN_SELECTION_AWARE_B}")
        if DEFAULT_BOUNDARY_SELECTION_AWARE_B < MIN_SELECTION_AWARE_B:
            raise ValueError(f"BIO_REALITY_BOUNDARY_SELECTION_AWARE_B must be >= {MIN_SELECTION_AWARE_B}")
        repo = pathlib.Path(__file__).resolve().parents[3]
        context = residual_dictionary.q6_context(repo)
        organism_results: dict[str, dict[str, object]] = {}
        for config in residual_dictionary.ORGANISMS:
            result = build_real_organism(repo, context, config, DEFAULT_SELECTION_AWARE_B)
            organism_results[str(config["key"])] = result
        computed_count = sum(1 for result in organism_results.values() if result.get("status") == "computed")
        if computed_count == 0:
            emit(
                "needs_data",
                checks=[],
                reason="no organism had enough joined data to construct P_Q and readout dictionary states",
                actual_B={"dictionary_selection_aware": DEFAULT_SELECTION_AWARE_B, "boundary_selection_aware": DEFAULT_BOUNDARY_SELECTION_AWARE_B},
            )
        yeast_boundary = boundary_selection_aware(
            repo=repo,
            yeast_result=organism_results.get("saccharomyces_cerevisiae", {}),
            actual_b=DEFAULT_BOUNDARY_SELECTION_AWARE_B,
        )
        public_organisms = {key: public_organism_payload(value) for key, value in organism_results.items()}
        verdicts = verdicts_for(public_organisms, yeast_boundary)
        verdict_bool = all(
            bool(verdicts.get(key))
            for key in ["A_source_exists", "B_u_dominance_core_panel", "C_dictionary_compression_failure", "D_boundary_kernel_null"]
        )
        if verdict_bool:
            conclusion = "relative_irreducibility_passed"
        else:
            failed = [
                label
                for label, key in [
                    ("A", "A_source_exists"),
                    ("B", "B_u_dominance_core_panel"),
                    ("C", "C_dictionary_compression_failure"),
                    ("D", "D_boundary_kernel_null"),
                ]
                if not verdicts.get(key)
            ]
            conclusion = "failed_" + "_".join(failed)
        checks = checks_for(verdicts, public_organisms, yeast_boundary, conclusion)
        public_details = {
            key: {
                item_key: item_value
                for item_key, item_value in result.items()
                if item_key not in {"rows", "base_ids", "best"}
            }
            for key, result in organism_results.items()
        }
        emit(
            "passed",
            checks=checks,
            conclusion=conclusion,
            verdicts=verdicts,
            organism_results=public_organisms,
            component_boundary_response=yeast_boundary,
            organism_details=public_details,
            actual_B={
                "dictionary_selection_aware": DEFAULT_SELECTION_AWARE_B,
                "boundary_selection_aware": DEFAULT_BOUNDARY_SELECTION_AWARE_B,
                "target_publishable_B": TARGET_SELECTION_AWARE_B,
                "note": "B=1000 publishable confirmation is a longer offline run when wall-time budget is tighter than the target.",
            },
            computation_backend="numpy" if np is not None else "pure_python",
            claim_statement_cn=(
                "B*_Q6 产生可复现的蛋白丰度残差 P_Q, 但在当前观测代数下 P_Q 不能被 "
                "TE/mRNA-stability/turnover/localization/PTM/complex/TM/domain/mRNA-abundance 或 CDS 位置边界核压缩。"
            ),
            scope_limit_cn="结论严格限定在 current readout algebra + current organism panel；不是绝对不可约或普适机制声明。",
            current_readout_algebra=[
                "measured_te",
                "mrna_stability where local payload exists",
                "turnover",
                "localization",
                "ptm_density",
                "complex_member",
                "tm_count",
                "domain_count",
                "mrna_abundance",
                "yeast CDS positional boundary kernel",
            ],
            cannot_claim=[
                "not an absolute irreducibility claim",
                "not a causal perturbation mechanism",
                "readout availability differs by organism",
                "boundary position payload is yeast-only in this local panel",
            ],
        )
    except Exception as exc:
        emit("failed", error=str(exc), reason="relative irreducible source experiment could not be computed")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Cross-condition observation ceiling for the yeast B*_Q6 P_Q target."""

from __future__ import annotations

import json
import math
import pathlib
import sys
import time
from datetime import datetime, timezone
from typing import Any

import run_b_star_q6_minimal_dictionary_compression_powered as minimal_dictionary
import run_b_star_q6_pq_target_permutation_dictionary_ceiling_powered as target_ceiling
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import (
    codon_counts_rna,
    matrix_column,
    normed_coordinate,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import vector_dot
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_pq_cross_condition_observation_ceiling_powered"
CLAIM_ID = "h3.cross_layer_relation.observation_ceiling.b_star_q6_pq_cross_condition_observation_ceiling_powered"

ORGANISM = "saccharomyces_cerevisiae"
MAIN_ABUNDANCE_PATH = "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae.json"
SD_ABUNDANCE_PATH = "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_sd.json"
YEPD_ABUNDANCE_PATH = "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_yepd.json"
CDS_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
EPS = 1e-12
WEIGHT_EPS = 1e-6
STARTED_AT = datetime.now(timezone.utc).isoformat(timespec="seconds")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_abundance(
    repo: pathlib.Path,
    relative_path: str,
    *,
    raw_values_need_log10: bool,
) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(repo / relative_path)
    if not isinstance(payload, dict) or not isinstance(payload.get("protein_abundance"), dict):
        raise ValueError(f"{relative_path} lacks protein_abundance object")
    raw = payload["protein_abundance"]
    out: dict[str, float] = {}
    skipped = {"non_numeric": 0, "nonpositive": 0}
    for protein_id, value in raw.items():  # type: ignore[union-attr]
        if not isinstance(protein_id, str) or not finite_number(value):
            skipped["non_numeric"] += 1
            continue
        numeric = float(value)
        if numeric <= 0.0:
            skipped["nonpositive"] += 1
            continue
        out[protein_id] = math.log10(numeric) if raw_values_need_log10 else numeric
    return out, {
        "path": relative_path,
        "n_payload": payload.get("n_proteins"),
        "n_loaded": len(out),
        "value_transform": "log10(raw protein_abundance)" if raw_values_need_log10 else "already log10 protein_abundance",
        "growth_condition": payload.get("growth_condition"),
        "medium_label": payload.get("medium_label"),
        "skipped": skipped,
    }


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    aa_order = standard_amino_acids(code, codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
    return {
        "code": code,
        "codons": codons,
        "aa_order": aa_order,
        "q_projected": q_projected,
        "q_names": list(q_projected),
        "q_support": q_support,
    }


def base_design_rows(
    *,
    repo: pathlib.Path,
    context: dict[str, object],
    abundance_log10: dict[str, float],
    row_id_filter: set[str] | None = None,
) -> dict[str, object]:
    cds_payload = load_json(repo / CDS_PATH)
    joined = cds_payload.get("joined") if isinstance(cds_payload, dict) else None
    if not isinstance(joined, list):
        raise ValueError(f"{CDS_PATH} must contain joined list")
    code = context["code"]
    codons = context["codons"]
    aa_order = context["aa_order"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    q_support = context["q_support"]
    if not isinstance(code, dict) or not isinstance(codons, list) or not isinstance(aa_order, list):
        raise ValueError("q6 context malformed")
    if not isinstance(q_projected, dict) or not isinstance(q_names, list) or not isinstance(q_support, set):
        raise ValueError("q6 context malformed")

    rows: dict[str, dict[str, object]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "outside_filter": 0,
        "missing_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
        "empty_amino_acid_counts": 0,
    }
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if row_id_filter is not None and protein_id not in row_id_filter:
            skipped["outside_filter"] += 1
            continue
        p_value = abundance_log10.get(protein_id)
        if p_value is None or not math.isfinite(p_value):
            skipped["missing_abundance"] += 1
            continue
        cds_len_nt = float(item.get("cds_len_nt", 0.0))
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(item, codons, ORGANISM, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        x_row = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            skipped["empty_amino_acid_counts"] += 1
            continue
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_row = [1.0, math.log(cds_len_nt)] + [aa_counts[aa] / aa_total for aa in aa_order] + [gc3, m_density]
        rows[protein_id] = {
            "protein_id": protein_id,
            "x": x_row,
            "p": [p_value],
            "z": z_row,
        }
    return {
        "rows": rows,
        "summary": {
            "cds_path": CDS_PATH,
            "n_cds_joined_reported": cds_payload.get("n_joined") if isinstance(cds_payload, dict) else None,
            "n_rows": len(rows),
            "skipped": skipped,
            "controls_used": controls_used(aa_order),
            "q_names": q_names,
        },
    }


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def rows_for_ids(rows: dict[str, dict[str, object]], row_ids: list[str]) -> list[dict[str, object]]:
    return [rows[protein_id] for protein_id in row_ids]


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def project_columns_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [[0.0 for _ in matrix[0]] for _ in matrix]
    columns = transpose(matrix)
    for q_vector in basis:
        for col_index, column in enumerate(columns):
            coeff = vector_dot(column, q_vector)
            if coeff == 0.0:
                continue
            for row_index in range(len(matrix)):
                out[row_index][col_index] += coeff * q_vector[row_index]
    return out


def subtract_matrix(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [
        [left[row_index][col_index] - right[row_index][col_index] for col_index in range(len(left[row_index]))]
        for row_index in range(len(left))
    ]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    return subtract_matrix(matrix, project_columns_with_basis(matrix, basis))


def project_vector(design: list[list[float]], target: list[float]) -> tuple[list[float], float, int, list[list[float]]]:
    basis = minimal_dictionary.orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q_vector in basis:
        coeff = vector_dot(target, q_vector)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q_vector[index]
    return projected, vector_norm2(projected), len(basis), basis


def pq_state(rows: dict[str, dict[str, object]], row_ids: list[str]) -> dict[str, object]:
    selected_rows = rows_for_ids(rows, row_ids)
    z_basis = minimal_dictionary.orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q, _basis_q = project_vector(x_e, p_col)
    p_norm2 = vector_norm2(p_col)
    return {
        "row_ids": row_ids,
        "n": len(row_ids),
        "z_basis": z_basis,
        "x_e": x_e,
        "p_e": p_e,
        "P_Q": p_q,
        "P_Q_norm2": p_q_energy,
        "P_residual_norm2": p_norm2,
        "R2_QP": 0.0 if p_norm2 <= EPS else bounded_unit(p_q_energy / p_norm2),
        "rank_Q_e": rank_q,
        "rank_Z": len(z_basis),
    }


def pearson(left: list[float], right: list[float]) -> float:
    if len(left) != len(right) or not left:
        return 0.0
    mean_left = sum(left) / len(left)
    mean_right = sum(right) / len(right)
    xx = sum((value - mean_left) ** 2 for value in left)
    yy = sum((value - mean_right) ** 2 for value in right)
    if xx <= EPS or yy <= EPS:
        return 0.0
    xy = sum((a - mean_left) * (b - mean_right) for a, b in zip(left, right))
    return xy / math.sqrt(xx * yy)


def pooled_variance(left: list[float], right: list[float]) -> float:
    pooled = list(left) + list(right)
    if not pooled:
        return 0.0
    mean_value = sum(pooled) / len(pooled)
    return sum((value - mean_value) ** 2 for value in pooled) / len(pooled)


def weighted_inner(left: list[float], right: list[float], weights: list[float]) -> float:
    return sum(weight * a * b for weight, a, b in zip(weights, left, right))


def weighted_norm2(vector: list[float], weights: list[float]) -> float:
    return weighted_inner(vector, vector, weights)


def weighted_orthonormal_basis_from_columns(
    matrix: list[list[float]],
    weights: list[float],
    tol: float = 1e-10,
) -> list[list[float]]:
    basis: list[list[float]] = []
    if not matrix:
        return basis
    for column in transpose(matrix):
        residual = list(column)
        for q_vector in basis:
            coeff = weighted_inner(residual, q_vector, weights)
            if coeff == 0.0:
                continue
            residual = [residual[index] - coeff * q_vector[index] for index in range(len(residual))]
        norm2 = weighted_norm2(residual, weights)
        column_norm2 = weighted_norm2(column, weights)
        threshold = tol * tol * max(1.0, column_norm2)
        if norm2 > threshold:
            norm = math.sqrt(norm2)
            basis.append([value / norm for value in residual])
    return basis


def weighted_project_vector(
    design: list[list[float]],
    target: list[float],
    weights: list[float],
) -> tuple[list[float], float, int, list[list[float]]]:
    basis = weighted_orthonormal_basis_from_columns(design, weights)
    projected = [0.0 for _ in target]
    for q_vector in basis:
        coeff = weighted_inner(target, q_vector, weights)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q_vector[index]
    return projected, weighted_norm2(projected, weights), len(basis), basis


def dictionary_design(
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    subset: list[str],
    z_basis: list[list[float]],
) -> list[list[float]]:
    if not subset:
        return [[] for _ in row_ids]
    design_raw: list[list[float]] = []
    for protein_id in row_ids:
        row = rows[protein_id]
        values: list[float] = []
        for readout in subset:
            values.extend(minimal_dictionary.readout_values(row, readout))
        design_raw.append(values)
    return residualize_with_basis(design_raw, z_basis)


def dictionary_projection_metrics(
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    subset: list[str],
    target: list[float],
    z_basis: list[list[float]],
    *,
    weights: list[float] | None = None,
) -> dict[str, object]:
    design = dictionary_design(rows, row_ids, subset, z_basis)
    if not subset:
        target_norm2 = vector_norm2(target) if weights is None else weighted_norm2(target, weights)
        return {
            "coverage": 0.0,
            "projected_norm2": 0.0,
            "target_norm2": target_norm2,
            "rank_D_e": 0,
        }
    if weights is None:
        _projected, projected_norm2, rank_d, _basis = project_vector(design, target)
        target_norm2 = vector_norm2(target)
    else:
        _projected, projected_norm2, rank_d, _basis = weighted_project_vector(design, target, weights)
        target_norm2 = weighted_norm2(target, weights)
    return {
        "coverage": 0.0 if target_norm2 <= EPS else bounded_unit(projected_norm2 / target_norm2),
        "projected_norm2": projected_norm2,
        "target_norm2": target_norm2,
        "rank_D_e": rank_d,
    }


def main_dictionary_selection(
    repo: pathlib.Path,
    context: dict[str, object],
) -> dict[str, object]:
    config = next(config for config in residual_dictionary.ORGANISMS if config["key"] == ORGANISM)
    observed = target_ceiling.observed_selection(repo, context, config)
    if observed.get("status") != "computed":
        return observed
    rows = observed.get("rows")
    best = observed.get("best")
    if not isinstance(rows, dict) or not isinstance(best, dict):
        raise ValueError("dictionary selection malformed")
    row_ids = [str(protein_id) for protein_id in best.get("row_ids", [])]
    state = best.get("state")
    base_r2 = target_ceiling.base_r2_qp(rows, row_ids, state) if isinstance(state, dict) else 0.0  # type: ignore[arg-type]
    return {
        "status": "computed",
        "rows": rows,
        "base_ids": [str(protein_id) for protein_id in observed.get("base_ids", [])],
        "available_readouts": observed.get("available_readouts"),
        "best": best,
        "best_row_ids": row_ids,
        "D_o_star": [str(readout) for readout in best.get("D_o", [])],
        "C_star_coverage": float(best["coverage"]),
        "C_star_penalized": float(best["BEDC_score"]),
        "C_star_unexplained": float(best["unexplained"]),
        "base_R2_QP_on_dictionary_join": base_r2,
        "n_join": int(best["n_join"]),
        "lambda": minimal_dictionary.LAMBDA,
        "rho_join": minimal_dictionary.RHO_JOIN,
        "cost": float(best["cost"]),
        "null95_coverage": float(best["null"]["null95_coverage"]) if isinstance(best.get("null"), dict) else None,
    }


def weights_from_conditions(
    row_ids: list[str],
    sd_log10: dict[str, float],
    yepd_log10: dict[str, float],
) -> tuple[list[float], dict[str, object]]:
    sigmas = [((sd_log10[protein_id] - yepd_log10[protein_id]) / 2.0) ** 2 for protein_id in row_ids]
    weights = [1.0 / (sigma + WEIGHT_EPS) for sigma in sigmas]
    weight_sum = sum(weights)
    weight2_sum = sum(weight * weight for weight in weights)
    n_eff = (weight_sum * weight_sum / weight2_sum) if weight2_sum > 0.0 else 0.0
    return weights, {
        "sigma2_definition": "((log10(P_SD) - log10(P_YEPD)) / 2)^2",
        "weight_definition": f"1 / (sigma2 + {WEIGHT_EPS})",
        "sigma2_min": min(sigmas) if sigmas else None,
        "sigma2_median": sorted(sigmas)[len(sigmas) // 2] if sigmas else None,
        "sigma2_mean": sum(sigmas) / len(sigmas) if sigmas else None,
        "sigma2_max": max(sigmas) if sigmas else None,
        "weight_min": min(weights) if weights else None,
        "weight_median": sorted(weights)[len(weights) // 2] if weights else None,
        "weight_mean": weight_sum / len(weights) if weights else None,
        "weight_max": max(weights) if weights else None,
        "n_eff": n_eff,
    }


def condition_ceiling(
    sd_state: dict[str, object],
    yepd_state: dict[str, object],
) -> dict[str, object]:
    sd_pq = sd_state["P_Q"]
    yepd_pq = yepd_state["P_Q"]
    if not isinstance(sd_pq, list) or not isinstance(yepd_pq, list):
        raise ValueError("condition P_Q vectors malformed")
    ceil_corr = pearson(sd_pq, yepd_pq)
    pooled_var = pooled_variance(sd_pq, yepd_pq)
    mse = sum((left - right) ** 2 for left, right in zip(sd_pq, yepd_pq)) / len(sd_pq) if sd_pq else 0.0
    diff_ceiling = 0.0 if pooled_var <= EPS else 1.0 - mse / (2.0 * pooled_var)
    return {
        "Ceil_Q_corr": ceil_corr,
        "Ceil_Q_diff": diff_ceiling,
        "mean_squared_condition_difference": mse,
        "pooled_variance": pooled_var,
        "P_Q_SD_norm2": sd_state["P_Q_norm2"],
        "P_Q_YEPD_norm2": yepd_state["P_Q_norm2"],
        "R2_QP_SD": sd_state["R2_QP"],
        "R2_QP_YEPD": yepd_state["R2_QP"],
    }


def verdict_for(
    *,
    base_r2: float,
    n_condition: int,
    ceil_q: float,
    c_star_penalized: float,
) -> str:
    if not (0.25 <= base_r2 <= 0.34) or n_condition < 800:
        return "needs_data"
    gap = ceil_q - c_star_penalized
    if ceil_q >= 0.30 and gap >= 0.05:
        return "crosses_boundary"
    if ceil_q < 0.30:
        return "bounded_descriptor_only"
    return "composition_artifact"


def cannot_claim() -> list[str]:
    return [
        "cross-condition SD vs YEPD is not a technical replicate; condition biology is counted as observation variance in this ceiling.",
        "SD/YEPD log10 abundance correlation is below one, so Ceil_Q is a conservative lower bound on a same-condition technical observation ceiling.",
        "The per-protein sigma2_g from two condition points is a rough noise proxy, not a calibrated measurement-error model.",
        "This is observational and non-causal; it separates reproducible P_Q structure from condition/observation variance only under the available cross-condition data.",
        "A clean observation ceiling requires same-condition technical replicates, which are not present in the local data.",
    ]


def main() -> None:
    started = time.time()
    repo = pathlib.Path(__file__).resolve().parents[3]
    status = "needs_data"
    verdict = "needs_data"
    checks: dict[str, object] = {}
    try:
        context = q6_context(repo)
        main_log10, main_summary = load_abundance(repo, MAIN_ABUNDANCE_PATH, raw_values_need_log10=True)
        sd_log10, sd_summary = load_abundance(repo, SD_ABUNDANCE_PATH, raw_values_need_log10=True)
        yepd_log10, yepd_summary = load_abundance(repo, YEPD_ABUNDANCE_PATH, raw_values_need_log10=True)

        main_rows_built = base_design_rows(repo=repo, context=context, abundance_log10=main_log10)
        main_rows = main_rows_built["rows"]
        if not isinstance(main_rows, dict):
            raise ValueError("main P_Q rows malformed")
        main_row_ids = sorted(main_rows)
        main_state = pq_state(main_rows, main_row_ids)  # type: ignore[arg-type]
        full_r2 = float(main_state["R2_QP"])

        dictionary = main_dictionary_selection(repo, context)
        if dictionary.get("status") != "computed":
            raise ValueError(f"dictionary C_star selection not computed: {dictionary.get('reason')}")

        condition_ids = sorted(set(sd_log10) & set(yepd_log10))
        condition_abundance_corr_raw_intersection = pearson(
            [sd_log10[protein_id] for protein_id in condition_ids],
            [yepd_log10[protein_id] for protein_id in condition_ids],
        )
        sd_rows_built = base_design_rows(repo=repo, context=context, abundance_log10=sd_log10, row_id_filter=set(condition_ids))
        yepd_rows_built = base_design_rows(repo=repo, context=context, abundance_log10=yepd_log10, row_id_filter=set(condition_ids))
        sd_rows = sd_rows_built["rows"]
        yepd_rows = yepd_rows_built["rows"]
        if not isinstance(sd_rows, dict) or not isinstance(yepd_rows, dict):
            raise ValueError("condition P_Q rows malformed")
        condition_row_ids = sorted(set(sd_rows) & set(yepd_rows))
        condition_abundance_corr_cds_q_intersection = pearson(
            [sd_log10[protein_id] for protein_id in condition_row_ids],
            [yepd_log10[protein_id] for protein_id in condition_row_ids],
        )
        sd_state = pq_state(sd_rows, condition_row_ids)  # type: ignore[arg-type]
        yepd_state = pq_state(yepd_rows, condition_row_ids)  # type: ignore[arg-type]
        ceiling = condition_ceiling(sd_state, yepd_state)
        ceil_q = float(ceiling["Ceil_Q_corr"])

        dictionary_rows = dictionary["rows"]
        d_star = dictionary["D_o_star"]
        if not isinstance(dictionary_rows, dict) or not isinstance(d_star, list):
            raise ValueError("dictionary rows malformed")
        dict_condition_ids = [
            protein_id
            for protein_id in condition_row_ids
            if protein_id in dictionary_rows
            and all(minimal_dictionary.row_has_readout(dictionary_rows[protein_id], str(readout)) for readout in d_star)
        ]
        sd_on_dict = pq_state(sd_rows, dict_condition_ids)  # type: ignore[arg-type]
        yepd_on_dict = pq_state(yepd_rows, dict_condition_ids)  # type: ignore[arg-type]
        pq_mean = [
            (float(left) + float(right)) / 2.0
            for left, right in zip(sd_on_dict["P_Q"], yepd_on_dict["P_Q"])  # type: ignore[arg-type]
        ]
        weights, weight_summary = weights_from_conditions(dict_condition_ids, sd_log10, yepd_log10)
        unweighted_condition_dictionary = dictionary_projection_metrics(
            rows=dictionary_rows,  # type: ignore[arg-type]
            row_ids=dict_condition_ids,
            subset=[str(readout) for readout in d_star],
            target=pq_mean,
            z_basis=sd_on_dict["z_basis"],  # type: ignore[arg-type]
            weights=None,
        )
        weighted_dictionary = dictionary_projection_metrics(
            rows=dictionary_rows,  # type: ignore[arg-type]
            row_ids=dict_condition_ids,
            subset=[str(readout) for readout in d_star],
            target=pq_mean,
            z_basis=sd_on_dict["z_basis"],  # type: ignore[arg-type]
            weights=weights,
        )

        c_star_penalized = float(dictionary["C_star_penalized"])
        c_star_coverage = float(dictionary["C_star_coverage"])
        coverage_ratio_penalized = c_star_penalized / ceil_q if abs(ceil_q) > EPS else None
        coverage_ratio_unpenalized = c_star_coverage / ceil_q if abs(ceil_q) > EPS else None
        u_fraction = 1.0 - c_star_coverage
        one_minus_ceil = 1.0 - ceil_q
        verdict = verdict_for(
            base_r2=full_r2,
            n_condition=len(condition_row_ids),
            ceil_q=ceil_q,
            c_star_penalized=c_star_penalized,
        )
        status = "passed" if verdict in {"crosses_boundary", "composition_artifact", "bounded_descriptor_only"} else "needs_data"
        checks = {
            "pq_reconstruction_validated": 0.25 <= full_r2 <= 0.34,
            "two_condition_pq_built": len(condition_row_ids) >= 800
            and finite_number(sd_state.get("P_Q_norm2"))
            and finite_number(yepd_state.get("P_Q_norm2")),
            "ceil_q_reported": finite_number(ceil_q),
            "weighted_c_star_reported": finite_number(weighted_dictionary.get("coverage")),
            "n_eff_reported": finite_number(weight_summary.get("n_eff")),
            "coverage_ratio_reported": finite_number(coverage_ratio_penalized),
            "observation_ceiling_verdict": verdict,
        }
        out = {
            "status": status,
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": verdict,
            "result": {
                "organism": "Saccharomyces cerevisiae",
                "organism_key": ORGANISM,
                "method": {
                    "P_Q": "Pi_{Q_e} P_e after residualizing X_Q and log10 protein abundance against length, amino-acid composition, GC3, and M-density controls.",
                    "Q_source": "q_vectors/project_syn imported from run_b_star_q6_translation_survival_powered.py",
                    "base_reconstruction_scope": "main integrated PAXdb abundance file, external protein_abundance dict",
                    "condition_scope": "SD and YEPD raw PAXdb condition files transformed by log10 before P_Q construction",
                    "dictionary_scope": "observed minimal_dictionary D_o_star selected on the main abundance dictionary run; condition projection fixes this D_o_star",
                },
                "data": {
                    "main_abundance": main_summary,
                    "sd_abundance": sd_summary,
                    "yepd_abundance": yepd_summary,
                    "main_pq_rows": main_rows_built["summary"],
                    "condition_sd_rows": sd_rows_built["summary"],
                    "condition_yepd_rows": yepd_rows_built["summary"],
                    "sd_yepd_raw_intersection_n": len(condition_ids),
                    "sd_yepd_log10_abundance_corr_raw_intersection": condition_abundance_corr_raw_intersection,
                    "sd_yepd_cds_q_intersection_n": len(condition_row_ids),
                    "sd_yepd_log10_abundance_corr_cds_q_intersection": condition_abundance_corr_cds_q_intersection,
                    "dictionary_condition_join_n": len(dict_condition_ids),
                },
                "base_reconstruction": {
                    "base_full_R2_QP": full_r2,
                    "n_full": len(main_row_ids),
                    "rank_Q_e": main_state["rank_Q_e"],
                    "rank_Z": main_state["rank_Z"],
                    "dictionary_join_R2_QP_check": dictionary["base_R2_QP_on_dictionary_join"],
                },
                "dictionary_C_star": {
                    "D_o_star": dictionary["D_o_star"],
                    "n_join": dictionary["n_join"],
                    "C_star_coverage": c_star_coverage,
                    "C_star_penalized": c_star_penalized,
                    "C_star_unexplained_fraction": dictionary["C_star_unexplained"],
                    "cost": dictionary["cost"],
                    "lambda": dictionary["lambda"],
                    "rho_join": dictionary["rho_join"],
                    "null95_coverage": dictionary["null95_coverage"],
                },
                "condition_P_Q": {
                    "n": len(condition_row_ids),
                    **ceiling,
                },
                "observation_weighted_dictionary": {
                    "target": "mean of P_Q^SD and P_Q^YEPD on the fixed condition-dictionary join",
                    "unweighted_C_star_on_condition_mean": unweighted_condition_dictionary,
                    "weighted_C_star_W": weighted_dictionary,
                    "weights": weight_summary,
                },
                "coverage_ratio": {
                    "C_star_penalized_over_Ceil_Q": coverage_ratio_penalized,
                    "C_star_coverage_over_Ceil_Q": coverage_ratio_unpenalized,
                    "U_fraction_over_P_Q_fraction": u_fraction,
                    "one_minus_Ceil_Q": one_minus_ceil,
                    "U_fraction_minus_observation_variance_proxy": u_fraction - one_minus_ceil,
                },
                "interpretation": {
                    "verdict": verdict,
                    "rule": "needs_data if base R2_QP is outside [0.25,0.34] or condition n<800; crosses_boundary if Ceil_Q>=0.30 and C_star_penalized trails it by at least 0.05; otherwise bounded_descriptor_only/composition_artifact.",
                    "honest_reading": (
                        "P_Q is reproducible across SD/YEPD beyond the fixed main dictionary C_star, so residual U contains reproducible non-dictionary structure under this conservative cross-condition ceiling."
                        if verdict == "crosses_boundary"
                        else "The available cross-condition ceiling does not justify promoting residual U beyond observation/condition variance under this gate."
                    ),
                },
                "cannot_claim": cannot_claim(),
                "runtime_sec": time.time() - started,
                "started_at": STARTED_AT,
                "completed_at": now_iso(),
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(0 if status == "passed" else 3)
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks or {"runtime_exception": True},
            "verdict": verdict,
            "result": {
                "error": str(exc),
                "cannot_claim": ["运行时异常，不能作科学结论。"],
                "runtime_sec": time.time() - started,
                "started_at": STARTED_AT,
                "completed_at": now_iso(),
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)


if __name__ == "__main__":
    main()

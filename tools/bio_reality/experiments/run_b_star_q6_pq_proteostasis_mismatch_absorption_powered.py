#!/usr/bin/env python3
"""Burden-only proteostasis mismatch absorption of the yeast B*_Q6 residual U."""

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
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot


EXPERIMENT_ID = "b_star_q6_pq_proteostasis_mismatch_absorption_powered"
CLAIM_ID = "h3.cross_layer_relation.proteostasis_mismatch.b_star_q6_pq_proteostasis_mismatch_absorption_powered"

ORGANISM_KEY = "saccharomyces_cerevisiae"
TE_PATH = "tools/bio_reality/data/riboseq_translation_efficiency_saccharomyces_cerevisiae.json"
STRUCTURAL_ORDER_PATH = "tools/bio_reality/data/structural_order_saccharomyces_cerevisiae.json"
UNIPROT_FEATURES_PATH = "tools/bio_reality/data/uniprot_protein_features_saccharomyces_cerevisiae.json"

FEATURE_NAMES = ["log_te", "disorder", "domain_count", "tm_count", "complex_member", "ptm_density"]
BURDEN_FEATURE_NAMES = ["disorder", "domain_count", "tm_count", "complex_member", "ptm_density"]
B = 200
FOLDS = 5
SEED = 91387
EPS = 1e-12
BASE_R2_QP_MIN = 0.25
BASE_R2_QP_MAX = 0.34
CROSS_HELDOUT_DELTA_R2 = 0.01
CROSS_PARTIAL_RHO = 0.10
ABUNDANCE_BINS = 10
LENGTH_BINS = 10


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def strip_4932(identifier: str) -> str:
    return identifier.split(".", 1)[1] if identifier.startswith("4932.") else identifier


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = hashlib.sha256(f"{material}|seed={SEED}|index={index}|n={n}".encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def matrix_vector(design: list[list[float]], coeff: list[float]) -> list[float]:
    return [sum(row[index] * coeff[index] for index in range(len(coeff))) for row in design]


def sse(values: list[float], pred: list[float]) -> float:
    return sum((value - fit) * (value - fit) for value, fit in zip(values, pred))


def r2_from_predictions(values: list[float], pred: list[float]) -> float:
    base = mean(values)
    total = sum((value - base) * (value - base) for value in values)
    if total <= EPS:
        return 0.0
    return 1.0 - sse(values, pred) / total


def pearson(left: list[float], right: list[float]) -> float:
    left_mean = mean(left)
    right_mean = mean(right)
    left_ss = sum((value - left_mean) * (value - left_mean) for value in left)
    right_ss = sum((value - right_mean) * (value - right_mean) for value in right)
    if left_ss <= EPS or right_ss <= EPS:
        return 0.0
    cov = sum((l_value - left_mean) * (r_value - right_mean) for l_value, r_value in zip(left, right))
    return cov / math.sqrt(left_ss * right_ss)


def ranks(values: list[float]) -> list[float]:
    pairs = sorted((value, index) for index, value in enumerate(values))
    out = [0.0 for _ in values]
    index = 0
    while index < len(pairs):
        end = index + 1
        while end < len(pairs) and pairs[end][0] == pairs[index][0]:
            end += 1
        rank = (index + end - 1) / 2.0 + 1.0
        for item in range(index, end):
            out[pairs[item][1]] = rank
        index = end
    return out


def standardize_rows(rows: list[list[float]]) -> tuple[list[list[float]], list[float], list[float]]:
    if not rows:
        return [], [], []
    width = len(rows[0])
    centers: list[float] = []
    scales: list[float] = []
    for col in range(width):
        values = [row[col] for row in rows]
        center = mean(values)
        variance = sum((value - center) * (value - center) for value in values) / len(values)
        scale = math.sqrt(variance) if variance > EPS else 1.0
        centers.append(center)
        scales.append(scale)
    out = [[(row[col] - centers[col]) / scales[col] for col in range(width)] for row in rows]
    return out, centers, scales


def project_absorption(design: list[list[float]], target: list[float]) -> tuple[float, float, int]:
    target_norm2 = vector_norm2(target)
    if target_norm2 <= EPS or not design:
        return 0.0, 0.0, 0
    basis = orthonormal_basis_from_columns(design)
    energy = sum(vector_dot(target, q_vector) ** 2 for q_vector in basis)
    if energy > target_norm2 and energy <= target_norm2 + 1e-8:
        energy = target_norm2
    return bounded_unit(max(0.0, energy) / target_norm2), energy, len(basis)


def fit_ridge_standardized(x_rows: list[list[float]], y_values: list[float]) -> dict[str, object]:
    if not x_rows:
        raise ValueError("empty design")
    width = len(x_rows[0])
    centers: list[float] = []
    scales: list[float] = []
    for col in range(width):
        values = [row[col] for row in x_rows]
        center = mean(values)
        variance = sum((value - center) * (value - center) for value in values) / len(values)
        scale = math.sqrt(variance) if variance > EPS else 1.0
        centers.append(center)
        scales.append(scale)
    design = [[1.0] + [(row[col] - centers[col]) / scales[col] for col in range(width)] for row in x_rows]
    coeff = solve_regularized_normal_equation(design, y_values, ridge=1e-8)
    return {"centers": centers, "scales": scales, "coeff": coeff}


def predict_ridge(model: dict[str, object], x_rows: list[list[float]]) -> list[float]:
    centers = model["centers"]
    scales = model["scales"]
    coeff = model["coeff"]
    if not isinstance(centers, list) or not isinstance(scales, list) or not isinstance(coeff, list):
        raise ValueError("ridge model malformed")
    design = [
        [1.0] + [(row[col] - float(centers[col])) / float(scales[col]) for col in range(len(centers))]
        for row in x_rows
    ]
    return matrix_vector(design, [float(value) for value in coeff])


def select_rows(rows: list[list[float]], indices: list[int]) -> list[list[float]]:
    return [rows[index] for index in indices]


def heldout_delta_r2(x_rows: list[list[float]], y_values: list[float]) -> dict[str, float]:
    n = len(y_values)
    order = deterministic_permutation(n, f"{EXPERIMENT_ID}|heldout-folds")
    model_pred = [0.0 for _ in y_values]
    baseline_pred = [0.0 for _ in y_values]
    for fold in range(FOLDS):
        test = [index for position, index in enumerate(order) if position % FOLDS == fold]
        train = [index for position, index in enumerate(order) if position % FOLDS != fold]
        model = fit_ridge_standardized(select_rows(x_rows, train), [y_values[index] for index in train])
        pred = predict_ridge(model, select_rows(x_rows, test))
        train_mean = mean([y_values[index] for index in train])
        for index, value in zip(test, pred):
            model_pred[index] = value
            baseline_pred[index] = train_mean
    total = sum((value - mean(y_values)) * (value - mean(y_values)) for value in y_values)
    delta = 0.0 if total <= EPS else (sse(y_values, baseline_pred) - sse(y_values, model_pred)) / total
    return {
        "heldout_delta_r2": delta,
        "heldout_model_r2": r2_from_predictions(y_values, model_pred),
        "heldout_baseline_r2": r2_from_predictions(y_values, baseline_pred),
    }


def residuals_after_controls(response: list[float], controls: list[list[float]]) -> list[float]:
    design = [[1.0] + row for row in controls]
    coeff = solve_regularized_normal_equation(design, response, ridge=1e-8)
    pred = matrix_vector(design, coeff)
    return [value - fit for value, fit in zip(response, pred)]


def partial_spearman(feature: list[float], target: list[float], controls: list[list[float]]) -> float:
    ranked_feature = ranks(feature)
    ranked_target = ranks(target)
    ranked_controls = []
    if controls:
        control_columns = [[row[col] for row in controls] for col in range(len(controls[0]))]
        ranked_control_columns = [ranks(column) for column in control_columns]
        ranked_controls = [
            [ranked_control_columns[col][row_index] for col in range(len(ranked_control_columns))]
            for row_index in range(len(controls))
        ]
    feature_residual = residuals_after_controls(ranked_feature, ranked_controls)
    target_residual = residuals_after_controls(ranked_target, ranked_controls)
    return pearson(feature_residual, target_residual)


def bin_assignments(values_by_id: dict[str, float], bin_count: int) -> dict[str, int]:
    ordered = sorted(values_by_id.items(), key=lambda item: (item[1], item[0]))
    n = len(ordered)
    return {gene_id: min(bin_count - 1, (rank * bin_count) // n) for rank, (gene_id, _value) in enumerate(ordered)}


def groups_for_rows(rows: list[dict[str, object]]) -> tuple[list[list[int]], dict[str, object]]:
    abundance = {str(row["gene_id"]): float(row["abundance_log10"]) for row in rows}
    length = {str(row["gene_id"]): float(row["protein_length"]) for row in rows}
    abundance_bin = bin_assignments(abundance, ABUNDANCE_BINS)
    length_bin = bin_assignments(length, LENGTH_BINS)
    grouped: dict[tuple[int, int], list[int]] = defaultdict(list)
    for index, row in enumerate(rows):
        gene_id = str(row["gene_id"])
        grouped[(abundance_bin[gene_id], length_bin[gene_id])].append(index)
    groups = [grouped[key] for key in sorted(grouped)]
    sizes = sorted(len(group) for group in groups)
    movable = sum(size for size in sizes if size >= 2)
    summary = {
        "matched_axes": ["protein_abundance_decile", "protein_length_decile"],
        "abundance_bins": ABUNDANCE_BINS,
        "length_bins": LENGTH_BINS,
        "strata_n": len(groups),
        "singleton_strata_n": sum(1 for size in sizes if size == 1),
        "movable_rows_n": movable,
        "movable_rows_fraction": movable / len(rows) if rows else 0.0,
        "min_stratum_size": sizes[0] if sizes else 0,
        "median_stratum_size": sizes[len(sizes) // 2] if sizes else 0,
        "max_stratum_size": sizes[-1] if sizes else 0,
    }
    return groups, summary


def permute_feature_rows(feature_rows: list[list[float]], groups: list[list[int]], trial: int) -> list[list[float]]:
    out = [list(row) for row in feature_rows]
    for group_index, positions in enumerate(groups):
        if len(positions) < 2:
            continue
        order = deterministic_permutation(len(positions), f"{EXPERIMENT_ID}|matched-null|trial={trial}|group={group_index}")
        for dest_local, src_local in enumerate(order):
            out[positions[dest_local]] = list(feature_rows[positions[src_local]])
    return out


def load_translation_efficiency(repo: pathlib.Path) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(repo / TE_PATH)
    genes = payload.get("genes") if isinstance(payload, dict) else None
    if not isinstance(genes, list):
        raise ValueError(f"{TE_PATH} must contain genes list")
    out: dict[str, float] = {}
    skipped = Counter()
    for item in genes:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        te = item.get("translation_efficiency")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        if not finite_number(te) or float(te) <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        out[strip_4932(gene_id)] = math.log(float(te))
    return out, {"path": TE_PATH, "n_loaded": len(out), "skipped": dict(sorted(skipped.items())), "transform": "natural log(translation_efficiency)"}


def load_structural_order(repo: pathlib.Path) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(repo / STRUCTURAL_ORDER_PATH)
    proteins = payload.get("proteins") if isinstance(payload, dict) else None
    if not isinstance(proteins, list):
        raise ValueError(f"{STRUCTURAL_ORDER_PATH} must contain proteins list")
    out: dict[str, float] = {}
    skipped = Counter()
    for item in proteins:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        order = item.get("structural_order")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if not finite_number(order):
            skipped["non_numeric_order"] += 1
            continue
        out[strip_4932(protein_id)] = float(order)
    return out, {"path": STRUCTURAL_ORDER_PATH, "n_loaded": len(out), "skipped": dict(sorted(skipped.items()))}


def load_uniprot_features(repo: pathlib.Path) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    payload = load_json(repo / UNIPROT_FEATURES_PATH)
    proteins = payload.get("proteins") if isinstance(payload, dict) else None
    if not isinstance(proteins, dict):
        raise ValueError(f"{UNIPROT_FEATURES_PATH} must contain proteins object")
    out: dict[str, dict[str, float]] = {}
    skipped = Counter()
    for protein_id, item in proteins.items():
        if not isinstance(protein_id, str) or not isinstance(item, dict):
            skipped["malformed_record"] += 1
            continue
        features = item.get("features")
        length = item.get("length")
        if not isinstance(features, dict) or not finite_number(length) or float(length) <= 0.0:
            skipped["missing_features_or_length"] += 1
            continue
        row: dict[str, float] = {"length": float(length)}
        valid = True
        for name in ["domain_count", "tm_count", "complex_member", "ptm_density"]:
            value = features.get(name)
            if not finite_number(value):
                valid = False
                break
            row[name] = float(value)
        if not valid:
            skipped["non_numeric_feature"] += 1
            continue
        out[strip_4932(protein_id)] = row
    return out, {"path": UNIPROT_FEATURES_PATH, "n_loaded": len(out), "skipped": dict(sorted(skipped.items()))}


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
    return bounded_unit(float(p_q_norm2) / p_norm2)


def reconstruct_yeast_u(repo: pathlib.Path) -> dict[str, object]:
    context = residual_dictionary.q6_context(repo)
    config = next(item for item in residual_dictionary.ORGANISMS if item["key"] == ORGANISM_KEY)
    compression = minimal_dictionary.build_organism_compression(repo, context, config)
    if compression.get("status") != "computed":
        return {"status": "needs_data", "reason": compression.get("reason"), "compression": compression}
    rows = compression.get("rows")
    best = compression.get("best")
    if not isinstance(rows, dict) or not isinstance(best, dict):
        raise ValueError("yeast compression result malformed")
    state = best.get("state")
    row_ids = best.get("row_ids")
    if not isinstance(state, dict) or not isinstance(row_ids, list):
        raise ValueError("yeast best dictionary state malformed")
    p_q = state.get("P_Q")
    residual = state.get("residual")
    if not isinstance(p_q, list) or not isinstance(residual, list):
        raise ValueError("yeast P_Q or U vector missing")
    return {
        "status": "computed",
        "rows": rows,
        "row_ids": [str(protein_id) for protein_id in row_ids],
        "p_q": [float(value) for value in p_q],
        "u": [float(value) for value in residual],
        "best": best,
        "base_ids_n": len(compression.get("base_ids", [])) if isinstance(compression.get("base_ids"), list) else None,
        "base_r2_qp": base_r2_qp(rows, [str(protein_id) for protein_id in row_ids], state),
        "u_energy_ratio_full_active": float(state["unexplained"]),
        "p_q_norm2_full_active": float(state["P_Q_norm2"]),
        "u_norm2_full_active": vector_norm2([float(value) for value in residual]),
    }


def build_proteostasis_rows(
    *,
    repo: pathlib.Path,
    compression_rows: dict[str, dict[str, object]],
    row_ids: list[str],
    p_q: list[float],
    u: list[float],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    te, te_summary = load_translation_efficiency(repo)
    structural_order, structural_order_summary = load_structural_order(repo)
    uniprot, uniprot_summary = load_uniprot_features(repo)
    normalized_intersection = set(te) & set(structural_order) & set(uniprot)
    rows: list[dict[str, object]] = []
    missing = Counter()
    for index, protein_id in enumerate(row_ids):
        gene_id = strip_4932(protein_id)
        if gene_id not in te:
            missing["translation_efficiency"] += 1
            continue
        if gene_id not in structural_order:
            missing["structural_order"] += 1
            continue
        if gene_id not in uniprot:
            missing["uniprot_features"] += 1
            continue
        compression_row = compression_rows.get(protein_id)
        if not isinstance(compression_row, dict):
            missing["compression_row"] += 1
            continue
        abundance_values = compression_row.get("p")
        if not isinstance(abundance_values, list) or not abundance_values or not finite_number(abundance_values[0]):
            missing["protein_abundance"] += 1
            continue
        uf = uniprot[gene_id]
        structural_order_value = structural_order[gene_id]
        rows.append(
            {
                "gene_id": gene_id,
                "protein_id": protein_id,
                "u": u[index],
                "p_q": p_q[index],
                "abundance_log10": float(abundance_values[0]),
                "protein_length": uf["length"],
                "raw_features": {
                    "log_te": te[gene_id],
                    "disorder": 100.0 - structural_order_value,
                    "domain_count": uf["domain_count"],
                    "tm_count": uf["tm_count"],
                    "complex_member": uf["complex_member"],
                    "ptm_density": uf["ptm_density"],
                },
            }
        )
    summary = {
        "translation_efficiency": te_summary,
        "structural_order": structural_order_summary,
        "uniprot_features": uniprot_summary,
        "id_normalization": "strip leading 4932. from structural_order and UniProt feature ids before joining to plain systematic gene ids",
        "te_structural_order_uniprot_intersection_n": len(normalized_intersection),
        "active_dictionary_join_n": len(row_ids),
        "proteostasis_join_n": len(rows),
        "dropped_active_rows": dict(sorted(missing.items())),
    }
    return rows, summary


def attach_standardized_features(rows: list[dict[str, object]]) -> dict[str, object]:
    raw_matrix = [
        [float(row["raw_features"][name]) for name in FEATURE_NAMES]  # type: ignore[index]
        for row in rows
    ]
    standardized, centers, scales = standardize_rows(raw_matrix)
    for row, feature_row in zip(rows, standardized):
        row["feature_row"] = feature_row
        row["burden_score"] = sum(feature_row[FEATURE_NAMES.index(name)] for name in BURDEN_FEATURE_NAMES)
    return {
        "feature_order": FEATURE_NAMES,
        "burden_component_order": BURDEN_FEATURE_NAMES,
        "feature_centers": dict(zip(FEATURE_NAMES, centers)),
        "feature_scales": dict(zip(FEATURE_NAMES, scales)),
        "burden_definition": "sum of z-scored disorder, domain_count, tm_count, complex_member, and ptm_density; proteostasis mismatch subspace also includes z-scored log_te",
    }


def matched_permutation_null(feature_rows: list[list[float]], target: list[float], groups: list[list[int]]) -> dict[str, object]:
    values = []
    for trial in range(B):
        permuted = permute_feature_rows(feature_rows, groups, trial)
        absorbed, _energy, _rank = project_absorption(permuted, target)
        values.append(absorbed)
    return {
        "B": B,
        "values": values,
        "null95": percentile_nearest_rank(values, 0.95),
        "null_mean": mean(values),
        "null_max": max(values) if values else 0.0,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|seed={SEED}|matched-null",
    }


def analyze(repo: pathlib.Path) -> dict[str, object]:
    reconstructed = reconstruct_yeast_u(repo)
    if reconstructed.get("status") != "computed":
        return {
            "status": "needs_data",
            "verdict": "needs_data",
            "checks": {
                "pq_u_reconstructed": False,
                "base_r2_qp_validated": False,
                "id_normalization_applied": False,
                "burden_components_built": False,
                "a_prot_reported": False,
                "matched_perm_null": False,
                "heldout_validated": False,
                "proteostasis_verdict": "needs_data",
            },
            "result": {"reason": reconstructed.get("reason"), "cannot_claim": cannot_claim()},
        }

    rows, data_summary = build_proteostasis_rows(
        repo=repo,
        compression_rows=reconstructed["rows"],  # type: ignore[arg-type]
        row_ids=reconstructed["row_ids"],  # type: ignore[arg-type]
        p_q=reconstructed["p_q"],  # type: ignore[arg-type]
        u=reconstructed["u"],  # type: ignore[arg-type]
    )
    feature_summary = attach_standardized_features(rows) if rows else {}
    base_r2 = float(reconstructed["base_r2_qp"])
    base_r2_valid = BASE_R2_QP_MIN <= base_r2 <= BASE_R2_QP_MAX
    enough_rows = len(rows) >= MIN_PROTEINS_PER_ORGANISM

    if not base_r2_valid or not enough_rows:
        verdict = "needs_data"
        checks = {
            "pq_u_reconstructed": True,
            "base_r2_qp_validated": base_r2_valid,
            "id_normalization_applied": data_summary.get("te_structural_order_uniprot_intersection_n") == 5092,
            "burden_components_built": bool(rows),
            "a_prot_reported": False,
            "matched_perm_null": False,
            "heldout_validated": False,
            "proteostasis_verdict": verdict,
        }
        return {
            "status": "needs_data",
            "verdict": verdict,
            "checks": checks,
            "result": {
                "base_r2_qp": base_r2,
                "n_genes_used": len(rows),
                "data_summary": data_summary,
                "feature_summary": feature_summary,
                "cannot_claim": cannot_claim(),
            },
        }

    feature_rows = [list(row["feature_row"]) for row in rows]  # type: ignore[arg-type]
    target_u = [float(row["u"]) for row in rows]
    p_q_subset = [float(row["p_q"]) for row in rows]
    u_norm2 = vector_norm2(target_u)
    p_q_norm2 = vector_norm2(p_q_subset)
    a_prot, projected_energy, rank_delta = project_absorption(feature_rows, target_u)
    cv = heldout_delta_r2(feature_rows, target_u)
    groups, strata_summary = groups_for_rows(rows)
    null = matched_permutation_null(feature_rows, target_u, groups)
    null95 = float(null["null95"])
    p_prot = (1 + sum(1 for value in null["values"] if float(value) >= a_prot)) / (1 + B)  # type: ignore[index]

    controls = [[float(row["abundance_log10"]), float(row["protein_length"])] for row in rows]
    partials = {}
    for index, name in enumerate(FEATURE_NAMES):
        feature = [row[index] for row in feature_rows]
        partials[name] = partial_spearman(feature, target_u, controls)
    dominant_component = max(partials, key=lambda name: abs(partials[name]))
    dominant_partial_rho = partials[dominant_component]

    exceeds_null = a_prot > null95
    heldout_gate = float(cv["heldout_delta_r2"]) >= CROSS_HELDOUT_DELTA_R2
    partial_gate = abs(dominant_partial_rho) >= CROSS_PARTIAL_RHO
    if exceeds_null and (heldout_gate or partial_gate):
        verdict = "crosses_boundary"
    elif exceeds_null:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "composition_artifact"

    checks = {
        "pq_u_reconstructed": True,
        "base_r2_qp_validated": base_r2_valid,
        "id_normalization_applied": data_summary.get("te_structural_order_uniprot_intersection_n") == 5092,
        "burden_components_built": all(
            isinstance(row.get("raw_features"), dict)
            and all(finite_number(row["raw_features"].get(name)) for name in BURDEN_FEATURE_NAMES)  # type: ignore[union-attr]
            for row in rows
        )
        and len(rows) >= MIN_PROTEINS_PER_ORGANISM,
        "a_prot_reported": math.isfinite(a_prot),
        "matched_perm_null": len(null["values"]) == B,
        "heldout_validated": math.isfinite(float(cv["heldout_delta_r2"])),
        "proteostasis_verdict": verdict,
    }
    status = "passed" if all(value is True or key == "proteostasis_verdict" for key, value in checks.items()) else "failed"

    best = reconstructed["best"]
    best_dictionary = best.get("D_o") if isinstance(best, dict) else None
    result = {
        "organism": "Saccharomyces cerevisiae",
        "base_r2_qp": base_r2,
        "base_r2_qp_gate": [BASE_R2_QP_MIN, BASE_R2_QP_MAX],
        "best_dictionary_D": best_dictionary,
        "base_n_before_dictionary_join": reconstructed.get("base_ids_n"),
        "dictionary_active_n": data_summary["active_dictionary_join_n"],
        "n_genes_used": len(rows),
        "u_energy_ratio_full_active": reconstructed["u_energy_ratio_full_active"],
        "u_energy_ratio_proteostasis_join": bounded_unit(u_norm2 / p_q_norm2) if p_q_norm2 > EPS else 0.0,
        "A_prot": a_prot,
        "A_prot_projected_energy": projected_energy,
        "A_prot_rank_delta": rank_delta,
        "null95": null95,
        "null_mean": null["null_mean"],
        "null_max": null["null_max"],
        "p_prot": p_prot,
        "heldout_delta_r2": cv["heldout_delta_r2"],
        "heldout_model_r2": cv["heldout_model_r2"],
        "heldout_baseline_r2": cv["heldout_baseline_r2"],
        "dominant_partial_spearman": {
            "component": dominant_component,
            "rho": dominant_partial_rho,
            "all_components": partials,
            "controls": ["protein_abundance_log10", "protein_length"],
        },
        "matched_null": {
            "B": B,
            "model": "within protein_abundance_decile x protein_length_decile, permute the standardized proteostasis-mismatch feature rows and recompute projection absorption",
            "strata": strata_summary,
            "deterministic_seed": null["deterministic_seed"],
        },
        "feature_summary": feature_summary,
        "data_summary": data_summary,
        "decision_rule": {
            "needs_data": "base R2_QP outside [0.25,0.34] or proteostasis join n below the project organism gate",
            "crosses_boundary": "A_prot exceeds matched-null 95th percentile and heldout_delta_r2 >= 0.01 or dominant partial |rho| >= 0.10",
            "bounded_descriptor_only": "A_prot exceeds matched-null 95th percentile but the effect is below the crossing lower bound",
            "composition_artifact": "A_prot does not exceed matched-null 95th percentile",
        },
        "verdict": verdict,
        "cannot_claim": cannot_claim(),
    }
    return {"status": status, "verdict": verdict, "checks": checks, "result": result}


def cannot_claim() -> list[str]:
    return [
        "Burden-only Delta lacks a chaperone-capacity C term because no local chaperone-client capacity payload is available; a null result cannot exclude chaperone-mediated proteostasis.",
        "Structural_order is mean AlphaFold pLDDT-style predicted order, not an experimental folding-rate or aggregation-rate measurement.",
        "Domain, transmembrane, complex-membership, and PTM-density values are annotation counts rather than dynamic proteostasis states.",
        "log(translation_efficiency) partly overlaps measured-TE information already present in the selected dictionary D, so the Delta subspace and D are not sharply separated; held-out prediction and matched permutation only partially control that collinearity.",
        "The projection is observational and descriptive; it is not a causal perturbation test of translation, folding, chaperone loading, or protein abundance.",
        "The proteostasis test is evaluated on the subset of the selected yeast dictionary join that also has TE, structural-order, and UniProt feature payloads.",
    ]


def main() -> None:
    started = time.time()
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        analysis = analyze(repo)
        payload = {
            "status": analysis["status"],
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": analysis["checks"],
            "verdict": analysis["verdict"],
            "result": analysis["result"],
            "runtime_sec": time.time() - started,
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(0 if analysis["status"] == "passed" else (2 if analysis["status"] == "failed" else 3))
    except Exception as exc:
        payload = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"runtime_exception": True},
            "verdict": "needs_data",
            "result": {"error": str(exc), "cannot_claim": cannot_claim()},
            "runtime_sec": time.time() - started,
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(2)


if __name__ == "__main__":
    main()

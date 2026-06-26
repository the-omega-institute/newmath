#!/usr/bin/env python3
"""Two-axis closure audit for universal optimal synonymous-codon directions."""

from __future__ import annotations

import json
import math
import pathlib
import sys
import types
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

if "_tai" not in sys.modules:
    tai_shim = types.ModuleType("_tai")
    tai_shim.AA_ONE_TO_THREE = {
        "A": "Ala",
        "R": "Arg",
        "N": "Asn",
        "D": "Asp",
        "C": "Cys",
        "Q": "Gln",
        "E": "Glu",
        "G": "Gly",
        "H": "His",
        "I": "Ile",
        "L": "Leu",
        "K": "Lys",
        "M": "Met",
        "F": "Phe",
        "P": "Pro",
        "S": "Ser",
        "T": "Thr",
        "W": "Trp",
        "Y": "Tyr",
        "V": "Val",
    }
    tai_shim.RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}
    tai_shim.DOS_REIS_2004_WOBBLE_S = {
        ("G", "U"): 0.41,
        ("U", "G"): 0.68,
        ("I", "C"): 0.28,
        ("I", "A"): 0.9999,
        ("I", "U"): 0.0,
        ("L", "A"): 0.89,
    }

    def _tai_first_two_positions_match(codon: str, anticodon: str) -> bool:
        return tai_shim.RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and tai_shim.RNA_COMPLEMENT.get(anticodon[1]) == codon[1]

    def _tai_effective_wobble_base(aa_label: str, anticodon: str) -> str:
        wobble = anticodon[0]
        if wobble == "A":
            return "I"
        if aa_label == "Ile2" and anticodon == "CAU":
            return "L"
        return wobble

    def _tai_wobble_penalty(wobble: str, codon_third: str) -> float | None:
        if tai_shim.RNA_COMPLEMENT.get(wobble) == codon_third:
            return 0.0
        return tai_shim.DOS_REIS_2004_WOBBLE_S.get((wobble, codon_third))

    def _tai_codon_w_values(*_args: object, **_kw: object) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
        raise RuntimeError("local _tai shim is import-only in this experiment; Route N codon_w_values is used for tAI")

    tai_shim.first_two_positions_match = _tai_first_two_positions_match
    tai_shim.effective_wobble_base = _tai_effective_wobble_base
    tai_shim.wobble_penalty = _tai_wobble_penalty
    tai_shim.codon_w_values = _tai_codon_w_values
    sys.modules["_tai"] = tai_shim

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    F3_COORDINATE,
    deterministic_folds,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    cv_r2_multivariate,
    solve_linear_system,
    synonymous_contrast_columns,
    xtx_xty,
)
from run_b_star_q6_organism_specificity_meta_powered import (  # noqa: E402
    ORGANISMS,
    organism_domain,
)
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM  # noqa: E402
from run_b_star_q6_translation_survival_powered import (  # noqa: E402
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)
from run_b_star_q6_universal_core_is_trna_adaptation_powered import (  # noqa: E402
    codon_w_values,
    load_trna_records,
    trna_contrast_direction,
)
from run_b_star_q6_universal_optimal_residual_axis_powered import (  # noqa: E402
    cosine,
    cv_r2_fixed_direction,
    finite_numeric,
    fit_optimal_direction,
    gc3_contrast_direction,
    load_json,
    mean,
    median,
    organism_rows,
    sign_test_greater,
    t_test_mean_greater_zero,
    unit_vector,
    vector_norm,
)


EXPERIMENT_ID = "b_star_q6_universal_optimal_two_axis_closure_powered"
CLAIM_ID = "h3.cross_layer_relation.universal_optimal_two_axis_closure.b_star_q6_trna_f3_span_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
MIN_MEAN_CAPTURED_FRACTION_FOR_CLOSURE = 0.50
MAX_MEAN_PERP_POSITIVE_R2_RATIO_FOR_CLOSURE = 0.25
MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_THIRD_AXIS = 0.08
ALPHA = 0.05
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def paired_sign_test_greater(left: list[float], right: list[float]) -> dict[str, object]:
    deltas = [left[index] - right[index] for index in range(min(len(left), len(right)))]
    return {**sign_test_greater(deltas), "mean_delta": mean(deltas), "median_delta": median(deltas)}


def summarize_values(values: list[float]) -> dict[str, object]:
    if not values:
        return {
            "n": 0,
            "mean": None,
            "median": None,
            "min": None,
            "max": None,
            "positive_count": 0,
            "negative_count": 0,
        }
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values),
        "max": max(values),
        "positive_count": sum(1 for value in values if value > EPS),
        "negative_count": sum(1 for value in values if value < -EPS),
    }


def normal_approx_mean_less_equal_threshold(values: list[float], threshold: float) -> dict[str, object]:
    n = len(values)
    value_mean = mean(values)
    if n < 2 or value_mean is None:
        return {"n": n, "threshold": threshold, "mean": value_mean, "sd": None, "z_approx": None, "p_less_equal_normal_approx": None}
    variance = sum((value - value_mean) ** 2 for value in values) / (n - 1)
    sd = math.sqrt(variance)
    if sd <= EPS:
        z = -math.inf if value_mean < threshold else (math.inf if value_mean > threshold else 0.0)
    else:
        z = (value_mean - threshold) / (sd / math.sqrt(n))
    p = 0.0 if z == -math.inf else (1.0 if z == math.inf else normal_cdf(z))
    return {
        "n": n,
        "threshold": threshold,
        "mean": value_mean,
        "sd": sd,
        "z_approx": z,
        "p_less_equal_normal_approx": p,
    }


def fixed_basis_cv_r2(
    x_rows: list[list[float]],
    y: list[float],
    basis: list[list[float]],
    folds: list[list[int]],
) -> tuple[float, list[float], dict[str, object]]:
    predictors = [[vector_dot(row, direction) for direction in basis] for row in x_rows]
    if not predictors or not predictors[0]:
        return 0.0, [], {"ridge_steps": [], "predictor_count": 0}
    xtx, xty = xtx_xty(predictors, y)
    full_beta, full_ridge_step = solve_linear_system(xtx, xty)
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return 0.0, full_beta, {"full_sample_ridge_step": full_ridge_step, "fold_ridge_steps": [], "predictor_count": len(basis)}
    all_indices = set(range(len(y)))
    sse = 0.0
    fold_ridge_steps: list[int] = []
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        fold_xtx, fold_xty = xtx_xty(predictors, y, train_indices)
        fold_beta, fold_ridge_step = solve_linear_system(fold_xtx, fold_xty)
        fold_ridge_steps.append(fold_ridge_step)
        for index in test_indices:
            predicted = sum(fold_beta[j] * predictors[index][j] for j in range(len(fold_beta)))
            residual = y[index] - predicted
            sse += residual * residual
    return 1.0 - sse / y_energy, full_beta, {
        "full_sample_ridge_step": full_ridge_step,
        "fold_ridge_steps": fold_ridge_steps,
        "predictor_count": len(basis),
    }


def orthonormal_trna_f3_basis(
    trna_direction: list[float],
    f3_direction: list[float],
) -> tuple[list[list[float]] | None, dict[str, object]]:
    e_trna = unit_vector(trna_direction)
    if e_trna is None:
        return None, {"reason": "zero tRNA direction"}
    f3_parallel = vector_dot(f3_direction, e_trna)
    f3_perp_raw = [f3_direction[index] - f3_parallel * e_trna[index] for index in range(len(f3_direction))]
    e_f3_perp = unit_vector(f3_perp_raw)
    if e_f3_perp is None:
        return [e_trna], {
            "span_rank": 1,
            "cos_trna_f3": cosine(trna_direction, f3_direction),
            "f3_residual_norm_after_trna_projection": vector_norm(f3_perp_raw),
            "reason": "f3 direction collapsed after projecting out tRNA direction",
        }
    return [e_trna, e_f3_perp], {
        "span_rank": 2,
        "cos_trna_f3": cosine(trna_direction, f3_direction),
        "f3_residual_norm_after_trna_projection": vector_norm(f3_perp_raw),
    }


def project_onto_basis(direction: list[float], basis: list[list[float]]) -> tuple[list[float], list[float]]:
    coefficients = [vector_dot(direction, basis_vector) for basis_vector in basis]
    projection = [0.0 for _ in direction]
    for coefficient, basis_vector in zip(coefficients, basis):
        for index in range(len(direction)):
            projection[index] += coefficient * basis_vector[index]
    return projection, coefficients


def residual_after_basis(direction: list[float], basis: list[list[float]]) -> tuple[list[float] | None, float, list[float]]:
    projection, coefficients = project_onto_basis(direction, basis)
    direction_energy = vector_dot(direction, direction)
    projection_energy = vector_dot(projection, projection)
    captured_fraction = 0.0 if direction_energy <= EPS else max(0.0, min(1.0, projection_energy / direction_energy))
    residual_raw = [direction[index] - projection[index] for index in range(len(direction))]
    return unit_vector(residual_raw), captured_fraction, coefficients


def pairwise_cosine_summary(rows: list[dict[str, object]], direction_key: str) -> dict[str, object]:
    pairs: list[dict[str, object]] = []
    cosines: list[float] = []
    abs_cosines: list[float] = []
    for left_index in range(len(rows)):
        left_direction = rows[left_index].get(direction_key)
        if not isinstance(left_direction, list):
            continue
        for right_index in range(left_index + 1, len(rows)):
            right_direction = rows[right_index].get(direction_key)
            if not isinstance(right_direction, list):
                continue
            value = cosine(left_direction, right_direction)
            cosines.append(value)
            abs_cosines.append(abs(value))
            pairs.append(
                {
                    "left": rows[left_index]["organism"],
                    "right": rows[right_index]["organism"],
                    "cosine": value,
                    "abs_cosine": abs(value),
                }
            )
    return {
        "pair_count": len(cosines),
        "mean_pairwise_cosine": mean(cosines),
        "median_pairwise_cosine": median(cosines),
        "mean_abs_pairwise_cosine": mean(abs_cosines),
        "median_abs_pairwise_cosine": median(abs_cosines),
        "min_pairwise_cosine": None if not cosines else min(cosines),
        "max_pairwise_cosine": None if not cosines else max(cosines),
        "pairwise_cosine_sign_test_greater": sign_test_greater(cosines),
        "pairwise_cosine_mean_test_normal_approx": t_test_mean_greater_zero(cosines),
        "pairs": pairs,
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
) -> dict[str, object]:
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    proteomics_path = data_dir / f"proteomics_abundance_{organism}.json"
    gtrna_path = data_dir / f"gtrnadb_trna_all_copy_{organism}.json"
    trna_summary_path = data_dir / f"trna_gene_copy_{organism}.json"
    if not cds_path.exists() or not proteomics_path.exists() or (not gtrna_path.exists() and not trna_summary_path.exists()):
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance, proteomics_abundance, or GtRNAdb/tRNA JSON",
            "cds_exists": cds_path.exists(),
            "proteomics_exists": proteomics_path.exists(),
            "gtrnadb_exists": gtrna_path.exists(),
            "trna_summary_exists": trna_summary_path.exists(),
        }

    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "cds payload is not an object"}
    proteomics_payload = load_json(proteomics_path)
    proteomics_n = proteomics_payload.get("n_proteins") if isinstance(proteomics_payload, dict) else None

    syn_raw, y_raw, controls, gc3, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    n_join = len(y_raw)
    base = {
        "organism": organism,
        "status": "needs_data",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "data_summary": data_summary,
    }
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        base["reason"] = f"join below gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}"
        return base

    trna_records, trna_source_summary = load_trna_records(repo, organism)
    weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    if trna_direction is None:
        base["reason"] = "zero tRNA contrast direction"
        base["trna_source_summary"] = trna_source_summary
        base["tai_weight_summary"] = tai_summary
        return base

    span_basis, span_summary = orthonormal_trna_f3_basis(trna_direction, f3_direction)
    if span_basis is None:
        base["reason"] = str(span_summary.get("reason", "could not construct tRNA/f3 span"))
        base["trna_source_summary"] = trna_source_summary
        base["tai_weight_summary"] = tai_summary
        return base

    syn_residualized, rank_controls_syn = residualize(syn_raw, controls)
    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y = matrix_column(y_residualized, 0)
    if vector_dot(y, y) <= EPS:
        base["reason"] = "zero residual abundance energy after controls"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        return base

    optimal_direction, fit_summary = fit_optimal_direction(syn_residualized, y)
    if optimal_direction is None:
        base["reason"] = str(fit_summary.get("reason", "could not fit optimal direction"))
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    d_perp_direction, captured_fraction, span_coefficients = residual_after_basis(optimal_direction, span_basis)
    if d_perp_direction is None:
        d_perp_residual_norm = 0.0
    else:
        projection, _ = project_onto_basis(optimal_direction, span_basis)
        d_perp_residual_norm = vector_norm([optimal_direction[index] - projection[index] for index in range(len(optimal_direction))])

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)
    trna_r2, trna_slope = cv_r2_fixed_direction(syn_residualized, y, trna_direction, folds)
    f3_r2, f3_slope = cv_r2_fixed_direction(syn_residualized, y, f3_direction, folds)
    two_axis_r2, two_axis_slopes, two_axis_cv_summary = fixed_basis_cv_r2(syn_residualized, y, span_basis, folds)
    if d_perp_direction is None:
        d_perp_r2 = 0.0
        d_perp_slope = 0.0
    else:
        d_perp_r2, d_perp_slope = cv_r2_fixed_direction(syn_residualized, y, d_perp_direction, folds)

    positive_self = max(0.0, self_r2)
    positive_two_axis = max(0.0, two_axis_r2)
    positive_d_perp = max(0.0, d_perp_r2)

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "optimal_direction": optimal_direction,
        "trna_direction": trna_direction,
        "f3_direction": f3_direction,
        "d_perp_direction": d_perp_direction,
        "captured_fraction": captured_fraction,
        "d_perp_residual_norm": d_perp_residual_norm,
        "span_rank": span_summary["span_rank"],
        "span_coefficients": {
            "trna": span_coefficients[0] if len(span_coefficients) > 0 else None,
            "f3_after_trna_orthogonalization": span_coefficients[1] if len(span_coefficients) > 1 else None,
        },
        "cos_optimal_trna": cosine(optimal_direction, trna_direction),
        "cos_optimal_f3": cosine(optimal_direction, f3_direction),
        "cos_trna_f3": cosine(trna_direction, f3_direction),
        "cos_d_perp_trna": None if d_perp_direction is None else cosine(d_perp_direction, trna_direction),
        "cos_d_perp_f3": None if d_perp_direction is None else cosine(d_perp_direction, f3_direction),
        "total_syn_selection_held_out_r2": total_syn_selection,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "trna_alone_held_out_r2": trna_r2,
        "trna_alone_slope": trna_slope,
        "f3_direction_held_out_r2": f3_r2,
        "f3_direction_slope": f3_slope,
        "two_axis_held_out_r2": two_axis_r2,
        "two_axis_slopes": two_axis_slopes,
        "two_axis_positive_r2_over_self_positive_r2": None if positive_self <= EPS else positive_two_axis / positive_self,
        "d_perp_held_out_r2": d_perp_r2,
        "d_perp_slope": d_perp_slope,
        "d_perp_positive_r2_over_self_positive_r2": None if positive_self <= EPS else positive_d_perp / positive_self,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "span_summary": span_summary,
        "two_axis_cv_summary": two_axis_cv_summary,
        "synonymous_cv_summary": syn_cv_summary,
        "residual_synonymous_columns": len(syn_columns),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
        "trna_source_summary": trna_source_summary,
        "tai_weight_summary": {
            **tai_summary,
            "raw_W_by_codon": raw_w,
            "normalized_w_by_codon": weights,
        },
    }


def compact_per_organism(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    output = []
    for row in rows:
        output.append(
            {
                "organism": row["organism"],
                "domain": row["domain"],
                "gc3": row["gc3"],
                "n_join": row["n_join"],
                "captured_fraction": row["captured_fraction"],
                "d_perp_R2": row["d_perp_held_out_r2"],
                "trna_R2": row["trna_alone_held_out_r2"],
                "f3_R2": row["f3_direction_held_out_r2"],
                "two_axis_R2": row["two_axis_held_out_r2"],
                "self_R2": row["self_direction_held_out_r2"],
                "total_syn_selection_R2": row["total_syn_selection_held_out_r2"],
                "two_axis_positive_R2_over_self_positive_R2": row["two_axis_positive_r2_over_self_positive_r2"],
                "d_perp_positive_R2_over_self_positive_R2": row["d_perp_positive_r2_over_self_positive_r2"],
                "d_perp_residual_norm": row["d_perp_residual_norm"],
                "span_rank": row["span_rank"],
                "cos_optimal_trna": row["cos_optimal_trna"],
                "cos_optimal_f3": row["cos_optimal_f3"],
                "cos_trna_f3": row["cos_trna_f3"],
                "cos_d_perp_trna": row["cos_d_perp_trna"],
                "cos_d_perp_f3": row["cos_d_perp_f3"],
                "fit_coefficient_norm": row["fit_summary"].get("coefficient_norm"),
                "usable_tai_record_count": row["trna_source_summary"].get("usable_tai_record_count"),
            }
        )
    return sorted(output, key=lambda item: str(item["organism"]))


def numeric_values(rows: list[dict[str, object]], key: str) -> list[float]:
    return [float(row[key]) for row in rows if finite_numeric(row.get(key))]


def determine_verdict(
    *,
    captured_fractions: list[float],
    d_perp_r2_values: list[float],
    self_r2_values: list[float],
    d_perp_ratios: list[float],
    pairwise_summary: dict[str, object],
) -> tuple[str, dict[str, object]]:
    positive_d_perp_r2 = [max(0.0, value) for value in d_perp_r2_values]
    positive_self_r2 = [max(0.0, value) for value in self_r2_values]
    mean_positive_d_perp = mean(positive_d_perp_r2)
    mean_positive_self = mean(positive_self_r2)
    pooled_perp_ratio = None if mean_positive_self is None or mean_positive_self <= EPS or mean_positive_d_perp is None else mean_positive_d_perp / mean_positive_self

    captured_high_sign = sign_test_greater([value - MIN_MEAN_CAPTURED_FRACTION_FOR_CLOSURE for value in captured_fractions])
    captured_high_mean = t_test_mean_greater_zero([value - MIN_MEAN_CAPTURED_FRACTION_FOR_CLOSURE for value in captured_fractions])
    residual_positive_sign = sign_test_greater(d_perp_r2_values)
    residual_positive_mean = t_test_mean_greater_zero(d_perp_r2_values)
    residual_ratio_low = (
        pooled_perp_ratio is not None
        and pooled_perp_ratio <= MAX_MEAN_PERP_POSITIVE_R2_RATIO_FOR_CLOSURE
        and normal_approx_mean_less_equal_threshold(
            [max(0.0, value) for value in d_perp_ratios],
            MAX_MEAN_PERP_POSITIVE_R2_RATIO_FOR_CLOSURE,
        )
    )

    mean_captured = mean(captured_fractions)
    p_captured = captured_high_sign.get("p_greater")
    captured_is_high = (
        mean_captured is not None
        and mean_captured >= MIN_MEAN_CAPTURED_FRACTION_FOR_CLOSURE
        and p_captured is not None
        and float(p_captured) <= ALPHA
    )

    p_residual_sign = residual_positive_sign.get("p_greater")
    p_residual_mean = residual_positive_mean.get("p_greater_normal_approx")
    residual_is_systematically_positive = (
        mean(d_perp_r2_values) is not None
        and mean(d_perp_r2_values) > 0.0
        and p_residual_sign is not None
        and float(p_residual_sign) <= ALPHA
        and p_residual_mean is not None
        and float(p_residual_mean) <= ALPHA
        and int(residual_positive_sign.get("positive", 0)) > int(residual_positive_sign.get("negative", 0))
    )

    pairwise_sign = pairwise_summary["pairwise_cosine_sign_test_greater"]
    pairwise_mean_test = pairwise_summary["pairwise_cosine_mean_test_normal_approx"]
    mean_pairwise = pairwise_summary["mean_pairwise_cosine"]
    p_pairwise_sign = pairwise_sign.get("p_greater") if isinstance(pairwise_sign, dict) else None
    p_pairwise_mean = pairwise_mean_test.get("p_greater_normal_approx") if isinstance(pairwise_mean_test, dict) else None
    universal_third_axis_aligned = (
        mean_pairwise is not None
        and float(mean_pairwise) >= MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_THIRD_AXIS
        and p_pairwise_sign is not None
        and float(p_pairwise_sign) <= ALPHA
        and p_pairwise_mean is not None
        and float(p_pairwise_mean) <= ALPHA
    )

    if residual_is_systematically_positive and universal_third_axis_aligned:
        verdict = "third_axis_present"
        reason = "d_perp has systematically positive held-out R2 and d_perp directions are mutually same-signed across organisms"
    elif residual_is_systematically_positive:
        verdict = "organism_specific_residual"
        reason = "d_perp has systematically positive held-out R2, but residual directions do not form a same-signed universal third axis"
    elif captured_is_high and pooled_perp_ratio is not None and pooled_perp_ratio <= MAX_MEAN_PERP_POSITIVE_R2_RATIO_FOR_CLOSURE:
        verdict = "two_axis_closure"
        reason = "tRNA/f3 span captures at least half of d_opt direction on average and residual positive R2 is small relative to self"
    else:
        verdict = "organism_specific_residual"
        reason = "tRNA/f3 span does not clear the high-capture closure gate, and no same-signed universal third axis is detected"

    return verdict, {
        "reason": reason,
        "captured_high_gate": {
            "passed": captured_is_high,
            "threshold": MIN_MEAN_CAPTURED_FRACTION_FOR_CLOSURE,
            "sign_test_greater_than_threshold": captured_high_sign,
            "mean_test_greater_than_threshold_normal_approx": captured_high_mean,
        },
        "d_perp_residual_strength_gate": {
            "systematically_positive": residual_is_systematically_positive,
            "sign_test_greater_than_zero": residual_positive_sign,
            "mean_test_greater_than_zero_normal_approx": residual_positive_mean,
            "pooled_positive_d_perp_R2_over_self_R2": pooled_perp_ratio,
            "closure_max_ratio": MAX_MEAN_PERP_POSITIVE_R2_RATIO_FOR_CLOSURE,
            "ratio_low_diagnostic": residual_ratio_low,
        },
        "universal_third_axis_alignment_gate": {
            "passed": universal_third_axis_aligned,
            "threshold_mean_pairwise_cosine": MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_THIRD_AXIS,
            "mean_pairwise_cosine": mean_pairwise,
            "pairwise_cosine_sign_test_greater": pairwise_sign,
            "pairwise_cosine_mean_test_normal_approx": pairwise_mean_test,
        },
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        gc_direction = gc3_contrast_direction(syn_columns=syn_columns)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)
        f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
        if gc_direction is None or f3_direction is None:
            emit(
                "failed",
                reason="GC3 or f3_stress contrast direction could not be constructed",
                seed=SEED,
                fold_count=FOLD_COUNT,
                checks={
                    "directions_computed": {"passed": False},
                    "captured_fraction_computed": {"passed": False},
                    "closure_verdict_determined": {"passed": False},
                },
            )

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                syn_columns=syn_columns,
                f3_direction=f3_direction,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        directions_ok = n_computed >= MIN_COMPLETE_ORGANISMS and len(syn_columns) == 41
        if not directions_ok:
            emit(
                "needs_data",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                synonymous_design_columns=len(syn_columns),
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
                checks={
                    "directions_computed": {
                        "passed": False,
                        "organisms_computed": n_computed,
                        "minimum": MIN_COMPLETE_ORGANISMS,
                        "synonymous_design_columns": len(syn_columns),
                        "expected_synonymous_design_columns": 41,
                    },
                    "captured_fraction_computed": {"passed": False},
                    "closure_verdict_determined": {"passed": False},
                },
                caveats=[
                    "requires same-organism proteomics, cds_codon_abundance, and GtRNAdb/tRNA gene-copy payloads",
                    "strict same-key organism matching is used; near-name strain substitutions are not inferred",
                ],
            )

        captured_fractions = numeric_values(computed, "captured_fraction")
        d_perp_r2_values = numeric_values(computed, "d_perp_held_out_r2")
        trna_r2_values = numeric_values(computed, "trna_alone_held_out_r2")
        f3_r2_values = numeric_values(computed, "f3_direction_held_out_r2")
        two_axis_r2_values = numeric_values(computed, "two_axis_held_out_r2")
        self_r2_values = numeric_values(computed, "self_direction_held_out_r2")
        total_syn_r2_values = numeric_values(computed, "total_syn_selection_held_out_r2")
        two_axis_ratios = numeric_values(computed, "two_axis_positive_r2_over_self_positive_r2")
        d_perp_ratios = numeric_values(computed, "d_perp_positive_r2_over_self_positive_r2")
        d_perp_norms = numeric_values(computed, "d_perp_residual_norm")

        pairwise_summary = pairwise_cosine_summary(computed, "d_perp_direction")
        verdict, verdict_summary = determine_verdict(
            captured_fractions=captured_fractions,
            d_perp_r2_values=d_perp_r2_values,
            self_r2_values=self_r2_values,
            d_perp_ratios=d_perp_ratios,
            pairwise_summary=pairwise_summary,
        )

        captured_vs_trna_r2 = paired_sign_test_greater(two_axis_r2_values, trna_r2_values)
        captured_vs_f3_r2 = paired_sign_test_greater(two_axis_r2_values, f3_r2_values)
        captured_vs_perp_r2 = paired_sign_test_greater(two_axis_r2_values, d_perp_r2_values)

        checks = {
            "directions_computed": {
                "passed": True,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
                "fixed_reference_directions_available": {
                    "gc3": gc_direction is not None,
                    "f3_stress": f3_direction is not None,
                },
            },
            "captured_fraction_computed": {
                "passed": len(captured_fractions) == n_computed and all(0.0 <= value <= 1.0 for value in captured_fractions),
                "summary": summarize_values(captured_fractions),
            },
            "closure_verdict_determined": {
                "passed": verdict in {"two_axis_closure", "third_axis_present", "organism_specific_residual"},
                "verdict": verdict,
                **verdict_summary,
            },
        }

        emit(
            "passed",
            reason=verdict_summary["reason"],
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            synonymous_design_columns=len(syn_columns),
            conclusion=verdict,
            payload={
                "per_organism": compact_per_organism(computed),
                "cross_species": {
                    "captured_fraction": {
                        **summarize_values(captured_fractions),
                        "sign_test_greater_than_0_5": sign_test_greater([value - 0.5 for value in captured_fractions]),
                        "mean_test_greater_than_0_5_normal_approx": t_test_mean_greater_zero([value - 0.5 for value in captured_fractions]),
                    },
                    "d_perp_R2": {
                        **summarize_values(d_perp_r2_values),
                        "sign_test_greater_than_zero": sign_test_greater(d_perp_r2_values),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(d_perp_r2_values),
                    },
                    "trna_R2": summarize_values(trna_r2_values),
                    "f3_R2": summarize_values(f3_r2_values),
                    "two_axis_R2": {
                        **summarize_values(two_axis_r2_values),
                        "two_axis_greater_than_trna_alone": captured_vs_trna_r2,
                        "two_axis_greater_than_f3_alone": captured_vs_f3_r2,
                        "two_axis_greater_than_d_perp": captured_vs_perp_r2,
                    },
                    "self_R2": summarize_values(self_r2_values),
                    "total_syn_selection_R2": summarize_values(total_syn_r2_values),
                    "two_axis_positive_R2_over_self_positive_R2": summarize_values(two_axis_ratios),
                    "d_perp_positive_R2_over_self_positive_R2": summarize_values(d_perp_ratios),
                    "d_perp_residual_norm": summarize_values(d_perp_norms),
                    "d_perp_pairwise_alignment": pairwise_summary,
                    "cos_gc_f3": cosine(gc_direction, f3_direction),
                },
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "optimal_direction": "Route O construction: full-sample least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized",
                "trna_direction": "Route O/N construction: dos Reis tAI codon weights from same-organism GtRNAdb/tRNA gene-copy records, projected as w_positive_codon - w_reference_codon on the same 41 contrasts, then unit-normalized",
                "f3_direction": "Route O construction: fixed f3_stress vector from q_vectors(codons)['f3_stress'], synonymous-family projected with project_syn, converted to the same 41 contrast columns, then unit-normalized",
                "two_axis_projection": "orthonormal basis [d_tRNA, normalize(d_f3 - (d_f3 dot d_tRNA)d_tRNA)]; captured_fraction = ||Proj_span(d_opt)||^2 / ||d_opt||^2",
                "d_perp": "normalize(d_opt - Proj_span{d_tRNA,d_f3}(d_opt)); if the residual norm is numerically zero, d_perp R2 is reported as 0",
                "held_out_strength": "5-fold CV R2 for fixed one-dimensional directions or the fixed two-dimensional span with fold-local slope(s), after residualizing target and synonymous contrasts against controls",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            checks=checks,
            organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            caveats=[
                "observational abundance-associated optimal directions are not causal perturbation estimates",
                "tRNA gene copy number and dos Reis wobble penalties are proxies for supply/adaptation, not direct charged tRNA abundance",
                "captured fraction is a coefficient-space geometric diagnostic; held-out R2 is the abundance-prediction diagnostic and can differ because synonymous contrast predictors are correlated",
                "the one-sided mean tests use a normal approximation because the standard library has no exact t CDF",
                "no phylogenetic comparative correction is applied",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "directions_computed": {"passed": False},
                "captured_fraction_computed": {"passed": False},
                "closure_verdict_determined": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

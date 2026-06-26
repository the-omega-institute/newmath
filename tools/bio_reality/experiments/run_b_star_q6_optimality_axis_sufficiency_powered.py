#!/usr/bin/env python3
"""Three independent mechanism-axis sufficiency audit for optimal codon directions."""

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
    synonymous_contrast_columns,
)
from run_b_star_q6_organism_specificity_meta_powered import (  # noqa: E402
    ORGANISMS,
    organism_domain,
)
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_third_axis_identity_powered import (  # noqa: E402
    contrast_direction_from_codon_values,
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
    load_json,
    mean,
    median,
    organism_rows,
    sign_test_greater,
    t_test_mean_greater_zero,
    unit_vector,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import (  # noqa: E402
    fixed_basis_cv_r2,
    pairwise_cosine_summary,
    project_onto_basis,
    residual_after_basis,
)


EXPERIMENT_ID = "b_star_q6_optimality_axis_sufficiency_powered"
CLAIM_ID = "h3.cross_layer_relation.optimality_axis_sufficiency.b_star_q6_three_axis_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_FOURTH = 0.08
ALPHA = 0.05
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


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


def numeric_values(rows: list[dict[str, object]], key: str) -> list[float]:
    return [float(row[key]) for row in rows if finite_numeric(row.get(key))]


def paired_sign_test_greater(left: list[float], right: list[float]) -> dict[str, object]:
    deltas = [left[index] - right[index] for index in range(min(len(left), len(right)))]
    return {**sign_test_greater(deltas), "mean_delta": mean(deltas), "median_delta": median(deltas)}


def pooled_positive_ratio(numerator: list[float], denominator: list[float]) -> float | None:
    numerator_mean = mean([max(0.0, value) for value in numerator])
    denominator_mean = mean([max(0.0, value) for value in denominator])
    if numerator_mean is None or denominator_mean is None or denominator_mean <= EPS:
        return None
    return numerator_mean / denominator_mean


def usage_frequency_axis(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
) -> tuple[list[float] | None, dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        return None, {"reason": "cds payload lacks joined list"}
    counts = {codon: 0 for codon in codons}
    records_used = 0
    skipped_non_object = 0
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped_non_object += 1
            continue
        row_counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(row_counts.values())
        if total <= 0:
            continue
        records_used += 1
        for codon in codons:
            counts[codon] += row_counts[codon]

    family_frequencies: dict[str, float] = {}
    zero_count_families = 0
    for family in fibers.values():
        total = sum(counts[codon] for codon in family)
        if total <= 0:
            zero_count_families += 1
            for codon in family:
                family_frequencies[codon] = 0.0
            continue
        for codon in family:
            family_frequencies[codon] = counts[codon] / total

    direction = contrast_direction_from_codon_values(family_frequencies, syn_columns)
    return direction, {
        "records_used": records_used,
        "skipped_non_object_records": skipped_non_object,
        "total_sense_codons": sum(counts.values()),
        "zero_count_families": zero_count_families,
        "definition": "within-synonymous-family CDS codon usage frequency from cds_codon_abundance joined records; independent of d_opt",
    }


def orthonormal_basis(
    named_directions: list[tuple[str, list[float]]],
) -> tuple[list[list[float]] | None, dict[str, object]]:
    basis: list[list[float]] = []
    steps: list[dict[str, object]] = []
    for name, direction in named_directions:
        raw_norm = vector_norm(direction)
        residual = [float(value) for value in direction]
        projection_coefficients = []
        for basis_vector in basis:
            coefficient = vector_dot(residual, basis_vector)
            projection_coefficients.append(coefficient)
            residual = [residual[index] - coefficient * basis_vector[index] for index in range(len(residual))]
        residual_norm = vector_norm(residual)
        unit = unit_vector(residual)
        accepted = unit is not None
        if accepted and unit is not None:
            basis.append(unit)
        steps.append(
            {
                "axis": name,
                "raw_norm": raw_norm,
                "residual_norm_after_previous_basis": residual_norm,
                "accepted_into_basis": accepted,
                "projection_coefficients_onto_previous_basis": projection_coefficients,
            }
        )
    if not basis:
        return None, {"span_rank": 0, "steps": steps, "reason": "all directions collapsed"}
    return basis, {"span_rank": len(basis), "axis_count_requested": len(named_directions), "steps": steps}


def axis_independence_summary(rows: list[dict[str, object]]) -> dict[str, object]:
    trna_f3 = numeric_values(rows, "cos_trna_f3")
    trna_usage = numeric_values(rows, "cos_trna_usage")
    f3_usage = numeric_values(rows, "cos_f3_usage")
    return {
        "trna_vs_f3_cosine": {
            **summarize_values(trna_f3),
            "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(trna_f3),
        },
        "trna_vs_usage_cosine": {
            **summarize_values(trna_usage),
            "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(trna_usage),
        },
        "f3_vs_usage_cosine": {
            **summarize_values(f3_usage),
            "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(f3_usage),
        },
        "mean_abs_cosines": {
            "trna_vs_f3": mean([abs(value) for value in trna_f3]),
            "trna_vs_usage": mean([abs(value) for value in trna_usage]),
            "f3_vs_usage": mean([abs(value) for value in f3_usage]),
        },
    }


def fourth_mechanism_verdict(
    *,
    d_resid4_r2_values: list[float],
    d_resid4_pairwise_summary: dict[str, object],
) -> tuple[str, dict[str, object]]:
    r2_sign = sign_test_greater(d_resid4_r2_values)
    r2_mean_test = t_test_mean_greater_zero(d_resid4_r2_values)
    r2_mean = mean(d_resid4_r2_values)
    r2_p_sign = r2_sign.get("p_greater")
    r2_p_mean = r2_mean_test.get("p_greater_normal_approx")
    r2_systematically_positive = (
        r2_mean is not None
        and r2_mean > 0.0
        and r2_p_sign is not None
        and float(r2_p_sign) <= ALPHA
        and r2_p_mean is not None
        and float(r2_p_mean) <= ALPHA
        and int(r2_sign.get("positive", 0)) > int(r2_sign.get("negative", 0))
    )

    pairwise_sign = d_resid4_pairwise_summary.get("pairwise_cosine_sign_test_greater")
    pairwise_mean_test = d_resid4_pairwise_summary.get("pairwise_cosine_mean_test_normal_approx")
    mean_pairwise = d_resid4_pairwise_summary.get("mean_pairwise_cosine")
    p_pairwise_sign = pairwise_sign.get("p_greater") if isinstance(pairwise_sign, dict) else None
    p_pairwise_mean = pairwise_mean_test.get("p_greater_normal_approx") if isinstance(pairwise_mean_test, dict) else None
    pairwise_aligned = (
        mean_pairwise is not None
        and float(mean_pairwise) >= MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_FOURTH
        and p_pairwise_sign is not None
        and float(p_pairwise_sign) <= ALPHA
        and p_pairwise_mean is not None
        and float(p_pairwise_mean) <= ALPHA
    )

    fourth_present = r2_systematically_positive and pairwise_aligned
    verdict = "fourth_mechanism_present" if fourth_present else "three_independent_axes_largely_sufficient"
    reason = (
        "d_resid4 remains same-signed across species and has systematically positive held-out abundance R2"
        if fourth_present
        else "d_resid4 does not jointly clear cross-species alignment and held-out abundance-prediction gates"
    )
    return verdict, {
        "reason": reason,
        "fourth_present": fourth_present,
        "alignment_gate": {
            "passed": pairwise_aligned,
            "threshold_mean_pairwise_cosine": MIN_MEAN_PAIRWISE_COSINE_FOR_UNIVERSAL_FOURTH,
            "mean_pairwise_cosine": mean_pairwise,
            "pairwise_cosine_sign_test_greater": pairwise_sign,
            "pairwise_cosine_mean_test_normal_approx": pairwise_mean_test,
        },
        "held_out_R2_gate": {
            "passed": r2_systematically_positive,
            "sign_test_greater_than_zero": r2_sign,
            "mean_test_greater_than_zero_normal_approx": r2_mean_test,
        },
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
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

    usage_direction, usage_summary = usage_frequency_axis(
        payload=payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    if usage_direction is None:
        base["reason"] = str(usage_summary.get("reason", "could not construct usage-frequency axis"))
        base["trna_source_summary"] = trna_source_summary
        base["tai_weight_summary"] = tai_summary
        base["usage_axis_summary"] = usage_summary
        return base

    two_axis_basis, two_axis_basis_summary = orthonormal_basis([("d_tRNA", trna_direction), ("d_f3", f3_direction)])
    three_axis_basis, three_axis_basis_summary = orthonormal_basis(
        [("d_tRNA", trna_direction), ("d_f3", f3_direction), ("d_usage", usage_direction)]
    )
    if two_axis_basis is None or three_axis_basis is None:
        base["reason"] = "could not construct fixed mechanism-axis basis"
        base["two_axis_basis_summary"] = two_axis_basis_summary
        base["three_axis_basis_summary"] = three_axis_basis_summary
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

    d_resid2_direction, captured_fraction_2, two_axis_projection_coefficients = residual_after_basis(optimal_direction, two_axis_basis)
    d_resid4_direction, captured_fraction_3indep, three_axis_projection_coefficients = residual_after_basis(
        optimal_direction,
        three_axis_basis,
    )
    if d_resid4_direction is None:
        d_resid4_residual_norm = 0.0
    else:
        three_axis_projection, _ = project_onto_basis(optimal_direction, three_axis_basis)
        d_resid4_residual_norm = vector_norm(
            [optimal_direction[index] - three_axis_projection[index] for index in range(len(optimal_direction))]
        )

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)
    trna_r2, trna_slope = cv_r2_fixed_direction(syn_residualized, y, trna_direction, folds)
    f3_r2, f3_slope = cv_r2_fixed_direction(syn_residualized, y, f3_direction, folds)
    usage_r2, usage_slope = cv_r2_fixed_direction(syn_residualized, y, usage_direction, folds)
    two_axis_r2, two_axis_slopes, two_axis_cv_summary = fixed_basis_cv_r2(syn_residualized, y, two_axis_basis, folds)
    three_axis_r2, three_axis_slopes, three_axis_cv_summary = fixed_basis_cv_r2(syn_residualized, y, three_axis_basis, folds)
    if d_resid2_direction is None:
        d_resid2_r2 = 0.0
        d_resid2_slope = 0.0
    else:
        d_resid2_r2, d_resid2_slope = cv_r2_fixed_direction(syn_residualized, y, d_resid2_direction, folds)
    if d_resid4_direction is None:
        d_resid4_r2 = 0.0
        d_resid4_slope = 0.0
    else:
        d_resid4_r2, d_resid4_slope = cv_r2_fixed_direction(syn_residualized, y, d_resid4_direction, folds)

    positive_self = max(0.0, self_r2)
    positive_two_axis = max(0.0, two_axis_r2)
    positive_three_axis = max(0.0, three_axis_r2)
    positive_resid4 = max(0.0, d_resid4_r2)

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
        "usage_direction": usage_direction,
        "d_resid2_direction": d_resid2_direction,
        "d_resid4_direction": d_resid4_direction,
        "captured_fraction_2": captured_fraction_2,
        "captured_fraction_3indep": captured_fraction_3indep,
        "d_resid4_residual_norm": d_resid4_residual_norm,
        "two_axis_span_rank": two_axis_basis_summary["span_rank"],
        "three_axis_span_rank": three_axis_basis_summary["span_rank"],
        "two_axis_projection_coefficients": two_axis_projection_coefficients,
        "three_axis_projection_coefficients": three_axis_projection_coefficients,
        "cos_optimal_trna": cosine(optimal_direction, trna_direction),
        "cos_optimal_f3": cosine(optimal_direction, f3_direction),
        "cos_optimal_usage": cosine(optimal_direction, usage_direction),
        "cos_trna_f3": cosine(trna_direction, f3_direction),
        "cos_trna_usage": cosine(trna_direction, usage_direction),
        "cos_f3_usage": cosine(f3_direction, usage_direction),
        "total_syn_selection_held_out_r2": total_syn_selection,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "trna_alone_held_out_r2": trna_r2,
        "trna_alone_slope": trna_slope,
        "f3_direction_held_out_r2": f3_r2,
        "f3_direction_slope": f3_slope,
        "usage_direction_held_out_r2": usage_r2,
        "usage_direction_slope": usage_slope,
        "two_axis_held_out_r2": two_axis_r2,
        "two_axis_slopes": two_axis_slopes,
        "three_indep_axis_held_out_r2": three_axis_r2,
        "three_indep_axis_slopes": three_axis_slopes,
        "d_resid2_held_out_r2": d_resid2_r2,
        "d_resid2_slope": d_resid2_slope,
        "d_resid4_held_out_r2": d_resid4_r2,
        "d_resid4_slope": d_resid4_slope,
        "two_axis_positive_r2_over_self_positive_r2": None if positive_self <= EPS else positive_two_axis / positive_self,
        "three_axis_positive_r2_over_self_positive_r2": None if positive_self <= EPS else positive_three_axis / positive_self,
        "d_resid4_positive_r2_over_self_positive_r2": None if positive_self <= EPS else positive_resid4 / positive_self,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "two_axis_basis_summary": two_axis_basis_summary,
        "three_axis_basis_summary": three_axis_basis_summary,
        "two_axis_cv_summary": two_axis_cv_summary,
        "three_axis_cv_summary": three_axis_cv_summary,
        "synonymous_cv_summary": syn_cv_summary,
        "residual_synonymous_columns": len(syn_columns),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
        "usage_axis_summary": usage_summary,
        "trna_source_summary": trna_source_summary,
        "tai_weight_summary": {
            **tai_summary,
            "raw_w_min": min(raw_w.values()) if raw_w else None,
            "raw_w_max": max(raw_w.values()) if raw_w else None,
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
                "captured_fraction_2": row["captured_fraction_2"],
                "captured_fraction_3indep": row["captured_fraction_3indep"],
                "two_axis_R2": row["two_axis_held_out_r2"],
                "three_indep_axis_R2": row["three_indep_axis_held_out_r2"],
                "self_R2": row["self_direction_held_out_r2"],
                "d_resid4_R2": row["d_resid4_held_out_r2"],
                "trna_R2": row["trna_alone_held_out_r2"],
                "f3_R2": row["f3_direction_held_out_r2"],
                "usage_R2": row["usage_direction_held_out_r2"],
                "total_syn_selection_R2": row["total_syn_selection_held_out_r2"],
                "three_axis_positive_R2_over_self_positive_R2": row["three_axis_positive_r2_over_self_positive_r2"],
                "two_axis_positive_R2_over_self_positive_R2": row["two_axis_positive_r2_over_self_positive_r2"],
                "d_resid4_positive_R2_over_self_positive_R2": row["d_resid4_positive_r2_over_self_positive_r2"],
                "d_resid4_residual_norm": row["d_resid4_residual_norm"],
                "two_axis_span_rank": row["two_axis_span_rank"],
                "three_axis_span_rank": row["three_axis_span_rank"],
                "cos_optimal_trna": row["cos_optimal_trna"],
                "cos_optimal_f3": row["cos_optimal_f3"],
                "cos_optimal_usage": row["cos_optimal_usage"],
                "cos_trna_f3": row["cos_trna_f3"],
                "cos_trna_usage": row["cos_trna_usage"],
                "cos_f3_usage": row["cos_f3_usage"],
                "fit_coefficient_norm": row["fit_summary"].get("coefficient_norm"),
                "usage_records_used": row["usage_axis_summary"].get("records_used"),
                "usable_tai_record_count": row["trna_source_summary"].get("usable_tai_record_count"),
            }
        )
    return sorted(output, key=lambda item: str(item["organism"]))


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)
        f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
        if f3_direction is None or len(syn_columns) != 41:
            emit(
                "failed",
                reason="could not construct f3_stress synonymous contrast direction",
                seed=SEED,
                fold_count=FOLD_COUNT,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "independent_axes_computed": {"passed": False},
                    "joint_capture_below_one": {"passed": False},
                    "fourth_mechanism_verdict": {"passed": False},
                },
            )

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                fibers=fibers,
                syn_columns=syn_columns,
                f3_direction=f3_direction,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        if n_computed < MIN_COMPLETE_ORGANISMS:
            emit(
                "needs_data",
                reason="complete proteomics/cds_codon_abundance/tRNA organism intersection below gate",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "independent_axes_computed": {"passed": False, "organisms_computed": n_computed, "minimum": MIN_COMPLETE_ORGANISMS},
                    "joint_capture_below_one": {"passed": False},
                    "fourth_mechanism_verdict": {"passed": False},
                },
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            )

        captured_2 = numeric_values(computed, "captured_fraction_2")
        captured_3 = numeric_values(computed, "captured_fraction_3indep")
        trna_r2 = numeric_values(computed, "trna_alone_held_out_r2")
        f3_r2 = numeric_values(computed, "f3_direction_held_out_r2")
        usage_r2 = numeric_values(computed, "usage_direction_held_out_r2")
        two_axis_r2 = numeric_values(computed, "two_axis_held_out_r2")
        three_axis_r2 = numeric_values(computed, "three_indep_axis_held_out_r2")
        self_r2 = numeric_values(computed, "self_direction_held_out_r2")
        d_resid4_r2 = numeric_values(computed, "d_resid4_held_out_r2")
        total_syn_r2 = numeric_values(computed, "total_syn_selection_held_out_r2")
        two_axis_ratios = numeric_values(computed, "two_axis_positive_r2_over_self_positive_r2")
        three_axis_ratios = numeric_values(computed, "three_axis_positive_r2_over_self_positive_r2")
        resid4_ratios = numeric_values(computed, "d_resid4_positive_r2_over_self_positive_r2")
        resid4_norms = numeric_values(computed, "d_resid4_residual_norm")

        d_resid4_pairwise = pairwise_cosine_summary(computed, "d_resid4_direction")
        verdict, verdict_summary = fourth_mechanism_verdict(
            d_resid4_r2_values=d_resid4_r2,
            d_resid4_pairwise_summary=d_resid4_pairwise,
        )

        mean_captured_3 = mean(captured_3)
        joint_capture_below_one = (
            len(captured_3) == n_computed
            and all(0.0 <= value <= 1.0 + 1e-10 for value in captured_3)
            and mean_captured_3 is not None
            and mean_captured_3 < 1.0 - 1e-10
            and all(value < 1.0 - 1e-10 for value in captured_3)
        )

        independent_axes_computed = (
            n_computed >= MIN_COMPLETE_ORGANISMS
            and len(syn_columns) == 41
            and all(isinstance(row.get("trna_direction"), list) for row in computed)
            and all(isinstance(row.get("f3_direction"), list) for row in computed)
            and all(isinstance(row.get("usage_direction"), list) for row in computed)
        )

        checks = {
            "independent_axes_computed": {
                "passed": independent_axes_computed,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
                "axis_definitions": {
                    "d_tRNA": "dos Reis tAI direction from same-organism GtRNAdb/tRNA gene-copy records",
                    "d_f3": "fixed f3_stress direction from codon_topology q_vectors, family-projected",
                    "d_usage": "same-organism within-synonymous-family CDS usage frequency direction from cds_codon_abundance, independent of d_opt",
                },
                "three_axis_span_rank_summary": summarize_values(numeric_values(computed, "three_axis_span_rank")),
            },
            "joint_capture_below_one": {
                "passed": joint_capture_below_one,
                "mean_captured_fraction_3indep": mean_captured_3,
                "max_captured_fraction_3indep": max(captured_3) if captured_3 else None,
                "rule": "every per-organism captured_fraction_3indep and the mean must be strictly below 1; exact 1.0 is treated as a circular-axis bug",
            },
            "fourth_mechanism_verdict": {
                "passed": verdict in {"three_independent_axes_largely_sufficient", "fourth_mechanism_present"},
                "verdict": verdict,
                **verdict_summary,
            },
        }

        status = "passed" if all(bool(block["passed"]) for block in checks.values()) else "failed"
        reason = None if status == "passed" else "three independent axes were not computed cleanly or captured_fraction_3indep reached the circularity sanity bound"

        emit(
            status,
            reason=reason,
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
                    "captured_fraction_3indep": {
                        **summarize_values(captured_3),
                        "sign_test_greater_than_captured_fraction_2": paired_sign_test_greater(captured_3, captured_2),
                    },
                    "captured_fraction_2": summarize_values(captured_2),
                    "three_indep_axis_R2": {
                        **summarize_values(three_axis_r2),
                        "sign_test_greater_than_two_axis_R2": paired_sign_test_greater(three_axis_r2, two_axis_r2),
                        "pooled_positive_R2_over_self_positive_R2": pooled_positive_ratio(three_axis_r2, self_r2),
                    },
                    "two_axis_R2": {
                        **summarize_values(two_axis_r2),
                        "pooled_positive_R2_over_self_positive_R2": pooled_positive_ratio(two_axis_r2, self_r2),
                    },
                    "self_R2": summarize_values(self_r2),
                    "d_resid4_R2": {
                        **summarize_values(d_resid4_r2),
                        "sign_test_greater_than_zero": sign_test_greater(d_resid4_r2),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(d_resid4_r2),
                        "pooled_positive_R2_over_self_positive_R2": pooled_positive_ratio(d_resid4_r2, self_r2),
                    },
                    "single_axis_R2": {
                        "trna": summarize_values(trna_r2),
                        "f3": summarize_values(f3_r2),
                        "usage": summarize_values(usage_r2),
                    },
                    "usage_increment": {
                        "three_axis_minus_two_axis_R2": paired_sign_test_greater(three_axis_r2, two_axis_r2),
                        "captured_fraction_3indep_minus_2": paired_sign_test_greater(captured_3, captured_2),
                    },
                    "total_syn_selection_R2": summarize_values(total_syn_r2),
                    "two_axis_positive_R2_over_self_positive_R2": summarize_values(two_axis_ratios),
                    "three_axis_positive_R2_over_self_positive_R2": summarize_values(three_axis_ratios),
                    "d_resid4_positive_R2_over_self_positive_R2": summarize_values(resid4_ratios),
                    "d_resid4_residual_norm": summarize_values(resid4_norms),
                    "d_resid4_pairwise_alignment": d_resid4_pairwise,
                    "three_axis_independence": axis_independence_summary(computed),
                    "fourth_mechanism_verdict": verdict_summary,
                },
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "optimal_direction": "full-sample least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized; this self-optimal direction and directions derived from it are optimistic diagnostics",
                "d_tRNA": "dos Reis tAI codon weights from same-organism GtRNAdb/tRNA records, projected as synonymous contrasts, then unit-normalized",
                "d_f3": "fixed f3_stress vector from q_vectors(codons)['f3_stress'], synonymous-family projected, converted to the same contrast coordinates, then unit-normalized",
                "d_usage": "within-synonymous-family CDS codon usage frequency from cds_codon_abundance records, converted to the same contrast coordinates, then unit-normalized; never defined from d_opt or a d_opt residual",
                "two_axis_projection": "orthonormal Gram-Schmidt basis from [d_tRNA,d_f3]; captured_fraction_2 = ||Proj_span(d_opt)||^2 / ||d_opt||^2",
                "three_axis_projection": "orthonormal Gram-Schmidt basis from [d_tRNA,d_f3,d_usage]; captured_fraction_3indep = ||Proj_span(d_opt)||^2 / ||d_opt||^2",
                "d_resid4": "normalize(d_opt - Proj_span{d_tRNA,d_f3,d_usage}(d_opt)); used only as a diagnostic residual, not inserted back as a mechanism axis",
                "held_out_strength": "5-fold CV R2 for fixed one-dimensional directions or fixed span basis with fold-local slope(s), after residualizing target and synonymous contrasts against controls",
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
                "d_tRNA, d_f3, and d_usage are constructed independently of d_opt; d_resid4 is the only direction derived from the post-three-axis residual and is not used to inflate the three-axis span",
                "self_R2 uses a full-sample fitted d_opt direction and is therefore an optimistic reference rather than a fair independently pre-registered predictor",
                "observational abundance-associated optimal directions are not causal perturbation estimates",
                "tRNA gene copy number and dos Reis wobble penalties are proxies for supply/adaptation, not direct charged tRNA abundance",
                "captured fraction is a coefficient-space geometric diagnostic; held-out R2 can differ because synonymous contrast predictors are correlated",
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
                "independent_axes_computed": {"passed": False},
                "joint_capture_below_one": {"passed": False},
                "fourth_mechanism_verdict": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

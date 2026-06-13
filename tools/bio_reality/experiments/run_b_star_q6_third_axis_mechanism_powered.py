#!/usr/bin/env python3
"""Mechanism audit for the Route-P third synonymous-selection axis."""

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
    controls_for_counts,
    deterministic_folds,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    synonymous_contrast_columns,
    synonymous_contrast_row,
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
    fit_optimal_direction,
    gc3_contrast_direction,
    load_json,
    mean,
    median,
    sign_test_greater,
    t_test_mean_greater_zero,
    unit_vector,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import (  # noqa: E402
    orthonormal_trna_f3_basis,
    pairwise_cosine_summary,
    project_onto_basis,
    residual_after_basis,
)


EXPERIMENT_ID = "b_star_q6_third_axis_mechanism_powered"
CLAIM_ID = "h3.cross_layer_relation.third_axis_mechanism.b_star_q6_d_perp_csc_vs_gc_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
ALPHA = 0.05
EPS = 1e-12
F3_COORDINATE = "f3_stress"
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"


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


def contrast_direction_from_codon_values(values: dict[str, float], syn_columns: list[dict[str, object]]) -> list[float] | None:
    return unit_vector(
        [
            values[str(column["positive_codon"])] - values[str(column["negative_codon"])]
            for column in syn_columns
        ]
    )


def contrast_to_codon_loadings(direction: list[float], codons: list[str], fibers: dict[str, list[str]], syn_columns: list[dict[str, object]]) -> dict[str, float]:
    loadings = {codon: 0.0 for codon in codons}
    for coefficient, column in zip(direction, syn_columns):
        positive = str(column["positive_codon"])
        negative = str(column["negative_codon"])
        loadings[positive] += coefficient
        loadings[negative] -= coefficient
    return project_syn(loadings, fibers)


def direction_consensus(rows: list[dict[str, object]], direction_key: str) -> tuple[list[float] | None, dict[str, object]]:
    directions = [row.get(direction_key) for row in rows if isinstance(row.get(direction_key), list)]
    if not directions:
        return None, {"reason": f"no {direction_key} vectors"}
    anchor = [float(value) for value in directions[0]]  # type: ignore[index]
    aligned: list[list[float]] = []
    flipped = 0
    for direction_any in directions:
        direction = [float(value) for value in direction_any]  # type: ignore[union-attr]
        if cosine(direction, anchor) < 0.0:
            direction = [-value for value in direction]
            flipped += 1
        aligned.append(direction)
    width = len(aligned[0])
    average = [sum(direction[index] for direction in aligned) / len(aligned) for index in range(width)]
    unit = unit_vector(average)
    if unit is None:
        return None, {"reason": f"{direction_key} aligned mean collapsed", "n": len(aligned)}
    alignments = [cosine(direction, unit) for direction in aligned]
    return unit, {
        "n": len(aligned),
        "flipped_to_first_vector_count": flipped,
        "mean_alignment_to_consensus": mean(alignments),
        "median_alignment_to_consensus": median(alignments),
        "min_alignment_to_consensus": min(alignments),
        "max_alignment_to_consensus": max(alignments),
        "mean_norm_before_unit": vector_norm(average),
    }


def organism_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> tuple[list[list[float]], list[float], list[list[float]], float | None, dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    syn_rows: list[list[float]] = []
    y_rows: list[float] = []
    controls: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    total_gc3_count = 0
    total_sense_count = 0
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = item.get("abundance_ppm")
        cds_len_nt = item.get("cds_len_nt")
        if not isinstance(abundance, (int, float)) or isinstance(abundance, bool) or not math.isfinite(float(abundance)) or float(abundance) <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        if not isinstance(cds_len_nt, (int, float)) or isinstance(cds_len_nt, bool) or not math.isfinite(float(cds_len_nt)) or float(cds_len_nt) <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        y_rows.append(math.log10(float(abundance)))
        controls.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=float(cds_len_nt),
            )
        )
        total_sense_count += total
        total_gc3_count += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})

    gc3 = None if total_sense_count <= 0 else total_gc3_count / total_sense_count
    return syn_rows, y_rows, controls, gc3, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
    gc_direction: list[float],
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
        base["reason"] = "optimal direction collapsed after projecting out tRNA/f3 span"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    gc_projection, gc_projection_coefficients = project_onto_basis(d_perp_direction, [gc_direction])
    d_perp_gc_orth = unit_vector([d_perp_direction[index] - gc_projection[index] for index in range(len(d_perp_direction))])
    if d_perp_gc_orth is None:
        base["reason"] = "d_perp collapsed after projecting out GC3 contrast direction"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    projection, _ = project_onto_basis(optimal_direction, span_basis)
    d_perp_residual_norm = vector_norm([optimal_direction[index] - projection[index] for index in range(len(optimal_direction))])

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    d_perp_r2, d_perp_slope = cv_r2_fixed_direction(syn_residualized, y, d_perp_direction, folds)
    d_perp_gc_orth_r2, d_perp_gc_orth_slope = cv_r2_fixed_direction(syn_residualized, y, d_perp_gc_orth, folds)
    gc_r2, gc_slope = cv_r2_fixed_direction(syn_residualized, y, gc_direction, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)

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
        "d_perp_gc_orth_direction": d_perp_gc_orth,
        "captured_fraction": captured_fraction,
        "d_perp_residual_norm": d_perp_residual_norm,
        "d_perp_gc_projection_coefficient": gc_projection_coefficients[0],
        "d_perp_gc_projection_abs_coefficient": abs(gc_projection_coefficients[0]),
        "d_perp_gc_projection_energy_fraction": gc_projection_coefficients[0] * gc_projection_coefficients[0],
        "span_rank": span_summary["span_rank"],
        "span_coefficients": {
            "trna": span_coefficients[0] if len(span_coefficients) > 0 else None,
            "f3_after_trna_orthogonalization": span_coefficients[1] if len(span_coefficients) > 1 else None,
        },
        "cos_d_perp_gc3": cosine(d_perp_direction, gc_direction),
        "cos_d_perp_gc_orth_gc3": cosine(d_perp_gc_orth, gc_direction),
        "cos_d_perp_gc_orth_trna": cosine(d_perp_gc_orth, trna_direction),
        "cos_d_perp_gc_orth_f3": cosine(d_perp_gc_orth, f3_direction),
        "d_perp_held_out_r2": d_perp_r2,
        "d_perp_slope": d_perp_slope,
        "d_perp_gc_orth_held_out_r2": d_perp_gc_orth_r2,
        "d_perp_gc_orth_slope": d_perp_gc_orth_slope,
        "gc3_held_out_r2": gc_r2,
        "gc3_slope": gc_slope,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "span_summary": span_summary,
        "residual_synonymous_columns": len(syn_columns),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
        "trna_source_summary": trna_source_summary,
        "tai_weight_summary": {
            **tai_summary,
            "raw_w_min": min(raw_w.values()) if raw_w else None,
            "raw_w_max": max(raw_w.values()) if raw_w else None,
        },
    }


def wobble_decoding_class(codon: str) -> str:
    third = codon[2]
    if third in {"C", "U"}:
        return "pyrimidine_wobble_pair_NNY"
    if third in {"A", "G"}:
        return "purine_wobble_pair_NNR"
    return "unknown"


def standard_wobble_proxy_class(codon: str) -> str:
    third = codon[2]
    if third in {"C", "G"}:
        return "canonical_watson_crick_third_base_CG"
    if third in {"U", "A"}:
        return "standard_wobble_accessible_third_base_UA"
    return "unknown"


def codon_class_rows(codons: list[str], code: dict[str, str], fibers: dict[str, list[str]], loadings: dict[str, float]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for codon in codons:
        family = fibers[code[codon]]
        size = len(family)
        row = {
            "codon": codon,
            "amino_acid": code[codon],
            "family_size": size,
            "third_base": codon[2],
            "third_is_gc": codon[2] in {"G", "C"},
            "d_perp_consensus_loading": loadings[codon],
            "standard_wobble_pair_class": wobble_decoding_class(codon),
            "fourfold_NNU_NNC_vs_NNA_NNG": None,
            "two_codon_U_vs_C": None,
            "watson_crick_vs_wobble_accessible_proxy": standard_wobble_proxy_class(codon),
        }
        if size == 4 and {member[2] for member in family} == {"U", "C", "A", "G"}:
            row["fourfold_NNU_NNC_vs_NNA_NNG"] = "NNU_NNC" if codon[2] in {"U", "C"} else "NNA_NNG"
        if size == 2 and {member[2] for member in family} == {"U", "C"}:
            row["two_codon_U_vs_C"] = "NNU" if codon[2] == "U" else "NNC"
        rows.append(row)
    return rows


def group_values(rows: list[dict[str, object]], field: str, label: str) -> list[float]:
    return [
        float(row["d_perp_consensus_loading"])
        for row in rows
        if row.get(field) == label and isinstance(row.get("d_perp_consensus_loading"), (int, float))
    ]


def two_group_difference(rows: list[dict[str, object]], field: str, left_label: str, right_label: str) -> dict[str, object]:
    left = group_values(rows, field, left_label)
    right = group_values(rows, field, right_label)
    diffs = []
    right_sorted = sorted(
        [
            row
            for row in rows
            if row.get(field) == right_label and isinstance(row.get("d_perp_consensus_loading"), (int, float))
        ],
        key=lambda row: (str(row["amino_acid"]), str(row["codon"])),
    )
    left_sorted = sorted(
        [
            row
            for row in rows
            if row.get(field) == left_label and isinstance(row.get("d_perp_consensus_loading"), (int, float))
        ],
        key=lambda row: (str(row["amino_acid"]), str(row["codon"])),
    )
    for left_row, right_row in zip(left_sorted, right_sorted):
        if left_row["amino_acid"] == right_row["amino_acid"]:
            diffs.append(float(left_row["d_perp_consensus_loading"]) - float(right_row["d_perp_consensus_loading"]))
    mean_left = mean(left)
    mean_right = mean(right)
    delta = None if mean_left is None or mean_right is None else mean_left - mean_right
    return {
        "field": field,
        "left_label": left_label,
        "right_label": right_label,
        "n_left": len(left),
        "n_right": len(right),
        "mean_left": mean_left,
        "mean_right": mean_right,
        "mean_delta_left_minus_right": delta,
        "absolute_mean_delta": None if delta is None else abs(delta),
        "paired_within_amino_acid_deltas": summarize_values(diffs),
        "paired_sign_test_left_greater_right": sign_test_greater(diffs),
        "paired_sign_test_right_greater_left": sign_test_greater([-value for value in diffs]),
        "paired_mean_test_left_greater_right_normal_approx": t_test_mean_greater_zero(diffs),
        "paired_mean_test_right_greater_left_normal_approx": t_test_mean_greater_zero([-value for value in diffs]),
    }


def third_base_summary(rows: list[dict[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for base in ["U", "C", "A", "G"]:
        values = group_values(rows, "third_base", base)
        result[base] = summarize_values(values)
    return result


def wobble_cluster_test(loadings: dict[str, float], codons: list[str], code: dict[str, str], fibers: dict[str, list[str]]) -> dict[str, object]:
    rows = codon_class_rows(codons, code, fibers, loadings)
    tests = {
        "watson_crick_vs_wobble_accessible_proxy": two_group_difference(
            rows,
            "watson_crick_vs_wobble_accessible_proxy",
            "canonical_watson_crick_third_base_CG",
            "standard_wobble_accessible_third_base_UA",
        ),
        "fourfold_NNU_NNC_vs_NNA_NNG": two_group_difference(
            rows,
            "fourfold_NNU_NNC_vs_NNA_NNG",
            "NNU_NNC",
            "NNA_NNG",
        ),
        "two_codon_U_vs_C": two_group_difference(
            rows,
            "two_codon_U_vs_C",
            "NNU",
            "NNC",
        ),
    }
    significant = []
    for name, block in tests.items():
        sign = block.get("paired_sign_test_left_greater_right")
        p_value = sign.get("p_greater") if isinstance(sign, dict) else None
        reverse_sign = block.get("paired_sign_test_right_greater_left")
        reverse_p = reverse_sign.get("p_greater") if isinstance(reverse_sign, dict) else None
        if isinstance(p_value, (int, float)) and p_value <= ALPHA:
            significant.append({"test": name, "direction": f"{block['left_label']}>{block['right_label']}", "p_greater": p_value})
        if isinstance(reverse_p, (int, float)) and reverse_p <= ALPHA:
            significant.append({"test": name, "direction": f"{block['right_label']}>{block['left_label']}", "p_greater": reverse_p})
    return {
        "definition": "wobble classes from standard code family structure and standard C/U, A/G wobble pair partitions; no organism-specific modified-tRNA chemistry is assumed",
        "per_codon": rows,
        "third_base_loading_summary": third_base_summary(rows),
        "tests": tests,
        "significant_left_greater_tests_alpha_0_05": significant,
    }


def compact_organism_row(row: dict[str, object]) -> dict[str, object]:
    return {
        "organism": row["organism"],
        "domain": row["domain"],
        "n_join": row["n_join"],
        "gc3": row["gc3"],
        "captured_fraction": row["captured_fraction"],
        "d_perp_R2": row["d_perp_held_out_r2"],
        "d_perp_gc_orth_R2": row["d_perp_gc_orth_held_out_r2"],
        "gc3_R2": row["gc3_held_out_r2"],
        "self_R2": row["self_direction_held_out_r2"],
        "cos_d_perp_gc3": row["cos_d_perp_gc3"],
        "d_perp_gc_projection_energy_fraction": row["d_perp_gc_projection_energy_fraction"],
        "cos_d_perp_gc_orth_gc3": row["cos_d_perp_gc_orth_gc3"],
        "data_summary": row["data_summary"],
        "trna_source_summary": row["trna_source_summary"],
        "tai_weight_summary": row["tai_weight_summary"],
    }


def gate_from_alignment_and_r2(pairwise_summary: dict[str, object], r2_values: list[float]) -> tuple[bool, dict[str, object]]:
    pairwise_sign = pairwise_summary.get("pairwise_cosine_sign_test_greater")
    pairwise_p = pairwise_sign.get("p_greater") if isinstance(pairwise_sign, dict) else None
    pairwise_mean = pairwise_summary.get("mean_pairwise_cosine")
    r2_sign = sign_test_greater(r2_values)
    r2_p = r2_sign.get("p_greater")
    r2_mean = mean(r2_values)
    survived = (
        isinstance(pairwise_p, (int, float))
        and pairwise_p <= ALPHA
        and isinstance(pairwise_mean, (int, float))
        and float(pairwise_mean) > 0.0
        and isinstance(r2_p, (int, float))
        and r2_p <= ALPHA
        and isinstance(r2_mean, (int, float))
        and float(r2_mean) > 0.0
    )
    return survived, {
        "alignment_alpha": ALPHA,
        "r2_alpha": ALPHA,
        "pairwise_mean_positive": pairwise_mean,
        "pairwise_sign_test_p_greater": pairwise_p,
        "r2_mean_positive": r2_mean,
        "r2_sign_test_p_greater": r2_p,
        "requires": "mean pairwise cosine > 0 with one-sided sign-test p<=0.05, and mean held-out R2 > 0 with one-sided sign-test p<=0.05",
    }


def conclusion_text(gc_survived: bool, wobble_result: dict[str, object]) -> str:
    tests = wobble_result.get("tests")
    wobble_hits = 0
    if isinstance(tests, dict):
        for block in tests.values():
            if not isinstance(block, dict):
                continue
            sign = block.get("paired_sign_test_left_greater_right")
            p_value = sign.get("p_greater") if isinstance(sign, dict) else None
            delta = block.get("absolute_mean_delta")
            if isinstance(p_value, (int, float)) and p_value <= ALPHA and isinstance(delta, (int, float)) and delta > EPS:
                wobble_hits += 1
    gc_part = "selection-not-GC" if gc_survived else "GC-null-not-defeated"
    wobble_part = "wobble-clustered" if wobble_hits >= 2 else ("partially-wobble-clustered" if wobble_hits == 1 else "not-wobble-clustered")
    return f"{gc_part}; {wobble_part}; CSC/positional identity needs_external"


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
        if gc_direction is None or f3_direction is None or len(syn_columns) != 41:
            emit(
                "failed",
                reason="could not construct GC3 or f3 fixed synonymous contrast directions",
                seed=SEED,
                fold_count=FOLD_COUNT,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "d_perp_computed": {"passed": False},
                    "gc_null_test": {"passed": False},
                    "wobble_class_test": {"passed": False},
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
                gc_direction=gc_direction,
                f3_direction=f3_direction,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        if len(computed) < MIN_COMPLETE_ORGANISMS:
            emit(
                "needs_data",
                reason="complete proteomics/cds_codon_abundance/tRNA organism intersection below gate",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=len(computed),
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                checks={
                    "d_perp_computed": {"passed": False, "organisms_computed": len(computed), "minimum": MIN_COMPLETE_ORGANISMS},
                    "gc_null_test": {"passed": False},
                    "wobble_class_test": {"passed": False},
                },
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            )

        d_perp_pairwise = pairwise_cosine_summary(computed, "d_perp_direction")
        gc_orth_pairwise = pairwise_cosine_summary(computed, "d_perp_gc_orth_direction")
        d_perp_r2_values = [float(row["d_perp_held_out_r2"]) for row in computed]
        gc_orth_r2_values = [float(row["d_perp_gc_orth_held_out_r2"]) for row in computed]
        gc_r2_values = [float(row["gc3_held_out_r2"]) for row in computed]
        gc_projection_energy = [float(row["d_perp_gc_projection_energy_fraction"]) for row in computed]

        gc_survived, gc_gate = gate_from_alignment_and_r2(gc_orth_pairwise, gc_orth_r2_values)
        d_perp_consensus, d_perp_consensus_summary = direction_consensus(computed, "d_perp_direction")
        gc_orth_consensus, gc_orth_consensus_summary = direction_consensus(computed, "d_perp_gc_orth_direction")
        if d_perp_consensus is None or gc_orth_consensus is None:
            emit(
                "failed",
                reason="could not construct consensus d_perp directions",
                seed=SEED,
                fold_count=FOLD_COUNT,
                checks={
                    "d_perp_computed": {"passed": False},
                    "gc_null_test": {"passed": gc_survived},
                    "wobble_class_test": {"passed": False},
                },
            )

        d_perp_loadings = contrast_to_codon_loadings(d_perp_consensus, codons, fibers, syn_columns)
        gc_orth_loadings = contrast_to_codon_loadings(gc_orth_consensus, codons, fibers, syn_columns)
        wobble_result = wobble_cluster_test(d_perp_loadings, codons, code, fibers)
        wobble_gc_orth_result = wobble_cluster_test(gc_orth_loadings, codons, code, fibers)
        conclusion = conclusion_text(gc_survived, wobble_result)

        checks = {
            "d_perp_computed": {
                "passed": len(computed) >= MIN_COMPLETE_ORGANISMS and all(isinstance(row.get("d_perp_direction"), list) for row in computed),
                "organisms_computed": len(computed),
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
            },
            "gc_null_test": {
                "passed": True,
                "gc_null_defeated": gc_survived,
                "gate": gc_gate,
            },
            "wobble_class_test": {
                "passed": True,
                "tests_run": list(wobble_result["tests"].keys()),
            },
        }
        status = "passed" if all(bool(block["passed"]) for block in checks.values()) else "failed"
        reason = (
            "GC-orthogonalized d_perp keeps significant cross-species alignment and held-out R2"
            if gc_survived
            else "GC-orthogonalized d_perp does not clear both alignment and held-out R2 gates"
        )
        emit(
            status,
            reason=reason,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=len(computed),
            synonymous_design_columns=len(syn_columns),
            conclusion=conclusion,
            payload={
                "per_organism": [compact_organism_row(row) for row in computed],
                "cross_species": {
                    "d_perp_pairwise_alignment": d_perp_pairwise,
                    "gc_orthogonalized_d_perp_pairwise_alignment": gc_orth_pairwise,
                    "gc_null_gate": gc_gate,
                    "d_perp_R2": {
                        **summarize_values(d_perp_r2_values),
                        "sign_test_greater_than_zero": sign_test_greater(d_perp_r2_values),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(d_perp_r2_values),
                    },
                    "gc_orthogonalized_d_perp_R2": {
                        **summarize_values(gc_orth_r2_values),
                        "sign_test_greater_than_zero": sign_test_greater(gc_orth_r2_values),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(gc_orth_r2_values),
                    },
                    "gc3_R2": {
                        **summarize_values(gc_r2_values),
                        "sign_test_greater_than_zero": sign_test_greater(gc_r2_values),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(gc_r2_values),
                    },
                    "d_perp_projection_onto_gc3_energy_fraction": summarize_values(gc_projection_energy),
                    "d_perp_consensus": d_perp_consensus_summary,
                    "gc_orthogonalized_d_perp_consensus": gc_orth_consensus_summary,
                },
                "wobble_class": wobble_result,
                "wobble_class_after_gc_orthogonalization": wobble_gc_orth_result,
                "needs_external_prongs": {
                    "csc_vector_alignment": {
                        "status": "needs_external",
                        "reason": "repo snapshot does not contain published organism-matched CSC codon-stability coefficient vectors for the proteomics intersection",
                        "required_data": "per-organism CSC-like codon/mRNA stability vectors or mRNA half-life models mapped to the same standard-code synonymous families",
                    },
                    "positional_5prime_vs_3prime_localization": {
                        "status": "needs_external",
                        "reason": "core proteomics intersection is built from aggregate CDS codon counts; available position-level files are not organism-complete for this cross-species d_perp test",
                        "required_data": "position-resolved CDS codon profiles for each computed organism, ideally matched to abundance/mRNA-stability targets",
                    },
                },
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "d_perp": "Route P construction: normalize(d_opt - Proj_span{d_tRNA,d_f3}(d_opt)) with d_opt from residualized full-sample least-squares, d_tRNA from GtRNAdb/dos Reis tAI, and d_f3 from q_vectors(codons)['f3_stress']",
                "gc_null": "normalize(d_perp - Proj_{d_GC3}(d_perp)); survival requires positive pairwise cross-organism cosine sign-test and positive 5-fold held-out R2 sign-test",
                "wobble_classification": "standard-code synonymous family partitions: C/G as Watson-Crick third-base proxy vs U/A wobble-accessible proxy; fourfold NNU/NNC vs NNA/NNG; two-codon U vs C",
                "held_out_strength": "5-fold CV R2 for fixed one-dimensional directions with fold-local slope after residualizing target and synonymous contrasts against amino-acid composition, length, and other sibling controls",
            },
            checks=checks,
            organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            caveats=[
                "GC-null defeat here means d_perp is not explained by the single GC3 synonymous contrast direction; it is not a full mutational-spectrum model",
                "wobble classes use standard genetic-code family structure and simple wobble proxies, not organism-specific tRNA modification maps",
                "CSC-like identity and positional localization are explicitly marked needs_external rather than inferred from aggregate codon counts",
                "observational abundance-associated optimal directions are not causal perturbation estimates",
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
                "d_perp_computed": {"passed": False},
                "gc_null_test": {"passed": False},
                "wobble_class_test": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

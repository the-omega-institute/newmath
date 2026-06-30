#!/usr/bin/env python3
"""Characterize the Route-P third universal synonymous-selection axis."""

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
    cv_r2_multivariate,
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
    fixed_basis_cv_r2,
    orthonormal_trna_f3_basis,
    pairwise_cosine_summary,
    project_onto_basis,
    residual_after_basis,
)


EXPERIMENT_ID = "b_star_q6_third_axis_identity_powered"
CLAIM_ID = "h3.cross_layer_relation.third_axis_identity.b_star_q6_d_perp_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
MIN_AXIS_MEAN_COSINE = 0.12
ALPHA = 0.05
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"
EPS = 1e-12
F3_COORDINATE = "f3_stress"
BC5_EXPORT_PATH = pathlib.Path("/tmp/routeq-exp/out/codon_q6_selection_vectors.json")


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


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 3:
        return None
    left_mean = sum(left) / len(left)
    right_mean = sum(right) / len(right)
    left_centered = [value - left_mean for value in left]
    right_centered = [value - right_mean for value in right]
    denom = vector_norm(left_centered) * vector_norm(right_centered)
    if denom <= EPS:
        return None
    return vector_dot(left_centered, right_centered) / denom


def paired_sign_test_greater(left: list[float], right: list[float]) -> dict[str, object]:
    deltas = [left[index] - right[index] for index in range(min(len(left), len(right)))]
    return {**sign_test_greater(deltas), "mean_delta": mean(deltas), "median_delta": median(deltas)}


def contrast_direction_from_codon_values(values: dict[str, float], syn_columns: list[dict[str, object]]) -> list[float] | None:
    direction = [
        values[str(column["positive_codon"])] - values[str(column["negative_codon"])]
        for column in syn_columns
    ]
    return unit_vector(direction)


def contrast_to_codon_loadings(direction: list[float], codons: list[str], fibers: dict[str, list[str]], syn_columns: list[dict[str, object]]) -> dict[str, float]:
    loadings = {codon: 0.0 for codon in codons}
    for coefficient, column in zip(direction, syn_columns):
        positive = str(column["positive_codon"])
        negative = str(column["negative_codon"])
        loadings[positive] += coefficient
        loadings[negative] -= coefficient
    return project_syn(loadings, fibers)


def codon_values_to_centered_loadings(values: dict[str, float], codons: list[str], fibers: dict[str, list[str]]) -> dict[str, float]:
    complete = {codon: float(values.get(codon, 0.0)) for codon in codons}
    return project_syn(complete, fibers)


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
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            continue
        row_counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(row_counts.values())
        if total <= 0:
            continue
        records_used += 1
        for codon in codons:
            counts[codon] += row_counts[codon]
    family_frequencies: dict[str, float] = {}
    for _aa, family in fibers.items():
        total = sum(counts[codon] for codon in family)
        if total <= 0:
            for codon in family:
                family_frequencies[codon] = 0.0
            continue
        for codon in family:
            family_frequencies[codon] = counts[codon] / total
    direction = contrast_direction_from_codon_values(family_frequencies, syn_columns)
    return direction, {
        "records_used": records_used,
        "total_sense_codons": sum(counts.values()),
        "zero_count_families": sum(1 for family in fibers.values() if sum(counts[codon] for codon in family) <= 0),
        "definition": "within-synonymous-family genome/proteome CDS codon usage frequency; higher value means more frequently used codon in that organism payload",
    }


def position_base_axes(codons: list[str], syn_columns: list[dict[str, object]]) -> dict[str, list[float]]:
    axes: dict[str, list[float]] = {}
    bases = ["U", "C", "A", "G"]
    for position in [0, 1, 2]:
        for base in bases:
            values = {codon: 1.0 if codon[position] == base else 0.0 for codon in codons}
            direction = contrast_direction_from_codon_values(values, syn_columns)
            if direction is not None:
                axes[f"pos{position + 1}_{base}"] = direction
        for name, predicate in [
            ("GC", lambda c, p=position: c[p] in {"G", "C"}),
            ("purine", lambda c, p=position: c[p] in {"A", "G"}),
            ("amino", lambda c, p=position: c[p] in {"A", "C"}),
        ]:
            values = {codon: 1.0 if predicate(codon) else 0.0 for codon in codons}
            direction = contrast_direction_from_codon_values(values, syn_columns)
            if direction is not None:
                axes[f"pos{position + 1}_{name}"] = direction
    return axes


def q_vector_axes(codons: list[str], fibers: dict[str, list[str]], syn_columns: list[dict[str, object]]) -> dict[str, list[float]]:
    axes: dict[str, list[float]] = {}
    for name, vector in q_vectors(codons).items():
        projected = project_syn(vector, fibers)
        direction = contrast_direction_from_codon_values(projected, syn_columns)
        if direction is not None:
            axes[f"q_{name}"] = direction
    return axes


def reference_axes(codons: list[str], fibers: dict[str, list[str]], syn_columns: list[dict[str, object]], gc_direction: list[float], f3_direction: list[float]) -> dict[str, list[float]]:
    axes = {
        "gc3": gc_direction,
        "f3_stress": f3_direction,
    }
    axes.update(position_base_axes(codons, syn_columns))
    axes.update(q_vector_axes(codons, fibers, syn_columns))
    return axes


def axis_summary(rows: list[dict[str, object]], axis_name: str) -> dict[str, object]:
    cos_values = [float(row["candidate_axes"][axis_name]["cos_d_perp_axis"]) for row in rows if axis_name in row["candidate_axes"]]
    abs_cos_values = [abs(value) for value in cos_values]
    r2_values = [float(row["candidate_axes"][axis_name]["held_out_r2"]) for row in rows if axis_name in row["candidate_axes"]]
    slopes = [float(row["candidate_axes"][axis_name]["slope"]) for row in rows if axis_name in row["candidate_axes"]]
    signed_r2 = [r2_values[index] if slopes[index] >= 0.0 else -r2_values[index] for index in range(len(r2_values))]
    return {
        "axis": axis_name,
        "cos_d_perp_axis": {
            **summarize_values(cos_values),
            "sign_test_greater_than_zero": sign_test_greater(cos_values),
            "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(cos_values),
        },
        "abs_cos_d_perp_axis": summarize_values(abs_cos_values),
        "held_out_R2": {
            **summarize_values(r2_values),
            "sign_test_greater_than_zero": sign_test_greater(r2_values),
            "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(r2_values),
        },
        "slope": summarize_values(slopes),
        "signed_R2_by_slope": summarize_values(signed_r2),
    }


def best_axis_verdict(axis_summaries: dict[str, dict[str, object]]) -> tuple[str, dict[str, object]]:
    eligible = []
    for name, summary in axis_summaries.items():
        cos_block = summary["cos_d_perp_axis"]
        sign = cos_block["sign_test_greater_than_zero"]
        mean_cos = cos_block["mean"]
        p_sign = sign["p_greater"] if isinstance(sign, dict) else None
        if isinstance(mean_cos, (int, float)) and isinstance(p_sign, (int, float)):
            eligible.append((float(mean_cos), float(p_sign), name, summary))
    eligible.sort(key=lambda item: (-item[0], item[1], item[2]))
    if not eligible:
        return "unresolved", {"reason": "no candidate axis had usable d_perp cosine statistics"}
    top_mean, top_p, top_name, top_summary = eligible[0]
    if top_mean >= MIN_AXIS_MEAN_COSINE and top_p <= ALPHA:
        return f"aligned_to_{top_name}", {
            "reason": f"d_perp is provisionally identified with candidate axis {top_name}: mean cosine {top_mean:.3g}, one-sided sign-test p {top_p:.3g}",
            "top_axis": top_name,
            "top_axis_summary": top_summary,
            "gate": {"min_mean_cosine": MIN_AXIS_MEAN_COSINE, "alpha": ALPHA},
        }
    tested = [name for _mean, _p, name, _summary in eligible]
    return "unresolved", {
        "reason": "d_perp did not show a systemically positive, gate-passing cosine against any tested fixed reference axis",
        "top_axis": top_name,
        "top_axis_mean_cosine": top_mean,
        "top_axis_sign_test_p": top_p,
        "excluded_axes": tested,
        "gate": {"min_mean_cosine": MIN_AXIS_MEAN_COSINE, "alpha": ALPHA},
    }


def direction_consensus(rows: list[dict[str, object]], direction_key: str, anchor_key: str | None = None) -> tuple[list[float] | None, dict[str, object]]:
    directions = [row.get(direction_key) for row in rows if isinstance(row.get(direction_key), list)]
    if not directions:
        return None, {"reason": f"no {direction_key} vectors"}
    anchor = directions[0]
    if anchor_key is not None:
        anchored = direction_consensus(rows, anchor_key)[0]
        if anchored is not None:
            anchor = anchored
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
        "flipped_to_anchor_count": flipped,
        "mean_alignment_to_consensus": mean(alignments),
        "median_alignment_to_consensus": median(alignments),
        "min_alignment_to_consensus": min(alignments),
        "max_alignment_to_consensus": max(alignments),
        "mean_norm_before_unit": vector_norm(average),
        "anchor": "first_vector" if anchor_key is None else f"consensus({anchor_key})",
    }


def compact_axis_rows(row: dict[str, object]) -> dict[str, object]:
    axes = row["candidate_axes"]
    keep = sorted(axes, key=lambda name: abs(float(axes[name]["cos_d_perp_axis"])), reverse=True)[:10]
    return {
        "organism": row["organism"],
        "domain": row["domain"],
        "n_join": row["n_join"],
        "gc3": row["gc3"],
        "captured_fraction": row["captured_fraction"],
        "d_perp_held_out_R2": row["d_perp_held_out_r2"],
        "self_direction_held_out_R2": row["self_direction_held_out_r2"],
        "two_axis_held_out_R2": row["two_axis_held_out_r2"],
        "top_candidate_axes_by_abs_cos": {name: axes[name] for name in keep},
        "usage_axis_summary": row.get("usage_axis_summary"),
        "data_summary": row["data_summary"],
        "trna_source_summary": row["trna_source_summary"],
        "tai_weight_summary": row["tai_weight_summary"],
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
    fixed_axes: dict[str, list[float]],
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
    projection, _ = project_onto_basis(optimal_direction, span_basis)
    d_perp_residual_norm = vector_norm([optimal_direction[index] - projection[index] for index in range(len(optimal_direction))])

    usage_axis, usage_summary = usage_frequency_axis(
        payload=payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    organism_axes = dict(fixed_axes)
    if usage_axis is not None:
        organism_axes["usage_frequency_within_family"] = usage_axis

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)
    trna_r2, trna_slope = cv_r2_fixed_direction(syn_residualized, y, trna_direction, folds)
    two_axis_r2, two_axis_slopes, two_axis_cv_summary = fixed_basis_cv_r2(syn_residualized, y, span_basis, folds)
    d_perp_r2, d_perp_slope = cv_r2_fixed_direction(syn_residualized, y, d_perp_direction, folds)

    candidate_axis_results: dict[str, dict[str, object]] = {}
    for axis_name, axis_direction in sorted(organism_axes.items()):
        axis_r2, axis_slope = cv_r2_fixed_direction(syn_residualized, y, axis_direction, folds)
        candidate_axis_results[axis_name] = {
            "cos_d_perp_axis": cosine(d_perp_direction, axis_direction),
            "abs_cos_d_perp_axis": abs(cosine(d_perp_direction, axis_direction)),
            "cos_optimal_axis": cosine(optimal_direction, axis_direction),
            "held_out_r2": axis_r2,
            "slope": axis_slope,
        }

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
        "cos_d_perp_trna": cosine(d_perp_direction, trna_direction),
        "cos_d_perp_f3": cosine(d_perp_direction, f3_direction),
        "total_syn_selection_held_out_r2": total_syn_selection,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "trna_alone_held_out_r2": trna_r2,
        "trna_alone_slope": trna_slope,
        "two_axis_held_out_r2": two_axis_r2,
        "two_axis_slopes": two_axis_slopes,
        "d_perp_held_out_r2": d_perp_r2,
        "d_perp_slope": d_perp_slope,
        "candidate_axes": candidate_axis_results,
        "usage_axis_summary": usage_summary,
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
            "raw_w_min": min(raw_w.values()) if raw_w else None,
            "raw_w_max": max(raw_w.values()) if raw_w else None,
        },
        "tai_weights": weights,
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


def load_codon_topology_refs(repo: pathlib.Path):
    data_dir = repo / "tools/bio_reality/data"
    if str(data_dir) not in sys.path:
        sys.path.insert(0, str(data_dir))
    import codon_topology_refs  # type: ignore  # noqa: PLC0415

    return codon_topology_refs


def build_bc5_export(
    *,
    repo: pathlib.Path,
    rows: list[dict[str, object]],
    codons: list[str],
    code: dict[str, str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
) -> dict[str, object]:
    refs = load_codon_topology_refs(repo)
    refs_data = refs.load_code_data()
    refs.validate_code_data(refs_data)
    codon_order_64 = list(refs_data["codon_order"])
    sense_codons = [codon for codon in codon_order_64 if code.get(codon) and code[codon] != "*"]
    d_perp_consensus, d_perp_consensus_summary = direction_consensus(rows, "d_perp_direction")
    optimal_consensus, optimal_consensus_summary = direction_consensus(rows, "optimal_direction")
    trna_consensus, trna_consensus_summary = direction_consensus(rows, "trna_direction")
    if d_perp_consensus is None or optimal_consensus is None or trna_consensus is None:
        raise ValueError("could not construct BC5 consensus directions")

    d_perp_loadings = contrast_to_codon_loadings(d_perp_consensus, codons, fibers, syn_columns)
    optimal_loadings = contrast_to_codon_loadings(optimal_consensus, codons, fibers, syn_columns)
    f3_loadings = contrast_to_codon_loadings(f3_direction, codons, fibers, syn_columns)
    trna_loadings = contrast_to_codon_loadings(trna_consensus, codons, fibers, syn_columns)

    all_tai_weights = []
    for row in rows:
        weights = row.get("tai_weights")
        if isinstance(weights, dict):
            all_tai_weights.append({codon: float(weights[codon]) for codon in codons if codon in weights})
    mean_tai = {
        codon: (sum(weights[codon] for weights in all_tai_weights if codon in weights) / sum(1 for weights in all_tai_weights if codon in weights))
        for codon in codons
    }
    mean_tai_centered = codon_values_to_centered_loadings(mean_tai, codons, fibers)
    tai_vs_consensus_loading = pearson([mean_tai_centered[codon] for codon in codons], [trna_loadings[codon] for codon in codons])

    per_codon = []
    for codon in codon_order_64:
        entry: dict[str, object] = {
            "codon": codon,
            "q6_bits": list(refs.codon_to_q6(codon)),
            "q6_label": "".join(str(bit) for bit in refs.codon_to_q6(codon)),
            "amino_acid": code.get(codon),
            "is_sense": bool(code.get(codon) and code[codon] != "*"),
            "d_perp_loading": None,
            "trna_supply_tai_mean": None,
            "trna_supply_tai_centered_loading": None,
            "trna_consensus_loading": None,
            "f3_loading": None,
            "optimal_loading": None,
        }
        if codon in codons:
            entry.update(
                {
                    "d_perp_loading": d_perp_loadings[codon],
                    "trna_supply_tai_mean": mean_tai[codon],
                    "trna_supply_tai_centered_loading": mean_tai_centered[codon],
                    "trna_consensus_loading": trna_loadings[codon],
                    "f3_loading": f3_loadings[codon],
                    "optimal_loading": optimal_loadings[codon],
                }
            )
        per_codon.append(entry)

    export = {
        "schema": "codon_q6_selection_vectors.v1",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "seed": SEED,
        "codon_q6_source": {
            "module": "tools/bio_reality/data/codon_topology_refs.py",
            "function": "codon_to_q6",
            "base_to_bits": {base: list(bits) for base, bits in refs.BASE_TO_BITS.items()},
            "codon_order_source": "tools/bio_reality/data/ncbi_genetic_codes.json::codon_order via codon_topology_refs.load_code_data()",
            "codon_order_64": codon_order_64,
            "sense_codon_order": sense_codons,
        },
        "direction_space": {
            "description": "41-dimensional synonymous contrast space; columns use one positive codon against the lexicographically last reference codon within each synonymous family.",
            "synonymous_contrast_columns": syn_columns,
            "per_codon_loading_mapping": "For a contrast coefficient, positive_codon receives +coefficient and negative/reference codon receives -coefficient; resulting 64-codon vectors are centered within synonymous families.",
            "consensus_direction": "unit-normalized cross-organism mean of unit directions after sign alignment to the first computed organism vector",
        },
        "organisms": [row["organism"] for row in rows],
        "consensus_summaries": {
            "d_perp": d_perp_consensus_summary,
            "optimal": optimal_consensus_summary,
            "trna": trna_consensus_summary,
            "tai_mean_vs_trna_consensus_loading_pearson": tai_vs_consensus_loading,
        },
        "vectors": per_codon,
    }
    BC5_EXPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    BC5_EXPORT_PATH.write_text(json.dumps(export, sort_keys=False, indent=2), encoding="utf-8")
    return export


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
                reason="could not construct fixed synonymous contrast directions",
                seed=SEED,
                fold_count=FOLD_COUNT,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "d_perp_computed": {"passed": False},
                    "candidate_axes_tested": {"passed": False},
                    "bc5_vectors_exported": {"passed": False},
                },
            )

        fixed_axes = reference_axes(codons, fibers, syn_columns, gc_direction, f3_direction)
        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                fibers=fibers,
                syn_columns=syn_columns,
                fixed_axes=fixed_axes,
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
                    "candidate_axes_tested": {"passed": False},
                    "bc5_vectors_exported": {"passed": False},
                },
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            )

        all_axis_names = sorted({axis for row in computed for axis in row["candidate_axes"]})
        axis_summaries = {axis_name: axis_summary(computed, axis_name) for axis_name in all_axis_names}
        verdict, verdict_summary = best_axis_verdict(axis_summaries)

        d_perp_r2_values = [float(row["d_perp_held_out_r2"]) for row in computed]
        self_r2_values = [float(row["self_direction_held_out_r2"]) for row in computed]
        two_axis_r2_values = [float(row["two_axis_held_out_r2"]) for row in computed]
        trna_r2_values = [float(row["trna_alone_held_out_r2"]) for row in computed]
        captured_fractions = [float(row["captured_fraction"]) for row in computed]
        d_perp_norms = [float(row["d_perp_residual_norm"]) for row in computed]
        pairwise_summary = pairwise_cosine_summary(computed, "d_perp_direction")
        bc5_export = build_bc5_export(
            repo=repo,
            rows=computed,
            codons=codons,
            code=code,
            fibers=fibers,
            syn_columns=syn_columns,
            f3_direction=f3_direction,
        )

        bc5_export_file_ok = BC5_EXPORT_PATH.exists() and BC5_EXPORT_PATH.stat().st_size > 0
        checks = {
            "d_perp_computed": {
                "passed": len(computed) >= MIN_COMPLETE_ORGANISMS and all(isinstance(row.get("d_perp_direction"), list) for row in computed),
                "organisms_computed": len(computed),
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
            },
            "candidate_axes_tested": {
                "passed": bool(axis_summaries) and "usage_frequency_within_family" in axis_summaries and any(name.startswith("q_") for name in axis_summaries),
                "axis_count": len(axis_summaries),
                "axis_names": all_axis_names,
                "identity_verdict": verdict,
            },
            "bc5_vectors_exported": {
                "passed": bc5_export_file_ok and len(bc5_export["vectors"]) == 64,
                "path": str(BC5_EXPORT_PATH),
                "vector_count": len(bc5_export["vectors"]),
            },
        }
        status = "passed" if all(block["passed"] for block in checks.values()) else "failed"
        conclusion = (
            f"d_perp identity: {verdict}; {verdict_summary['reason']}"
            if verdict != "unresolved"
            else f"d_perp identity unresolved; {verdict_summary['reason']}"
        )
        emit(
            status,
            reason=verdict_summary["reason"],
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=len(computed),
            synonymous_design_columns=len(syn_columns),
            conclusion=conclusion,
            payload={
                "per_organism": [compact_axis_rows(row) for row in computed],
                "cross_species": {
                    "identity_verdict": verdict,
                    "identity_verdict_summary": verdict_summary,
                    "candidate_axis_summaries": axis_summaries,
                    "d_perp_R2": {
                        **summarize_values(d_perp_r2_values),
                        "sign_test_greater_than_zero": sign_test_greater(d_perp_r2_values),
                        "mean_test_greater_than_zero_normal_approx": t_test_mean_greater_zero(d_perp_r2_values),
                    },
                    "self_R2": summarize_values(self_r2_values),
                    "two_axis_R2": {
                        **summarize_values(two_axis_r2_values),
                        "two_axis_greater_than_d_perp": paired_sign_test_greater(two_axis_r2_values, d_perp_r2_values),
                    },
                    "trna_R2": summarize_values(trna_r2_values),
                    "captured_fraction": summarize_values(captured_fractions),
                    "d_perp_residual_norm": summarize_values(d_perp_norms),
                    "d_perp_pairwise_alignment": pairwise_summary,
                },
                "bc5_export": bc5_export,
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "d_perp": "Route P construction: normalize(d_opt - Proj_span{d_tRNA,d_f3}(d_opt)) with d_opt from residualized full-sample least-squares, d_tRNA from GtRNAdb/dos Reis tAI, and d_f3 from q_vectors(codons)['f3_stress']",
                "candidate_axes": [
                    "organism-specific within-family codon usage frequency",
                    "fixed position 1/2/3 base, GC, purine, amino/keto composition contrasts",
                    "all nine sibling B*_Q6 q_vectors, with f3_stress retained as a control and the other eight tested as possible identities",
                ],
                "held_out_strength": "5-fold CV R2 for fixed one-dimensional candidate axes with fold-local slope after residualizing target and synonymous contrasts against controls",
                "bc5_export_path": str(BC5_EXPORT_PATH),
            },
            checks=checks,
            organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            caveats=[
                "observational abundance-associated optimal directions are not causal perturbation estimates",
                "candidate axes are fixed/reference contrasts in the same 41-dimensional synonymous contrast coordinate system; mRNA folding, GC-skew, and purine-load mechanisms require external data not present in this repository snapshot",
                "per-codon BC5 loadings are a family-centered contrast back-projection, not an independently fitted 64-parameter codon model",
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
                "candidate_axes_tested": {"passed": False},
                "bc5_vectors_exported": {"passed": False, "path": str(BC5_EXPORT_PATH)},
            },
        )


if __name__ == "__main__":
    main()

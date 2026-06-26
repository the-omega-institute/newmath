#!/usr/bin/env python3
"""Test whether Route-S abundance d_resid4 is a ribosome dwell / elongation axis."""

from __future__ import annotations

import hashlib
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

    def _tai_codon_w_values(*_args: object, **_kwargs: object) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
        raise RuntimeError("import shim only; Route N codon_w_values is used")

    tai_shim.first_two_positions_match = _tai_first_two_positions_match
    tai_shim.effective_wobble_base = _tai_effective_wobble_base
    tai_shim.wobble_penalty = _tai_wobble_penalty
    tai_shim.codon_w_values = _tai_codon_w_values
    sys.modules["_tai"] = tai_shim

import run_b_star_q6_wobble_dwell_coupling_powered as wobble_dwell  # noqa: E402
from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    F3_COORDINATE,
    controls_for_counts,
    deterministic_folds,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    cv_r2_multivariate,
    synonymous_contrast_columns,
    synonymous_contrast_row,
)
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_optimality_axis_sufficiency_powered import (  # noqa: E402
    orthonormal_basis,
    usage_frequency_axis,
)
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_third_axis_identity_powered import contrast_direction_from_codon_values  # noqa: E402
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
    fit_optimal_direction,
    load_json,
    mean,
    median,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import residual_after_basis  # noqa: E402


EXPERIMENT_ID = "b_star_q6_fourth_mechanism_elongation_dwell_powered"
CLAIM_ID = "h3.cross_layer_relation.fourth_mechanism_identity.b_star_q6_elongation_dwell_powered"

ORGANISM = "saccharomyces_cerevisiae"
REPO_ROOT = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath")
DATA_DIR = REPO_ROOT / "tools/bio_reality/data"
OCCUPANCY_PATH = DATA_DIR / "riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = DATA_DIR / "cds_ordered_sequences_saccharomyces_cerevisiae.json"
CDS_ABUNDANCE_PATH = DATA_DIR / "cds_codon_abundance_saccharomyces_cerevisiae.json"
FOLD_COUNT = 5
EPS = 1e-12
MIN_DWELL_POSITION_COUNT = 50
MIN_STRONG_ABS_COS = 0.35
MIN_PARTIAL_ABS_COS = 0.18
MIN_POSITIVE_INCREMENT = 0.0
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def finite_numeric(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def summarize_values(values: list[float]) -> dict[str, object]:
    if not values:
        return {"n": 0, "mean": None, "median": None, "min": None, "max": None, "positive_count": 0, "negative_count": 0}
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values),
        "max": max(values),
        "positive_count": sum(1 for value in values if value > EPS),
        "negative_count": sum(1 for value in values if value < -EPS),
    }


def compact_direction(direction: list[float], syn_columns: list[dict[str, object]], limit: int = 8) -> list[dict[str, object]]:
    rows = []
    for index, value in enumerate(direction):
        column = syn_columns[index]
        rows.append(
            {
                "contrast": f"{column['aa']}:{column['positive_codon']}>{column['negative_codon']}",
                "loading": value,
            }
        )
    return sorted(rows, key=lambda row: abs(float(row["loading"])), reverse=True)[:limit]


def load_dwell_direction(
    *,
    codons: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
) -> tuple[list[float] | None, dict[str, object]]:
    missing = [str(path) for path in [OCCUPANCY_PATH, ORDERED_CDS_PATH] if not path.exists()]
    if missing:
        return None, {"status": "needs_data", "reason": "missing riboseq positional occupancy or ordered CDS data", "missing": missing}
    occupancy = load_json(OCCUPANCY_PATH)
    ordered_cds = load_json(ORDERED_CDS_PATH)
    if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict):
        raise ValueError("dwell data payloads must be JSON objects")

    joined, schema = wobble_dwell.schema_and_join(occupancy, ordered_cds)
    dwell_sum = {codon: 0.0 for codon in codons}
    dwell_count = {codon: 0 for codon in codons}
    window_counts = {"5prime": 0, "3prime": 0}
    skipped = {"codon_not_standard_sense": 0, "nonfinite_occupancy": 0}
    total_rows = 0
    for gene_id, item in joined.items():
        for row in wobble_dwell.iter_gene_windows(gene_id, item):
            total_rows += 1
            value = row.get("occupancy")
            codon = row.get("codon")
            window = row.get("window")
            if not finite_numeric(value):
                skipped["nonfinite_occupancy"] += 1
                continue
            if not isinstance(codon, str):
                skipped["codon_not_standard_sense"] += 1
                continue
            rna_codon = dna_to_rna(codon)
            if rna_codon not in dwell_sum:
                skipped["codon_not_standard_sense"] += 1
                continue
            dwell_sum[rna_codon] += float(value)
            dwell_count[rna_codon] += 1
            if isinstance(window, str) and window in window_counts:
                window_counts[window] += 1

    codon_mean = {
        codon: (dwell_sum[codon] / dwell_count[codon] if dwell_count[codon] > 0 else 0.0)
        for codon in codons
    }
    observed_codons = [codon for codon in codons if dwell_count[codon] > 0]
    low_count_codons = [codon for codon in codons if 0 < dwell_count[codon] < MIN_DWELL_POSITION_COUNT]
    missing_family_codons = {
        aa: [codon for codon in sorted(family) if dwell_count.get(codon, 0) <= 0]
        for aa, family in fibers.items()
        if len(family) > 1 and any(dwell_count.get(codon, 0) <= 0 for codon in family)
    }
    projected = project_syn(codon_mean, fibers)
    direction = contrast_direction_from_codon_values(projected, syn_columns)
    if direction is None:
        return None, {
            "status": "needs_data",
            "reason": "per-codon dwell collapsed to zero in synonymous contrast space",
            "schema_and_gene_id_join": schema,
            "total_window_positions": total_rows,
            "observed_sense_codons": len(observed_codons),
        }

    count_values = list(dwell_count.values())
    mean_values = [codon_mean[codon] for codon in codons if dwell_count[codon] > 0]
    return direction, {
        "status": "computed",
        "definition": "per-codon-type mean of file-provided local relative ribosome occupancy over sibling iter_gene_windows 5prime and 3prime windows; then synonymous-family centered and encoded in the 41-column contrast basis",
        "schema_and_gene_id_join": schema,
        "total_joined_window_positions": total_rows,
        "retained_window_positions": sum(dwell_count.values()),
        "retained_window_counts": window_counts,
        "skipped": skipped,
        "observed_sense_codons": len(observed_codons),
        "sense_codons_expected": len(codons),
        "codons_below_min_position_count": low_count_codons,
        "minimum_position_count_reference": MIN_DWELL_POSITION_COUNT,
        "missing_synonymous_family_codons": missing_family_codons,
        "position_count_summary_by_codon": summarize_values([float(value) for value in count_values]),
        "mean_relative_dwell_summary_by_codon": summarize_values(mean_values),
        "codon_mean_relative_dwell": codon_mean,
        "codon_position_counts": dwell_count,
        "top_abs_loadings": compact_direction(direction, syn_columns),
    }


def abundance_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> tuple[list[list[float]], list[float], list[list[float]], dict[str, object]]:
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
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        y_rows.append(math.log10(abundance))
        controls.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=cds_len_nt,
            )
        )
    return syn_rows, y_rows, controls, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def regression_increment(
    *,
    syn_rows: list[list[float]],
    y_rows: list[float],
    controls: list[list[float]],
    three_axis_basis: list[list[float]],
    trna_direction: list[float],
    dwell_direction: list[float],
) -> dict[str, object]:
    n = len(y_rows)
    if n < MIN_PROTEINS_PER_ORGANISM:
        return {"status": "needs_data", "reason": f"abundance join below gate n={n} < {MIN_PROTEINS_PER_ORGANISM}", "n": n}
    syn_tilde, rank_controls_syn = residualize(syn_rows, controls)
    y_tilde, rank_controls_y = residualize([[value] for value in y_rows], controls)
    y = matrix_column(y_tilde, 0)
    if vector_dot(y, y) <= EPS:
        return {"status": "needs_data", "reason": "zero residual abundance energy after controls", "n": n}

    folds = deterministic_folds(n, f"{SEED}|{ORGANISM}|folds", FOLD_COUNT)
    baseline_predictors = [[vector_dot(row, direction) for direction in three_axis_basis] for row in syn_tilde]
    dwell_scores = [vector_dot(row, dwell_direction) for row in syn_tilde]
    trna_scores = [vector_dot(row, trna_direction) for row in syn_tilde]
    extended_predictors = [baseline_predictors[index] + [dwell_scores[index]] for index in range(n)]

    baseline_r2, baseline_cv = cv_r2_multivariate(baseline_predictors, y, folds)
    extended_r2, extended_cv = cv_r2_multivariate(extended_predictors, y, folds)
    dwell_only_r2, dwell_only_cv = cv_r2_multivariate([[value] for value in dwell_scores], y, folds)
    trna_plus_dwell_r2, trna_plus_dwell_cv = cv_r2_multivariate(
        [[trna_scores[index], dwell_scores[index]] for index in range(n)],
        y,
        folds,
    )
    trna_only_r2, trna_only_cv = cv_r2_multivariate([[value] for value in trna_scores], y, folds)

    return {
        "status": "computed",
        "n": n,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "baseline_three_axis_held_out_r2": baseline_r2,
        "extended_three_axis_plus_dwell_held_out_r2": extended_r2,
        "dwell_increment_over_three_axis_held_out_r2": extended_r2 - baseline_r2,
        "dwell_only_after_controls_held_out_r2": dwell_only_r2,
        "trna_only_after_controls_held_out_r2": trna_only_r2,
        "trna_plus_dwell_after_controls_held_out_r2": trna_plus_dwell_r2,
        "dwell_increment_over_tRNA_only_held_out_r2": trna_plus_dwell_r2 - trna_only_r2,
        "baseline_cv_summary": baseline_cv,
        "extended_cv_summary": extended_cv,
        "dwell_only_cv_summary": dwell_only_cv,
        "trna_only_cv_summary": trna_only_cv,
        "trna_plus_dwell_cv_summary": trna_plus_dwell_cv,
        "_syn_tilde": syn_tilde,
        "_y": y,
        "_folds": folds,
    }


def verdict(evidence: dict[str, object]) -> tuple[str, dict[str, object]]:
    if evidence.get("status") != "computed":
        return "needs_data", {"reason": "yeast dwell evidence was not computed"}
    cos_resid4 = float(evidence["abs_cos_dwell_resid4"])
    cos_usage = float(evidence["abs_cos_dwell_usage"])
    cos_trna = float(evidence["abs_cos_dwell_tRNA"])
    increment = float(evidence["dwell_increment_over_three_axis_held_out_r2"])
    partial_increment = float(evidence["dwell_increment_over_tRNA_only_held_out_r2"])
    dominant_resid4_alignment = cos_resid4 >= max(cos_usage, cos_trna) and cos_resid4 >= MIN_STRONG_ABS_COS
    partial_alignment = cos_resid4 >= MIN_PARTIAL_ABS_COS
    positive_increment = increment > MIN_POSITIVE_INCREMENT

    if dominant_resid4_alignment and positive_increment:
        return (
            "fourth_axis_is_elongation_dwell",
            {
                "reason": "yeast per-codon ribosome dwell aligns most strongly with d_resid4 and adds held-out abundance R2 beyond d_tRNA/d_f3/d_usage",
                "abs_cos_dwell_resid4": cos_resid4,
                "abs_cos_dwell_usage": cos_usage,
                "abs_cos_dwell_tRNA": cos_trna,
                "dwell_increment_over_three_axis_held_out_r2": increment,
                "dwell_increment_over_tRNA_only_held_out_r2": partial_increment,
            },
        )
    if partial_alignment or positive_increment:
        return (
            "partial",
            {
                "reason": "yeast dwell has either nontrivial d_resid4 alignment or positive held-out increment, but not the fixed joint evidence required for a clean fourth-axis dwell identity call",
                "abs_cos_dwell_resid4": cos_resid4,
                "abs_cos_dwell_usage": cos_usage,
                "abs_cos_dwell_tRNA": cos_trna,
                "dwell_increment_over_three_axis_held_out_r2": increment,
                "dwell_increment_over_tRNA_only_held_out_r2": partial_increment,
            },
        )
    return (
        "not_dwell",
        {
            "reason": "yeast per-codon ribosome dwell does not align with d_resid4 and does not add held-out abundance R2 beyond the three independent single-codon axes; under repo data this excludes dwell as the dominant fourth-axis identity",
            "abs_cos_dwell_resid4": cos_resid4,
            "abs_cos_dwell_usage": cos_usage,
            "abs_cos_dwell_tRNA": cos_trna,
            "dwell_increment_over_three_axis_held_out_r2": increment,
            "dwell_increment_over_tRNA_only_held_out_r2": partial_increment,
        },
    )


def main() -> None:
    try:
        missing = [
            str(path)
            for path in [OCCUPANCY_PATH, ORDERED_CDS_PATH, CDS_ABUNDANCE_PATH]
            if not path.exists()
        ]
        if missing:
            emit(
                "needs_data",
                reason="required yeast riboseq, ordered CDS, or abundance data are missing",
                seed=SEED,
                missing_required_data=missing,
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        code = standard_code(REPO_ROOT)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)
        f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
        if f3_direction is None or len(syn_columns) != 41:
            emit(
                "failed",
                reason="could not construct 41-column f3_stress synonymous contrast direction",
                seed=SEED,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        cds_payload = load_json(CDS_ABUNDANCE_PATH)
        if not isinstance(cds_payload, dict):
            emit(
                "needs_data",
                reason="cds_codon_abundance yeast payload is not a JSON object",
                seed=SEED,
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        trna_records, trna_summary = load_trna_records(REPO_ROOT, ORGANISM)
        weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
        trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
        if trna_direction is None:
            emit(
                "needs_data",
                reason="zero yeast tRNA contrast direction",
                seed=SEED,
                trna_source_summary=trna_summary,
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        usage_direction, usage_summary = usage_frequency_axis(
            payload=cds_payload,
            organism=ORGANISM,
            codons=codons,
            fibers=fibers,
            syn_columns=syn_columns,
        )
        if usage_direction is None:
            emit(
                "needs_data",
                reason=str(usage_summary.get("reason", "could not construct usage-frequency direction")),
                seed=SEED,
                usage_axis_summary=usage_summary,
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        three_axis_basis, three_axis_summary = orthonormal_basis(
            [("d_tRNA", trna_direction), ("d_f3", f3_direction), ("d_usage", usage_direction)]
        )
        if three_axis_basis is None:
            emit(
                "needs_data",
                reason="could not construct Route-S three-axis basis",
                seed=SEED,
                three_axis_basis_summary=three_axis_summary,
                checks={
                    "dwell_vector_computed": {"passed": False},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        dwell_direction, dwell_summary = load_dwell_direction(codons=codons, fibers=fibers, syn_columns=syn_columns)
        if dwell_direction is None:
            emit(
                "needs_data",
                reason=str(dwell_summary.get("reason", "could not construct dwell direction")),
                seed=SEED,
                fold_count=FOLD_COUNT,
                dwell_summary=dwell_summary,
                checks={
                    "dwell_vector_computed": {"passed": False, **dwell_summary},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        syn_rows, y_rows, controls, abundance_summary = abundance_rows(
            payload=cds_payload,
            organism=ORGANISM,
            codons=codons,
            code=code,
            aa_order=aa_order,
            syn_columns=syn_columns,
        )
        syn_tilde, rank_controls_syn_for_opt = residualize(syn_rows, controls)
        y_tilde, rank_controls_y_for_opt = residualize([[value] for value in y_rows], controls)
        y = matrix_column(y_tilde, 0)
        if vector_dot(y, y) <= EPS:
            emit(
                "needs_data",
                reason="zero residual abundance energy after controls",
                seed=SEED,
                abundance_summary=abundance_summary,
                checks={
                    "dwell_vector_computed": {"passed": True},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )
        d_opt, fit_summary = fit_optimal_direction(syn_tilde, y)
        if d_opt is None:
            emit(
                "needs_data",
                reason=str(fit_summary.get("reason", "could not fit abundance d_opt")),
                seed=SEED,
                abundance_summary=abundance_summary,
                fit_summary=fit_summary,
                checks={
                    "dwell_vector_computed": {"passed": True},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        d_resid4, captured_fraction_3indep, projection_coefficients = residual_after_basis(d_opt, three_axis_basis)
        if d_resid4 is None:
            emit(
                "needs_data",
                reason="d_opt collapsed after projection onto d_tRNA/d_f3/d_usage",
                seed=SEED,
                captured_fraction_3indep=captured_fraction_3indep,
                checks={
                    "dwell_vector_computed": {"passed": True},
                    "dwell_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        increment = regression_increment(
            syn_rows=syn_rows,
            y_rows=y_rows,
            controls=controls,
            three_axis_basis=three_axis_basis,
            trna_direction=trna_direction,
            dwell_direction=dwell_direction,
        )
        if increment.get("status") != "computed":
            emit(
                "needs_data",
                reason=str(increment.get("reason", "dwell abundance increment could not be computed")),
                seed=SEED,
                dwell_summary=dwell_summary,
                increment=increment,
                checks={
                    "dwell_vector_computed": {"passed": True},
                    "dwell_vs_resid4_alignment": {"passed": True},
                    "fourth_mechanism_dwell_verdict": {"passed": False},
                },
            )

        cos_dwell_resid4 = cosine(dwell_direction, d_resid4)
        cos_dwell_usage = cosine(dwell_direction, usage_direction)
        cos_dwell_trna = cosine(dwell_direction, trna_direction)
        cos_dwell_f3 = cosine(dwell_direction, f3_direction)
        cos_resid4_usage = cosine(d_resid4, usage_direction)
        cos_resid4_trna = cosine(d_resid4, trna_direction)
        cos_resid4_f3 = cosine(d_resid4, f3_direction)
        evidence = {
            "status": "computed",
            "abs_cos_dwell_resid4": abs(cos_dwell_resid4),
            "abs_cos_dwell_usage": abs(cos_dwell_usage),
            "abs_cos_dwell_tRNA": abs(cos_dwell_trna),
            "dwell_increment_over_three_axis_held_out_r2": increment["dwell_increment_over_three_axis_held_out_r2"],
            "dwell_increment_over_tRNA_only_held_out_r2": increment["dwell_increment_over_tRNA_only_held_out_r2"],
        }
        conclusion, conclusion_summary = verdict(evidence)

        compact_increment = {key: value for key, value in increment.items() if not key.startswith("_")}
        alignment = {
            "cos_d_dwell_d_resid4": cos_dwell_resid4,
            "abs_cos_d_dwell_d_resid4": abs(cos_dwell_resid4),
            "cos_d_dwell_d_usage": cos_dwell_usage,
            "abs_cos_d_dwell_d_usage": abs(cos_dwell_usage),
            "cos_d_dwell_d_tRNA": cos_dwell_trna,
            "abs_cos_d_dwell_d_tRNA": abs(cos_dwell_trna),
            "cos_d_dwell_d_f3": cos_dwell_f3,
            "abs_cos_d_dwell_d_f3": abs(cos_dwell_f3),
            "cos_d_resid4_d_usage": cos_resid4_usage,
            "cos_d_resid4_d_tRNA": cos_resid4_trna,
            "cos_d_resid4_d_f3": cos_resid4_f3,
            "dwell_tRNA_correlation": cos_dwell_trna,
            "dwell_direction_top_abs_loadings": compact_direction(dwell_direction, syn_columns),
            "d_resid4_top_abs_loadings": compact_direction(d_resid4, syn_columns),
        }
        checks = {
            "dwell_vector_computed": {
                "passed": dwell_summary.get("status") == "computed" and len(syn_columns) == 41,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
                "observed_sense_codons": dwell_summary.get("observed_sense_codons"),
                "retained_window_positions": dwell_summary.get("retained_window_positions"),
                "definition": dwell_summary.get("definition"),
            },
            "dwell_vs_resid4_alignment": {
                "passed": all(finite_numeric(value) for value in [cos_dwell_resid4, cos_dwell_usage, cos_dwell_trna, cos_dwell_f3]),
                **alignment,
            },
            "fourth_mechanism_dwell_verdict": {
                "passed": conclusion in {"fourth_axis_is_elongation_dwell", "not_dwell", "partial"},
                "conclusion": conclusion,
                **conclusion_summary,
            },
        }
        status = "passed" if all(bool(block["passed"]) for block in checks.values()) else "failed"

        emit(
            status,
            reason=None if status == "passed" else "dwell vector, alignment, or verdict checks did not compute cleanly",
            seed=SEED,
            fold_count=FOLD_COUNT,
            organism=ORGANISM,
            conclusion=conclusion,
            payload={
                "yeast_only_power_note": "riboseq positional occupancy is available here only for Saccharomyces cerevisiae; this is a single-species mechanism identity assay with no cross-species power or phylogenetic correction.",
                "alignment": alignment,
                "dwell_abundance_increment": compact_increment,
                "dwell_vector": dwell_summary,
                "abundance_d_resid4": {
                    "captured_fraction_span_tRNA_f3_usage": captured_fraction_3indep,
                    "projection_coefficients_orthonormal_basis": projection_coefficients,
                    "d_resid4_norm": vector_norm(d_resid4),
                    "top_abs_loadings": compact_direction(d_resid4, syn_columns),
                    "fit_summary": fit_summary,
                    "rank_controls_syn_for_d_opt": rank_controls_syn_for_opt,
                    "rank_controls_y_for_d_opt": rank_controls_y_for_opt,
                    "residual_abundance_energy": vector_dot(y, y),
                },
                "axes": {
                    "three_axis_basis_summary": three_axis_summary,
                    "cos_trna_f3": cosine(trna_direction, f3_direction),
                    "cos_trna_usage": cosine(trna_direction, usage_direction),
                    "cos_f3_usage": cosine(f3_direction, usage_direction),
                    "usage_axis_summary": usage_summary,
                    "trna_source_summary": trna_summary,
                    "tai_weight_summary": {
                        **tai_summary,
                        "raw_w_min": min(raw_w.values()) if raw_w else None,
                        "raw_w_max": max(raw_w.values()) if raw_w else None,
                    },
                },
                "abundance_join": abundance_summary,
                "verdict": conclusion_summary,
                "arc_note": (
                    "If conclusion is not_dwell, then under the current repo-observable candidates this final elongation/dwell assay does not identify d_resid4; "
                    "the residual fourth axis remains unidentified by available repo data rather than being promoted to an unsupported mechanism."
                ),
            },
            controls_used={
                "target": "log10(abundance_ppm) from yeast cds_codon_abundance joined records",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "d_dwell": "per-codon-type mean relative ribosome occupancy from sibling wobble_dwell.schema_and_join + iter_gene_windows, family-centered by project_syn, then unit-normalized in synonymous contrast coordinates",
                "baseline_single_codon_axes": [
                    "d_tRNA: dos Reis tAI direction from yeast GtRNAdb/tRNA records",
                    "d_f3: fixed f3_stress direction from codon_topology q_vectors, projected within synonymous families",
                    "d_usage: yeast CDS within-synonymous-family usage-frequency direction from cds_codon_abundance",
                ],
                "d_resid4": "normalize(d_opt_abundance - Proj_span{d_tRNA,d_f3,d_usage}(d_opt_abundance)); dwell is not used to construct d_resid4",
                "held_out_increment": "5-fold deterministic CV R2 for baseline three-axis predictors versus baseline plus d_dwell score; fold-local slopes are refit after residualizing synonymous contrasts and target against controls",
                "tRNA_partial_increment": "5-fold held-out R2 for d_tRNA alone versus d_tRNA plus d_dwell after the same controls, reported because dwell can correlate with tRNA",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            checks=checks,
            caveats=[
                "Relative ribosome occupancy is treated as a descriptive dwell proxy, not a direct causal elongation-rate measurement.",
                "The assay is yeast-only because the local riboseq positional occupancy file is yeast-only.",
                "The dwell vector uses only file-provided 5prime and 3prime occupancy windows exposed by the sibling dwell parser, not whole-CDS ribosome profiling.",
                "d_opt and d_resid4 are full-sample abundance directions and therefore diagnostic, not pre-registered causal predictors.",
                "Negative or partial results are retained as exclusion evidence; no unmeasured mechanism is inferred from absence of alignment.",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            seed=SEED,
            checks={
                "dwell_vector_computed": {"passed": False},
                "dwell_vs_resid4_alignment": {"passed": False},
                "fourth_mechanism_dwell_verdict": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

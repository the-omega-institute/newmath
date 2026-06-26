#!/usr/bin/env python3
"""Mutation-vs-selection axis audit for non-tRNA universal optimal codon residuals."""

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
    controls_for_counts,
    deterministic_folds,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    cv_r2_multivariate,
    solve_linear_system,
    synonymous_contrast_columns,
    synonymous_contrast_row,
    xtx_xty,
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


EXPERIMENT_ID = "b_star_q6_universal_optimal_residual_axis_powered"
CLAIM_ID = "h3.cross_layer_relation.universal_optimal_residual_axis.b_star_q6_mutation_vs_selection_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
MIN_MEAN_COSINE = 0.08
ALPHA = 0.05
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return 0.5 * (ordered[middle - 1] + ordered[middle])


def vector_norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def unit_vector(values: list[float]) -> list[float] | None:
    norm = vector_norm(values)
    if norm <= EPS:
        return None
    return [value / norm for value in values]


def cosine(left: list[float], right: list[float]) -> float:
    denom = vector_norm(left) * vector_norm(right)
    if denom <= EPS:
        return 0.0
    return vector_dot(left, right) / denom


def gram_schmidt_residual(direction: list[float], basis: list[float]) -> list[float] | None:
    projection = vector_dot(direction, basis)
    return unit_vector([direction[index] - projection * basis[index] for index in range(len(direction))])


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def sign_test_greater(values: list[float]) -> dict[str, object]:
    positives = sum(1 for value in values if value > EPS)
    negatives = sum(1 for value in values if value < -EPS)
    n = positives + negatives
    if n <= 0:
        return {"n_nonzero": 0, "positive": positives, "negative": negatives, "p_greater": None}
    tail = sum(math.comb(n, k) for k in range(positives, n + 1)) / (2.0**n)
    return {"n_nonzero": n, "positive": positives, "negative": negatives, "p_greater": tail}


def t_test_mean_greater_zero(values: list[float]) -> dict[str, object]:
    n = len(values)
    value_mean = mean(values)
    if n < 2 or value_mean is None:
        return {"n": n, "mean": value_mean, "sd": None, "z_approx": None, "p_greater_normal_approx": None}
    variance = sum((value - value_mean) ** 2 for value in values) / (n - 1)
    sd = math.sqrt(variance)
    if sd <= EPS:
        z = math.inf if value_mean > 0.0 else (-math.inf if value_mean < 0.0 else 0.0)
    else:
        z = value_mean / (sd / math.sqrt(n))
    p = 0.0 if z == math.inf else (1.0 if z == -math.inf else 1.0 - normal_cdf(z))
    return {"n": n, "mean": value_mean, "sd": sd, "z_approx": z, "p_greater_normal_approx": p}


def paired_sign_test_greater(left: list[float], right: list[float]) -> dict[str, object]:
    deltas = [left[index] - right[index] for index in range(min(len(left), len(right)))]
    return {**sign_test_greater(deltas), "mean_delta": mean(deltas), "median_delta": median(deltas)}


def cv_r2_fixed_direction(
    x_rows: list[list[float]],
    y: list[float],
    direction: list[float],
    folds: list[list[int]],
) -> tuple[float, float]:
    x = [vector_dot(row, direction) for row in x_rows]
    y_energy = vector_dot(y, y)
    slope = 0.0 if vector_dot(x, x) <= EPS else vector_dot(x, y) / vector_dot(x, x)
    if y_energy <= EPS:
        return 0.0, slope
    all_indices = set(range(len(y)))
    sse = 0.0
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        x_train_energy = sum(x[index] * x[index] for index in train_indices)
        if x_train_energy <= EPS:
            fold_slope = 0.0
        else:
            fold_slope = sum(x[index] * y[index] for index in train_indices) / x_train_energy
        for index in test_indices:
            residual = y[index] - fold_slope * x[index]
            sse += residual * residual
    return 1.0 - sse / y_energy, slope


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
        total_sense_count += total
        total_gc3_count += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})

    gc3 = None if total_sense_count <= 0 else total_gc3_count / total_sense_count
    return syn_rows, y_rows, controls, gc3, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def fit_optimal_direction(syn_residualized: list[list[float]], y: list[float]) -> tuple[list[float] | None, dict[str, object]]:
    if not syn_residualized or not syn_residualized[0]:
        return None, {"ridge_step": None, "reason": "empty synonymous design"}
    xtx, xty = xtx_xty(syn_residualized, y)
    beta, ridge_step = solve_linear_system(xtx, xty)
    direction = unit_vector(beta)
    if direction is None:
        return None, {"ridge_step": ridge_step, "reason": "zero fitted coefficient norm"}
    return direction, {
        "ridge_step": ridge_step,
        "coefficient_norm": vector_norm(beta),
        "nonzero_coefficients_abs_gt_1e_12": sum(1 for value in beta if abs(value) > EPS),
    }


def gc3_contrast_direction(*, syn_columns: list[dict[str, object]]) -> list[float] | None:
    values = []
    for column in syn_columns:
        positive = str(column["positive_codon"])
        negative = str(column["negative_codon"])
        values.append((1.0 if positive[2] in {"G", "C"} else 0.0) - (1.0 if negative[2] in {"G", "C"} else 0.0))
    return unit_vector(values)


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

    residual_direction = gram_schmidt_residual(optimal_direction, trna_direction)
    if residual_direction is None:
        base["reason"] = "optimal direction collapsed after projecting out tRNA direction"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)
    trna_r2, trna_slope = cv_r2_fixed_direction(syn_residualized, y, trna_direction, folds)
    residual_r2, residual_slope = cv_r2_fixed_direction(syn_residualized, y, residual_direction, folds)
    gc_r2, gc_slope = cv_r2_fixed_direction(syn_residualized, y, gc_direction, folds)
    f3_r2, f3_slope = cv_r2_fixed_direction(syn_residualized, y, f3_direction, folds)

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "optimal_direction": optimal_direction,
        "trna_direction": trna_direction,
        "residual_direction": residual_direction,
        "cos_optimal_trna": cosine(optimal_direction, trna_direction),
        "cos_residual_gc": cosine(residual_direction, gc_direction),
        "cos_residual_f3": cosine(residual_direction, f3_direction),
        "abs_cos_residual_gc": abs(cosine(residual_direction, gc_direction)),
        "abs_cos_residual_f3": abs(cosine(residual_direction, f3_direction)),
        "cos_gc_f3": cosine(gc_direction, f3_direction),
        "total_syn_selection_held_out_r2": total_syn_selection,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "trna_alone_held_out_r2": trna_r2,
        "trna_alone_slope": trna_slope,
        "residual_direction_held_out_r2": residual_r2,
        "residual_direction_slope": residual_slope,
        "gc_direction_held_out_r2": gc_r2,
        "gc_direction_slope": gc_slope,
        "f3_direction_held_out_r2": f3_r2,
        "f3_direction_slope": f3_slope,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
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
    output: list[dict[str, object]] = []
    for row in rows:
        output.append(
            {
                "organism": row["organism"],
                "domain": row["domain"],
                "gc3": row["gc3"],
                "n_join": row["n_join"],
                "cos_optimal_trna": row["cos_optimal_trna"],
                "cos_residual_gc": row["cos_residual_gc"],
                "cos_residual_f3": row["cos_residual_f3"],
                "abs_cos_residual_gc": row["abs_cos_residual_gc"],
                "abs_cos_residual_f3": row["abs_cos_residual_f3"],
                "residual_R2": row["residual_direction_held_out_r2"],
                "gc_R2": row["gc_direction_held_out_r2"],
                "f3_R2": row["f3_direction_held_out_r2"],
                "trna_R2": row["trna_alone_held_out_r2"],
                "self_R2": row["self_direction_held_out_r2"],
                "total_syn_selection_R2": row["total_syn_selection_held_out_r2"],
                "fit_coefficient_norm": row["fit_summary"].get("coefficient_norm"),
                "usable_tai_record_count": row["trna_source_summary"].get("usable_tai_record_count"),
            }
        )
    return sorted(output, key=lambda item: str(item["organism"]))


def axis_pass(values: list[float], sign_test: dict[str, object], mean_test: dict[str, object]) -> bool:
    value_mean = mean(values)
    p_sign = sign_test.get("p_greater")
    p_mean = mean_test.get("p_greater_normal_approx")
    return (
        value_mean is not None
        and value_mean > MIN_MEAN_COSINE
        and p_sign is not None
        and float(p_sign) <= ALPHA
        and p_mean is not None
        and float(p_mean) <= ALPHA
        and int(sign_test.get("positive", 0)) > int(sign_test.get("negative", 0))
    )


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
                    "residual_aligns_some_axis_sign_test": {"passed": False},
                    "dominant_axis_identified": {"passed": False},
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
                    "residual_aligns_some_axis_sign_test": {"passed": False},
                    "dominant_axis_identified": {"passed": False},
                },
                caveats=[
                    "requires same-organism proteomics, cds_codon_abundance, and GtRNAdb/tRNA gene-copy payloads",
                    "strict same-key organism matching is used; near-name strain substitutions are not inferred",
                ],
            )

        gc_cosines = [float(row["cos_residual_gc"]) for row in computed]
        f3_cosines = [float(row["cos_residual_f3"]) for row in computed]
        abs_gc = [abs(value) for value in gc_cosines]
        abs_f3 = [abs(value) for value in f3_cosines]
        residual_r2_values = [float(row["residual_direction_held_out_r2"]) for row in computed]
        gc_r2_values = [float(row["gc_direction_held_out_r2"]) for row in computed]
        f3_r2_values = [float(row["f3_direction_held_out_r2"]) for row in computed]

        gc_sign = sign_test_greater(gc_cosines)
        f3_sign = sign_test_greater(f3_cosines)
        gc_mean_test = t_test_mean_greater_zero(gc_cosines)
        f3_mean_test = t_test_mean_greater_zero(f3_cosines)
        gc_abs_gt_f3 = paired_sign_test_greater(abs_gc, abs_f3)
        f3_abs_gt_gc = paired_sign_test_greater(abs_f3, abs_gc)

        gc_pass = axis_pass(gc_cosines, gc_sign, gc_mean_test)
        f3_pass = axis_pass(f3_cosines, f3_sign, f3_mean_test)
        residual_aligns_some_axis = gc_pass or f3_pass

        mean_abs_gc = mean(abs_gc)
        mean_abs_f3 = mean(abs_f3)
        if gc_pass and not f3_pass:
            dominant_axis = "GC_mutation_bias"
            dominance_reason = "GC axis alone clears signed cross-organism gates"
        elif f3_pass and not gc_pass:
            dominant_axis = "f3_translation_selection"
            dominance_reason = "f3_stress axis alone clears signed cross-organism gates"
        elif gc_pass and f3_pass:
            gc_stronger = mean_abs_gc is not None and mean_abs_f3 is not None and mean_abs_gc >= mean_abs_f3
            dominant_axis = "GC_mutation_bias" if gc_stronger else "f3_translation_selection"
            dominance_reason = "both axes clear signed gates; larger mean absolute residual cosine is reported as dominant"
        else:
            dominant_axis = "none"
            dominance_reason = "neither GC nor f3_stress clears signed cross-organism gates"

        status = "passed" if residual_aligns_some_axis else "failed"
        checks = {
            "directions_computed": {
                "passed": True,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
                "fixed_reference_directions_available": {"gc3": gc_direction is not None, "f3_stress": f3_direction is not None},
            },
            "residual_aligns_some_axis_sign_test": {
                "passed": residual_aligns_some_axis,
                "rule": "at least one axis has mean cosine > 0.08, one-sided sign-test p<=0.05, one-sided normal-approx mean-test p<=0.05, and more positives than negatives",
                "gc_axis_passed": gc_pass,
                "f3_axis_passed": f3_pass,
                "gc": {
                    "mean_cos": mean(gc_cosines),
                    "median_cos": median(gc_cosines),
                    "min_cos": min(gc_cosines),
                    "max_cos": max(gc_cosines),
                    "sign_test_greater": gc_sign,
                    "mean_test_normal_approx": gc_mean_test,
                },
                "f3": {
                    "mean_cos": mean(f3_cosines),
                    "median_cos": median(f3_cosines),
                    "min_cos": min(f3_cosines),
                    "max_cos": max(f3_cosines),
                    "sign_test_greater": f3_sign,
                    "mean_test_normal_approx": f3_mean_test,
                },
            },
            "dominant_axis_identified": {
                "passed": residual_aligns_some_axis and dominant_axis != "none",
                "dominant_axis": dominant_axis,
                "dominance_reason": dominance_reason,
                "mean_abs_cos_residual_gc": mean_abs_gc,
                "mean_abs_cos_residual_f3": mean_abs_f3,
                "paired_abs_gc_greater_than_abs_f3": gc_abs_gt_f3,
                "paired_abs_f3_greater_than_abs_gc": f3_abs_gt_gc,
                "mean_gc_minus_f3_abs_cos": None if mean_abs_gc is None or mean_abs_f3 is None else mean_abs_gc - mean_abs_f3,
            },
        }

        conclusion = (
            f"non-tRNA residual optimality aligns most with {dominant_axis}"
            if status == "passed"
            else "non-tRNA residual optimality does not systematically align with GC3 mutation-bias or f3_stress axes under these gates"
        )

        emit(
            status,
            reason=None if status == "passed" else "residual optimal directions did not clear signed cross-organism alignment gates for GC3 or f3_stress",
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            synonymous_design_columns=len(syn_columns),
            dominant_axis=dominant_axis,
            conclusion=conclusion,
            payload={
                "per_organism": compact_per_organism(computed),
                "cross_species": {
                    "mean_cos_residual_gc": mean(gc_cosines),
                    "median_cos_residual_gc": median(gc_cosines),
                    "residual_gc_sign_test_greater": gc_sign,
                    "residual_gc_mean_test_normal_approx": gc_mean_test,
                    "mean_cos_residual_f3": mean(f3_cosines),
                    "median_cos_residual_f3": median(f3_cosines),
                    "residual_f3_sign_test_greater": f3_sign,
                    "residual_f3_mean_test_normal_approx": f3_mean_test,
                    "mean_abs_cos_residual_gc": mean_abs_gc,
                    "mean_abs_cos_residual_f3": mean_abs_f3,
                    "paired_abs_gc_greater_than_abs_f3": gc_abs_gt_f3,
                    "paired_abs_f3_greater_than_abs_gc": f3_abs_gt_gc,
                    "mean_residual_R2": mean(residual_r2_values),
                    "median_residual_R2": median(residual_r2_values),
                    "mean_gc_R2": mean(gc_r2_values),
                    "median_gc_R2": median(gc_r2_values),
                    "mean_f3_R2": mean(f3_r2_values),
                    "median_f3_R2": median(f3_r2_values),
                    "positive_residual_R2_count": sum(1 for value in residual_r2_values if value > 0.0),
                    "positive_gc_R2_count": sum(1 for value in gc_r2_values if value > 0.0),
                    "positive_f3_R2_count": sum(1 for value in f3_r2_values if value > 0.0),
                    "cos_gc_f3": cosine(gc_direction, f3_direction),
                },
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "optimal_direction": "full-sample least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized",
                "trna_direction": "dos Reis tAI codon weights from same-organism GtRNAdb/tRNA gene-copy records, projected as w_positive_codon - w_reference_codon on the same 41 contrasts, then unit-normalized",
                "residual_direction": "Gram-Schmidt residual normalize(d_opt - (d_opt dot d_trna) d_trna)",
                "gc_direction": "fixed same-contrast vector using I(third base is G/C)_positive_codon - I(third base is G/C)_reference_codon, then unit-normalized",
                "f3_direction": "fixed f3_stress vector from q_vectors(codons)['f3_stress'], synonymous-family projected with project_syn, converted to the same 41 contrast columns, then unit-normalized",
                "held_out_strength": "5-fold CV R2 for each fixed one-dimensional direction with fold-local slope after residualizing target and synonymous contrasts against controls",
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
                "GC3 and f3_stress reference axes are fixed low-dimensional mechanism proxies; non-alignment does not exclude other mutational or translational structure",
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
                "residual_aligns_some_axis_sign_test": {"passed": False},
                "dominant_axis_identified": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Conservation audit for organism-specific optimal synonymous-codon directions."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    controls_for_counts,
    deterministic_folds,
    full_sample_slope,
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
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import (  # noqa: E402
    MIN_PROTEINS_PER_ORGANISM,
)
from run_b_star_q6_translation_survival_powered import (  # noqa: E402
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_optimal_codon_conservation_powered"
CLAIM_ID = "h3.cross_layer_relation.optimal_codon_conservation.b_star_q6_cross_organism_direction_powered"

F3_COORDINATE = "f3_stress"
FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
SEED = "sha256:b_star_q6_optimal_codon_conservation_powered:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def vector_norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def unit_vector(values: list[float]) -> list[float] | None:
    norm = vector_norm(values)
    if norm <= EPS:
        return None
    return [value / norm for value in values]


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return 0.5 * (ordered[middle - 1] + ordered[middle])


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


def cosine(left: list[float], right: list[float]) -> float:
    denom = vector_norm(left) * vector_norm(right)
    if denom <= EPS:
        return 0.0
    return vector_dot(left, right) / denom


def cv_r2_fixed_direction(
    x_rows: list[list[float]],
    y: list[float],
    direction: list[float],
    folds: list[list[int]],
) -> tuple[float, float]:
    x = [vector_dot(row, direction) for row in x_rows]
    slope = full_sample_slope(x, y)
    if len(x) != len(y):
        raise ValueError("predictor and target lengths differ")
    y_energy = vector_dot(y, y)
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
    summary = {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }
    return syn_rows, y_rows, controls, gc3, summary


def fit_optimal_direction(
    *,
    syn_residualized: list[list[float]],
    y: list[float],
) -> tuple[list[float] | None, dict[str, object]]:
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


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    proteomics_path = data_dir / f"proteomics_abundance_{organism}.json"
    if not cds_path.exists() or not proteomics_path.exists():
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance or proteomics_abundance JSON",
            "cds_exists": cds_path.exists(),
            "proteomics_exists": proteomics_path.exists(),
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

    syn_residualized, rank_controls_syn = residualize(syn_raw, controls)
    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y = matrix_column(y_residualized, 0)
    if vector_dot(y, y) <= EPS:
        base["reason"] = "zero residual abundance energy after controls"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        return base

    direction, fit_summary = fit_optimal_direction(syn_residualized=syn_residualized, y=y)
    if direction is None:
        base["reason"] = str(fit_summary.get("reason", "could not fit optimal direction"))
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_direction_r2, self_direction_slope = cv_r2_fixed_direction(
        syn_residualized,
        y,
        direction,
        folds,
    )

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "optimal_direction": direction,
        "total_syn_selection_held_out_r2": total_syn_selection,
        "total_syn_selection_nonnegative": max(0.0, total_syn_selection),
        "self_direction_held_out_r2": self_direction_r2,
        "self_direction_slope": self_direction_slope,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "synonymous_cv_summary": syn_cv_summary,
        "residual_synonymous_columns": len(syn_columns),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
    }


def pairwise_conservation(rows: list[dict[str, object]]) -> dict[str, object]:
    organisms = [str(row["organism"]) for row in rows]
    directions = [row["optimal_direction"] for row in rows]
    matrix: list[list[float]] = []
    pair_rows: list[dict[str, object]] = []
    for i, left in enumerate(rows):
        matrix_row: list[float] = []
        for j, right in enumerate(rows):
            value = cosine(directions[i], directions[j])  # type: ignore[arg-type]
            matrix_row.append(value)
            if i < j:
                gc_left = left.get("gc3")
                gc_right = right.get("gc3")
                gc_delta = (
                    None
                    if not finite_numeric(gc_left) or not finite_numeric(gc_right)
                    else abs(float(gc_left) - float(gc_right))
                )
                pair_rows.append(
                    {
                        "organism_a": left["organism"],
                        "organism_b": right["organism"],
                        "cosine": value,
                        "same_domain": left.get("domain") == right.get("domain"),
                        "domain_a": left.get("domain"),
                        "domain_b": right.get("domain"),
                        "gc3_delta": gc_delta,
                    }
                )
        matrix.append(matrix_row)
    pair_cosines = [float(row["cosine"]) for row in pair_rows]
    same_domain = [float(row["cosine"]) for row in pair_rows if row["same_domain"]]
    different_domain = [float(row["cosine"]) for row in pair_rows if not row["same_domain"]]
    gc_deltas = [
        float(row["gc3_delta"])
        for row in pair_rows
        if finite_numeric(row.get("gc3_delta"))
    ]
    gc_cosines = [
        float(row["cosine"])
        for row in pair_rows
        if finite_numeric(row.get("gc3_delta"))
    ]
    top_pairs = sorted(pair_rows, key=lambda row: float(row["cosine"]), reverse=True)[:12]
    bottom_pairs = sorted(pair_rows, key=lambda row: float(row["cosine"]))[:12]
    return {
        "organism_order": organisms,
        "cosine_matrix": matrix,
        "pair_count": len(pair_rows),
        "mean_pairwise_cosine": mean(pair_cosines),
        "median_pairwise_cosine": median(pair_cosines),
        "min_pairwise_cosine": min(pair_cosines) if pair_cosines else None,
        "max_pairwise_cosine": max(pair_cosines) if pair_cosines else None,
        "same_domain_mean_cosine": mean(same_domain),
        "different_domain_mean_cosine": mean(different_domain),
        "same_domain_pair_count": len(same_domain),
        "different_domain_pair_count": len(different_domain),
        "gc3_delta_vs_cosine_pearson": pearson(gc_deltas, gc_cosines),
        "top_cosine_pairs": top_pairs,
        "bottom_cosine_pairs": bottom_pairs,
    }


def conservation_call(summary: dict[str, object]) -> str:
    mean_cos = summary.get("mean_pairwise_cosine")
    same_mean = summary.get("same_domain_mean_cosine")
    diff_mean = summary.get("different_domain_mean_cosine")
    gc_corr = summary.get("gc3_delta_vs_cosine_pearson")
    if not finite_numeric(mean_cos):
        return "idiosyncratic"
    mean_value = float(mean_cos)
    domain_gap = (
        0.0
        if not finite_numeric(same_mean) or not finite_numeric(diff_mean)
        else float(same_mean) - float(diff_mean)
    )
    gc_clustered = finite_numeric(gc_corr) and float(gc_corr) <= -0.35
    domain_clustered = domain_gap >= 0.15
    if mean_value >= 0.60:
        return "conserved"
    if mean_value >= 0.25 and (gc_clustered or domain_clustered):
        return "clustered"
    if gc_clustered or domain_clustered:
        return "clustered"
    return "idiosyncratic"


def universal_core(rows: list[dict[str, object]]) -> tuple[list[float] | None, dict[str, object]]:
    if not rows:
        return None, {"reason": "no computed rows"}
    p = len(rows[0]["optimal_direction"])  # type: ignore[arg-type]
    average = [0.0 for _ in range(p)]
    for row in rows:
        direction = row["optimal_direction"]
        for index in range(p):
            average[index] += direction[index]  # type: ignore[index]
    average = [value / len(rows) for value in average]
    core = unit_vector(average)
    if core is None:
        return None, {"reason": "mean direction has zero norm", "mean_direction_norm": 0.0}
    alignments = [cosine(row["optimal_direction"], core) for row in rows]  # type: ignore[arg-type]
    return core, {
        "mean_direction_norm_before_normalization": vector_norm(average),
        "mean_alignment_to_core": mean(alignments),
        "min_alignment_to_core": min(alignments),
        "max_alignment_to_core": max(alignments),
    }


def evaluate_universal_core(
    *,
    repo: pathlib.Path,
    rows: list[dict[str, object]],
    core: list[float],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    for row in rows:
        organism = str(row["organism"])
        payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json")
        syn_raw, y_raw, controls, _gc3, _data_summary = organism_rows(
            payload=payload,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            syn_columns=syn_columns,
        )
        syn_residualized, _rank_controls_syn = residualize(syn_raw, controls)
        y_residualized, _rank_controls_y = residualize([[value] for value in y_raw], controls)
        y = matrix_column(y_residualized, 0)
        folds = deterministic_folds(len(y), f"{SEED}|{organism}|folds", FOLD_COUNT)
        r2, slope = cv_r2_fixed_direction(syn_residualized, y, core, folds)
        results.append(
            {
                "organism": organism,
                "universal_core_held_out_r2": r2,
                "universal_core_slope": slope,
                "self_direction_held_out_r2": row["self_direction_held_out_r2"],
                "total_syn_selection_held_out_r2": row["total_syn_selection_held_out_r2"],
                "core_vs_self_r2_delta": r2 - float(row["self_direction_held_out_r2"]),
                "core_vs_full_syn_r2_delta": r2 - float(row["total_syn_selection_held_out_r2"]),
            }
        )
    return results


def f3_contrast_direction(
    *,
    syn_columns: list[dict[str, object]],
    f3_projected: dict[str, float],
) -> list[float] | None:
    values = [
        f3_projected[str(column["positive_codon"])] - f3_projected[str(column["negative_codon"])]
        for column in syn_columns
    ]
    return unit_vector(values)


def named_direction_cosine(
    rows: list[dict[str, object]],
    organism: str,
    direction: list[float] | None,
) -> float | None:
    if direction is None:
        return None
    row = next((item for item in rows if item.get("organism") == organism), None)
    if row is None:
        return None
    return cosine(direction, row["optimal_direction"])  # type: ignore[arg-type]


def compact_per_organism(rows: list[dict[str, object]], core_rows: list[dict[str, object]]) -> list[dict[str, object]]:
    core_by_org = {str(row["organism"]): row for row in core_rows}
    output: list[dict[str, object]] = []
    for row in rows:
        core_row = core_by_org.get(str(row["organism"]), {})
        output.append(
            {
                "organism": row["organism"],
                "domain": row["domain"],
                "gc3": row["gc3"],
                "n_join": row["n_join"],
                "total_syn_selection_held_out_r2": row["total_syn_selection_held_out_r2"],
                "self_direction_held_out_r2": row["self_direction_held_out_r2"],
                "universal_core_held_out_r2": core_row.get("universal_core_held_out_r2"),
                "core_alignment": row.get("core_alignment"),
                "fit_coefficient_norm": row["fit_summary"].get("coefficient_norm"),
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

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                syn_columns=syn_columns,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        if n_computed < MIN_COMPLETE_ORGANISMS:
            emit(
                "failed",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
                checks={
                    "optimal_directions_computed": {
                        "passed": False,
                        "organisms_computed": n_computed,
                        "minimum": MIN_COMPLETE_ORGANISMS,
                    },
                    "conservation_structure_reported": {"passed": False},
                    "universal_core_explains": {"passed": False},
                },
                caveats=[
                    "n=15-scale organism panel is small and descriptive",
                    "no phylogenetic comparative correction is applied",
                ],
            )

        conservation = pairwise_conservation(computed)
        call = conservation_call(conservation)
        core, core_summary = universal_core(computed)
        if core is None:
            emit(
                "failed",
                reason=str(core_summary.get("reason", "universal core unavailable")),
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                conservation_summary=conservation,
                conservation_call=call,
                checks={
                    "optimal_directions_computed": {"passed": True, "organisms_computed": n_computed},
                    "conservation_structure_reported": {"passed": True},
                    "universal_core_explains": {"passed": False},
                },
                caveats=[
                    "n=15-scale organism panel is small and descriptive",
                    "no phylogenetic comparative correction is applied",
                ],
            )

        core_rows = evaluate_universal_core(
            repo=repo,
            rows=computed,
            core=core,
            codons=codons,
            code=code,
            aa_order=aa_order,
            syn_columns=syn_columns,
        )
        core_r2_values = [float(row["universal_core_held_out_r2"]) for row in core_rows]
        self_r2_values = [float(row["self_direction_held_out_r2"]) for row in computed]
        total_syn_values = [float(row["total_syn_selection_held_out_r2"]) for row in computed]
        core_positive = sum(1 for value in core_r2_values if value > 0.0)
        universal_core_summary = {
            **core_summary,
            "mean_universal_core_held_out_r2": mean(core_r2_values),
            "median_universal_core_held_out_r2": median(core_r2_values),
            "min_universal_core_held_out_r2": min(core_r2_values),
            "max_universal_core_held_out_r2": max(core_r2_values),
            "positive_universal_core_r2_count": core_positive,
            "organism_count": len(core_rows),
            "mean_self_direction_held_out_r2": mean(self_r2_values),
            "mean_total_syn_selection_held_out_r2": mean(total_syn_values),
        }
        universal_core_nontrivial = (
            finite_numeric(universal_core_summary["mean_universal_core_held_out_r2"])
            and float(universal_core_summary["mean_universal_core_held_out_r2"]) > 0.0
            and core_positive >= max(1, math.ceil(len(core_rows) / 3))
        )

        f3_localization = {
            "f3_vs_universal_core_cosine": None if f3_direction is None else cosine(f3_direction, core),
            "f3_vs_saccharomyces_cerevisiae_optimal_direction_cosine": named_direction_cosine(
                computed,
                "saccharomyces_cerevisiae",
                f3_direction,
            ),
            "f3_vs_escherichia_coli_k12_mg1655_optimal_direction_cosine": named_direction_cosine(
                computed,
                "escherichia_coli_k12_mg1655",
                f3_direction,
            ),
            "f3_direction_available": f3_direction is not None,
        }

        core_alignment_by_org = {
            str(row["organism"]): cosine(row["optimal_direction"], core)  # type: ignore[arg-type]
            for row in computed
        }
        for row in computed:
            row["core_alignment"] = core_alignment_by_org[str(row["organism"])]

        controls_used = {
            "target": "log10(abundance_ppm)",
            "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
            "direction_fit": "full-sample least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized",
            "held_out_strength": "5-fold CV R2 for full 41-column synonymous design after the same residualization",
            "universal_core": "unit-normalized mean of all organism unit optimal directions; tested as a fixed one-dimensional predictor with fold-local slopes",
            "controls": [
                "intercept",
                "log(cds_len_nt)",
                "log(total_sense_codons)",
                "gc3_fraction",
                "20 standard amino-acid composition fractions",
            ],
        }
        checks = {
            "optimal_directions_computed": {
                "passed": n_computed >= MIN_COMPLETE_ORGANISMS,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
            },
            "conservation_structure_reported": {
                "passed": conservation.get("pair_count") == n_computed * (n_computed - 1) // 2,
                "pair_count": conservation.get("pair_count"),
                "expected_pair_count": n_computed * (n_computed - 1) // 2,
                "mean_pairwise_cosine": conservation.get("mean_pairwise_cosine"),
                "conservation_call": call,
            },
            "universal_core_explains": {
                "passed": universal_core_nontrivial,
                "rule": "mean universal-core held-out R2 > 0 and at least one third of organisms have positive universal-core R2",
                "mean_universal_core_held_out_r2": universal_core_summary["mean_universal_core_held_out_r2"],
                "positive_universal_core_r2_count": core_positive,
                "organism_count": len(core_rows),
            },
        }

        status = "passed" if checks["optimal_directions_computed"]["passed"] and checks["conservation_structure_reported"]["passed"] else "failed"
        emit(
            status,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            synonymous_design_columns=len(syn_columns),
            mean_pairwise_cosine=conservation.get("mean_pairwise_cosine"),
            conservation_call=call,
            conservation_thresholds={
                "conserved": "mean_pairwise_cosine >= 0.60",
                "clustered": "mean_pairwise_cosine < 0.60 and either same-domain mean exceeds different-domain mean by >= 0.15 or GC3-delta-vs-cosine Pearson <= -0.35",
                "idiosyncratic": "neither conserved nor clustered by these descriptive thresholds",
            },
            per_organism=compact_per_organism(computed, core_rows),
            conservation_summary=conservation,
            universal_core_summary=universal_core_summary,
            universal_core_per_organism=core_rows,
            f3_localization=f3_localization,
            organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            controls_used=controls_used,
            checks=checks,
            caveats=[
                "n=15-scale organism panel is small and descriptive, so conservation and clustering calls are structure summaries rather than definitive evolutionary claims",
                "no phylogenetic comparative correction is applied",
                "the optimal direction is inferred from abundance-associated synonymous contrasts and should not be read as causal without independent perturbation or mechanistic validation",
            ],
        )
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "optimal_directions_computed": {"passed": False},
                "conservation_structure_reported": {"passed": False},
                "universal_core_explains": {"passed": False},
            },
            caveats=[
                "n=15-scale organism panel is small and descriptive",
                "no phylogenetic comparative correction is applied",
            ],
        )


if __name__ == "__main__":
    main()

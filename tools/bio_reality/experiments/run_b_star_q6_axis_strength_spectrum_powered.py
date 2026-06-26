#!/usr/bin/env python3
"""Per-organism mechanism-axis strength spectrum audit for optimal codon directions."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from collections import Counter, defaultdict
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_b_star_q6_optimality_axis_sufficiency_powered import (  # noqa: E402
    EPS,
    FOLD_COUNT,
    MIN_COMPLETE_ORGANISMS,
    compact_per_organism as route_s_compact_per_organism,
    summarize_values,
    test_organism,
)
from run_b_star_q6_f3_stress_cross_organism_powered import F3_COORDINATE  # noqa: E402
from run_b_star_q6_f3_stress_strength_driver_powered import synonymous_contrast_columns  # noqa: E402
from run_b_star_q6_organism_specificity_meta_powered import ORGANISMS  # noqa: E402
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import standard_amino_acids  # noqa: E402
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM  # noqa: E402
from run_b_star_q6_translation_survival_powered import fibers_for, project_syn, q_vectors, standard_code  # noqa: E402
from run_b_star_q6_universal_optimal_residual_axis_powered import (  # noqa: E402
    finite_numeric,
    mean,
    median,
    normal_cdf,
)


EXPERIMENT_ID = "b_star_q6_axis_strength_spectrum_powered"
CLAIM_ID = "h3.cross_layer_relation.axis_strength_spectrum.b_star_q6_per_organism_powered"
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"

AXES = ["d_tRNA", "d_f3", "d_usage", "d_resid4"]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def sd(values: list[float]) -> float | None:
    if len(values) < 2:
        return None
    value_mean = sum(values) / len(values)
    return math.sqrt(sum((value - value_mean) ** 2 for value in values) / (len(values) - 1))


def quantile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = q * (len(ordered) - 1)
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[int(position)]
    fraction = position - lower
    return ordered[lower] * (1.0 - fraction) + ordered[upper] * fraction


def descriptive(values: list[float]) -> dict[str, object]:
    return {
        **summarize_values(values),
        "sd": sd(values),
        "q25": quantile(values, 0.25),
        "q75": quantile(values, 0.75),
        "iqr": None if quantile(values, 0.25) is None or quantile(values, 0.75) is None else quantile(values, 0.75) - quantile(values, 0.25),
    }


def rank_average(values: list[float]) -> list[float]:
    indexed = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0] * len(values)
    index = 0
    while index < len(indexed):
        end = index + 1
        while end < len(indexed) and indexed[end][1] == indexed[index][1]:
            end += 1
        average_rank = 0.5 * (index + 1 + end)
        for cursor in range(index, end):
            ranks[indexed[cursor][0]] = average_rank
        index = end
    return ranks


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    left_mean = sum(left) / len(left)
    right_mean = sum(right) / len(right)
    numerator = sum((left[index] - left_mean) * (right[index] - right_mean) for index in range(len(left)))
    left_energy = sum((value - left_mean) ** 2 for value in left)
    right_energy = sum((value - right_mean) ** 2 for value in right)
    denom = math.sqrt(left_energy * right_energy)
    if denom <= EPS:
        return None
    return numerator / denom


def spearman(left: list[float], right: list[float]) -> dict[str, object]:
    pairs = [
        (float(x), float(y))
        for x, y in zip(left, right)
        if math.isfinite(float(x)) and math.isfinite(float(y))
    ]
    n = len(pairs)
    if n < 3:
        return {"n": n, "rho": None, "p_two_sided_normal_approx": None, "direction": "insufficient_n"}
    left_ranks = rank_average([pair[0] for pair in pairs])
    right_ranks = rank_average([pair[1] for pair in pairs])
    rho = pearson(left_ranks, right_ranks)
    if rho is None:
        return {"n": n, "rho": None, "p_two_sided_normal_approx": None, "direction": "constant_rank"}
    if abs(rho) >= 1.0:
        p = 0.0
    else:
        statistic = rho * math.sqrt((n - 2) / max(EPS, 1.0 - rho * rho))
        p = 2.0 * (1.0 - normal_cdf(abs(statistic)))
    if rho > 0.05:
        direction = "positive"
    elif rho < -0.05:
        direction = "negative"
    else:
        direction = "near_zero"
    return {
        "n": n,
        "rho": rho,
        "p_two_sided_normal_approx": p,
        "direction": direction,
        "p_value_caveat": "descriptive only; normal approximation on the Spearman t statistic, not an exact small-sample test",
    }


def normalized_positive(values: dict[str, float]) -> dict[str, float] | None:
    positive = {key: max(0.0, value) for key, value in values.items()}
    total = sum(positive.values())
    if total <= EPS:
        return None
    return {key: value / total for key, value in positive.items()}


def captured_spectrum(row: dict[str, object]) -> dict[str, float]:
    coefficients = row.get("three_axis_projection_coefficients")
    if not isinstance(coefficients, list) or len(coefficients) != 3:
        raise ValueError(f"{row.get('organism')} lacks three_axis_projection_coefficients")
    residual_norm = row.get("d_resid4_residual_norm")
    if not finite_numeric(residual_norm):
        raise ValueError(f"{row.get('organism')} lacks finite d_resid4_residual_norm")
    raw = {
        "d_tRNA": float(coefficients[0]) ** 2,
        "d_f3": float(coefficients[1]) ** 2,
        "d_usage": float(coefficients[2]) ** 2,
        "d_resid4": float(residual_norm) ** 2,
    }
    total = sum(raw.values())
    if total <= EPS:
        raise ValueError(f"{row.get('organism')} has zero captured-spectrum total")
    return {axis: raw[axis] / total for axis in AXES}


def heldout_r2(row: dict[str, object]) -> dict[str, float]:
    fields = {
        "d_tRNA": "trna_alone_held_out_r2",
        "d_f3": "f3_direction_held_out_r2",
        "d_usage": "usage_direction_held_out_r2",
        "d_resid4": "d_resid4_held_out_r2",
    }
    out: dict[str, float] = {}
    for axis, field in fields.items():
        value = row.get(field)
        if not finite_numeric(value):
            raise ValueError(f"{row.get('organism')} lacks finite {field}")
        out[axis] = float(value)
    return out


def dominant_axis(values: dict[str, float]) -> str:
    return max(AXES, key=lambda axis: (values[axis], -AXES.index(axis)))


def spectrum_rows(computed: list[dict[str, object]]) -> list[dict[str, object]]:
    output = []
    for row in computed:
        captured = captured_spectrum(row)
        r2 = heldout_r2(row)
        positive_r2_spectrum = normalized_positive(r2)
        output.append(
            {
                "organism": row["organism"],
                "domain": row["domain"],
                "gc3": row["gc3"],
                "n_join": row["n_join"],
                "proteomics_n_proteins": row.get("proteomics_n_proteins"),
                "captured_fraction": captured,
                "captured_fraction_sum": sum(captured.values()),
                "dominant_captured_axis": dominant_axis(captured),
                "held_out_R2": r2,
                "positive_held_out_R2_fraction": positive_r2_spectrum,
                "dominant_positive_held_out_R2_axis": None if positive_r2_spectrum is None else dominant_axis(positive_r2_spectrum),
                "self_R2": row["self_direction_held_out_r2"],
                "three_indep_axis_R2": row["three_indep_axis_held_out_r2"],
                "total_syn_selection_R2": row["total_syn_selection_held_out_r2"],
                "captured_fraction_3indep": row["captured_fraction_3indep"],
                "d_resid4_residual_norm": row["d_resid4_residual_norm"],
                "cos_optimal": {
                    "d_tRNA": row["cos_optimal_trna"],
                    "d_f3": row["cos_optimal_f3"],
                    "d_usage": row["cos_optimal_usage"],
                },
            }
        )
    return sorted(output, key=lambda item: str(item["organism"]))


def dominant_summary(rows: list[dict[str, object]], field: str) -> dict[str, object]:
    values = [str(row[field]) for row in rows if row.get(field) is not None]
    counts = Counter(values)
    examples = {
        axis: sorted(str(row["organism"]) for row in rows if row.get(field) == axis)
        for axis in AXES
        if counts.get(axis, 0) > 0
    }
    return {"counts": dict(sorted(counts.items())), "organisms_by_axis": examples}


def axis_dispersion(rows: list[dict[str, object]], spectrum_field: str) -> dict[str, object]:
    out = {}
    for axis in AXES:
        values = [
            float(row[spectrum_field][axis])
            for row in rows
            if isinstance(row.get(spectrum_field), dict) and finite_numeric(row[spectrum_field].get(axis))
        ]
        out[axis] = descriptive(values)
    return out


def by_domain(rows: list[dict[str, object]]) -> dict[str, object]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["domain"])].append(row)

    domain_means = {}
    for domain, members in sorted(grouped.items()):
        captured = {axis: [float(row["captured_fraction"][axis]) for row in members] for axis in AXES}
        r2 = {axis: [float(row["held_out_R2"][axis]) for row in members] for axis in AXES}
        positive_r2 = {
            axis: [
                float(row["positive_held_out_R2_fraction"][axis])
                for row in members
                if isinstance(row.get("positive_held_out_R2_fraction"), dict)
            ]
            for axis in AXES
        }
        domain_means[domain] = {
            "n": len(members),
            "organisms": sorted(str(row["organism"]) for row in members),
            "mean_gc3": mean([float(row["gc3"]) for row in members if finite_numeric(row.get("gc3"))]),
            "captured_fraction_mean": {axis: mean(captured[axis]) for axis in AXES},
            "captured_fraction_median": {axis: median(captured[axis]) for axis in AXES},
            "held_out_R2_mean": {axis: mean(r2[axis]) for axis in AXES},
            "positive_held_out_R2_fraction_mean": {axis: mean(positive_r2[axis]) for axis in AXES},
            "dominant_captured_axis_counts": dict(Counter(str(row["dominant_captured_axis"]) for row in members)),
        }

    axis_ranges = {}
    for axis in AXES:
        means = [
            float(summary["captured_fraction_mean"][axis])
            for summary in domain_means.values()
            if finite_numeric(summary["captured_fraction_mean"].get(axis))
        ]
        axis_ranges[axis] = None if not means else max(means) - min(means)

    return {
        "domain_count": len(grouped),
        "domain_sample_sizes": {domain: len(members) for domain, members in sorted(grouped.items())},
        "domain_means": domain_means,
        "captured_fraction_domain_mean_range": axis_ranges,
        "power_warning": "domain comparison is descriptive and underpowered because the complete intersection is small and domain sample sizes are imbalanced",
    }


def gc_covariation(rows: list[dict[str, object]]) -> dict[str, object]:
    gc3 = [float(row["gc3"]) for row in rows if finite_numeric(row.get("gc3"))]
    out = {"gc3_summary": descriptive(gc3), "captured_fraction_spearman": {}, "positive_held_out_R2_fraction_spearman": {}}
    for axis in AXES:
        captured_x = []
        captured_y = []
        positive_x = []
        positive_y = []
        for row in rows:
            if not finite_numeric(row.get("gc3")):
                continue
            captured_x.append(float(row["gc3"]))
            captured_y.append(float(row["captured_fraction"][axis]))
            if isinstance(row.get("positive_held_out_R2_fraction"), dict):
                positive_x.append(float(row["gc3"]))
                positive_y.append(float(row["positive_held_out_R2_fraction"][axis]))
        out["captured_fraction_spearman"][axis] = spearman(captured_x, captured_y)
        out["positive_held_out_R2_fraction_spearman"][axis] = spearman(positive_x, positive_y)
    out["power_warning"] = "GC3 correlations are effect-size descriptions; p values are small-sample approximations and not a basis for strong claims"
    return out


def conclusion_from(rows: list[dict[str, object]], domain_summary: dict[str, object], gc_summary: dict[str, object]) -> str:
    mean_captured = {
        axis: mean([float(row["captured_fraction"][axis]) for row in rows])
        for axis in AXES
    }
    ordered_axes = sorted(AXES, key=lambda axis: float(mean_captured[axis] or 0.0), reverse=True)
    dominant_counts = Counter(str(row["dominant_captured_axis"]) for row in rows)
    top_axis = ordered_axes[0]
    second_axis = ordered_axes[1]
    domain_sizes = domain_summary.get("domain_sample_sizes", {})
    gc_effects = gc_summary.get("captured_fraction_spearman", {})
    strongest_gc_axis = None
    strongest_gc_rho = -1.0
    if isinstance(gc_effects, dict):
        for axis, result in gc_effects.items():
            if isinstance(result, dict) and finite_numeric(result.get("rho")):
                rho_abs = abs(float(result["rho"]))
                if rho_abs > strongest_gc_rho:
                    strongest_gc_axis = axis
                    strongest_gc_rho = rho_abs
    gc_clause = "no finite GC3 effect estimate" if strongest_gc_axis is None else f"largest GC3 rank effect is {strongest_gc_axis} rho={gc_effects[strongest_gc_axis]['rho']:.3g}"
    return (
        f"Captured spectra are led by {top_axis} on average (then {second_axis}); "
        f"per-organism dominant counts are {dict(sorted(dominant_counts.items()))}; "
        f"domain means are descriptive only under imbalanced n={domain_sizes}; {gc_clause}."
    )


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
                    "spectrum_computed": {"passed": False},
                    "dominant_axis_distribution": {"passed": False},
                    "domain_gc_covariation_descriptive": {"passed": False},
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
                min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                synonymous_design_columns=len(syn_columns),
                checks={
                    "spectrum_computed": {"passed": False, "organisms_computed": n_computed, "minimum": MIN_COMPLETE_ORGANISMS},
                    "dominant_axis_distribution": {"passed": False},
                    "domain_gc_covariation_descriptive": {"passed": False},
                },
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
                caveats=["requires same-organism proteomics, cds_codon_abundance, and GtRNAdb/tRNA JSON intersection"],
            )

        rows = spectrum_rows(computed)
        domain_summary = by_domain(rows)
        gc_summary = gc_covariation(rows)
        n_domains = int(domain_summary["domain_count"])
        n_gc = int(gc_summary["gc3_summary"]["n"])

        spectrum_ok = (
            len(rows) == n_computed
            and all(abs(float(row["captured_fraction_sum"]) - 1.0) <= 1e-9 for row in rows)
            and all(all(finite_numeric(row["captured_fraction"].get(axis)) for axis in AXES) for row in rows)
            and all(all(finite_numeric(row["held_out_R2"].get(axis)) for axis in AXES) for row in rows)
        )
        dominant_ok = len(rows) > 0 and sum(Counter(str(row["dominant_captured_axis"]) for row in rows).values()) == len(rows)
        domain_gc_ok = n_domains >= 2 and n_gc >= 3

        checks = {
            "spectrum_computed": {
                "passed": spectrum_ok,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "captured_fraction_sum_tolerance": 1e-9,
                "axis_strength_definition": "squared coefficients of d_opt on the Route S Gram-Schmidt basis [d_tRNA,d_f3,d_usage] plus squared residual norm d_resid4, normalized to sum one",
                "held_out_R2_definition": "5-fold fixed-direction R2 for each axis with fold-local slopes; d_resid4 is fit from the full-sample post-three-axis residual, so this is diagnostic and optimistic",
            },
            "dominant_axis_distribution": {
                "passed": dominant_ok,
                "captured": dominant_summary(rows, "dominant_captured_axis"),
                "positive_held_out_R2_fraction": dominant_summary(rows, "dominant_positive_held_out_R2_axis"),
            },
            "domain_gc_covariation_descriptive": {
                "passed": domain_gc_ok,
                "domain_count": n_domains,
                "domain_sample_sizes": domain_summary["domain_sample_sizes"],
                "gc3_finite_n": n_gc,
                "power_warning": "complete intersection is small and domain-unbalanced; domain/GC analyses are descriptive effect-size scans, not powered tests",
            },
        }

        if not spectrum_ok:
            status = "failed"
            reason = "axis strength spectrum construction failed sanity checks"
        elif not domain_gc_ok:
            status = "needs_data"
            reason = "organism/domain/GC3 coverage is insufficient for even descriptive cross-domain or GC comparison"
        else:
            status = "passed"
            reason = None

        conclusion = conclusion_from(rows, domain_summary, gc_summary) if rows else "no complete organism spectra were computed"

        emit(
            status,
            reason=reason,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            synonymous_design_columns=len(syn_columns),
            conclusion=conclusion,
            payload={
                "per_organism": rows,
                "dominant_axis_distribution": checks["dominant_axis_distribution"],
                "axis_strength_dispersion": {
                    "captured_fraction": axis_dispersion(rows, "captured_fraction"),
                    "positive_held_out_R2_fraction": axis_dispersion(
                        [row for row in rows if isinstance(row.get("positive_held_out_R2_fraction"), dict)],
                        "positive_held_out_R2_fraction",
                    ),
                    "held_out_R2": {
                        axis: descriptive([float(row["held_out_R2"][axis]) for row in rows])
                        for axis in AXES
                    },
                },
                "domain_covariation": domain_summary,
                "gc3_covariation": gc_summary,
                "route_s_reference_compact": route_s_compact_per_organism(computed),
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "d_opt": "full-sample least-squares optimal direction after residualizing target and synonymous contrasts against controls, then unit-normalized",
                "d_tRNA": "Route S/N dos Reis tAI direction from same-organism GtRNAdb/tRNA records, independent of d_opt",
                "d_f3": "Route S/O fixed f3_stress direction from codon_topology q_vectors, family-projected, independent of d_opt",
                "d_usage": "Route S/Q same-organism within-synonymous-family CDS usage-frequency direction, independent of d_opt",
                "d_resid4": "Route S residual normalize(d_opt - Proj_span{d_tRNA,d_f3,d_usage}(d_opt)); fourth diagnostic component, not a pre-specified external mechanism",
                "captured_strength_spectrum": "squared Route S Gram-Schmidt projection coefficients for [d_tRNA,d_f3,d_usage] plus squared d_resid4 norm, normalized per organism to sum one; reported as the primary no-heldout geometric spectrum",
                "held_out_R2": "5-fold CV R2 for each fixed one-dimensional direction with fold-local slope after residualizing against controls; directions involving d_opt are full-sample-derived diagnostics and can be optimistic",
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
                "sample warning: the complete organism intersection is about a dozen organisms and is domain-imbalanced; cross-domain comparison has low power",
                "domain means and GC3 correlations are descriptive effect sizes; p values are approximate and should not be treated as confirmatory",
                "captured fractions are coefficient-space geometry on an ordered Gram-Schmidt basis [d_tRNA,d_f3,d_usage]; they can differ from held-out abundance R2 because predictors are correlated",
                "d_tRNA, d_f3, and d_usage are independent of d_opt; d_resid4 is derived from the post-three-axis d_opt residual",
                "held-out R2 for d_opt-derived directions, including d_resid4, remains optimistic because the direction is fitted on the full organism sample before fold scoring",
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
            seed=SEED,
            checks={
                "spectrum_computed": {"passed": False},
                "dominant_axis_distribution": {"passed": False},
                "domain_gc_covariation_descriptive": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

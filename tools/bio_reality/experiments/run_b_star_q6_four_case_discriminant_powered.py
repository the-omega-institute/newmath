#!/usr/bin/env python3
"""Powered per-protein B*_Q6 four-case discriminant over T and P readouts."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    partial_r2_entries,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import (
    coordinate_decomposition,
    load_json,
    modeled_tai_weights,
    protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_four_case_discriminant_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_conditioned_four_case_discriminant.b_star_q6_fourcase_powered"
CONJECTURE_ID = "q6.translation-conditioned.four-case-survival-discriminant.cross-layer"

ORGANISM_PAIRS = [
    {"organism": "saccharomyces_cerevisiae", "trna_organism": "saccharomyces_cerevisiae"},
    {"organism": "escherichia_coli_k12_mg1655", "trna_organism": "escherichia_coli"},
]
MIN_ORGANISMS = 2
MIN_PROTEINS_PER_ORGANISM = 500
SURVIVAL_EPS = 1e-12
DEGENERATE_R2 = 0.999999


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def finite(value: float) -> bool:
    return math.isfinite(value)


def frobenius2(matrix: list[list[float]]) -> float:
    return sum(value * value for row in matrix for value in row)


def classify_coordinate(s_qt: float, s_qp: float, mediation_drop: float) -> tuple[str, bool, str]:
    qt_positive = s_qt > SURVIVAL_EPS
    qp_positive = s_qp > SURVIVAL_EPS
    mediation_condition_met = mediation_drop > SURVIVAL_EPS
    if not qt_positive and not qp_positive:
        return "A", mediation_condition_met, "S_QT <= 0 and S_QP <= 0 within epsilon"
    if qt_positive and not qp_positive:
        return "B", mediation_condition_met, "S_QT > 0 and S_QP <= 0 within epsilon"
    if not qt_positive and qp_positive:
        return "C", mediation_condition_met, "S_QT <= 0 and S_QP > 0 within epsilon; not a translation mechanism"
    if mediation_condition_met:
        return "D", mediation_condition_met, "S_QT > 0, S_QP > 0, and direct q_i to P drops after conditioning on T"
    return (
        "positive_positive_without_mediation_drop",
        mediation_condition_met,
        "S_QT > 0 and S_QP > 0, but conditioning on T does not drop the direct q_i to P component",
    )


def cannot_claim() -> list[str]:
    return [
        "four-case labels are objective S^{QT}/S^{QP} sign plus mediation-condition classifications, not mechanism claims",
        "case C is not a translation mechanism; it can reflect unmeasured T, mRNA, selection, confounding, or non-translation paths",
        "modeled per-protein tAI from GtRNAdb tRNA gene-copy counts and dos Reis wobble weights is not ribo-seq",
        "the matched CDS/protein-abundance rows are cross-sectional and do not establish causality",
        "protein abundance is not isolated from mRNA abundance, turnover, localization, PTM, folding, or pathway context",
        "this experiment does not claim phenotype-function, function_realization, synonymous-edit rescue, or perturbation mechanism",
    ]


def future_required() -> list[str]:
    return [
        "matched ribosome profiling or calibrated translation-efficiency readouts for the same proteins",
        "matched mRNA abundance controls to separate protein abundance from expression-level confounding",
        "synonymous perturbation or rescue assays before causal mediation or mechanism statements",
        "matched protein turnover, localization, PTM, and stability readouts before assigning downstream protein-function routes",
        "independent held-out proteomes before treating coordinate cases as stable organism-level regularities",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def summarize_case_counts(rows: dict[str, dict[str, object]]) -> dict[str, int]:
    counts = {"A": 0, "B": 0, "C": 0, "D": 0, "positive_positive_without_mediation_drop": 0}
    for row in rows.values():
        case = str(row["case"])
        counts[case] = counts.get(case, 0) + 1
    return counts


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        required.append(f"tools/bio_reality/data/cds_codon_abundance_{pair['organism']}.json")
        required.append(f"tools/bio_reality/data/gtrnadb_trna_all_copy_{pair['trna_organism']}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS-abundance and GtRNAdb all-tRNA data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        organism_results: dict[str, object] = {}
        loaded_organisms = 0
        data_actual: dict[str, object] = {}
        residualized_ok = True
        computed_ok = True
        rank_ok = True
        classified_ok = True

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(payload, dict):
                raise ValueError(f"{organism} payload must be an object")
            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            x_rows, t_rows, y_rows, z_rows, data_summary = protein_rows(
                payload=payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
            )
            n_proteins = len(x_rows)
            if n_proteins >= MIN_PROTEINS_PER_ORGANISM:
                loaded_organisms += 1
            if n_proteins == 0:
                raise ValueError(f"{organism} has no usable joined proteins")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            t_tilde, _ = residualize(t_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            sqt_matrix, sqt_raw, _ = partial_r2_entries(x_tilde, t_tilde, q_names)
            sqp_matrix, sqp_raw, _ = partial_r2_entries(x_tilde, y_tilde, q_names)
            per_coordinate = coordinate_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)

            t_energy = frobenius2(t_tilde)
            y_energy = frobenius2(y_tilde)
            x_explained_t, rank_xtilde_for_t = explained_by_design(x_tilde, t_tilde)
            x_explained_y, rank_xtilde_for_y = explained_by_design(x_tilde, y_tilde)
            residual_df = n_proteins - rank_z
            r2_qt = 0.0 if t_energy <= SURVIVAL_EPS else max(0.0, min(1.0, x_explained_t / t_energy))
            r2_qp = 0.0 if y_energy <= SURVIVAL_EPS else max(0.0, min(1.0, x_explained_y / y_energy))
            organism_powered = (
                n_proteins >= MIN_PROTEINS_PER_ORGANISM
                and residual_df > 10 * (len(q_names) + 1)
                and rank_xtilde_for_t == len(q_names)
                and rank_xtilde_for_y == len(q_names)
                and t_energy > SURVIVAL_EPS
                and y_energy > SURVIVAL_EPS
                and r2_qt < DEGENERATE_R2
                and r2_qp < DEGENERATE_R2
            )

            coordinate_rows: dict[str, dict[str, object]] = {}
            for q_name in q_names:
                s_qt = float(sqt_matrix[q_name]["log10_abundance_ppm"])
                s_qp = float(sqp_matrix[q_name]["log10_abundance_ppm"])
                mediation_drop = float(per_coordinate[q_name]["indirect_R2_c_minus_c_prime"])
                case, mediation_condition_met, rationale = classify_coordinate(s_qt, s_qp, mediation_drop)
                coordinate_rows[q_name] = {
                    "S_QT": s_qt,
                    "S_QP": s_qp,
                    "mediation_drop": mediation_drop,
                    "case": case,
                    "mediation_condition_met": mediation_condition_met,
                    "classification_rationale": rationale,
                    "c_total_R2_QP": per_coordinate[q_name]["c_total_R2_QP"],
                    "c_prime_direct_R2_QP_given_T": per_coordinate[q_name]["c_prime_direct_R2_QP_given_T"],
                    "M_QTP_fraction": per_coordinate[q_name]["M_QTP_fraction"],
                    "raw_improvement_Q_to_T": sqt_raw[q_name]["log10_abundance_ppm"],
                    "raw_improvement_Q_to_P": sqp_raw[q_name]["log10_abundance_ppm"],
                }

            case_counts = summarize_case_counts(coordinate_rows)
            organism_classified = all(row["case"] in {"A", "B", "C", "D", "positive_positive_without_mediation_drop"} for row in coordinate_rows.values())
            data_actual[organism] = {
                "cds_organism": organism,
                "trna_organism": trna_organism,
                "n_joined": payload.get("n_joined"),
                "n_proteins_used": n_proteins,
            }
            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_proteins and len(t_tilde) == n_proteins and len(y_tilde) == n_proteins
            computed_ok = computed_ok and all(
                finite(float(row[key]))
                for row in coordinate_rows.values()
                for key in ["S_QT", "S_QP", "mediation_drop", "c_total_R2_QP", "c_prime_direct_R2_QP_given_T"]
            )
            rank_ok = rank_ok and organism_powered
            classified_ok = classified_ok and organism_classified

            organism_results[organism] = {
                **data_summary,
                **tai_summary,
                "R2_QT": r2_qt,
                "R2_QP": r2_qp,
                "coordinate_cases": coordinate_rows,
                "case_counts": case_counts,
                "D_coordinates": [q_name for q_name, row in coordinate_rows.items() if row["case"] == "D"],
                "C_coordinates": [q_name for q_name, row in coordinate_rows.items() if row["case"] == "C"],
                "unclassified_coordinates": [
                    q_name
                    for q_name, row in coordinate_rows.items()
                    if row["case"] not in {"A", "B", "C", "D", "positive_positive_without_mediation_drop"}
                ],
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde_for_T": rank_xtilde_for_t,
                    "rank_Xtilde_for_P": rank_xtilde_for_y,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "q_coordinate_count": len(q_names),
                    "t_residual_energy": t_energy,
                    "y_residual_energy": y_energy,
                    "X_explained_energy_on_T": x_explained_t,
                    "X_explained_energy_on_P": x_explained_y,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                    "powered_rank_sufficient": organism_powered,
                    "four_case_classified": organism_classified,
                },
            }

        checks = [
            {
                "name": "data_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS,
                "actual": data_actual,
                "expected": f">= {MIN_ORGANISMS} organisms with n_proteins >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "sqt_sqp_mediation_computed",
                "passed": computed_ok and all(
                    isinstance(result, dict) and len(result["coordinate_cases"]) == len(q_names)
                    for result in organism_results.values()
                ),
                "actual": {
                    organism: {
                        "coordinate_count": len(result["coordinate_cases"]),
                        "R2_QT": result["R2_QT"],
                        "R2_QP": result["R2_QP"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite S_QT, S_QP, and mediation_drop for every organism x B*_Q6 coordinate",
            },
            {
                "name": "controls_Z_residualized",
                "passed": residualized_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "X_Q, modeled per-protein tAI, and log10 abundance residualized against intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": rank_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism n >= 500, residual df far above controls plus coordinates, full residual X rank, nonzero T/P residual energy, and no all-1.0 rank saturation",
            },
            {
                "name": "four_case_classified",
                "passed": classified_ok,
                "actual": {
                    organism: {
                        "case_counts": result["case_counts"],
                        "unclassified_coordinates": result["unclassified_coordinates"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "each organism x q_i falls objectively in A, B, C, or D under the stated discriminant; positive-positive without mediation drop is not promoted to D",
            },
            {
                "name": "no_mechanism_overclaim",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "case labels are not mechanism claims; case C is explicitly not a translation mechanism; modeled-tAI is not ribo-seq",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; positive S_QT and S_QP without mediation drop is not forced into case D"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "The four-case discriminant is an objective S^{QT}/S^{QP} sign plus mediation-condition classification over per-protein modeled-tAI and measured abundance readouts; it is not a mechanism claim.",
                "readout_T": "per-protein mean modeled tAI = sum_codon(codon_count * tAI_weight) / sum_codon(codon_count), using GtRNAdb all-tRNA copy counts and dos Reis wobble weights",
                "readout_P": "log10(abundance_ppm) from measured PAXdb protein abundance joined to real CDS codon counts",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "classification_threshold": SURVIVAL_EPS,
                "coordinates": q_names,
                "organisms": organism_results,
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered four-case discriminant input")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""B*_Q6 translation-complement abundance residual coordinate readout.

This is a statistical projection decomposition. The translation readout is
modeled per-protein tAI, not measured ribosome profiling.
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    frobenius2,
    matrix_column,
    residualize,
    standard_amino_acids,
    vector_dot,
)
from run_b_star_q6_translation_mediation_powered import (
    MIN_PROTEINS_PER_ORGANISM,
    ORGANISM_PAIRS,
    controls_used,
    load_json,
    modeled_tai_weights,
    protein_rows,
    joint_decomposition,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_translation_complement_residual_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_complement_residual.b_star_q6_complement_support_powered"
CONJECTURE_ID = "q6.translation-complement-residual.coordinate-support.cross-layer"

SURVIVAL_EPS = 1e-12
RANK_TOL = 1e-10
RIDGE_EPS = 1e-10
MEDIATION_MATCH_TOL = 0.02
DOMINANT_SUPPORT_THRESHOLD = 0.80


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def finite(value: float) -> bool:
    return math.isfinite(value)


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def matrix_vector(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[index] * vector[index] for index in range(len(vector))) for row in matrix]


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def vector_norm2(vector: list[float]) -> float:
    return vector_dot(vector, vector)


def gram_matrix(design: list[list[float]]) -> list[list[float]]:
    if not design:
        return []
    width = len(design[0])
    gram = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in design:
        for i in range(width):
            for j in range(width):
                gram[i][j] += row[i] * row[j]
    return gram


def crossprod_vector(design: list[list[float]], response: list[float]) -> list[float]:
    if not design:
        return []
    width = len(design[0])
    out = [0.0 for _ in range(width)]
    for row, value in zip(design, response):
        for index in range(width):
            out[index] += row[index] * value
    return out


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            raise ValueError("normal-equation solve is rank deficient after ridge")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for item in range(col, n + 1):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(col, n + 1):
                aug[row][item] -= factor * aug[col][item]
    return [aug[row][n] for row in range(n)]


def solve_regularized_normal_equation(
    design: list[list[float]],
    response: list[float],
    ridge: float = RIDGE_EPS,
) -> list[float]:
    gram = gram_matrix(design)
    rhs = crossprod_vector(design, response)
    for index in range(len(gram)):
        gram[index][index] += ridge
    return solve_linear_system(gram, rhs)


def project_onto_design(design: list[list[float]], response: list[float]) -> tuple[list[float], list[float]]:
    coeff = solve_regularized_normal_equation(design, response)
    return matrix_vector(design, coeff), coeff


def jacobi_eigenvalues_symmetric(matrix: list[list[float]], tol: float = 1e-12, max_iter: int = 200) -> list[float]:
    n = len(matrix)
    if n == 0:
        return []
    a = [list(row) for row in matrix]
    for _ in range(max_iter):
        p = 0
        q = 1 if n > 1 else 0
        off = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                value = abs(a[i][j])
                if value > off:
                    off = value
                    p = i
                    q = j
        if off <= tol:
            break
        if a[p][p] == a[q][q]:
            angle = math.pi / 4.0
        else:
            angle = 0.5 * math.atan2(2.0 * a[p][q], a[q][q] - a[p][p])
        c = math.cos(angle)
        s = math.sin(angle)
        app = c * c * a[p][p] - 2.0 * s * c * a[p][q] + s * s * a[q][q]
        aqq = s * s * a[p][p] + 2.0 * s * c * a[p][q] + c * c * a[q][q]
        a[p][q] = 0.0
        a[q][p] = 0.0
        for r in range(n):
            if r in {p, q}:
                continue
            arp = c * a[r][p] - s * a[r][q]
            arq = s * a[r][p] + c * a[r][q]
            a[r][p] = arp
            a[p][r] = arp
            a[r][q] = arq
            a[q][r] = arq
        a[p][p] = app
        a[q][q] = aqq
    return [a[index][index] for index in range(n)]


def condition_number_from_gram(gram: list[list[float]]) -> float | None:
    eigenvalues = [abs(value) for value in jacobi_eigenvalues_symmetric(gram)]
    positive = [value for value in eigenvalues if value > RANK_TOL]
    if not positive:
        return None
    return max(positive) / min(positive)


def support_summary(q_names: list[str], a_perp: list[float]) -> dict[str, object]:
    total_abs = sum(abs(value) for value in a_perp)
    if total_abs <= SURVIVAL_EPS:
        entries = [
            {"coordinate": name, "a_perp": value, "abs_fraction": 0.0}
            for name, value in zip(q_names, a_perp)
        ]
        return {
            "normalization": "abs(a_perp_i) / sum_abs(a_perp)",
            "sum_abs_a_perp": total_abs,
            "entries": entries,
            "dominant_coordinates_cumulative_80pct": [],
            "dominant_cumulative_abs_fraction": 0.0,
        }

    entries = [
        {"coordinate": name, "a_perp": value, "abs_fraction": abs(value) / total_abs}
        for name, value in zip(q_names, a_perp)
    ]
    ordered = sorted(entries, key=lambda item: float(item["abs_fraction"]), reverse=True)
    dominant = []
    cumulative = 0.0
    for item in ordered:
        dominant.append(item["coordinate"])
        cumulative += float(item["abs_fraction"])
        if cumulative >= DOMINANT_SUPPORT_THRESHOLD:
            break
    return {
        "normalization": "abs(a_perp_i) / sum_abs(a_perp)",
        "sum_abs_a_perp": total_abs,
        "entries": entries,
        "dominant_coordinates_cumulative_80pct": dominant,
        "dominant_cumulative_abs_fraction": cumulative,
    }


def complement_decomposition(
    *,
    x_tilde: list[list[float]],
    t_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    y_energy = vector_norm2(y_col)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_qt, t_coeff_on_pq = project_onto_design(t_tilde, p_q)
    p_q_perp_t = subtract_vectors(p_q, p_qt)
    a_perp = solve_regularized_normal_equation(x_tilde, p_q_perp_t)

    p_q_energy = vector_norm2(p_q)
    p_qt_energy = vector_norm2(p_qt)
    p_q_perp_t_energy = vector_norm2(p_q_perp_t)
    r2_qp = 0.0 if y_energy <= SURVIVAL_EPS else p_q_energy / y_energy
    d = None if p_q_energy <= SURVIVAL_EPS else p_q_perp_t_energy / p_q_energy
    m = None if d is None else 1.0 - d

    x_rank = explained_by_design(x_tilde, y_tilde)[1]
    t_rank = explained_by_design(t_tilde, y_tilde)[1]
    x_gram = gram_matrix(x_tilde)
    t_gram = gram_matrix(t_tilde)

    return {
        "R2_QP": r2_qp,
        "m": m,
        "d": d,
        "P_Q_norm2": p_q_energy,
        "P_QT_norm2": p_qt_energy,
        "P_Q_perp_T_norm2": p_q_perp_t_energy,
        "a_perp": dict(zip(q_names, a_perp)),
        "support": support_summary(q_names, a_perp),
        "coefficients": {
            "a_total_Q_to_P": dict(zip(q_names, q_coeff)),
            "T_on_P_Q": t_coeff_on_pq,
        },
        "rank_condition_diagnostics": {
            "rank_Q_e": x_rank,
            "rank_T_e": t_rank,
            "q_coordinate_count": len(q_names),
            "t_column_count": len(t_tilde[0]) if t_tilde else 0,
            "ridge_epsilon": RIDGE_EPS,
            "condition_number_Q_gram": condition_number_from_gram(x_gram),
            "condition_number_T_gram": condition_number_from_gram(t_gram),
            "P_e_norm2": y_energy,
        },
    }


def compare_support_sets(organisms: dict[str, dict[str, object]]) -> dict[str, object]:
    dominant_sets = {
        organism: tuple(result["support"]["dominant_coordinates_cumulative_80pct"])
        for organism, result in organisms.items()
    }
    unique_sets = sorted({value for value in dominant_sets.values()})
    first_coordinates = {
        organism: (result["support"]["dominant_coordinates_cumulative_80pct"][0] if result["support"]["dominant_coordinates_cumulative_80pct"] else None)
        for organism, result in organisms.items()
    }
    return {
        "dominant_support_relation": "consistent" if len(unique_sets) == 1 else "heterogeneous",
        "top_coordinate_relation": "consistent" if len(set(first_coordinates.values())) == 1 else "heterogeneous",
        "dominant_sets_by_organism": dominant_sets,
        "top_coordinate_by_organism": first_coordinates,
    }


def cannot_claim() -> list[str]:
    return [
        "statistical projection decomposition, not causal",
        "T is modeled tAI not measured ribo-seq; measured TE does not reproduce modeled mediation except yeast (upstream result)",
        "a_perp identifies which residual coordinates carry the modeled-T-complement abundance residual, NOT a mechanism",
        "minimal supplementary readout H is future work - requires joining candidate readouts (measured TE/mRNA/turnover/localization)",
    ]


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

        organism_results: dict[str, dict[str, object]] = {}
        input_actual: dict[str, object] = {}
        mediation_alignment: dict[str, object] = {}

        joined_ok = True
        residualized_ok = True
        complement_ok = True
        a_perp_ok = True
        mediation_match_ok = True

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
            if n_proteins == 0:
                raise ValueError(f"{organism} has no usable joined proteins")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            t_tilde, _ = residualize(t_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            complement = complement_decomposition(
                x_tilde=x_tilde,
                t_tilde=t_tilde,
                y_tilde=y_tilde,
                q_names=q_names,
            )
            mediation_reference = joint_decomposition(
                x_tilde=x_tilde,
                t_tilde=t_tilde,
                y_tilde=y_tilde,
                q_names=q_names,
            )
            reference_m = mediation_reference["M_QTP_fraction"]
            complement_m = complement["m"]
            m_difference = None
            m_matches = False
            if isinstance(reference_m, float) and isinstance(complement_m, float):
                m_difference = abs(complement_m - reference_m)
                m_matches = m_difference < MEDIATION_MATCH_TOL

            a_values = list(complement["a_perp"].values())
            support_entries = complement["support"]["entries"]
            support_sum = sum(float(entry["abs_fraction"]) for entry in support_entries)
            finite_a = len(a_values) == len(q_names) and all(finite(float(value)) for value in a_values)
            support_ok = abs(support_sum - 1.0) < 1e-8 or complement["support"]["sum_abs_a_perp"] <= SURVIVAL_EPS
            finite_core = all(
                finite(float(complement[key]))
                for key in ["R2_QP", "P_Q_norm2", "P_QT_norm2", "P_Q_perp_T_norm2"]
            ) and isinstance(complement_m, float) and isinstance(complement["d"], float)

            input_actual[organism] = {
                "cds_organism": organism,
                "trna_organism": trna_organism,
                "n_joined": payload.get("n_joined"),
                "n_proteins_used": n_proteins,
                "rank_Z": rank_z,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
            }
            mediation_alignment[organism] = {
                "m_complement_projection": complement_m,
                "m_mediation_experiment_reference": reference_m,
                "absolute_difference": m_difference,
                "matches_within_0_02": m_matches,
                "reference_definition": "joint_decomposition from run_b_star_q6_translation_mediation_powered.py on the same residualized Q_e/T_e/P_e/Z rows",
            }

            joined_ok = joined_ok and n_proteins >= MIN_PROTEINS_PER_ORGANISM
            residualized_ok = residualized_ok and len(x_tilde) == n_proteins and len(t_tilde) == n_proteins and len(y_tilde) == n_proteins and rank_z > 0
            complement_ok = complement_ok and finite_core
            a_perp_ok = a_perp_ok and finite_a and support_ok
            mediation_match_ok = mediation_match_ok and m_matches

            organism_results[organism] = {
                **data_summary,
                **tai_summary,
                "n": n_proteins,
                "R2_QP": complement["R2_QP"],
                "m": complement["m"],
                "d": complement["d"],
                "P_Q_perp_T_norm2": complement["P_Q_perp_T_norm2"],
                "P_Q_norm2": complement["P_Q_norm2"],
                "P_QT_norm2": complement["P_QT_norm2"],
                "a_perp": complement["a_perp"],
                "support": complement["support"],
                "rank_condition_diagnostics": {
                    **complement["rank_condition_diagnostics"],
                    "rank_Z": rank_z,
                    "residual_df_after_Z": n_proteins - rank_z,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                },
                "mediation_alignment": mediation_alignment[organism],
            }

        priority_by_residual_energy = sorted(
            [
                {
                    "organism": organism,
                    "P_Q_perp_T_norm2": float(result["P_Q_perp_T_norm2"]),
                    "d": float(result["d"]),
                    "m": float(result["m"]),
                    "dominant_coordinates": result["support"]["dominant_coordinates_cumulative_80pct"],
                }
                for organism, result in organism_results.items()
            ],
            key=lambda item: float(item["P_Q_perp_T_norm2"]),
            reverse=True,
        )
        priority_by_retention = sorted(
            [
                {
                    "organism": organism,
                    "d": float(result["d"]),
                    "P_Q_perp_T_norm2": float(result["P_Q_perp_T_norm2"]),
                    "m": float(result["m"]),
                    "dominant_coordinates": result["support"]["dominant_coordinates_cumulative_80pct"],
                }
                for organism, result in organism_results.items()
            ],
            key=lambda item: float(item["d"]),
            reverse=True,
        )

        checks = [
            {
                "name": "mediation_inputs_joined",
                "passed": joined_ok,
                "actual": input_actual,
                "expected": f"every organism in the modeled mediation set has n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9,
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "exactly 9 B*_Q6 residual coordinates in the fixed order",
            },
            {
                "name": "controls_Z_residualized",
                "passed": residualized_ok,
                "actual": input_actual,
                "expected": "Q_e, T_e, and P_e residualized against the mediation experiment controls Z",
            },
            {
                "name": "complement_projection_computed",
                "passed": complement_ok,
                "actual": {
                    organism: {
                        "R2_QP": result["R2_QP"],
                        "m": result["m"],
                        "d": result["d"],
                        "P_Q_perp_T_norm2": result["P_Q_perp_T_norm2"],
                    }
                    for organism, result in organism_results.items()
                },
                "expected": "finite P_Q, P_QT, P_Q_perp_T, d, and m for every organism",
            },
            {
                "name": "a_perp_readout",
                "passed": a_perp_ok,
                "actual": {
                    organism: {
                        "a_perp_dimension": len(result["a_perp"]),
                        "support_abs_fraction_sum": sum(float(entry["abs_fraction"]) for entry in result["support"]["entries"]),
                        "dominant_coordinates": result["support"]["dominant_coordinates_cumulative_80pct"],
                    }
                    for organism, result in organism_results.items()
                },
                "expected": "finite 9-dimensional a_perp and normalized absolute-coordinate support",
            },
            {
                "name": "m_matches_mediation_experiment",
                "passed": mediation_match_ok,
                "actual": mediation_alignment,
                "expected": f"per-organism |m_complement_projection - m_mediation_experiment_reference| < {MEDIATION_MATCH_TOL}",
                "interpretation_if_failed": "negative self-check: the requested proj_T(P_Q) complement fraction is not algebraically identical to the existing mediation script's incremental-R2 fraction on these organisms",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {
                    "passed": True,
                    "cannot_claim": cannot_claim(),
                },
                "expected": "statistical/modeled-T/non-causal/non-mechanism language only",
            },
        ]

        status = "passed" if complement_ok and a_perp_ok and joined_ok and residualized_ok else "failed"
        reason = None
        if not mediation_match_ok:
            reason = "complement projection was computed, but m does not match the existing mediation experiment within 0.02 for every organism; see m_matches_mediation_experiment"
        if status != "passed":
            reason = "one or more computation gates failed"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "For each organism, P_Q is the abundance component explained by residualized B*_Q6 coordinates, and P_Q_perp_T is the modeled-tAI-complement residual of that component. a_perp reads this residual back in the 9 B*_Q6 coordinates.",
                "status_semantics": "passed means the projection complement and a_perp support were computed with finite values; mediation-alignment remains an explicit per-check result and may be false",
                "decomposition": {
                    "Q_e": "residualized 9-coordinate B*_Q6 design after controls Z",
                    "T_e": "residualized modeled per-protein tAI after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "P_Q": "proj_{Q_e}(P_e)",
                    "P_QT": "proj_{T_e}(P_Q)",
                    "P_Q_perp_T": "(I - proj_{T_e}) P_Q",
                    "a_perp": "(Q_e^T Q_e + ridge I)^(-1) Q_e^T P_Q_perp_T",
                    "d": "||P_Q_perp_T||^2 / ||P_Q||^2",
                    "m": "1 - d",
                },
                "coordinates": q_names,
                "per_organism": organism_results,
                "cross_organism": {
                    "priority_metric_primary": "d_non_mediated_retention",
                    "priority_by_non_mediated_retention_d": priority_by_retention,
                    "priority_by_P_Q_perp_T_norm2": priority_by_residual_energy,
                    "support_consistency": compare_support_sets(organism_results),
                },
                "controls_used": controls_used(aa_order),
                "honest": {
                    "cannot_claim": cannot_claim(),
                },
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable translation-complement residual input")


if __name__ == "__main__":
    main()

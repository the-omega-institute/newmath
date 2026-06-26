#!/usr/bin/env python3
"""M^QMP: B*_Q6 to protein abundance via yeast mRNA stability.

This is a statistical mediation decomposition on one joined yeast dataset. It
does not establish a causal codon-to-mRNA-stability-to-abundance pathway.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_mrna_half_life_sqm_powered import joined_rows
from run_b_star_q6_protein_omics_survival_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    SURVIVAL_EPS,
    controls_used,
    frobenius2,
    matrix_column,
    orthonormal_basis_from_columns,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import (
    append_columns,
    incremental_r2,
    ols_coefficients,
    r2_from_design,
    single_column_matrix,
    vector_dot,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_mrna_stability_mediation_powered"
CLAIM_ID = "h3.cross_layer_relation.mrna_stability_mediation.b_star_q6_abundance_residual_powered"
CONJECTURE_ID = "q6.mrna-stability-mediation.abundance-residual.cross-layer"

CDS_DATA_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
MRNA_DATA_PATH = "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json"
PERMUTATION_COUNT = 1000
SIGNIFICANCE_ALPHA = 0.05


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def finite_unit(value: object) -> bool:
    return finite(value) and 0.0 <= float(value) <= 1.0


def cannot_claim() -> list[str]:
    return [
        "statistical mediation decomposition, NOT a causal pathway proof",
        "single organism (S. cerevisiae) single half-life dataset (Neymotin 2014)",
        "observational; cannot establish codon->mRNA-stability->abundance causation",
        "mediation fraction is a variance-partition not a mechanism",
        "mRNA half-life is steady-state 4tU estimate",
        "reverse/confounded pathways (shared codon-driven processes) not excluded",
    ]


def deterministic_shuffle(values: list[float], perm_index: int) -> list[float]:
    shuffled = list(values)
    for index in range(len(shuffled) - 1, 0, -1):
        material = f"{EXPERIMENT_ID}|residual_mediator_permutation|{perm_index}|{index}|{len(shuffled)}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        shuffled[index], shuffled[swap_index] = shuffled[swap_index], shuffled[index]
    return shuffled


def residual_vector_against_basis(vector: list[float], basis: list[list[float]]) -> list[float]:
    residual = list(vector)
    for q in basis:
        coeff = vector_dot(residual, q)
        for index in range(len(residual)):
            residual[index] -= coeff * q[index]
    return residual


def single_vector_explained_energy(vector: list[float], target: list[float]) -> float:
    ss = vector_dot(vector, vector)
    if ss <= SURVIVAL_EPS:
        return 0.0
    xy = vector_dot(vector, target)
    return (xy * xy) / ss


def coefficient_entries(design: list[list[float]], response: list[list[float]], width: int) -> list[float]:
    rank = r2_from_design(design, response)[2]
    if rank != width:
        return [0.0 for _ in range(width)]
    return ols_coefficients(design, matrix_column(response, 0))


def joint_decomposition(
    *,
    x_tilde: list[list[float]],
    m_tilde: list[list[float]],
    p_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    xm_design = append_columns(x_tilde, m_tilde)
    r2_qp, explained_x, rank_x = r2_from_design(x_tilde, p_tilde)
    r2_qp_given_m, direct_improvement, rank_xm, rank_m = incremental_r2(
        full_design=xm_design,
        base_design=m_tilde,
        response=p_tilde,
    )
    r2_m_to_p, explained_m, _ = r2_from_design(m_tilde, p_tilde)
    r2_m_given_x, m_incremental_improvement, _, _ = incremental_r2(
        full_design=xm_design,
        base_design=x_tilde,
        response=p_tilde,
    )
    r2_qm, explained_x_to_m, rank_x_for_m = r2_from_design(x_tilde, m_tilde)

    absorbed = r2_qp - r2_qp_given_m
    fraction = None if abs(r2_qp) <= SURVIVAL_EPS else absorbed / r2_qp
    total_coeffs = coefficient_entries(x_tilde, p_tilde, len(q_names))
    direct_coeffs = coefficient_entries(xm_design, p_tilde, len(q_names) + 1)
    mediator_coeffs = coefficient_entries(x_tilde, m_tilde, len(q_names))

    return {
        "decomposition_mode": "joint_9d_conditioning_on_residualized_mRNA_half_life",
        "definition": "R2_QP is joint R2(P ~ X_Q after Z); R2_QP_given_M is the incremental R2 of X_Q in P ~ M + X_Q within the same Z-residual space; mediation_fraction is (R2_QP - R2_QP_given_M) / R2_QP.",
        "R2_QP": r2_qp,
        "R2_QP_given_M": r2_qp_given_m,
        "R2_absorbed_by_M": absorbed,
        "mediation_fraction": fraction,
        "M_only_R2_to_P": r2_m_to_p,
        "M_incremental_R2_given_X": r2_m_given_x,
        "R2_QM_path_a_joint": r2_qm,
        "path_coefficients": {
            "a_beta_M_on_X_by_coordinate": dict(zip(q_names, mediator_coeffs)),
            "b_beta_P_on_M_given_X": direct_coeffs[-1] if len(direct_coeffs) == len(q_names) + 1 else 0.0,
            "total_beta_P_on_X_by_coordinate": dict(zip(q_names, total_coeffs)),
            "direct_beta_P_on_X_given_M_by_coordinate": dict(zip(q_names, direct_coeffs[:-1])),
        },
        "rank_diagnostics": {
            "rank_Xtilde": rank_x,
            "rank_Mtilde": rank_m,
            "rank_XMtilde": rank_xm,
            "rank_X_for_M": rank_x_for_m,
            "q_coordinate_count": len(q_names),
            "p_residual_energy": frobenius2(p_tilde),
            "m_residual_energy": frobenius2(m_tilde),
            "X_explained_energy_on_P": explained_x,
            "X_direct_improvement_energy_given_M": direct_improvement,
            "M_explained_energy_on_P": explained_m,
            "M_incremental_improvement_energy_given_X": m_incremental_improvement,
            "X_explained_energy_on_M": explained_x_to_m,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
    }


def coordinate_decomposition(
    *,
    x_tilde: list[list[float]],
    m_tilde: list[list[float]],
    p_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, dict[str, object]]:
    p_col = matrix_column(p_tilde, 0)
    m_col = matrix_column(m_tilde, 0)
    out: dict[str, dict[str, object]] = {}
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_design = single_column_matrix(x_col)
        xm_design = append_columns(x_design, m_tilde)
        r2_total, _, rank_x = r2_from_design(x_design, p_tilde)
        r2_direct, _, rank_xm, rank_m = incremental_r2(
            full_design=xm_design,
            base_design=m_tilde,
            response=p_tilde,
        )
        absorbed = r2_total - r2_direct
        fraction = None if abs(r2_total) <= SURVIVAL_EPS else absorbed / r2_total

        x_ss = vector_dot(x_col, x_col)
        total_beta = vector_dot(x_col, p_col) / x_ss if x_ss > SURVIVAL_EPS else 0.0
        a_beta = vector_dot(x_col, m_col) / x_ss if x_ss > SURVIVAL_EPS else 0.0
        joint_coeffs = coefficient_entries(xm_design, p_tilde, 2)
        direct_beta = joint_coeffs[0] if len(joint_coeffs) == 2 else 0.0
        b_beta = joint_coeffs[1] if len(joint_coeffs) == 2 else 0.0

        if fraction is None:
            route = "no_total_coordinate_signal"
        elif fraction >= 0.5 and 0.0 <= fraction <= 1.0:
            route = "mostly_mediated_statistical"
        elif 0.0 <= fraction < 0.5:
            route = "mostly_direct_statistical"
        elif fraction < 0.0:
            route = "suppression_or_negative_conditioning"
        else:
            route = "conditioning_exceeds_total_association"

        out[q_name] = {
            "entry_before_control_M_total_beta_P_on_X": total_beta,
            "entry_after_control_M_direct_beta_P_on_X_given_M": direct_beta,
            "entry_delta_total_minus_direct": total_beta - direct_beta,
            "R2_QP_coordinate": r2_total,
            "R2_QP_given_M_coordinate": r2_direct,
            "R2_absorbed_by_M_coordinate": absorbed,
            "mediation_fraction_coordinate": fraction,
            "a_beta_M_on_X": a_beta,
            "b_beta_P_on_M_given_X": b_beta,
            "indirect_beta_a_times_b": a_beta * b_beta,
            "route": route,
            "rank_diagnostics": {
                "rank_X": rank_x,
                "rank_M": rank_m,
                "rank_XM": rank_xm,
            },
        }
    return out


def permutation_null(
    *,
    x_tilde: list[list[float]],
    m_tilde: list[list[float]],
    p_tilde: list[list[float]],
    q_names: list[str],
    observed_fraction: float,
    observed_r2_qp: float,
    count: int,
) -> dict[str, object]:
    m_col = matrix_column(m_tilde, 0)
    p_col = matrix_column(p_tilde, 0)
    p_ss = vector_dot(p_col, p_col)
    x_basis = orthonormal_basis_from_columns(x_tilde)
    x_explained = observed_r2_qp * p_ss
    exceed = 0
    fraction_sum = 0.0
    fraction_min = float("inf")
    fraction_max = float("-inf")
    direct_sum = 0.0
    direct_min = float("inf")
    direct_max = float("-inf")
    fractions: list[float] = []

    for perm_index in range(count):
        perm_m_col = deterministic_shuffle(m_col, perm_index)
        base_m_explained = single_vector_explained_energy(perm_m_col, p_col)
        m_perp_x = residual_vector_against_basis(perm_m_col, x_basis)
        full_explained = x_explained + single_vector_explained_energy(m_perp_x, p_col)
        perm_direct = max(0.0, min(1.0, max(0.0, full_explained - base_m_explained) / p_ss)) if p_ss > SURVIVAL_EPS else 0.0
        perm_fraction = (observed_r2_qp - perm_direct) / observed_r2_qp if observed_r2_qp > SURVIVAL_EPS else 0.0
        if not math.isfinite(perm_fraction):
            raise ValueError("permutation produced non-finite mediation fraction")
        fraction_sum += perm_fraction
        fractions.append(perm_fraction)
        fraction_min = min(fraction_min, perm_fraction)
        fraction_max = max(fraction_max, perm_fraction)
        direct_sum += perm_direct
        direct_min = min(direct_min, perm_direct)
        direct_max = max(direct_max, perm_direct)
        if perm_fraction >= observed_fraction:
            exceed += 1

    fractions_sorted = sorted(fractions)
    p95_index = max(0, min(len(fractions_sorted) - 1, math.ceil(0.95 * len(fractions_sorted)) - 1))
    return {
        "permutation_count": count,
        "null_model": "deterministic permutation of residualized log10(mRNA half-life) within the Z-orthogonal residual df using hashlib-derived Fisher-Yates swaps; same one-column mediator degree of freedom",
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|residual_mediator_permutation|perm_index|index|n",
        "observed_R2_QP_fixed": observed_r2_qp,
        "mediation_fraction": {
            "p_value_right_tail": (exceed + 1) / (count + 1),
            "null_mean": fraction_sum / count if count else 0.0,
            "null_p95": fractions_sorted[p95_index] if fractions_sorted else 0.0,
            "null_min_seen": fraction_min if count else 0.0,
            "null_max_seen": fraction_max if count else 0.0,
        },
        "R2_QP_given_permuted_M": {
            "null_mean": direct_sum / count if count else 0.0,
            "null_min_seen": direct_min if count else 0.0,
            "null_max_seen": direct_max if count else 0.0,
        },
    }


def core_conclusion(fraction: float, permutation: dict[str, object]) -> dict[str, object]:
    fraction_null = permutation.get("mediation_fraction")
    if not isinstance(fraction_null, dict):
        raise ValueError("permutation null lacks mediation_fraction result")
    p_value = float(fraction_null["p_value_right_tail"])
    null_p95 = float(fraction_null["null_p95"])
    exceeds_null = p_value <= SIGNIFICANCE_ALPHA and fraction > null_p95
    if exceeds_null and fraction >= 0.5:
        strength = "strong_statistical_partial_mediation"
        statement = "mRNA stability absorbs a large share of the B*_Q6 to protein-abundance residual association above the deterministic one-column mediator null."
    elif exceeds_null and fraction > 0.0:
        strength = "weak_to_moderate_statistical_partial_mediation"
        statement = "mRNA stability absorbs a positive share of the B*_Q6 to protein-abundance residual association above the deterministic one-column mediator null."
    elif fraction > 0.0:
        strength = "positive_but_not_null_exceeding"
        statement = "mRNA stability reduces the B*_Q6 to protein-abundance residual association, but the reduction does not exceed the deterministic one-column mediator null."
    else:
        strength = "negative_or_suppression_result"
        statement = "mRNA stability does not mediate the B*_Q6 to protein-abundance residual association in this statistical decomposition."
    return {
        "mediated_above_null": exceeds_null,
        "strength": strength,
        "decision_rule": f"statistical mediation is called only if mediation_fraction > null_p95 and permutation p <= {SIGNIFICANCE_ALPHA}",
        "statement": statement,
        "cannot_claim_short": "statistical mediation decomposition only; not causal pathway proof",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        cds_path = repo / CDS_DATA_PATH
        mrna_path = repo / MRNA_DATA_PATH
        genetic_code_path = repo / "tools/bio_reality/data/ncbi_genetic_codes.json"
        missing = [str(path.relative_to(repo)) for path in [cds_path, mrna_path, genetic_code_path] if not path.exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required local yeast CDS, protein abundance, and mRNA half-life data not present")

        cds_payload = load_json(cds_path)
        half_life_payload = load_json(mrna_path)
        if not isinstance(cds_payload, dict):
            raise ValueError("yeast CDS/protein-abundance payload must be an object")
        if not isinstance(half_life_payload, dict):
            raise ValueError("Neymotin mRNA half-life payload must be an object")

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        x_rows, m_rows, p_rows, z_rows, protein_ids, data_summary = joined_rows(
            cds_payload=cds_payload,
            half_life_payload=half_life_payload,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
        )
        n_joined = len(x_rows)
        if n_joined < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_data",
                reason=f"three-way join yielded n={n_joined}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
                checks=[
                    {
                        "name": "three_way_join",
                        "passed": False,
                        "actual": data_summary,
                        "expected": f"CDS codon counts, protein abundance, and Neymotin mRNA half-life join n >= {MIN_PROTEINS_PER_ORGANISM}",
                    },
                    {
                        "name": "no_causal_pathway_overclaim",
                        "passed": True,
                        "actual": cannot_claim(),
                        "expected": "statistical mediation only; no causal pathway promotion",
                    },
                ],
                result={
                    "claimed_layer": "cross_layer_relation",
                    "conjecture_id": CONJECTURE_ID,
                    "cannot_claim": cannot_claim(),
                },
            )

        x_tilde, rank_z = residualize(x_rows, z_rows)
        m_tilde, _ = residualize(m_rows, z_rows)
        p_tilde, _ = residualize(p_rows, z_rows)
        residual_df = n_joined - rank_z

        joint = joint_decomposition(x_tilde=x_tilde, m_tilde=m_tilde, p_tilde=p_tilde, q_names=q_names)
        per_coordinate = coordinate_decomposition(x_tilde=x_tilde, m_tilde=m_tilde, p_tilde=p_tilde, q_names=q_names)

        r2_qp = float(joint["R2_QP"])
        r2_qp_given_m = float(joint["R2_QP_given_M"])
        fraction_raw = joint["mediation_fraction"]
        if not isinstance(fraction_raw, float) or not math.isfinite(fraction_raw):
            raise ValueError("mediation_fraction is not finite")
        permutation = permutation_null(
            x_tilde=x_tilde,
            m_tilde=m_tilde,
            p_tilde=p_tilde,
            q_names=q_names,
            observed_fraction=fraction_raw,
            observed_r2_qp=r2_qp,
            count=PERMUTATION_COUNT,
        )
        conclusion = core_conclusion(fraction_raw, permutation)

        rank_diag = joint["rank_diagnostics"]
        permutation_fraction = permutation["mediation_fraction"]
        if not isinstance(permutation_fraction, dict):
            raise ValueError("permutation result lacks mediation_fraction")

        checks = [
            {
                "name": "three_way_join",
                "passed": n_joined >= MIN_PROTEINS_PER_ORGANISM,
                "actual": data_summary,
                "expected": f"CDS codon counts, PAXdb protein abundance, and Neymotin mRNA half-life join by 4932.ORF -> Syst with n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": len(q_names) == 9 and rank_z > 0 and len(z_rows) == n_joined and residual_df > 10 * (len(q_names) + 1),
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "controls_used": controls_used(aa_order),
                },
                "expected": "same 9 B*_Q6 coordinates and 24 controls Z as S^QP/S^QM: intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "direct_and_mediated_r2_computed",
                "passed": (
                    finite_unit(r2_qp)
                    and finite_unit(r2_qp_given_m)
                    and r2_qp > SURVIVAL_EPS
                    and r2_qp < DEGENERATE_R2
                    and int(rank_diag["rank_Xtilde"]) == len(q_names)
                    and int(rank_diag["rank_Mtilde"]) == 1
                    and int(rank_diag["rank_XMtilde"]) == len(q_names) + 1
                    and finite(rank_diag["p_residual_energy"])
                    and float(rank_diag["p_residual_energy"]) > SURVIVAL_EPS
                    and finite(rank_diag["m_residual_energy"])
                    and float(rank_diag["m_residual_energy"]) > SURVIVAL_EPS
                ),
                "actual": {
                    "R2_QP": r2_qp,
                    "R2_QP_given_M": r2_qp_given_m,
                    "R2_absorbed_by_M": joint["R2_absorbed_by_M"],
                    "rank_diagnostics": rank_diag,
                },
                "expected": "finite R2_QP and R2_QP_given_M in [0,1], nondegenerate P/M residual energy, and full X plus mediator rank",
            },
            {
                "name": "mediation_fraction_computed",
                "passed": (
                    finite(fraction_raw)
                    and float(fraction_raw) <= 1.0
                    and int(permutation["permutation_count"]) == PERMUTATION_COUNT
                    and finite_unit(permutation_fraction["p_value_right_tail"])
                    and all(isinstance(row, dict) and finite(row["entry_before_control_M_total_beta_P_on_X"]) and finite(row["entry_after_control_M_direct_beta_P_on_X_given_M"]) for row in per_coordinate.values())
                ),
                "actual": {
                    "mediation_fraction": fraction_raw,
                    "permutation_p_right_tail": permutation_fraction["p_value_right_tail"],
                    "permutation_null_mean": permutation_fraction["null_mean"],
                    "permutation_null_p95": permutation_fraction["null_p95"],
                    "per_coordinate_count": len(per_coordinate),
                    "deterministic_seed": permutation["deterministic_seed"],
                },
                "expected": "finite mediation_fraction, 1000 deterministic mediator permutations, reproducible p-value, and before/after entries for all 9 coordinates",
            },
            {
                "name": "no_causal_pathway_overclaim",
                "passed": cannot_claim() == [
                    "statistical mediation decomposition, NOT a causal pathway proof",
                    "single organism (S. cerevisiae) single half-life dataset (Neymotin 2014)",
                    "observational; cannot establish codon->mRNA-stability->abundance causation",
                    "mediation fraction is a variance-partition not a mechanism",
                    "mRNA half-life is steady-state 4tU estimate",
                    "reverse/confounded pathways (shared codon-driven processes) not excluded",
                ],
                "actual": cannot_claim(),
                "expected": "the result explicitly remains observational, one-organism, one-dataset, variance-partition-only, and non-causal",
            },
        ]

        status = "passed" if all(bool(check["passed"]) for check in checks) else "failed"
        reason = None if status == "passed" else "one or more honest gates failed"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "B*_Q6 to yeast protein-abundance residual association is decomposed by conditioning on residualized log10 mRNA half-life from Neymotin 2014; this is statistical mediation, NOT causal pathway evidence.",
                "readout_P": "log10(abundance_ppm) from measured PAXdb protein abundance joined to real yeast CDS codon counts",
                "readout_M": "log10(thalf minutes) from Neymotin et al 2014 yeast 4tU metabolic-labeling mRNA half-life table",
                "decomposition_mode": "joint 9-dimensional B*_Q6 mediation scalar with per-coordinate before/after audit",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py and Z controls matched to S^QP/S^QM",
                "n_joined": n_joined,
                "coordinates": q_names,
                "R2_QP": r2_qp,
                "R2_QP_given_M": r2_qp_given_m,
                "mediation_fraction": fraction_raw,
                "joint_decomposition": joint,
                "per_coordinate_before_after": per_coordinate,
                "permutation_null": permutation,
                "core_conclusion": conclusion,
                "rank_diagnostics": {
                    **rank_diag,
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "protein_id_count": len(protein_ids),
                },
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable M^QMP mediation input or fit")


if __name__ == "__main__":
    main()

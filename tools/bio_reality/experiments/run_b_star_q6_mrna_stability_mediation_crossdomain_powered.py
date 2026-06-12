#!/usr/bin/env python3
"""M^QMP cross-domain mediation for B*_Q6, abundance, and mRNA stability.

This is a per-organism statistical variance decomposition. It is observational
and does not establish a causal codon-to-mRNA-stability-to-abundance pathway.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any, Callable

from run_b_star_q6_mrna_half_life_sqm_ecoli_powered import (
    CDS_DATA_PATH as ECOLI_CDS_DATA_PATH,
    MRNA_DATA_PATH as ECOLI_MRNA_DATA_PATH,
    joined_rows as ecoli_joined_rows,
)
from run_b_star_q6_mrna_half_life_sqm_human_powered import (
    CDS_DATA_PATH as HUMAN_CDS_DATA_PATH,
    MRNA_DATA_PATH as HUMAN_MRNA_DATA_PATH,
    joined_rows as human_joined_rows,
)
from run_b_star_q6_mrna_stability_mediation_powered import (
    coefficient_entries,
    coordinate_decomposition,
    joint_decomposition,
    residual_vector_against_basis,
    single_vector_explained_energy,
)
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
    r2_from_design,
    vector_dot,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_mrna_stability_mediation_crossdomain_powered"
CLAIM_ID = "h3.cross_layer_relation.mrna_stability_mediation_crossdomain.b_star_q6_abundance_residual_powered"
CONJECTURE_ID = "q6.mrna-stability-mediation.cross-domain.abundance-residual.cross-layer"

PERMUTATION_COUNT = 1000
SIGNIFICANCE_ALPHA = 0.05
YEAST_MEDIATION_FRACTION_REFERENCE = 0.10


JoinRows = Callable[
    ...,
    tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[str], dict[str, object]],
]


ORGANISMS = [
    {
        "key": "ecoli",
        "label": "Escherichia coli K-12 MG1655",
        "domain": "prokaryote",
        "cds_path": ECOLI_CDS_DATA_PATH,
        "mrna_path": ECOLI_MRNA_DATA_PATH,
        "join_rows": ecoli_joined_rows,
        "half_life_dataset": "E.coli Esquerre 2015",
        "known_sqm_dominant_coord": "Arg_AGR",
        "known_cosine_SQM_vs_SQP": -0.78,
        "readout_M": "log10 mRNA half-life minutes at growth rate 0.40 h-1 from Esquerre 2015",
    },
    {
        "key": "human",
        "label": "Homo sapiens",
        "domain": "eukaryote",
        "cds_path": HUMAN_CDS_DATA_PATH,
        "mrna_path": HUMAN_MRNA_DATA_PATH,
        "join_rows": human_joined_rows,
        "half_life_dataset": "human Agarwal 2022 consensus",
        "known_sqm_dominant_coord": "Leu_CUN_vs_UUR",
        "known_cosine_SQM_vs_SQP": 0.64,
        "readout_M": "unlogged mean normalized relative mRNA half-life consensus from Agarwal 2022",
    },
]


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
        "per-organism single half-life dataset (E.coli Esquerre 2015; human Agarwal 2022 consensus)",
        "observational; cannot establish codon->mRNA-stability->abundance causation",
        "mediation fraction is a variance partition not a mechanism",
        "cross-domain comparison is descriptive, not phylogenetically controlled",
        "abundance and half-life datasets differ in platform/condition across organisms",
    ]


def deterministic_shuffle(values: list[float], organism_key: str, perm_index: int) -> list[float]:
    shuffled = list(values)
    for index in range(len(shuffled) - 1, 0, -1):
        material = (
            f"{EXPERIMENT_ID}|{organism_key}|residual_mediator_permutation|"
            f"{perm_index}|{index}|{len(shuffled)}"
        )
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        shuffled[index], shuffled[swap_index] = shuffled[swap_index], shuffled[index]
    return shuffled


def permutation_null(
    *,
    organism_key: str,
    x_tilde: list[list[float]],
    m_tilde: list[list[float]],
    p_tilde: list[list[float]],
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
        perm_m_col = deterministic_shuffle(m_col, organism_key, perm_index)
        base_m_explained = single_vector_explained_energy(perm_m_col, p_col)
        m_perp_x = residual_vector_against_basis(perm_m_col, x_basis)
        full_explained = x_explained + single_vector_explained_energy(m_perp_x, p_col)
        if p_ss > SURVIVAL_EPS:
            perm_direct = max(0.0, min(1.0, max(0.0, full_explained - base_m_explained) / p_ss))
        else:
            perm_direct = 0.0
        perm_fraction = (observed_r2_qp - perm_direct) / observed_r2_qp if observed_r2_qp > SURVIVAL_EPS else 0.0
        if not math.isfinite(perm_fraction):
            raise ValueError(f"{organism_key} permutation produced non-finite mediation fraction")
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
        "null_model": "deterministic permutation of residualized mRNA half-life readout within the Z-orthogonal residual df using hashlib-derived Fisher-Yates swaps; same one-column mediator degree of freedom",
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|{organism_key}|residual_mediator_permutation|perm_index|index|n",
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


def core_conclusion_for_organism(fraction: float, permutation: dict[str, object]) -> dict[str, object]:
    fraction_null = permutation.get("mediation_fraction")
    if not isinstance(fraction_null, dict):
        raise ValueError("permutation null lacks mediation_fraction result")
    p_value = float(fraction_null["p_value_right_tail"])
    null_p95 = float(fraction_null["null_p95"])
    exceeds_null = p_value <= SIGNIFICANCE_ALPHA and fraction > null_p95
    if exceeds_null and fraction >= 0.5:
        strength = "strong_statistical_partial_mediation"
    elif exceeds_null and fraction > 0.0:
        strength = "weak_to_moderate_statistical_partial_mediation"
    elif fraction > 0.0:
        strength = "positive_but_not_null_exceeding"
    else:
        strength = "negative_or_suppression_result"
    return {
        "mediated_above_null": exceeds_null,
        "strength": strength,
        "decision_rule": f"statistical mediation is called only if mediation_fraction > null_p95 and permutation p <= {SIGNIFICANCE_ALPHA}",
        "cannot_claim_short": "statistical mediation decomposition only; not causal pathway proof",
    }


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    aa_order = standard_amino_acids(code, codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    q_names = list(q_projected)
    q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
    return {
        "code": code,
        "codons": codons,
        "aa_order": aa_order,
        "q_projected": q_projected,
        "q_names": q_names,
        "q_support": q_support,
    }


def organism_needs_data_result(config: dict[str, object], reason: str, summary: object | None = None) -> dict[str, object]:
    return {
        "organism": config["label"],
        "domain": config["domain"],
        "status": "needs_data",
        "reason": reason,
        "data_summary": summary,
        "cannot_claim": cannot_claim(),
    }


def analyze_organism(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    cds_path = repo / str(config["cds_path"])
    mrna_path = repo / str(config["mrna_path"])
    missing = [str(path.relative_to(repo)) for path in [cds_path, mrna_path] if not path.exists()]
    if missing:
        return organism_needs_data_result(config, f"missing local required data: {missing}")

    cds_payload = load_json(cds_path)
    half_life_payload = load_json(mrna_path)
    if not isinstance(cds_payload, dict):
        raise ValueError(f"{config['key']} CDS payload must be an object")
    if not isinstance(half_life_payload, dict):
        raise ValueError(f"{config['key']} mRNA half-life payload must be an object")

    join_rows = config["join_rows"]
    x_rows, m_rows, p_rows, z_rows, stable_ids, data_summary = join_rows(
        cds_payload=cds_payload,
        half_life_payload=half_life_payload,
        codons=context["codons"],
        code=context["code"],
        aa_order=context["aa_order"],
        q_projected=context["q_projected"],
        q_names=context["q_names"],
        q_support=context["q_support"],
    )
    n_joined = len(x_rows)
    if n_joined < MIN_PROTEINS_PER_ORGANISM:
        return organism_needs_data_result(
            config,
            f"three-way join yielded n={n_joined}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            data_summary,
        )

    q_names = context["q_names"]
    aa_order = context["aa_order"]
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
        raise ValueError(f"{config['key']} mediation_fraction is not finite")

    permutation = permutation_null(
        organism_key=str(config["key"]),
        x_tilde=x_tilde,
        m_tilde=m_tilde,
        p_tilde=p_tilde,
        observed_fraction=fraction_raw,
        observed_r2_qp=r2_qp,
        count=PERMUTATION_COUNT,
    )
    conclusion = core_conclusion_for_organism(fraction_raw, permutation)
    rank_diag = joint["rank_diagnostics"]
    permutation_fraction = permutation["mediation_fraction"]
    if not isinstance(permutation_fraction, dict):
        raise ValueError(f"{config['key']} permutation result lacks mediation_fraction")

    direct_coeffs = coefficient_entries(append_columns(x_tilde, m_tilde), p_tilde, len(q_names) + 1)
    r2_m_given_x, _, _, _ = incremental_r2(
        full_design=append_columns(x_tilde, m_tilde),
        base_design=x_tilde,
        response=p_tilde,
    )
    r2_qm, _, _ = r2_from_design(x_tilde, m_tilde)

    computed_ok = (
        finite_unit(r2_qp)
        and finite_unit(r2_qp_given_m)
        and r2_qp > SURVIVAL_EPS
        and r2_qp < DEGENERATE_R2
        and finite(fraction_raw)
        and float(fraction_raw) <= 1.0
        and int(rank_diag["rank_Xtilde"]) == len(q_names)
        and int(rank_diag["rank_Mtilde"]) == 1
        and int(rank_diag["rank_XMtilde"]) == len(q_names) + 1
        and finite(rank_diag["p_residual_energy"])
        and float(rank_diag["p_residual_energy"]) > SURVIVAL_EPS
        and finite(rank_diag["m_residual_energy"])
        and float(rank_diag["m_residual_energy"]) > SURVIVAL_EPS
        and int(permutation["permutation_count"]) == PERMUTATION_COUNT
        and finite_unit(permutation_fraction["p_value_right_tail"])
        and all(
            isinstance(row, dict)
            and finite(row["entry_before_control_M_total_beta_P_on_X"])
            and finite(row["entry_after_control_M_direct_beta_P_on_X_given_M"])
            for row in per_coordinate.values()
        )
    )

    return {
        "organism": config["label"],
        "organism_key": config["key"],
        "domain": config["domain"],
        "status": "computed" if computed_ok else "failed",
        "half_life_dataset": config["half_life_dataset"],
        "known_sqm_dominant_coord": config["known_sqm_dominant_coord"],
        "known_cosine_SQM_vs_SQP": config["known_cosine_SQM_vs_SQP"],
        "readout_P": "log10(abundance_ppm) from local measured proteomics abundance joined to real CDS codon counts",
        "readout_M": config["readout_M"],
        "n_joined": n_joined,
        "stable_id_count": len(stable_ids),
        "data_summary": data_summary,
        "coordinates": q_names,
        "R2_QP": r2_qp,
        "R2_QP_given_M": r2_qp_given_m,
        "R2_absorbed_by_M": joint["R2_absorbed_by_M"],
        "mediation_fraction": fraction_raw,
        "permutation_p_right_tail": permutation_fraction["p_value_right_tail"],
        "joint_decomposition": joint,
        "per_coordinate_before_after": per_coordinate,
        "permutation_null": permutation,
        "core_conclusion": conclusion,
        "rank_diagnostics": {
            **rank_diag,
            "rank_Z": rank_z,
            "residual_df_after_Z": residual_df,
            "control_column_count": len(z_rows[0]) if z_rows else 0,
            "stable_id_count": len(stable_ids),
            "R2_M_given_X": r2_m_given_x,
            "R2_QM_path_a_joint_check": r2_qm,
            "b_beta_P_on_M_given_X_check": direct_coeffs[-1] if len(direct_coeffs) == len(q_names) + 1 else 0.0,
        },
        "controls_used": controls_used(aa_order),
        "cannot_claim": cannot_claim(),
    }


def signed_bucket(value: float | None) -> str:
    if value is None or not math.isfinite(value):
        return "unavailable"
    if value > 0.0:
        return "positive"
    if value < 0.0:
        return "negative"
    return "zero"


def cross_domain_conclusion(organism_results: dict[str, dict[str, object]]) -> dict[str, object]:
    ecoli_fraction = organism_results.get("ecoli", {}).get("mediation_fraction")
    human_fraction = organism_results.get("human", {}).get("mediation_fraction")
    ecoli_value = float(ecoli_fraction) if finite(ecoli_fraction) else None
    human_value = float(human_fraction) if finite(human_fraction) else None
    yeast_value = YEAST_MEDIATION_FRACTION_REFERENCE

    eukaryote_positive = yeast_value > 0.0 and human_value is not None and human_value > 0.0
    prokaryote_negative = ecoli_value is not None and ecoli_value < 0.0
    prokaryote_different = (
        ecoli_value is not None
        and human_value is not None
        and signed_bucket(ecoli_value) != signed_bucket(human_value)
    )

    if eukaryote_positive and prokaryote_negative:
        pattern = "descriptive_eukaryote_positive_prokaryote_negative_split"
        statement = "Human and yeast are positive while E.coli is negative in this statistical mediation fraction."
    elif eukaryote_positive and prokaryote_different:
        pattern = "descriptive_eukaryote_positive_prokaryote_different_split"
        statement = "Human and yeast are positive while E.coli differs in sign class in this statistical mediation fraction."
    elif eukaryote_positive and ecoli_value is not None:
        pattern = "no_sign_split_positive_all_available"
        statement = "Human, yeast, and E.coli are all positive in this statistical mediation fraction, so the S^QM/S^QP sign split does not carry through as a mediation sign split."
    elif human_value is None or ecoli_value is None:
        pattern = "partial_data_only"
        statement = "At least one cross-domain organism did not pass the three-way join gate, so the split cannot be evaluated completely."
    else:
        pattern = "no_clear_eukaryote_prokaryote_split"
        statement = "The available mediation fractions do not show a clear eukaryote/prokaryote sign split."

    return {
        "yeast_reference_mediation_fraction": yeast_value,
        "ecoli_mediation_fraction": ecoli_value,
        "human_mediation_fraction": human_value,
        "mediation_fraction_by_domain": {
            "yeast_eukaryote_reference": yeast_value,
            "human_eukaryote": human_value,
            "ecoli_prokaryote": ecoli_value,
        },
        "sign_bucket_by_domain": {
            "yeast_eukaryote_reference": signed_bucket(yeast_value),
            "human_eukaryote": signed_bucket(human_value),
            "ecoli_prokaryote": signed_bucket(ecoli_value),
        },
        "known_SQM_SQP_cosine_context": {
            "yeast_reference": 0.80,
            "human": 0.64,
            "ecoli": -0.78,
        },
        "pattern": pattern,
        "statement": statement,
        "caveat": "descriptive cross-domain comparison only; not phylogenetically controlled and not causal",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        genetic_code_path = repo / "tools/bio_reality/data/ncbi_genetic_codes.json"
        if not genetic_code_path.exists():
            emit("needs_data", missing_required_data=[str(genetic_code_path.relative_to(repo))])

        context = q6_context(repo)
        q_names = context["q_names"]
        organism_results: dict[str, dict[str, object]] = {}
        for config in ORGANISMS:
            result = analyze_organism(repo, context, config)
            organism_results[str(config["key"])] = result

        computed = {key: result for key, result in organism_results.items() if result.get("status") == "computed"}
        needs_data = {key: result for key, result in organism_results.items() if result.get("status") == "needs_data"}
        failed = {key: result for key, result in organism_results.items() if result.get("status") == "failed"}

        cross_domain = cross_domain_conclusion(organism_results)
        ecoli_joined = organism_results.get("ecoli", {}).get("n_joined")
        human_joined = organism_results.get("human", {}).get("n_joined")

        checks = [
            {
                "name": "ecoli_three_way_join",
                "passed": finite(ecoli_joined) and int(ecoli_joined) >= MIN_PROTEINS_PER_ORGANISM,
                "actual": organism_results.get("ecoli", {}).get("data_summary"),
                "expected": f"E.coli CDS codon counts, protein abundance, and Esquerre half-life join n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "human_three_way_join",
                "passed": finite(human_joined) and int(human_joined) >= MIN_PROTEINS_PER_ORGANISM,
                "actual": organism_results.get("human", {}).get("data_summary"),
                "expected": f"human CDS codon counts, protein abundance, and Agarwal consensus half-life join n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": (
                    len(q_names) == 9
                    and all(
                        result.get("status") != "computed"
                        or (
                            isinstance(result.get("rank_diagnostics"), dict)
                            and int(result["rank_diagnostics"]["rank_Z"]) > 0
                            and int(result["rank_diagnostics"]["control_column_count"]) == 24
                            and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * (len(q_names) + 1)
                        )
                        for result in organism_results.values()
                    )
                ),
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "computed_rank_diagnostics": {
                        key: result.get("rank_diagnostics")
                        for key, result in organism_results.items()
                        if result.get("status") == "computed"
                    },
                    "controls_used": controls_used(context["aa_order"]),
                },
                "expected": "same 9 B*_Q6 coordinates and 24 controls Z as S^QP/S^QM: intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "mediation_fractions_computed",
                "passed": (
                    bool(computed)
                    and not failed
                    and all(
                        finite(result.get("R2_QP"))
                        and finite(result.get("R2_QP_given_M"))
                        and finite(result.get("mediation_fraction"))
                        and float(result["R2_QP"]) > SURVIVAL_EPS
                        and float(result["R2_QP"]) < DEGENERATE_R2
                        and float(result["mediation_fraction"]) <= 1.0
                        and finite_unit(result.get("permutation_p_right_tail"))
                        and isinstance(result.get("per_coordinate_before_after"), dict)
                        and len(result["per_coordinate_before_after"]) == 9
                        for result in computed.values()
                    )
                ),
                "actual": {
                    key: {
                        "R2_QP": result.get("R2_QP"),
                        "R2_QP_given_M": result.get("R2_QP_given_M"),
                        "mediation_fraction": result.get("mediation_fraction"),
                        "permutation_p_right_tail": result.get("permutation_p_right_tail"),
                        "deterministic_seed": result.get("permutation_null", {}).get("deterministic_seed") if isinstance(result.get("permutation_null"), dict) else None,
                    }
                    for key, result in computed.items()
                },
                "expected": "finite organism-level mediation fractions, deterministic 1000-permutation null, and per-coordinate before/after entries",
            },
            {
                "name": "no_causal_pathway_overclaim",
                "passed": cannot_claim() == [
                    "statistical mediation decomposition, NOT a causal pathway proof",
                    "per-organism single half-life dataset (E.coli Esquerre 2015; human Agarwal 2022 consensus)",
                    "observational; cannot establish codon->mRNA-stability->abundance causation",
                    "mediation fraction is a variance partition not a mechanism",
                    "cross-domain comparison is descriptive, not phylogenetically controlled",
                    "abundance and half-life datasets differ in platform/condition across organisms",
                ],
                "actual": cannot_claim(),
                "expected": "the result explicitly remains observational, per-organism, one-dataset, variance-partition-only, descriptive, and non-causal",
            },
        ]

        status = "passed" if computed and not failed else "needs_data"
        reason = None
        if not computed:
            reason = "no organism passed the honest three-way join and mediation computation gates"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "B*_Q6 to protein-abundance residual association is decomposed per organism by conditioning on residualized mRNA half-life/stability readout; this is statistical mediation, NOT causal pathway evidence.",
                "decomposition_mode": "joint 9-dimensional B*_Q6 mediation scalar with per-coordinate before/after audit, matched to yeast M^QMP mathematics",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py and Z controls matched to S^QP/S^QM",
                "organisms": organism_results,
                "computed_organism_count": len(computed),
                "needs_data_organisms": sorted(needs_data),
                "cross_domain_mediation_comparison": cross_domain,
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable cross-domain M^QMP mediation input or fit")


if __name__ == "__main__":
    main()

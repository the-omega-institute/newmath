#!/usr/bin/env python3
"""Yeast B*_Q6 abundance-residual mediation through 5-prime coding MFE.

This is an observational variance-partition experiment. The structure readout
is a precomputed first-39nt CDS MFE proxy and is not a measured initiation rate.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_joint_te_stability_mediation_powered import (
    cds_rows_for_item,
    finite,
    finite_unit,
    load_json,
    q6_context,
    te_indices,
    yeast_join_keys,
    yeast_mrna_index,
)
from run_b_star_q6_protein_omics_survival_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    SURVIVAL_EPS,
    controls_used,
    frobenius2,
    matrix_column,
    numeric,
    residualize,
)
from run_b_star_q6_translation_mediation_powered import (
    append_columns,
    incremental_r2,
    r2_from_design,
)


EXPERIMENT_ID = "b_star_q6_structure_mediation_yeast_powered"
CLAIM_ID = "h3.cross_layer_relation.structure_mediation_yeast.b_star_q6_abundance_residual_powered"
CONJECTURE_ID = "q6.mrna-structure-mediation.abundance-residual.cross-layer"

ORGANISM_KEY = "saccharomyces_cerevisiae"
ORGANISM_LABEL = "Saccharomyces cerevisiae"
PERMUTATION_COUNT = 1000
SIGNIFICANCE_ALPHA = 0.05

CDS_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
TE_PATH = "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json"
MRNA_PATH = "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json"
STRUCTURE_PATH = "tools/bio_reality/data/mrna_five_prime_structure_saccharomyces_cerevisiae.json"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status in {"passed", "needs_data"} else 2)


def cannot_claim() -> list[str]:
    return [
        "5' coding-region MFE is a CDS-only structure proxy (no 5'UTR)",
        "minimum-free-energy single-structure estimate, not ensemble",
        "structure is sequence-derived, partially GC-correlated; controlled-Z mediation mitigates but does not fully isolate",
        "not a measured translation-initiation rate",
        "single organism (yeast), single datasets per readout",
        "statistical variance-partition, NOT causal pathway proof",
    ]


def fraction(numerator: float, denominator: float) -> float:
    if abs(denominator) <= SURVIVAL_EPS:
        return 0.0
    return numerator / denominator


def structure_index(payload: dict[str, object]) -> tuple[dict[str, float], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, dict):
        raise ValueError("structure payload must contain genes object")

    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_mfe": 0, "nonfinite_mfe": 0}
    for key, value in genes.items():
        if not isinstance(value, dict):
            skipped["non_object"] += 1
            continue
        mfe = value.get("five_prime_mfe_kcal_mol")
        if mfe is None:
            skipped["missing_mfe"] += 1
            continue
        mfe_value = numeric(mfe, f"structure.genes.{key}.five_prime_mfe_kcal_mol")
        if not math.isfinite(mfe_value):
            skipped["nonfinite_mfe"] += 1
            continue
        locus_tag = value.get("locus_tag")
        stable_id = str(locus_tag) if isinstance(locus_tag, str) and locus_tag else str(key)
        out[stable_id] = mfe_value

    return out, {
        "structure_readout": payload.get("readout"),
        "structure_join_key": payload.get("join_key"),
        "structure_n_genes_reported": payload.get("n_genes"),
        "n_valid_structure_mfe": len(out),
        "skipped_structure_records": skipped,
    }


def five_way_rows(
    *,
    cds_payload: dict[str, object],
    te_payload: dict[str, object],
    mrna_payload: dict[str, object],
    structure_payload: dict[str, object],
    context: dict[str, object],
) -> tuple[
    list[list[float]],
    list[list[float]],
    list[list[float]],
    list[list[float]],
    list[list[float]],
    list[list[float]],
    list[str],
    dict[str, object],
]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("CDS payload must contain joined list")

    te_by_protein, te_by_gene, te_summary = te_indices(te_payload, ORGANISM_KEY)
    mrna_by_key, mrna_summary = yeast_mrna_index(mrna_payload)
    structure_by_key, structure_summary = structure_index(structure_payload)

    x_rows: list[list[float]] = []
    p_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    m_rows: list[list[float]] = []
    s_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    stable_ids: list[str] = []
    seen: set[str] = set()
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "unparseable_yeast_orf": 0,
        "duplicate_stable_id": 0,
        "no_te_match": 0,
        "no_mrna_half_life_match": 0,
        "no_structure_match": 0,
        "nonpositive_abundance": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna_half_life": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    join_sources = {
        "te_protein_id": 0,
        "te_gene_key": 0,
        "mrna_syst": 0,
        "structure_locus_tag": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue

        protein_id, orf, error = yeast_join_keys(item)
        if error:
            skipped[error] += 1
            continue
        stable_id = str(orf)
        if stable_id in seen:
            skipped["duplicate_stable_id"] += 1
            continue

        te_record = te_by_protein.get(str(protein_id))
        if te_record is None:
            te_record = te_by_gene.get(stable_id)
            if te_record is not None:
                join_sources["te_gene_key"] += 1
        else:
            join_sources["te_protein_id"] += 1
        if te_record is None:
            skipped["no_te_match"] += 1
            continue
        if te_record["te"] <= 0.0:
            skipped["nonpositive_te"] += 1
            continue

        mrna_value = mrna_by_key.get(stable_id)
        if mrna_value is None:
            skipped["no_mrna_half_life_match"] += 1
            continue
        if mrna_value <= 0.0:
            skipped["nonpositive_mrna_half_life"] += 1
            continue
        join_sources["mrna_syst"] += 1

        structure_value = structure_by_key.get(stable_id)
        if structure_value is None:
            skipped["no_structure_match"] += 1
            continue
        join_sources["structure_locus_tag"] += 1

        abundance = numeric(item.get("abundance_ppm"), f"{ORGANISM_KEY}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue

        try:
            x_row, z_row = cds_rows_for_item(
                item=item,
                row_index=row_index,
                organism_key=ORGANISM_KEY,
                codons=context["codons"],
                code=context["code"],
                aa_order=context["aa_order"],
                q_projected=context["q_projected"],
                q_names=context["q_names"],
                q_support=context["q_support"],
            )
        except ValueError as exc:
            key = str(exc)
            if key in skipped:
                skipped[key] += 1
                continue
            raise

        x_rows.append(x_row)
        p_rows.append([math.log10(abundance)])
        t_rows.append([math.log10(te_record["te"])])
        m_rows.append([mrna_value])
        s_rows.append([structure_value])
        z_rows.append(z_row)
        stable_ids.append(stable_id)
        seen.add(stable_id)

    summary = {
        **te_summary,
        **{f"mrna_{key}": value for key, value in mrna_summary.items()},
        **structure_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined": len(x_rows),
        "join_sources": join_sources,
        "skipped_cds_records": skipped,
    }
    return x_rows, p_rows, t_rows, m_rows, s_rows, z_rows, stable_ids, summary


def deterministic_shuffle(values: list[float], label: str, perm_index: int) -> list[float]:
    shuffled = list(values)
    for index in range(len(shuffled) - 1, 0, -1):
        material = f"{EXPERIMENT_ID}|{label}|{perm_index}|{index}|{len(shuffled)}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        shuffled[index], shuffled[swap_index] = shuffled[swap_index], shuffled[index]
    return shuffled


def decomposition(
    *,
    x_tilde: list[list[float]],
    p_tilde: list[list[float]],
    t_tilde: list[list[float]],
    m_tilde: list[list[float]],
    s_tilde: list[list[float]],
) -> dict[str, object]:
    tm_tilde = append_columns(t_tilde, m_tilde)
    tms_tilde = append_columns(tm_tilde, s_tilde)
    xs_tilde = append_columns(x_tilde, s_tilde)
    xtm_tilde = append_columns(x_tilde, tm_tilde)
    xtms_tilde = append_columns(x_tilde, tms_tilde)

    r2_qp, explained_qp, rank_x = r2_from_design(x_tilde, p_tilde)
    r2_qp_given_s, explained_qp_given_s, rank_xs, rank_s = incremental_r2(
        full_design=xs_tilde,
        base_design=s_tilde,
        response=p_tilde,
    )
    r2_qp_given_tm, explained_qp_given_tm, rank_xtm, rank_tm = incremental_r2(
        full_design=xtm_tilde,
        base_design=tm_tilde,
        response=p_tilde,
    )
    r2_qp_given_tms, explained_qp_given_tms, rank_xtms, rank_tms = incremental_r2(
        full_design=xtms_tilde,
        base_design=tms_tilde,
        response=p_tilde,
    )
    r2_sq_structure, explained_sq_structure, rank_x_to_s = r2_from_design(x_tilde, s_tilde)

    structure_only = fraction(r2_qp - r2_qp_given_s, r2_qp)
    structure_incremental = fraction(r2_qp_given_tm - r2_qp_given_tms, r2_qp)
    return {
        "R2_QP": r2_qp,
        "R2_QP_given_S": r2_qp_given_s,
        "R2_QP_given_T_M": r2_qp_given_tm,
        "R2_QP_given_T_M_S": r2_qp_given_tms,
        "R2_absorbed_by_S": r2_qp - r2_qp_given_s,
        "R2_absorbed_by_S_beyond_T_M": r2_qp_given_tm - r2_qp_given_tms,
        "structure_only_fraction": structure_only,
        "structure_incremental_fraction": structure_incremental,
        "S_Q_structure_R2": r2_sq_structure,
        "rank_diagnostics": {
            "rank_Xtilde": rank_x,
            "rank_Stilde": rank_s,
            "rank_TMtilde": rank_tm,
            "rank_TMStilde": rank_tms,
            "rank_XStilde": rank_xs,
            "rank_XTMtilde": rank_xtm,
            "rank_XTMStilde": rank_xtms,
            "rank_X_to_S": rank_x_to_s,
            "p_residual_energy": frobenius2(p_tilde),
            "t_residual_energy": frobenius2(t_tilde),
            "m_residual_energy": frobenius2(m_tilde),
            "s_residual_energy": frobenius2(s_tilde),
            "X_explained_energy_on_P": explained_qp,
            "X_direct_improvement_energy_given_S": explained_qp_given_s,
            "X_direct_improvement_energy_given_T_M": explained_qp_given_tm,
            "X_direct_improvement_energy_given_T_M_S": explained_qp_given_tms,
            "X_explained_energy_on_S": explained_sq_structure,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
    }


def permutation_null(
    *,
    x_tilde: list[list[float]],
    p_tilde: list[list[float]],
    t_tilde: list[list[float]],
    m_tilde: list[list[float]],
    s_tilde: list[list[float]],
    observed: dict[str, object],
    count: int,
) -> dict[str, object]:
    s_col = matrix_column(s_tilde, 0)
    observed_incremental = float(observed["structure_incremental_fraction"])
    observed_sq = float(observed["S_Q_structure_R2"])
    observed_r2_qp = float(observed["R2_QP"])
    observed_r2_qp_given_tm = float(observed["R2_QP_given_T_M"])

    tm_tilde = append_columns(t_tilde, m_tilde)
    exceed_incremental = 0
    exceed_sq = 0
    incremental_values: list[float] = []
    sq_values: list[float] = []
    direct_tms_values: list[float] = []

    for perm_index in range(count):
        perm_s_tilde = [[value] for value in deterministic_shuffle(s_col, "structure_residual_permutation", perm_index)]
        tms_perm = append_columns(tm_tilde, perm_s_tilde)
        xtms_perm = append_columns(x_tilde, tms_perm)
        perm_r2_qp_given_tms, _explained, _rank_full, _rank_base = incremental_r2(
            full_design=xtms_perm,
            base_design=tms_perm,
            response=p_tilde,
        )
        perm_incremental = fraction(observed_r2_qp_given_tm - perm_r2_qp_given_tms, observed_r2_qp)
        perm_sq, _sq_explained, _sq_rank = r2_from_design(x_tilde, perm_s_tilde)
        if not math.isfinite(perm_incremental) or not math.isfinite(perm_sq):
            raise ValueError("permutation produced non-finite structure null statistic")
        incremental_values.append(perm_incremental)
        sq_values.append(perm_sq)
        direct_tms_values.append(perm_r2_qp_given_tms)
        if perm_incremental >= observed_incremental:
            exceed_incremental += 1
        if perm_sq >= observed_sq:
            exceed_sq += 1

    incremental_sorted = sorted(incremental_values)
    sq_sorted = sorted(sq_values)
    direct_sorted = sorted(direct_tms_values)
    p95_index = max(0, min(count - 1, math.ceil(0.95 * count) - 1)) if count else 0
    return {
        "permutation_count": count,
        "null_model": "deterministic row permutation of residualized 5-prime CDS MFE within the Z-orthogonal residual df; one-column structure mediator df is preserved",
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|structure_residual_permutation|perm_index|index|n",
        "structure_incremental_fraction": {
            "p_value_right_tail": (exceed_incremental + 1) / (count + 1),
            "null_mean": sum(incremental_values) / count if count else 0.0,
            "null_p95": incremental_sorted[p95_index] if incremental_sorted else 0.0,
            "null_min_seen": incremental_sorted[0] if incremental_sorted else 0.0,
            "null_max_seen": incremental_sorted[-1] if incremental_sorted else 0.0,
        },
        "S_Q_structure_R2": {
            "p_value_right_tail": (exceed_sq + 1) / (count + 1),
            "null_mean": sum(sq_values) / count if count else 0.0,
            "null_p95": sq_sorted[p95_index] if sq_sorted else 0.0,
            "null_min_seen": sq_sorted[0] if sq_sorted else 0.0,
            "null_max_seen": sq_sorted[-1] if sq_sorted else 0.0,
        },
        "R2_QP_given_T_M_permuted_S": {
            "null_mean": sum(direct_tms_values) / count if count else 0.0,
            "null_min_seen": direct_sorted[0] if direct_sorted else 0.0,
            "null_max_seen": direct_sorted[-1] if direct_sorted else 0.0,
        },
    }


def conclusion(observed: dict[str, object], permutation: dict[str, object]) -> dict[str, object]:
    inc_null = permutation["structure_incremental_fraction"]
    sq_null = permutation["S_Q_structure_R2"]
    if not isinstance(inc_null, dict) or not isinstance(sq_null, dict):
        raise ValueError("missing permutation null blocks")

    structure_only = float(observed["structure_only_fraction"])
    structure_incremental = float(observed["structure_incremental_fraction"])
    sq_r2 = float(observed["S_Q_structure_R2"])
    inc_above_null = (
        structure_incremental > float(inc_null["null_p95"])
        and float(inc_null["p_value_right_tail"]) <= SIGNIFICANCE_ALPHA
        and structure_incremental > 0.0
    )
    sq_above_null = (
        sq_r2 > float(sq_null["null_p95"])
        and float(sq_null["p_value_right_tail"]) <= SIGNIFICANCE_ALPHA
        and sq_r2 > 0.0
    )

    if inc_above_null:
        redundancy_call = "non_redundant_beyond_TE_stability"
        redundancy_statement = "5-prime CDS MFE explains additional B*_Q6-to-abundance residual variance beyond measured-TE plus mRNA-stability in this variance partition."
    elif abs(structure_incremental) <= max(0.01, abs(float(inc_null["null_p95"]))):
        redundancy_call = "redundant_with_TE_stability_or_too_small"
        redundancy_statement = "The additional structure term beyond measured-TE plus mRNA-stability is approximately zero or within the permutation null scale."
    else:
        redundancy_call = "positive_but_not_null_exceeding"
        redundancy_statement = "The structure term is positive but does not pass the fixed right-tail permutation rule."

    if structure_only > 0.0:
        mediation_call = "positive_structure_mediation_fraction"
    else:
        mediation_call = "negative_or_zero_structure_mediation_fraction"

    return {
        "structure_mediation": mediation_call,
        "structure_only_fraction": structure_only,
        "structure_beyond_TE_stability": redundancy_call,
        "structure_beyond_TE_stability_statement": redundancy_statement,
        "structure_incremental_above_null": inc_above_null,
        "S_Q_structure_above_null": sq_above_null,
        "S_Q_structure_statement": "B*_Q6 residual coordinates predict residualized 5-prime CDS MFE above the permutation null."
        if sq_above_null
        else "B*_Q6 residual coordinates do not exceed the permutation null for residualized 5-prime CDS MFE.",
        "decision_rule": f"called above null only if observed > null_p95 and right-tail p <= {SIGNIFICANCE_ALPHA}",
        "cannot_claim_short": "CDS-only MFE proxy; sequence-derived; variance partition only, not causal pathway proof",
    }


def analyze(repo: pathlib.Path, context: dict[str, object]) -> dict[str, object]:
    required = [repo / CDS_PATH, repo / TE_PATH, repo / MRNA_PATH, repo / STRUCTURE_PATH]
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        return {"status": "needs_data", "reason": f"missing local required data: {missing}", "cannot_claim": cannot_claim()}

    cds_payload, te_payload, mrna_payload, structure_payload = [load_json(path) for path in required]
    if not all(isinstance(payload, dict) for payload in [cds_payload, te_payload, mrna_payload, structure_payload]):
        raise ValueError("all input payloads must be JSON objects")

    x_rows, p_rows, t_rows, m_rows, s_rows, z_rows, stable_ids, data_summary = five_way_rows(
        cds_payload=cds_payload,
        te_payload=te_payload,
        mrna_payload=mrna_payload,
        structure_payload=structure_payload,
        context=context,
    )
    n_joined = len(x_rows)
    if n_joined < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"five-way join yielded n={n_joined}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "n_joined": n_joined,
            "data_summary": data_summary,
            "cannot_claim": cannot_claim(),
        }

    x_tilde, rank_z = residualize(x_rows, z_rows)
    p_tilde, _ = residualize(p_rows, z_rows)
    t_tilde, _ = residualize(t_rows, z_rows)
    m_tilde, _ = residualize(m_rows, z_rows)
    s_tilde, _ = residualize(s_rows, z_rows)
    residual_df = n_joined - rank_z

    observed = decomposition(x_tilde=x_tilde, p_tilde=p_tilde, t_tilde=t_tilde, m_tilde=m_tilde, s_tilde=s_tilde)
    permutation = permutation_null(
        x_tilde=x_tilde,
        p_tilde=p_tilde,
        t_tilde=t_tilde,
        m_tilde=m_tilde,
        s_tilde=s_tilde,
        observed=observed,
        count=PERMUTATION_COUNT,
    )
    core_conclusion = conclusion(observed, permutation)
    rank_diag = observed["rank_diagnostics"]
    inc_null = permutation["structure_incremental_fraction"]
    sq_null = permutation["S_Q_structure_R2"]
    if not isinstance(rank_diag, dict) or not isinstance(inc_null, dict) or not isinstance(sq_null, dict):
        raise ValueError("missing diagnostics")

    computed_ok = (
        finite_unit(observed["R2_QP"])
        and finite_unit(observed["R2_QP_given_S"])
        and finite_unit(observed["R2_QP_given_T_M"])
        and finite_unit(observed["R2_QP_given_T_M_S"])
        and finite_unit(observed["S_Q_structure_R2"])
        and float(observed["R2_QP"]) > SURVIVAL_EPS
        and float(observed["R2_QP"]) < DEGENERATE_R2
        and all(
            finite(observed[key])
            and abs(float(observed[key])) <= 10.0
            for key in ["structure_only_fraction", "structure_incremental_fraction"]
        )
        and int(rank_diag["rank_Xtilde"]) == len(context["q_names"])
        and int(rank_diag["rank_Stilde"]) == 1
        and int(rank_diag["rank_TMtilde"]) == 2
        and int(rank_diag["rank_TMStilde"]) == 3
        and int(rank_diag["rank_XTMStilde"]) == len(context["q_names"]) + 3
        and float(rank_diag["p_residual_energy"]) > SURVIVAL_EPS
        and float(rank_diag["t_residual_energy"]) > SURVIVAL_EPS
        and float(rank_diag["m_residual_energy"]) > SURVIVAL_EPS
        and float(rank_diag["s_residual_energy"]) > SURVIVAL_EPS
        and int(permutation["permutation_count"]) == PERMUTATION_COUNT
        and finite_unit(inc_null["p_value_right_tail"])
        and finite_unit(sq_null["p_value_right_tail"])
    )

    return {
        "organism": ORGANISM_LABEL,
        "organism_key": ORGANISM_KEY,
        "status": "computed" if computed_ok else "failed",
        "readout_P": "log10(abundance_ppm)",
        "readout_T": "log10(measured TE), TE = ribosome footprint / mRNA",
        "readout_M": "mRNA half-life minutes from Neymotin et al 2014 yeast 4tU dataset, unlogged per task definition",
        "readout_S": "precomputed five_prime_mfe_kcal_mol for first 39nt CDS window",
        "n_joined": n_joined,
        "stable_id_count": len(stable_ids),
        "data_summary": data_summary,
        "coordinates": context["q_names"],
        "R2_QP": observed["R2_QP"],
        "R2_QP_given_S": observed["R2_QP_given_S"],
        "R2_QP_given_T_M": observed["R2_QP_given_T_M"],
        "R2_QP_given_T_M_S": observed["R2_QP_given_T_M_S"],
        "structure_only_fraction": observed["structure_only_fraction"],
        "structure_incremental_fraction": observed["structure_incremental_fraction"],
        "S_Q_structure_R2": observed["S_Q_structure_R2"],
        "permutation_p_structure_incremental_right_tail": inc_null["p_value_right_tail"],
        "permutation_p_S_Q_structure_right_tail": sq_null["p_value_right_tail"],
        "permutation_null": permutation,
        "core_conclusion": core_conclusion,
        "rank_diagnostics": {
            **rank_diag,
            "rank_Z": rank_z,
            "residual_df_after_Z": residual_df,
            "control_column_count": len(z_rows[0]) if z_rows else 0,
        },
        "controls_used": controls_used(context["aa_order"]),
        "cannot_claim": cannot_claim(),
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        genetic_code_path = repo / "tools/bio_reality/data/ncbi_genetic_codes.json"
        if not genetic_code_path.exists():
            emit("needs_data", reason="missing local required genetic code data", missing_required_data=[str(genetic_code_path.relative_to(repo))])

        context = q6_context(repo)
        result = analyze(repo, context)
        status = "passed" if result.get("status") == "computed" else str(result.get("status", "failed"))

        checks = [
            {
                "name": "five_way_join",
                "passed": result.get("status") == "computed" and int(result.get("n_joined", 0)) >= MIN_PROTEINS_PER_ORGANISM,
                "actual": {
                    "status": result.get("status"),
                    "n_joined": result.get("n_joined"),
                    "data_summary": result.get("data_summary"),
                },
                "expected": f"CDS, abundance, measured-TE, mRNA half-life, and 5-prime structure join n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": (
                    len(context["q_names"]) == 9
                    and (
                        result.get("status") != "computed"
                        or (
                            isinstance(result.get("rank_diagnostics"), dict)
                            and int(result["rank_diagnostics"]["rank_Z"]) > 0
                            and int(result["rank_diagnostics"]["control_column_count"]) == 24
                            and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * (len(context["q_names"]) + 3)
                        )
                    )
                ),
                "actual": {
                    "coordinates": context["q_names"],
                    "coordinate_count": len(context["q_names"]),
                    "rank_diagnostics": result.get("rank_diagnostics"),
                    "controls_used": controls_used(context["aa_order"]),
                },
                "expected": "same 9 B*_Q6 coordinates and 24 controls Z: intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "single_and_joint_r2_computed",
                "passed": (
                    result.get("status") == "computed"
                    and finite_unit(result.get("R2_QP"))
                    and finite_unit(result.get("R2_QP_given_S"))
                    and finite_unit(result.get("R2_QP_given_T_M"))
                    and finite_unit(result.get("R2_QP_given_T_M_S"))
                    and float(result["R2_QP"]) > SURVIVAL_EPS
                    and float(result["R2_QP"]) < DEGENERATE_R2
                ),
                "actual": {
                    "R2_QP": result.get("R2_QP"),
                    "R2_QP_given_S": result.get("R2_QP_given_S"),
                    "R2_QP_given_T_M": result.get("R2_QP_given_T_M"),
                    "R2_QP_given_T_M_S": result.get("R2_QP_given_T_M_S"),
                },
                "expected": "finite R2_QP, R2_QP|S, R2_QP|T,M, and R2_QP|T,M,S in [0,1]",
            },
            {
                "name": "structure_incremental_and_sq_structure_computed",
                "passed": (
                    result.get("status") == "computed"
                    and finite(result.get("structure_only_fraction"))
                    and finite(result.get("structure_incremental_fraction"))
                    and abs(float(result["structure_only_fraction"])) <= 10.0
                    and abs(float(result["structure_incremental_fraction"])) <= 10.0
                    and finite_unit(result.get("S_Q_structure_R2"))
                    and finite_unit(result.get("permutation_p_structure_incremental_right_tail"))
                    and finite_unit(result.get("permutation_p_S_Q_structure_right_tail"))
                    and isinstance(result.get("permutation_null"), dict)
                    and bool(result["permutation_null"].get("deterministic_seed"))
                ),
                "actual": {
                    "structure_only_fraction": result.get("structure_only_fraction"),
                    "structure_incremental_fraction": result.get("structure_incremental_fraction"),
                    "S_Q_structure_R2": result.get("S_Q_structure_R2"),
                    "permutation_p_structure_incremental_right_tail": result.get("permutation_p_structure_incremental_right_tail"),
                    "permutation_p_S_Q_structure_right_tail": result.get("permutation_p_S_Q_structure_right_tail"),
                    "deterministic_seed": result.get("permutation_null", {}).get("deterministic_seed")
                    if isinstance(result.get("permutation_null"), dict)
                    else None,
                },
                "expected": "finite structure fractions, S^Q-structure R2, and reproducible deterministic 1000-permutation null",
            },
            {
                "name": "no_causal_or_structure_overclaim",
                "passed": cannot_claim() == [
                    "5' coding-region MFE is a CDS-only structure proxy (no 5'UTR)",
                    "minimum-free-energy single-structure estimate, not ensemble",
                    "structure is sequence-derived, partially GC-correlated; controlled-Z mediation mitigates but does not fully isolate",
                    "not a measured translation-initiation rate",
                    "single organism (yeast), single datasets per readout",
                    "statistical variance-partition, NOT causal pathway proof",
                ],
                "actual": cannot_claim(),
                "expected": "required CDS-only proxy, sequence-derived, non-initiation-rate, single-dataset, and non-causal cautions are present verbatim",
            },
        ]

        if status == "failed":
            emit("failed", checks=checks, result=result, reason="structure mediation computation failed an internal honesty gate")

        emit(
            status,
            reason=None if status == "passed" else result.get("reason"),
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "B*_Q6 to protein-abundance residual association is decomposed by conditioning on residualized 5-prime CDS MFE alone and beyond residualized measured-TE plus mRNA-stability; this is a statistical variance partition, not causal pathway evidence.",
                "decomposition_definition": "R2_QP is R2(P_e ~ Q_e) after Z residualization. R2_QP|S, R2_QP|T,M, and R2_QP|T,M,S are incremental R2 values for Q_e after conditioning on residualized structure, measured-TE plus mRNA-stability, or all three. structure_only_fraction=(R2_QP-R2_QP|S)/R2_QP. structure_incremental_fraction=(R2_QP|T,M-R2_QP|T,M,S)/R2_QP. S_Q_structure_R2 is R2(S_e ~ Q_e).",
                "organism": result,
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable yeast structure mediation input or fit")


if __name__ == "__main__":
    main()

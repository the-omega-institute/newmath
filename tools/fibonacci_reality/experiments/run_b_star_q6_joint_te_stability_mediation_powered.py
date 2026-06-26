#!/usr/bin/env python3
"""Joint measured-TE plus mRNA-stability mediation for B*_Q6 abundance residuals.

This is an observational variance-partition experiment. It does not establish
causal codon-to-TE, codon-to-stability, or downstream abundance mechanisms.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_mrna_half_life_sqm_ecoli_powered import (
    PRIMARY_GROWTH_RATE as ECOLI_PRIMARY_GROWTH_RATE,
    half_life_by_gene_id as ecoli_half_life_by_gene_id,
)
from run_b_star_q6_mrna_half_life_sqm_human_powered import (
    consensus_indices as human_consensus_indices,
    normalize_ensembl_gene_id,
    parse_cds_gene_keys,
)
from run_b_star_q6_mrna_half_life_sqm_powered import (
    half_life_by_syst as yeast_half_life_by_syst,
    yeast_orf_from_protein_id,
)
from run_b_star_q6_protein_omics_survival_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    SURVIVAL_EPS,
    codon_counts_rna,
    controls_used,
    frobenius2,
    matrix_column,
    normed_coordinate,
    numeric,
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


EXPERIMENT_ID = "b_star_q6_joint_te_stability_mediation_powered"
CLAIM_ID = "h3.cross_layer_relation.joint_te_stability_mediation.b_star_q6_abundance_residual_powered"
CONJECTURE_ID = "q6.joint-te-stability-mediation.abundance-residual.cross-layer"

PERMUTATION_COUNT = 1000
SIGNIFICANCE_ALPHA = 0.05

ORGANISMS = [
    {
        "key": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
        "domain": "eukaryote",
        "cds_path": "tools/fibonacci_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json",
        "te_path": "tools/fibonacci_reality/data/ribosome_te_saccharomyces_cerevisiae.json",
        "mrna_path": "tools/fibonacci_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
        "half_life_dataset": "Neymotin et al 2014 yeast 4tU mRNA half-life",
        "readout_M": "log10(thalf minutes)",
    },
    {
        "key": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
        "domain": "prokaryote",
        "cds_path": "tools/fibonacci_reality/data/cds_codon_abundance_escherichia_coli_k12_mg1655.json",
        "te_path": "tools/fibonacci_reality/data/ribosome_te_escherichia_coli_k12_mg1655.json",
        "mrna_path": "tools/fibonacci_reality/data/mrna_half_life_escherichia_coli_esquerre.json",
        "half_life_dataset": "Esquerre et al 2015 E.coli mRNA half-life at growth rate 0.40 h-1",
        "readout_M": "log10(half-life minutes at growth rate 0.40 h-1)",
    },
    {
        "key": "homo_sapiens",
        "label": "Homo sapiens",
        "domain": "eukaryote",
        "cds_path": "tools/fibonacci_reality/data/cds_codon_abundance_homo_sapiens.json",
        "te_path": "tools/fibonacci_reality/data/ribosome_te_homo_sapiens.json",
        "mrna_path": "tools/fibonacci_reality/data/mrna_half_life_homo_sapiens_agarwal_consensus.json",
        "half_life_dataset": "Agarwal and Kelley 2022 human consensus relative mRNA half-life",
        "readout_M": "unlogged mean normalized relative mRNA half-life consensus",
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
        "statistical variance-partition mediation, NOT causal pathway proof",
        "per-organism single datasets (abundance/TE/half-life from different studies, platform/condition differ)",
        "observational; cannot establish causation",
        "mediation fractions are variance partitions not mechanisms",
        "measured-TE and half-life are themselves noisy estimates",
        "cross-domain comparison is descriptive, not phylogenetically controlled",
    ]


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    aa_order = standard_amino_acids(code, codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
    return {
        "code": code,
        "codons": codons,
        "aa_order": aa_order,
        "q_projected": q_projected,
        "q_names": list(q_projected),
        "q_support": q_support,
    }


def protein_id_suffix(protein_id: str, taxid: str) -> str | None:
    prefix = f"{taxid}."
    if protein_id.startswith(prefix):
        return protein_id[len(prefix):]
    return None


def human_header_keys(header: str) -> tuple[str | None, str | None]:
    ensg, symbol = parse_cds_gene_keys(header)
    return ensg, symbol


def human_te_gene_key(value: str) -> str:
    text = value.strip()
    if text.startswith("ENSG"):
        return normalize_ensembl_gene_id(text)
    return text.upper()


def te_indices(payload: dict[str, object], organism_key: str) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism_key} TE payload must contain genes list")

    by_protein: dict[str, dict[str, float]] = {}
    by_gene: dict[str, dict[str, float]] = {}
    gene_buckets: dict[str, list[dict[str, float]]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "missing_gene_key": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna": 0,
        "nonpositive_footprint": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        gene_key = item.get("gene_key")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if not isinstance(gene_key, str) or not gene_key:
            skipped["missing_gene_key"] += 1
            continue
        te = numeric(item.get("te"), f"{organism_key}.genes[{row_index}].te")
        mrna = numeric(item.get("mrna"), f"{organism_key}.genes[{row_index}].mrna")
        footprint = numeric(item.get("footprint"), f"{organism_key}.genes[{row_index}].footprint")
        if te <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        if mrna <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue
        if footprint <= 0.0:
            skipped["nonpositive_footprint"] += 1
            continue
        record = {"te": te, "mrna": mrna, "footprint": footprint}
        if protein_id in by_protein:
            skipped["duplicate_protein_id"] += 1
        else:
            by_protein[protein_id] = record
        normalized_gene = human_te_gene_key(gene_key) if organism_key == "homo_sapiens" else gene_key
        gene_buckets.setdefault(normalized_gene, []).append(record)

    for gene_key, bucket in gene_buckets.items():
        if len(bucket) == 1:
            by_gene[gene_key] = bucket[0]

    return by_protein, by_gene, {
        "n_genes_with_te_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "n_valid_te_by_protein": len(by_protein),
        "n_unique_te_gene_keys": len(by_gene),
        "n_ambiguous_te_gene_keys": sum(1 for bucket in gene_buckets.values() if len(bucket) > 1),
        "skipped_te_records": skipped,
    }


def yeast_mrna_index(payload: dict[str, object]) -> tuple[dict[str, float], dict[str, object]]:
    raw, summary = yeast_half_life_by_syst(payload)
    return {key: float(value["thalf"]) for key, value in raw.items()}, summary


def ecoli_mrna_index(payload: dict[str, object]) -> tuple[dict[str, float], dict[str, object]]:
    raw, summary = ecoli_half_life_by_gene_id(payload, ECOLI_PRIMARY_GROWTH_RATE)
    return {key: float(value["half_life"]) for key, value in raw.items()}, summary


def human_mrna_indices(payload: dict[str, object]) -> tuple[dict[str, float], dict[str, float], dict[str, object]]:
    by_ensg, by_symbol, summary = human_consensus_indices(payload)
    ensg_index = {key: float(value["consensus_relative_half_life"]) for key, value in by_ensg.items()}
    symbol_index = {key: float(value["consensus_relative_half_life"]) for key, value in by_symbol.items()}
    return ensg_index, symbol_index, summary


def cds_rows_for_item(
    *,
    item: dict[str, object],
    row_index: int,
    organism_key: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[float], list[float]]:
    cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism_key}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        raise ValueError("invalid_length")

    counts = codon_counts_rna(item, codons, organism_key, row_index)
    total = sum(counts.values())
    if total <= 0:
        raise ValueError("empty_sense_codon_counts")

    frequencies = {codon: counts[codon] / total for codon in codons}
    x_row = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]

    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("empty_amino_acid_counts")

    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    z_row = [1.0, math.log(cds_len_nt)] + [aa_counts[aa] / aa_total for aa in aa_order] + [gc3, m_density]
    return x_row, z_row


def yeast_join_keys(item: dict[str, object]) -> tuple[str | None, str | None, str]:
    protein_id = item.get("protein_id")
    if not isinstance(protein_id, str) or not protein_id:
        return None, None, "missing_protein_id"
    orf = yeast_orf_from_protein_id(protein_id)
    if orf is None:
        return protein_id, None, "unparseable_yeast_orf"
    return protein_id, orf, ""


def ecoli_join_keys(item: dict[str, object]) -> tuple[str | None, str | None, str]:
    protein_id = item.get("protein_id")
    locus_tag = item.get("cds_match_id")
    if not isinstance(protein_id, str) or not protein_id:
        return None, None, "missing_protein_id"
    if not isinstance(locus_tag, str) or not locus_tag.startswith("b"):
        return protein_id, None, "missing_locus_tag"
    return protein_id, locus_tag, ""


def human_join_keys(item: dict[str, object]) -> tuple[str | None, str | None, str | None, str]:
    protein_id = item.get("protein_id")
    header = item.get("cds_header")
    if not isinstance(protein_id, str) or not protein_id:
        return None, None, None, "missing_protein_id"
    if not isinstance(header, str) or not header:
        return protein_id, None, None, "missing_cds_header"
    ensg, symbol = human_header_keys(header)
    if ensg is None and symbol is None:
        return protein_id, None, None, "missing_gene_keys"
    return protein_id, ensg, symbol, ""


def four_way_rows(
    *,
    organism_key: str,
    cds_payload: dict[str, object],
    te_payload: dict[str, object],
    mrna_payload: dict[str, object],
    context: dict[str, object],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[str], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism_key} CDS payload must contain joined list")

    te_by_protein, te_by_gene, te_summary = te_indices(te_payload, organism_key)
    if organism_key == "saccharomyces_cerevisiae":
        mrna_by_key, mrna_summary = yeast_mrna_index(mrna_payload)
    elif organism_key == "escherichia_coli_k12_mg1655":
        mrna_by_key, mrna_summary = ecoli_mrna_index(mrna_payload)
    elif organism_key == "homo_sapiens":
        mrna_by_ensg, mrna_by_symbol, mrna_summary = human_mrna_indices(mrna_payload)
    else:
        raise ValueError(f"unsupported organism {organism_key}")

    x_rows: list[list[float]] = []
    p_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    m_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    stable_ids: list[str] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "unparseable_yeast_orf": 0,
        "missing_locus_tag": 0,
        "missing_cds_header": 0,
        "missing_gene_keys": 0,
        "duplicate_stable_id": 0,
        "no_te_match": 0,
        "no_mrna_half_life_match": 0,
        "nonpositive_abundance": 0,
        "nonpositive_mrna_half_life": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    join_sources = {
        "te_protein_id": 0,
        "te_gene_key": 0,
        "mrna_primary_key": 0,
        "mrna_gene_symbol_fallback": 0,
    }
    seen: set[str] = set()

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue

        te_record: dict[str, float] | None = None
        mrna_value: float | None = None
        stable_id: str | None = None
        protein_id: str | None = None

        if organism_key == "saccharomyces_cerevisiae":
            protein_id, orf, error = yeast_join_keys(item)
            if error:
                skipped[error] += 1
                continue
            stable_id = str(orf)
            te_record = te_by_protein.get(str(protein_id))
            if te_record is None:
                te_record = te_by_gene.get(stable_id)
                if te_record is not None:
                    join_sources["te_gene_key"] += 1
            else:
                join_sources["te_protein_id"] += 1
            mrna_value = mrna_by_key.get(stable_id)
            if mrna_value is not None:
                join_sources["mrna_primary_key"] += 1
        elif organism_key == "escherichia_coli_k12_mg1655":
            protein_id, locus_tag, error = ecoli_join_keys(item)
            if error:
                skipped[error] += 1
                continue
            stable_id = str(locus_tag)
            te_record = te_by_protein.get(str(protein_id))
            if te_record is None:
                te_record = te_by_gene.get(stable_id)
                if te_record is not None:
                    join_sources["te_gene_key"] += 1
            else:
                join_sources["te_protein_id"] += 1
            mrna_value = mrna_by_key.get(stable_id)
            if mrna_value is not None:
                join_sources["mrna_primary_key"] += 1
        else:
            protein_id, ensg, symbol, error = human_join_keys(item)
            if error:
                skipped[error] += 1
                continue
            stable_id = ensg or f"symbol:{symbol}"
            te_record = te_by_protein.get(str(protein_id))
            if te_record is None and ensg is not None:
                te_record = te_by_gene.get(ensg)
                if te_record is not None:
                    join_sources["te_gene_key"] += 1
            elif te_record is not None:
                join_sources["te_protein_id"] += 1
            mrna_value = mrna_by_ensg.get(ensg) if ensg is not None else None
            if mrna_value is not None:
                join_sources["mrna_primary_key"] += 1
            elif symbol is not None:
                mrna_value = mrna_by_symbol.get(symbol)
                if mrna_value is not None:
                    join_sources["mrna_gene_symbol_fallback"] += 1

        if stable_id is None:
            skipped["missing_gene_keys"] += 1
            continue
        if stable_id in seen:
            skipped["duplicate_stable_id"] += 1
            continue
        if te_record is None:
            skipped["no_te_match"] += 1
            continue
        if mrna_value is None:
            skipped["no_mrna_half_life_match"] += 1
            continue
        if mrna_value <= 0.0:
            skipped["nonpositive_mrna_half_life"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism_key}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue

        try:
            x_row, z_row = cds_rows_for_item(
                item=item,
                row_index=row_index,
                organism_key=organism_key,
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
        if organism_key == "homo_sapiens":
            m_rows.append([mrna_value])
        else:
            m_rows.append([math.log10(mrna_value)])
        z_rows.append(z_row)
        stable_ids.append(stable_id)
        seen.add(stable_id)

    summary = {
        **te_summary,
        **{f"mrna_{key}": value for key, value in mrna_summary.items()},
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined": len(x_rows),
        "join_sources": join_sources,
        "skipped_cds_records": skipped,
    }
    return x_rows, p_rows, t_rows, m_rows, z_rows, stable_ids, summary


def deterministic_shuffle_pairs(
    t_values: list[float],
    m_values: list[float],
    organism_key: str,
    perm_index: int,
) -> tuple[list[float], list[float]]:
    pairs = list(zip(t_values, m_values))
    for index in range(len(pairs) - 1, 0, -1):
        material = f"{EXPERIMENT_ID}|{organism_key}|joint_tm_pair_permutation|{perm_index}|{index}|{len(pairs)}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        pairs[index], pairs[swap_index] = pairs[swap_index], pairs[index]
    return [pair[0] for pair in pairs], [pair[1] for pair in pairs]


def residual_vector_against_basis(vector: list[float], basis: list[list[float]]) -> list[float]:
    residual = list(vector)
    for q in basis:
        coeff = vector_dot(residual, q)
        for index in range(len(residual)):
            residual[index] -= coeff * q[index]
    return residual


def projection_energy_from_columns(columns: list[list[float]], target: list[float]) -> tuple[float, int]:
    design = [[column[row_index] for column in columns] for row_index in range(len(target))]
    response = [[value] for value in target]
    r2, explained, rank = r2_from_design(design, response)
    _ = r2
    return explained, rank


def fraction(numerator: float, denominator: float) -> float:
    if abs(denominator) <= SURVIVAL_EPS:
        return 0.0
    return numerator / denominator


def classify_overlap(joint_fraction: float, te_fraction: float, stability_fraction: float) -> dict[str, object]:
    additive = te_fraction + stability_fraction
    gap = additive - joint_fraction
    tolerance = 0.05 * max(1.0, abs(additive), abs(joint_fraction))
    if gap > tolerance:
        mode = "overlap"
        statement = "joint mediation is below the sum of the single-mediator fractions, so the two mediators overlap in this variance partition."
    elif abs(gap) <= tolerance:
        mode = "approximately_independent"
        statement = "joint mediation is close to the sum of the single-mediator fractions within the fixed descriptive tolerance."
    else:
        mode = "suppression_or_synergy"
        statement = "joint mediation exceeds the sum of the single-mediator fractions, consistent with suppression or joint-only structure in this variance partition."
    return {
        "mode": mode,
        "single_mediator_sum": additive,
        "joint_minus_single_sum": joint_fraction - additive,
        "descriptive_tolerance": tolerance,
        "statement": statement,
    }


def decomposition(
    *,
    x_tilde: list[list[float]],
    p_tilde: list[list[float]],
    t_tilde: list[list[float]],
    m_tilde: list[list[float]],
) -> dict[str, object]:
    tm_tilde = append_columns(t_tilde, m_tilde)
    xt_tilde = append_columns(x_tilde, t_tilde)
    xm_tilde = append_columns(x_tilde, m_tilde)
    xtm_tilde = append_columns(x_tilde, tm_tilde)

    r2_qp, explained_qp, rank_x = r2_from_design(x_tilde, p_tilde)
    r2_qp_given_t, explained_qp_given_t, rank_xt, rank_t = incremental_r2(
        full_design=xt_tilde,
        base_design=t_tilde,
        response=p_tilde,
    )
    r2_qp_given_m, explained_qp_given_m, rank_xm, rank_m = incremental_r2(
        full_design=xm_tilde,
        base_design=m_tilde,
        response=p_tilde,
    )
    r2_qp_given_tm, explained_qp_given_tm, rank_xtm, rank_tm = incremental_r2(
        full_design=xtm_tilde,
        base_design=tm_tilde,
        response=p_tilde,
    )
    r2_t_to_p, explained_t, _ = r2_from_design(t_tilde, p_tilde)
    r2_m_to_p, explained_m, _ = r2_from_design(m_tilde, p_tilde)
    r2_tm_to_p, explained_tm, _ = r2_from_design(tm_tilde, p_tilde)

    te_only = fraction(r2_qp - r2_qp_given_t, r2_qp)
    stability_only = fraction(r2_qp - r2_qp_given_m, r2_qp)
    joint = fraction(r2_qp - r2_qp_given_tm, r2_qp)
    unexplained = 1.0 - joint
    return {
        "R2_QP": r2_qp,
        "R2_QP_given_T": r2_qp_given_t,
        "R2_QP_given_M": r2_qp_given_m,
        "R2_QP_given_T_M": r2_qp_given_tm,
        "R2_absorbed_by_T": r2_qp - r2_qp_given_t,
        "R2_absorbed_by_M": r2_qp - r2_qp_given_m,
        "R2_absorbed_by_T_M": r2_qp - r2_qp_given_tm,
        "joint_mediation_fraction": joint,
        "TE_only_fraction": te_only,
        "stability_only_fraction": stability_only,
        "unexplained_fraction_after_joint_TE_stability": unexplained,
        "overlap": classify_overlap(joint, te_only, stability_only),
        "mediator_R2_to_P": {
            "R2_T_to_P": r2_t_to_p,
            "R2_M_to_P": r2_m_to_p,
            "R2_T_M_to_P": r2_tm_to_p,
        },
        "rank_diagnostics": {
            "rank_Xtilde": rank_x,
            "rank_Ttilde": rank_t,
            "rank_Mtilde": rank_m,
            "rank_TMtilde": rank_tm,
            "rank_XTtilde": rank_xt,
            "rank_XMtilde": rank_xm,
            "rank_XTMtilde": rank_xtm,
            "p_residual_energy": frobenius2(p_tilde),
            "t_residual_energy": frobenius2(t_tilde),
            "m_residual_energy": frobenius2(m_tilde),
            "X_explained_energy_on_P": explained_qp,
            "X_direct_improvement_energy_given_T": explained_qp_given_t,
            "X_direct_improvement_energy_given_M": explained_qp_given_m,
            "X_direct_improvement_energy_given_T_M": explained_qp_given_tm,
            "T_explained_energy_on_P": explained_t,
            "M_explained_energy_on_P": explained_m,
            "T_M_explained_energy_on_P": explained_tm,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
    }


def permutation_null(
    *,
    organism_key: str,
    x_tilde: list[list[float]],
    p_tilde: list[list[float]],
    t_tilde: list[list[float]],
    m_tilde: list[list[float]],
    observed_fraction: float,
    observed_r2_qp: float,
    count: int,
) -> dict[str, object]:
    t_col = matrix_column(t_tilde, 0)
    m_col = matrix_column(m_tilde, 0)
    p_col = matrix_column(p_tilde, 0)
    p_ss = vector_dot(p_col, p_col)
    x_basis = orthonormal_basis_from_columns(x_tilde)
    x_explained = observed_r2_qp * p_ss
    exceed = 0
    fractions: list[float] = []
    direct_values: list[float] = []

    for perm_index in range(count):
        perm_t_col, perm_m_col = deterministic_shuffle_pairs(t_col, m_col, organism_key, perm_index)
        base_explained, _rank = projection_energy_from_columns([perm_t_col, perm_m_col], p_col)
        t_perp_x = residual_vector_against_basis(perm_t_col, x_basis)
        m_perp_x = residual_vector_against_basis(perm_m_col, x_basis)
        mediator_perp_explained, _ = projection_energy_from_columns([t_perp_x, m_perp_x], p_col)
        full_explained = x_explained + mediator_perp_explained
        perm_direct = max(0.0, min(1.0, max(0.0, full_explained - base_explained) / p_ss)) if p_ss > SURVIVAL_EPS else 0.0
        perm_fraction = fraction(observed_r2_qp - perm_direct, observed_r2_qp)
        if not math.isfinite(perm_fraction):
            raise ValueError(f"{organism_key} permutation produced non-finite joint mediation fraction")
        fractions.append(perm_fraction)
        direct_values.append(perm_direct)
        if perm_fraction >= observed_fraction:
            exceed += 1

    fractions_sorted = sorted(fractions)
    directs_sorted = sorted(direct_values)
    p95_index = max(0, min(len(fractions_sorted) - 1, math.ceil(0.95 * len(fractions_sorted)) - 1))
    return {
        "permutation_count": count,
        "null_model": "deterministic row permutation of the residualized (measured-TE, mRNA-stability) two-column mediator pair within the Z-orthogonal residual df; preserves TE/stability covariance and mediator df=2",
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|{organism_key}|joint_tm_pair_permutation|perm_index|index|n",
        "observed_R2_QP_fixed": observed_r2_qp,
        "joint_mediation_fraction": {
            "p_value_right_tail": (exceed + 1) / (count + 1),
            "null_mean": sum(fractions) / count if count else 0.0,
            "null_p95": fractions_sorted[p95_index] if fractions_sorted else 0.0,
            "null_min_seen": fractions_sorted[0] if fractions_sorted else 0.0,
            "null_max_seen": fractions_sorted[-1] if fractions_sorted else 0.0,
        },
        "R2_QP_given_permuted_T_M": {
            "null_mean": sum(direct_values) / count if count else 0.0,
            "null_min_seen": directs_sorted[0] if directs_sorted else 0.0,
            "null_max_seen": directs_sorted[-1] if directs_sorted else 0.0,
        },
    }


def conclusion_for_organism(result: dict[str, object], permutation: dict[str, object]) -> dict[str, object]:
    null = permutation["joint_mediation_fraction"]
    if not isinstance(null, dict):
        raise ValueError("permutation result lacks joint_mediation_fraction")
    fraction_value = float(result["joint_mediation_fraction"])
    p_value = float(null["p_value_right_tail"])
    null_p95 = float(null["null_p95"])
    above_null = p_value <= SIGNIFICANCE_ALPHA and fraction_value > null_p95
    if above_null and fraction_value > 0.0:
        strength = "joint_statistical_mediation_above_null"
    elif fraction_value > 0.0:
        strength = "positive_but_not_null_exceeding"
    else:
        strength = "negative_or_suppression_result"
    return {
        "joint_mediation_above_null": above_null,
        "strength": strength,
        "decision_rule": f"joint mediation is called only if joint_mediation_fraction > null_p95 and permutation p <= {SIGNIFICANCE_ALPHA}",
        "remaining_unexplained_fraction": result["unexplained_fraction_after_joint_TE_stability"],
        "overlap_mode": result["overlap"]["mode"] if isinstance(result.get("overlap"), dict) else "unavailable",
        "cannot_claim_short": "variance partition only; not causal pathway proof",
    }


def organism_needs_data(config: dict[str, object], reason: str, summary: object | None = None) -> dict[str, object]:
    return {
        "organism": config["label"],
        "organism_key": config["key"],
        "domain": config["domain"],
        "status": "needs_data",
        "reason": reason,
        "data_summary": summary,
        "cannot_claim": cannot_claim(),
    }


def analyze_organism(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    required = [repo / str(config["cds_path"]), repo / str(config["te_path"]), repo / str(config["mrna_path"])]
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        return organism_needs_data(config, f"missing local required data: {missing}")

    cds_payload = load_json(required[0])
    te_payload = load_json(required[1])
    mrna_payload = load_json(required[2])
    if not isinstance(cds_payload, dict) or not isinstance(te_payload, dict) or not isinstance(mrna_payload, dict):
        raise ValueError(f"{config['key']} input payloads must be JSON objects")

    x_rows, p_rows, t_rows, m_rows, z_rows, stable_ids, data_summary = four_way_rows(
        organism_key=str(config["key"]),
        cds_payload=cds_payload,
        te_payload=te_payload,
        mrna_payload=mrna_payload,
        context=context,
    )
    n_joined = len(x_rows)
    if n_joined < MIN_PROTEINS_PER_ORGANISM:
        return organism_needs_data(
            config,
            f"four-way join yielded n={n_joined}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            data_summary,
        )

    x_tilde, rank_z = residualize(x_rows, z_rows)
    p_tilde, _ = residualize(p_rows, z_rows)
    t_tilde, _ = residualize(t_rows, z_rows)
    m_tilde, _ = residualize(m_rows, z_rows)
    residual_df = n_joined - rank_z

    decomp = decomposition(x_tilde=x_tilde, p_tilde=p_tilde, t_tilde=t_tilde, m_tilde=m_tilde)
    permutation = permutation_null(
        organism_key=str(config["key"]),
        x_tilde=x_tilde,
        p_tilde=p_tilde,
        t_tilde=t_tilde,
        m_tilde=m_tilde,
        observed_fraction=float(decomp["joint_mediation_fraction"]),
        observed_r2_qp=float(decomp["R2_QP"]),
        count=PERMUTATION_COUNT,
    )
    conclusion = conclusion_for_organism(decomp, permutation)
    rank_diag = decomp["rank_diagnostics"]
    null = permutation["joint_mediation_fraction"]
    if not isinstance(rank_diag, dict) or not isinstance(null, dict):
        raise ValueError("missing diagnostics")

    computed_ok = (
        finite_unit(decomp["R2_QP"])
        and finite_unit(decomp["R2_QP_given_T"])
        and finite_unit(decomp["R2_QP_given_M"])
        and finite_unit(decomp["R2_QP_given_T_M"])
        and float(decomp["R2_QP"]) > SURVIVAL_EPS
        and float(decomp["R2_QP"]) < DEGENERATE_R2
        and all(finite(decomp[key]) for key in ["joint_mediation_fraction", "TE_only_fraction", "stability_only_fraction"])
        and all(abs(float(decomp[key])) <= 10.0 for key in ["joint_mediation_fraction", "TE_only_fraction", "stability_only_fraction"])
        and int(rank_diag["rank_Xtilde"]) == len(context["q_names"])
        and int(rank_diag["rank_Ttilde"]) == 1
        and int(rank_diag["rank_Mtilde"]) == 1
        and int(rank_diag["rank_TMtilde"]) == 2
        and int(rank_diag["rank_XTMtilde"]) == len(context["q_names"]) + 2
        and float(rank_diag["p_residual_energy"]) > SURVIVAL_EPS
        and float(rank_diag["t_residual_energy"]) > SURVIVAL_EPS
        and float(rank_diag["m_residual_energy"]) > SURVIVAL_EPS
        and int(permutation["permutation_count"]) == PERMUTATION_COUNT
        and finite_unit(null["p_value_right_tail"])
    )

    return {
        "organism": config["label"],
        "organism_key": config["key"],
        "domain": config["domain"],
        "status": "computed" if computed_ok else "failed",
        "half_life_dataset": config["half_life_dataset"],
        "readout_P": "log10(abundance_ppm)",
        "readout_T": "log10(measured TE), TE = ribosome footprint / mRNA",
        "readout_M": config["readout_M"],
        "n_joined": n_joined,
        "stable_id_count": len(stable_ids),
        "data_summary": data_summary,
        "coordinates": context["q_names"],
        "R2_QP": decomp["R2_QP"],
        "R2_QP_given_T": decomp["R2_QP_given_T"],
        "R2_QP_given_M": decomp["R2_QP_given_M"],
        "R2_QP_given_T_M": decomp["R2_QP_given_T_M"],
        "joint_mediation_fraction": decomp["joint_mediation_fraction"],
        "TE_only_fraction": decomp["TE_only_fraction"],
        "stability_only_fraction": decomp["stability_only_fraction"],
        "unexplained_fraction_after_joint_TE_stability": decomp["unexplained_fraction_after_joint_TE_stability"],
        "overlap": decomp["overlap"],
        "permutation_p_right_tail": null["p_value_right_tail"],
        "permutation_null": permutation,
        "core_conclusion": conclusion,
        "rank_diagnostics": {
            **rank_diag,
            "rank_Z": rank_z,
            "residual_df_after_Z": residual_df,
            "control_column_count": len(z_rows[0]) if z_rows else 0,
        },
        "controls_used": controls_used(context["aa_order"]),
        "cannot_claim": cannot_claim(),
    }


def domain_split_summary(organism_results: dict[str, dict[str, object]]) -> dict[str, object]:
    computed = {key: result for key, result in organism_results.items() if result.get("status") == "computed"}
    fractions = {
        key: float(result["joint_mediation_fraction"])
        for key, result in computed.items()
        if finite(result.get("joint_mediation_fraction"))
    }
    eukaryote = [
        float(result["joint_mediation_fraction"])
        for result in computed.values()
        if result.get("domain") == "eukaryote" and finite(result.get("joint_mediation_fraction"))
    ]
    prokaryote = [
        float(result["joint_mediation_fraction"])
        for result in computed.values()
        if result.get("domain") == "prokaryote" and finite(result.get("joint_mediation_fraction"))
    ]
    euk_mean = sum(eukaryote) / len(eukaryote) if eukaryote else None
    prok_mean = sum(prokaryote) / len(prokaryote) if prokaryote else None
    if euk_mean is None or prok_mean is None:
        pattern = "insufficient_computed_domains"
        statement = "At least one domain lacks a computed organism, so domain split is not evaluated."
    else:
        diff = euk_mean - prok_mean
        if abs(diff) < 0.05:
            pattern = "no_clear_eukaryote_prokaryote_split"
            statement = "The descriptive eukaryote mean and prokaryote value differ by less than 0.05 joint-mediation fraction."
        elif diff > 0.0:
            pattern = "descriptive_eukaryote_higher_than_prokaryote"
            statement = "The descriptive eukaryote mean joint-mediation fraction is higher than the prokaryote value."
        else:
            pattern = "descriptive_prokaryote_higher_than_eukaryote"
            statement = "The descriptive prokaryote joint-mediation fraction is higher than the eukaryote mean."
    return {
        "joint_mediation_fraction_by_organism": fractions,
        "eukaryote_mean_joint_mediation_fraction": euk_mean,
        "prokaryote_mean_joint_mediation_fraction": prok_mean,
        "pattern": pattern,
        "statement": statement,
        "caveat": "descriptive cross-domain comparison only; not phylogenetically controlled",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        if not genetic_code_path.exists():
            emit("needs_data", missing_required_data=[str(genetic_code_path.relative_to(repo))])

        context = q6_context(repo)
        q_names = context["q_names"]
        organism_results = {
            str(config["key"]): analyze_organism(repo, context, config)
            for config in ORGANISMS
        }
        computed = {key: result for key, result in organism_results.items() if result.get("status") == "computed"}
        failed = {key: result for key, result in organism_results.items() if result.get("status") == "failed"}
        needs_data = {key: result for key, result in organism_results.items() if result.get("status") == "needs_data"}
        cross_domain = domain_split_summary(organism_results)

        checks = [
            {
                "name": "four_way_join_per_organism",
                "passed": bool(computed) and all(int(result["n_joined"]) >= MIN_PROTEINS_PER_ORGANISM for result in computed.values()),
                "actual": {
                    key: {
                        "status": result.get("status"),
                        "n_joined": result.get("n_joined"),
                        "data_summary": result.get("data_summary"),
                    }
                    for key, result in organism_results.items()
                },
                "expected": f">=1 organism with CDS, abundance, measured-TE, and mRNA-stability four-way join n >= {MIN_PROTEINS_PER_ORGANISM}; organisms below gate are needs_data",
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
                            and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * (len(q_names) + 2)
                        )
                        for result in organism_results.values()
                    )
                ),
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "computed_rank_diagnostics": {
                        key: result.get("rank_diagnostics")
                        for key, result in computed.items()
                    },
                    "controls_used": controls_used(context["aa_order"]),
                },
                "expected": "same 9 B*_Q6 coordinates and 24 controls Z: intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "single_and_joint_r2_computed",
                "passed": (
                    bool(computed)
                    and not failed
                    and all(
                        finite_unit(result.get("R2_QP"))
                        and finite_unit(result.get("R2_QP_given_T"))
                        and finite_unit(result.get("R2_QP_given_M"))
                        and finite_unit(result.get("R2_QP_given_T_M"))
                        and float(result["R2_QP"]) > SURVIVAL_EPS
                        and float(result["R2_QP"]) < DEGENERATE_R2
                        for result in computed.values()
                    )
                ),
                "actual": {
                    key: {
                        "R2_QP": result.get("R2_QP"),
                        "R2_QP_given_T": result.get("R2_QP_given_T"),
                        "R2_QP_given_M": result.get("R2_QP_given_M"),
                        "R2_QP_given_T_M": result.get("R2_QP_given_T_M"),
                    }
                    for key, result in computed.items()
                },
                "expected": "finite R2_QP, R2_QP|T, R2_QP|M, and R2_QP|T,M in [0,1]",
            },
            {
                "name": "joint_mediation_and_overlap_computed",
                "passed": (
                    bool(computed)
                    and all(
                        finite(result.get("joint_mediation_fraction"))
                        and finite(result.get("TE_only_fraction"))
                        and finite(result.get("stability_only_fraction"))
                        and abs(float(result["joint_mediation_fraction"])) <= 10.0
                        and abs(float(result["TE_only_fraction"])) <= 10.0
                        and abs(float(result["stability_only_fraction"])) <= 10.0
                        and isinstance(result.get("overlap"), dict)
                        and result["overlap"].get("mode") in {"overlap", "approximately_independent", "suppression_or_synergy"}
                        and finite_unit(result.get("permutation_p_right_tail"))
                        and isinstance(result.get("permutation_null"), dict)
                        and result["permutation_null"].get("deterministic_seed")
                        for result in computed.values()
                    )
                ),
                "actual": {
                    key: {
                        "joint_mediation_fraction": result.get("joint_mediation_fraction"),
                        "TE_only_fraction": result.get("TE_only_fraction"),
                        "stability_only_fraction": result.get("stability_only_fraction"),
                        "overlap": result.get("overlap"),
                        "permutation_p_right_tail": result.get("permutation_p_right_tail"),
                        "deterministic_seed": result.get("permutation_null", {}).get("deterministic_seed")
                        if isinstance(result.get("permutation_null"), dict)
                        else None,
                    }
                    for key, result in computed.items()
                },
                "expected": "finite fractions, descriptive overlap classification, and reproducible deterministic 1000-permutation null",
            },
            {
                "name": "no_causal_overclaim",
                "passed": cannot_claim() == [
                    "statistical variance-partition mediation, NOT causal pathway proof",
                    "per-organism single datasets (abundance/TE/half-life from different studies, platform/condition differ)",
                    "observational; cannot establish causation",
                    "mediation fractions are variance partitions not mechanisms",
                    "measured-TE and half-life are themselves noisy estimates",
                    "cross-domain comparison is descriptive, not phylogenetically controlled",
                ],
                "actual": cannot_claim(),
                "expected": "required non-causal, variance-partition, noisy-readout, descriptive cross-domain cautions are present verbatim",
            },
        ]

        status = "passed" if computed and not failed else "needs_data"
        reason = None if status == "passed" else "no organism passed the honest four-way join and joint mediation computation gates"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "B*_Q6 to protein-abundance residual association is decomposed per organism by conditioning on residualized measured-TE, residualized mRNA-stability, and both mediators jointly; this is a statistical variance partition, not causal pathway evidence.",
                "decomposition_definition": "R2_QP is R2(P_e ~ Q_e) after Z residualization. R2_QP|T, R2_QP|M, and R2_QP|T,M are incremental R2 values for Q_e after conditioning on residualized measured-TE, mRNA-stability, or both. joint_mediation_fraction=(R2_QP-R2_QP|T,M)/R2_QP.",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py and Z controls matched to S^QP/S^QM",
                "organisms": organism_results,
                "computed_organism_count": len(computed),
                "needs_data_organisms": sorted(needs_data),
                "cross_domain_joint_mediation_comparison": cross_domain,
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable joint TE plus mRNA-stability mediation input or fit")


if __name__ == "__main__":
    main()

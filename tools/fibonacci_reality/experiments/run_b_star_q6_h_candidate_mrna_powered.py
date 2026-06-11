#!/usr/bin/env python3
"""mRNA as an H-candidate for the modeled-tAI complement residual.

This is a descriptive statistical projection audit. It tests whether measured
ribo-seq mRNA absorbs the B*_Q6 abundance component left after modeled tAI, not
a causal mediation or mechanism claim.
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_measured_mediation_powered import abundance_by_protein
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import (
    RIDGE_EPS,
    complement_decomposition,
    condition_number_from_gram,
    gram_matrix,
    project_onto_design,
    subtract_vectors,
    vector_norm2,
)
from run_b_star_q6_translation_mediation_powered import (
    MIN_PROTEINS_PER_ORGANISM,
    controls_used,
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


EXPERIMENT_ID = "b_star_q6_h_candidate_mrna_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_mrna.b_star_q6_abundance_residual_powered"
CONJECTURE_ID = "q6.h-candidate-mrna.abundance-residual.cross-layer"

ORGANISM_PAIRS = [
    {"organism": "saccharomyces_cerevisiae", "trna_organism": "saccharomyces_cerevisiae"},
    {"organism": "escherichia_coli_k12_mg1655", "trna_organism": "escherichia_coli"},
    {"organism": "homo_sapiens", "trna_organism": "homo_sapiens"},
    {"organism": "danio_rerio", "trna_organism": "danio_rerio"},
]

ABSORPTION_LABEL_THRESHOLD = 0.30
SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if not math.isfinite(value):
        return value
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def finite_unit_interval(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)) and 0.0 <= float(value) <= 1.0


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0 or int(value) != value:
                raise ValueError(f"{organism}.joined[{row_index}].codon_counts.{raw_codon} must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def mrna_by_protein(payload: dict[str, object], organism: str) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} ribosome readout payload must contain genes list")
    out: dict[str, dict[str, float]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "nonpositive_mrna": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        mrna = numeric(item.get("mrna"), f"{organism}.genes[{row_index}].mrna")
        if mrna <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue
        if protein_id in out:
            skipped["duplicate_protein_id"] += 1
            continue
        out[protein_id] = {"mrna": mrna}
    return out, {
        "n_genes_with_mrna_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "mrna_definition": "positive mrna field from local ribosome_te organism payload",
        "study_ref": payload.get("study_ref"),
        "n_valid_mrna_by_protein": len(out),
        "skipped_mrna_records": skipped,
    }


def h_candidate_rows(
    *,
    cds_payload: dict[str, object],
    ribosome_payload: dict[str, object],
    abundance_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    mrna_index, mrna_summary = mrna_by_protein(ribosome_payload, organism)
    abundance_index, abundance_summary = abundance_by_protein(abundance_payload, organism)

    x_rows: list[list[float]] = []
    t_mod_rows: list[list[float]] = []
    m_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_mrna_match": 0,
        "no_abundance_match": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        mrna_record = mrna_index.get(protein_id)
        if mrna_record is None:
            skipped["no_mrna_match"] += 1
            continue
        abundance = abundance_index.get(protein_id)
        if abundance is None:
            skipped["no_abundance_match"] += 1
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
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_mod_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
        m_rows.append([math.log10(mrna_record["mrna"])])
        y_rows.append([math.log10(abundance)])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )

    summary = {
        **mrna_summary,
        **abundance_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined_all_readouts": len(x_rows),
        "skipped_cds_records": skipped,
    }
    return x_rows, t_mod_rows, m_rows, y_rows, z_rows, summary


def h_candidate_decomposition(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    m_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    absorbed_vector, mrna_coeff = project_onto_design(m_tilde, p_q_perp_tmod)
    combined_design = append_columns(t_mod_tilde, m_tilde)
    p_q_from_combined, combined_coeff = project_onto_design(combined_design, p_q)
    p_q_perp_combined = subtract_vectors(p_q, p_q_from_combined)

    p_q_norm2 = vector_norm2(p_q)
    p_q_perp_tmod_norm2 = vector_norm2(p_q_perp_tmod)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    p_q_perp_combined_norm2 = vector_norm2(p_q_perp_combined)
    d_modeled = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_tmod_norm2 / p_q_norm2)
    absorbed_by_mrna = None if p_q_perp_tmod_norm2 <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / p_q_perp_tmod_norm2)
    d_combined = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_combined_norm2 / p_q_norm2)

    return {
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": p_q_perp_tmod_norm2,
        "P_Q_perp_Tmod_absorbed_by_mRNA_norm2": absorbed_norm2,
        "P_Q_perp_combined_norm2": p_q_perp_combined_norm2,
        "d_modeled": d_modeled,
        "absorbed_by_mRNA": absorbed_by_mrna,
        "d_combined": d_combined,
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
            "mRNA_on_P_Q_perp_Tmod": mrna_coeff,
            "Tmod_mRNA_on_P_Q": combined_coeff,
        },
    }


def interpretation_label(absorbed_by_mrna: float | None) -> str:
    if absorbed_by_mrna is None:
        return "no_modeled_complement_energy_to_classify"
    if absorbed_by_mrna >= ABSORPTION_LABEL_THRESHOLD:
        return "residual_is_transcript_level"
    return "residual_beyond_transcript"


def cannot_claim() -> list[str]:
    return [
        "statistical projection not causal",
        "mRNA from same ribo-seq dataset, condition-specific",
        "absorbed high != causal transcript mechanism; low != H found",
        "if low, residual is beyond transcript+translation - needs turnover/localization (fetch)",
    ]


def conclusion_from_absorption(absorptions: list[float]) -> dict[str, object]:
    high = [value for value in absorptions if value >= ABSORPTION_LABEL_THRESHOLD]
    low = [value for value in absorptions if value < ABSORPTION_LABEL_THRESHOLD]
    if len(high) == len(absorptions):
        consistency = "consistently_high"
        verdict = "mRNA is a plausible H candidate for this residual in this descriptive projection"
        residual_read = "the modeled-tAI complement residual is mostly compatible with a transcript-level readout"
    elif len(low) == len(absorptions):
        consistency = "consistently_low"
        verdict = "mRNA is not sufficient as H for this residual"
        residual_read = "the residual remains beyond transcript plus modeled translation in this descriptive projection"
    else:
        consistency = "mixed"
        verdict = "mRNA is not a stable standalone H across organisms"
        residual_read = "some residual is compatible with transcript level, but the cross-organism pattern is not consistent"
    return {
        "threshold_for_descriptive_label_only": ABSORPTION_LABEL_THRESHOLD,
        "high_count": len(high),
        "low_count": len(low),
        "consistency": consistency,
        "mRNA_H_candidate_conclusion": verdict,
        "abundance_residual_conclusion": residual_read,
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        organism = pair["organism"]
        trna_organism = pair["trna_organism"]
        required.append(f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{trna_organism}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local mRNA, modeled tAI, PAXdb abundance, and CDS codon data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        per_organism: dict[str, object] = {}
        input_actual: dict[str, object] = {}
        alignment_actual: dict[str, object] = {}
        absorption_values: list[float] = []
        all_joined_ok = True
        all_residualized_ok = True
        all_complement_ok = True
        all_absorption_ok = True
        all_alignment_ok = True

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            ribosome_payload = load_json(repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
            abundance_payload = load_json(repo / f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
            if not isinstance(cds_payload, dict) or not isinstance(ribosome_payload, dict) or not isinstance(abundance_payload, dict):
                raise ValueError(f"{organism} payloads must be JSON objects")

            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            x_rows, t_mod_rows, m_rows, y_rows, z_rows, data_summary = h_candidate_rows(
                cds_payload=cds_payload,
                ribosome_payload=ribosome_payload,
                abundance_payload=abundance_payload,
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
                raise ValueError(f"{organism} has no usable proteins after mRNA x modeled tAI x abundance x codon join")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            t_mod_tilde, _ = residualize(t_mod_rows, z_rows)
            m_tilde, _ = residualize(m_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            decomposition = h_candidate_decomposition(
                x_tilde=x_tilde,
                t_mod_tilde=t_mod_tilde,
                m_tilde=m_tilde,
                y_tilde=y_tilde,
            )

            full_x_rows, full_t_rows, full_y_rows, full_z_rows, _ = protein_rows(
                payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
            )
            full_x_tilde, full_rank_z = residualize(full_x_rows, full_z_rows)
            full_t_tilde, _ = residualize(full_t_rows, full_z_rows)
            full_y_tilde, _ = residualize(full_y_rows, full_z_rows)
            complement_reference = complement_decomposition(
                x_tilde=full_x_tilde,
                t_tilde=full_t_tilde,
                y_tilde=full_y_tilde,
                q_names=q_names,
            )

            d_modeled = decomposition["d_modeled"]
            absorbed = decomposition["absorbed_by_mRNA"]
            d_combined = decomposition["d_combined"]
            d_reference = complement_reference["d"]
            d_difference = None
            d_matches = False
            if isinstance(d_modeled, float) and isinstance(d_reference, float):
                d_difference = abs(d_modeled - d_reference)
                d_matches = d_difference < MODELED_ALIGNMENT_TOL

            x_rank = explained_by_design(x_tilde, y_tilde)[1]
            t_mod_rank = explained_by_design(t_mod_tilde, y_tilde)[1]
            mrna_rank = explained_by_design(m_tilde, y_tilde)[1]
            combined_rank = explained_by_design(append_columns(t_mod_tilde, m_tilde), y_tilde)[1]
            residual_df = n_proteins - rank_z

            organism_joined_ok = n_proteins >= MIN_PROTEINS_PER_ORGANISM
            organism_residualized_ok = (
                rank_z > 0
                and len(x_tilde) == n_proteins
                and len(t_mod_tilde) == n_proteins
                and len(m_tilde) == n_proteins
                and len(y_tilde) == n_proteins
            )
            organism_complement_ok = finite_unit_interval(d_modeled)
            organism_absorption_ok = finite_unit_interval(absorbed) and finite_unit_interval(d_combined)

            all_joined_ok = all_joined_ok and organism_joined_ok
            all_residualized_ok = all_residualized_ok and organism_residualized_ok
            all_complement_ok = all_complement_ok and organism_complement_ok
            all_absorption_ok = all_absorption_ok and organism_absorption_ok
            all_alignment_ok = all_alignment_ok and d_matches
            if isinstance(absorbed, float):
                absorption_values.append(absorbed)

            input_actual[organism] = {
                "n": n_proteins,
                "n_valid_mrna_by_protein": data_summary["n_valid_mrna_by_protein"],
                "n_valid_abundance_by_protein": data_summary["n_valid_abundance_by_protein"],
                "n_cds_joined_reported": data_summary["n_cds_joined_reported"],
                "rank_Z": rank_z,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
            }
            alignment_actual[organism] = {
                "d_modeled_current_all_readout_join": d_modeled,
                "d_modeled_complement_experiment_reference_full_abundance_cds_join": d_reference,
                "absolute_difference": d_difference,
                "matches_within_0_02": d_matches,
                "current_join_n": n_proteins,
                "complement_reference_join_n": len(full_x_rows),
                "interpretation_if_failed": "negative self-check: mRNA availability changes the protein_id join used by the H-candidate projection",
            }

            per_organism[organism] = {
                **data_summary,
                **tai_summary,
                "n": n_proteins,
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_difference,
                "d_modeled_matches_complement_experiment_within_0_02": d_matches,
                "absorbed_by_mRNA": absorbed,
                "d_combined": d_combined,
                "interpretation_label": interpretation_label(absorbed if isinstance(absorbed, float) else None),
                "interpretation_label_threshold_descriptive_only": ABSORPTION_LABEL_THRESHOLD,
                "norms": {
                    "P_Q_norm2": decomposition["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": decomposition["P_Q_perp_Tmod_norm2"],
                    "P_Q_perp_Tmod_absorbed_by_mRNA_norm2": decomposition["P_Q_perp_Tmod_absorbed_by_mRNA_norm2"],
                    "P_Q_perp_combined_norm2": decomposition["P_Q_perp_combined_norm2"],
                },
                "rank_condition_diagnostics": {
                    "rank_Q_e": x_rank,
                    "rank_Tmod": t_mod_rank,
                    "rank_mRNA": mrna_rank,
                    "rank_Tmod_mRNA": combined_rank,
                    "rank_Z": rank_z,
                    "reference_full_join_rank_Z": full_rank_z,
                    "residual_df_after_Z": residual_df,
                    "q_coordinate_count": len(q_names),
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "ridge_epsilon": RIDGE_EPS,
                    "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                    "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                    "condition_number_mRNA_gram": condition_number_from_gram(gram_matrix(m_tilde)),
                    "condition_number_Tmod_mRNA_gram": condition_number_from_gram(gram_matrix(append_columns(t_mod_tilde, m_tilde))),
                },
            }

        conclusion = conclusion_from_absorption(absorption_values)
        checks = [
            {
                "name": "inputs_joined",
                "passed": all_joined_ok and len(per_organism) == len(ORGANISM_PAIRS),
                "actual": input_actual,
                "expected": f"4 organisms with n >= {MIN_PROTEINS_PER_ORGANISM} after mRNA x modeled tAI x PAXdb abundance x CDS protein_id join",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": len(q_names) == 9 and all_residualized_ok,
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "controls_used": controls_used(aa_order),
                    "per_organism": input_actual,
                },
                "expected": "Q_e, T_mod, M_e, and P_e residualized against the same Z controls",
            },
            {
                "name": "modeled_complement_computed",
                "passed": all_complement_ok,
                "actual": {
                    organism: {
                        "d_modeled": result["d_modeled"],
                        "P_Q_norm2": result["norms"]["P_Q_norm2"],
                        "P_Q_perp_Tmod_norm2": result["norms"]["P_Q_perp_Tmod_norm2"],
                    }
                    for organism, result in per_organism.items()
                    if isinstance(result, dict)
                },
                "expected": "finite P_hat_{Q perp Tmod} with d_modeled in [0,1]",
            },
            {
                "name": "d_modeled_matches_complement_experiment",
                "passed": all_alignment_ok,
                "actual": alignment_actual,
                "expected": f"|d_current_join - d_complement_reference_full_join| < {MODELED_ALIGNMENT_TOL}",
                "interpretation_if_failed": "reported honestly; the H-candidate projection uses the mRNA protein_id intersection, while the upstream complement experiment used the full abundance/CDS join",
            },
            {
                "name": "mrna_absorption_computed",
                "passed": all_absorption_ok,
                "actual": {
                    organism: {
                        "absorbed_by_mRNA": result["absorbed_by_mRNA"],
                        "d_combined": result["d_combined"],
                    }
                    for organism, result in per_organism.items()
                    if isinstance(result, dict)
                },
                "expected": "absorbed_by_mRNA and d_combined are finite values in [0,1]",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {
                    "passed": True,
                    "cannot_claim": cannot_claim(),
                },
                "expected": "statistical projection only; no causal or mechanism promotion",
            },
        ]

        status = "passed" if all_joined_ok and all_residualized_ok and all_complement_ok and all_absorption_ok else "failed"
        reason = None
        if status == "passed" and not all_alignment_ok:
            reason = "computed on the mRNA all-readout join; d_modeled does not match the full-join complement reference within 0.02 for every organism"
        if status != "passed":
            reason = "one or more computation gates failed"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "mRNA is tested as an H-candidate by projecting the modeled-tAI complement abundance residual P_hat_{Q perp Tmod} onto residualized log10 mRNA.",
                "status_semantics": "passed means the descriptive projection quantities were computed and bounded; absorption high or low is reported without promotion to causality",
                "decomposition": {
                    "Q_e": "9 B*_Q6 residual coordinates after residualizing controls Z",
                    "T_mod": "residualized modeled per-protein tAI after controls Z",
                    "M_e": "residualized log10 mRNA after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "P_hat_Q": "Pi_{Q_e} P_e",
                    "P_hat_Q_perp_Tmod": "(I - Pi_{Tmod}) P_hat_Q",
                    "absorbed_by_mRNA": "||Pi_{M_e} P_hat_{Q perp Tmod}||^2 / ||P_hat_{Q perp Tmod}||^2",
                    "P_hat_Q_perp_Tmod_mRNA": "(I - Pi_{[Tmod,M_e]}) P_hat_Q",
                    "d_combined": "||P_hat_Q_perp_Tmod_mRNA||^2 / ||P_hat_Q||^2",
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "per_organism": per_organism,
                "cross_organism": {
                    "absorbed_by_mRNA_distribution": {
                        "values_by_organism": {
                            organism: result["absorbed_by_mRNA"]
                            for organism, result in per_organism.items()
                            if isinstance(result, dict)
                        },
                        "min": min(absorption_values) if absorption_values else None,
                        "max": max(absorption_values) if absorption_values else None,
                        "mean": mean(absorption_values),
                        "median": median(absorption_values),
                    },
                    **conclusion,
                    "ordered_by_absorbed_by_mRNA": sorted(
                        [
                            {
                                "organism": organism,
                                "absorbed_by_mRNA": float(result["absorbed_by_mRNA"]),
                                "d_modeled": float(result["d_modeled"]),
                                "d_combined": float(result["d_combined"]),
                                "interpretation_label": result["interpretation_label"],
                            }
                            for organism, result in per_organism.items()
                            if isinstance(result, dict)
                            and isinstance(result.get("absorbed_by_mRNA"), float)
                            and isinstance(result.get("d_modeled"), float)
                            and isinstance(result.get("d_combined"), float)
                        ],
                        key=lambda row: row["absorbed_by_mRNA"],
                        reverse=True,
                    ),
                },
                "honest": {
                    "cannot_claim": cannot_claim(),
                },
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable mRNA H-candidate input")


if __name__ == "__main__":
    main()

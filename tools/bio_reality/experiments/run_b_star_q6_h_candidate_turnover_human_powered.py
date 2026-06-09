#!/usr/bin/env python3
"""Human protein turnover as an H-candidate for the large modeled-tAI complement.

This is a descriptive statistical projection audit. It tests whether
Mathieson et al. 2018 human primary-cell protein half-life absorbs the
human B*_Q6 abundance component left after modeled tAI. It is not causal.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_h_candidate_measured_te_powered import (
    append_columns,
    bounded_unit,
    finite_unit_interval,
)
from run_b_star_q6_h_candidate_turnover_powered import turnover_by_protein
from run_b_star_q6_measured_mediation_powered import abundance_by_protein
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    orthonormal_basis_from_columns,
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
    codon_counts_rna,
    controls_used,
    load_json,
    modeled_tai_weights,
    normed_coordinate,
    numeric,
    protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_h_candidate_turnover_human_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_turnover_human.b_star_q6_large_residual_powered"
CONJECTURE_ID = "q6.h-candidate-turnover-human.large-residual.cross-layer"

ORGANISM = "homo_sapiens"
TRNA_ORGANISM = "homo_sapiens"
TURNOVER_DATA_RELATIVE_PATH = "tools/bio_reality/data/protein_turnover_homo_sapiens.json"

SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02
NULL_TRIALS = 200


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "Mathieson 2018 human primary cells, median across cell types",
        "absorbed fraction descriptive, not causal mediator",
        "modeled tAI complement readout for T",
        "if low, residual is beyond turnover even at large human residual - H deeper (condition-specific / complex dynamics)",
    ]


def file_sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [list(row) for row in matrix]
    width = len(matrix[0])
    for q in basis:
        for col in range(width):
            coeff = sum(matrix[row][col] * q[row] for row in range(len(matrix)))
            if coeff == 0.0:
                continue
            for row in range(len(matrix)):
                out[row][col] -= coeff * q[row]
    return out


def absorption_by_basis(design_tilde: list[list[float]], target: list[float]) -> dict[str, object]:
    basis = orthonormal_basis_from_columns(design_tilde)
    absorbed_vector = [0.0 for _ in target]
    for q in basis:
        coeff = sum(target[index] * q[index] for index in range(len(target)))
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            absorbed_vector[index] += coeff * q[index]
    denominator = vector_norm2(target)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    absorbed = None if denominator <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / denominator)
    return {
        "absorbed": absorbed,
        "absorbed_norm2": absorbed_norm2,
        "target_norm2": denominator,
        "rank": len(basis),
    }


def lcg_uniform(seed: int) -> tuple[int, float]:
    next_seed = (1664525 * seed + 1013904223) & 0xFFFFFFFF
    return next_seed, (next_seed + 0.5) / 4294967296.0


def deterministic_gaussian_matrix(*, trial: int, n_rows: int, k_cols: int) -> list[list[float]]:
    digest = hashlib.sha256(f"{EXPERIMENT_ID}|{ORGANISM}|{trial}".encode("utf-8")).digest()
    seed = int.from_bytes(digest[:4], "big")
    values: list[float] = []
    need = n_rows * k_cols
    while len(values) < need:
        seed, u1 = lcg_uniform(seed)
        seed, u2 = lcg_uniform(seed)
        u1 = max(u1, 1e-12)
        radius = math.sqrt(-2.0 * math.log(u1))
        angle = 2.0 * math.pi * u2
        values.append(radius * math.cos(angle))
        if len(values) < need:
            values.append(radius * math.sin(angle))
    return [values[row * k_cols:(row + 1) * k_cols] for row in range(n_rows)]


def dof_matched_null(
    *,
    n_rows: int,
    z_basis: list[list[float]],
    target: list[float],
    trials: int = NULL_TRIALS,
) -> dict[str, object]:
    absorptions: list[float] = []
    ranks: list[int] = []
    for trial in range(trials):
        raw = deterministic_gaussian_matrix(trial=trial, n_rows=n_rows, k_cols=1)
        null_tilde = residualize_with_basis(raw, z_basis)
        result = absorption_by_basis(null_tilde, target)
        absorbed = result["absorbed"]
        if not isinstance(absorbed, float):
            raise ValueError(f"null trial {trial} did not produce finite absorption")
        absorptions.append(absorbed)
        ranks.append(int(result["rank"]))
    return {
        "trial_count": trials,
        "absorbed_values": absorptions,
        "absorbed_null_mean": mean(absorptions),
        "absorbed_null_p95": percentile_nearest_rank(absorptions, 0.95),
        "rank_min": min(ranks) if ranks else None,
        "rank_max": max(ranks) if ranks else None,
        "rank_unique_values": sorted(set(ranks)),
        "randomness": "one deterministic hashlib-derived seed per trial, then LCG and Box-Muller; no system time",
    }


def human_turnover_rows(
    *,
    cds_payload: dict[str, object],
    turnover_payload: dict[str, object],
    abundance_payload: dict[str, object],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[str], list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("human CDS payload must contain joined list")
    turnover_index, turnover_summary = turnover_by_protein(turnover_payload)
    abundance_index, abundance_summary = abundance_by_protein(abundance_payload, ORGANISM)

    x_rows: list[list[float]] = []
    t_mod_rows: list[list[float]] = []
    t_turn_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    protein_ids: list[str] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_turnover_match": 0,
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
        half_life = turnover_index.get(protein_id)
        if half_life is None:
            skipped["no_turnover_match"] += 1
            continue
        abundance = abundance_index.get(protein_id)
        if abundance is None:
            skipped["no_abundance_match"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{ORGANISM}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, ORGANISM, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_mod_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
        t_turn_rows.append([math.log10(half_life)])
        y_rows.append([math.log10(abundance)])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{ORGANISM}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )
        protein_ids.append(protein_id)

    summary = {
        **turnover_summary,
        **abundance_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined_all_readouts": len(x_rows),
        "n_joined_turnover_abundance_cds": len(x_rows),
        "skipped_cds_records": skipped,
    }
    return protein_ids, x_rows, t_mod_rows, t_turn_rows, y_rows, z_rows, summary


def human_abundance_rows_with_ids(
    *,
    cds_payload: dict[str, object],
    abundance_payload: dict[str, object],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[str], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("human CDS payload must contain joined list")
    abundance_index, abundance_summary = abundance_by_protein(abundance_payload, ORGANISM)

    protein_ids: list[str] = []
    x_rows: list[list[float]] = []
    t_mod_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
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
        abundance = abundance_index.get(protein_id)
        if abundance is None:
            skipped["no_abundance_match"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{ORGANISM}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, ORGANISM, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_mod_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
        y_rows.append([math.log10(abundance)])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{ORGANISM}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )
        protein_ids.append(protein_id)

    summary = {
        **abundance_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined_abundance_cds": len(x_rows),
        "skipped_full_human_cds_records": skipped,
    }
    return protein_ids, x_rows, t_mod_rows, y_rows, z_rows, summary


def modeled_complement_target(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    p_q_norm2 = vector_norm2(p_q)
    p_q_perp_tmod_norm2 = vector_norm2(p_q_perp_tmod)
    return {
        "P_Q": p_q,
        "P_Q_perp_Tmod": p_q_perp_tmod,
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": p_q_perp_tmod_norm2,
        "d_modeled": None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_tmod_norm2 / p_q_norm2),
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
        },
    }


def h_candidate_decomposition(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    t_turn_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    turn_col = matrix_column(t_turn_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    absorbed_vector, tturn_coeff = project_onto_design(t_turn_tilde, p_q_perp_tmod)
    combined_design = append_columns(t_mod_tilde, t_turn_tilde)
    p_q_from_combined, combined_coeff = project_onto_design(combined_design, p_q)
    p_q_perp_combined = subtract_vectors(p_q, p_q_from_combined)
    p_tturn_from_q, q_to_tturn_coeff = project_onto_design(x_tilde, turn_col)

    p_q_norm2 = vector_norm2(p_q)
    p_q_perp_tmod_norm2 = vector_norm2(p_q_perp_tmod)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    p_q_perp_combined_norm2 = vector_norm2(p_q_perp_combined)
    tturn_norm2 = vector_norm2(turn_col)
    q_to_tturn_norm2 = vector_norm2(p_tturn_from_q)
    d_modeled = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_tmod_norm2 / p_q_norm2)
    absorbed_by_turnover = None if p_q_perp_tmod_norm2 <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / p_q_perp_tmod_norm2)
    d_combined = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_combined_norm2 / p_q_norm2)
    r2_q_tturn = None if tturn_norm2 <= SURVIVAL_EPS else bounded_unit(q_to_tturn_norm2 / tturn_norm2)

    return {
        "P_Q": p_q,
        "P_Q_perp_Tmod": p_q_perp_tmod,
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": p_q_perp_tmod_norm2,
        "P_Q_perp_Tmod_absorbed_by_Tturn_norm2": absorbed_norm2,
        "P_Q_perp_combined_norm2": p_q_perp_combined_norm2,
        "Tturn_norm2": tturn_norm2,
        "Q_to_Tturn_norm2": q_to_tturn_norm2,
        "d_modeled": d_modeled,
        "absorbed_by_turnover": absorbed_by_turnover,
        "d_combined": d_combined,
        "R2_Q_Tturn": r2_q_tturn,
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
            "Tturn_on_P_Q_perp_Tmod": tturn_coeff,
            "Tmod_Tturn_on_P_Q": combined_coeff,
            "Q_to_Tturn": q_to_tturn_coeff,
        },
    }


def conclusion(absorbed: float | None, null_p95: float | None) -> dict[str, object]:
    exceeds = isinstance(absorbed, float) and isinstance(null_p95, float) and absorbed > null_p95
    if absorbed is None or null_p95 is None:
        verdict = "protein turnover could not be classified"
        label = "no_modeled_complement_energy_to_classify"
    elif exceeds:
        verdict = "protein turnover is an H-candidate for the large human residual by this descriptive projection criterion"
        label = "turnover_exceeds_dof_matched_null"
    else:
        verdict = "protein turnover does not absorb the large human residual beyond the single-column dof-matched null"
        label = "turnover_no_better_than_dof_matched_null"
    return {
        "criterion": "turnover is called an H candidate only when absorbed_by_turnover > null_p95 for the same single-column residualized design",
        "absorbed_by_turnover": absorbed,
        "null_p95": null_p95,
        "exceeds_null": exceeds,
        "interpretation_label": label,
        "verdict": verdict,
        "noncausal_boundary": "projection signal, not causal mediation",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = [
        "tools/bio_reality/data/ncbi_genetic_codes.json",
        f"tools/bio_reality/data/proteomics_abundance_{ORGANISM}.json",
        f"tools/bio_reality/data/cds_codon_abundance_{ORGANISM}.json",
        f"tools/bio_reality/data/gtrnadb_trna_all_copy_{TRNA_ORGANISM}.json",
        TURNOVER_DATA_RELATIVE_PATH,
    ]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit(
            "needs_data",
            reason="required local human abundance, CDS, modeled tAI, or Mathieson turnover data not present",
            missing_required_data=missing,
            checks=[
                {
                    "name": "human_turnover_loaded",
                    "passed": False,
                    "actual": {"missing_required_data": missing},
                    "expected": "tools/bio_reality/data/protein_turnover_homo_sapiens.json exists and contains protein_turnover with n >= 500",
                },
                {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
            ],
        )

    try:
        turnover_path = repo / TURNOVER_DATA_RELATIVE_PATH
        turnover_payload = load_json(turnover_path)
        cds_payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{ORGANISM}.json")
        abundance_payload = load_json(repo / f"tools/bio_reality/data/proteomics_abundance_{ORGANISM}.json")
        if not isinstance(turnover_payload, dict) or not isinstance(turnover_payload.get("protein_turnover"), dict):
            emit(
                "needs_data",
                reason="local Mathieson human turnover data lacks protein_turnover map",
                checks=[
                    {"name": "human_turnover_loaded", "passed": False, "actual": {"path": TURNOVER_DATA_RELATIVE_PATH}, "expected": "protein_turnover JSON object"},
                    {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
                ],
            )
        if not isinstance(cds_payload, dict) or not isinstance(abundance_payload, dict):
            raise ValueError("human CDS and abundance payloads must be JSON objects")

        turnover_index, turnover_summary = turnover_by_protein(turnover_payload)
        turnover_file_sha = file_sha256(turnover_path)
        human_turnover_loaded_ok = len(turnover_index) >= MIN_PROTEINS_PER_ORGANISM
        print(
            "turnover_self_check "
            + json.dumps(
                {
                    "organism": ORGANISM,
                    "n_turnover_proteins": len(turnover_index),
                    "source_xlsx_sha256": turnover_payload.get("source_xlsx_sha256"),
                    "payload_sha256": turnover_payload.get("payload_sha256"),
                    "file_sha256": turnover_file_sha,
                },
                sort_keys=True,
            )
        )
        if not human_turnover_loaded_ok:
            emit(
                "needs_data",
                reason="Mathieson human turnover data yielded too few usable half-life rows",
                checks=[
                    {
                        "name": "human_turnover_loaded",
                        "passed": False,
                        "actual": {**turnover_summary, "file_sha256": turnover_file_sha},
                        "expected": f"human turnover n >= {MIN_PROTEINS_PER_ORGANISM}",
                    },
                    {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
                ],
            )

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        tai_weights, tai_summary = modeled_tai_weights(
            repo=repo,
            organism=ORGANISM,
            trna_organism=TRNA_ORGANISM,
            code=code,
            codons=codons,
        )
        full_protein_ids, full_x_rows, full_t_mod_rows, full_y_rows, full_z_rows, full_data_summary = human_abundance_rows_with_ids(
            cds_payload=cds_payload,
            abundance_payload=abundance_payload,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        full_z_basis = orthonormal_basis_from_columns(full_z_rows)
        full_rank_z = len(full_z_basis)
        full_x_tilde = residualize_with_basis(full_x_rows, full_z_basis)
        full_t_tilde = residualize_with_basis(full_t_mod_rows, full_z_basis)
        full_y_tilde = residualize_with_basis(full_y_rows, full_z_basis)
        full_target = modeled_complement_target(
            x_tilde=full_x_tilde,
            t_mod_tilde=full_t_tilde,
            y_tilde=full_y_tilde,
        )
        full_p_q_by_protein = dict(zip(full_protein_ids, full_target["P_Q"]))
        full_residual_by_protein = dict(zip(full_protein_ids, full_target["P_Q_perp_Tmod"]))

        protein_ids, x_rows, t_mod_rows, t_turn_rows, y_rows, z_rows, data_summary = human_turnover_rows(
            cds_payload=cds_payload,
            turnover_payload=turnover_payload,
            abundance_payload=abundance_payload,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        n_proteins = len(x_rows)
        print("join_self_check " + json.dumps({"organism": ORGANISM, "n_joined": n_proteins}, sort_keys=True))
        target = [full_residual_by_protein[protein_id] for protein_id in protein_ids]
        p_q_slice = [full_p_q_by_protein[protein_id] for protein_id in protein_ids]

        z_basis = orthonormal_basis_from_columns(z_rows)
        rank_z = len(z_basis)
        x_tilde = residualize_with_basis(x_rows, z_basis)
        t_mod_tilde = residualize_with_basis(t_mod_rows, z_basis)
        t_turn_tilde = residualize_with_basis(t_turn_rows, z_basis)
        y_tilde = residualize_with_basis(y_rows, z_basis)
        coverage_recomputed_decomposition = h_candidate_decomposition(
            x_tilde=x_tilde,
            t_mod_tilde=t_mod_tilde,
            t_turn_tilde=t_turn_tilde,
            y_tilde=y_tilde,
        )

        turnover_absorption_basis = absorption_by_basis(t_turn_tilde, target)
        absorbed_vector, tturn_coeff = project_onto_design(t_turn_tilde, target)
        remaining_after_turnover = subtract_vectors(target, absorbed_vector)
        target_norm2 = vector_norm2(target)
        p_q_slice_norm2 = vector_norm2(p_q_slice)
        absorbed_norm2 = vector_norm2(absorbed_vector)
        remaining_norm2 = vector_norm2(remaining_after_turnover)
        absorbed = None if target_norm2 <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / target_norm2)
        d_combined = None if p_q_slice_norm2 <= SURVIVAL_EPS else bounded_unit(remaining_norm2 / p_q_slice_norm2)

        turn_col = matrix_column(t_turn_tilde, 0)
        p_tturn_from_q, q_to_tturn_coeff = project_onto_design(x_tilde, turn_col)
        tturn_norm2 = vector_norm2(turn_col)
        q_to_tturn_norm2 = vector_norm2(p_tturn_from_q)
        r2_q_tturn = None if tturn_norm2 <= SURVIVAL_EPS else bounded_unit(q_to_tturn_norm2 / tturn_norm2)

        null = dof_matched_null(n_rows=n_proteins, z_basis=z_basis, target=target)
        complement_reference = complement_decomposition(
            x_tilde=full_x_tilde,
            t_tilde=full_t_tilde,
            y_tilde=full_y_tilde,
            q_names=q_names,
        )

        d_modeled = full_target["d_modeled"]
        absorbed_basis = turnover_absorption_basis["absorbed"]
        null_mean = null["absorbed_null_mean"]
        null_p95 = null["absorbed_null_p95"]
        d_reference = complement_reference["d"]
        d_difference = None
        d_matches = False
        if isinstance(d_modeled, float) and isinstance(d_reference, float):
            d_difference = abs(d_modeled - d_reference)
            d_matches = d_difference < MODELED_ALIGNMENT_TOL
        exceeds_null = isinstance(absorbed, float) and isinstance(null_p95, float) and absorbed > null_p95
        excess = absorbed - null_mean if isinstance(absorbed, float) and isinstance(null_mean, float) else None

        x_rank = explained_by_design(x_tilde, y_tilde)[1]
        t_mod_rank = explained_by_design(t_mod_tilde, y_tilde)[1]
        t_turn_rank = int(turnover_absorption_basis["rank"])
        combined_rank = explained_by_design(append_columns(t_mod_tilde, t_turn_tilde), y_tilde)[1]
        residual_df = n_proteins - rank_z

        joined_ok = n_proteins >= MIN_PROTEINS_PER_ORGANISM
        residualized_ok = rank_z > 0 and len(x_tilde) == n_proteins and len(t_mod_tilde) == n_proteins and len(t_turn_tilde) == n_proteins and len(y_tilde) == n_proteins
        complement_ok = finite_unit_interval(d_modeled)
        absorption_ok = finite_unit_interval(absorbed) and finite_unit_interval(absorbed_basis) and finite_unit_interval(d_combined)
        null_ok = isinstance(null_mean, float) and isinstance(null_p95, float) and 0.0 <= null_mean <= 1.0 and 0.0 <= null_p95 <= 1.0
        r2_ok = finite_unit_interval(r2_q_tturn)
        status = "passed" if human_turnover_loaded_ok and joined_ok and residualized_ok and complement_ok and absorption_ok and null_ok and r2_ok else "failed"

        turnover_provenance = {
            "source_kind": turnover_payload.get("source_kind"),
            "source_url": turnover_payload.get("source_url"),
            "source_xlsx_sha256": turnover_payload.get("source_xlsx_sha256"),
            "payload_sha256": turnover_payload.get("payload_sha256"),
            "file_sha256": turnover_file_sha,
            "payload_byte_size": turnover_payload.get("payload_byte_size"),
            "id_mapping_method": turnover_payload.get("id_mapping_method"),
            "turnover_transform_for_experiment": turnover_payload.get("turnover_transform_for_experiment"),
            "identified_orf_column": turnover_payload.get("identified_orf_column"),
            "identified_half_life_column": turnover_payload.get("identified_half_life_column"),
        }
        core_conclusion = conclusion(absorbed if isinstance(absorbed, float) else None, null_p95 if isinstance(null_p95, float) else None)

        checks = [
            {
                "name": "human_turnover_loaded",
                "passed": human_turnover_loaded_ok,
                "actual": {
                    **turnover_summary,
                    "n_valid_turnover_by_protein": len(turnover_index),
                    "source_xlsx_sha256": turnover_payload.get("source_xlsx_sha256"),
                    "payload_sha256": turnover_payload.get("payload_sha256"),
                    "file_sha256": turnover_file_sha,
                },
                "expected": f"protein_turnover_homo_sapiens JSON loaded, n >= {MIN_PROTEINS_PER_ORGANISM}, sha256 recorded",
            },
            {
                "name": "inputs_joined",
                "passed": joined_ok,
                "actual": {"n_joined": n_proteins, **data_summary},
                "expected": f"human n >= {MIN_PROTEINS_PER_ORGANISM} after turnover x modeled tAI x PAXdb abundance x CDS protein_id join",
            },
            {
                "name": "b_star_q6_residuals + controls_Z + modeled_complement",
                "passed": len(q_names) == 9 and residualized_ok and complement_ok,
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "controls_used": controls_used(aa_order),
                    "rank_Z": full_rank_z,
                    "control_column_count": len(full_z_rows[0]) if full_z_rows else 0,
                    "d_modeled": d_modeled,
                    "P_Q_norm2": full_target["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": full_target["P_Q_perp_Tmod_norm2"],
                    "full_human_join_n": len(full_x_rows),
                },
                "expected": "Q_e, T_mod, and P_e residualized against the same 24 control columns Z on the full human abundance-CDS join; modeled complement computed",
            },
            {
                "name": "d_modeled_matches_human_complement",
                "passed": d_matches,
                "actual": {
                    "d_modeled_current_full_human_join": d_modeled,
                    "d_modeled_complement_experiment_reference_full_abundance_cds_join": d_reference,
                    "absolute_difference": d_difference,
                    "matches_within_0_02": d_matches,
                    "current_join_n": n_proteins,
                    "complement_reference_join_n": len(full_x_rows),
                    "coverage_recomputed_d_modeled_diagnostic": coverage_recomputed_decomposition["d_modeled"],
                },
                "expected": f"human |d_current_full_join - d_complement_reference_full_join| < {MODELED_ALIGNMENT_TOL}",
                "interpretation_if_failed": "reported honestly; full human residual should align with the upstream complement experiment",
            },
            {
                "name": "turnover_absorption_computed",
                "passed": absorption_ok,
                "actual": {
                    "absorbed_by_turnover": absorbed,
                    "absorbed_by_turnover_basis_check": absorbed_basis,
                    "d_combined": d_combined,
                    "R2_Q_Tturn": r2_q_tturn,
                },
                "expected": "absorbed_by_turnover, d_combined, and basis cross-check are finite values in [0,1]",
            },
            {
                "name": "dof_null_computed",
                "passed": null_ok,
                "actual": {
                    "null_mean": null_mean,
                    "null_p95": null_p95,
                    "trial_count": null["trial_count"],
                    "rank_unique_values": null["rank_unique_values"],
                    "exceeds_null": exceeds_null,
                },
                "expected": f"{NULL_TRIALS} deterministic one-column Gaussian null projections residualized by Z",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {
                    "passed": True,
                    "cannot_claim": cannot_claim(),
                    "conclusion_noncausal_boundary": core_conclusion["noncausal_boundary"],
                },
                "expected": "statistical projection only; no causal or mechanism promotion",
            },
        ]

        reason = None
        if status == "failed":
            reason = "one or more computation gates failed"
        elif not d_matches:
            reason = "full human modeled-complement self-check did not match the complement experiment within 0.02"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "Mathieson 2018 human protein turnover is tested as an H-candidate by projecting the large human modeled-tAI complement abundance residual P_hat_{Q perp Tmod} onto residualized log10 half-life.",
                "status_semantics": "passed means the descriptive projection quantities and the dof-matched null were computed; absorption above the null 95th percentile is an H-candidate signal, not causality",
                "decomposition": {
                    "Q_e": "9 B*_Q6 residual coordinates after residualizing controls Z",
                    "T_mod": "residualized modeled per-protein tAI after controls Z",
                    "T_turn": "residualized log10(Mathieson 2018 half_life_hr) after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "P_hat_Q": "Pi_{Q_e} P_e",
                    "P_hat_Q_perp_Tmod": "(I - Pi_{Tmod}) P_hat_Q",
                    "absorbed_by_turnover": "||Pi_{Tturn} P_hat_{Q perp Tmod}||^2 / ||P_hat_{Q perp Tmod}||^2",
                    "dof_matched_null": "one-column deterministic Gaussian designs residualized by Z, projected onto the same P_hat_{Q perp Tmod}",
                    "d_combined": "||P_hat_Q - Pi_{[Tmod,Tturn]} P_hat_Q||^2 / ||P_hat_Q||^2",
                    "R2_Q_Tturn": "||Pi_{Q_e} T_turn||^2 / ||T_turn||^2 after controls Z",
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "human": {
                    **data_summary,
                    **tai_summary,
                    "n_joined": n_proteins,
                    "full_human_abundance_cds_join": {
                        **full_data_summary,
                        "n_joined": len(full_x_rows),
                        "rank_Z": full_rank_z,
                    },
                    "d_modeled": d_modeled,
                    "d_modeled_reference_from_complement_experiment": d_reference,
                    "d_modeled_reference_absolute_difference": d_difference,
                    "d_modeled_matches_human_complement_within_0_02": d_matches,
                    "coverage_recomputed_d_modeled_diagnostic": coverage_recomputed_decomposition["d_modeled"],
                    "absorbed_by_turnover": absorbed,
                    "null_mean": null_mean,
                    "null_p95": null_p95,
                    "excess_over_null_mean": excess,
                    "exceeds_null": exceeds_null,
                    "d_combined": d_combined,
                    "R2_Q_Tturn": r2_q_tturn,
                    "turnover_provenance": turnover_provenance,
                    "core_conclusion": core_conclusion,
                    "norms": {
                        "full_P_Q_norm2": full_target["P_Q_norm2"],
                        "full_P_Q_perp_Tmod_norm2": full_target["P_Q_perp_Tmod_norm2"],
                        "turnover_join_P_Q_slice_norm2": p_q_slice_norm2,
                        "turnover_join_P_Q_perp_Tmod_target_norm2": target_norm2,
                        "P_Q_perp_Tmod_absorbed_by_Tturn_norm2": absorbed_norm2,
                        "P_Q_perp_Tmod_remaining_after_Tturn_norm2": remaining_norm2,
                        "Tturn_norm2": tturn_norm2,
                        "Q_to_Tturn_norm2": q_to_tturn_norm2,
                    },
                    "rank_condition_diagnostics": {
                        "rank_Q_e": x_rank,
                        "rank_Tmod": t_mod_rank,
                        "rank_Tturn": t_turn_rank,
                        "rank_Tmod_Tturn": combined_rank,
                        "rank_Z": rank_z,
                        "reference_full_join_rank_Z": full_rank_z,
                        "residual_df_after_Z": residual_df,
                        "q_coordinate_count": len(q_names),
                        "control_column_count": len(z_rows[0]) if z_rows else 0,
                        "ridge_epsilon": RIDGE_EPS,
                        "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                        "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                        "condition_number_Tturn_gram": condition_number_from_gram(gram_matrix(t_turn_tilde)),
                        "condition_number_Tmod_Tturn_gram": condition_number_from_gram(gram_matrix(append_columns(t_mod_tilde, t_turn_tilde))),
                        "null_rank_min": null["rank_min"],
                        "null_rank_max": null["rank_max"],
                    },
                    "dof_matched_null": {
                        "trial_count": null["trial_count"],
                        "randomness": null["randomness"],
                        "rank_unique_values": null["rank_unique_values"],
                    },
                },
                "turnover_H_candidate_conclusion": core_conclusion,
                "honest": {
                    "cannot_claim": cannot_claim(),
                },
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable human turnover H-candidate input", cannot_claim=cannot_claim())


if __name__ == "__main__":
    main()

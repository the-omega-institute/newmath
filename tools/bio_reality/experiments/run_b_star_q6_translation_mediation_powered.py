#!/usr/bin/env python3
"""Powered per-protein B*_Q6 statistical mediation decomposition.

This experiment decomposes codon-to-abundance association by conditioning on a
modeled per-protein tAI readout. It is cross-sectional and non-causal.
"""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from _tai import codon_w_values
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
    synthesize_tai_records,
)


EXPERIMENT_ID = "b_star_q6_translation_mediation_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_mediated_protein_abundance.b_star_q6_mqtp_powered"
CONJECTURE_ID = "q6.translation-mediated.protein-abundance.cross-layer"

ORGANISM_PAIRS = [
    {"organism": "saccharomyces_cerevisiae", "trna_organism": "saccharomyces_cerevisiae"},
    {"organism": "mycobacterium_smegmatis_str_mc2_155", "trna_organism": "mycobacterium_smegmatis_str_mc2_155"},
    {"organism": "escherichia_coli_k12_mg1655", "trna_organism": "escherichia_coli"},
    {"organism": "homo_sapiens", "trna_organism": "homo_sapiens"},
    {"organism": "danio_rerio", "trna_organism": "danio_rerio"},
    {"organism": "gallus_gallus", "trna_organism": "gallus_gallus"},
    {"organism": "bacillus_subtilis_subsp_subtilis_str_168", "trna_organism": "bacillus_subtilis_subsp_subtilis_str_168"},
    {"organism": "mus_musculus", "trna_organism": "mus_musculus"},
    {"organism": "caenorhabditis_elegans", "trna_organism": "caenorhabditis_elegans"},
    {"organism": "drosophila_melanogaster", "trna_organism": "drosophila_melanogaster"},
    {"organism": "sulfolobus_solfataricus", "trna_organism": "sulfolobus_solfataricus"},
    {"organism": "rattus_norvegicus", "trna_organism": "rattus_norvegicus"},
]
MIN_ORGANISMS = 2
MIN_PROTEINS_PER_ORGANISM = 500
SURVIVAL_EPS = 1e-12
RANK_TOL = 1e-10
DEGENERATE_R2 = 0.999999


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def frobenius2(matrix: list[list[float]]) -> float:
    return sum(value * value for row in matrix for value in row)


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def single_column_matrix(column: list[float]) -> list[list[float]]:
    return [[value] for value in column]


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            raise ValueError("least-squares normal equation is rank deficient")
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


def ols_coefficients(design: list[list[float]], response: list[float]) -> list[float]:
    if not design:
        return []
    width = len(design[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, y in zip(design, response):
        for i in range(width):
            xty[i] += row[i] * y
            for j in range(width):
                xtx[i][j] += row[i] * row[j]
    return solve_linear_system(xtx, xty)


def r2_from_design(design: list[list[float]], response: list[list[float]]) -> tuple[float, float, int]:
    y_ss = frobenius2(response)
    if y_ss <= SURVIVAL_EPS:
        return 0.0, 0.0, 0
    explained, rank = explained_by_design(design, response)
    r2 = max(0.0, min(1.0, explained / y_ss))
    return r2, explained, rank


def incremental_r2(
    *,
    full_design: list[list[float]],
    base_design: list[list[float]],
    response: list[list[float]],
) -> tuple[float, float, int, int]:
    y_ss = frobenius2(response)
    if y_ss <= SURVIVAL_EPS:
        return 0.0, 0.0, 0, 0
    full_explained, full_rank = explained_by_design(full_design, response)
    base_explained, base_rank = explained_by_design(base_design, response)
    improvement = max(0.0, full_explained - base_explained)
    return max(0.0, min(1.0, improvement / y_ss)), improvement, full_rank, base_rank


def finite(value: float) -> bool:
    return math.isfinite(value)


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


def trna_copy_counts(repo: pathlib.Path, trna_organism: str) -> dict[str, int]:
    raw = load_json(repo / f"tools/bio_reality/data/gtrnadb_trna_all_copy_{trna_organism}.json")
    if not isinstance(raw, dict):
        raise ValueError(f"{trna_organism} GtRNAdb payload must be an object")
    copies_raw = raw.get("trna_all_copies")
    if not isinstance(copies_raw, dict):
        raise ValueError(f"{trna_organism} trna_all_copies object is missing")
    return {
        str(anticodon).replace("T", "U"): int(numeric(value, f"{trna_organism}.trna_all_copies.{anticodon}"))
        for anticodon, value in copies_raw.items()
    }


def modeled_tai_weights(
    *,
    repo: pathlib.Path,
    organism: str,
    trna_organism: str,
    code: dict[str, str],
    codons: list[str],
) -> tuple[dict[str, float], dict[str, object]]:
    copies = trna_copy_counts(repo, trna_organism)
    records, ambiguous = synthesize_tai_records(
        organism=trna_organism,
        code=code,
        codons=codons,
        trna_all_copies=copies,
    )
    if not records:
        raise ValueError(f"{organism} has no usable anticodon copy records for modeled tAI")
    tai, raw_w, contributors = codon_w_values(
        organism=trna_organism,
        code=code,
        records=records,
        codons=codons,
    )
    zero_raw_w = sorted(codon for codon, value in raw_w.items() if value == 0.0)
    return tai, {
        "cds_organism": organism,
        "trna_organism": trna_organism,
        "trna_all_copy_total": sum(copies.values()),
        "usable_synthetic_tai_record_count": len(records),
        "anticodon_count": len(copies),
        "ambiguous_anticodon_assignments": ambiguous,
        "zero_raw_W_filled_by_geometric_mean_count": len(zero_raw_w),
        "tai_contributor_contact_count": len(contributors),
    }


def protein_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} payload must contain joined list")

    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

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
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
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
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_proteins": len(x_rows),
        "skipped_records": skipped,
    }
    return x_rows, t_rows, y_rows, z_rows, summary


def coordinate_decomposition(
    *,
    x_tilde: list[list[float]],
    t_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, dict[str, object]]:
    y_col = matrix_column(y_tilde, 0)
    t_col = matrix_column(t_tilde, 0)
    out: dict[str, dict[str, object]] = {}
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_design = single_column_matrix(x_col)
        t_design = single_column_matrix(t_col)
        xt_design = append_columns(x_design, t_design)

        total_r2, _, rank_x = r2_from_design(x_design, y_tilde)
        direct_r2, _, rank_xt, rank_t = incremental_r2(
            full_design=xt_design,
            base_design=t_design,
            response=y_tilde,
        )
        indirect_r2 = total_r2 - direct_r2
        fraction = None if abs(total_r2) <= SURVIVAL_EPS else indirect_r2 / total_r2

        a_coeff = 0.0
        x_ss = vector_dot(x_col, x_col)
        if x_ss > SURVIVAL_EPS:
            a_coeff = vector_dot(x_col, t_col) / x_ss
        xt_coeff = ols_coefficients(xt_design, y_col) if rank_xt == 2 else [0.0, 0.0]
        total_coeff = 0.0
        if x_ss > SURVIVAL_EPS:
            total_coeff = vector_dot(x_col, y_col) / x_ss

        route = "mixed_or_unresolved"
        if fraction is not None and total_r2 > SURVIVAL_EPS:
            if fraction >= 0.5 and 0.0 <= fraction <= 1.0:
                route = "mostly_mediated_statistical"
            elif 0.0 <= fraction < 0.5:
                route = "mostly_direct_statistical"
            elif fraction < 0.0:
                route = "suppression_or_negative_conditioning"
            else:
                route = "conditioning_exceeds_total_association"

        out[q_name] = {
            "c_total_R2_QP": total_r2,
            "c_prime_direct_R2_QP_given_T": direct_r2,
            "indirect_R2_c_minus_c_prime": indirect_r2,
            "M_QTP_fraction": fraction,
            "a_beta_T_on_X": a_coeff,
            "b_beta_Y_on_T_given_X": xt_coeff[1],
            "indirect_beta_a_times_b": a_coeff * xt_coeff[1],
            "total_beta_Y_on_X": total_coeff,
            "direct_beta_Y_on_X_given_T": xt_coeff[0],
            "route": route,
            "rank_diagnostics": {
                "rank_X": rank_x,
                "rank_T": rank_t,
                "rank_XT": rank_xt,
            },
        }
    return out


def joint_decomposition(
    *,
    x_tilde: list[list[float]],
    t_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    t_col = matrix_column(t_tilde, 0)
    xt_design = append_columns(x_tilde, t_tilde)
    c_total, explained_x, rank_x = r2_from_design(x_tilde, y_tilde)
    c_prime, direct_improvement, rank_xt, rank_t = incremental_r2(
        full_design=xt_design,
        base_design=t_tilde,
        response=y_tilde,
    )
    t_given_x, t_improvement, _, _ = incremental_r2(
        full_design=xt_design,
        base_design=x_tilde,
        response=y_tilde,
    )
    t_to_y, t_explained, _ = r2_from_design(t_tilde, y_tilde)
    x_to_t, x_to_t_explained, rank_x_for_t = r2_from_design(x_tilde, t_tilde)
    indirect = c_total - c_prime
    fraction = None if abs(c_total) <= SURVIVAL_EPS else indirect / c_total
    coeff_xt = ols_coefficients(xt_design, y_col) if rank_xt == len(q_names) + 1 else [0.0 for _ in range(len(q_names) + 1)]
    coeff_t_on_x = ols_coefficients(x_tilde, t_col) if rank_x == len(q_names) else [0.0 for _ in q_names]

    return {
        "decomposition_mode": "joint_9d_conditioning_plus_per_coordinate_audit",
        "definition": "c is joint R2(Y_P ~ X_Q after Z); c_prime is incremental R2 of X_Q in Y_P ~ T + X_Q; indirect is c - c_prime; M_QTP_fraction is indirect / c.",
        "c_total_R2_QP": c_total,
        "c_prime_direct_R2_QP_given_T": c_prime,
        "indirect_R2_c_minus_c_prime": indirect,
        "M_QTP_fraction": fraction,
        "T_only_R2_to_Y": t_to_y,
        "T_incremental_R2_given_X": t_given_x,
        "X_to_T_R2_path_a_joint": x_to_t,
        "path_coefficients": {
            "a_beta_T_on_X_by_coordinate": dict(zip(q_names, coeff_t_on_x)),
            "b_beta_Y_on_T_given_X": coeff_xt[-1],
            "total_beta_Y_on_X_by_coordinate": dict(zip(q_names, ols_coefficients(x_tilde, y_col) if rank_x == len(q_names) else [0.0 for _ in q_names])),
            "direct_beta_Y_on_X_given_T_by_coordinate": dict(zip(q_names, coeff_xt[:-1])),
        },
        "rank_diagnostics": {
            "rank_Xtilde": rank_x,
            "rank_Ttilde": rank_t,
            "rank_XTtilde": rank_xt,
            "rank_X_for_T": rank_x_for_t,
            "q_coordinate_count": len(q_names),
            "y_residual_energy": frobenius2(y_tilde),
            "t_residual_energy": frobenius2(t_tilde),
            "X_explained_energy_on_Y": explained_x,
            "X_direct_improvement_energy_given_T": direct_improvement,
            "T_explained_energy_on_Y": t_explained,
            "T_incremental_improvement_energy_given_X": t_improvement,
            "X_explained_energy_on_T": x_to_t_explained,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
    }


def summarize_routes(per_coordinate: dict[str, dict[str, object]]) -> dict[str, object]:
    rows = []
    for q_name, result in per_coordinate.items():
        total = float(result["c_total_R2_QP"])
        fraction = result["M_QTP_fraction"]
        rows.append(
            {
                "q_coordinate": q_name,
                "total_R2": total,
                "direct_R2": result["c_prime_direct_R2_QP_given_T"],
                "indirect_R2": result["indirect_R2_c_minus_c_prime"],
                "M_QTP_fraction": fraction,
                "route": result["route"],
            }
        )
    mediated = sorted(
        [row for row in rows if isinstance(row["M_QTP_fraction"], float) and 0.0 <= row["M_QTP_fraction"] <= 1.0],
        key=lambda row: (float(row["M_QTP_fraction"]), float(row["total_R2"])),
        reverse=True,
    )
    direct = sorted(
        [row for row in rows if isinstance(row["M_QTP_fraction"], float) and 0.0 <= row["M_QTP_fraction"] <= 1.0],
        key=lambda row: (float(row["M_QTP_fraction"]), -float(row["total_R2"])),
    )
    return {
        "mostly_mediated_coordinates": mediated[:3],
        "mostly_direct_coordinates": direct[:3],
        "all_coordinate_routes": rows,
    }


def cannot_claim() -> list[str]:
    return [
        "M^{QTP} here is a statistical mediation decomposition, not a causal effect",
        "modeled per-protein tAI from GtRNAdb tRNA gene-copy counts and dos Reis wobble weights is not ribo-seq",
        "conditioning on modeled tAI in cross-sectional matched CDS/protein-abundance rows is not a proven translation mechanism",
        "protein abundance is not isolated from mRNA abundance, protein turnover, localization, PTM, folding, or pathway context",
        "positive mediated fractions do not establish synonymous-edit, perturbation, rescue, or mechanism_realization claims",
    ]


def future_required() -> list[str]:
    return [
        "matched ribosome profiling or calibrated translation-efficiency readouts for the same proteins",
        "matched mRNA abundance controls to separate protein abundance from expression-level confounding",
        "synonymous perturbation or rescue assays before any causal mediation or mechanism statement",
        "independent held-out organism/proteome validation before treating coordinate routes as stable biological regularities",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
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

        organism_results: dict[str, object] = {}
        loaded_organisms = 0
        data_actual: dict[str, object] = {}
        tai_ok = True
        residualized_ok = True
        rank_ok = True
        mediation_ok = True
        fraction_ok = True

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
            joint = joint_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
            per_coordinate = coordinate_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
            route_summary = summarize_routes(per_coordinate)
            residual_df = n_proteins - rank_z
            rank_diag = joint["rank_diagnostics"]

            organism_powered = (
                n_proteins >= MIN_PROTEINS_PER_ORGANISM
                and residual_df > 10 * (len(q_names) + 1)
                and int(rank_diag["rank_Xtilde"]) == len(q_names)
                and int(rank_diag["rank_Ttilde"]) == 1
                and int(rank_diag["rank_XTtilde"]) == len(q_names) + 1
                and float(rank_diag["y_residual_energy"]) > SURVIVAL_EPS
                and float(rank_diag["t_residual_energy"]) > SURVIVAL_EPS
                and float(joint["c_total_R2_QP"]) > SURVIVAL_EPS
                and float(joint["c_total_R2_QP"]) < DEGENERATE_R2
            )
            organism_fraction = joint["M_QTP_fraction"]
            organism_fraction_ok = isinstance(organism_fraction, float) and 0.0 <= organism_fraction <= 1.0
            finite_joint = all(
                finite(float(joint[key]))
                for key in [
                    "c_total_R2_QP",
                    "c_prime_direct_R2_QP_given_T",
                    "indirect_R2_c_minus_c_prime",
                    "T_only_R2_to_Y",
                    "T_incremental_R2_given_X",
                    "X_to_T_R2_path_a_joint",
                ]
            )

            data_actual[organism] = {
                "cds_organism": organism,
                "trna_organism": trna_organism,
                "n_joined": payload.get("n_joined"),
                "n_proteins_used": n_proteins,
            }
            tai_ok = tai_ok and all(finite(value) and value > 0.0 for value in tai_weights.values()) and len(t_rows) == n_proteins
            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_proteins and len(t_tilde) == n_proteins and len(y_tilde) == n_proteins
            rank_ok = rank_ok and organism_powered
            mediation_ok = mediation_ok and finite_joint
            fraction_ok = fraction_ok and organism_fraction_ok

            organism_results[organism] = {
                **data_summary,
                **tai_summary,
                "c_total_R2_QP": joint["c_total_R2_QP"],
                "c_prime_direct_R2_QP_given_T": joint["c_prime_direct_R2_QP_given_T"],
                "indirect_R2_c_minus_c_prime": joint["indirect_R2_c_minus_c_prime"],
                "M_QTP_fraction": joint["M_QTP_fraction"],
                "joint_decomposition": joint,
                "per_coordinate_decomposition": per_coordinate,
                "coordinate_route_summary": route_summary,
                "rank_diagnostics": {
                    **rank_diag,
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "powered_rank_sufficient": organism_powered,
                    "M_QTP_fraction_in_unit_interval": organism_fraction_ok,
                },
            }

        checks = [
            {
                "name": "cds_abundance_and_trna_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS,
                "actual": data_actual,
                "expected": f">= {MIN_ORGANISMS} organisms with local CDS-abundance joins, matched all-tRNA copy data, and n_proteins >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "per_protein_tai_computed",
                "passed": tai_ok,
                "actual": {
                    organism: {
                        "n_proteins": result["n_proteins"],
                        "trna_organism": result["trna_organism"],
                        "trna_all_copy_total": result["trna_all_copy_total"],
                        "zero_raw_W_filled_by_geometric_mean_count": result["zero_raw_W_filled_by_geometric_mean_count"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite positive per-codon tAI weights and finite per-protein mean modeled tAI for every usable joined protein",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9,
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "exactly the 9 B*_Q6 synonymous-residual coordinates reused from run_b_star_q6_translation_survival_powered.py",
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
                "expected": "per-organism n >= 500, full 9-coordinate X rank, nonzero T/Y residual energy, full X+T rank, and c_total_R2_QP nonzero but not saturated",
            },
            {
                "name": "mediation_decomposition_computed",
                "passed": mediation_ok and fraction_ok,
                "actual": {
                    organism: {
                        "c_total_R2_QP": result["c_total_R2_QP"],
                        "c_prime_direct_R2_QP_given_T": result["c_prime_direct_R2_QP_given_T"],
                        "indirect_R2_c_minus_c_prime": result["indirect_R2_c_minus_c_prime"],
                        "M_QTP_fraction": result["M_QTP_fraction"],
                        "M_QTP_fraction_in_unit_interval": result["rank_diagnostics"]["M_QTP_fraction_in_unit_interval"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite c, c_prime, indirect, and M^{QTP} fraction in [0, 1] for every promoted organism",
            },
            {
                "name": "no_causal_or_mechanism_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "statistical mediation only; not causal, not a proven mechanism, modeled-tAI is not ribo-seq, and the data are cross-sectional",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; result is not promoted to powered M^{QTP}"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Per-protein B*_Q6 codon residual to protein-abundance association is decomposed by conditioning on modeled per-protein tAI; this is a statistical mediation decomposition, NOT a causal mechanism.",
                "readout_T": "per-protein mean modeled tAI = sum_codon(codon_count * tAI_weight) / sum_codon(codon_count), using GtRNAdb all-tRNA copy counts and dos Reis wobble weights",
                "readout_Y": "log10(abundance_ppm) from measured PAXdb protein abundance joined to real CDS codon counts",
                "decomposition_mode": "joint 9-dimensional X_Q mediation scalar with per-coordinate decomposition audit",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
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
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered translation-mediation input")


if __name__ == "__main__":
    main()

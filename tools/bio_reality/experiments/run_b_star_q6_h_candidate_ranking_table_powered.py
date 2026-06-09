#!/usr/bin/env python3
"""Direction-aware H-candidate ranking table for the B*_Q6 complement.

This is a deterministic descriptive projection audit. It ranks local
H-candidate readouts by absorption, coordinate-support direction, and a stated
description-length regularizer. It is not causal and not mechanistic.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys

from _tai import codon_w_values, normalize_aa
from run_b_star_q6_h_candidate_localization_powered import LOCALIZATION_CATEGORIES
from run_b_star_q6_h_candidate_turnover_powered import turnover_by_protein
from run_b_star_q6_measured_te_survival_powered import te_by_protein
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    orthonormal_basis_from_columns,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import (
    RIDGE_EPS,
    complement_decomposition,
    condition_number_from_gram,
    gram_matrix,
    project_onto_design,
    solve_regularized_normal_equation,
    subtract_vectors,
    vector_norm2,
)
from run_b_star_q6_translation_mediation_powered import (
    MIN_PROTEINS_PER_ORGANISM,
    ORGANISM_PAIRS,
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


EXPERIMENT_ID = "b_star_q6_h_candidate_ranking_table_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_ranking_table.b_star_q6_non_translation_residual_powered"
CONJECTURE_ID = "q6.h-ranking-table.direction-aware.cross-layer"

NULL_TRIALS = 64
BONFERRONI_ALPHA = 0.05
LAMBDA_DL = 0.01
SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02
SHARED_COVERAGE_THRESHOLD = 2

Q_NAMES_FIXED = [
    "K_AAA",
    "Arg_AGR",
    "Ile_AUA",
    "Leu_CUN_vs_UUR",
    "Leu_UUA_vs_UUG",
    "Ser_UCR_vs_AGY",
    "Ser_UCA_vs_UCG",
    "Thr_ACR_vs_ACY",
    "f3_stress",
]

ROADMAP_D_MODELED = {
    "saccharomyces_cerevisiae": 0.21,
    "escherichia_coli_k12_mg1655": 0.66,
    "mycobacterium_smegmatis_str_mc2_155": 0.90,
    "homo_sapiens": 0.92,
    "danio_rerio": 0.88,
    "gallus_gallus": 0.94,
}

DOMINANT_COORDINATE_PRIOR = {
    "saccharomyces_cerevisiae": "Ser_UCR_vs_AGY",
    "mycobacterium_smegmatis_str_mc2_155": "K_AAA",
    "escherichia_coli_k12_mg1655": "Thr_ACR_vs_ACY",
    "homo_sapiens": "Arg_AGR",
    "gallus_gallus": "Arg_AGR",
    "danio_rerio": "f3_stress",
}

H_CANDIDATES = [
    "mrna",
    "measured_te",
    "measured_trna_tai",
    "turnover",
    "localization",
    "ptm_density",
    "complex_member",
    "tm_count",
    "domain_count",
]

FEATURE_CANDIDATES = {"ptm_density", "complex_member", "tm_count", "domain_count"}


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if not math.isfinite(value):
        return value
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def finite_unit_interval(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
        and 0.0 <= float(value) <= 1.0
    )


def finite_cosine(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
        and -1.0 <= float(value) <= 1.0
    )


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def matrix_column(matrix: list[list[float]], index: int) -> list[float]:
    return [row[index] for row in matrix]


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


def project_by_basis(design_tilde: list[list[float]], target: list[float]) -> dict[str, object]:
    basis = orthonormal_basis_from_columns(design_tilde)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = sum(target[index] * q[index] for index in range(len(target)))
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    denom = vector_norm2(target)
    projected_norm2 = vector_norm2(projected)
    absorbed = None if denom <= SURVIVAL_EPS else bounded_unit(projected_norm2 / denom)
    return {
        "projected_vector": projected,
        "absorbed": absorbed,
        "projected_norm2": projected_norm2,
        "target_norm2": denom,
        "rank": len(basis),
    }


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def support_cosine(left: list[float], right: list[float]) -> tuple[float, str | None]:
    left_norm = math.sqrt(vector_dot(left, left))
    right_norm = math.sqrt(vector_dot(right, right))
    if left_norm <= SURVIVAL_EPS:
        return 0.0, "a_H_zero_vector"
    if right_norm <= SURVIVAL_EPS:
        return 0.0, "a_perp_zero_vector"
    value = vector_dot(left, right) / (left_norm * right_norm)
    if -1.0 - 1e-8 <= value < -1.0:
        value = -1.0
    if 1.0 < value <= 1.0 + 1e-8:
        value = 1.0
    return value, None


def lcg_uniform(seed: int) -> tuple[int, float]:
    next_seed = (1664525 * seed + 1013904223) & 0xFFFFFFFF
    return next_seed, (next_seed + 0.5) / 4294967296.0


def deterministic_gaussian_matrix(
    *,
    organism: str,
    candidate: str,
    trial: int,
    n_rows: int,
    k_cols: int,
) -> list[list[float]]:
    material = f"{EXPERIMENT_ID}|{organism}|{candidate}|{trial}|{n_rows}|{k_cols}"
    seed = int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:4], "big")
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
    return [values[row * k_cols : (row + 1) * k_cols] for row in range(n_rows)]


def dof_matched_null(
    *,
    organism: str,
    candidate: str,
    n_rows: int,
    k_cols: int,
    z_basis: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    absorptions: list[float] = []
    ranks: list[int] = []
    for trial in range(NULL_TRIALS):
        raw = deterministic_gaussian_matrix(
            organism=organism,
            candidate=candidate,
            trial=trial,
            n_rows=n_rows,
            k_cols=k_cols,
        )
        null_tilde = residualize_with_basis(raw, z_basis)
        result = project_by_basis(null_tilde, target)
        absorbed = result["absorbed"]
        if not isinstance(absorbed, float):
            raise ValueError(f"{organism} {candidate} null trial {trial} did not produce finite absorption")
        absorptions.append(absorbed)
        ranks.append(int(result["rank"]))
    return {
        "trial_count": NULL_TRIALS,
        "absorbed_values": absorptions,
        "null_mean": mean(absorptions),
        "null_p95": percentile_nearest_rank(absorptions, 0.95),
        "rank_min": min(ranks) if ranks else None,
        "rank_max": max(ranks) if ranks else None,
        "rank_unique_values": sorted(set(ranks)),
        "randomness": "hashlib-derived seed from experiment_id, organism, H, trial, n_rows, and k_cols; LCG plus Box-Muller; no system time",
    }


def build_core_row(
    *,
    item: dict[str, object],
    organism: str,
    row_index: int,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[str, list[float], list[float], list[float], list[float], dict[str, int]] | None:
    skipped = {
        "missing_protein_id": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    protein_id = item.get("protein_id")
    if not isinstance(protein_id, str) or not protein_id:
        skipped["missing_protein_id"] += 1
        return None
    abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
    if abundance <= 0.0:
        skipped["nonpositive_abundance"] += 1
        return None
    cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        skipped["invalid_length"] += 1
        return None
    counts = codon_counts_rna(item, codons, organism, row_index)
    total = sum(counts.values())
    if total <= 0:
        skipped["empty_sense_codon_counts"] += 1
        return None

    frequencies = {codon: counts[codon] / total for codon in codons}
    x_row = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]
    t_row = [sum(counts[codon] * tai_weights[codon] for codon in codons) / total]
    y_row = [math.log10(abundance)]

    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    z_row = [1.0, math.log(cds_len_nt)] + [aa_counts[aa] / aa_total for aa in aa_order] + [gc3, m_density]
    return protein_id, x_row, t_row, y_row, z_row, skipped


def base_rows_with_ids(
    *,
    cds_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> dict[str, object]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    protein_ids: list[str] = []
    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        built = build_core_row(
            item=item,
            organism=organism,
            row_index=row_index,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        if built is None:
            for key in skipped:
                if key != "non_object":
                    skipped[key] += 1
            continue
        protein_id, x_row, t_row, y_row, z_row, _ = built
        protein_ids.append(protein_id)
        x_rows.append(x_row)
        t_rows.append(t_row)
        y_rows.append(y_row)
        z_rows.append(z_row)
    return {
        "protein_ids": protein_ids,
        "x_rows": x_rows,
        "t_rows": t_rows,
        "y_rows": y_rows,
        "z_rows": z_rows,
        "summary": {
            "n_joined_reported": cds_payload.get("n_joined"),
            "join_hit_rate": cds_payload.get("join_hit_rate"),
            "n_proteins": len(x_rows),
            "skipped_records": skipped,
        },
    }


def complement_from_rows(
    *,
    x_rows: list[list[float]],
    t_rows: list[list[float]],
    y_rows: list[list[float]],
    z_rows: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_tilde = residualize_with_basis(x_rows, z_basis)
    t_tilde = residualize_with_basis(t_rows, z_basis)
    y_tilde = residualize_with_basis(y_rows, z_basis)
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_tilde, p_q)
    target = subtract_vectors(p_q, p_q_from_tmod)
    p_q_norm2 = vector_norm2(p_q)
    target_norm2 = vector_norm2(target)
    a_perp = solve_regularized_normal_equation(x_tilde, target)
    return {
        "z_basis": z_basis,
        "x_tilde": x_tilde,
        "t_tilde": t_tilde,
        "y_tilde": y_tilde,
        "P_Q": p_q,
        "P_Q_perp_Tmod": target,
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": target_norm2,
        "d_modeled": None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(target_norm2 / p_q_norm2),
        "a_perp_vector": a_perp,
        "a_perp": dict(zip(q_names, a_perp)),
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
        },
        "rank_condition_diagnostics": {
            "rank_Z": len(z_basis),
            "control_column_count": len(z_rows[0]) if z_rows else 0,
            "rank_Q_e": explained_by_design(x_tilde, y_tilde)[1],
            "rank_Tmod": explained_by_design(t_tilde, y_tilde)[1],
            "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
            "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_tilde)),
            "ridge_epsilon": RIDGE_EPS,
        },
    }


def h_rows_from_index(
    *,
    base_rows: dict[str, object],
    h_index: dict[str, list[float]],
    h_name: str,
) -> dict[str, object]:
    protein_ids = base_rows["protein_ids"]
    x_rows = base_rows["x_rows"]
    t_rows = base_rows["t_rows"]
    y_rows = base_rows["y_rows"]
    z_rows = base_rows["z_rows"]
    if not isinstance(protein_ids, list) or not isinstance(x_rows, list):
        raise ValueError(f"{h_name} base rows malformed")
    out_ids: list[str] = []
    out_x: list[list[float]] = []
    out_t: list[list[float]] = []
    out_y: list[list[float]] = []
    out_z: list[list[float]] = []
    out_h: list[list[float]] = []
    missing = 0
    invalid = 0
    for protein_id, x_row, t_row, y_row, z_row in zip(protein_ids, x_rows, t_rows, y_rows, z_rows):
        h_row = h_index.get(str(protein_id))
        if h_row is None:
            missing += 1
            continue
        if not h_row or not all(math.isfinite(value) for value in h_row):
            invalid += 1
            continue
        out_ids.append(str(protein_id))
        out_x.append(list(x_row))
        out_t.append(list(t_row))
        out_y.append(list(y_row))
        out_z.append(list(z_row))
        out_h.append(list(h_row))
    return {
        "protein_ids": out_ids,
        "x_rows": out_x,
        "t_rows": out_t,
        "y_rows": out_y,
        "z_rows": out_z,
        "h_rows": out_h,
        "summary": {
            "h_candidate": h_name,
            "n_joined": len(out_h),
            "missing_h_match": missing,
            "invalid_h_row": invalid,
            "n_columns": len(out_h[0]) if out_h else 0,
        },
    }


def ribosome_index(payload: dict[str, object], organism: str, field: str) -> tuple[dict[str, list[float]], dict[str, object]]:
    te_index, summary = te_by_protein(payload, organism)
    if field == "mrna":
        return {
            protein_id: [math.log10(record["mrna"])]
            for protein_id, record in te_index.items()
            if record.get("mrna", 0.0) > 0.0
        }, summary
    if field == "measured_te":
        return {
            protein_id: [math.log10(record["te"])]
            for protein_id, record in te_index.items()
            if record.get("te", 0.0) > 0.0
        }, summary
    raise ValueError(f"unknown ribosome field {field}")


def turnover_index(payload: dict[str, object]) -> tuple[dict[str, list[float]], dict[str, object]]:
    values, summary = turnover_by_protein(payload)
    return {protein_id: [math.log10(value)] for protein_id, value in values.items() if value > 0.0}, summary


def measured_trna_records_from_payload(payload: dict[str, object]) -> list[dict[str, str]]:
    raw = payload.get("trna_aa_anticodon_gene_copy_counts")
    if not isinstance(raw, dict):
        raise ValueError("measured tRNA payload lacks trna_aa_anticodon_gene_copy_counts")
    records: list[dict[str, str]] = []
    for key, value in raw.items():
        if not isinstance(key, str) or ":" not in key:
            continue
        aa_label, anticodon = key.split(":", 1)
        count = int(numeric(value, f"trna_aa_anticodon_gene_copy_counts.{key}"))
        if count <= 0:
            continue
        for _ in range(count):
            records.append(
                {
                    "aa": normalize_aa(aa_label),
                    "aa_label": aa_label,
                    "anticodon": anticodon.replace("T", "U"),
                    "matched": True,
                }
            )
    return records


def measured_trna_index(
    *,
    payload: dict[str, object],
    organism: str,
    base_rows: dict[str, object],
    code: dict[str, str],
    codons: list[str],
) -> tuple[dict[str, list[float]], dict[str, object]]:
    records = measured_trna_records_from_payload(payload)
    weights, raw_w, contributors = codon_w_values(organism=organism, code=code, records=records, codons=codons)
    out: dict[str, list[float]] = {}
    joined = base_rows.get("source_joined")
    protein_ids = base_rows.get("source_protein_ids")
    if not isinstance(joined, list) or not isinstance(protein_ids, list):
        raise ValueError(f"{organism} base source rows are unavailable for measured_trna_tai")
    for protein_id, item in zip(protein_ids, joined):
        if not isinstance(item, dict):
            continue
        counts = codon_counts_rna(item, codons, organism, 0)
        total = sum(counts.values())
        if total <= 0:
            continue
        value = math.exp(sum(counts[codon] * math.log(weights[codon]) for codon in codons) / total)
        if math.isfinite(value) and value > 0.0:
            out[str(protein_id)] = [value]
    return out, {
        "source_kind": payload.get("source_kind"),
        "payload_sha256": payload.get("payload_sha256"),
        "n_trna_records_expanded": len(records),
        "n_trna_genes_included_for_gcn": payload.get("n_trna_genes_included_for_gcn"),
        "usable_measured_tai_record_count": len(records),
        "tai_contributor_contact_count": len(contributors),
        "zero_raw_W_filled_by_geometric_mean_count": sum(1 for value in raw_w.values() if value == 0.0),
    }


def localization_index(payload: dict[str, object]) -> tuple[dict[str, list[float]], dict[str, object]]:
    proteins = payload.get("proteins")
    if not isinstance(proteins, dict):
        raise ValueError("localization payload must contain proteins object")
    category_counts = {category: 0 for category in LOCALIZATION_CATEGORIES}
    raw_categories: dict[str, set[str]] = {}
    for protein_id, record in proteins.items():
        if not isinstance(record, dict):
            continue
        categories = record.get("categories")
        if not isinstance(categories, list) or not categories:
            continue
        category_set = {str(category) for category in categories if str(category) in category_counts}
        if not category_set:
            continue
        raw_categories[str(protein_id)] = category_set
        for category in category_set:
            category_counts[category] += 1
    present = [category for category in LOCALIZATION_CATEGORIES if category_counts[category] > 0]
    index = {
        protein_id: [1.0 if category in categories else 0.0 for category in present]
        for protein_id, categories in raw_categories.items()
    }
    return index, {
        "source_kind": payload.get("source_kind"),
        "n_string_localization_records": payload.get("n_string_localization_records"),
        "localization_categories_used": present,
        "localization_category_counts": {category: category_counts[category] for category in present},
        "payload_sha256": (payload.get("provenance") or {}).get("payload_sha256") if isinstance(payload.get("provenance"), dict) else None,
    }


def feature_index(payload: dict[str, object], candidate: str) -> tuple[dict[str, list[float]], dict[str, object]]:
    proteins = payload.get("proteins")
    if not isinstance(proteins, dict):
        raise ValueError("protein-feature payload must contain proteins object")
    out: dict[str, list[float]] = {}
    for protein_id, record in proteins.items():
        if not isinstance(record, dict):
            continue
        features = record.get("features")
        if not isinstance(features, dict) or candidate not in features:
            continue
        value = numeric(features[candidate], f"features.{candidate}")
        if math.isfinite(value):
            out[str(protein_id)] = [value]
    return out, {
        "source_kind": payload.get("source_kind"),
        "n_string_feature_records": payload.get("n_string_feature_records"),
        "feature_distribution_summary": (payload.get("feature_distribution_summary") or {}).get(candidate)
        if isinstance(payload.get("feature_distribution_summary"), dict)
        else None,
        "feature_parse_policy": (payload.get("feature_parse_policy") or {}).get(candidate)
        if isinstance(payload.get("feature_parse_policy"), dict)
        else None,
        "payload_sha256": (payload.get("provenance") or {}).get("payload_sha256") if isinstance(payload.get("provenance"), dict) else None,
    }


def load_h_index(
    *,
    repo: pathlib.Path,
    organism: str,
    candidate: str,
    base_rows: dict[str, object],
    code: dict[str, str],
    codons: list[str],
) -> tuple[dict[str, list[float]] | None, dict[str, object]]:
    if candidate in {"mrna", "measured_te"}:
        path = repo / f"tools/bio_reality/data/ribosome_te_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return ribosome_index(payload, organism, candidate)

    if candidate == "measured_trna_tai":
        path = repo / f"tools/bio_reality/data/trna_gene_copy_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return measured_trna_index(payload=payload, organism=organism, base_rows=base_rows, code=code, codons=codons)

    if candidate == "turnover":
        path = repo / f"tools/bio_reality/data/protein_turnover_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return turnover_index(payload)

    if candidate == "localization":
        path = repo / f"tools/bio_reality/data/subcellular_localization_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return localization_index(payload)

    if candidate in FEATURE_CANDIDATES:
        path = repo / f"tools/bio_reality/data/uniprot_protein_features_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return feature_index(payload, candidate)

    raise ValueError(f"unknown H candidate {candidate}")


def candidate_result(
    *,
    organism: str,
    candidate: str,
    rows: dict[str, object],
    base_d_modeled: float | None,
    q_names: list[str],
    source_summary: dict[str, object],
) -> dict[str, object]:
    n_joined = int(rows["summary"]["n_joined"])  # type: ignore[index]
    if n_joined < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"join below threshold n_joined < {MIN_PROTEINS_PER_ORGANISM}",
            "n_joined": n_joined,
            "source_summary": source_summary,
            "join_summary": rows["summary"],
        }

    x_rows = rows["x_rows"]
    t_rows = rows["t_rows"]
    y_rows = rows["y_rows"]
    z_rows = rows["z_rows"]
    h_rows = rows["h_rows"]
    if not isinstance(x_rows, list) or not isinstance(h_rows, list) or not h_rows:
        raise ValueError(f"{organism} {candidate} rows malformed")

    complement = complement_from_rows(
        x_rows=x_rows,  # type: ignore[arg-type]
        t_rows=t_rows,  # type: ignore[arg-type]
        y_rows=y_rows,  # type: ignore[arg-type]
        z_rows=z_rows,  # type: ignore[arg-type]
        q_names=q_names,
    )
    z_basis = complement["z_basis"]
    target = complement["P_Q_perp_Tmod"]
    x_tilde = complement["x_tilde"]
    if not isinstance(z_basis, list) or not isinstance(target, list) or not isinstance(x_tilde, list):
        raise ValueError(f"{organism} {candidate} complement malformed")

    h_tilde = residualize_with_basis(h_rows, z_basis)  # type: ignore[arg-type]
    projection = project_by_basis(h_tilde, target)
    absorbed = projection["absorbed"]
    projected_vector = projection["projected_vector"]
    if not isinstance(absorbed, float) or not isinstance(projected_vector, list):
        raise ValueError(f"{organism} {candidate} absorption is not finite")
    a_perp_vector = complement["a_perp_vector"]
    if not isinstance(a_perp_vector, list):
        raise ValueError(f"{organism} {candidate} a_perp is malformed")
    a_h = solve_regularized_normal_equation(x_tilde, projected_vector)
    cosine, cosine_note = support_cosine(a_h, a_perp_vector)
    raw_score = absorbed * cosine
    n_columns = len(h_rows[0])  # type: ignore[index]
    dl = math.log2(1.0 + n_columns)
    score = raw_score - LAMBDA_DL * dl
    null = dof_matched_null(
        organism=organism,
        candidate=candidate,
        n_rows=n_joined,
        k_cols=n_columns,
        z_basis=z_basis,
        target=target,
    )
    d_modeled = complement["d_modeled"]
    d_difference = None
    if isinstance(d_modeled, float) and isinstance(base_d_modeled, float):
        d_difference = abs(d_modeled - base_d_modeled)

    return {
        "status": "computed",
        "H": candidate,
        "A_H": absorbed,
        "C_H": cosine,
        "A_H_times_C_H": raw_score,
        "Score": score,
        "DL_H": dl,
        "DL_definition": "log2(1 + n_columns(H))",
        "lambda": LAMBDA_DL,
        "n_columns": n_columns,
        "n_joined": n_joined,
        "a_H": dict(zip(q_names, a_h)),
        "a_perp_on_H_join": dict(zip(q_names, a_perp_vector)),
        "cosine_note": cosine_note,
        "P_Q_norm2": complement["P_Q_norm2"],
        "P_Q_perp_Tmod_norm2": complement["P_Q_perp_Tmod_norm2"],
        "d_modeled_on_H_join": d_modeled,
        "d_modeled_base_reference": base_d_modeled,
        "d_modeled_base_absolute_difference": d_difference,
        "d_modeled_base_matches_within_0_02": isinstance(d_difference, float) and d_difference < MODELED_ALIGNMENT_TOL,
        "absorbed_norm2": projection["projected_norm2"],
        "target_norm2": projection["target_norm2"],
        "rank_H": projection["rank"],
        "condition_number_H_gram": condition_number_from_gram(gram_matrix(h_tilde)),
        "null_mean": null["null_mean"],
        "null_p95": null["null_p95"],
        "_null_absorbed_values_for_threshold": null["absorbed_values"],
        "dof_matched_null": {
            "trial_count": null["trial_count"],
            "rank_min": null["rank_min"],
            "rank_max": null["rank_max"],
            "rank_unique_values": null["rank_unique_values"],
            "randomness": null["randomness"],
        },
        "source_summary": source_summary,
        "join_summary": rows["summary"],
        "rank_condition_diagnostics": complement["rank_condition_diagnostics"],
    }


def assemble_ranking(candidates: dict[str, dict[str, object]]) -> tuple[list[dict[str, object]], str | None]:
    computed = [value for value in candidates.values() if value.get("status") == "computed"]
    k = len(computed)
    probability = None if k == 0 else 1.0 - BONFERRONI_ALPHA / k
    for value in computed:
        null_values = value.get("_null_absorbed_values_for_threshold")
        threshold = percentile_nearest_rank([float(x) for x in null_values], probability) if isinstance(null_values, list) and isinstance(probability, float) else None
        value["candidate_count_K_for_organism"] = k
        value["bonferroni_probability"] = probability
        value["bonferroni_threshold"] = threshold
        absorbed = value.get("A_H")
        value["exceeds_bonferroni"] = bool(isinstance(absorbed, float) and isinstance(threshold, float) and absorbed > threshold)
        value.pop("_null_absorbed_values_for_threshold", None)

    ranking = sorted(
        [
            {
                "H": value["H"],
                "Score": value["Score"],
                "A_H_times_C_H": value["A_H_times_C_H"],
                "A_H": value["A_H"],
                "C_H": value["C_H"],
                "DL_H": value["DL_H"],
                "n_columns": value["n_columns"],
                "n_joined": value["n_joined"],
                "null_p95": value["null_p95"],
                "bonferroni_threshold": value["bonferroni_threshold"],
                "exceeds_bonferroni": value["exceeds_bonferroni"],
            }
            for value in computed
        ],
        key=lambda item: float(item["Score"]),
        reverse=True,
    )
    winners = [item for item in ranking if item.get("exceeds_bonferroni") is True]
    return ranking, str(winners[0]["H"]) if winners else None


def shared_analysis(per_organism: dict[str, dict[str, object]]) -> dict[str, object]:
    by_h: dict[str, list[dict[str, object]]] = {name: [] for name in H_CANDIDATES}
    for organism, result in per_organism.items():
        candidates = result.get("candidates")
        if not isinstance(candidates, dict):
            continue
        for h_name, candidate in candidates.items():
            if not isinstance(candidate, dict) or candidate.get("status") != "computed":
                continue
            by_h[h_name].append(
                {
                    "organism": organism,
                    "Score": candidate["Score"],
                    "A_H_times_C_H": candidate["A_H_times_C_H"],
                    "A_H": candidate["A_H"],
                    "C_H": candidate["C_H"],
                    "exceeds_bonferroni": candidate.get("exceeds_bonferroni"),
                    "n_joined": candidate["n_joined"],
                }
            )

    summaries: dict[str, dict[str, object]] = {}
    eligible: list[dict[str, object]] = []
    for h_name, entries in by_h.items():
        scores = [float(entry["Score"]) for entry in entries]
        raw_scores = [float(entry["A_H_times_C_H"]) for entry in entries]
        positives = [entry for entry in entries if entry.get("exceeds_bonferroni") is True]
        summary = {
            "H": h_name,
            "coverage": len(entries),
            "coverage_threshold": SHARED_COVERAGE_THRESHOLD,
            "organisms": [entry["organism"] for entry in entries],
            "min_Score": min(scores) if scores else None,
            "sum_Score": sum(scores) if scores else None,
            "mean_Score": mean(scores),
            "min_raw_A_H_times_C_H": min(raw_scores) if raw_scores else None,
            "sum_raw_A_H_times_C_H": sum(raw_scores) if raw_scores else None,
            "exceeds_bonferroni_count": len(positives),
            "exceeds_bonferroni_all_covered": bool(entries) and len(positives) == len(entries),
            "per_organism": entries,
        }
        summaries[h_name] = summary
        if len(entries) >= SHARED_COVERAGE_THRESHOLD and scores:
            eligible.append(summary)

    eligible.sort(
        key=lambda item: (
            float(item["min_Score"]),
            float(item["sum_Score"]),
            int(item["exceeds_bonferroni_count"]),
            int(item["coverage"]),
        ),
        reverse=True,
    )
    h_shared = str(eligible[0]["H"]) if eligible else None
    h_shared_summary = summaries[h_shared] if h_shared is not None else None
    stable_shared = False
    if isinstance(h_shared_summary, dict):
        stable_shared = bool(
            h_shared_summary["exceeds_bonferroni_all_covered"]
            and isinstance(h_shared_summary["min_raw_A_H_times_C_H"], float)
            and float(h_shared_summary["min_raw_A_H_times_C_H"]) > 0.0
        )

    organism_specific: dict[str, dict[str, object]] = {}
    for organism, result in per_organism.items():
        h_o = result.get("H_o_star")
        organism_specific[organism] = {
            "H_o_star": h_o,
            "H_shared_star": h_shared,
            "organism_specific": h_o is not None and h_o != h_shared,
            "dominant_coordinate_prior": DOMINANT_COORDINATE_PRIOR.get(organism),
        }

    if stable_shared:
        verdict = "a shared H candidate has positive direction-aware support and exceeds Bonferroni in every covered organism"
    elif any(item["H_o_star"] for item in organism_specific.values()):
        verdict = "no stable shared H is supported; winning H_o* calls are organism-specific or coverage-limited"
    else:
        verdict = "no H candidate clears the direction-aware Bonferroni ranking; the non-translation residual remains organism-specific unexplained"

    return {
        "H_shared_star": h_shared,
        "selection_rule": "among H with coverage >= 2, maximize min Score, then sum Score, then Bonferroni-positive count",
        "coverage_threshold": SHARED_COVERAGE_THRESHOLD,
        "stable_shared_H_supported": stable_shared,
        "shared_summary": h_shared_summary,
        "all_H_summaries": summaries,
        "organism_specific_vs_shared": organism_specific,
        "core_conclusion": verdict,
    }


def cannot_claim() -> list[str]:
    return [
        "statistical projection + descriptive ranking, not causal",
        "C_H is coordinate-support alignment not mechanism",
        "Score lambda=0.01 DL=log2(1+n_col) is a stated regularizer choice, raw A_H*C_H also reported",
        "H absorbing energy != biological pathway",
        "if no stable shared H: non-translation residual is organism-specific unexplained, an important negative result not a failure",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        required.append(f"tools/bio_reality/data/cds_codon_abundance_{pair['organism']}.json")
        required.append(f"tools/bio_reality/data/gtrnadb_trna_all_copy_{pair['trna_organism']}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS-abundance and modeled tAI data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        if q_names != Q_NAMES_FIXED:
            raise ValueError(f"B*_Q6 coordinate order drifted: {q_names}")
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        per_organism: dict[str, dict[str, object]] = {}
        input_actual: dict[str, object] = {}
        complement_actual: dict[str, object] = {}
        skipped_h: dict[str, dict[str, object]] = {}

        inputs_joined_ok = True
        complement_ok = True
        a_perp_ok = True
        per_h_ok = True
        null_ok = True

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            cds_payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            joined_source = cds_payload.get("joined")
            if not isinstance(joined_source, list):
                raise ValueError(f"{organism} CDS payload must contain joined list")

            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            base = base_rows_with_ids(
                cds_payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
            )
            base["source_joined"] = joined_source
            base["source_protein_ids"] = base["protein_ids"]
            n_base = len(base["x_rows"]) if isinstance(base.get("x_rows"), list) else 0
            if n_base == 0:
                raise ValueError(f"{organism} has no usable abundance/CDS rows")

            base_complement = complement_from_rows(
                x_rows=base["x_rows"],  # type: ignore[arg-type]
                t_rows=base["t_rows"],  # type: ignore[arg-type]
                y_rows=base["y_rows"],  # type: ignore[arg-type]
                z_rows=base["z_rows"],  # type: ignore[arg-type]
                q_names=q_names,
            )

            reference_x, reference_t, reference_y, reference_z, _ = protein_rows(
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
            reference = complement_decomposition(
                x_tilde=residualize_with_basis(reference_x, orthonormal_basis_from_columns(reference_z)),
                t_tilde=residualize_with_basis(reference_t, orthonormal_basis_from_columns(reference_z)),
                y_tilde=residualize_with_basis(reference_y, orthonormal_basis_from_columns(reference_z)),
                q_names=q_names,
            )

            d_modeled = base_complement["d_modeled"]
            d_reference = reference["d"]
            d_reference_difference = None
            if isinstance(d_modeled, float) and isinstance(d_reference, float):
                d_reference_difference = abs(d_modeled - d_reference)
            d_roadmap = ROADMAP_D_MODELED.get(organism)
            d_roadmap_difference = None
            if isinstance(d_modeled, float) and isinstance(d_roadmap, float):
                d_roadmap_difference = abs(d_modeled - d_roadmap)

            input_actual[organism] = {
                "n": n_base,
                "rank_Z": base_complement["rank_condition_diagnostics"]["rank_Z"],
                "control_column_count": base_complement["rank_condition_diagnostics"]["control_column_count"],
                "n_joined_reported": base["summary"]["n_joined_reported"],  # type: ignore[index]
            }
            complement_actual[organism] = {
                "d_modeled": d_modeled,
                "d_reference_from_complement_function": d_reference,
                "d_reference_absolute_difference": d_reference_difference,
                "d_reference_matches_within_0_02": isinstance(d_reference_difference, float) and d_reference_difference < MODELED_ALIGNMENT_TOL,
                "d_roadmap_reference": d_roadmap,
                "d_roadmap_absolute_difference": d_roadmap_difference,
                "d_roadmap_matches_within_0_02": isinstance(d_roadmap_difference, float) and d_roadmap_difference < MODELED_ALIGNMENT_TOL,
                "P_Q_norm2": base_complement["P_Q_norm2"],
                "P_Q_perp_Tmod_norm2": base_complement["P_Q_perp_Tmod_norm2"],
            }

            inputs_joined_ok = inputs_joined_ok and n_base >= MIN_PROTEINS_PER_ORGANISM
            complement_ok = complement_ok and finite_unit_interval(d_modeled) and (
                isinstance(d_reference_difference, float) and d_reference_difference < MODELED_ALIGNMENT_TOL
            ) and (isinstance(d_roadmap_difference, float) and d_roadmap_difference < MODELED_ALIGNMENT_TOL)
            a_values = base_complement["a_perp_vector"]
            a_perp_ok = a_perp_ok and isinstance(a_values, list) and len(a_values) == len(q_names) and all(math.isfinite(float(value)) for value in a_values)

            candidates: dict[str, dict[str, object]] = {}
            skipped_h[organism] = {}
            for candidate in H_CANDIDATES:
                h_index, source_summary = load_h_index(
                    repo=repo,
                    organism=organism,
                    candidate=candidate,
                    base_rows=base,
                    code=code,
                    codons=codons,
                )
                if h_index is None:
                    candidates[candidate] = {
                        "status": "needs_data",
                        "reason": "local H readout file missing; no fetch attempted",
                        "n_joined": 0,
                        "source_summary": source_summary,
                    }
                    skipped_h[organism][candidate] = candidates[candidate]
                    continue
                h_rows = h_rows_from_index(base_rows=base, h_index=h_index, h_name=candidate)
                result = candidate_result(
                    organism=organism,
                    candidate=candidate,
                    rows=h_rows,
                    base_d_modeled=d_modeled if isinstance(d_modeled, float) else None,
                    q_names=q_names,
                    source_summary=source_summary,
                )
                candidates[candidate] = result
                if result.get("status") != "computed":
                    skipped_h[organism][candidate] = result

            ranking, h_o_star = assemble_ranking(candidates)
            computed_candidates = [value for value in candidates.values() if value.get("status") == "computed"]
            per_h_ok = per_h_ok and all(
                finite_unit_interval(value.get("A_H")) and finite_cosine(value.get("C_H"))
                for value in computed_candidates
            )
            null_ok = null_ok and all(
                isinstance(value.get("null_mean"), float)
                and isinstance(value.get("null_p95"), float)
                and isinstance(value.get("bonferroni_threshold"), float)
                and finite_unit_interval(value.get("null_mean"))
                and finite_unit_interval(value.get("null_p95"))
                and finite_unit_interval(value.get("bonferroni_threshold"))
                and value.get("dof_matched_null", {}).get("trial_count") == NULL_TRIALS
                for value in computed_candidates
            )

            per_organism[organism] = {
                **base["summary"],  # type: ignore[arg-type]
                **tai_summary,
                "n": n_base,
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_reference_difference,
                "d_modeled_matches_complement_experiment_within_0_02": isinstance(d_reference_difference, float) and d_reference_difference < MODELED_ALIGNMENT_TOL,
                "d_modeled_roadmap_reference": d_roadmap,
                "d_modeled_roadmap_absolute_difference": d_roadmap_difference,
                "d_modeled_matches_roadmap_within_0_02": isinstance(d_roadmap_difference, float) and d_roadmap_difference < MODELED_ALIGNMENT_TOL,
                "a_perp": base_complement["a_perp"],
                "P_Q_norm2": base_complement["P_Q_norm2"],
                "P_Q_perp_Tmod_norm2": base_complement["P_Q_perp_Tmod_norm2"],
                "rank_condition_diagnostics": base_complement["rank_condition_diagnostics"],
                "candidates": candidates,
                "ranking": ranking,
                "H_o_star": h_o_star,
                "dominant_coordinate_prior": DOMINANT_COORDINATE_PRIOR.get(organism),
            }

        shared = shared_analysis(per_organism)
        ranking_ok = all("ranking" in result for result in per_organism.values())
        status = "passed" if inputs_joined_ok and complement_ok and a_perp_ok and per_h_ok and null_ok and ranking_ok else "failed"
        reason = None
        if status != "passed":
            reason = "one or more computation gates failed"

        checks = [
            {
                "name": "inputs_joined",
                "passed": inputs_joined_ok,
                "actual": input_actual,
                "expected": f"every organism has base CDS-abundance join n >= {MIN_PROTEINS_PER_ORGANISM}; per-H joins below this are skipped as needs_data",
            },
            {
                "name": "complement_computed",
                "passed": complement_ok,
                "actual": complement_actual,
                "expected": f"d_modeled finite in [0,1] and aligned with the complement experiment/roadmap within {MODELED_ALIGNMENT_TOL}",
            },
            {
                "name": "a_perp_computed",
                "passed": a_perp_ok,
                "actual": {
                    organism: {
                        "a_perp_dimension": len(result["a_perp"]),
                        "coordinates": q_names,
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "finite 9-dimensional a_perp for every organism",
            },
            {
                "name": "per_H_A_and_C_computed",
                "passed": per_h_ok,
                "actual": {
                    organism: [
                        {
                            "H": item["H"],
                            "A_H": item["A_H"],
                            "C_H": item["C_H"],
                            "n_joined": item["n_joined"],
                        }
                        for item in result["ranking"]
                    ]
                    for organism, result in per_organism.items()
                },
                "expected": "for every computed H, A_H in [0,1] and C_H in [-1,1]; missing/sparse joins are not forced",
            },
            {
                "name": "dof_null_bonferroni_computed",
                "passed": null_ok,
                "actual": {
                    organism: {
                        item["H"]: {
                            "null_p95": item["null_p95"],
                            "bonferroni_threshold": item["bonferroni_threshold"],
                            "exceeds_bonferroni": item["exceeds_bonferroni"],
                            "n_joined": item["n_joined"],
                        }
                        for item in result["ranking"]
                    }
                    for organism, result in per_organism.items()
                },
                "expected": f"{NULL_TRIALS} deterministic dof-matched Gaussian null trials per computed H and Bonferroni threshold 1 - 0.05/K per organism",
            },
            {
                "name": "ranking_assembled",
                "passed": ranking_ok,
                "actual": {
                    organism: {
                        "H_o_star": result["H_o_star"],
                        "ranking": result["ranking"],
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "per-organism H ranking sorted by Score descending and H_o* selected only among Bonferroni-positive candidates",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {"cannot_claim": cannot_claim()},
                "expected": "statistical projection and descriptive ranking only",
            },
        ]

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "H-candidate readouts are ranked by direction-aware support for the modeled-tAI complement of the B*_Q6 abundance component.",
                "status_semantics": "passed means all base complements and all computable H rankings were produced; weak, negative, missing, or organism-specific H outcomes are reported without causal promotion",
                "decomposition": {
                    "Q": Q_NAMES_FIXED,
                    "T": "modeled tAI",
                    "P": "log10(abundance_ppm)",
                    "Z": controls_used(aa_order),
                    "P_Q": "Pi_{Q_e} P_e",
                    "P_Q_perp_Tmod": "(I - Pi_{T_mod}) P_Q",
                    "a_perp": "(Q_e^T Q_e + ridge I)^(-1) Q_e^T P_Q_perp_Tmod",
                    "A_H": "||Pi_H P_Q_perp_Tmod||^2 / ||P_Q_perp_Tmod||^2 on the organism,H join",
                    "a_H": "(Q_e^T Q_e + ridge I)^(-1) Q_e^T (Pi_H P_Q_perp_Tmod)",
                    "C_H": "<a_H,a_perp>/(||a_H|| ||a_perp||), zero if either support vector is zero",
                    "Score": "A_H*C_H - lambda*DL(H)",
                    "DL_H": "log2(1+n_columns(H))",
                    "lambda": LAMBDA_DL,
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "H_candidates": H_CANDIDATES,
                "per_organism": per_organism,
                "ranking": {organism: result["ranking"] for organism, result in per_organism.items()},
                "H_o_star_by_organism": {organism: result["H_o_star"] for organism, result in per_organism.items()},
                "shared_analysis": shared,
                "skipped_or_needs_data_H": skipped_h,
                "honest": {
                    "cannot_claim": cannot_claim(),
                    "negative_result_policy": "absence of a stable shared H is reported as organism-specific unexplained residual, not as a failed computation",
                    "no_fetch_policy": "only local readout JSON files were used; missing H files remain needs_data",
                    "sparse_join_policy": f"per-organism,H joins with n_joined < {MIN_PROTEINS_PER_ORGANISM} are skipped/needs_data",
                },
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable H-candidate ranking-table input")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Greedy readout-basis extraction for the B*_Q6 non-translation residual.

This is a descriptive statistical projection audit. Greedy absorption of
residual energy is compression evidence only, not causation or mechanism.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
import datetime as dt
from collections.abc import Callable
from typing import Any

from run_b_star_q6_h_candidate_localization_powered import LOCALIZATION_CATEGORIES
from run_b_star_q6_h_candidate_mrna_powered import mrna_by_protein
from run_b_star_q6_h_candidate_protein_features_powered import CANDIDATES as PROTEIN_FEATURE_CANDIDATES
from run_b_star_q6_h_candidate_turnover_powered import turnover_by_protein as yeast_turnover_by_protein
from run_b_star_q6_measured_mediation_powered import abundance_by_protein
from run_b_star_q6_measured_te_survival_powered import te_by_protein
from run_b_star_q6_measured_trna_tai_residual_absorption_powered import measured_trna_tai_weights
from run_b_star_q6_protein_omics_survival_powered import orthonormal_basis_from_columns, residualize, standard_amino_acids
from run_b_star_q6_translation_complement_residual_powered import (
    RIDGE_EPS,
    complement_decomposition,
    project_onto_design,
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
from run_b_star_q6_translation_survival_powered import fibers_for, project_syn, q_vectors, standard_code, synthesize_tai_records


EXPERIMENT_ID = "b_star_q6_residual_basis_extraction_powered"
CLAIM_ID = "h3.cross_layer_relation.residual_basis_extraction.b_star_q6_non_translation_residual_powered"
CONJECTURE_ID = "q6.residual-basis-extraction.greedy-readout.cross-layer"

SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02
NULL_TRIALS = 128
LAMBDA = 0.01
COMPRESSIBLE_RHO_THRESHOLD = 0.50
PERSISTENT_RHO_THRESHOLD = 0.80
STRONG_PERSISTENT_RHO_FLOOR = 0.97
MIN_COMPUTED_ORGANISMS_FOR_PERSISTENCE = 4

READOUT_ORDER = [
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

FEATURE_TO_UNIPROT_NAME = {
    "ptm_density": "ptm_density",
    "complex_member": "complex_member",
    "tm_count": "tm_count",
    "domain_count": "domain_count",
}

TRNA_SOURCE_ORGANISMS = {"saccharomyces_cerevisiae", "homo_sapiens", "danio_rerio"}
STARTED_AT = dt.datetime.now(dt.timezone.utc).isoformat()


class CandidateSpec:
    def __init__(
        self,
        *,
        name: str,
        columns: list[str],
        getter: Callable[[str], list[float] | None],
        source_summary: dict[str, object],
    ) -> None:
        self.name = name
        self.columns = columns
        self.getter = getter
        self.source_summary = source_summary


def emit(status: str, **kw: object) -> None:
    checks = kw.pop("checks", [])
    result = kw.pop("result", None)
    if result is None:
        result = kw
    elif kw and isinstance(result, dict):
        result = {**result, **kw}
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks if isinstance(checks, list) else [],
        "result": result if isinstance(result, dict) else {"value": result},
        "started_at": STARTED_AT,
        "completed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
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


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def vector_sub(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def matrix_rows(matrix: list[list[float]], indexes: list[int]) -> list[list[float]]:
    return [matrix[index] for index in indexes]


def vector_rows(vector: list[float], indexes: list[int]) -> list[float]:
    return [vector[index] for index in indexes]


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def select_columns(matrix: list[list[float]], indexes: list[int]) -> list[list[float]]:
    return [[row[index] for index in indexes] for row in matrix]


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


def nonconstant_column_indexes(matrix: list[list[float]], tol: float = 1e-12) -> list[int]:
    if not matrix:
        return []
    out: list[int] = []
    for col in range(len(matrix[0])):
        values = [row[col] for row in matrix]
        if max(values) - min(values) > tol:
            out.append(col)
    return out


def lcg_uniform(seed: int) -> tuple[int, float]:
    next_seed = (1664525 * seed + 1013904223) & 0xFFFFFFFF
    return next_seed, (next_seed + 0.5) / 4294967296.0


def deterministic_gaussian_matrix(
    *,
    organism: str,
    step_index: int,
    candidate_name: str,
    trial: int,
    n_rows: int,
    k_cols: int,
) -> list[list[float]]:
    material = f"{EXPERIMENT_ID}|{organism}|{step_index}|{candidate_name}|{trial}"
    digest = hashlib.sha256(material.encode("utf-8")).digest()
    seed = int.from_bytes(digest[:4], "big")
    values: list[float] = []
    need = n_rows * k_cols
    while len(values) < need:
        seed, u1 = lcg_uniform(seed)
        seed, u2 = lcg_uniform(seed)
        radius = math.sqrt(-2.0 * math.log(max(u1, 1e-12)))
        angle = 2.0 * math.pi * u2
        values.append(radius * math.cos(angle))
        if len(values) < need:
            values.append(radius * math.sin(angle))
    return [values[row * k_cols:(row + 1) * k_cols] for row in range(n_rows)]


def residualize_vector_with_basis(vector: list[float], basis: list[list[float]]) -> list[float]:
    out = list(vector)
    for q in basis:
        coeff = sum(vector[index] * q[index] for index in range(len(vector)))
        if coeff == 0.0:
            continue
        for index in range(len(vector)):
            out[index] -= coeff * q[index]
    return out


def normalize_vector(vector: list[float], tol: float = 1e-10) -> list[float] | None:
    norm = math.sqrt(vector_norm2(vector))
    if norm <= tol:
        return None
    return [value / norm for value in vector]


def deterministic_gaussian_vector(
    *,
    organism: str,
    step_index: int,
    candidate_name: str,
    trial: int,
    column: int,
    n_rows: int,
) -> list[float]:
    material = f"{EXPERIMENT_ID}|{organism}|{step_index}|{candidate_name}|{trial}|{column}"
    digest = hashlib.sha256(material.encode("utf-8")).digest()
    seed = int.from_bytes(digest[:4], "big")
    values: list[float] = []
    while len(values) < n_rows:
        seed, u1 = lcg_uniform(seed)
        seed, u2 = lcg_uniform(seed)
        radius = math.sqrt(-2.0 * math.log(max(u1, 1e-12)))
        angle = 2.0 * math.pi * u2
        values.append(radius * math.cos(angle))
        if len(values) < n_rows:
            values.append(radius * math.sin(angle))
    return values


def deterministic_gaussian_stream_sum_squares(
    *,
    organism: str,
    step_index: int,
    candidate_name: str,
    trial: int,
    stream_name: str,
    count: int,
) -> float:
    material = f"{EXPERIMENT_ID}|{organism}|{step_index}|{candidate_name}|{trial}|{stream_name}"
    digest = hashlib.sha256(material.encode("utf-8")).digest()
    seed = int.from_bytes(digest[:4], "big")
    total = 0.0
    produced = 0
    while produced < count:
        seed, u1 = lcg_uniform(seed)
        seed, u2 = lcg_uniform(seed)
        radius = math.sqrt(-2.0 * math.log(max(u1, 1e-12)))
        angle = 2.0 * math.pi * u2
        z1 = radius * math.cos(angle)
        total += z1 * z1
        produced += 1
        if produced < count:
            z2 = radius * math.sin(angle)
            total += z2 * z2
            produced += 1
    return total


def deterministic_null_basis(
    *,
    organism: str,
    step_index: int,
    candidate_name: str,
    trial: int,
    n_rows: int,
    k_cols: int,
    z_basis: list[list[float]],
) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in range(k_cols):
        residual = residualize_vector_with_basis(
            deterministic_gaussian_vector(
                organism=organism,
                step_index=step_index,
                candidate_name=candidate_name,
                trial=trial,
                column=column,
                n_rows=n_rows,
            ),
            z_basis,
        )
        for q in basis:
            coeff = sum(residual[index] * q[index] for index in range(n_rows))
            if coeff == 0.0:
                continue
            for index in range(n_rows):
                residual[index] -= coeff * q[index]
        normalized = normalize_vector(residual)
        if normalized is not None:
            basis.append(normalized)
    return basis


def absorption_by_basis(basis: list[list[float]], target: list[float]) -> dict[str, object]:
    denominator = vector_norm2(target)
    if denominator <= SURVIVAL_EPS:
        return {"absorbed": None, "absorbed_norm2": 0.0, "projected": [0.0 for _ in target], "rank": len(basis)}
    projected = [0.0 for _ in target]
    absorbed_norm2 = 0.0
    for q in basis:
        coeff = sum(target[index] * q[index] for index in range(len(target)))
        absorbed_norm2 += coeff * coeff
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return {
        "absorbed": bounded_unit(absorbed_norm2 / denominator),
        "absorbed_norm2": absorbed_norm2,
        "projected": projected,
        "rank": len(basis),
    }


def absorption_by_design(design_tilde: list[list[float]], target: list[float]) -> dict[str, object]:
    return absorption_by_basis(orthonormal_basis_from_columns(design_tilde), target)


def dof_matched_null(
    *,
    organism: str,
    step_index: int,
    candidate_name: str,
    n_rows: int,
    k_cols: int,
    z_basis: list[list[float]],
    target: list[float],
    trials: int = NULL_TRIALS,
) -> dict[str, object]:
    absorptions: list[float] = []
    residual_df = max(0, n_rows - len(z_basis))
    effective_rank = max(0, min(k_cols, residual_df))
    for trial in range(trials):
        numerator = deterministic_gaussian_stream_sum_squares(
            organism=organism,
            step_index=step_index,
            candidate_name=candidate_name,
            trial=trial,
            stream_name="selected",
            count=effective_rank,
        )
        denominator_tail = deterministic_gaussian_stream_sum_squares(
            organism=organism,
            step_index=step_index,
            candidate_name=candidate_name,
            trial=trial,
            stream_name="orthogonal_tail",
            count=max(0, residual_df - effective_rank),
        )
        denominator = numerator + denominator_tail
        absorptions.append(0.0 if denominator <= SURVIVAL_EPS else bounded_unit(numerator / denominator))
    return {
        "trial_count": trials,
        "absorbed_null_mean": mean(absorptions),
        "absorbed_null_p95": percentile_nearest_rank(absorptions, 0.95),
        "rank_min": effective_rank,
        "rank_max": effective_rank,
        "rank_unique_values": [effective_rank],
        "residual_df_after_Z": residual_df,
        "randomness": "hashlib-derived Gaussian chi-square energy ratio for a k-dimensional random subspace inside the Z-orthogonal residual df; no system time",
    }


def base_row_for_cds_item(
    *,
    item: dict[str, object],
    row_index: int,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[float], list[float], list[float], list[float], str] | None:
    protein_id = item.get("protein_id")
    if not isinstance(protein_id, str) or not protein_id:
        return None
    abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
    if abundance <= 0.0:
        return None
    cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        return None
    counts = codon_counts_rna(item, codons, organism, row_index)
    total = sum(counts.values())
    if total <= 0:
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
        return None
    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    z_row = [1.0, math.log(cds_len_nt)] + [aa_counts[aa] / aa_total for aa in aa_order] + [gc3, m_density]
    return x_row, t_row, y_row, z_row, protein_id


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
) -> tuple[list[str], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    protein_ids: list[str] = []
    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {"non_object": 0, "unusable_base_row": 0}
    for row_index, raw in enumerate(joined):
        if not isinstance(raw, dict):
            skipped["non_object"] += 1
            continue
        row = base_row_for_cds_item(
            item=raw,
            row_index=row_index,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        if row is None:
            skipped["unusable_base_row"] += 1
            continue
        x_row, t_row, y_row, z_row, protein_id = row
        protein_ids.append(protein_id)
        x_rows.append(x_row)
        t_rows.append(t_row)
        y_rows.append(y_row)
        z_rows.append(z_row)
    return protein_ids, x_rows, t_rows, y_rows, z_rows, {
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_base_rows": len(x_rows),
        "skipped_base_cds_records": skipped,
    }


def trna_records_from_local_payload(
    *,
    payload: dict[str, object],
    organism: str,
    code: dict[str, str],
    codons: list[str],
) -> tuple[list[dict[str, str]], list[dict[str, object]]]:
    raw = payload.get("trna_anticodon_gene_copy_counts_for_elongator_tai")
    if not isinstance(raw, dict):
        return [], []
    copies: dict[str, int] = {}
    for anticodon, count in raw.items():
        n = int(numeric(count, f"trna_anticodon_gene_copy_counts_for_elongator_tai.{anticodon}"))
        copies[str(anticodon).replace("T", "U")] = max(0, n)
    return synthesize_tai_records(organism=organism, code=code, codons=codons, trna_all_copies=copies)


def measured_trna_from_gene_copy_counts(
    *,
    organism: str,
    repo: pathlib.Path,
    code: dict[str, str],
    codons: list[str],
) -> tuple[dict[str, float] | None, dict[str, object]]:
    path = repo / f"tools/fibonacci_reality/data/trna_gene_copy_{organism}.json"
    if not path.exists():
        return None, {"available": False, "reason": "local measured tRNA gene-copy payload missing"}
    payload = load_json(path)
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    records, ambiguous = trna_records_from_local_payload(payload=payload, organism=organism, code=code, codons=codons)
    if not records:
        return None, {"available": False, "reason": "local measured tRNA payload has no elongator anticodon counts"}
    weights, summary = measured_trna_tai_weights(organism=organism, code=code, codons=codons, records=records)
    return weights, {
        "available": True,
        "data_path": str(path.relative_to(repo)),
        "measured_trna_payload_sha256": payload.get("payload_sha256"),
        "ambiguous_anticodon_assignments": ambiguous,
        **summary,
    }


def build_candidate_specs(
    *,
    repo: pathlib.Path,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    measured_trna_weights: dict[str, float] | None,
) -> dict[str, CandidateSpec]:
    specs: dict[str, CandidateSpec] = {}

    ribosome_path = repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json"
    if ribosome_path.exists():
        ribosome_payload = load_json(ribosome_path)
        if not isinstance(ribosome_payload, dict):
            raise ValueError(f"{ribosome_path} must contain a JSON object")
        mrna_index, mrna_summary = mrna_by_protein(ribosome_payload, organism)
        te_index, te_summary = te_by_protein(ribosome_payload, organism)
        specs["mrna"] = CandidateSpec(
            name="mrna",
            columns=["log10_mrna"],
            getter=lambda protein_id, index=mrna_index: [math.log10(index[protein_id]["mrna"])] if protein_id in index else None,
            source_summary={"data_path": str(ribosome_path.relative_to(repo)), **mrna_summary},
        )
        specs["measured_te"] = CandidateSpec(
            name="measured_te",
            columns=["log10_measured_te"],
            getter=lambda protein_id, index=te_index: [math.log10(index[protein_id]["te"])] if protein_id in index else None,
            source_summary={"data_path": str(ribosome_path.relative_to(repo)), **te_summary},
        )

    if measured_trna_weights is not None:
        specs["measured_trna_tai"] = CandidateSpec(
            name="measured_trna_tai",
            columns=["measured_trna_tai_geomean"],
            getter=lambda protein_id: None,
            source_summary={"definition": "per-CDS geometric mean from local measured tRNA gene-copy tAI weights"},
        )

    turnover_path = repo / f"tools/fibonacci_reality/data/protein_turnover_{organism}.json"
    if turnover_path.exists():
        turnover_payload = load_json(turnover_path)
        if not isinstance(turnover_payload, dict):
            raise ValueError(f"{turnover_path} must contain a JSON object")
        turnover_index, turnover_summary = yeast_turnover_by_protein(turnover_payload)
        specs["turnover"] = CandidateSpec(
            name="turnover",
            columns=["log10_protein_half_life"],
            getter=lambda protein_id, index=turnover_index: [math.log10(index[protein_id])] if protein_id in index else None,
            source_summary={"data_path": str(turnover_path.relative_to(repo)), **turnover_summary},
        )

    localization_path = repo / f"tools/fibonacci_reality/data/subcellular_localization_{organism}.json"
    if localization_path.exists():
        localization_payload = load_json(localization_path)
        proteins = localization_payload.get("proteins") if isinstance(localization_payload, dict) else None
        if not isinstance(proteins, dict):
            raise ValueError(f"{localization_path} must contain proteins object")

        def localization_getter(protein_id: str, index: dict[str, object] = proteins) -> list[float] | None:
            record = index.get(protein_id)
            if not isinstance(record, dict):
                return None
            categories = record.get("categories")
            if not isinstance(categories, list) or not categories:
                return None
            category_set = set(str(category) for category in categories)
            return [1.0 if category in category_set else 0.0 for category in LOCALIZATION_CATEGORIES]

        specs["localization"] = CandidateSpec(
            name="localization",
            columns=LOCALIZATION_CATEGORIES,
            getter=localization_getter,
            source_summary={
                "data_path": str(localization_path.relative_to(repo)),
                "n_localization_records": localization_payload.get("n_string_localization_records"),
                "source_kind": localization_payload.get("source_kind"),
            },
        )

    feature_path = repo / f"tools/fibonacci_reality/data/uniprot_protein_features_{organism}.json"
    if feature_path.exists():
        feature_payload = load_json(feature_path)
        proteins = feature_payload.get("proteins") if isinstance(feature_payload, dict) else None
        if not isinstance(proteins, dict):
            raise ValueError(f"{feature_path} must contain proteins object")
        for readout_name, feature_name in FEATURE_TO_UNIPROT_NAME.items():
            if feature_name not in PROTEIN_FEATURE_CANDIDATES:
                continue

            def feature_getter(
                protein_id: str,
                *,
                index: dict[str, object] = proteins,
                field: str = feature_name,
            ) -> list[float] | None:
                record = index.get(protein_id)
                if not isinstance(record, dict):
                    return None
                features = record.get("features")
                if not isinstance(features, dict) or field not in features:
                    return None
                value = features[field]
                if isinstance(value, bool) or not isinstance(value, (int, float)):
                    return None
                return [float(value)]

            specs[readout_name] = CandidateSpec(
                name=readout_name,
                columns=[feature_name],
                getter=feature_getter,
                source_summary={
                    "data_path": str(feature_path.relative_to(repo)),
                    "n_feature_records": feature_payload.get("n_string_feature_records"),
                    "source_kind": feature_payload.get("source_kind"),
                },
            )

    return specs


def measured_trna_tai_value(counts: dict[str, int], weights: dict[str, float]) -> float | None:
    total = sum(counts.values())
    if total <= 0:
        return None
    logs = []
    for codon, count in counts.items():
        weight = weights.get(codon)
        if weight is None or weight <= 0.0:
            return None
        if count:
            logs.append(count * math.log(weight))
    return math.exp(sum(logs) / total)


def rows_for_candidate_set(
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
    measured_trna_weights: dict[str, float] | None,
    candidates: dict[str, CandidateSpec],
) -> tuple[
    list[str],
    list[list[float]],
    list[list[float]],
    list[list[float]],
    list[list[float]],
    dict[str, list[list[float]]],
    dict[str, object],
]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    protein_ids: list[str] = []
    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    h_rows = {name: [] for name in candidates}
    skipped = {"non_object": 0, "unusable_base_row": 0, "candidate_missing": {name: 0 for name in candidates}}

    for row_index, raw in enumerate(joined):
        if not isinstance(raw, dict):
            skipped["non_object"] += 1
            continue
        base = base_row_for_cds_item(
            item=raw,
            row_index=row_index,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        if base is None:
            skipped["unusable_base_row"] += 1
            continue
        x_row, t_row, y_row, z_row, protein_id = base
        candidate_values: dict[str, list[float]] = {}
        counts = codon_counts_rna(raw, codons, organism, row_index)
        missing = False
        for name, spec in candidates.items():
            if name == "measured_trna_tai":
                value = measured_trna_tai_value(counts, measured_trna_weights or {})
                row = None if value is None else [value]
            else:
                row = spec.getter(protein_id)
            if row is None or len(row) != len(spec.columns) or not all(math.isfinite(value) for value in row):
                skipped["candidate_missing"][name] += 1
                missing = True
                break
            candidate_values[name] = row
        if missing:
            continue
        protein_ids.append(protein_id)
        x_rows.append(x_row)
        t_rows.append(t_row)
        y_rows.append(y_row)
        z_rows.append(z_row)
        for name, row in candidate_values.items():
            h_rows[name].append(row)

    summary = {
        "n_joined_common_candidate_set": len(x_rows),
        "candidate_set": list(candidates),
        "skipped_cds_records": skipped,
    }
    return protein_ids, x_rows, t_rows, y_rows, z_rows, h_rows, summary


def candidate_self_join_counts(
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
    measured_trna_weights: dict[str, float] | None,
    specs: dict[str, CandidateSpec],
) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for name in READOUT_ORDER:
        spec = specs.get(name)
        if spec is None:
            out[name] = {"available": False, "skip_reason": "local readout payload absent"}
            continue
        _, x_rows, _, _, _, h_rows, summary = rows_for_candidate_set(
            cds_payload=cds_payload,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
            measured_trna_weights=measured_trna_weights,
            candidates={name: spec},
        )
        matrix = h_rows[name]
        keep = nonconstant_column_indexes(matrix)
        out[name] = {
            "available": True,
            "n_joined": len(x_rows),
            "n_columns_raw": len(spec.columns),
            "n_columns_used_after_constant_filter": len(keep),
            "passes_n_joined_gate": len(x_rows) >= MIN_PROTEINS_PER_ORGANISM,
            "passes_nonconstant_gate": bool(keep),
            "source_summary": spec.source_summary,
            "join_summary": summary,
        }
    return out


def residual_target(
    *,
    x_rows: list[list[float]],
    t_rows: list[list[float]],
    y_rows: list[list[float]],
    z_rows: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    x_tilde, rank_z = residualize(x_rows, z_rows)
    t_tilde, _ = residualize(t_rows, z_rows)
    y_tilde, _ = residualize(y_rows, z_rows)
    comp = complement_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
    y_col = [row[0] for row in y_tilde]
    p_q, _ = project_onto_design(x_tilde, y_col)
    p_q_from_t, _ = project_onto_design(t_tilde, p_q)
    r0 = subtract_vectors(p_q, p_q_from_t)
    return {
        "rank_Z": rank_z,
        "x_tilde": x_tilde,
        "t_tilde": t_tilde,
        "y_tilde": y_tilde,
        "R0": r0,
        "d_modeled": comp["d"],
        "P_Q_norm2": comp["P_Q_norm2"],
        "R0_norm2": comp["P_Q_perp_T_norm2"],
    }


def recursive_extraction(
    *,
    organism: str,
    z_rows: list[list[float]],
    target: list[float],
    h_rows: dict[str, list[list[float]]],
    candidate_columns: dict[str, list[str]],
) -> dict[str, object]:
    remaining = list(h_rows)
    current = list(target)
    z_basis = orthonormal_basis_from_columns(z_rows)
    h_tilde_by_name = {name: residualize(h_rows[name], z_rows)[0] for name in h_rows}
    h_basis_by_name = {name: orthonormal_basis_from_columns(h_tilde_by_name[name]) for name in h_tilde_by_name}
    initial_norm2 = vector_norm2(target)
    steps: list[dict[str, object]] = []
    rho_curve = [1.0]
    selected_order: list[str] = []

    for step_index in range(1, len(remaining) + 1):
        current_norm2 = vector_norm2(current)
        if current_norm2 <= SURVIVAL_EPS:
            break

        scored: list[dict[str, object]] = []
        for name in remaining:
            absorbed = absorption_by_basis(h_basis_by_name[name], current)
            increment = absorbed["absorbed"]
            if not isinstance(increment, float):
                continue
            n_cols = len(h_tilde_by_name[name][0]) if h_tilde_by_name[name] else 0
            dl = math.log2(1.0 + n_cols)
            scored.append(
                {
                    "name": name,
                    "increment": increment,
                    "score": increment - LAMBDA * dl,
                    "dl": dl,
                    "n_columns": n_cols,
                    "projected": absorbed["projected"],
                    "rank": absorbed["rank"],
                }
            )
        if not scored:
            break
        scored.sort(key=lambda item: (-float(item["score"]), READOUT_ORDER.index(str(item["name"]))))
        best = scored[0]
        name = str(best["name"])
        projected = best["projected"]
        if not isinstance(projected, list):
            raise ValueError(f"{organism} step {step_index} did not produce projected vector")
        next_current = vector_sub(current, [float(value) for value in projected])
        next_norm2 = vector_norm2(next_current)
        rho = 0.0 if initial_norm2 <= SURVIVAL_EPS else bounded_unit(next_norm2 / initial_norm2)
        null = dof_matched_null(
            organism=organism,
            step_index=step_index,
            candidate_name=name,
            n_rows=len(z_rows),
            k_cols=int(best["n_columns"]),
            z_basis=z_basis,
            target=current,
        )
        null_p95 = null["absorbed_null_p95"]
        exceeds_null = isinstance(null_p95, float) and float(best["increment"]) > null_p95
        steps.append(
            {
                "step": step_index,
                "selected": name,
                "incremental_absorbed_fraction_of_R_prev": best["increment"],
                "rho_k": rho,
                "exceeds_null": exceeds_null,
                "null_p95": null_p95,
                "null_mean": null["absorbed_null_mean"],
                "score": best["score"],
                "DL": best["dl"],
                "lambda": LAMBDA,
                "n_columns": best["n_columns"],
                "columns": candidate_columns[name],
                "rank": best["rank"],
                "null": null,
            }
        )
        selected_order.append(name)
        rho_curve.append(rho)
        current = next_current
        remaining.remove(name)

    return {
        "steps": steps,
        "selected_order": selected_order,
        "rho_curve": rho_curve,
        "final_rho": rho_curve[-1] if rho_curve else 1.0,
        "final_residual_norm2": vector_norm2(current),
    }


def choose_basis_compatible_join(
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
    measured_trna_weights: dict[str, float] | None,
    specs: dict[str, CandidateSpec],
    eligible_names: list[str],
    reference_d: float | None,
    self_counts: dict[str, dict[str, object]],
) -> dict[str, object]:
    names = list(eligible_names)
    pruning: list[dict[str, object]] = []
    while names:
        candidate_specs = {name: specs[name] for name in names}
        protein_ids, x_rows, t_rows, y_rows, z_rows, h_raw, summary = rows_for_candidate_set(
            cds_payload=cds_payload,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
            measured_trna_weights=measured_trna_weights,
            candidates=candidate_specs,
        )
        common_n = len(x_rows)
        d_difference = None
        target = None
        d_matches = False
        if common_n >= MIN_PROTEINS_PER_ORGANISM:
            target = residual_target(x_rows=x_rows, t_rows=t_rows, y_rows=y_rows, z_rows=z_rows, q_names=q_names)
            d_modeled = target["d_modeled"]
            if isinstance(d_modeled, float) and isinstance(reference_d, float):
                d_difference = abs(d_modeled - reference_d)
                d_matches = d_difference < MODELED_ALIGNMENT_TOL
            if d_matches:
                return {
                    "names": names,
                    "protein_ids": protein_ids,
                    "x_rows": x_rows,
                    "t_rows": t_rows,
                    "y_rows": y_rows,
                    "z_rows": z_rows,
                    "h_raw": h_raw,
                    "summary": summary,
                    "target": target,
                    "d_difference": d_difference,
                    "d_matches": d_matches,
                    "pruning": pruning,
                }
        removable = sorted(
            names,
            key=lambda name: (
                int(self_counts.get(name, {}).get("n_joined") or 0),
                -READOUT_ORDER.index(name),
            ),
        )[0]
        pruning.append(
            {
                "removed_readout": removable,
                "reason": "basis-compatible common join did not preserve d_modeled alignment with the full complement reference",
                "common_n_before_removal": common_n,
                "d_difference_before_removal": d_difference,
                "alignment_tolerance": MODELED_ALIGNMENT_TOL,
            }
        )
        names.remove(removable)
    return {"names": [], "pruning": pruning}


def classify_extraction(steps: list[dict[str, object]], final_rho: float) -> str:
    if not steps:
        return "needs_data"
    all_prefix_excess = True
    for step in steps:
        if float(step["rho_k"]) < COMPRESSIBLE_RHO_THRESHOLD:
            return "compressible" if all_prefix_excess and step["exceeds_null"] is True else "persistent"
        all_prefix_excess = all_prefix_excess and step["exceeds_null"] is True
    if final_rho <= COMPRESSIBLE_RHO_THRESHOLD and all_prefix_excess:
        return "compressible"
    if final_rho >= PERSISTENT_RHO_THRESHOLD:
        return "persistent"
    if any(step["exceeds_null"] is not True for step in steps):
        return "persistent"
    return "partially_compressible"


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "greedy basis extraction is descriptive compression, not mechanism",
        "λ=0.01 DL=log2(1+n_col) stated regularizer",
        "Π_H absorbing residual energy ≠ biological causation",
        "persistent non-decaying R_k = unexplained residual (needs new readout type or more data), an important negative result not a failure",
        "greedy not guaranteed globally optimal basis",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{pair['organism']}.json")
        required.append(f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{pair['trna_organism']}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS and modeled-tAI data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        per_organism: dict[str, dict[str, object]] = {}
        checks_actual: dict[str, object] = {}
        all_inputs_ok = True
        all_complement_ok = True
        all_recursive_ok = True
        all_null_ok = True
        all_labeled = True
        computed_count = 0

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            measured_trna_weights, measured_trna_summary = measured_trna_from_gene_copy_counts(
                organism=organism,
                repo=repo,
                code=code,
                codons=codons,
            )
            specs = build_candidate_specs(
                repo=repo,
                organism=organism,
                code=code,
                codons=codons,
                measured_trna_weights=measured_trna_weights,
            )
            self_counts = candidate_self_join_counts(
                cds_payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
                measured_trna_weights=measured_trna_weights,
                specs=specs,
            )
            eligible_names = [
                name for name in READOUT_ORDER
                if self_counts.get(name, {}).get("passes_n_joined_gate") is True
                and self_counts.get(name, {}).get("passes_nonconstant_gate") is True
                and name in specs
            ]

            base_ids, base_x, base_t, base_y, base_z, base_summary = base_rows_with_ids(
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
            base_x_tilde, _ = residualize(base_x, base_z)
            base_t_tilde, _ = residualize(base_t, base_z)
            base_y_tilde, _ = residualize(base_y, base_z)
            base_comp = complement_decomposition(
                x_tilde=base_x_tilde,
                t_tilde=base_t_tilde,
                y_tilde=base_y_tilde,
                q_names=q_names,
            )

            organism_result: dict[str, object] = {
                **tai_summary,
                "measured_trna_source": measured_trna_summary,
                "base_full_join": base_summary,
                "d_modeled_reference_full_join": base_comp["d"],
                "candidate_join_inventory": self_counts,
                "candidate_count_eligible_self_join": len(eligible_names),
                "eligible_self_join_candidates": eligible_names,
                "skipped_readouts": {
                    name: self_counts.get(name, {"available": False, "skip_reason": "local readout payload absent"})
                    for name in READOUT_ORDER
                    if name not in eligible_names
                },
            }

            if not eligible_names:
                organism_result.update(
                    {
                        "status": "needs_data",
                        "reason": "no readout candidate has local data, n_joined >= 500, and at least one nonconstant column",
                        "label": "needs_data",
                    }
                )
                per_organism[organism] = organism_result
                continue

            basis_choice = choose_basis_compatible_join(
                cds_payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
                measured_trna_weights=measured_trna_weights,
                specs=specs,
                eligible_names=eligible_names,
                reference_d=base_comp["d"] if isinstance(base_comp["d"], float) else None,
                self_counts=self_counts,
            )
            basis_names = basis_choice.get("names")
            if not isinstance(basis_names, list) or not basis_names:
                organism_result.update(
                    {
                        "status": "needs_data",
                        "reason": "no basis-compatible common readout join preserved d_modeled alignment with the full complement reference",
                        "basis_compatibility_pruning": basis_choice.get("pruning"),
                        "label": "needs_data",
                    }
                )
                per_organism[organism] = organism_result
                continue

            x_rows = basis_choice["x_rows"]
            t_rows = basis_choice["t_rows"]
            y_rows = basis_choice["y_rows"]
            z_rows = basis_choice["z_rows"]
            h_raw = basis_choice["h_raw"]
            common_summary = basis_choice["summary"]
            target = basis_choice["target"]
            if not isinstance(x_rows, list) or not isinstance(t_rows, list) or not isinstance(y_rows, list) or not isinstance(z_rows, list):
                raise ValueError(f"{organism} basis-compatible rows were not materialized")
            if not isinstance(h_raw, dict) or not isinstance(common_summary, dict) or not isinstance(target, dict):
                raise ValueError(f"{organism} basis-compatible target was not materialized")
            common_n = len(x_rows)
            if common_n < MIN_PROTEINS_PER_ORGANISM:
                organism_result.update(
                    {
                        "status": "needs_data",
                        "reason": "common protein_id intersection across eligible readouts is below n_joined >= 500",
                        "common_candidate_join": common_summary,
                        "label": "needs_data",
                    }
                )
                per_organism[organism] = organism_result
                continue

            h_rows: dict[str, list[list[float]]] = {}
            candidate_columns: dict[str, list[str]] = {}
            constant_filtered: dict[str, object] = {}
            candidate_specs = {name: specs[name] for name in basis_names}
            for name, matrix in h_raw.items():
                keep = nonconstant_column_indexes(matrix)
                if not keep:
                    continue
                h_rows[name] = select_columns(matrix, keep)
                candidate_columns[name] = [candidate_specs[name].columns[index] for index in keep]
                constant_filtered[name] = {
                    "n_columns_raw": len(candidate_specs[name].columns),
                    "n_columns_used": len(keep),
                    "columns_used": candidate_columns[name],
                }
            if not h_rows:
                organism_result.update(
                    {
                        "status": "needs_data",
                        "reason": "common join exists but all readout columns are constant",
                        "common_candidate_join": common_summary,
                        "label": "needs_data",
                    }
                )
                per_organism[organism] = organism_result
                continue

            d_modeled = target["d_modeled"]
            d_reference = base_comp["d"]
            d_difference = basis_choice["d_difference"]
            d_matches = basis_choice["d_matches"]
            extraction = recursive_extraction(
                organism=organism,
                z_rows=z_rows,
                target=target["R0"],
                h_rows=h_rows,
                candidate_columns=candidate_columns,
            )
            steps = extraction["steps"]
            final_rho = float(extraction["final_rho"])
            label = classify_extraction(steps, final_rho)
            rho_curve = extraction["rho_curve"]
            monotone = all(float(rho_curve[index]) <= float(rho_curve[index - 1]) + 1e-8 for index in range(1, len(rho_curve)))
            bounded = all(finite_unit_interval(value) for value in rho_curve)
            null_ok = all(isinstance(step.get("null_p95"), float) and finite_unit_interval(step.get("null_p95")) for step in steps)

            computed_count += 1
            all_inputs_ok = all_inputs_ok and common_n >= MIN_PROTEINS_PER_ORGANISM
            all_complement_ok = all_complement_ok and finite_unit_interval(d_modeled) and d_matches
            all_recursive_ok = all_recursive_ok and monotone and bounded and bool(steps)
            all_null_ok = all_null_ok and null_ok
            all_labeled = all_labeled and label in {"compressible", "persistent", "partially_compressible"}

            organism_result.update(
                {
                    "status": "computed",
                    "n_joined_common": common_n,
                    "candidate_count": len(h_rows),
                    "candidate_columns": candidate_columns,
                    "basis_compatible_candidates": list(h_rows),
                    "basis_compatibility_pruning": basis_choice.get("pruning"),
                    "constant_column_filter": constant_filtered,
                    "common_candidate_join": common_summary,
                    "d_modeled": d_modeled,
                    "d_modeled_reference_full_join": d_reference,
                    "d_modeled_reference_absolute_difference": d_difference,
                    "d_modeled_aligns_with_full_join_within_0_02": d_matches,
                    "P_Q_norm2": target["P_Q_norm2"],
                    "R0_norm2": target["R0_norm2"],
                    "rank_Z": target["rank_Z"],
                    "rho_curve": rho_curve,
                    "extraction_sequence": steps,
                    "final_rho": final_rho,
                    "final_residual_norm2": extraction["final_residual_norm2"],
                    "label": label,
                    "label_rule": {
                        "compressible": "some greedy prefix reaches rho_k < 0.5 and every prefix step exceeds the dof-matched null p95",
                        "persistent": "rho remains high or at least one selected step does not exceed dof-matched null p95",
                        "partially_compressible": "rho drops below the persistent threshold but does not satisfy the strict compressible prefix rule",
                    },
                    "recursive_checks": {"rho_monotone_nonincreasing": monotone, "rho_bounded_unit_interval": bounded, "null_per_step_finite": null_ok},
                }
            )
            per_organism[organism] = organism_result

        labels = {
            organism: result.get("label")
            for organism, result in per_organism.items()
        }
        compressible = sorted(organism for organism, label in labels.items() if label == "compressible")
        persistent = sorted(organism for organism, label in labels.items() if label == "persistent")
        partial = sorted(organism for organism, label in labels.items() if label == "partially_compressible")
        needs_data = sorted(organism for organism, label in labels.items() if label == "needs_data")
        if compressible and not persistent and not partial:
            answer = "computed organisms are compressible by the current readout basis under this greedy descriptive projection"
        elif persistent and not compressible and not partial:
            answer = "computed organisms are persistent: the current readout basis does not compress the non-translation residual beyond null-supported descriptive steps"
        else:
            answer = "compression is organism-dependent; persistent labels are unexplained residuals rather than failures"

        checks_actual = {
            organism: {
                "status": result.get("status"),
                "n_joined_common": result.get("n_joined_common"),
                "candidate_count": result.get("candidate_count"),
                "d_modeled": result.get("d_modeled"),
                "d_difference": result.get("d_modeled_reference_absolute_difference"),
                "rho_curve": result.get("rho_curve"),
                "label": result.get("label"),
            }
            for organism, result in per_organism.items()
        }
        computed_final_rhos = [
            float(result["final_rho"])
            for result in per_organism.values()
            if result.get("status") == "computed" and isinstance(result.get("final_rho"), (int, float))
        ]
        strong_persistent_negative = (
            computed_count >= MIN_COMPUTED_ORGANISMS_FOR_PERSISTENCE
            and len(persistent) == computed_count
            and not compressible
            and not partial
            and bool(computed_final_rhos)
            and min(computed_final_rhos) >= STRONG_PERSISTENT_RHO_FLOOR
        )
        checks = [
            {
                "name": "computed_organism_scope",
                "passed": all_inputs_ok and computed_count > 0,
                "actual": checks_actual,
                "expected": f"each computed organism uses a common readout join n >= {MIN_PROTEINS_PER_ORGANISM}; readouts below threshold are skipped",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": all_complement_ok and computed_count > 0,
                "actual": checks_actual,
                "expected": f"per computed organism d_modeled aligns with full-join complement reference within {MODELED_ALIGNMENT_TOL}",
            },
            {
                "name": "greedy_basis_extraction_computed",
                "passed": all_recursive_ok and computed_count > 0,
                "actual": checks_actual,
                "expected": "rho_k is monotone nonincreasing and all rho values lie in [0,1]",
            },
            {
                "name": "dof_matched_null_computed",
                "passed": all_null_ok and computed_count > 0,
                "actual": {
                    organism: [
                        {
                            "step": step["step"],
                            "selected": step["selected"],
                            "increment": step["incremental_absorbed_fraction_of_R_prev"],
                            "null_p95": step["null_p95"],
                            "exceeds_null": step["exceeds_null"],
                        }
                        for step in result.get("extraction_sequence", [])
                    ]
                    for organism, result in per_organism.items()
                    if isinstance(result.get("extraction_sequence"), list)
                },
                "expected": f"{NULL_TRIALS} deterministic dof-matched Gaussian null projections per selected step",
            },
            {
                "name": "persistent_residual_negative_result",
                "passed": strong_persistent_negative,
                "actual": {
                    "computed_count": computed_count,
                    "persistent": persistent,
                    "compressible": compressible,
                    "partially_compressible": partial,
                    "min_final_rho": min(computed_final_rhos) if computed_final_rhos else None,
                    "rho_floor": STRONG_PERSISTENT_RHO_FLOOR,
                },
                "expected": f"at least {MIN_COMPUTED_ORGANISMS_FOR_PERSISTENCE} computed organisms, all persistent, no compressible or partial labels, and min final rho >= {STRONG_PERSISTENT_RHO_FLOOR}",
            },
            {
                "name": "compressible_vs_persistent_labeled",
                "passed": all_labeled and computed_count > 0,
                "actual": labels,
                "expected": "each computed organism receives compressible, persistent, or partially_compressible; skipped organisms are needs_data",
            },
            {
                "name": "boundary_no_promotion",
                "passed": True,
                "actual": {"cannot_claim": cannot_claim()},
                "expected": "descriptive statistical compression language only",
            },
        ]

        status = "passed" if computed_count > 0 and all_recursive_ok and all_null_ok and all_labeled and strong_persistent_negative else "needs_data"
        if computed_count > 0 and not all_complement_ok:
            status = "failed"
        reason = None
        if status == "needs_data":
            reason = "residual-basis extraction did not satisfy the strong persistent negative-result gate"
        elif status == "failed":
            reason = "one or more computation gates failed"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "For each organism with sufficient local readout data, R_0 = P_{Q perp Tmod}; a lambda-regularized greedy basis selects readout blocks H_k to absorb R_{k-1}, records rho_k decay, and compares each selected step with a dof-matched deterministic Gaussian null.",
                "status_semantics": "passed means the recursive extraction and per-step null were computed for at least one organism; compressible, partially_compressible, persistent, and needs_data are descriptive labels",
                "parameters": {
                    "lambda": LAMBDA,
                    "DL": "log2(1+n_columns(H))",
                    "null_trials_per_step": NULL_TRIALS,
                    "ridge_epsilon": RIDGE_EPS,
                    "min_joined_per_readout_per_organism": MIN_PROTEINS_PER_ORGANISM,
                    "compressible_rho_threshold": COMPRESSIBLE_RHO_THRESHOLD,
                    "persistent_rho_threshold": PERSISTENT_RHO_THRESHOLD,
                    "strong_persistent_rho_floor": STRONG_PERSISTENT_RHO_FLOOR,
                    "min_computed_organisms_for_persistence": MIN_COMPUTED_ORGANISMS_FOR_PERSISTENCE,
                },
                "decomposition": {
                    "Q": q_names,
                    "T": "modeled per-protein tAI",
                    "P": "log10 abundance_ppm",
                    "Z": controls_used(aa_order),
                    "R0": "P_{Q perp Tmod} = (I - Pi_Tmod) Pi_Q P after residualizing Q, T, P, and H by Z",
                    "greedy_score": "||Pi_H R_{k-1}||^2 / ||R_{k-1}||^2 - lambda * log2(1+n_columns(H))",
                },
                "readout_order": READOUT_ORDER,
                "per_organism": per_organism,
                "cross_organism": {
                    "computed_count": computed_count,
                    "compressible": compressible,
                    "partially_compressible": partial,
                    "persistent": persistent,
                    "needs_data": needs_data,
                    "answer_to_core_question": answer,
                },
                "honest": {"cannot_claim": cannot_claim()},
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable local residual-basis extraction input")


if __name__ == "__main__":
    main()

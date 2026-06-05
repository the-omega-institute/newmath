#!/usr/bin/env python3
"""Powered B*_Q6 per-protein survival against measured protein abundance."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_protein_omics_survival_powered"
CLAIM_ID = "h3.cross_layer_relation.direct_protein_omics_survival.b_star_q6_sqp_powered"
CONJECTURE_ID = "q6.direct-protein-omics-survival.with-translation-boundary.cross-layer"

ORGANISMS = [
    "escherichia_coli_k12_mg1655",
    "mycobacterium_smegmatis_str_mc2_155",
    "saccharomyces_cerevisiae",
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


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def vector_norm(vector: list[float]) -> float:
    return math.sqrt(vector_dot(vector, vector))


def orthonormal_basis_from_columns(matrix: list[list[float]], tol: float = RANK_TOL) -> list[list[float]]:
    basis: list[list[float]] = []
    if not matrix:
        return basis
    for column in transpose(matrix):
        residual = list(column)
        for q in basis:
            coeff = vector_dot(residual, q)
            residual = [residual[index] - coeff * q[index] for index in range(len(residual))]
        norm = vector_norm(residual)
        column_norm = vector_norm(column)
        threshold = tol * max(1.0, column_norm)
        if norm > threshold:
            basis.append([value / norm for value in residual])
    return basis


def project_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [[0.0 for _ in matrix[0]] for _ in matrix]
    columns = transpose(matrix)
    for q in basis:
        for col_index, column in enumerate(columns):
            coeff = vector_dot(column, q)
            for row_index in range(len(matrix)):
                out[row_index][col_index] += coeff * q[row_index]
    return out


def subtract(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [
        [left[row][col] - right[row][col] for col in range(len(left[row]))]
        for row in range(len(left))
    ]


def residualize(matrix: list[list[float]], controls: list[list[float]]) -> tuple[list[list[float]], int]:
    basis = orthonormal_basis_from_columns(controls)
    return subtract(matrix, project_with_basis(matrix, basis)), len(basis)


def frobenius2(matrix: list[list[float]]) -> float:
    return sum(value * value for row in matrix for value in row)


def matrix_column(matrix: list[list[float]], index: int) -> list[float]:
    return [row[index] for row in matrix]


def explained_by_design(design: list[list[float]], response: list[list[float]]) -> tuple[float, int]:
    basis = orthonormal_basis_from_columns(design)
    return frobenius2(project_with_basis(response, basis)), len(basis)


def standard_amino_acids(code: dict[str, str], codons: list[str]) -> list[str]:
    aas = sorted({code[codon] for codon in codons if code[codon] != "*"})
    if len(aas) != 20:
        raise ValueError(f"standard genetic code should expose 20 amino acids, got {len(aas)}")
    return aas


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
) -> tuple[list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} payload must contain joined list")

    x_rows: list[list[float]] = []
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
    return x_rows, y_rows, z_rows, summary


def partial_r2_entries(
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], list[dict[str, object]]]:
    y_col = matrix_column(y_tilde, 0)
    y_ss = vector_dot(y_col, y_col)
    matrix: dict[str, dict[str, float]] = {}
    raw_improvement: dict[str, dict[str, float]] = {}
    survivors: list[dict[str, object]] = []
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_ss = vector_dot(x_col, x_col)
        if x_ss <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
            improvement = 0.0
            partial = 0.0
        else:
            xy = vector_dot(x_col, y_col)
            improvement = (xy * xy) / x_ss
            partial = max(0.0, min(1.0, improvement / y_ss))
        matrix[q_name] = {"log10_abundance_ppm": partial}
        raw_improvement[q_name] = {"log10_abundance_ppm": improvement}
        if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
            survivors.append({"q_coordinate": q_name, "readout": "log10_abundance_ppm", "S_QP": partial})
    return matrix, raw_improvement, survivors


def cannot_claim() -> list[str]:
    return [
        "measured PAXdb protein abundance is a cross-sectional protein-omics readout, not a translation-rate measurement",
        "S^{QP} here is a direct codon-usage to protein-abundance association after controls, not a mechanism claim",
        "this experiment is not causal and does not use perturbation, rescue, ribosome profiling, or matched transcript controls",
        "positive entries are not M^{QTP}; mediation needs joint translation and abundance readouts with an explicit mediation fit",
        "this does not claim protein folding, localization, PTM, pathway function, or function_realization",
    ]


def future_required() -> list[str]:
    return [
        "M^{QTP} requires matched translation readouts and matched protein abundance for the same proteins",
        "matched mRNA abundance controls are required before separating abundance from expression-level confounding",
        "perturbation or synonymous-edit assays are required before any causal or mechanism statement",
        "ribosome profiling or calibrated stAI/tAI contacts are required to test translation-mediated paths",
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
    required = [
        f"tools/bio_reality/data/cds_codon_abundance_{organism}.json"
        for organism in ORGANISMS
    ] + ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS codon and PAXdb abundance data not present")

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
        loaded_data_actual: dict[str, object] = {}
        residualized_ok = True
        survival_ok = True
        powered_ok = True

        for organism in ORGANISMS:
            path = repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json"
            payload = load_json(path)
            if not isinstance(payload, dict):
                raise ValueError(f"{organism} payload must be an object")
            x_rows, y_rows, z_rows, data_summary = protein_rows(
                payload=payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            n_proteins = len(x_rows)
            loaded_data_actual[organism] = {
                "n_joined": payload.get("n_joined"),
                "join_hit_rate": payload.get("join_hit_rate"),
                "n_proteins_used": n_proteins,
            }
            if n_proteins >= MIN_PROTEINS_PER_ORGANISM:
                loaded_organisms += 1
            if n_proteins == 0:
                raise ValueError(f"{organism} has no usable joined proteins")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            y_ss = frobenius2(y_tilde)
            explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
            r2_qp = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
            sqp_matrix, raw_improvement, survivors = partial_r2_entries(x_tilde, y_tilde, q_names)
            residual_df = n_proteins - rank_z
            organism_powered = (
                n_proteins >= MIN_PROTEINS_PER_ORGANISM
                and residual_df > 10 * len(q_names)
                and rank_xtilde == len(q_names)
                and y_ss > SURVIVAL_EPS
                and r2_qp < DEGENERATE_R2
            )
            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_proteins and len(y_tilde) == n_proteins
            survival_ok = survival_ok and math.isfinite(r2_qp) and all(
                math.isfinite(value)
                for row in sqp_matrix.values()
                for value in row.values()
            )
            powered_ok = powered_ok and organism_powered

            organism_results[organism] = {
                **data_summary,
                "R2_QP": r2_qp,
                "sqp_matrix": sqp_matrix,
                "raw_sse_improvement": raw_improvement,
                "surviving_coordinates": survivors,
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "q_coordinate_count": len(q_names),
                    "y_residual_energy": y_ss,
                    "explained_energy": explained,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                    "powered_rank_sufficient": organism_powered,
                },
            }

        checks = [
            {
                "name": "cds_abundance_data_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS and all(
                    isinstance(loaded_data_actual[organism]["n_joined"], int)
                    and int(loaded_data_actual[organism]["n_joined"]) >= MIN_PROTEINS_PER_ORGANISM
                    for organism in ORGANISMS
                ),
                "actual": loaded_data_actual,
                "expected": f">= {MIN_ORGANISMS} organisms and every local joined dataset has n_joined >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(len(row["sqp_matrix"]) == 9 for row in organism_results.values() if isinstance(row, dict)),
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
                "expected": "X_Q and log10 abundance residualized within each organism against intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": powered_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism protein n >= 500, full 9-coordinate residual rank, residual df comfortably above coordinate count, and R2_QP not saturated at 1.0",
            },
            {
                "name": "sqp_survival_computed",
                "passed": survival_ok,
                "actual": {
                    organism: {
                        "R2_QP": result["R2_QP"],
                        "surviving_coordinate_count": len(result["surviving_coordinates"]),
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite per-organism R2_QP and finite 9 x 1 S^{QP} partial survival matrix",
            },
            {
                "name": "no_mechanism_or_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "measured abundance is a direct cross-sectional omics correlation, not translation rate, mechanism, causality, function_realization, or M^{QTP}",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; result is not promoted to powered S^{QP}"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Direct per-protein B*_Q6 codon-usage residual survival against measured PAXdb protein abundance after length, amino-acid composition, GC3, and M-density controls; this is a direct omics correlation, NOT a translation-mediated mechanism.",
                "readout": "log10(abundance_ppm) from measured PAXdb protein abundance joined to real CDS codon counts",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "coordinates": q_names,
                "positive_partial_r2_threshold": SURVIVAL_EPS,
                "organisms": organism_results,
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered protein-omics survival input")


if __name__ == "__main__":
    main()

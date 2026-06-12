#!/usr/bin/env python3
"""Powered B*_Q6 per-gene survival against lab knockout essentiality."""

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


EXPERIMENT_ID = "b_star_q6_essentiality_survival_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_mediated_protein_function.b_star_q6_fe_powered"
CONJECTURE_ID = "q6.translation-mediated.protein-function-boundary.cross-layer"

ORGANISMS = [
    "saccharomyces_cerevisiae",
    "escherichia_coli_k12_mg1655",
]
MIN_ORGANISMS = 2
MIN_GENES_PER_ORGANISM = 500
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


def essentiality_by_protein(payload: dict[str, object], organism: str) -> tuple[dict[str, int], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} essentiality payload must contain genes list")

    labels: dict[str, int] = {}
    duplicate_labels = 0
    invalid_records = 0
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            invalid_records += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            invalid_records += 1
            continue
        essential_value = numeric(item.get("essential"), f"{organism}.genes[{row_index}].essential")
        if essential_value not in {0.0, 1.0}:
            raise ValueError(f"{organism}.genes[{row_index}].essential must be 0 or 1")
        if protein_id in labels:
            duplicate_labels += 1
        labels[protein_id] = int(essential_value)

    summary = {
        "n_genes_with_label_reported": payload.get("n_genes_with_label"),
        "n_essential_reported": payload.get("n_essential"),
        "n_nonessential_reported": payload.get("n_nonessential"),
        "essentiality_join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_unique_essentiality_labels": len(labels),
        "duplicate_essentiality_labels": duplicate_labels,
        "invalid_essentiality_records": invalid_records,
    }
    return labels, summary


def gene_rows(
    *,
    abundance_payload: dict[str, object],
    labels: dict[str, int],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = abundance_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} abundance payload must contain joined list")

    x_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "missing_essentiality_label": 0,
        "nonpositive_abundance": 0,
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
        essential = labels.get(protein_id)
        if essential is None:
            skipped["missing_essentiality_label"] += 1
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
        y_rows.append([float(essential)])

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
            + [gc3, m_density, math.log10(abundance)]
        )

    essential_count = int(sum(row[0] for row in y_rows))
    summary = {
        "n_abundance_joined_reported": abundance_payload.get("n_joined"),
        "abundance_join_hit_rate_reported": abundance_payload.get("join_hit_rate"),
        "n_genes": len(x_rows),
        "n_essential": essential_count,
        "n_nonessential": len(x_rows) - essential_count,
        "essential_fraction": (essential_count / len(x_rows)) if x_rows else None,
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
        matrix[q_name] = {"essentiality_linear_probability": partial}
        raw_improvement[q_name] = {"essentiality_linear_probability": improvement}
        if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
            survivors.append(
                {
                    "q_coordinate": q_name,
                    "readout": "essentiality_linear_probability",
                    "S_FE": partial,
                }
            )
    return matrix, raw_improvement, survivors


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt) length control from real CDS records",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
        "log10(abundance_ppm) measured protein-abundance control, required for beyond-expression residualization",
    ]


def cannot_claim() -> list[str]:
    return [
        "essentiality is a lab knockout binary phenotype, not codon causality and not a molecular mechanism",
        "the binary readout is residualized with an ordinary least-squares linear-probability approximation",
        "positive S^{FE} entries are codon residual associations after amino-acid composition and measured protein-abundance controls",
        "this is cross-sectional observational evidence and does not establish synonymous-edit, expression, translation, or pathway causality",
        "protein abundance is a required confounding control here; residual signal is beyond-expression association only",
        "small or null R2_FE is an honest powered outcome and is not promoted into a mechanism claim",
    ]


def future_required() -> list[str]:
    return [
        "synonymous perturbation or rescue assays before any causal statement",
        "matched condition-specific essentiality and abundance readouts to test context dependence",
        "matched transcript abundance and translation readouts to separate expression, translation, and protein-abundance paths",
        "larger phenotype panels before claiming function realization beyond this binary knockout readout",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = (
        [
            f"tools/bio_reality/data/gene_essentiality_{organism}.json"
            for organism in ORGANISMS
        ]
        + [
            f"tools/bio_reality/data/cds_codon_abundance_{organism}.json"
            for organism in ORGANISMS
        ]
        + ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    )
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local essentiality, CDS codon, and abundance data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        organism_results: dict[str, object] = {}
        loaded_data_actual: dict[str, object] = {}
        loaded_organisms = 0
        residualized_ok = True
        survival_ok = True
        powered_ok = True
        controls_include_aa_and_abundance = True

        for organism in ORGANISMS:
            essentiality_payload = load_json(repo / f"tools/bio_reality/data/gene_essentiality_{organism}.json")
            abundance_payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(essentiality_payload, dict):
                raise ValueError(f"{organism} essentiality payload must be an object")
            if not isinstance(abundance_payload, dict):
                raise ValueError(f"{organism} abundance payload must be an object")

            labels, essentiality_summary = essentiality_by_protein(essentiality_payload, organism)
            x_rows, y_rows, z_rows, data_summary = gene_rows(
                abundance_payload=abundance_payload,
                labels=labels,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            n_genes = len(x_rows)
            has_both_classes = data_summary["n_essential"] > 0 and data_summary["n_nonessential"] > 0
            if n_genes >= MIN_GENES_PER_ORGANISM and has_both_classes:
                loaded_organisms += 1
            if n_genes == 0:
                raise ValueError(f"{organism} has no usable essentiality x codon x abundance joined genes")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            y_ss = frobenius2(y_tilde)
            explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
            r2_fe = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
            sfe_matrix, raw_improvement, survivors = partial_r2_entries(x_tilde, y_tilde, q_names)
            residual_df = n_genes - rank_z
            control_column_count = len(z_rows[0]) if z_rows else 0
            organism_powered = (
                n_genes >= MIN_GENES_PER_ORGANISM
                and has_both_classes
                and residual_df > 10 * (control_column_count + len(q_names))
                and rank_xtilde == len(q_names)
                and y_ss > SURVIVAL_EPS
                and r2_fe < DEGENERATE_R2
            )

            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_genes and len(y_tilde) == n_genes
            survival_ok = survival_ok and math.isfinite(r2_fe) and all(
                math.isfinite(value)
                for row in sfe_matrix.values()
                for value in row.values()
            )
            powered_ok = powered_ok and organism_powered
            controls_include_aa_and_abundance = controls_include_aa_and_abundance and control_column_count == 25

            loaded_data_actual[organism] = {
                "n_genes_used": n_genes,
                "n_essential": data_summary["n_essential"],
                "n_nonessential": data_summary["n_nonessential"],
                "essential_fraction": data_summary["essential_fraction"],
                "has_both_classes": has_both_classes,
                "n_unique_essentiality_labels": essentiality_summary["n_unique_essentiality_labels"],
                "n_abundance_joined_reported": data_summary["n_abundance_joined_reported"],
            }
            organism_results[organism] = {
                **essentiality_summary,
                **data_summary,
                "R2_FE": r2_fe,
                "sfe_matrix": sfe_matrix,
                "raw_sse_improvement": raw_improvement,
                "surviving_coordinates": survivors,
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": control_column_count,
                    "q_coordinate_count": len(q_names),
                    "y_residual_energy": y_ss,
                    "explained_energy": explained,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                    "powered_rank_sufficient": organism_powered,
                    "has_both_essentiality_classes": has_both_classes,
                },
            }

        checks = [
            {
                "name": "essentiality_codon_abundance_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS,
                "actual": loaded_data_actual,
                "expected": f">= {MIN_ORGANISMS} organisms with n >= {MIN_GENES_PER_ORGANISM} and both essential/non-essential classes after protein_id join",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(
                    len(row["sfe_matrix"]) == 9
                    for row in organism_results.values()
                    if isinstance(row, dict)
                ),
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "exactly the 9 B*_Q6 synonymous-residual coordinates reused from run_b_star_q6_translation_survival_powered.py",
            },
            {
                "name": "controls_Z_with_aa_and_abundance_residualized",
                "passed": residualized_ok and controls_include_aa_and_abundance,
                "actual": {
                    "controls_used": controls_used(aa_order),
                    "organisms": {
                        organism: result["rank_diagnostics"]
                        for organism, result in organism_results.items()
                        if isinstance(result, dict)
                    },
                },
                "expected": "X_Q and binary essentiality residualized within each organism against intercept, log length, 20 amino-acid composition controls, GC3, M-density, and log10 protein abundance",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": powered_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism n >= 500, both binary classes, full 9-coordinate residual rank, residual df far above controls plus coordinates, and R2_FE not saturated at 1.0",
            },
            {
                "name": "essentiality_survival_computed",
                "passed": survival_ok,
                "actual": {
                    organism: {
                        "R2_FE": result["R2_FE"],
                        "surviving_coordinate_count": len(result["surviving_coordinates"]),
                        "essential_fraction": result["essential_fraction"],
                        "n_genes": result["n_genes"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite per-organism R2_FE and finite 9 x 1 S^{FE} partial survival matrix; small or null values still pass if powered",
            },
            {
                "name": "no_causal_or_mechanism_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "binary lab phenotype, linear-probability approximation, abundance-controlled association only, non-causal, non-mechanistic, and cross-sectional",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest powered gates failed; result is not promoted to B*_Q6 essentiality survival"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Per-gene B*_Q6 codon residual association with lab knockout essentiality after amino-acid composition and measured protein-abundance control, using a binary linear-probability residualization; this is NOT causal and NOT a mechanism claim.",
                "readout": "essentiality binary lab knockout phenotype joined by protein_id to real CDS codon counts and measured protein abundance",
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
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered essentiality survival input")


if __name__ == "__main__":
    main()

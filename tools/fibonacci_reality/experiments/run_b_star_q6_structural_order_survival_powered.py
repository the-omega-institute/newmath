#!/usr/bin/env python3
"""Powered B*_Q6 per-protein survival against AlphaFold mean pLDDT."""

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


EXPERIMENT_ID = "b_star_q6_structural_order_survival_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_gated_structural_order.b_star_q6_sso_powered"
CONJECTURE_ID = "q6.translation-gated.structural-order.cross-layer"

ORGANISMS = [
    "escherichia_coli_k12_mg1655",
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


def structural_order_index(payload: dict[str, object], organism: str) -> dict[str, float]:
    proteins = payload.get("proteins")
    if not isinstance(proteins, list):
        raise ValueError(f"{organism} structural-order payload must contain proteins list")
    out: dict[str, float] = {}
    for row_index, item in enumerate(proteins):
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            continue
        order = numeric(item.get("structural_order"), f"{organism}.proteins[{row_index}].structural_order")
        if not math.isfinite(order):
            raise ValueError(f"{organism}.proteins[{row_index}].structural_order must be finite")
        if order < 0.0 or order > 100.0:
            raise ValueError(f"{organism}.proteins[{row_index}].structural_order must be mean pLDDT on 0..100")
        out[protein_id] = order
    return out


def protein_rows(
    *,
    codon_payload: dict[str, object],
    structural_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = codon_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS-codon payload must contain joined list")
    order_by_protein = structural_order_index(structural_payload, organism)

    x_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    used_protein_ids: list[str] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_structural_order_match": 0,
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
        structural_order = order_by_protein.get(protein_id)
        if structural_order is None:
            skipped["no_structural_order_match"] += 1
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
        y_rows.append([structural_order])
        used_protein_ids.append(protein_id)

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
        "n_codon_joined_reported": codon_payload.get("n_joined"),
        "n_structural_order_proteins_reported": structural_payload.get("n_proteins_with_order"),
        "structural_order_join_hit_rate": structural_payload.get("join_hit_rate"),
        "n_matched_proteins": len(used_protein_ids),
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
    readout_name = "mean_plddt_predicted_structure_confidence"
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
        matrix[q_name] = {readout_name: partial}
        raw_improvement[q_name] = {readout_name: improvement}
        if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
            survivors.append({"q_coordinate": q_name, "readout": readout_name, "S_SO": partial})
    return matrix, raw_improvement, survivors


def cannot_claim() -> list[str]:
    return [
        "AlphaFold mean pLDDT is predicted structure confidence, not experimental structural order",
        "mean pLDDT is not protein function, phenotype, abundance, localization, folding kinetics, or pathway activity",
        "S^{SO} here is a cross-sectional codon-usage to predicted-structure-confidence association after controls, not causality",
        "positive entries do not establish a translation-mediated mechanism or any function_realization claim",
        "the amino-acid composition controls are included so this is not promoted from amino-acid composition alone",
    ]


def future_required() -> list[str]:
    return [
        "matched experimental structural measurements are required before claiming experimental structural order",
        "matched functional or phenotype assays are required before any function or phenotype statement",
        "synonymous-edit perturbation or matched translation data are required before causal or translation-mediated mechanism claims",
        "additional organisms with matched CDS and AlphaFold-style readouts are required before cross-organism generalization",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def material_signal_label(r2: float, survivors: list[dict[str, object]]) -> str:
    if not survivors or r2 <= SURVIVAL_EPS:
        return "null: no positive partial survival above numerical epsilon"
    if r2 < 0.01:
        return "weak: finite positive partial survival but total R2_SO below 0.01"
    if r2 < 0.05:
        return "modest: finite association, still cross-sectional and non-causal"
    return "finite association: cross-sectional predicted-confidence readout only"


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = [
        f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json"
        for organism in ORGANISMS
    ] + [
        f"tools/fibonacci_reality/data/structural_order_{organism}.json"
        for organism in ORGANISMS
    ] + ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit(
            "needs_data",
            missing_required_data=missing,
            reason="required local CDS codon and AlphaFold structural-order data not present",
        )

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
            codon_path = repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json"
            structural_path = repo / f"tools/fibonacci_reality/data/structural_order_{organism}.json"
            codon_payload = load_json(codon_path)
            structural_payload = load_json(structural_path)
            if not isinstance(codon_payload, dict) or not isinstance(structural_payload, dict):
                raise ValueError(f"{organism} payloads must be objects")

            x_rows, y_rows, z_rows, data_summary = protein_rows(
                codon_payload=codon_payload,
                structural_payload=structural_payload,
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
                "n_codon_joined": codon_payload.get("n_joined"),
                "n_structural_order_proteins": structural_payload.get("n_proteins_with_order"),
                "n_matched_proteins_used": n_proteins,
                "structural_order_join_hit_rate": structural_payload.get("join_hit_rate"),
            }
            if n_proteins >= MIN_PROTEINS_PER_ORGANISM:
                loaded_organisms += 1
            if n_proteins == 0:
                raise ValueError(f"{organism} has no matched structural-order and CDS-codon proteins")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            y_ss = frobenius2(y_tilde)
            explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
            r2_so = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
            sso_matrix, raw_improvement, survivors = partial_r2_entries(x_tilde, y_tilde, q_names)
            residual_df = n_proteins - rank_z
            organism_powered = (
                n_proteins >= MIN_PROTEINS_PER_ORGANISM
                and residual_df > 10 * len(q_names)
                and rank_xtilde == len(q_names)
                and y_ss > SURVIVAL_EPS
                and r2_so < DEGENERATE_R2
            )
            residualized_ok = (
                residualized_ok
                and rank_z > 0
                and len(z_rows[0]) == 24
                and len(x_tilde) == n_proteins
                and len(y_tilde) == n_proteins
            )
            survival_ok = survival_ok and math.isfinite(r2_so) and all(
                math.isfinite(value)
                for row in sso_matrix.values()
                for value in row.values()
            )
            powered_ok = powered_ok and organism_powered

            organism_results[organism] = {
                **data_summary,
                "R2_SO": r2_so,
                "sso_matrix": sso_matrix,
                "raw_sse_improvement": raw_improvement,
                "surviving_coordinates": survivors,
                "signal_interpretation": material_signal_label(r2_so, survivors),
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "aa_composition_control_count": len(aa_order),
                    "q_coordinate_count": len(q_names),
                    "y_residual_energy": y_ss,
                    "explained_energy": explained,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                    "powered_rank_sufficient": organism_powered,
                },
            }

        checks = [
            {
                "name": "structural_order_and_codon_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS,
                "actual": loaded_data_actual,
                "expected": f">= {MIN_ORGANISMS} organisms with matched structural-order and CDS-codon data, each n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(
                    isinstance(row, dict) and len(row["sso_matrix"]) == 9
                    for row in organism_results.values()
                ),
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "exactly the 9 B*_Q6 synonymous-residual coordinates reused from run_b_star_q6_translation_survival_powered.py",
            },
            {
                "name": "controls_Z_with_aa_residualized",
                "passed": residualized_ok and len(aa_order) == 20,
                "actual": {
                    "controls_used": controls_used(aa_order),
                    "organism_rank_diagnostics": {
                        organism: result["rank_diagnostics"]
                        for organism, result in organism_results.items()
                        if isinstance(result, dict)
                    },
                },
                "expected": "X_Q and mean pLDDT residualized within each organism against intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": powered_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism protein n >= 500, full 9-coordinate residual rank, residual df comfortably above coordinate count, and R2_SO not saturated at 1.0",
            },
            {
                "name": "structural_order_survival_computed",
                "passed": survival_ok,
                "actual": {
                    organism: {
                        "R2_SO": result["R2_SO"],
                        "surviving_coordinate_count": len(result["surviving_coordinates"]),
                        "signal_interpretation": result["signal_interpretation"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite per-organism R2_SO and finite 9 x 1 S^{SO} partial survival matrix",
            },
            {
                "name": "no_function_or_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "mean pLDDT is predicted structure confidence, not experimental structural order, function, phenotype, or causality",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; result is not promoted to powered S^{SO}"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Per-protein B*_Q6 codon-usage residual association with AlphaFold mean pLDDT predicted structural-order confidence after length, 20 amino-acid composition, GC3, and M-density controls; this is NOT function, phenotype, causality, or experimental structural order.",
                "readout": "AlphaFold mean pLDDT on 0..100, interpreted only as predicted structure confidence",
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
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered structural-order survival input")


if __name__ == "__main__":
    main()

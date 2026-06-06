#!/usr/bin/env python3
"""Powered B*_Q6 modeled-tAI translation-survival matrix over matched organisms."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from _tai import (
    AA_ONE_TO_THREE,
    RNA_COMPLEMENT,
    codon_w_values,
    effective_wobble_base,
    first_two_positions_match,
    wobble_penalty,
)


EXPERIMENT_ID = "b_star_q6_translation_survival_powered"
CLAIM_ID = "h3.translation_realization.b_star_q6_sqt_powered"
POWERED_SURVIVAL_MIN_ORGANISMS = 40
SURVIVAL_EPS = 1e-12
RANK_TOL = 1e-10
DEGENERATE_R2 = 0.999999

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]


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


def standard_code(repo: pathlib.Path) -> dict[str, str]:
    raw = load_json(repo / "tools/bio_reality/data/ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("NCBI genetic-code payload must be an object")
    table = next((item for item in raw.get("tables", []) if item.get("table_id") == 1), None)
    codons = raw.get("codon_order", [])
    if not isinstance(codons, list) or not isinstance(table, dict) or len(codons) != len(table.get("aa", "")):
        raise ValueError("NCBI standard genetic code table is missing or malformed")
    return {str(codon): aa for codon, aa in zip(codons, table["aa"])}


def manifest_organisms(repo: pathlib.Path) -> list[str]:
    path = repo / "tools/bio_reality/data/multi_organism_campaign_manifest.json"
    raw = load_json(path)
    if not isinstance(raw, dict) or not isinstance(raw.get("successes"), list):
        raise ValueError("multi-organism manifest must contain a successes list")
    organisms = []
    for item in raw["successes"]:
        if not isinstance(item, dict) or not isinstance(item.get("organism"), str):
            raise ValueError("manifest success entry is missing organism")
        organisms.append(item["organism"])
    if len(set(organisms)) != len(organisms):
        raise ValueError("manifest contains duplicate organism slugs")
    return organisms


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        mean = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - mean
    return out


def dot(left: dict[str, float], right: dict[str, float], codons: list[str]) -> float:
    return sum(left[codon] * right[codon] for codon in codons)


def q_vectors(codons: list[str]) -> dict[str, dict[str, float]]:
    raw: dict[str, dict[str, float]] = {}
    q = zero(codons); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero(codons)
    for c in ["AGA", "AGG"]: q[c] = 1.0
    for c in ["CGU", "CGC", "CGA", "CGG"]: q[c] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for c in CUN_CODONS: q[c] = 0.25
    for c in UUR_CODONS: q[c] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for c in ["UCA", "UCG"]: q[c] = 0.5
    for c in ["AGU", "AGC"]: q[c] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for c in ["ACA", "ACG"]: q[c] = 0.5
    for c in ["ACU", "ACC"]: q[c] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(dot(q, q, codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return dot(vector, q, codons) / denom


def codon_frequency_residual(
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    fibers: dict[str, list[str]],
) -> tuple[dict[str, float], dict[str, int], dict[str, int], int]:
    raw = load_json(repo / f"tools/bio_reality/data/codon_usage_{organism}.json")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism} codon-usage payload must be an object")
    counts_raw = raw.get("codon_counts")
    aa_counts_raw = raw.get("amino_acid_counts")
    if not isinstance(counts_raw, dict):
        raise ValueError(f"{organism} codon_counts object is missing")
    if not isinstance(aa_counts_raw, dict):
        raise ValueError(f"{organism} amino_acid_counts object is missing")
    counts = {codon: int(numeric(counts_raw.get(codon, 0), f"{organism}.codon_counts.{codon}")) for codon in codons}
    aa_counts = {str(aa): int(numeric(value, f"{organism}.amino_acid_counts.{aa}")) for aa, value in aa_counts_raw.items()}
    total = sum(counts.values())
    if total <= 0:
        raise ValueError(f"{organism} has no positive sense-codon total")
    frequencies = {codon: counts[codon] / total for codon in codons}
    return project_syn(frequencies, fibers), counts, aa_counts, total


def complement_codon_for_anticodon(anticodon: str) -> str | None:
    bases = [RNA_COMPLEMENT.get(anticodon[index]) for index in [2, 1, 0]]
    if any(base is None for base in bases):
        return None
    return "".join(str(base) for base in bases)


def synthesize_tai_records(
    *,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    trna_all_copies: dict[str, int],
) -> tuple[list[dict[str, str]], list[dict[str, object]]]:
    records: list[dict[str, str]] = []
    ambiguous: list[dict[str, object]] = []
    for anticodon, copy_count in sorted(trna_all_copies.items()):
        if copy_count <= 0 or len(anticodon) != 3:
            continue
        exact_codon = complement_codon_for_anticodon(anticodon)
        candidate_aas = sorted({
            AA_ONE_TO_THREE[code[codon]]
            for codon in codons
            if first_two_positions_match(codon, anticodon)
            and wobble_penalty(effective_wobble_base(AA_ONE_TO_THREE[code[codon]], anticodon, organism), codon[2]) is not None
        })
        if exact_codon in code and code[exact_codon] != "*":
            aa = AA_ONE_TO_THREE[code[exact_codon]]
        elif len(candidate_aas) == 1:
            aa = candidate_aas[0]
        else:
            ambiguous.append({"anticodon": anticodon, "copy_count": copy_count, "candidate_aa": candidate_aas})
            continue
        if len(candidate_aas) > 1:
            ambiguous.append({"anticodon": anticodon, "copy_count": copy_count, "chosen_aa": aa, "candidate_aa": candidate_aas})
        for _ in range(copy_count):
            records.append({"aa": aa, "aa_label": aa, "anticodon": anticodon, "matched": True})
    return records, ambiguous


def modeled_tai_residual(
    repo: pathlib.Path,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    fibers: dict[str, list[str]],
) -> tuple[dict[str, float], dict[str, object]]:
    raw = load_json(repo / f"tools/bio_reality/data/gtrnadb_trna_all_copy_{organism}.json")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism} GtRNAdb payload must be an object")
    copies_raw = raw.get("trna_all_copies")
    if not isinstance(copies_raw, dict):
        raise ValueError(f"{organism} trna_all_copies object is missing")
    copies = {str(anticodon).replace("T", "U"): int(numeric(value, f"{organism}.trna_all_copies.{anticodon}")) for anticodon, value in copies_raw.items()}
    records, ambiguous = synthesize_tai_records(organism=organism, code=code, codons=codons, trna_all_copies=copies)
    if not records:
        raise ValueError(f"{organism} has no usable anticodon copy records for modeled tAI")
    tai, raw_w, contributors = codon_w_values(organism=organism, code=code, records=records, codons=codons)
    zero_raw_w = sorted(codon for codon, value in raw_w.items() if value == 0.0)
    return project_syn(tai, fibers), {
        "trna_all_copy_total": sum(copies.values()),
        "usable_synthetic_tai_record_count": len(records),
        "anticodon_count": len(copies),
        "ambiguous_anticodon_assignments": ambiguous,
        "zero_raw_W_filled_by_geometric_mean_count": len(zero_raw_w),
        "tai_contributor_contact_count": len(contributors),
    }


def controls_row(
    *,
    counts: dict[str, int],
    aa_counts: dict[str, int],
    codons: list[str],
    q_support: set[str],
    total: int,
) -> list[float]:
    row = [1.0]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("amino-acid count total must be positive")
    for aa in sorted(AA_ONE_TO_THREE):
        row.append(aa_counts.get(aa, 0) / aa_total)
    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    row.extend([gc3, math.log(total), m_density])
    return row


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
    for q in basis:
        for col_index, column in enumerate(transpose(matrix)):
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


def single_column_matrix(column: list[float]) -> list[list[float]]:
    return [[value] for value in column]


def explained_by_design(design: list[list[float]], response: list[list[float]]) -> tuple[float, int]:
    basis = orthonormal_basis_from_columns(design)
    return frobenius2(project_with_basis(response, basis)), len(basis)


def partial_r2_matrix(
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], list[dict[str, object]]]:
    sqt: dict[str, dict[str, float]] = {}
    raw_improvement: dict[str, dict[str, float]] = {}
    survivors: list[dict[str, object]] = []
    for i, left_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, i)
        x_ss = vector_dot(x_col, x_col)
        sqt[left_name] = {}
        raw_improvement[left_name] = {}
        for j, right_name in enumerate(q_names):
            y_col = matrix_column(y_tilde, j)
            y_ss = vector_dot(y_col, y_col)
            if x_ss <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
                improvement = 0.0
                partial = 0.0
            else:
                xy = vector_dot(x_col, y_col)
                improvement = (xy * xy) / x_ss
                partial = max(0.0, min(1.0, improvement / y_ss))
            sqt[left_name][right_name] = partial
            raw_improvement[left_name][right_name] = improvement
            if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
                survivors.append({"q_coordinate": left_name, "readout_coordinate": right_name, "S_ij": partial})
    return sqt, raw_improvement, survivors


def cannot_claim() -> list[str]:
    return [
        "modeled tAI from GtRNAdb tRNA gene-copy counts and dos Reis wobble weights is not ribo-seq",
        "modeled tAI is not measured elongation speed, ribosome occupancy, proteomics, protein folding, or protein realization",
        "cross-organism codon-usage/tRNA-copy survival is not a gene-level mechanism or pathway-level claim",
        "positive S^{QT} entries are modeled translation-readout survival under controls, not evidence for S^{QP} or M^{QTP}",
    ]


def future_required() -> list[str]:
    return [
        "matched ribo-seq or other measured translation-efficiency readouts to upgrade beyond modeled tAI",
        "matched proteomics/protein-abundance data for S^{QP}",
        "matched translation and proteomics data with transcript controls for M^{QTP} mediation",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
        organisms = manifest_organisms(repo)
        missing = []
        for organism in organisms:
            for prefix in ["codon_usage_", "gtrnadb_trna_all_copy_"]:
                path = repo / f"tools/bio_reality/data/{prefix}{organism}.json"
                if not path.exists():
                    missing.append(str(path.relative_to(repo)))
        if missing:
            emit("needs_data", missing_required_data=missing, reason="manifest organism is missing matched local data")

        x_rows: list[list[float]] = []
        y_rows: list[list[float]] = []
        z_rows: list[list[float]] = []
        organism_summaries: dict[str, object] = {}
        for organism in organisms:
            usage_residual, counts, aa_counts, total = codon_frequency_residual(repo, organism, codons, fibers)
            tai_residual, tai_summary = modeled_tai_residual(repo, organism, code, codons, fibers)
            x_rows.append([normed_coordinate(usage_residual, q_projected[name], codons) for name in q_names])
            y_rows.append([normed_coordinate(tai_residual, q_projected[name], codons) for name in q_names])
            z_rows.append(controls_row(counts=counts, aa_counts=aa_counts, codons=codons, q_support=q_support, total=total))
            organism_summaries[organism] = {
                "sense_codon_total": total,
                "gc3": z_rows[-1][-3],
                "log_sense_codon_total": z_rows[-1][-2],
                "M_density_baseline": z_rows[-1][-1],
                **tai_summary,
            }

        x_tilde, rank_z = residualize(x_rows, z_rows)
        y_tilde, _ = residualize(y_rows, z_rows)
        y_ss = frobenius2(y_tilde)
        if y_ss <= SURVIVAL_EPS:
            raise ValueError("modeled-tAI readout has no residual energy after controls")
        explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
        r2_qt = max(0.0, min(1.0, explained / y_ss))
        sqt_matrix, raw_improvement, survivor_entries = partial_r2_matrix(x_tilde, y_tilde, q_names)
        survivor_by_coordinate: dict[str, dict[str, object]] = {}
        for entry in survivor_entries:
            q = str(entry["q_coordinate"])
            current = survivor_by_coordinate.setdefault(q, {"max_S_ij": 0.0, "readout_coordinates": []})
            current["max_S_ij"] = max(float(current["max_S_ij"]), float(entry["S_ij"]))
            current["readout_coordinates"].append(entry["readout_coordinate"])

        residual_df = len(organisms) - rank_z
        rank_sufficient = (
            len(organisms) >= POWERED_SURVIVAL_MIN_ORGANISMS
            and rank_xtilde == len(q_names)
            and residual_df > rank_xtilde + 5
            and r2_qt < DEGENERATE_R2
            and any(value < DEGENERATE_R2 for row in sqt_matrix.values() for value in row.values())
        )
        checks = [
            {
                "name": "cross_organism_data_loaded",
                "passed": len(organisms) >= POWERED_SURVIVAL_MIN_ORGANISMS,
                "actual": {"organism_n": len(organisms), "organisms": organisms},
                "expected": f">= {POWERED_SURVIVAL_MIN_ORGANISMS} manifest-success organisms with matched local codon usage and all-tRNA copy files",
            },
            {
                "name": "modeled_tai_readout_computed",
                "passed": all(len(row) == len(q_names) and all(math.isfinite(value) for value in row) for row in y_rows),
                "actual": {"readout_columns": q_names, "readout_column_count": len(q_names)},
                "expected": "finite modeled-tAI projection readout for every B*_Q6 coordinate",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(len(row) == 9 and all(math.isfinite(value) for value in row) for row in x_rows),
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "9 finite B*_Q6 synonymous-residual coordinates",
            },
            {
                "name": "controls_Z_residualized",
                "passed": rank_z > 0 and len(z_rows) == len(organisms) and len(x_tilde) == len(organisms) and len(y_tilde) == len(organisms),
                "actual": {"rank_Z": rank_z, "control_column_count": len(z_rows[0]), "residual_df_after_Z": residual_df},
                "expected": "X_Q and Y_T residualized against amino-acid composition, GC3, log codon total, and M-density baseline",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": rank_sufficient,
                "actual": {
                    "organism_n": len(organisms),
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "R2_QT": r2_qt,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                },
                "expected": "n >= 40, full 9-coordinate X rank after controls, residual df comfortably above coordinate rank, and R2_QT not rank-saturated at 1.0",
            },
            {
                "name": "sqt_survival_computed",
                "passed": math.isfinite(r2_qt) and all(math.isfinite(value) for row in sqt_matrix.values() for value in row.values()),
                "actual": {"R2_QT": r2_qt, "matrix_shape": [len(sqt_matrix), len(next(iter(sqt_matrix.values())))]},
                "expected": "finite global R2_QT and finite 9 x 9 S^{QT} partial survival matrix",
            },
            {
                "name": "no_ribo_seq_or_protein_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "modeled-tAI cross-organism survival is not ribo-seq, measured elongation, proteomics, or protein realization",
            },
        ]
        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if not rank_sufficient:
            reason = "powered rank gate failed or R2_QT remains rank-degenerate; result is not promoted to powered modeled-tAI survival"
        emit(
            status,
            checks=checks,
            reason=reason,
            result={
                "claimed_layer": "translation_realization_modeled",
                "readout": "modeled per-codon tAI from GtRNAdb anticodon copy counts and dos Reis wobble weights, projected onto B*_Q6 synonymous-residual coordinates",
                "organism_n": len(organisms),
                "R2_QT": r2_qt,
                "sqt_matrix": sqt_matrix,
                "raw_sse_improvement_matrix": raw_improvement,
                "surviving_coordinates": [
                    {"q_coordinate": q, **summary}
                    for q, summary in sorted(survivor_by_coordinate.items())
                ],
                "surviving_entries": sorted(survivor_entries, key=lambda item: (str(item["q_coordinate"]), str(item["readout_coordinate"]))),
                "positive_partial_r2_threshold": SURVIVAL_EPS,
                "controls_used": [
                    "intercept",
                    "20 amino-acid composition proportions from codon_usage amino_acid_counts",
                    "GC3 from codon_usage codon_counts",
                    "log sense-codon total as length proxy",
                    "M_density_baseline = fraction of codon usage on the union support of the 9 projected B*_Q6 q vectors",
                ],
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "global_y_residual_energy": y_ss,
                    "global_explained_energy": explained,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                },
                "coordinates": q_names,
                "organisms": organism_summaries,
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered modeled-tAI survival input")


if __name__ == "__main__":
    main()

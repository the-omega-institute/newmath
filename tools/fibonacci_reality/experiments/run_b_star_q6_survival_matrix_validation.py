#!/usr/bin/env python3
"""B*_Q6 modeled-tAI translation-survival boundary experiment."""

from __future__ import annotations

import json
import math
import pathlib
import sys

from _tai import (
    aa_coverage,
    anticodon_copy_counts,
    codon_w_values,
    has_full_standard_aa_coverage,
    parse_gtrnadb_fasta,
)


EXPERIMENT_ID = "b_star_q6_survival_matrix_validation"
CLAIM_ID = "h3.codon_usage_topology.translation_survival.b_star_q6_modeled_tai"
ORGANISMS = ["homo_sapiens", "saccharomyces_cerevisiae", "escherichia_coli_k12"]
COUPLING_THRESHOLD = 0.01
POWERED_SURVIVAL_MIN_SPECIES = 40

REQUIRED_DATA = [
    "tools/fibonacci_reality/data/kazusa_codon_usage_homo_sapiens.json",
    "tools/fibonacci_reality/data/kazusa_codon_usage_saccharomyces_cerevisiae.json",
    "tools/fibonacci_reality/data/kazusa_codon_usage_escherichia_coli_k12.json",
    "tools/fibonacci_reality/data/gtrnadb_trna_leu_copy_homo_sapiens.json",
    "tools/fibonacci_reality/data/gtrnadb_trna_leu_copy_saccharomyces_cerevisiae.json",
    "tools/fibonacci_reality/data/gtrnadb_trna_leu_copy_escherichia_coli_k12.json",
    "tools/fibonacci_reality/data/ncbi_genetic_codes.json",
]

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


def load_json(path: pathlib.Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def standard_code(repo: pathlib.Path) -> dict[str, str]:
    raw = load_json(repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("NCBI genetic-code payload must be an object")
    table = next((item for item in raw.get("tables", []) if item.get("table_id") == 1), None)
    codons = raw.get("codon_order", [])
    if not isinstance(codons, list) or not isinstance(table, dict) or len(codons) != len(table.get("aa", "")):
        raise ValueError("NCBI standard genetic code table is missing or malformed")
    return {str(codon): aa for codon, aa in zip(codons, table["aa"])}


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


def codon_residual(repo: pathlib.Path, organism: str, codons: list[str], fibers: dict[str, list[str]]) -> dict[str, float]:
    raw = load_json(repo / f"tools/fibonacci_reality/data/kazusa_codon_usage_{organism}.json")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism} Kazusa payload must be an object")
    counts = raw.get("codon_counts")
    if not isinstance(counts, dict):
        raise ValueError(f"{organism} codon_counts object is missing")
    return project_syn({c: numeric(counts.get(c, 0), f"{organism}.{c}") for c in codons}, fibers)


def centered_vectors(rows: list[dict[str, float]], codons: list[str]) -> list[dict[str, float]]:
    means = {codon: sum(row[codon] for row in rows) / len(rows) for codon in codons}
    return [{codon: row[codon] - means[codon] for codon in codons} for row in rows]


def covariance_apply(
    usage_rows: list[dict[str, float]],
    tai_rows: list[dict[str, float]],
    vector: dict[str, float],
    codons: list[str],
) -> dict[str, float]:
    scale = 1.0 / (len(usage_rows) - 1)
    return {
        left_codon: scale * sum(
            usage_rows[index][left_codon] * dot(tai_rows[index], vector, codons)
            for index in range(len(usage_rows))
        )
        for left_codon in codons
    }


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


def cannot_claim() -> list[str]:
    return [
        "This is a modeled-tAI contact from tRNA gene copy and dos Reis wobble weights, not ribo-seq, proteomics, or measured elongation speed.",
        "With exactly 3 organisms this experiment has no powered survival fit; it reports bounded cross-layer coupling only.",
        "This result does not verify translation_realization, protein abundance, protein folding, biological function, or pathway-level mechanism.",
        "This result does not assert universal sign direction or population-level effect size.",
        "The amino-acid composition quotient is kept explicit through synonymous projection of codon usage, tAI readout, and B*_Q6 q vectors.",
    ]


def missing_powered_survival_data() -> list[str]:
    return [
        f">={POWERED_SURVIVAL_MIN_SPECIES} organisms with full tRNA gene copy tables and matched codon-usage tables",
        "powered tAI survival also needs matched measured translation-efficiency readouts such as ribo-seq, stAI calibration, or proteomics",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    missing = [path for path in REQUIRED_DATA if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required modeled-tAI input data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        usage_rows = []
        tai_rows = []
        organisms: dict[str, object] = {}
        local_payload_checks: dict[str, object] = {}

        for organism in ORGANISMS:
            usage_rows.append(codon_residual(repo, organism, codons, fibers))
            trna_path = repo / f"tools/fibonacci_reality/data/gtrnadb_trna_leu_copy_{organism}.json"
            trna_raw = load_json(trna_path)
            if not isinstance(trna_raw, dict):
                raise ValueError(f"{organism} GtRNAdb payload must be an object")
            raw_payload_text = trna_raw.get("raw_payload_text")
            if not isinstance(raw_payload_text, str) or not raw_payload_text.startswith(">"):
                raise ValueError(f"{organism} raw_payload_text FASTA is missing")
            records = parse_gtrnadb_fasta(raw_payload_text)
            matched_records = [record for record in records if record.get("matched")]
            coverage = aa_coverage(records)
            standard_family_count = len([
                aa for aa in coverage
                if aa in {
                    "Ala", "Arg", "Asn", "Asp", "Cys", "Gln", "Glu", "Gly", "His", "Ile",
                    "Leu", "Lys", "Met", "Phe", "Pro", "Ser", "Thr", "Trp", "Tyr", "Val",
                }
            ])
            if not has_full_standard_aa_coverage(records):
                emit(
                    "needs_data",
                    checks=[
                        {
                            "name": "local_gtrnadb_payload_contains_all_standard_tRNA_families",
                            "passed": False,
                            "actual": {"organism": organism, "aa_coverage": aa_coverage(records)},
                            "expected": "all 20 standard amino-acid tRNA families in local raw_payload_text or fetched all-tRNA FASTA",
                        }
                    ],
                    missing_data=[
                        f"full GtRNAdb tRNA FASTA for {organism} with all standard amino-acid tRNA families"
                    ],
                    reason="local GtRNAdb raw payload is not a full tRNA FASTA",
                )

            tai, raw_w, contributors = codon_w_values(
                organism=organism,
                code=code,
                records=records,
                codons=codons,
            )
            tai_projected = project_syn(tai, fibers)
            tai_rows.append(tai_projected)
            zero_raw_w = sorted(codon for codon, value in raw_w.items() if value == 0.0)
            organisms[organism] = {
                "local_raw_payload_used_without_fetch": True,
                "fasta_header_count": len(records),
                "matched_fasta_header_count": len(matched_records),
                "unmatched_fasta_header_count": len(records) - len(matched_records),
                "aa_coverage": coverage,
                "anticodon_copy_count": anticodon_copy_counts(records),
                "raw_W_zero_codons_filled_by_geometric_mean": zero_raw_w,
                "modeled_tAI_w": tai,
                "tAI_contributor_contact_count": len(contributors),
            }
            local_payload_checks[organism] = {
                "standard_aa_family_count": standard_family_count,
                "fasta_header_count": len(records),
                "matched_fasta_header_count": len(matched_records),
                "unmatched_fasta_header_count": len(records) - len(matched_records),
            }

        centered_usage = centered_vectors(usage_rows, codons)
        centered_tai = centered_vectors(tai_rows, codons)
        projected_q = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        syn_ok = all(
            abs(sum(vector[codon] for codon in fiber)) < 1e-8
            for vector in projected_q.values()
            for fiber in fibers.values()
        )

        survival_scores = {}
        survival_matrix = {}
        for left_name, left_q in projected_q.items():
            row = {}
            for right_name, right_q in projected_q.items():
                sigma_right = covariance_apply(centered_usage, centered_tai, right_q, codons)
                row[right_name] = dot(left_q, sigma_right, codons)
            survival_matrix[left_name] = row
            survival_scores[left_name] = row[left_name]

        max_abs = max(abs(value) for row in survival_matrix.values() for value in row.values())
        diagonal_max_abs = max(abs(value) for value in survival_scores.values())
        entries = [
            {"q_usage": left, "q_tAI": right, "S_ij": value}
            for left, row in survival_matrix.items()
            for right, value in row.items()
            if abs(value) > COUPLING_THRESHOLD
        ]
        bounded_coupling = math.isfinite(max_abs) and len(entries) >= 1

        checks = [
            {
                "name": "local_gtrnadb_payload_contains_all_standard_tRNA_families",
                "passed": True,
                "actual": local_payload_checks,
                "expected": "all 20 standard amino-acid tRNA families are present in each local raw_payload_text; no fetch required",
            },
            {
                "name": "modeled_tAI_readout_computed_from_dos_reis_wobble_weights",
                "passed": all(
                    all(math.isfinite(value) and value > 0.0 for value in organisms[organism]["modeled_tAI_w"].values())
                    for organism in ORGANISMS
                ),
                "actual": {
                    organism: {
                        "sense_codon_count": len(organisms[organism]["modeled_tAI_w"]),
                        "zero_raw_W_fallback_count": len(organisms[organism]["raw_W_zero_codons_filled_by_geometric_mean"]),
                    }
                    for organism in ORGANISMS
                },
                "expected": "finite positive w_codon for all 61 sense codons after documented W=0 geometric-mean fallback",
            },
            {
                "name": "b_star_q6_synonymous_residuals_computed",
                "passed": len(projected_q) == 9 and syn_ok,
                "actual": sorted(projected_q),
                "expected": "9 q_i projected to the synonymous residual subspace",
            },
            {
                "name": "modeled_tAI_bounded_coupling_nonzero",
                "passed": bounded_coupling,
                "actual": {
                    "max_abs_S_ij": max_abs,
                    "max_abs_diagonal_S_i": diagonal_max_abs,
                    "entries_above_threshold": len(entries),
                    "threshold": COUPLING_THRESHOLD,
                },
                "expected": "at least one finite modeled-tAI coupling entry above the bounded-contact threshold",
            },
            {
                "name": "no_powered_survival_without_more_species",
                "passed": True,
                "actual": "3 organisms are insufficient for powered survival; this is modeled-tAI bounded coupling, not ribo-seq/proteomics validation",
                "expected": f"powered tAI survival requires >= {POWERED_SURVIVAL_MIN_SPECIES} species plus matched translation-efficiency readouts",
            },
        ]

        if not bounded_coupling:
            emit(
                "needs_data",
                checks=checks,
                missing_data=missing_powered_survival_data(),
                reason="modeled-tAI statistics are finite but do not support even the bounded coupling threshold",
            )

        emit(
            "passed",
            checks=checks,
            result={
                "claimed_layer": "translation_realization_modeled_underpowered",
                "readout": "modeled tAI w_codon from GtRNAdb tRNA gene copy and dos Reis wobble s-values",
                "organism_n": len(ORGANISMS),
                "codon_count_space": len(codons),
                "organisms": organisms,
                "coupling_threshold": COUPLING_THRESHOLD,
                "survival_scores_diagonal_S_i": survival_scores,
                "survival_matrix_S_ij": survival_matrix,
                "entries_above_threshold": entries,
                "break_condition": "needs_data if finite modeled-tAI matrix has no |S_ij| above the bounded-contact threshold, or if powered survival is requested without >=40 matched species",
                "break_condition_met": False,
                "cannot_claim": cannot_claim(),
                "missing_data_for_powered_survival": missing_powered_survival_data(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable modeled-tAI input data")


if __name__ == "__main__":
    main()

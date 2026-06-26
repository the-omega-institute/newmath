#!/usr/bin/env python3
"""Track A yeast codon-wobble boundary response with a permutation null."""

from __future__ import annotations

import hashlib
import json
import math
import random
from pathlib import Path
from typing import Any


EXPERIMENT_ID = "track-a-yeast-wobble-boundary-response"
CLAIM_ID = "track-a.codon-wobble-boundary-response.yeast"
CDS_ABUNDANCE_PATH = (
    "tools/fibonacci_reality/data/"
    "cds_codon_abundance_saccharomyces_cerevisiae.json"
)
TRNA_PATH = (
    "tools/fibonacci_reality/data/"
    "gtrnadb_trna_all_copy_saccharomyces_cerevisiae.json"
)
MIN_CODON_COUNT = 50
NULL_N = 1000
WOBBLE_DISCOUNT = 0.5
EPS = 1e-12

STANDARD_CODE = {
    "TTT": "F", "TTC": "F", "TTA": "L", "TTG": "L",
    "TCT": "S", "TCC": "S", "TCA": "S", "TCG": "S",
    "TAT": "Y", "TAC": "Y", "TAA": "*", "TAG": "*",
    "TGT": "C", "TGC": "C", "TGA": "*", "TGG": "W",
    "CTT": "L", "CTC": "L", "CTA": "L", "CTG": "L",
    "CCT": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAT": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGT": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "ATT": "I", "ATC": "I", "ATA": "I", "ATG": "M",
    "ACT": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAT": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGT": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GTT": "V", "GTC": "V", "GTA": "V", "GTG": "V",
    "GCT": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAT": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGT": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

COMPLEMENT_RNA = {"A": "U", "T": "A", "G": "C", "C": "G"}


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def emit(status: str, checks: list[dict[str, Any]], result: dict[str, Any]) -> None:
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


def dna_codon_to_wc_anticodon_rna(codon: str) -> str:
    return "".join(COMPLEMENT_RNA[base] for base in reversed(codon.upper()))


def anticodon_reads_codon(anticodon: str, codon: str) -> bool:
    codon_rna = codon.upper().replace("T", "U")
    if len(anticodon) != 3 or len(codon_rna) != 3:
        return False
    if anticodon[1] != COMPLEMENT_RNA[codon[1]] or anticodon[2] != COMPLEMENT_RNA[codon[0]]:
        return False
    wobble_base = anticodon[0]
    codon_third = codon_rna[2]
    allowed = {
        "C": {"G"},
        "A": {"U"},
        "U": {"A", "G"},
        "G": {"C", "U"},
    }
    return codon_third in allowed.get(wobble_base, set())


def build_supply_maps(trna_copies: dict[str, int]) -> tuple[dict[str, float], dict[str, float], dict[str, Any]]:
    # GtRNAdb FASTA headers have forms such as "Ala (AGC)"; fetch_multi_organism.py
    # parses that parenthesized field as the anticodon and normalizes T to U.
    exact: dict[str, float] = {}
    supply: dict[str, float] = {}
    for codon, amino_acid in STANDARD_CODE.items():
        if amino_acid == "*":
            exact[codon] = 0.0
            supply[codon] = 0.0
            continue
        wc_anticodon = dna_codon_to_wc_anticodon_rna(codon)
        exact_copies = float(trna_copies.get(wc_anticodon, 0))
        exact[codon] = exact_copies
        wobble_copies = 0.0
        for anticodon, copies in trna_copies.items():
            if anticodon == wc_anticodon:
                continue
            if anticodon_reads_codon(anticodon, codon):
                wobble_copies += float(copies)
        supply[codon] = exact_copies + WOBBLE_DISCOUNT * wobble_copies
    sanity = {
        "met_atg_wc_anticodon": dna_codon_to_wc_anticodon_rna("ATG"),
        "met_atg_exact_copies": int(exact["ATG"]),
        "trp_tgg_wc_anticodon": dna_codon_to_wc_anticodon_rna("TGG"),
        "trp_tgg_exact_copies": int(exact["TGG"]),
        "stop_exact_copies": {
            codon: int(exact[codon])
            for codon in sorted(codon for codon, aa in STANDARD_CODE.items() if aa == "*")
        },
    }
    return exact, supply, sanity


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            raise ValueError("rank-deficient least-squares system")
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
    width = len(design[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, y in zip(design, response):
        for i in range(width):
            xty[i] += row[i] * y
            for j in range(width):
                xtx[i][j] += row[i] * row[j]
    return solve_linear_system(xtx, xty)


def residuals(design: list[list[float]], response: list[float]) -> list[float]:
    coeffs = ols_coefficients(design, response)
    return [
        y - sum(coeffs[index] * row[index] for index in range(len(coeffs)))
        for row, y in zip(design, response)
    ]


def sse_for_design(design: list[list[float]], response: list[float]) -> tuple[float, list[float]]:
    coeffs = ols_coefficients(design, response)
    sse = 0.0
    for row, y in zip(design, response):
        fit = sum(coeffs[index] * row[index] for index in range(len(coeffs)))
        diff = y - fit
        sse += diff * diff
    return sse, coeffs


def boundary_delta_r2(rhos: list[float], response: list[float]) -> tuple[float, list[float]]:
    intercept = [[1.0] for _ in response]
    baseline_sse, _ = sse_for_design(intercept, response)
    if baseline_sse <= EPS:
        raise ValueError("residual response has zero variance")
    design = [[1.0, rho, rho * rho] for rho in rhos]
    model_sse, coeffs = sse_for_design(design, response)
    delta = max(0.0, min(1.0, (baseline_sse - model_sse) / baseline_sse))
    return delta, [coeffs[1], coeffs[2]]


def deterministic_seed(n_genes: int) -> int:
    payload = f"{EXPERIMENT_ID}:{n_genes}:{NULL_N}".encode("utf-8")
    return int.from_bytes(hashlib.sha256(payload).digest()[:8], "big")


def gene_metrics(
    joined: list[dict[str, Any]],
    exact_supply: dict[str, float],
    discounted_supply: dict[str, float],
) -> tuple[list[str], list[float], list[float], list[float], int]:
    gene_ids: list[str] = []
    rhos: list[float] = []
    supplies: list[float] = []
    log_lengths: list[float] = []
    log_abundances: list[float] = []
    skipped = 0
    for row in joined:
        if row.get("len_mod3_ok") is not True:
            skipped += 1
            continue
        total = row.get("codon_count_total")
        abundance = row.get("abundance_ppm")
        cds_len = row.get("cds_len_nt")
        counts = row.get("codon_counts")
        if (
            not isinstance(total, int)
            or total < MIN_CODON_COUNT
            or not isinstance(abundance, (int, float))
            or float(abundance) <= 0.0
            or not isinstance(cds_len, int)
            or cds_len <= 0
            or not isinstance(counts, dict)
        ):
            skipped += 1
            continue
        sense_total = 0
        exact_missing_weight = 0
        weighted_supply = 0.0
        for codon, raw_count in counts.items():
            codon = str(codon).upper()
            if STANDARD_CODE.get(codon) in (None, "*"):
                continue
            if not isinstance(raw_count, int) or raw_count <= 0:
                continue
            sense_total += raw_count
            if exact_supply.get(codon, 0.0) <= 0.0:
                exact_missing_weight += raw_count
            weighted_supply += raw_count * discounted_supply.get(codon, 0.0)
        if sense_total <= 0:
            skipped += 1
            continue
        gene_ids.append(str(row.get("cds_match_id") or row.get("protein_id") or len(gene_ids)))
        rhos.append(exact_missing_weight / float(sense_total))
        supplies.append(weighted_supply / float(sense_total))
        log_lengths.append(math.log10(float(cds_len)))
        log_abundances.append(math.log10(float(abundance)))
    return gene_ids, rhos, supplies, log_lengths, log_abundances, skipped


def main() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    required = [repo_root / CDS_ABUNDANCE_PATH, repo_root / TRNA_PATH]
    missing = [str(path.relative_to(repo_root)) for path in required if not path.exists()]
    if missing:
        emit(
            "needs_data",
            [check("track_a_boundary_response_computed", False, "required data missing")],
            {"missing_required_data": missing},
        )
        return

    try:
        cds_data = load_json(repo_root / CDS_ABUNDANCE_PATH)
        trna_data = load_json(repo_root / TRNA_PATH)
        joined = cds_data.get("joined")
        trna_copies = trna_data.get("trna_all_copies")
        if not isinstance(joined, list) or not isinstance(trna_copies, dict):
            raise ValueError("required data payloads do not expose joined/trna_all_copies")
        normalized_trna = {str(key).upper().replace("T", "U"): int(value) for key, value in trna_copies.items()}
        exact_supply, discounted_supply, sanity = build_supply_maps(normalized_trna)
        if sanity["met_atg_exact_copies"] <= 0 or sanity["trp_tgg_exact_copies"] <= 0:
            raise ValueError("GtRNAdb anticodon sanity check failed for Met or Trp")
        if any(value != 0 for value in sanity["stop_exact_copies"].values()):
            raise ValueError("stop-codon tRNA sanity check failed")

        gene_ids, rhos, supplies, log_lengths, log_abundances, skipped = gene_metrics(
            joined,
            exact_supply,
            discounted_supply,
        )
        if len(gene_ids) < 50:
            emit(
                "needs_data",
                [check("track_a_boundary_response_computed", False, "too few valid genes")],
                {"n_genes": len(gene_ids), "min_required_genes": 50},
            )
            return

        baseline_design = [[1.0, supply, log_len] for supply, log_len in zip(supplies, log_lengths)]
        abundance_residuals = residuals(baseline_design, log_abundances)
        observed_delta, coeffs = boundary_delta_r2(rhos, abundance_residuals)

        rng = random.Random(deterministic_seed(len(gene_ids)))
        null_deltas: list[float] = []
        shuffled = list(rhos)
        for _ in range(NULL_N):
            rng.shuffle(shuffled)
            null_delta, _ = boundary_delta_r2(shuffled, abundance_residuals)
            null_deltas.append(null_delta)
        null_percentile = sum(1 for value in null_deltas if value < observed_delta) / float(NULL_N)
        supported = null_percentile >= 0.95

        checks = [
            check(
                "track_a_boundary_response_computed",
                True,
                "computed yeast codon-wobble boundary-response residual model with deterministic Null95 permutation",
            )
        ]
        result = {
            "n_genes": len(gene_ids),
            "n_input_joined": len(joined),
            "n_skipped": skipped,
            "rho_definition": (
                "per-gene sense-codon fraction, weighted by codon counts, whose Watson-Crick "
                "cognate anticodon is absent from the GtRNAdb yeast tRNA gene-copy pool"
            ),
            "trna_key_convention": (
                "trna_all_copies keys are GtRNAdb/tRNAscan anticodon triplets normalized to RNA U; "
                "basis: fetch_multi_organism.py parses FASTA headers like 'Ala (AGC)' as anticodon, "
                "and yeast sanity checks give ATG->CAU and TGG->CCA with positive copies while stops have none"
            ),
            "trna_key_sanity": sanity,
            "supply_definition": (
                "per-gene sense-codon weighted mean of exact Watson-Crick tRNA copy count plus "
                "0.5 times same-position wobble-readable tRNA copies; this baseline is not fitted"
            ),
            "delta_r2_observed": observed_delta,
            "q_coefficients": coeffs,
            "null_percentile": null_percentile,
            "boundary_response_supported": supported,
            "null_n": NULL_N,
            "deterministic_seed": deterministic_seed(len(gene_ids)),
            "note": (
                "正负皆真结果; 无 φ/571/Z6 预设; A-P-site dwell 机制 needs_data 另记"
            ),
        }
        print(
            "Track A yeast wobble boundary response: "
            f"n={len(gene_ids)} delta_r2={observed_delta:.6g} "
            f"null_percentile={null_percentile:.3f} supported={supported}"
        )
        emit("passed", checks, result)
    except Exception as exc:
        emit(
            "failed",
            [check("track_a_boundary_response_computed", False, str(exc))],
            {"error": str(exc)},
        )


if __name__ == "__main__":
    main()

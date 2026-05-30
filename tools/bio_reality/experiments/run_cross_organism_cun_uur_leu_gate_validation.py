#!/usr/bin/env python3
"""Cross-organism CUN/UUR Leu gate translation_realization probe."""

import json
import math
import pathlib
import sys


EXPERIMENT_ID = "cross_organism_cun_uur_leu_gate_validation"
CLAIM_ID = "h3.translation_realization.cross_organism.cun_uur_leu_gate"

REQUIRED_ORGANISMS = [
    "homo_sapiens",
    "saccharomyces_cerevisiae",
    "escherichia_coli_k12",
]

REQUIRED_DATA = [
    "tools/bio_reality/data/kazusa_codon_usage_homo_sapiens.json",
    "tools/bio_reality/data/kazusa_codon_usage_saccharomyces_cerevisiae.json",
    "tools/bio_reality/data/kazusa_codon_usage_escherichia_coli_k12.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_homo_sapiens.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_saccharomyces_cerevisiae.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_escherichia_coli_k12.json",
]

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
CUN_TRNA_ANTICODONS = ["UAG", "GAG", "CAG", "AAG"]
UUR_TRNA_ANTICODONS = ["CAA", "UAA"]


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def numeric(value, field):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def smoothed_log_ratio(numerator, denominator):
    return math.log((numerator + 0.5) / (denominator + 0.5))


def pearson_corr(xs, ys):
    n = len(xs)
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    cov = sum((xs[i] - mean_x) * (ys[i] - mean_y) for i in range(n))
    var_x = sum((x - mean_x) ** 2 for x in xs)
    var_y = sum((y - mean_y) ** 2 for y in ys)
    if var_x <= 0.0 or var_y <= 0.0:
        return 0.0
    return cov / math.sqrt(var_x * var_y)


def residualize_against_single_control(values, controls):
    n = len(values)
    mean_v = sum(values) / n
    mean_c = sum(controls) / n
    var_c = sum((c - mean_c) ** 2 for c in controls)
    if var_c <= 0.0:
        return [v - mean_v for v in values]
    slope = sum((controls[i] - mean_c) * (values[i] - mean_v) for i in range(n)) / var_c
    intercept = mean_v - slope * mean_c
    return [values[i] - (intercept + slope * controls[i]) for i in range(n)]


def organism_codons(repo, organism):
    path = repo / f"tools/bio_reality/data/kazusa_codon_usage_{organism}.json"
    raw = load_json(path)
    counts = raw.get("codon_counts")
    aa_counts = raw.get("amino_acid_counts")
    if not isinstance(counts, dict):
        raise ValueError(f"{path} must contain codon_counts object")
    if not isinstance(aa_counts, dict):
        raise ValueError(f"{path} must contain amino_acid_counts object")

    cun = sum(numeric(counts.get(codon, 0), f"{organism} codon_counts.{codon}") for codon in CUN_CODONS)
    uur = sum(numeric(counts.get(codon, 0), f"{organism} codon_counts.{codon}") for codon in UUR_CODONS)
    leu_total = numeric(aa_counts.get("L", cun + uur), f"{organism} amino_acid_counts.L")
    aa_total = sum(numeric(value, f"{organism} amino_acid_counts") for value in aa_counts.values())
    non_leu_total = max(aa_total - leu_total, 0.0)

    return {
        "CUN": cun,
        "UUR": uur,
        "Leu_total": leu_total,
        "AA_total": aa_total,
        "log_CUN_over_UUR": smoothed_log_ratio(cun, uur),
        "aa_composition_control": smoothed_log_ratio(leu_total, non_leu_total),
    }


def organism_trna(repo, organism):
    path = repo / f"tools/bio_reality/data/gtrnadb_trna_leu_copy_{organism}.json"
    raw = load_json(path)
    copies = raw.get("trna_leu_copies")
    if not isinstance(copies, dict):
        raise ValueError(f"{path} must contain trna_leu_copies object")
    cun_trna = sum(
        numeric(copies.get(anticodon, 0), f"{organism} trna_leu_copies.{anticodon}")
        for anticodon in CUN_TRNA_ANTICODONS
    )
    uur_trna = sum(
        numeric(copies.get(anticodon, 0), f"{organism} trna_leu_copies.{anticodon}")
        for anticodon in UUR_TRNA_ANTICODONS
    )
    return {
        "CUN_tRNA_Leu_copies": cun_trna,
        "UUR_tRNA_Leu_copies": uur_trna,
        "log_CUN_trna_over_UUR_trna": smoothed_log_ratio(cun_trna, uur_trna),
    }


def main():
    repo = pathlib.Path(__file__).resolve().parents[3]
    missing = [path for path in REQUIRED_DATA if not (repo / path).exists()]
    if missing:
        emit(
            "needs_data",
            missing_required_data=missing,
            reason="kazusa or gtrnadb data not present",
        )

    try:
        organisms = {}
        for organism in REQUIRED_ORGANISMS:
            codon_row = organism_codons(repo, organism)
            trna_row = organism_trna(repo, organism)
            codon_row.update(trna_row)
            organisms[organism] = codon_row

        ys = [organisms[organism]["log_CUN_over_UUR"] for organism in REQUIRED_ORGANISMS]
        xs = [organisms[organism]["log_CUN_trna_over_UUR_trna"] for organism in REQUIRED_ORGANISMS]
        controls = [organisms[organism]["aa_composition_control"] for organism in REQUIRED_ORGANISMS]
        signs = [1 if y > 0 else -1 for y in ys]
        sign_uniform = len(set(signs)) == 1

        residual_xs = residualize_against_single_control(xs, controls)
        residual_ys = residualize_against_single_control(ys, controls)
        partial_pearson = pearson_corr(residual_xs, residual_ys)

        checks = [
            {
                "name": "cross_organism_data_loaded",
                "passed": True,
                "actual": list(organisms.keys()),
                "expected": REQUIRED_ORGANISMS,
            },
            {
                "name": "sign_not_uniform_across_organisms",
                "passed": not sign_uniform,
                "actual": {"signs": signs, "log_ratios": ys},
                "expected": "at least one organism with opposite sign",
            },
            {
                "name": "positive_partial_correlation_with_trna_leu_ratio",
                "passed": partial_pearson > 0.5,
                "actual": {"partial_pearson": partial_pearson, "n": len(xs)},
                "expected": {"min_pearson": 0.5, "min_n": 3},
            },
            {
                "name": "no_cross_layer_promotion_to_function_or_structure",
                "passed": True,
                "actual": [
                    "The CUN/UUR codon-usage and tRNA-Leu copy contact does not establish protein folding.",
                    "The contact does not establish biological function or physical admissibility.",
                    "The contact does not promote translation_realization to a global biological law.",
                    "Sign reversal is reported as context-dependent, not as universal directionality.",
                ],
                "expected": "explicit cannot-claim across function, structure, physical admissibility, and universality",
            },
        ]
        all_passed = all(check["passed"] for check in checks)
        emit(
            "passed" if all_passed else "failed",
            checks=checks,
            organisms=organisms,
            pearson=partial_pearson,
            sign_uniform=sign_uniform,
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable required data")


if __name__ == "__main__":
    main()

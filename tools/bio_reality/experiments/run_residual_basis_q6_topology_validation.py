#!/usr/bin/env python3
"""Residual-basis Q6 codon-usage topology validation probe."""

import json
import math
import pathlib
import sys


EXPERIMENT_ID = "residual_basis_q6_topology_validation"
CLAIM_ID = "h3.codon_usage_topology.residual_basis.q6_topology_after_aa_quotient"

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

VARIANCE_THRESHOLD = 0.01
MIN_NONZERO_FRACTION = 0.6
PSEUDOCOUNT = 0.5

AA_BY_ELEMENT = {
    "K_AAA": "K",
    "Arg_AGR": "R",
    "Ile_AUA": "I",
    "Leu_CUN_vs_UUR": "L",
    "Leu_UUA_vs_UUG": "L",
    "Ser_UCR_vs_AGY": "S",
    "Ser_UCA_vs_UCG": "S",
    "Thr_ACR_vs_ACY": "T",
    "f3_stress_pair_antisymmetric": "multi_family",
}

STANDARD_CODE_FALLBACK = {
    **dict.fromkeys(["AAA", "AAG"], "K"),
    **dict.fromkeys(["AGA", "AGG", "CGU", "CGC", "CGA", "CGG"], "R"),
    **dict.fromkeys(["AUA", "AUU", "AUC"], "I"),
    **dict.fromkeys(["CUU", "CUC", "CUA", "CUG", "UUA", "UUG"], "L"),
    **dict.fromkeys(["UCU", "UCC", "UCA", "UCG", "AGU", "AGC"], "S"),
    **dict.fromkeys(["ACU", "ACC", "ACA", "ACG"], "T"),
}

F3_FOUR_CODON_FAMILIES = {
    "Ala_GCN": ["GCU", "GCC", "GCA", "GCG"],
    "Arg_CGN": ["CGU", "CGC", "CGA", "CGG"],
    "Gly_GGN": ["GGU", "GGC", "GGA", "GGG"],
    "Leu_CUN": ["CUU", "CUC", "CUA", "CUG"],
    "Pro_CCN": ["CCU", "CCC", "CCA", "CCG"],
    "Ser_UCN": ["UCU", "UCC", "UCA", "UCG"],
    "Thr_ACN": ["ACU", "ACC", "ACA", "ACG"],
    "Val_GUN": ["GUU", "GUC", "GUA", "GUG"],
}

ELEMENT_SPECS = {
    "K_AAA": (["AAA"], ["AAG"]),
    "Arg_AGR": (["AGA", "AGG"], ["CGU", "CGC", "CGA", "CGG"]),
    "Ile_AUA": (["AUA"], ["AUU", "AUC"]),
    "Leu_CUN_vs_UUR": (["CUU", "CUC", "CUA", "CUG"], ["UUA", "UUG"]),
    "Leu_UUA_vs_UUG": (["UUA"], ["UUG"]),
    "Ser_UCR_vs_AGY": (["UCU", "UCC", "UCA", "UCG"], ["AGU", "AGC"]),
    "Ser_UCA_vs_UCG": (["UCA"], ["UCG"]),
    "Thr_ACR_vs_ACY": (["ACA", "ACG"], ["ACU", "ACC"]),
}


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value, field):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def smoothed_log_ratio(numerator, denominator):
    return math.log((numerator + PSEUDOCOUNT) / (denominator + PSEUDOCOUNT))


def mean(values):
    return sum(values) / len(values)


def variance(values):
    center = mean(values)
    return sum((value - center) ** 2 for value in values) / len(values)


def load_standard_code(repo):
    path = repo / "tools/bio_reality/data/ncbi_genetic_codes.json"
    if not path.exists():
        return dict(STANDARD_CODE_FALLBACK), False
    raw = load_json(path)
    codon_order = raw.get("codon_order")
    tables = raw.get("tables")
    if not isinstance(codon_order, list) or not isinstance(tables, list):
        raise ValueError(f"{path} must contain codon_order and tables")
    standard = next((table for table in tables if table.get("table_id") == 1), None)
    if not isinstance(standard, dict) or not isinstance(standard.get("aa"), str):
        raise ValueError(f"{path} must contain NCBI table_id 1")
    aa_string = standard["aa"]
    if len(aa_string) != len(codon_order):
        raise ValueError(f"{path} standard code length does not match codon_order")
    return {str(codon): aa_string[index] for index, codon in enumerate(codon_order)}, True


def validate_standard_code(code):
    return [
        {"codon": codon, "expected": expected, "actual": code.get(codon)}
        for codon, expected in STANDARD_CODE_FALLBACK.items()
        if code.get(codon) != expected
    ]


def codon_total(counts, organism, codons):
    return sum(numeric(counts.get(codon, 0), f"{organism} codon_counts.{codon}") for codon in codons)


def aa_anchor(aa_counts, organism, aa):
    if aa == "multi_family":
        selected = sum(
            numeric(aa_counts.get(family, 0), f"{organism} amino_acid_counts.{family}")
            for family in ["A", "R", "G", "L", "P", "S", "T", "V"]
        )
        total = sum(numeric(value, f"{organism} amino_acid_counts") for value in aa_counts.values())
        return smoothed_log_ratio(selected, max(total - selected, 0.0))
    aa_count = numeric(aa_counts.get(aa, 0), f"{organism} amino_acid_counts.{aa}")
    total = sum(numeric(value, f"{organism} amino_acid_counts") for value in aa_counts.values())
    return smoothed_log_ratio(aa_count, max(total - aa_count, 0.0))


def f3_stress_pair_antisymmetric(counts, organism):
    family_values = {}
    for family_name, codons in F3_FOUR_CODON_FAMILIES.items():
        pyrimidine = codon_total(counts, organism, codons[:2])
        purine = codon_total(counts, organism, codons[2:])
        family_values[family_name] = smoothed_log_ratio(purine, pyrimidine)
    return mean(list(family_values.values())), family_values


def organism_rows(repo):
    rows = {}
    for organism in REQUIRED_ORGANISMS:
        codon_path = repo / f"tools/bio_reality/data/kazusa_codon_usage_{organism}.json"
        trna_path = repo / f"tools/bio_reality/data/gtrnadb_trna_leu_copy_{organism}.json"
        codon_raw = load_json(codon_path)
        trna_raw = load_json(trna_path)
        counts = codon_raw.get("codon_counts")
        aa_counts = codon_raw.get("amino_acid_counts")
        trna_leu = trna_raw.get("trna_leu_copies")
        if not isinstance(counts, dict):
            raise ValueError(f"{codon_path} must contain codon_counts object")
        if not isinstance(aa_counts, dict):
            raise ValueError(f"{codon_path} must contain amino_acid_counts object")
        if not isinstance(trna_leu, dict):
            raise ValueError(f"{trna_path} must contain trna_leu_copies object")

        raw = {
            element: smoothed_log_ratio(
                codon_total(counts, organism, numerator),
                codon_total(counts, organism, denominator),
            )
            for element, (numerator, denominator) in ELEMENT_SPECS.items()
        }
        raw["f3_stress_pair_antisymmetric"], f3_by_family = f3_stress_pair_antisymmetric(
            counts, organism
        )
        rows[organism] = {
            "raw": raw,
            "aa_anchors": {
                element: aa_anchor(aa_counts, organism, aa)
                for element, aa in AA_BY_ELEMENT.items()
            },
            "f3_family_components": f3_by_family,
            "loaded_context": {
                "kazusa_codon_counts": True,
                "kazusa_amino_acid_counts": True,
                "gtrnadb_trna_leu_copy": True,
                "organism_n_is_single_codon_count_contact": True,
            },
        }
    return rows


def projected_residuals(values, anchors):
    anchor_mean = mean(anchors)
    return [values[index] - (anchors[index] - anchor_mean) for index in range(len(values))]


def element_residual_report(rows):
    report = {}
    nonzero_count = 0
    for element in AA_BY_ELEMENT:
        values = [rows[organism]["raw"][element] for organism in REQUIRED_ORGANISMS]
        anchors = [rows[organism]["aa_anchors"][element] for organism in REQUIRED_ORGANISMS]
        residuals = projected_residuals(values, anchors)
        var = variance(residuals)
        nonzero = var > VARIANCE_THRESHOLD
        if nonzero:
            nonzero_count += 1
        report[element] = {
            "aa_family_anchor": AA_BY_ELEMENT[element],
            "per_organism_raw_values": dict(zip(REQUIRED_ORGANISMS, values)),
            "per_organism_aa_anchor": dict(zip(REQUIRED_ORGANISMS, anchors)),
            "per_organism_projected_residuals": dict(zip(REQUIRED_ORGANISMS, residuals)),
            "residual_variance": var,
            "nonzero_after_projection": nonzero,
        }
    return report, nonzero_count / len(AA_BY_ELEMENT)


def main():
    repo = pathlib.Path(__file__).resolve().parents[3]
    missing = [path for path in REQUIRED_DATA if not (repo / path).exists()]
    if missing:
        emit(
            "needs_data",
            missing_required_data=missing,
            reason="required Kazusa or GtRNAdb organism data not present",
        )

    try:
        code, code_loaded = load_standard_code(repo)
        code_mismatches = validate_standard_code(code)
        if code_mismatches:
            raise ValueError(f"standard genetic code mismatch: {code_mismatches}")

        rows = organism_rows(repo)
        element_residuals, nonzero_fraction = element_residual_report(rows)
        residuals_complete = all(
            math.isfinite(item["residual_variance"])
            and len(item["per_organism_projected_residuals"]) == len(REQUIRED_ORGANISMS)
            for item in element_residuals.values()
        )
        nontrivial = nonzero_fraction >= MIN_NONZERO_FRACTION

        checks = [
            {
                "name": "cross_organism_codon_counts_loaded",
                "passed": True,
                "actual": {
                    "organisms": REQUIRED_ORGANISMS,
                    "organism_n": len(REQUIRED_ORGANISMS),
                    "within_organism_contact": "one codon-count table per organism",
                    "ncbi_genetic_code_loaded": code_loaded,
                },
                "expected": "Kazusa codon counts and GtRNAdb tRNA-Leu context for all three organisms",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": residuals_complete,
                "actual": {
                    "elements": list(element_residuals.keys()),
                    "element_count": len(element_residuals),
                    "finite_contact_not_population_estimate": True,
                },
                "expected": "all 9 B*_Q6 residual elements have finite per-organism values",
            },
            {
                "name": "aa_quotient_residuals_nontrivial",
                "passed": nontrivial,
                "actual": {
                    "nonzero_fraction": nonzero_fraction,
                    "nonzero_count": sum(
                        1
                        for item in element_residuals.values()
                        if item["nonzero_after_projection"]
                    ),
                    "element_count": len(element_residuals),
                    "variance_threshold": VARIANCE_THRESHOLD,
                },
                "expected": {
                    "min_nonzero_fraction": MIN_NONZERO_FRACTION,
                    "break_condition": "failed if all or more than 40% of B*_Q6 elements collapse to AA-fiber constant at residual variance <= 0.01",
                },
            },
            {
                "name": "no_cross_layer_promotion_to_translation_function_structure",
                "passed": True,
                "actual": [
                    "Does not assert ribosome-mediated translation realization from codon-count residuals alone.",
                    "Does not assert protein folding, structural order, physical admissibility, biological function, biochemical mechanism, or universal biological law.",
                    "Does not promote nonzero per-organism residual variance to a translation-efficiency, ribosome-occupancy, or protein-output claim.",
                    "Does not interpret B*_Q6 residual signs as universal directionality.",
                ],
                "expected": "explicit cannot-claim boundary for translation, function, structure, and directionality",
            },
        ]
        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            checks=checks,
            element_residuals=element_residuals,
            nonzero_fraction=nonzero_fraction,
            organism_count=len(REQUIRED_ORGANISMS),
            organism_contact_scope="finite contact: human, yeast, and E. coli; not a population estimate",
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable required data")


if __name__ == "__main__":
    main()

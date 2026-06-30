#!/usr/bin/env python3
"""Exact fold certificate for the NCBI standard genetic code.

The certificate is deliberately narrow: it enumerates translation table 1 as a
64 codon to 21 output-class map, then derives the doublet-box fold counts.  It
does not treat Fibonacci or small ratio coincidences as forcing evidence.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import sys
from math import gcd


EXPERIMENT_ID = "genetic_code_fold_cert"
CLAIM_ID = "bridge.genetic_code.fold_structure_64_16_25_21"

BASES = ("U", "C", "A", "G")

CODON_TO_OUTPUT = {
    "UUU": "Phe", "UUC": "Phe", "UUA": "Leu", "UUG": "Leu",
    "UCU": "Ser", "UCC": "Ser", "UCA": "Ser", "UCG": "Ser",
    "UAU": "Tyr", "UAC": "Tyr", "UAA": "Stop", "UAG": "Stop",
    "UGU": "Cys", "UGC": "Cys", "UGA": "Stop", "UGG": "Trp",
    "CUU": "Leu", "CUC": "Leu", "CUA": "Leu", "CUG": "Leu",
    "CCU": "Pro", "CCC": "Pro", "CCA": "Pro", "CCG": "Pro",
    "CAU": "His", "CAC": "His", "CAA": "Gln", "CAG": "Gln",
    "CGU": "Arg", "CGC": "Arg", "CGA": "Arg", "CGG": "Arg",
    "AUU": "Ile", "AUC": "Ile", "AUA": "Ile", "AUG": "Met",
    "ACU": "Thr", "ACC": "Thr", "ACA": "Thr", "ACG": "Thr",
    "AAU": "Asn", "AAC": "Asn", "AAA": "Lys", "AAG": "Lys",
    "AGU": "Ser", "AGC": "Ser", "AGA": "Arg", "AGG": "Arg",
    "GUU": "Val", "GUC": "Val", "GUA": "Val", "GUG": "Val",
    "GCU": "Ala", "GCC": "Ala", "GCA": "Ala", "GCG": "Ala",
    "GAU": "Asp", "GAC": "Asp", "GAA": "Glu", "GAG": "Glu",
    "GGU": "Gly", "GGC": "Gly", "GGA": "Gly", "GGG": "Gly",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status == "certified" else 3)


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def output_classes(codons: list[str]) -> dict[str, list[str]]:
    classes: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        classes[CODON_TO_OUTPUT[codon]].append(codon)
    return dict(sorted(classes.items()))


def degeneracy_spectrum(classes: dict[str, list[str]]) -> dict[str, int]:
    spectrum = Counter(len(codons) for codons in classes.values())
    return {str(size): spectrum[size] for size in sorted(spectrum)}


def doublet_boxes(codons: list[str]) -> dict[str, dict[str, object]]:
    boxes: dict[str, dict[str, object]] = {}
    for left, right in product(BASES, repeat=2):
        prefix = left + right
        box_codons = [codon for codon in codons if codon.startswith(prefix)]
        fragments: dict[str, list[str]] = defaultdict(list)
        for codon in box_codons:
            fragments[CODON_TO_OUTPUT[codon]].append(codon)
        boxes[prefix] = {
            "codons": box_codons,
            "outputs": dict(sorted(fragments.items())),
            "fragment_count": len(fragments),
        }
    return dict(sorted(boxes.items()))


def box_decomposition(boxes: dict[str, dict[str, object]]) -> dict[str, object]:
    fragment_counts = Counter(int(box["fragment_count"]) for box in boxes.values())
    pure = fragment_counts[1]
    binary = fragment_counts[2]
    tri = fragment_counts[3]
    kind_by_box = {
        prefix: ("pure" if box["fragment_count"] == 1 else "binary_split" if box["fragment_count"] == 2 else "tri_split")
        for prefix, box in boxes.items()
    }
    return {
        "pure": pure,
        "binary_split": binary,
        "tri_split": tri,
        "fragments": sum(int(box["fragment_count"]) for box in boxes.values()),
        "fragment_counts": {str(key): fragment_counts[key] for key in sorted(fragment_counts)},
        "kind_by_box": kind_by_box,
    }


def cross_box_merges(boxes: dict[str, dict[str, object]]) -> dict[str, object]:
    boxes_by_output: dict[str, list[str]] = defaultdict(list)
    for prefix, box in boxes.items():
        for output in box["outputs"]:
            boxes_by_output[output].append(prefix)
    spanning = {
        output: prefixes
        for output, prefixes in sorted(boxes_by_output.items())
        if len(prefixes) > 1
    }
    merge_count = sum(len(prefixes) - 1 for prefixes in spanning.values())
    return {"count": merge_count, "spanning_outputs": spanning}


def reduced_ratio(numerator: int, denominator: int) -> dict[str, object]:
    divisor = gcd(numerator, denominator)
    return {
        "numerator": numerator,
        "denominator": denominator,
        "reduced": f"{numerator // divisor}/{denominator // divisor}",
        "value": numerator / denominator,
    }


def fibonacci_numbers(limit: int) -> dict[int, int]:
    fibs = {2: 1, 3: 2}
    index = 4
    while fibs[index - 1] <= limit:
        fibs[index] = fibs[index - 1] + fibs[index - 2]
        index += 1
    return {key: value for key, value in fibs.items() if value <= limit}


def zeckendorf(n: int) -> list[tuple[int, int]]:
    fibs = fibonacci_numbers(n)
    remaining = n
    terms: list[tuple[int, int]] = []
    for index, value in sorted(fibs.items(), reverse=True):
        if value <= remaining:
            terms.append((index, value))
            remaining -= value
    if remaining != 0:
        raise RuntimeError("Zeckendorf decomposition failed")
    return terms


def main() -> None:
    codons = codon_order()
    classes = output_classes(codons)
    boxes = doublet_boxes(codons)
    box_info = box_decomposition(boxes)
    merge_info = cross_box_merges(boxes)
    surplus = len(codons) - len(classes)
    z_terms = zeckendorf(surplus)
    z_string = f"{surplus}=" + "+".join(f"F{index}" for index, _ in z_terms) + " (universal)"

    ratios = {
        "pure_fourfold_boxes_over_twofold_classes": reduced_ratio(
            int(box_info["pure"]),
            degeneracy_spectrum(classes)["2"],
        ),
        "singletons_over_sextets": reduced_ratio(
            degeneracy_spectrum(classes)["1"],
            degeneracy_spectrum(classes)["6"],
        ),
        "threefold_surplus_over_twofold_classes": reduced_ratio(
            (3 - 1) * degeneracy_spectrum(classes)["3"],
            degeneracy_spectrum(classes)["2"],
        ),
    }

    hard = {
        "codon_count": len(codons),
        "output_class_count": len(classes),
        "degeneracy_spectrum": degeneracy_spectrum(classes),
        "doublet_box_count": len(boxes),
        "box_decomp": [box_info["pure"], box_info["binary_split"], box_info["tri_split"]],
        "box_fragments": box_info["fragments"],
        "cross_box_merges": merge_info["count"],
        "fold_chain": [len(codons), len(boxes), box_info["fragments"], len(classes)],
        "surplus": surplus,
    }

    checks = [
        check_row("codon_table_covers_ucag_cube", sorted(CODON_TO_OUTPUT), sorted(codons)),
        check_row("codon_count", hard["codon_count"], 64),
        check_row("output_class_count", hard["output_class_count"], 21),
        check_row("degeneracy_spectrum", hard["degeneracy_spectrum"], {"1": 2, "2": 9, "3": 2, "4": 5, "6": 3}),
        check_row("degeneracy_class_sum", sum(hard["degeneracy_spectrum"].values()), 21),
        check_row(
            "degeneracy_codon_sum",
            sum(int(size) * count for size, count in hard["degeneracy_spectrum"].items()),
            64,
        ),
        check_row("doublet_box_count", hard["doublet_box_count"], 16),
        check_row("doublet_box_sizes", sorted(len(box["codons"]) for box in boxes.values()), [4] * 16),
        check_row("box_decomp_pure_binary_tri", hard["box_decomp"], [8, 7, 1]),
        check_row("box_fragment_count_formula", hard["box_fragments"], 8 * 1 + 7 * 2 + 1 * 3),
        check_row("box_fragment_count", hard["box_fragments"], 25),
        check_row("tri_split_box", [prefix for prefix, kind in box_info["kind_by_box"].items() if kind == "tri_split"], ["UG"]),
        check_row("tri_split_outputs", sorted(boxes["UG"]["outputs"]), ["Cys", "Stop", "Trp"]),
        check_row("cross_box_merge_outputs", sorted(merge_info["spanning_outputs"]), ["Arg", "Leu", "Ser", "Stop"]),
        check_row("cross_box_merge_count", hard["cross_box_merges"], 4),
        check_row("fold_chain", hard["fold_chain"], [64, 16, 25, 21]),
        check_row("fragment_minus_merges", hard["box_fragments"] - hard["cross_box_merges"], 21),
        check_row("surplus_64_minus_21", surplus, 43),
        check_row("zeckendorf_surplus_terms", [(index, value) for index, value in z_terms], [(9, 34), (6, 8), (2, 1)]),
        check_row("ratio_pure_over_twofold", ratios["pure_fourfold_boxes_over_twofold_classes"]["reduced"], "8/9"),
        check_row("ratio_singletons_over_sextets", ratios["singletons_over_sextets"]["reduced"], "2/3"),
        check_row("ratio_threefold_surplus_over_twofold", ratios["threefold_surplus_over_twofold_classes"]["reduced"], "4/9"),
    ]

    honesty = {
        "hard_structure_facts": (
            "The degeneracy spectrum, 16=8+7+1 box decomposition, "
            "64->16->25->21 fold chain, and four cross-box merges are exact "
            "enumerations of NCBI standard genetic code table 1."
        ),
        "golden_fibonacci_status": (
            "The identity 21=F8 is exact but is a single-number observation. "
            "The Zeckendorf surplus decomposition is universal for positive "
            "integers, so it is presentational and non-forcing."
        ),
        "ratio_status": (
            "The ratios 8/9, 2/3, and 4/9 are ratios of small counts.  Any "
            "match to physical coefficients is a numerology risk unless an "
            "independent structural forcing argument is supplied."
        ),
        "certificate_scope": (
            "Certified only as an exact standard-code fold-structure certificate; "
            "not certified as golden-ratio forcing or as a physical derivation."
        ),
    }

    note = (
        "The standard genetic code is certified here as a 64->21 two-layer fold "
        "with bulk(8 pure box)/seam(7 split)/defect(1 tri-split) stratification "
        "and exact degeneracy spectrum; Zeckendorf and small-ratio observations "
        "are explicitly flagged non-forcing."
    )

    status = "certified" if all(row["ok"] for row in checks) else "needs_derivation"
    emit(
        status,
        fold_chain=hard["fold_chain"],
        box_decomp=hard["box_decomp"],
        degeneracy_spectrum=hard["degeneracy_spectrum"],
        ratios=ratios,
        zeckendorf_surplus=z_string,
        honesty=honesty,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

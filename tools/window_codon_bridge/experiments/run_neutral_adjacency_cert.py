#!/usr/bin/env python3
"""Standard-code Hamming-1 neutral-adjacency certificate.

The certificate is intentionally finite and narrow: enumerate NCBI standard
code table 1, count same-output Hamming-1 codon neighbors, and test a few
fixed biological edge-weighting views against the 27/22/9/6 physics-side
target without fitting parameters to that target.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import product
import json
import math
import sys
from typing import Callable


EXPERIMENT_ID = "neutral_adjacency_cert"
CLAIM_ID = "bridge.genetic_code.neutral_hamming_adjacency"
TARGET = [27, 22, 9, 6]
EXPECTED_HISTOGRAM = {0: 2, 1: 22, 2: 8, 3: 28, 4: 4}
EXPECTED_MERGED = [28, 22, 8, 6]

BASES = ("U", "C", "A", "G")
PURINES = {"A", "G"}
PYRIMIDINES = {"U", "C"}

CODON_TO_CLASS = {
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

WeightFn = Callable[[str, str, int], Fraction | None]


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def neighbors(codon: str) -> list[tuple[str, int, str, str]]:
    result = []
    for position, old_base in enumerate(codon):
        for new_base in BASES:
            if new_base == old_base:
                continue
            other = codon[:position] + new_base + codon[position + 1:]
            result.append((other, position, old_base, new_base))
    return result


def is_transition(old_base: str, new_base: str) -> bool:
    return (
        old_base in PURINES
        and new_base in PURINES
        or old_base in PYRIMIDINES
        and new_base in PYRIMIDINES
    )


def score_by_codon(weight_fn: WeightFn) -> dict[str, Fraction]:
    scores: dict[str, Fraction] = {}
    for codon in codon_order():
        score = Fraction(0, 1)
        codon_class = CODON_TO_CLASS[codon]
        for other, position, old_base, new_base in neighbors(codon):
            if CODON_TO_CLASS[other] != codon_class:
                continue
            weight = weight_fn(codon, other, position)
            if weight is not None:
                score += weight
        scores[codon] = score
    return scores


def fraction_key(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def histogram_from_scores(scores: dict[str, Fraction]) -> Counter[Fraction]:
    return Counter(scores.values())


def json_histogram(histogram: Counter[Fraction]) -> dict[str, int]:
    return {
        fraction_key(score): count
        for score, count in sorted(histogram.items(), key=lambda item: (item[0], item[1]))
    }


def ranked_profile(histogram: Counter[Fraction]) -> dict[str, object]:
    ranked = sorted(histogram.items(), key=lambda item: (-item[1], item[0]))
    top = ranked[:3]
    remainder = ranked[3:]
    vector = [count for _score, count in top] + [sum(count for _score, count in remainder)]
    while len(vector) < 4:
        vector.append(0)
    return {
        "method": "frequency_rank_top3_then_merge_rest",
        "vector": vector,
        "top_classes": [
            {"score": fraction_key(score), "count": count}
            for score, count in top
        ],
        "merged_rest": [
            {"score": fraction_key(score), "count": count}
            for score, count in remainder
        ],
    }


def distance(vector: list[int], target: list[int]) -> dict[str, float | int]:
    deltas = [observed - expected for observed, expected in zip(vector, target)]
    return {
        "l1": sum(abs(delta) for delta in deltas),
        "l2": math.sqrt(sum(delta * delta for delta in deltas)),
        "linf": max(abs(delta) for delta in deltas),
        "deltas": deltas,
    }


def unweighted_merge(histogram: Counter[Fraction]) -> list[int]:
    return [
        histogram[Fraction(3, 1)],
        histogram[Fraction(1, 1)],
        histogram[Fraction(2, 1)],
        histogram[Fraction(0, 1)] + histogram[Fraction(4, 1)],
    ]


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def evaluate_weighting(description: str, weight_fn: WeightFn, no_target_fit: bool = True) -> dict[str, object]:
    scores = score_by_codon(weight_fn)
    histogram = histogram_from_scores(scores)
    profile = ranked_profile(histogram)
    vector = profile["vector"]
    assert isinstance(vector, list)
    dist = distance(vector, TARGET)
    return {
        "status": "certified" if vector == TARGET else "not_certified",
        "description": description,
        "no_target_fit": no_target_fit,
        "score_histogram": json_histogram(histogram),
        "merged_profile": profile,
        "distance_to_27_22_9_6": dist,
        "per_codon_scores": {
            codon: fraction_key(score)
            for codon, score in sorted(scores.items())
        },
    }


def unweighted(_codon: str, _other: str, _position: int) -> Fraction:
    return Fraction(1, 1)


def transition_transversion_2_to_1(codon: str, other: str, position: int) -> Fraction:
    return Fraction(2, 1) if is_transition(codon[position], other[position]) else Fraction(1, 1)


def wobble_third_half(_codon: str, _other: str, position: int) -> Fraction:
    return Fraction(1, 2) if position == 2 else Fraction(1, 1)


def wobble_third_excluded(_codon: str, _other: str, position: int) -> Fraction:
    return Fraction(0, 1) if position == 2 else Fraction(1, 1)


def sense_only_no_stop_edges(codon: str, other: str, _position: int) -> Fraction | None:
    if CODON_TO_CLASS[codon] == "Stop" or CODON_TO_CLASS[other] == "Stop":
        return None
    return Fraction(1, 1)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else 3)


def main() -> None:
    codons = codon_order()
    labels = [CODON_TO_CLASS[codon] for codon in codons]
    base_scores = score_by_codon(unweighted)
    base_histogram = histogram_from_scores(base_scores)
    integer_histogram = {
        int(score): count
        for score, count in base_histogram.items()
        if score.denominator == 1
    }
    merged = unweighted_merge(base_histogram)
    base_profile = ranked_profile(base_histogram)

    checks = [
        check_row("standard_code_codon_count", len(codons), 64),
        check_row("standard_code_output_class_count", len(set(labels)), 21),
        check_row(
            "standard_code_degeneracy_spectrum",
            dict(sorted(Counter(Counter(labels).values()).items())),
            {1: 2, 2: 9, 3: 2, 4: 5, 6: 3},
        ),
        check_row(
            "hamming1_neighbor_count_per_codon",
            {codon: len(neighbors(codon)) for codon in codons},
            {codon: 9 for codon in codons},
        ),
        check_row("neutral_neighbor_histogram", dict(sorted(integer_histogram.items())), EXPECTED_HISTOGRAM),
        check_row("merged_28_22_8_6", merged, EXPECTED_MERGED),
        check_row("frequency_ranked_unweighted_profile", base_profile["vector"], EXPECTED_MERGED),
        check_row("physics_target_not_equal_unweighted", merged == TARGET, False),
    ]

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            histogram=dict(sorted(integer_histogram.items())),
            merged_28_22_8_6=merged,
            physics_target=TARGET,
            weightings={},
            best_weighting=None,
            checks=checks,
            note="Self-check failed; no neutral-adjacency certificate emitted.",
        )

    weightings: dict[str, object] = {
        "unweighted_baseline": {
            "status": "certified",
            "description": "Plain Hamming-1 same-output neighbor count; Stop is one output class.",
            "score_histogram": json_histogram(base_histogram),
            "merged_profile": base_profile,
            "distance_to_27_22_9_6": distance(merged, TARGET),
            "per_codon_scores": {
                codon: fraction_key(score)
                for codon, score in sorted(base_scores.items())
            },
        },
        "transition_transversion_2_to_1": evaluate_weighting(
            "Transition mutations have weight 2 and transversions weight 1; this is a fixed Ti/Tv contrast, not fitted to 27/22/9/6.",
            transition_transversion_2_to_1,
        ),
        "wobble_third_half": evaluate_weighting(
            "Third-position mutations have weight 1/2 and first/second-position mutations weight 1; fixed wobble downweight, not fitted.",
            wobble_third_half,
        ),
        "wobble_third_excluded": evaluate_weighting(
            "Third-position mutations have weight 0 and first/second-position mutations weight 1; extreme wobble-edge diagnostic, not fitted.",
            wobble_third_excluded,
        ),
        "sense_only_no_stop_edges": evaluate_weighting(
            "Edges incident to Stop are excluded; sense codon edges retain weight 1.",
            sense_only_no_stop_edges,
        ),
        "trna_anticodon_availability": {
            "status": "needs_external",
            "description": "A real tRNA availability weighting requires organism-specific tRNA copy number, tAI, or anticodon abundance data.",
            "score_histogram": None,
            "merged_profile": None,
            "distance_to_27_22_9_6": None,
            "no_target_fit": None,
        },
    }

    evaluated = {
        name: result
        for name, result in weightings.items()
        if name != "unweighted_baseline"
        and isinstance(result, dict)
        and result.get("distance_to_27_22_9_6") is not None
    }
    best_name, best_result = min(
        evaluated.items(),
        key=lambda item: (
            item[1]["distance_to_27_22_9_6"]["l1"],  # type: ignore[index]
            item[0],
        ),
    )
    natural_exact = [
        name
        for name, result in evaluated.items()
        if result.get("status") == "certified"
    ]
    best_weighting = {
        "name": best_name,
        "status": best_result["status"],
        "merged_profile": best_result["merged_profile"],
        "distance_to_27_22_9_6": best_result["distance_to_27_22_9_6"],
    }

    if natural_exact:
        physics_note = "At least one fixed natural weighting exactly gives 27/22/9/6."
    else:
        physics_note = (
            "No fixed natural weighting tested here turns the exact 28/22/8/6 "
            "neutral-adjacency profile into 27/22/9/6. The unweighted fact is "
            "certified; the physics-side 27/22/9/6 identification is not certified "
            "by these biological weightings."
        )

    emit(
        "certified",
        histogram=dict(sorted(integer_histogram.items())),
        merged_28_22_8_6=merged,
        physics_target=TARGET,
        weightings=weightings,
        best_weighting=best_weighting,
        checks=checks,
        note=physics_note,
    )


if __name__ == "__main__":
    main()

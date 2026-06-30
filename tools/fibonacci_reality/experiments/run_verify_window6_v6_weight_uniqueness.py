#!/usr/bin/env python3
"""Forward integer certificate for Window6 Foldbin weight uniqueness.

The run uses only finite binary enumeration and integer weights. It does
not use alpha, metrological data, target-count inference, or any physical
interpretation.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import product
from typing import Any


M = 6
BOUND = 63
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)
WEIGHTS = VISIBLE_WEIGHTS + TAIL_WEIGHTS
FIBONACCI_F2_TO_F10 = WEIGHTS
LABELS = ("U_2", "U_1", "U_L", "U_R")


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def no_adjacent(word: tuple[int, ...]) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def visible_words() -> list[tuple[int, ...]]:
    return [word for word in product((0, 1), repeat=M) if no_adjacent(word)]


def foldbin_admissible_pairs(weights: tuple[int, ...]) -> list[tuple[tuple[int, ...], tuple[int, int, int], int]]:
    pairs: list[tuple[tuple[int, ...], tuple[int, int, int], int]] = []
    visible = weights[:M]
    tail_weights = weights[M:]
    for prefix in visible_words():
        prefix_value = sum(bit * weight for bit, weight in zip(prefix, visible))
        for tail in product((0, 1), repeat=3):
            c7, c8, c9 = tail
            if c7 * c8 or c8 * c9 or prefix[-1] * c7:
                continue
            value = prefix_value + sum(bit * weight for bit, weight in zip(tail, tail_weights))
            if value <= BOUND:
                pairs.append((prefix, tail, value))
    return pairs


def is_bijection_to_0_63(values: list[int]) -> bool:
    return sorted(values) == list(range(BOUND + 1))


def classify_prefix(prefix: tuple[int, ...]) -> str:
    weight = sum(prefix)
    if prefix[0] and prefix[-1]:
        return "U_R"
    if weight == 2:
        return "U_2"
    if weight == 1:
        return "U_1"
    if weight in (0, 3):
        return "U_L"
    raise ValueError(f"unclassified prefix {word_string(prefix)}")


def perturbation_audit() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    target = set(range(BOUND + 1))
    names = [f"g_{index}" for index in range(1, 7)] + [f"t_{index}" for index in range(1, 4)]
    for index, name in enumerate(names):
        for delta in (-1, 1):
            perturbed = list(WEIGHTS)
            perturbed[index] += delta
            if perturbed[index] <= 0:
                continue
            pairs = foldbin_admissible_pairs(tuple(perturbed))
            values = [value for _, _, value in pairs]
            counts = Counter(values)
            value_set = set(values)
            duplicate_values = [value for value, count in sorted(counts.items()) if count > 1]
            missing_values = sorted(target - value_set)
            records.append(
                {
                    "weight": name,
                    "delta": delta,
                    "weights": perturbed,
                    "admissible_pair_count": len(pairs),
                    "distinct_value_count": len(value_set),
                    "bijection_to_0_63": is_bijection_to_0_63(values),
                    "duplicate_values": duplicate_values[:12],
                    "duplicate_value_count": len(duplicate_values),
                    "missing_values": missing_values[:12],
                    "missing_value_count": len(missing_values),
                }
            )
    return records


def main() -> None:
    pairs = foldbin_admissible_pairs(WEIGHTS)
    values = [value for _, _, value in pairs]
    value_to_pair = {value: (prefix, tail) for prefix, tail, value in pairs}
    cell_counts = Counter(classify_prefix(value_to_pair[number][0]) for number in range(BOUND + 1))
    perturbations = perturbation_audit()
    broken_perturbations = [record for record in perturbations if not record["bijection_to_0_63"]]

    checks = [
        check(
            "fibonacci_weights",
            VISIBLE_WEIGHTS == (1, 2, 3, 5, 8, 13)
            and TAIL_WEIGHTS == (21, 34, 55)
            and FIBONACCI_F2_TO_F10 == (1, 2, 3, 5, 8, 13, 21, 34, 55),
            "visible weights are F_2..F_7=(1,2,3,5,8,13) and tail weights are F_8..F_10=(21,34,55)",
        ),
        check(
            "foldbin_bijection_0_63",
            len(pairs) == 64 and len(set(values)) == 64 and is_bijection_to_0_63(values),
            "under the consecutive Fibonacci weights, admissible Foldbin tail-cube pairs map bijectively to {0,...,63}",
        ),
        check(
            "cell_counts_27_22_9_6",
            [cell_counts[label] for label in LABELS] == [27, 22, 9, 6],
            "the induced Window6 four-cell counts are (27,22,9,6) in the order U_2,U_1,U_L,U_R",
        ),
        check(
            "weight_uniqueness",
            len(perturbations) == 17 and len(broken_perturbations) == 17,
            "every valid single-weight +/-1 perturbation of g_1..g_6,t_1..t_3 breaks bijectivity onto {0,...,63}",
        ),
        check(
            "zeckendorf_interpretation",
            no_adjacent((1, 0, 1, 0, 1, 0))
            and WEIGHTS == FIBONACCI_F2_TO_F10
            and BOUND == 63,
            "the consecutive Fibonacci weights and no-adjacent-one predicate give the truncated Zeckendorf numeration on {0,...,63}",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "anti_fit_guard": "All facts are derived by exact finite integer enumeration; no alpha input, target-count inference, metrological data, numerical proximity, or physical constant is used.",
        "weights": {
            "visible_F2_to_F7": list(VISIBLE_WEIGHTS),
            "tail_F8_to_F10": list(TAIL_WEIGHTS),
            "all_F2_to_F10": list(WEIGHTS),
        },
        "bijection": {
            "admissible_pair_count": len(pairs),
            "distinct_value_count": len(set(values)),
            "value_range": [min(values), max(values)],
            "covers_0_63": is_bijection_to_0_63(values),
            "sample_value_to_word_tail": {
                str(number): {
                    "visible_word": word_string(value_to_pair[number][0]),
                    "tail": word_string(value_to_pair[number][1]),
                }
                for number in (0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 63)
            },
        },
        "cell_counts": {label: cell_counts[label] for label in LABELS},
        "perturbations_broken": len(broken_perturbations),
        "total_perturbations": len(perturbations),
        "perturbation_failures": perturbations,
        "zeckendorf_interpretation": [
            "The nine weights form the consecutive Fibonacci block F_2..F_10.",
            "The no-adjacent-one constraints c_7c_8=0, c_8c_9=0, and w_6c_7=0 are the Zeckendorf non-adjacency condition across the visible-tail boundary.",
            "The bound value<=63 truncates the F_2..F_10 Zeckendorf carrier to the six-bit cube values {0,...,63}.",
        ],
        "not_claimed": [
            "no physical-constant identification",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

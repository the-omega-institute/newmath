#!/usr/bin/env python3
"""Forward integer certificate for the Window6 Zeckendorf cylinder quotient.

The run uses only finite binary enumeration and integer Fibonacci weights.
It does not use alpha, metrological data, or any physical interpretation.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import product
from typing import Any


M = 6
N = 9
BOUND = 63
WEIGHTS = (1, 2, 3, 5, 8, 13, 21, 34, 55)
LABELS = ("U_2", "U_1", "U_L", "U_R")


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def value(word: tuple[int, ...]) -> int:
    return sum(bit * WEIGHTS[index] for index, bit in enumerate(word))


def no_adjacent(word: tuple[int, ...]) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def cyclic_no_adjacent(word: tuple[int, ...]) -> bool:
    return no_adjacent(word) and not (word[0] and word[-1])


def z9() -> list[tuple[int, ...]]:
    return [
        word
        for word in product((0, 1), repeat=N)
        if no_adjacent(word) and value(word) <= BOUND
    ]


def foldbin_tail_set(prefix: tuple[int, ...]) -> set[tuple[int, int, int]]:
    tails: set[tuple[int, int, int]] = set()
    if not no_adjacent(prefix):
        return tails
    prefix_value = value(prefix + (0, 0, 0))
    for c7, c8, c9 in product((0, 1), repeat=3):
        if c7 * c8 or c8 * c9 or prefix[-1] * c7:
            continue
        if prefix_value + 21 * c7 + 34 * c8 + 55 * c9 <= BOUND:
            tails.add((c7, c8, c9))
    return tails


def zeckendorf_cylinder_tail_set(prefix: tuple[int, ...]) -> set[tuple[int, int, int]]:
    tails: set[tuple[int, int, int]] = set()
    for tail in product((0, 1), repeat=3):
        word = prefix + tail
        if no_adjacent(word) and value(word) <= BOUND:
            tails.add(tail)
    return tails


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


def main() -> None:
    carrier = z9()
    values = [value(word) for word in carrier]
    value_to_word = {value(word): word for word in carrier}
    x6 = [word for word in product((0, 1), repeat=M) if no_adjacent(word)]
    cylinder_equalities = {
        word_string(prefix): sorted(word_string(tail) for tail in foldbin_tail_set(prefix))
        for prefix in x6
        if foldbin_tail_set(prefix) == zeckendorf_cylinder_tail_set(prefix)
    }
    mismatched_prefixes = [
        word_string(prefix)
        for prefix in x6
        if foldbin_tail_set(prefix) != zeckendorf_cylinder_tail_set(prefix)
    ]

    cell_counts = Counter(classify_prefix(value_to_word[number][:M]) for number in range(BOUND + 1))
    cyclic_words = [word for word in product((0, 1), repeat=M) if cyclic_no_adjacent(word)]
    cyclic_weight_distribution = Counter(sum(word) for word in cyclic_words)

    checks = [
        check(
            "zeckendorf_bijection",
            len(carrier) == 64 and sorted(values) == list(range(64)) and len(value_to_word) == 64,
            "Z_9(63) has 64 no-adjacent words and the Fibonacci-weight value map is a bijection onto {0,...,63}",
        ),
        check(
            "foldbin_equals_zeckendorf_cylinder",
            len(cylinder_equalities) == len(x6) and not mismatched_prefixes,
            "for every admissible visible six-prefix, the Foldbin tail-cube fiber equals the Zeckendorf cylinder tail set",
        ),
        check(
            "cell_counts_forced",
            [cell_counts[label] for label in LABELS] == [27, 22, 9, 6],
            "unique Zeckendorf representation plus the prefix predicates induces Window6 cell counts (27,22,9,6)",
        ),
        check(
            "cyclic_lucas_L6",
            len(cyclic_words) == 18 and dict(sorted(cyclic_weight_distribution.items())) == {0: 1, 1: 6, 2: 9, 3: 2},
            "length-six cyclic no-adjacent words have count 18=L_6 and weight distribution {0:1,1:6,2:9,3:2}",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "anti_fit_guard": "All facts are derived by finite integer enumeration from Zeckendorf weights F_2..F_10; no alpha input, target-count inference, or physical constant is used.",
        "weights_F2_to_F10": list(WEIGHTS),
        "Z9_63_size": len(carrier),
        "value_range": [min(values), max(values)],
        "bijection_to_0_63": sorted(values) == list(range(64)),
        "visible_prefix_count": len(x6),
        "foldbin_cylinder_equalities": cylinder_equalities,
        "mismatched_prefixes": mismatched_prefixes,
        "cell_counts": {label: cell_counts[label] for label in LABELS},
        "cyclic_L6_count": len(cyclic_words),
        "cyclic_weight_distribution": {str(key): cyclic_weight_distribution[key] for key in sorted(cyclic_weight_distribution)},
        "definitions": [
            "Z_9(63)={b in {0,1}^9: b has no adjacent 1s and sum_i b_i F_{i+1}<=63}, with weights F_2..F_10.",
            "The Zeckendorf value of b is sum_i b_i F_{i+1}.",
            "For a visible prefix w, the Foldbin tail-cube constraints are c_7c_8=0, c_8c_9=0, w_6c_7=0, and V_6(w)+21c_7+34c_8+55c_9<=63.",
            "U_2 is cyclic prefix weight 2; U_1 is cyclic prefix weight 1; U_L is cyclic prefix weight 0 or 3; U_R is boundary prefix w_1=w_6=1.",
        ],
        "not_claimed": [
            "physical alpha identification",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

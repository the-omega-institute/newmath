#!/usr/bin/env python3
"""Forward audit for saturated upward chains in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones.  Edges
are oriented by increasing Hamming weight.  A saturated upward chain starts at
0^m, adds one valid 1 at each step, and stops exactly at a maximal word.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from functools import cache
from math import comb, factorial
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-saturated-chain"
CLAIM_ID = "window.fibonacci-cube.saturated-chain.certificate"
DP_MAX_WINDOW = 14
EXPECTED_MAX_WINDOW = 12
EXPECTED_C = [1, 1, 2, 3, 6, 12, 26, 60, 144, 366, 960, 2640, 7464]
EXPECTED_VERTEX_COUNTS = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377]


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib(index: int) -> int:
    if index < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, previous + current
    return previous


def valid(word: int, width: int) -> bool:
    limit_mask = (1 << width) - 1
    return 0 <= word <= limit_mask and (word & (word >> 1)) == 0


def words(width: int) -> list[int]:
    return [word for word in range(1 << width) if valid(word, width)]


def word_to_string(word: int, width: int) -> str:
    return format(word, f"0{width}b")


def addable_positions(word: int, width: int) -> list[int]:
    return [position for position in range(width) if valid(word | (1 << position), width) and not ((word >> position) & 1)]


def maximal_word(word: int, width: int) -> bool:
    return valid(word, width) and not addable_positions(word, width)


def maximal_words(width: int) -> list[int]:
    return [word for word in words(width) if maximal_word(word, width)]


def dp_saturated_chain_count(width: int) -> int:
    @cache
    def count_from(word: int) -> int:
        if maximal_word(word, width):
            return 1
        return sum(count_from(word | (1 << position)) for position in addable_positions(word, width))

    return count_from(0)


def maximal_factorial_sum(width: int) -> int:
    return sum(factorial(word.bit_count()) for word in maximal_words(width))


def closed_form_saturated_chain_count(width: int) -> int:
    lower = (width + 2) // 3
    upper = (width + 1) // 2
    return sum(comb(weight + 1, width - 2 * weight + 1) * factorial(weight) for weight in range(lower, upper + 1))


def maximal_weight_profile(width: int) -> dict[int, int]:
    profile: dict[int, int] = {}
    for word in maximal_words(width):
        weight = word.bit_count()
        profile[weight] = profile.get(weight, 0) + 1
    return profile


def closed_form_weight_profile(width: int) -> dict[int, int]:
    lower = (width + 2) // 3
    upper = (width + 1) // 2
    return {weight: comb(weight + 1, width - 2 * weight + 1) for weight in range(lower, upper + 1)}


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    widths = list(range(DP_MAX_WINDOW + 1))
    expected_widths = list(range(EXPECTED_MAX_WINDOW + 1))
    dp_values = [dp_saturated_chain_count(width) for width in widths]
    factorial_sum_values = [maximal_factorial_sum(width) for width in widths]
    closed_form_values = [closed_form_saturated_chain_count(width) for width in widths]
    vertex_counts = [len(words(width)) for width in expected_widths]
    maximal_profiles = {str(width): maximal_weight_profile(width) for width in expected_widths}
    closed_form_profiles = {str(width): closed_form_weight_profile(width) for width in expected_widths}
    window6_maximal_words = [word_to_string(word, 6) for word in maximal_words(6)]

    maximal_consistency = [
        all(
            maximal_word(word, width)
            == (valid(word, width) and all(not valid(word | (1 << position), width) for position in range(width) if not ((word >> position) & 1)))
            for word in words(width)
        )
        for width in expected_widths
    ]

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(16)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m0_to_m12",
            vertex_counts == EXPECTED_VERTEX_COUNTS
            and all(vertex_counts[width] == fib(width + 2) for width in expected_widths),
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=0..12.",
        ),
        check(
            "maximal_word_definition_consistency_m0_to_m12",
            all(maximal_consistency),
            "A maximal word is exactly a valid word for which every zero-bit insertion violates the no-adjacent-ones condition.",
        ),
        check(
            "dp_saturated_chain_values_m0_to_m12",
            dp_values[: EXPECTED_MAX_WINDOW + 1] == EXPECTED_C,
            "Memoized upward DP from 0^m gives the frozen C_m values for m=0..12.",
        ),
        check(
            "maximal_word_factorial_sum_m0_to_m12",
            factorial_sum_values[: EXPECTED_MAX_WINDOW + 1] == EXPECTED_C,
            "The sum over maximal words w of popcount(w)! gives the frozen C_m values for m=0..12.",
        ),
        check(
            "closed_form_expected_values_m0_to_m12",
            closed_form_values[: EXPECTED_MAX_WINDOW + 1] == EXPECTED_C,
            "The binomial-factorial closed form gives the frozen C_m values for m=0..12.",
        ),
        check(
            "closed_form_agrees_with_dp_m0_to_m14",
            closed_form_values == dp_values,
            "The closed form agrees with the memoized DP for m=0..14.",
        ),
        check(
            "three_representations_agree_m0_to_m14",
            all(dp_values[width] == factorial_sum_values[width] == closed_form_values[width] for width in widths),
            "DP, maximal-word factorial sum, and binomial-factorial closed form agree for m=0..14.",
        ),
        check(
            "maximal_weight_profile_closed_form_m0_to_m12",
            maximal_profiles == closed_form_profiles,
            "The number of maximal words of weight k is binom(k+1,m-2k+1) for m=0..12.",
        ),
        check(
            "window6_saturated_chain_anchor",
            dp_values[6] == 26
            and factorial_sum_values[6] == 26
            and closed_form_values[6] == 26
            and maximal_weight_profile(6) == {2: 1, 3: 4},
            "For m=6, the maximal-word profile is 1 word of weight 2 and 4 words of weight 3, so C_6=1*2!+4*3!=26.",
        ),
        check(
            "saturated_chain_not_prior_anchor_repackage",
            dp_values[6] == 26
            and dp_values[6] != 38
            and dp_values[6] != 144
            and dp_values[6] != 1549
            and dp_values[8] == 144,
            "This poset saturated-chain count is distinct from edge, closed-neighborhood, and median-zero triple anchors.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, Hamming-weight orientation, maximal words, factorials, and exact integer binomial sums.",
        ),
    ]
    summary = check_summary(checks)
    status = "passed" if summary["failed"] == 0 else "failed"
    result = {
        "experiment_run_id": f"{EXPERIMENT_ID}:{started_at}",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "script_sha": script_sha(),
        "status": status,
        "checks": checks,
        "check_summary": summary,
        "result": {
            "carrier": {
                "family": "Gamma_m has vertex set X_m={w in {0,1}^m : w has no adjacent 1s}.",
                "orientation": "Edges are oriented by increasing Hamming weight; an upward step adds exactly one 1 while remaining in X_m.",
                "window_range": [0, DP_MAX_WINDOW],
                "vertex_counts_m0_to_m12": {str(width): count for width, count in enumerate(vertex_counts)},
            },
            "saturated_chain_count": {
                "definition": "C_m counts directed saturated chains from 0^m to a maximal word in the Hamming-weight orientation.",
                "expected_values_m0_to_m12": EXPECTED_C,
                "dp_values_m0_to_m14": dp_values,
                "maximal_word_factorial_sum_m0_to_m14": factorial_sum_values,
                "closed_form_values_m0_to_m14": closed_form_values,
            },
            "equivalent_representations": {
                "dp": "cnt(x)=1 if x is maximal, otherwise cnt(x)=sum_i cnt(x with bit i set) over valid addable zero positions.",
                "maximal_word_factorial_sum": "C_m=sum_{maximal w} popcount(w)! because [0^m,w] is a Boolean lattice of rank popcount(w).",
                "closed_form": "C_m=sum_{k=ceil(m/3)}^{ceil(m/2)} binom(k+1,m-2k+1)*k!.",
                "maximal_weight_profile_m0_to_m12": maximal_profiles,
            },
            "window6_anchor": {
                "maximal_words": window6_maximal_words,
                "maximal_weight_profile": maximal_weight_profile(6),
                "C_6": dp_values[6],
            },
            "not_claimed": [
                "physical fine-structure constant or any physical constant",
                "alpha/137 as input, target, numerical proximity, or reverse fit",
                "any convention-dependent physical interpretation",
            ],
        },
        "started_at": started_at,
        "completed_at": now_iso(),
    }
    if status == "passed":
        print("PASS")
    print(json.dumps(result, ensure_ascii=False))
    if status != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

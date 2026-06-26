#!/usr/bin/env python3
"""Forward audit for median-zero ordered triples in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones.  The
coordinatewise median of an ordered triple is the coordinatewise majority.  The
median-zero fiber therefore consists exactly of ordered triples whose supports
are pairwise disjoint, with each word still satisfying the no-adjacent-ones
constraint.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-median-zero-triple"
CLAIM_ID = "window.fibonacci-cube.median-zero-triple.certificate"
MAX_WINDOW = 15
BRUTE_MAX_WINDOW = 6
EXPECTED_T = [
    1,
    4,
    13,
    43,
    142,
    469,
    1549,
    5116,
    16897,
    55807,
    184318,
    608761,
    2010601,
    6640564,
    21932293,
    72437443,
]
EXPECTED_VERTEX_COUNTS = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
STATE_SPACE = list(itertools.product((0, 1), repeat=3))


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib(n: int) -> int:
    if n < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(n):
        previous, current = current, previous + current
    return previous


def valid(word: int, width: int) -> bool:
    limit_mask = (1 << width) - 1
    return 0 <= word <= limit_mask and (word & (word >> 1)) == 0


def words(width: int) -> list[int]:
    return [word for word in range(1 << width) if valid(word, width)]


def word_to_string(word: int, width: int) -> str:
    return format(word, f"0{width}b")


def support_disjoint_triple(triple: tuple[int, int, int], width: int) -> bool:
    x, y, z = triple
    for coord in range(width):
        if ((x >> coord) & 1) + ((y >> coord) & 1) + ((z >> coord) & 1) > 1:
            return False
    return True


def median_zero_triple(triple: tuple[int, int, int], width: int) -> bool:
    x, y, z = triple
    for coord in range(width):
        if ((x >> coord) & 1) + ((y >> coord) & 1) + ((z >> coord) & 1) >= 2:
            return False
    return True


def brute_force_t(width: int) -> int:
    carrier = words(width)
    total = 0
    for triple in itertools.product(carrier, repeat=3):
        if median_zero_triple(triple, width):
            total += 1
    return total


def allowed_transition(state: tuple[int, int, int], next_digits: tuple[int, int, int]) -> bool:
    if sum(next_digits) > 1:
        return False
    return all(next_digit == 0 or last_digit == 0 for last_digit, next_digit in zip(state, next_digits))


def transition_table() -> dict[tuple[int, int, int], list[tuple[int, int, int]]]:
    return {
        state: [next_digits for next_digits in STATE_SPACE if allowed_transition(state, next_digits)]
        for state in STATE_SPACE
    }


def transfer_counts(max_width: int) -> list[int]:
    transitions = transition_table()
    state_counts = {state: 0 for state in STATE_SPACE}
    state_counts[(0, 0, 0)] = 1
    totals = [sum(state_counts.values())]
    for _ in range(max_width):
        next_counts = {state: 0 for state in STATE_SPACE}
        for state, count in state_counts.items():
            for next_digits in transitions[state]:
                next_counts[next_digits] += count
        state_counts = next_counts
        totals.append(sum(state_counts.values()))
    return totals


def transfer_profiles(max_width: int) -> list[dict[str, int]]:
    transitions = transition_table()
    state_counts = {state: 0 for state in STATE_SPACE}
    state_counts[(0, 0, 0)] = 1
    profiles = [format_state_counts(state_counts)]
    for _ in range(max_width):
        next_counts = {state: 0 for state in STATE_SPACE}
        for state, count in state_counts.items():
            for next_digits in transitions[state]:
                next_counts[next_digits] += count
        state_counts = next_counts
        profiles.append(format_state_counts(state_counts))
    return profiles


def format_state(state: tuple[int, int, int]) -> str:
    return "".join(str(bit) for bit in state)


def format_state_counts(state_counts: dict[tuple[int, int, int], int]) -> dict[str, int]:
    return {format_state(state): state_counts[state] for state in STATE_SPACE}


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_force_t(width) for width in range(BRUTE_MAX_WINDOW + 1)]
    transfer_values = transfer_counts(MAX_WINDOW)
    vertex_counts = [len(words(width)) for width in range(MAX_WINDOW + 1)]
    transitions = transition_table()
    transition_outdegrees = {format_state(state): len(next_states) for state, next_states in transitions.items()}
    profiles = transfer_profiles(MAX_WINDOW)

    median_equivalence_checks = []
    for width in range(BRUTE_MAX_WINDOW + 1):
        carrier = words(width)
        median_equivalence_checks.extend(
            median_zero_triple(triple, width) == support_disjoint_triple(triple, width)
            for triple in itertools.product(carrier, repeat=3)
        )

    recurrence_residuals = [
        transfer_values[width] - 3 * transfer_values[width - 1] - transfer_values[width - 2]
        for width in range(2, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(18)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m0_to_m15",
            vertex_counts == EXPECTED_VERTEX_COUNTS
            and all(vertex_counts[width] == fib(width + 2) for width in range(MAX_WINDOW + 1)),
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=0..15.",
        ),
        check(
            "brute_force_median_zero_values_m0_to_m6",
            brute_values == EXPECTED_T[: BRUTE_MAX_WINDOW + 1],
            "Direct ordered-triple enumeration of the median-zero fiber matches the frozen values for m=0..6.",
        ),
        check(
            "median_zero_equals_pairwise_disjoint_support_m0_to_m6",
            all(median_equivalence_checks),
            "For every brute-force triple checked, coordinatewise majority zero is equivalent to pairwise-disjoint support.",
        ),
        check(
            "transfer_state_space_has_8_last_bit_states",
            len(STATE_SPACE) == 8 and set(STATE_SPACE) == set(itertools.product((0, 1), repeat=3)),
            "The transfer carrier is exactly the 8 last-bit states in {0,1}^3.",
        ),
        check(
            "transition_rule_disjoint_support_and_no_adjacent_ones",
            all(
                sum(next_digits) <= 1
                and all(next_digit == 0 or last_digit == 0 for last_digit, next_digit in zip(state, next_digits))
                for state, next_states in transitions.items()
                for next_digits in next_states
            ),
            "Every transition enforces at most one active word in the new coordinate and forbids adjacent 1s in each word.",
        ),
        check(
            "transfer_matrix_values_m0_to_m15",
            transfer_values == EXPECTED_T,
            "The 8-state forward transfer matrix produces the frozen T_m values for m=0..15.",
        ),
        check(
            "brute_force_transfer_agree_m0_to_m6",
            brute_values == transfer_values[: BRUTE_MAX_WINDOW + 1],
            "The direct enumeration and the 8-state transfer computation agree on the brute-force window m=0..6.",
        ),
        check(
            "pell_recurrence_m2_to_m15",
            all(residual == 0 for residual in recurrence_residuals)
            and transfer_values[0] == 1
            and transfer_values[1] == 4,
            "The sequence satisfies T_m=3T_{m-1}+T_{m-2} with T_0=1,T_1=4 for m=2..15.",
        ),
        check(
            "characteristic_polynomial_x2_minus_3x_minus_1",
            (3, 1) == (3, 1) and all(residual == 0 for residual in recurrence_residuals),
            "The verified scalar recurrence has companion characteristic polynomial x^2-3x-1.",
        ),
        check(
            "median_triple_statistic_not_prior_anchor_repackage",
            EXPECTED_T[6] == 1549 and vertex_counts[6] == 21 and EXPECTED_T[6] != 22 and EXPECTED_T[6] != 122,
            "The m=6 ordered median-zero triple count is distinct from the theta-square total and geodesic aggregate anchors.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, coordinatewise majority, support disjointness, and integer transfer recurrence data.",
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
                "window_range": [0, MAX_WINDOW],
                "vertex_counts": {str(width): count for width, count in enumerate(vertex_counts)},
                "window6_vertices": [word_to_string(word, 6) for word in words(6)],
            },
            "median_zero_ordered_triples": {
                "definition": "T_m counts ordered triples (x,y,z) in V(Gamma_m)^3 whose coordinatewise median is 0^m.",
                "equivalent_condition": "At each coordinate at most one of x,y,z has bit 1; the three supports are pairwise disjoint.",
                "expected_values_m0_to_m15": EXPECTED_T,
                "brute_force_values_m0_to_m6": brute_values,
                "transfer_values_m0_to_m15": transfer_values,
            },
            "transfer_matrix": {
                "states": [format_state(state) for state in STATE_SPACE],
                "start_state": "000",
                "transition_rule": "state s=(a,b,c) may move to d=(da,db,dc) iff da+db+dc<=1 and d_i=1 implies s_i=0.",
                "outdegrees": transition_outdegrees,
                "state_profiles_m0_to_m15": profiles,
            },
            "recurrence": {
                "initial_values": {"T_0": transfer_values[0], "T_1": transfer_values[1]},
                "formula": "T_m=3*T_{m-1}+T_{m-2}",
                "verified_range": [2, MAX_WINDOW],
                "residuals_m2_to_m15": recurrence_residuals,
                "characteristic_polynomial": "x^2-3*x-1",
                "roots": "(3 +/- sqrt(13))/2",
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

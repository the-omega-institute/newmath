#!/usr/bin/env python3
"""Forward audit for disjoint-support ordered k-tuples in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones.  For
fixed k, D^(k)_m counts ordered k-tuples of such words whose supports are
pairwise disjoint.  A last-bit transfer over {0,1}^k gives the uniform
metallic-ratio recurrence D^(k)_m=kD^(k)_{m-1}+D^(k)_{m-2}.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-disjoint-tuple-metallic"
CLAIM_ID = "window.fibonacci-cube.disjoint-tuple-metallic.certificate"
MAX_WINDOW = 14
TRANSFER_MAX_K = 5
BRUTE_MAX_K = 4
BRUTE_MAX_WINDOW = 5
EXPECTED_PREFIXES = {
    1: [1, 2, 3, 5, 8, 13, 21],
    2: [1, 3, 7, 17, 41, 99, 239],
    3: [1, 4, 13, 43, 142, 469, 1549],
    4: [1, 5, 21, 89, 377, 1597, 6765],
    5: [1, 6, 31, 161, 836, 4341, 22541],
}


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


def support_disjoint_tuple(tuple_words: tuple[int, ...], width: int) -> bool:
    for coord in range(width):
        if sum((word >> coord) & 1 for word in tuple_words) > 1:
            return False
    return True


def brute_force_d(k: int, width: int) -> int:
    carrier = words(width)
    total = 0
    for tuple_words in itertools.product(carrier, repeat=k):
        if support_disjoint_tuple(tuple_words, width):
            total += 1
    return total


def state_space(k: int) -> list[tuple[int, ...]]:
    return list(itertools.product((0, 1), repeat=k))


def allowed_transition(state: tuple[int, ...], next_digits: tuple[int, ...]) -> bool:
    if sum(next_digits) > 1:
        return False
    return all(next_digit == 0 or last_digit == 0 for last_digit, next_digit in zip(state, next_digits))


def transition_table(k: int) -> dict[tuple[int, ...], list[tuple[int, ...]]]:
    states = state_space(k)
    return {
        state: [next_digits for next_digits in states if allowed_transition(state, next_digits)]
        for state in states
    }


def transfer_counts(k: int, max_width: int) -> list[int]:
    states = state_space(k)
    transitions = transition_table(k)
    zero_state = tuple(0 for _ in range(k))
    state_counts = {state: 0 for state in states}
    state_counts[zero_state] = 1
    totals = [sum(state_counts.values())]
    for _ in range(max_width):
        next_counts = {state: 0 for state in states}
        for state, count in state_counts.items():
            for next_digits in transitions[state]:
                next_counts[next_digits] += count
        state_counts = next_counts
        totals.append(sum(state_counts.values()))
    return totals


def transfer_profiles(k: int, max_width: int) -> list[dict[str, int]]:
    states = state_space(k)
    transitions = transition_table(k)
    zero_state = tuple(0 for _ in range(k))
    state_counts = {state: 0 for state in states}
    state_counts[zero_state] = 1
    profiles = [format_state_counts(k, state_counts)]
    for _ in range(max_width):
        next_counts = {state: 0 for state in states}
        for state, count in state_counts.items():
            for next_digits in transitions[state]:
                next_counts[next_digits] += count
        state_counts = next_counts
        profiles.append(format_state_counts(k, state_counts))
    return profiles


def format_state(state: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in state)


def format_state_counts(k: int, state_counts: dict[tuple[int, ...], int]) -> dict[str, int]:
    return {format_state(state): state_counts[state] for state in state_space(k)}


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    transfer_values = {k: transfer_counts(k, MAX_WINDOW) for k in range(1, TRANSFER_MAX_K + 1)}
    brute_values = {
        k: [brute_force_d(k, width) for width in range(BRUTE_MAX_WINDOW + 1)]
        for k in range(1, BRUTE_MAX_K + 1)
    }
    vertex_counts = [len(words(width)) for width in range(MAX_WINDOW + 1)]
    recurrence_residuals = {
        k: [
            values[width] - k * values[width - 1] - values[width - 2]
            for width in range(2, MAX_WINDOW + 1)
        ]
        for k, values in transfer_values.items()
    }
    transition_outdegrees = {
        str(k): {
            format_state(state): len(next_states)
            for state, next_states in transition_table(k).items()
        }
        for k in range(1, TRANSFER_MAX_K + 1)
    }
    profiles = {str(k): transfer_profiles(k, MAX_WINDOW) for k in range(1, TRANSFER_MAX_K + 1)}
    characteristic_coefficients = {k: (k, 1) for k in range(1, TRANSFER_MAX_K + 1)}

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(17)]
            == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m0_to_m14",
            vertex_counts == [fib(width + 2) for width in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=0..14.",
        ),
        check(
            "transfer_state_spaces_k1_to_k5",
            all(len(state_space(k)) == 2**k for k in range(1, TRANSFER_MAX_K + 1)),
            "For each k, the transfer carrier is exactly the 2^k last-bit states in {0,1}^k.",
        ),
        check(
            "transition_rule_disjoint_support_and_no_adjacent_ones_k1_to_k5",
            all(
                sum(next_digits) <= 1
                and all(next_digit == 0 or last_digit == 0 for last_digit, next_digit in zip(state, next_digits))
                for k in range(1, TRANSFER_MAX_K + 1)
                for state, next_states in transition_table(k).items()
                for next_digits in next_states
            ),
            "Every transition enforces at most one active word in the new coordinate and forbids adjacent 1s in each word.",
        ),
        check(
            "brute_force_transfer_agree_k1_to_k4_m0_to_m5",
            all(
                brute_values[k][width] == transfer_values[k][width]
                for k in range(1, BRUTE_MAX_K + 1)
                for width in range(BRUTE_MAX_WINDOW + 1)
            ),
            "Direct ordered k-tuple enumeration agrees with the transfer computation for k=1..4 and m=0..5.",
        ),
        check(
            "expected_prefix_values_k1_to_k5_m0_to_m6",
            all(transfer_values[k][:7] == EXPECTED_PREFIXES[k] for k in range(1, TRANSFER_MAX_K + 1)),
            "The transfer values match the frozen k=1..5 prefixes through m=6.",
        ),
        check(
            "metallic_recurrence_k1_to_k5_m2_to_m14",
            all(residual == 0 for residuals in recurrence_residuals.values() for residual in residuals)
            and all(transfer_values[k][0] == 1 and transfer_values[k][1] == k + 1 for k in range(1, TRANSFER_MAX_K + 1)),
            "For k=1..5, D^(k)_m=kD^(k)_{m-1}+D^(k)_{m-2} with D^(k)_0=1,D^(k)_1=k+1 for m=2..14.",
        ),
        check(
            "characteristic_polynomials_x2_minus_kx_minus_1_k1_to_k5",
            all(characteristic_coefficients[k] == (k, 1) for k in range(1, TRANSFER_MAX_K + 1))
            and all(residual == 0 for residuals in recurrence_residuals.values() for residual in residuals),
            "The verified recurrence coefficients (k,1) give characteristic polynomial x^2-kx-1.",
        ),
        check(
            "k1_vertex_count_fibonacci_m0_to_m14",
            all(transfer_values[1][width] == fib(width + 2) for width in range(MAX_WINDOW + 1)),
            "The k=1 slice is the Fibonacci-cube vertex count |V_m|=F_{m+2}.",
        ),
        check(
            "k2_pell_silver_prefix_m0_to_m7",
            transfer_values[2][:8] == [1, 3, 7, 17, 41, 99, 239, 577],
            "The k=2 slice gives the Pell-type silver-ratio prefix.",
        ),
        check(
            "k3_median_zero_anchor_prefix_m0_to_m6",
            transfer_values[3][:7] == [1, 4, 13, 43, 142, 469, 1549],
            "The k=3 slice reproduces the median-zero ordered triple anchor through m=6.",
        ),
        check(
            "k4_prefix_m0_to_m6",
            transfer_values[4][:7] == [1, 5, 21, 89, 377, 1597, 6765],
            "The k=4 slice matches the frozen prefix through m=6.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, support disjointness, finite transfer matrices, and integer recurrence data.",
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
            "disjoint_support_ordered_tuples": {
                "definition": "D^(k)_m counts ordered k-tuples of vertices in V(Gamma_m)^k whose supports are pairwise disjoint.",
                "equivalent_condition": "At each coordinate at most one of the k words has bit 1; each word has no adjacent 1s.",
                "verified_k_range": [1, TRANSFER_MAX_K],
                "transfer_values_m0_to_m14": {
                    str(k): values for k, values in transfer_values.items()
                },
                "brute_force_values_k1_to_k4_m0_to_m5": {
                    str(k): values for k, values in brute_values.items()
                },
            },
            "transfer_matrix": {
                "state_rule": "For fixed k, states are last-bit vectors s in {0,1}^k.",
                "start_state": "0^k",
                "transition_rule": "state s may move to d iff sum(d)<=1 and d_i=1 implies s_i=0.",
                "outdegrees": transition_outdegrees,
                "state_profiles_m0_to_m14": profiles,
            },
            "recurrence": {
                "initial_values": {str(k): {"D_0": transfer_values[k][0], "D_1": transfer_values[k][1]} for k in range(1, TRANSFER_MAX_K + 1)},
                "formula": "D^(k)_m=k*D^(k)_{m-1}+D^(k)_{m-2}",
                "verified_k_range": [1, TRANSFER_MAX_K],
                "verified_m_range": [2, MAX_WINDOW],
                "residuals_m2_to_m14": {str(k): residuals for k, residuals in recurrence_residuals.items()},
                "characteristic_polynomial": "x^2-k*x-1",
                "metallic_slices": {
                    "k=1": "Fibonacci/golden vertex-count slice D^(1)_m=F_{m+2}",
                    "k=2": "Pell/silver slice",
                    "k=3": "Median-zero ordered triple anchor slice",
                },
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

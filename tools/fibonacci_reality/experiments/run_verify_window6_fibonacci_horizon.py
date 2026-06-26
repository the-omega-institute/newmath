#!/usr/bin/env python3
"""Forward finite check for the Window6 Fibonacci horizon anchor.

The run uses only integer Fibonacci arithmetic and direct finite enumeration.
It does not evaluate, fit, or assert any physical constant.
"""

from __future__ import annotations

import json
from itertools import product
from typing import Any


M = 6
WINDOW_BOUND = 2**M - 1
TAIL_BIT_INDICES = [7, 8, 9]
EXPECTED_VISIBLE_WEIGHTS = [1, 2, 3, 5, 8, 13]
EXPECTED_TAIL_ALIASES = [21, 34, 55]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def fib(index: int) -> int:
    if index < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, previous + current
    return previous


def v6(word: tuple[int, ...]) -> int:
    return sum(bit * EXPECTED_VISIBLE_WEIGHTS[index] for index, bit in enumerate(word))


def admissible(word: tuple[int, ...]) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def main() -> None:
    fibonacci_values = {index: fib(index) for index in range(0, 12)}
    visible_weights = [fib(index + 1) for index in range(1, M + 1)]
    tail_aliases = [fib(index + 1) for index in TAIL_BIT_INDICES]
    rho6 = max(index for index, value in fibonacci_values.items() if value <= WINDOW_BOUND)
    seam_s6 = M + 1
    foldbin_tail_alias_indices = [
        index
        for index, value in fibonacci_values.items()
        if value in set(tail_aliases)
    ]
    tail_fibonacci_block = [fib(index) for index in range(M + 2, rho6 + 1)]
    x6 = [
        word
        for word in product((0, 1), repeat=M)
        if admissible(word)
    ]
    singleton_tail_values = {
        f"c_{tail_index}": v6((0, 0, 0, 0, 0, 0)) + fib(tail_index + 1)
        for tail_index in TAIL_BIT_INDICES
    }
    tailcube_free_dimension = len(TAIL_BIT_INDICES)
    return_depth = rho6 - seam_s6

    checks = [
        check(
            "visible_weights",
            visible_weights == EXPECTED_VISIBLE_WEIGHTS,
            "positions 1..6 carry F_2..F_7 = 1,2,3,5,8,13",
        ),
        check(
            "tail_aliases_fibonacci_block",
            tail_aliases == EXPECTED_TAIL_ALIASES
            and tail_aliases == tail_fibonacci_block
            and foldbin_tail_alias_indices == [8, 9, 10],
            "Foldbin singleton tail aliases are F_8,F_9,F_10 = 21,34,55, the contiguous block F_{m+2}..F_{rho_6}",
        ),
        check(
            "rho6_horizon",
            rho6 == 10
            and fib(10) == 55
            and fib(11) == 89
            and fib(10) <= WINDOW_BOUND < fib(11)
            and max(foldbin_tail_alias_indices) == rho6,
            "rho_6=max{k:F_k<=2^6-1}=10 because 55<=63<89, matching the largest Foldbin tail alias index",
        ),
        check(
            "seam_s6",
            seam_s6 == M + 1 == 7,
            "s_6=m+1=7 is the first index beyond the visible weights F_2..F_7",
        ),
        check(
            "return_depth_equals_tailcube_dim",
            return_depth == 3 and return_depth == tailcube_free_dimension,
            "rho_6-s_6=3 equals the three Foldbin tail-cube bits c_7,c_8,c_9",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "anti_fit_guard": "All checks are forward finite arithmetic over the width-6 window, Fibonacci numbers, and Foldbin tail-bit aliases; no alpha input or physical constant is used.",
        "window_width": M,
        "window_bound": WINDOW_BOUND,
        "X6_count": len(x6),
        "visible_weights": visible_weights,
        "visible_weight_indices": ["F_2", "F_3", "F_4", "F_5", "F_6", "F_7"],
        "tail_aliases": tail_aliases,
        "tail_alias_indices": ["F_8", "F_9", "F_10"],
        "singleton_tail_values": singleton_tail_values,
        "rho_6": rho6,
        "rho_6_bound": "F_10=55<=63<F_11=89",
        "seam_s6": seam_s6,
        "return_depth": return_depth,
        "tailcube_free_dimension": tailcube_free_dimension,
        "tailcube_free_bits": ["c_7", "c_8", "c_9"],
        "forced_index_statement": "The functor seam/return indices are the Window6 Fibonacci-horizon indices s_6=7 and rho_6=10, and the return depth rho_6-s_6 equals the Foldbin tail-cube dimension.",
        "not_claimed": [
            "functor embedding form phi^-s Q(phi^-rho) forcedness",
            "physical alpha identification",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

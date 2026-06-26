#!/usr/bin/env python3
"""Forward audit for Theta-class resolved squares in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones and
edges join Hamming-distance-one words. The coordinate Theta-class Theta_i is
the set of edges flipping coordinate i. This certificate counts the induced
4-cycles whose two opposite edge pairs lie in Theta_i and Theta_j.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-theta-square-factorization"
CLAIM_ID = "window.fibonacci-cube.theta-square-factorization.certificate"
MIN_WINDOW = 2
MAX_WINDOW = 8
EXPECTED_WINDOW6_VERTEX_COUNT = 21
EXPECTED_WINDOW6_TOTAL_SQUARES = 22
EXPECTED_WINDOW6_PER_PAIR = {
    "1,3": 3,
    "1,4": 2,
    "1,5": 2,
    "1,6": 3,
    "2,4": 2,
    "2,5": 1,
    "2,6": 2,
    "3,5": 2,
    "3,6": 2,
    "4,6": 3,
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


def coord_mask(coord: int, width: int) -> int:
    if coord < 1 or coord > width:
        raise ValueError("coordinate out of range")
    return 1 << (width - coord)


def valid(word: int, width: int) -> bool:
    limit_mask = (1 << width) - 1
    return 0 <= word <= limit_mask and (word & (word >> 1)) == 0


def fibonacci_cube_words(width: int) -> list[int]:
    return [word for word in range(1 << width) if valid(word, width)]


def word_to_string(word: int, width: int) -> str:
    return format(word, f"0{width}b")


def theta_square_count(width: int, i: int, j: int) -> int:
    mask_i = coord_mask(i, width)
    mask_j = coord_mask(j, width)
    total = 0
    for word in fibonacci_cube_words(width):
        if word & (mask_i | mask_j):
            continue
        if (
            valid(word, width)
            and valid(word ^ mask_i, width)
            and valid(word ^ mask_j, width)
            and valid(word ^ mask_i ^ mask_j, width)
        ):
            total += 1
    return total


def theta_square_formula(width: int, i: int, j: int) -> int:
    if j == i + 1:
        return 0
    return fib(i) * fib(j - i - 1) * fib(width - j + 1)


def per_pair_counts(width: int) -> dict[str, int]:
    counts: dict[str, int] = {}
    for i in range(1, width + 1):
        for j in range(i + 1, width + 1):
            value = theta_square_count(width, i, j)
            if value:
                counts[f"{i},{j}"] = value
    return counts


def all_pair_table() -> dict[str, dict[str, int]]:
    table: dict[str, dict[str, int]] = {}
    for width in range(MIN_WINDOW, MAX_WINDOW + 1):
        table[str(width)] = {
            f"{i},{j}": theta_square_count(width, i, j)
            for i in range(1, width + 1)
            for j in range(i + 1, width + 1)
        }
    return table


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    vertex_counts = {
        width: len(fibonacci_cube_words(width))
        for width in range(MIN_WINDOW, MAX_WINDOW + 1)
    }
    pair_table = all_pair_table()
    formula_table = {
        str(width): {
            f"{i},{j}": theta_square_formula(width, i, j)
            for i in range(1, width + 1)
            for j in range(i + 1, width + 1)
        }
        for width in range(MIN_WINDOW, MAX_WINDOW + 1)
    }
    window6_counts = per_pair_counts(6)
    window6_total = sum(window6_counts.values())
    adjacent_counts = [
        theta_square_count(width, i, i + 1)
        for width in range(MIN_WINDOW, MAX_WINDOW + 1)
        for i in range(1, width)
    ]
    nonadjacent_factor_checks = [
        (
            width,
            i,
            j,
            theta_square_count(width, i, j),
            fib(i),
            fib(j - i - 1),
            fib(width - j + 1),
        )
        for width in range(MIN_WINDOW, MAX_WINDOW + 1)
        for i in range(1, width + 1)
        for j in range(i + 2, width + 1)
    ]
    nonzero_pair_count = len(window6_counts)

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(9)] == [0, 1, 1, 2, 3, 5, 8, 13, 21],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m2_to_m8",
            all(vertex_counts[width] == fib(width + 2) for width in vertex_counts),
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=2..8.",
        ),
        check(
            "window6_vertex_count",
            vertex_counts[6] == EXPECTED_WINDOW6_VERTEX_COUNT,
            "The m=6 carrier has 21 vertices.",
        ),
        check(
            "theta_square_formula_all_pairs_m2_to_m8",
            pair_table == formula_table,
            "Direct base-word enumeration matches S_m(i,j)=0 for adjacent coordinates and F_i F_{j-i-1} F_{m-j+1} otherwise.",
        ),
        check(
            "adjacent_theta_pairs_zero_m2_to_m8",
            all(value == 0 for value in adjacent_counts),
            "Adjacent coordinate Theta-class pairs have no induced 4-cycle base word.",
        ),
        check(
            "nonadjacent_three_fibonacci_factors_m2_to_m8",
            all(value == left * middle * right for _, _, _, value, left, middle, right in nonadjacent_factor_checks),
            "Every nonadjacent pair is forced by left, middle, and right Fibonacci path factors.",
        ),
        check(
            "window6_theta_square_per_pair_profile",
            window6_counts == EXPECTED_WINDOW6_PER_PAIR,
            "The m=6 nonzero coordinate-pair profile matches the frozen Theta-class breakdown.",
        ),
        check(
            "window6_theta_square_total",
            window6_total == EXPECTED_WINDOW6_TOTAL_SQUARES,
            "The m=6 coordinate-resolved square total is 22.",
        ),
        check(
            "theta_pair_breakdown_not_cube_polynomial_repackage",
            window6_total == EXPECTED_WINDOW6_TOTAL_SQUARES
            and nonzero_pair_count == len(EXPECTED_WINDOW6_PER_PAIR)
            and len(set(window6_counts.values())) > 1,
            "The certificate records a Theta-class-pair incidence profile, not only the total cube-polynomial square count.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only finite graph enumeration, coordinate flips, and integer Fibonacci counts.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "experiment_run_id": f"{EXPERIMENT_ID}:{started_at}",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "script_sha": script_sha(),
        "status": status,
        "checks": checks,
        "check_summary": check_summary(checks),
        "result": {
            "carrier": {
                "window_range": [MIN_WINDOW, MAX_WINDOW],
                "vertex_counts": {str(width): count for width, count in vertex_counts.items()},
                "window6_vertices": [
                    word_to_string(word, 6) for word in fibonacci_cube_words(6)
                ],
            },
            "theta_square_factorization": {
                "definition": "S_m(i,j) counts induced 4-cycles with opposite edge pairs in Theta_i and Theta_j.",
                "formula": "S_m(i,j)=0 if j=i+1, else F_i*F_{j-i-1}*F_{m-j+1}.",
                "direct_counts": pair_table,
                "formula_counts": formula_table,
            },
            "window6": {
                "coordinate_pair_profile": window6_counts,
                "coordinate_resolved_total": window6_total,
                "nonzero_pair_count": nonzero_pair_count,
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

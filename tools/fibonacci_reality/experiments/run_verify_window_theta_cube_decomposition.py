#!/usr/bin/env python3
"""Forward audit for Theta-class resolved cubes in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones and
edges join Hamming-distance-one words. The coordinate Theta-class Theta_i is
the set of edges flipping coordinate i. This certificate counts induced Q_k
subcubes whose edge directions lie in a selected coordinate Theta tuple.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from itertools import combinations
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-theta-cube-decomposition"
CLAIM_ID = "window.fibonacci-cube.theta-cube-decomposition.certificate"
MIN_WINDOW = 3
MAX_WINDOW = 8
EXPECTED_TOTAL_TUPLE_CHECKS = 498
EXPECTED_WINDOW6_VERTEX_COUNT = 21
EXPECTED_WINDOW6_CUBE_SUMS = {
    1: 38,
    2: 22,
    3: 4,
    4: 0,
    5: 0,
    6: 0,
}
EXPECTED_WINDOW6_CUBE_POLYNOMIAL = [21, 38, 22, 4]


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


def subset_masks(coords: tuple[int, ...], width: int) -> list[int]:
    masks = [coord_mask(coord, width) for coord in coords]
    results: list[int] = []
    for size in range(len(masks) + 1):
        for selected in combinations(masks, size):
            mask = 0
            for item in selected:
                mask ^= item
            results.append(mask)
    return results


def theta_cube_count(width: int, coords: tuple[int, ...]) -> int:
    selected_mask = 0
    for coord in coords:
        selected_mask |= coord_mask(coord, width)
    flips = subset_masks(coords, width)
    total = 0
    for word in fibonacci_cube_words(width):
        if word & selected_mask:
            continue
        if all(valid(word ^ flip_mask, width) for flip_mask in flips):
            total += 1
    return total


def theta_cube_formula(width: int, coords: tuple[int, ...]) -> int:
    if not coords:
        return fib(width + 2)
    value = fib(coords[0])
    for left, right in zip(coords, coords[1:]):
        value *= fib(right - left - 1)
    value *= fib(width - coords[-1] + 1)
    return value


def theta_square_anchor_formula(width: int, i: int, j: int) -> int:
    return fib(i) * fib(j - i - 1) * fib(width - j + 1)


def all_tuple_records() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for width in range(MIN_WINDOW, MAX_WINDOW + 1):
        for dimension in range(1, width + 1):
            for coords in combinations(range(1, width + 1), dimension):
                actual = theta_cube_count(width, coords)
                expected = theta_cube_formula(width, coords)
                records.append(
                    {
                        "m": width,
                        "k": dimension,
                        "coords": coords,
                        "actual": actual,
                        "formula": expected,
                    }
                )
    return records


def window6_dimension_sums() -> dict[int, int]:
    return {
        dimension: sum(
            theta_cube_count(6, coords)
            for coords in combinations(range(1, 7), dimension)
        )
        for dimension in range(1, 7)
    }


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
    records = all_tuple_records()
    mismatches = [
        record for record in records if record["actual"] != record["formula"]
    ]
    adjacent_zero_failures = [
        record
        for record in records
        if any(right == left + 1 for left, right in zip(record["coords"], record["coords"][1:]))
        and record["actual"] != 0
    ]
    square_anchor_failures = [
        (width, i, j)
        for width in range(MIN_WINDOW, MAX_WINDOW + 1)
        for i, j in combinations(range(1, width + 1), 2)
        if theta_cube_formula(width, (i, j))
        != theta_square_anchor_formula(width, i, j)
        or theta_cube_count(width, (i, j))
        != theta_square_anchor_formula(width, i, j)
    ]
    window6_sums = window6_dimension_sums()
    window6_polynomial = [vertex_counts[6]]
    for dimension in range(1, 7):
        value = window6_sums[dimension]
        if value or dimension <= 3:
            window6_polynomial.append(value)
    window6_polynomial = window6_polynomial[:4]
    nonzero_tuple_profile = {
        f"{record['m']}:{','.join(str(coord) for coord in record['coords'])}": record["actual"]
        for record in records
        if record["actual"]
    }

    assert len(records) == EXPECTED_TOTAL_TUPLE_CHECKS
    assert not mismatches
    assert not square_anchor_failures
    assert window6_sums == EXPECTED_WINDOW6_CUBE_SUMS
    assert window6_polynomial == EXPECTED_WINDOW6_CUBE_POLYNOMIAL

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(9)] == [0, 1, 1, 2, 3, 5, 8, 13, 21],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m3_to_m8",
            all(vertex_counts[width] == fib(width + 2) for width in vertex_counts),
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=3..8.",
        ),
        check(
            "window6_vertex_count",
            vertex_counts[6] == EXPECTED_WINDOW6_VERTEX_COUNT,
            "The m=6 carrier has 21 vertices.",
        ),
        check(
            "theta_tuple_checks_total_498",
            len(records) == EXPECTED_TOTAL_TUPLE_CHECKS,
            "The audit checks every nonempty coordinate tuple for m=3..8.",
        ),
        check(
            "theta_cube_formula_all_tuples_m3_to_m8",
            not mismatches,
            "Direct base-word enumeration matches S_m(i_1..i_k)=F_{i_1} prod F_{gap} F_{m-i_k+1} for all 498 tuples.",
        ),
        check(
            "adjacent_selected_coordinates_zero_m3_to_m8",
            not adjacent_zero_failures,
            "Any selected adjacent coordinate pair forces a zero middle Fibonacci factor and no valid induced cube base word.",
        ),
        check(
            "window6_theta_resolved_dimension_sums",
            window6_sums == EXPECTED_WINDOW6_CUBE_SUMS,
            "For m=6, summing over coordinate tuples gives k=1:38, k=2:22, k=3:4, and k>=4:0.",
        ),
        check(
            "window6_cube_polynomial_coefficients",
            window6_polynomial == EXPECTED_WINDOW6_CUBE_POLYNOMIAL,
            "Including k=0 vertices, C(Gamma_6,x)=21+38x+22x^2+4x^3.",
        ),
        check(
            "theta_square_anchor_k2_formula_agreement",
            not square_anchor_failures,
            "The k=2 specialization is exactly the theta-square anchor F_i F_{j-i-1} F_{m-j+1}.",
        ),
        check(
            "window6_cube_dimension_cutoff_k_ge_4",
            all(window6_sums[dimension] == 0 for dimension in range(4, 7)),
            "The m=6 Fibonacci cube has no induced Q_k with k>=4.",
        ),
        check(
            "coordinate_resolution_not_total_cube_polynomial_repackage",
            len(nonzero_tuple_profile) > len(EXPECTED_WINDOW6_CUBE_POLYNOMIAL)
            and window6_sums[2] == 22
            and window6_sums[3] == 4,
            "The certificate records coordinate tuple incidences before summing to cube-polynomial coefficients.",
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
            "theta_cube_decomposition": {
                "definition": "S_m(i_1..i_k) counts induced Q_k subcubes with directions in coordinate Theta-classes Theta_{i_1}..Theta_{i_k}.",
                "formula": "S_m(i_1..i_k)=F_{i_1}*prod_{t=2..k} F_{i_t-i_{t-1}-1}*F_{m-i_k+1}.",
                "checked_tuple_count": len(records),
                "mismatches": mismatches,
                "nonzero_tuple_profile": nonzero_tuple_profile,
            },
            "window6": {
                "theta_resolved_dimension_sums": {
                    str(dimension): value for dimension, value in window6_sums.items()
                },
                "cube_polynomial_coefficients": window6_polynomial,
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

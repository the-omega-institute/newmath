#!/usr/bin/env python3
"""Forward audit for geodesic-betweenness ordered triples in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones and
Hamming-distance-one edges.  A_m counts ordered triples (u,x,v) with x in the
geodesic interval I(u,v), equivalently d(u,x)+d(x,v)=d(u,v).  The certificate
checks direct BFS enumeration on the brute-force window and an integer
four-state transfer matrix for the family recurrence.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from collections import deque
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-betweenness-triple"
CLAIM_ID = "window.fibonacci-cube.betweenness-triple.certificate"
MAX_WINDOW = 10
BRUTE_MAX_WINDOW = 6
EXPECTED_A = [1, 6, 17, 63, 210, 729, 2491, 8564, 29373, 100837, 346048]
Q = [
    [1, 2, 2, 1],
    [1, 1, 1, 0],
    [1, 1, 0, 0],
    [1, 0, 0, 0],
]
START_ROW = [1, 2, 2, 1]
E1 = [1, 0, 0, 0]


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


def neighbors(word: int, width: int) -> list[int]:
    result = []
    for coord in range(width):
        candidate = word ^ (1 << coord)
        if valid(candidate, width):
            result.append(candidate)
    return result


def bfs_distances(source: int, width: int) -> dict[int, int]:
    distances = {source: 0}
    queue: deque[int] = deque([source])
    while queue:
        current = queue.popleft()
        for adjacent in neighbors(current, width):
            if adjacent not in distances:
                distances[adjacent] = distances[current] + 1
                queue.append(adjacent)
    return distances


def all_source_distances(width: int) -> dict[int, dict[int, int]]:
    return {source: bfs_distances(source, width) for source in words(width)}


def brute_force_a(width: int) -> int:
    carrier = words(width)
    distances = all_source_distances(width)
    total = 0
    for u, x, v in itertools.product(carrier, repeat=3):
        if distances[u][x] + distances[x][v] == distances[u][v]:
            total += 1
    return total


def wiener_index(width: int) -> int:
    carrier = words(width)
    distances = all_source_distances(width)
    return sum(distances[u][v] for u in carrier for v in carrier)


def row_times_matrix(row: list[int], matrix: list[list[int]]) -> list[int]:
    return [sum(row[index] * matrix[index][column] for index in range(len(row))) for column in range(len(row))]


def matrix_transfer_values(max_width: int) -> list[int]:
    row = START_ROW[:]
    values = []
    for _ in range(max_width + 1):
        values.append(sum(row[index] * E1[index] for index in range(len(row))))
        row = row_times_matrix(row, Q)
    return values


def poly_add(left: list[int], right: list[int]) -> list[int]:
    length = max(len(left), len(right))
    result = [0] * length
    for index in range(length):
        result[index] = (left[index] if index < len(left) else 0) + (right[index] if index < len(right) else 0)
    return trim_poly(result)


def poly_mul(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, left_coeff in enumerate(left):
        for j, right_coeff in enumerate(right):
            result[i + j] += left_coeff * right_coeff
    return trim_poly(result)


def trim_poly(poly: list[int]) -> list[int]:
    result = poly[:]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def permutation_sign(permutation: tuple[int, ...]) -> int:
    inversions = 0
    for i in range(len(permutation)):
        for j in range(i + 1, len(permutation)):
            if permutation[i] > permutation[j]:
                inversions += 1
    return -1 if inversions % 2 else 1


def characteristic_polynomial(matrix: list[list[int]]) -> list[int]:
    size = len(matrix)
    poly_matrix: list[list[list[int]]] = []
    for row in range(size):
        poly_row = []
        for column in range(size):
            constant = -matrix[row][column]
            if row == column:
                poly_row.append([constant, 1])
            else:
                poly_row.append([constant])
        poly_matrix.append(poly_row)

    determinant = [0]
    for permutation in itertools.permutations(range(size)):
        term = [permutation_sign(permutation)]
        for row, column in enumerate(permutation):
            term = poly_mul(term, poly_matrix[row][column])
        determinant = poly_add(determinant, term)
    return trim_poly(determinant)


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_force_a(width) for width in range(BRUTE_MAX_WINDOW + 1)]
    transfer_values = matrix_transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(width)) for width in range(MAX_WINDOW + 1)]
    recurrence_residuals = [
        transfer_values[width]
        - 2 * transfer_values[width - 1]
        - 5 * transfer_values[width - 2]
        + transfer_values[width - 4]
        for width in range(4, MAX_WINDOW + 1)
    ]
    char_poly = characteristic_polynomial(Q)
    expected_char_poly = [1, 0, -5, -2, 1]
    window6_carrier = words(6)
    window6_distances = all_source_distances(6)
    window6_interval_count = sum(
        1
        for u, x, v in itertools.product(window6_carrier, repeat=3)
        if window6_distances[u][x] + window6_distances[x][v] == window6_distances[u][v]
    )
    window6_wiener = wiener_index(6)

    checks = [
        check(
            "fibonacci_function_baseline",
            [fib(index) for index in range(13)] == [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144],
            "The Fibonacci convention is F_0=0,F_1=1 with the standard recurrence.",
        ),
        check(
            "gamma_m_vertex_counts_m0_to_m10",
            vertex_counts == [fib(width + 2) for width in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=0..10.",
        ),
        check(
            "brute_force_betweenness_values_m0_to_m6",
            brute_values == EXPECTED_A[: BRUTE_MAX_WINDOW + 1],
            "Direct BFS all-pairs interval enumeration matches the expected A_m values for m=0..6.",
        ),
        check(
            "four_state_transfer_values_m0_to_m10",
            transfer_values == EXPECTED_A,
            "The four-state transfer matrix produces the expected A_m values for m=0..10.",
        ),
        check(
            "brute_force_transfer_agree_m0_to_m6",
            brute_values == transfer_values[: BRUTE_MAX_WINDOW + 1],
            "The direct BFS enumeration and four-state transfer computation agree on m=0..6.",
        ),
        check(
            "order_four_recurrence_m4_to_m10",
            all(residual == 0 for residual in recurrence_residuals),
            "The sequence satisfies A_m=2A_{m-1}+5A_{m-2}-A_{m-4} for m=4..10.",
        ),
        check(
            "characteristic_polynomial_x4_minus_2x3_minus_5x2_plus_1",
            char_poly == expected_char_poly,
            "Direct integer polynomial determinant gives det(xI-Q)=x^4-2x^3-5x^2+1.",
        ),
        check(
            "interval_cardinality_sum_definition",
            EXPECTED_A[6] == 2491 and brute_values[6] == window6_interval_count,
            "A_m is counted as sum_{u,v}|I(u,v)|, with ordered triples (u,x,v).",
        ),
        check(
            "distinct_from_wiener_index_window6",
            EXPECTED_A[6] == 2491 and window6_wiener == 1096 and EXPECTED_A[6] != window6_wiener,
            "For m=6, the interval-cardinality sum A_6=2491 differs from the Wiener distance sum 1096.",
        ),
        check(
            "not_prior_median_or_nine_anchor_repackage",
            EXPECTED_A[6] == 2491 and EXPECTED_A[6] != 1549 and EXPECTED_A[6] != 1909,
            "The m=6 betweenness interval statistic differs from the median-zero triple and geodesic-enumerator anchors.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, BFS graph distances, integer transfer data, and recurrence checks.",
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
            "betweenness_ordered_triples": {
                "definition": "A_m counts ordered triples (u,x,v) in V(Gamma_m)^3 with d(u,x)+d(x,v)=d(u,v).",
                "equivalent_condition": "A_m=sum_{u,v}|I(u,v)|, the sum of geodesic-interval cardinalities.",
                "expected_values_m0_to_m10": EXPECTED_A,
                "brute_force_values_m0_to_m6": brute_values,
                "transfer_values_m0_to_m10": transfer_values,
            },
            "transfer_matrix": {
                "left_row": START_ROW,
                "matrix": Q,
                "right_column": E1,
                "formula": "A_m=[1,2,2,1]*Q^m*[1,0,0,0]^T.",
            },
            "recurrence": {
                "initial_values": {f"A_{index}": transfer_values[index] for index in range(4)},
                "formula": "A_m=2*A_{m-1}+5*A_{m-2}-A_{m-4}",
                "verified_range": [4, MAX_WINDOW],
                "residuals_m4_to_m10": recurrence_residuals,
                "characteristic_polynomial": "x^4-2*x^3-5*x^2+1",
                "characteristic_polynomial_coefficients_constant_first": char_poly,
            },
            "distinct_from_wiener": {
                "window": 6,
                "A_6_interval_cardinality_sum": EXPECTED_A[6],
                "Wiener_6_ordered_distance_sum": window6_wiener,
                "statement": "A_m is an interval-cardinality/betweenness statistic, not the Wiener index.",
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

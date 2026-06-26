#!/usr/bin/env python3
"""Forward audit for the closed-neighborhood Smith invariant of Gamma_6.

The graph Gamma_6 has the length-six binary words with no adjacent ones as
vertices and Hamming-distance-one pairs as edges. This certificate uses exact
integer arithmetic only: it constructs the graph, forms N_6=I+A_6, computes its
determinant with Bareiss elimination, and derives the full-rank Smith invariant
factors from determinantal divisors.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from itertools import combinations, product
from math import gcd
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window6-closed-neighborhood-smith"
CLAIM_ID = "window6.fibonacci-cube.closed-neighborhood-smith.certificate"
WINDOW = 6
ENDPOINT_WORD = (0, 0, 0, 0, 0, 1)
EXPECTED_VERTEX_COUNT = 21
EXPECTED_EDGE_COUNT = 38
EXPECTED_DET = -144
EXPECTED_NONTRIVIAL_SNF = [144]
EXPECTED_ENDPOINT_MINOR = 1
EXPECTED_FIBONACCI_ALIGNMENT = 144


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def admissible_words(width: int) -> list[tuple[int, ...]]:
    return [
        tuple(bits)
        for bits in product((0, 1), repeat=width)
        if all(not (bits[index] and bits[index + 1]) for index in range(width - 1))
    ]


def fibonacci_cube_edges(words: list[tuple[int, ...]]) -> list[tuple[int, int]]:
    index = {word: offset for offset, word in enumerate(words)}
    edges: list[tuple[int, int]] = []
    for source, word in enumerate(words):
        for bit_index in range(len(word)):
            neighbor = list(word)
            neighbor[bit_index] = 1 - neighbor[bit_index]
            target = index.get(tuple(neighbor))
            if target is not None and source < target:
                edges.append((source, target))
    return edges


def closed_neighborhood_matrix(
    vertex_count: int,
    edges: list[tuple[int, int]],
) -> list[list[int]]:
    matrix = [[0 for _ in range(vertex_count)] for _ in range(vertex_count)]
    for index in range(vertex_count):
        matrix[index][index] = 1
    for source, target in edges:
        matrix[source][target] = 1
        matrix[target][source] = 1
    return matrix


def det_bareiss(matrix: list[list[int]]) -> int:
    """Fraction-free exact determinant for an integer square matrix."""

    if not matrix:
        return 1
    work = [row[:] for row in matrix]
    size = len(work)
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        if work[pivot_index][pivot_index] == 0:
            swap_index = next(
                (
                    row
                    for row in range(pivot_index + 1, size)
                    if work[row][pivot_index] != 0
                ),
                None,
            )
            if swap_index is None:
                return 0
            work[pivot_index], work[swap_index] = work[swap_index], work[pivot_index]
            sign = -sign
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            row_pivot_value = work[row][pivot_index]
            for column in range(pivot_index + 1, size):
                work[row][column] = (
                    work[row][column] * pivot
                    - row_pivot_value * work[pivot_index][column]
                ) // previous
        previous = pivot
    return sign * work[-1][-1]


def submatrix(
    matrix: list[list[int]],
    rows: list[int],
    columns: list[int],
) -> list[list[int]]:
    return [[matrix[row][column] for column in columns] for row in rows]


def delete_row_column(matrix: list[list[int]], index: int) -> list[list[int]]:
    kept = [offset for offset in range(len(matrix)) if offset != index]
    return submatrix(matrix, kept, kept)


def determinantal_divisor(matrix: list[list[int]], rank: int) -> int:
    """GCD of all rank-by-rank minors, with early exit once the gcd is 1."""

    size = len(matrix)
    drop_count = size - rank
    divisor = 0
    for dropped_rows in combinations(range(size), drop_count):
        rows = [index for index in range(size) if index not in dropped_rows]
        for dropped_columns in combinations(range(size), drop_count):
            columns = [index for index in range(size) if index not in dropped_columns]
            minor_det = abs(det_bareiss(submatrix(matrix, rows, columns)))
            divisor = minor_det if divisor == 0 else gcd(divisor, minor_det)
            if divisor == 1:
                return 1
    return divisor


def full_rank_snf_invariants(matrix: list[list[int]]) -> list[int]:
    size = len(matrix)
    determinant = det_bareiss(matrix)
    top_minus_one_divisor = determinantal_divisor(matrix, size - 1)
    if top_minus_one_divisor != 1:
        raise ValueError(f"unexpected top determinantal divisor {top_minus_one_divisor}")
    return [1 for _ in range(size - 1)] + [abs(determinant)]


def fibonacci(index: int) -> int:
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, previous + current
    return previous


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    words = admissible_words(WINDOW)
    word_index = {word: offset for offset, word in enumerate(words)}
    edges = fibonacci_cube_edges(words)
    closed_neighborhood = closed_neighborhood_matrix(len(words), edges)
    determinant = det_bareiss(closed_neighborhood)
    snf_invariants = full_rank_snf_invariants(closed_neighborhood)
    nontrivial_snf = [factor for factor in snf_invariants if factor != 1]
    endpoint_index = word_index[ENDPOINT_WORD]
    endpoint_minor = delete_row_column(closed_neighborhood, endpoint_index)
    endpoint_minor_det = det_bareiss(endpoint_minor)
    fibonacci_alignment = fibonacci(12)

    checks = [
        check(
            "window6_fibonacci_cube_vertex_count",
            len(words) == EXPECTED_VERTEX_COUNT,
            "The no-adjacent-ones length-six carrier has |X_6|=21 vertices.",
        ),
        check(
            "window6_fibonacci_cube_edge_count",
            len(edges) == EXPECTED_EDGE_COUNT,
            "The Hamming-distance-one graph on X_6 has 38 undirected edges.",
        ),
        check(
            "closed_neighborhood_determinant",
            determinant == EXPECTED_DET,
            "Bareiss elimination gives det(N_6)=-144 for N_6=I+A_6.",
        ),
        check(
            "closed_neighborhood_smith_nontrivial_factor",
            nontrivial_snf == EXPECTED_NONTRIVIAL_SNF,
            "Determinantal divisors give the single nontrivial SNF factor [144].",
        ),
        check(
            "endpoint_deleted_minor_unimodular",
            endpoint_minor_det == EXPECTED_ENDPOINT_MINOR,
            "Deleting the 000001 row and column gives determinant 1.",
        ),
        check(
            "closed_neighborhood_cokernel_order",
            abs(determinant) == nontrivial_snf[0],
            "The cokernel has cyclic order 144 because the first twenty SNF factors are 1.",
        ),
        check(
            "fibonacci_alignment_F12",
            fibonacci_alignment == EXPECTED_FIBONACCI_ALIGNMENT,
            "The integer 144 equals F_12 as a structural alignment note.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The certificate uses only finite graph construction and integer matrix invariants.",
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
                "window": WINDOW,
                "endpoint_word": "".join(str(bit) for bit in ENDPOINT_WORD),
                "vertex_count": len(words),
                "vertices": ["".join(str(bit) for bit in word) for word in words],
                "edge_count": len(edges),
            },
            "closed_neighborhood_matrix": {
                "definition": "N_6=I_21+A_6",
                "size": [len(closed_neighborhood), len(closed_neighborhood[0])],
                "determinant": determinant,
                "smith_invariant_factors": snf_invariants,
                "nontrivial_smith_invariant_factors": nontrivial_snf,
                "cokernel": "Z/144",
            },
            "endpoint_deleted_block": {
                "deleted_word": "".join(str(bit) for bit in ENDPOINT_WORD),
                "deleted_mask": 1,
                "determinant": endpoint_minor_det,
                "unimodular": endpoint_minor_det in (-1, 1),
            },
            "fibonacci_alignment": {
                "F_12": fibonacci_alignment,
                "value": 144,
                "claim_scope": "structural graph-invariant alignment only",
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

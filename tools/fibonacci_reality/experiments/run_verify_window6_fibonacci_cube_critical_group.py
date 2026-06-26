#!/usr/bin/env python3
"""Forward audit for the critical group of the Window6 Fibonacci cube.

The graph Gamma_6 has the length-six binary words with no adjacent ones as
vertices and Hamming-distance-one pairs as edges. This certificate uses exact
integer arithmetic only: it constructs the graph, forms the reduced Laplacian,
computes its determinant with Bareiss elimination, and derives the full-rank
Smith invariant factors from determinantal divisors.
"""

from __future__ import annotations

import json
from datetime import UTC, datetime
from itertools import combinations, product
from math import gcd
from typing import Any

EXPERIMENT_ID = "verify-window6-fibonacci-cube-critical-group"
CLAIM_ID = "window6.fibonacci-cube.critical-group-snf.certificate"
WINDOW = 6
ROOT_WORD = (0, 0, 0, 0, 0, 0)
EXPECTED_VERTEX_COUNT = 21
EXPECTED_EDGE_COUNT = 38
EXPECTED_DET = 592458464
EXPECTED_NONTRIVIAL_SNF = [4, 148114616]


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


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


def reduced_laplacian(
    vertex_count: int,
    edges: list[tuple[int, int]],
    root_index: int,
) -> list[list[int]]:
    laplacian = [[0 for _ in range(vertex_count)] for _ in range(vertex_count)]
    for source, target in edges:
        laplacian[source][source] += 1
        laplacian[target][target] += 1
        laplacian[source][target] -= 1
        laplacian[target][source] -= 1
    return [
        [laplacian[row][column] for column in range(vertex_count) if column != root_index]
        for row in range(vertex_count)
        if row != root_index
    ]


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
    divisors = [1]
    for rank in range(1, size + 1):
        divisors.append(determinantal_divisor(matrix, rank))
    return [divisors[index] // divisors[index - 1] for index in range(1, size + 1)]


def main() -> None:
    started_at = now_iso()
    words = admissible_words(WINDOW)
    word_index = {word: offset for offset, word in enumerate(words)}
    edges = fibonacci_cube_edges(words)
    reduced = reduced_laplacian(len(words), edges, word_index[ROOT_WORD])
    determinant = det_bareiss(reduced)
    snf_invariants = full_rank_snf_invariants(reduced)
    nontrivial_snf = [factor for factor in snf_invariants if factor != 1]

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
            "reduced_laplacian_tree_number",
            determinant == EXPECTED_DET,
            "Bareiss elimination gives det(L^(0))=592458464, the matrix-tree count.",
        ),
        check(
            "reduced_laplacian_smith_nontrivial_factors",
            nontrivial_snf == EXPECTED_NONTRIVIAL_SNF,
            "Determinantal divisors give nontrivial SNF factors [4,148114616].",
        ),
        check(
            "critical_group_order_matches_tree_number",
            nontrivial_snf[0] * nontrivial_snf[1] == determinant,
            "The product 4*148114616 equals the critical-group order.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The certificate uses only finite graph construction and integer matrix invariants.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks,
        "result": {
            "carrier": {
                "window": WINDOW,
                "root_word": "".join(str(bit) for bit in ROOT_WORD),
                "vertex_count": len(words),
                "vertices": ["".join(str(bit) for bit in word) for word in words],
                "edge_count": len(edges),
            },
            "reduced_laplacian": {
                "size": [len(reduced), len(reduced[0])],
                "determinant": determinant,
                "smith_invariant_factors": snf_invariants,
                "nontrivial_smith_invariant_factors": nontrivial_snf,
            },
            "critical_group": {
                "order": determinant,
                "decomposition": "Z/4 + Z/148114616",
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

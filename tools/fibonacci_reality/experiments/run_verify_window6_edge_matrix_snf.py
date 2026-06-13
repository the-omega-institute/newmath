#!/usr/bin/env python3
"""Forward Smith normal form audit for the Window6 edge-flux matrix E.

The matrix is the finite edge-count matrix derived from the Window6 cell
partition and hypercube edges. The audit uses exact integer arithmetic and
Smith normal form only; it does not evaluate or identify any physical constant.
"""

from __future__ import annotations

import json
from functools import reduce
from itertools import product
from operator import mul
from typing import Any

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


LABELS = ["U_2", "U_1", "U_L", "U_R"]
FIB_WEIGHTS = (1, 2, 3, 5, 8, 13)
EXPECTED_EDGE_MATRIX = [
    [28, 63, 23, 20],
    [63, 21, 21, 6],
    [23, 21, 2, 6],
    [20, 6, 6, 2],
]
EXPECTED_DET = 10350
EXPECTED_SNF_DIAGONAL = [1, 1, 3, 3450]
REDUCED_LAPLACIAN_SNF_DIAGONAL = [1, 1, 123336]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def factor_record(value: int) -> dict[str, int]:
    return {str(prime): exponent for prime, exponent in sorted(sp.factorint(value).items())}


def matrix_record(matrix: sp.Matrix) -> list[list[int]]:
    return [[int(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


def fibonacci(index: int) -> int:
    if index < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, previous + current
    return previous


def fibonacci_values_until_exceeds(bound: int) -> list[int]:
    values: list[int] = []
    index = 0
    while True:
        value = fibonacci(index)
        values.append(value)
        if value > bound:
            return values
        index += 1


def v6(word: tuple[int, ...]) -> int:
    return sum(bit * FIB_WEIGHTS[index] for index, bit in enumerate(word))


def foldbin_fiber(word: tuple[int, ...]) -> set[int]:
    fiber: set[int] = set()
    for c7, c8, c9 in product((0, 1), repeat=3):
        if c7 * c8 or c8 * c9 or word[5] * c7:
            continue
        value = v6(word) + 21 * c7 + 34 * c8 + 55 * c9
        if value <= 63:
            fiber.add(value)
    return fiber


def derive_edge_matrix() -> dict[str, Any]:
    x6 = [
        word
        for word in product((0, 1), repeat=6)
        if all(not (word[index] and word[index + 1]) for index in range(5))
    ]
    weight = lambda word: sum(word)
    boundary = [word for word in x6 if word[0] and word[5]]
    cyclic = [word for word in x6 if word not in boundary]
    stable_blocks = [
        [word for word in cyclic if weight(word) == 2],
        [word for word in cyclic if weight(word) == 1],
        [word for word in cyclic if weight(word) in (0, 3)],
        boundary,
    ]

    micro_cells = [
        set().union(*(foldbin_fiber(word) for word in block))
        for block in stable_blocks
    ]
    vertex_owner = {vertex: index for index, cell in enumerate(micro_cells) for vertex in cell}

    edge_matrix = [[0 for _ in range(4)] for _ in range(4)]
    for vertex in range(64):
        for bit in range(6):
            neighbor = vertex ^ (1 << bit)
            if neighbor <= vertex:
                continue
            source = vertex_owner[vertex]
            target = vertex_owner[neighbor]
            if source == target:
                edge_matrix[source][source] += 1
            else:
                edge_matrix[source][target] += 1
                edge_matrix[target][source] += 1

    return {
        "cell_order": LABELS,
        "stable_block_counts": [len(block) for block in stable_blocks],
        "micro_cell_counts": [len(cell) for cell in micro_cells],
        "edge_matrix": edge_matrix,
    }


def main() -> None:
    derived = derive_edge_matrix()
    edge_matrix = sp.Matrix(derived["edge_matrix"])
    det_e = int(edge_matrix.det())
    snf_matrix = smith_normal_form(edge_matrix, domain=sp.ZZ)
    snf_diagonal = [
        abs(int(snf_matrix[index, index]))
        for index in range(min(snf_matrix.rows, snf_matrix.cols))
    ]
    invariant_product = reduce(mul, snf_diagonal, 1)
    nontrivial_factors = [factor for factor in snf_diagonal if factor != 1]
    small_invariant_factors = snf_diagonal[:3]
    expected_small_fibonacci = [fibonacci(2), fibonacci(2), fibonacci(4)]
    large_factor = snf_diagonal[-1]
    fibonacci_witness_values = fibonacci_values_until_exceeds(large_factor)
    large_factor_is_fibonacci = large_factor in fibonacci_witness_values

    checks = [
        check(
            "edge_matrix_symmetric_det",
            derived["edge_matrix"] == EXPECTED_EDGE_MATRIX
            and edge_matrix == edge_matrix.T
            and det_e == EXPECTED_DET
            and sp.factorint(det_e) == {2: 1, 3: 2, 5: 2, 23: 1},
            "The forward-enumerated edge-flux matrix E is symmetric and has determinant 10350=2*3^2*5^2*23.",
        ),
        check(
            "edge_matrix_snf",
            matrix_record(snf_matrix) == sp.diag(*EXPECTED_SNF_DIAGONAL).tolist()
            and snf_diagonal == EXPECTED_SNF_DIAGONAL,
            "Exact Smith normal form over ZZ gives SNF(E)=diag(1,1,3,3450).",
        ),
        check(
            "invariant_factor_product_equals_det",
            invariant_product == abs(det_e) == EXPECTED_DET,
            "The product of invariant factors equals |det(E)|=10350.",
        ),
        check(
            "cokernel_torsion",
            nontrivial_factors == [3, 3450] and sp.factorint(large_factor) == {2: 1, 3: 1, 5: 2, 23: 1},
            "The torsion cokernel Z^4/EZ^4 is Z/3 + Z/3450, with 3450=2*3*5^2*23.",
        ),
        check(
            "small_factors_fibonacci",
            small_invariant_factors == expected_small_fibonacci and not large_factor_is_fibonacci,
            "Only the small invariant factors (1,1,3)=(F_2,F_2,F_4) are Fibonacci; the large factor 3450 is not Fibonacci.",
        ),
        check(
            "distinct_from_laplacian_snf",
            snf_diagonal != REDUCED_LAPLACIAN_SNF_DIAGONAL,
            "SNF(E)=diag(1,1,3,3450) is distinct from the reduced Laplacian SNF diag(1,1,123336); these are different matrix invariants.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "E": derived["edge_matrix"],
        "cell_order": derived["cell_order"],
        "stable_block_counts": dict(zip(LABELS, derived["stable_block_counts"])),
        "micro_cell_counts": dict(zip(LABELS, derived["micro_cell_counts"])),
        "det": det_e,
        "det_factorization": factor_record(det_e),
        "smith_normal_form": matrix_record(snf_matrix),
        "invariant_factors": snf_diagonal,
        "invariant_factor_product": invariant_product,
        "cokernel": {
            "torsion_invariant_factors": nontrivial_factors,
            "torsion_decomposition": "Z/3 + Z/3450",
            "large_factor_factorization": factor_record(large_factor),
        },
        "factorizations": {
            "det_E": factor_record(det_e),
            "snf_factor_3": factor_record(3),
            "snf_factor_3450": factor_record(large_factor),
        },
        "small_factors_fibonacci": {
            "small_invariant_factors": small_invariant_factors,
            "fibonacci_indices": [2, 2, 4],
            "fibonacci_values": expected_small_fibonacci,
            "large_factor_is_fibonacci": large_factor_is_fibonacci,
            "large_factor": large_factor,
            "fibonacci_neighbors": {"below": 2584, "above": 4181},
        },
        "structural_distinction": {
            "edge_matrix_snf": snf_diagonal,
            "reduced_laplacian_snf": REDUCED_LAPLACIAN_SNF_DIAGONAL,
            "note": "The edge-flux matrix E and the reduced Laplacian are different integer matrices, so their Smith normal forms record different invariants.",
        },
        "not_claimed": [
            "no physical-constant identification",
            "the large invariant factor 3450 is not Fibonacci; no global Fibonacci forcing of the full SNF is claimed",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

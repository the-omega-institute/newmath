#!/usr/bin/env python3
"""Forward no-go audit for deriving the Window6 fold-gauge operator from E.

The audit uses exact rational/integer linear algebra. It certifies a boundary:
the paper-sourced fold-gauge operator A_0 has directed non-normal and defective
Jordan structure that is absent from the symmetric edge matrix E and the coarse
Markov kernel T. No physical constant identification is made.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Any

import sympy as sp


LABELS = ["U_2", "U_1", "U_L", "U_R"]
FIB_WEIGHTS = (1, 2, 3, 5, 8, 13)
EXPECTED_EDGE_MATRIX = [
    [28, 63, 23, 20],
    [63, 21, 21, 6],
    [23, 21, 2, 6],
    [20, 6, 6, 2],
]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def matrix_fraction_record(matrix: list[list[Fraction]]) -> list[list[dict[str, int]]]:
    return [[fraction_record(value) for value in row] for row in matrix]


def matrix_record(matrix: sp.Matrix) -> list[list[int]]:
    return [[int(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


def sympy_matrix_record(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


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


def derive_window6_edge_kernel() -> dict[str, Any]:
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

    sizes = [len(cell) for cell in micro_cells]
    kernel: list[list[Fraction]] = []
    for row_index in range(4):
        row: list[Fraction] = []
        for column_index in range(4):
            denominator = 6 * sizes[row_index]
            if row_index == column_index:
                row.append(Fraction(2 * edge_matrix[row_index][row_index], denominator))
            else:
                row.append(Fraction(edge_matrix[row_index][column_index], denominator))
        kernel.append(row)

    return {
        "cell_order": LABELS,
        "stable_block_counts": [len(block) for block in stable_blocks],
        "micro_cell_counts": sizes,
        "edge_matrix": edge_matrix,
        "kernel": kernel,
    }


def main() -> None:
    lam = sp.symbols("lambda")
    data = derive_window6_edge_kernel()
    a0 = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 2), 0, sp.Rational(1, 2)],
            [0, 0, sp.Rational(1, 2), 0],
            [sp.Rational(1, 2), 1, 0, 0],
            [sp.Rational(1, 2), 0, 0, 0],
        ]
    )
    edge = sp.Matrix(data["edge_matrix"])
    kernel = sp.Matrix(
        [[sp.Rational(value.numerator, value.denominator) for value in row] for row in data["kernel"]]
    )

    a0_charpoly = sp.factor(a0.charpoly(lam).as_expr())
    expected_a0_charpoly = sp.factor((lam - 1) * (2 * lam - 1) * (2 * lam + 1) ** 2 / 8)
    a0_spectrum = a0.eigenvals()
    neghalf_rank = (a0 + sp.Rational(1, 2) * sp.eye(4)).rank()
    neghalf_geometric_multiplicity = 4 - neghalf_rank
    nonnormality = sp.factor(a0 * a0.T - a0.T * a0)

    edge_charpoly = sp.factor(edge.charpoly(lam).as_expr())
    edge_eigenvalues_numeric = sorted(float(root) for root in sp.nroots(edge_charpoly))
    edge_powers = [sp.eye(4), edge, edge**2, edge**3]
    edge_power_antisymmetric_parts = [power - power.T for power in edge_powers]
    antisymmetric_a0 = a0 - a0.T
    edge_commutator = sp.factor(a0 * edge - edge * a0)

    kernel_charpoly = sp.factor(kernel.charpoly(lam).as_expr())
    kernel_commutator = sp.factor(a0 * kernel - kernel * a0)
    a0_spectrum_set = set(a0_spectrum.keys())
    kernel_spectrum_set = set(kernel.eigenvals().keys())

    checks = [
        check(
            "a0_nonnormal",
            nonnormality != sp.zeros(4),
            "A_0 A_0^T - A_0^T A_0 is nonzero, so the paper-sourced fold-gauge operator is non-normal.",
        ),
        check(
            "a0_defective_jordan",
            sp.simplify(a0_charpoly - expected_a0_charpoly) == 0
            and a0_spectrum == {sp.Integer(1): 1, sp.Rational(1, 2): 1, sp.Rational(-1, 2): 2}
            and neghalf_geometric_multiplicity == 1,
            "The eigenvalue -1/2 has algebraic multiplicity 2 and geometric multiplicity 1, hence one 2x2 Jordan block.",
        ),
        check(
            "edge_symmetric_normal",
            data["edge_matrix"] == EXPECTED_EDGE_MATRIX and edge == edge.T,
            "The forward-enumerated edge matrix E is symmetric, hence normal over the real inner product.",
        ),
        check(
            "a0_not_polynomial_in_E",
            all(part == sp.zeros(4) for part in edge_power_antisymmetric_parts)
            and antisymmetric_a0 != sp.zeros(4),
            "Every polynomial in the symmetric matrix E is symmetric, while A_0 has a nonzero antisymmetric part; therefore A_0 is not in span{I,E,E^2,E^3}.",
        ),
        check(
            "a0_E_noncommute",
            edge_commutator != sp.zeros(4),
            "The commutator [A_0,E]=A_0E-EA_0 is nonzero, so A_0 and E are not simultaneously diagonalized by a common eigenbasis.",
        ),
        check(
            "a0_T_noncommute_spectrum",
            kernel_commutator != sp.zeros(4) and a0_spectrum_set != kernel_spectrum_set,
            "The commutator [A_0,T] is nonzero and spec(A_0) differs from the coarse Markov-kernel spectrum.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "A_0": sympy_matrix_record(a0),
        "E": data["edge_matrix"],
        "T": matrix_fraction_record(data["kernel"]),
        "cell_order": data["cell_order"],
        "stable_block_counts": dict(zip(LABELS, data["stable_block_counts"])),
        "micro_cell_counts": dict(zip(LABELS, data["micro_cell_counts"])),
        "nonnormality": {
            "A0_A0T_minus_A0T_A0": sympy_matrix_record(nonnormality),
            "nonzero": nonnormality != sp.zeros(4),
            "conclusion": "A_0 is non-normal.",
        },
        "jordan": {
            "charpoly": str(a0_charpoly),
            "spectrum_with_algebraic_multiplicity": {
                "1": 1,
                "1/2": 1,
                "-1/2": 2,
            },
            "rank_A0_plus_half_I": neghalf_rank,
            "geometric_multiplicity_at_minus_half": neghalf_geometric_multiplicity,
            "conclusion": "-1/2 has algebraic multiplicity 2 and geometric multiplicity 1, hence one 2x2 Jordan block.",
        },
        "edge_matrix": {
            "symmetric": edge == edge.T,
            "normal_reason": "A real symmetric matrix is normal, and every polynomial in E is again symmetric.",
            "charpoly": str(edge_charpoly),
            "eigenvalues_numeric": [f"{value:.15f}" for value in edge_eigenvalues_numeric],
        },
        "polynomial_nogo": {
            "basis": ["I", "E", "E^2", "E^3"],
            "basis_antisymmetric_parts_zero": all(part == sp.zeros(4) for part in edge_power_antisymmetric_parts),
            "A0_antisymmetric_part": sympy_matrix_record(antisymmetric_a0),
            "A0_antisymmetric_part_nonzero": antisymmetric_a0 != sp.zeros(4),
            "conclusion": "A_0 is not a polynomial in E and not in the commutative polynomial algebra generated by E.",
        },
        "commutators": {
            "A0E_minus_EA0": matrix_record(edge_commutator),
            "A0E_minus_EA0_nonzero": edge_commutator != sp.zeros(4),
            "A0T_minus_TA0": sympy_matrix_record(kernel_commutator),
            "A0T_minus_TA0_nonzero": kernel_commutator != sp.zeros(4),
        },
        "spectra": {
            "A_0": {
                "charpoly": str(a0_charpoly),
                "eigenvalues_with_multiplicity": {"1": 1, "1/2": 1, "-1/2": 2},
            },
            "E": {
                "charpoly": str(edge_charpoly),
                "eigenvalues_numeric": [f"{value:.15f}" for value in edge_eigenvalues_numeric],
            },
            "T": {
                "charpoly": str(kernel_charpoly),
                "eigenvalues_numeric": [f"{float(value):.15f}" for value in sorted(sp.nroots(kernel_charpoly), key=lambda x: float(sp.re(x)))],
            },
            "A0_spectrum_equals_T_spectrum": a0_spectrum_set == kernel_spectrum_set,
        },
        "boundary_conclusion": (
            "The directed non-normal and defective Jordan structure of A_0 is absent from the symmetric edge matrix E "
            "and from the coarse stochastic kernel T; A_0 therefore requires an independent fold-gauge definition."
        ),
        "not_claimed": [
            "no physical-constant identification",
            "A_0 is paper-sourced; this anchor certifies the boundary (A_0 not derivable from E/T/partition), it does NOT derive A_0; A_0's Window6 first-principles origin remains an open obligation",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

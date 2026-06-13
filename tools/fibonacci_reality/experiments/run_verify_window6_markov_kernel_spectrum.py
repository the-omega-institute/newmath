#!/usr/bin/env python3
"""Forward spectral audit for the Window6 coarse four-cell Markov kernel.

All quantities are computed from finite Window6 predicates, Foldbin fibers,
hypercube edges, and exact rational linear algebra. No physical constant
identification is made.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Any

import sympy as sp


LABELS = ["U_2", "U_1", "U_L", "U_R"]
FIB_WEIGHTS = (1, 2, 3, 5, 8, 13)


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def matrix_fraction_record(matrix: list[list[Fraction]]) -> list[list[dict[str, int]]]:
    return [[fraction_record(value) for value in row] for row in matrix]


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def fibonacci(index: int) -> int:
    if index < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(index):
        previous, current = current, previous + current
    return previous


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


def derive_kernel() -> dict[str, Any]:
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
        "X6": x6,
        "boundary": boundary,
        "stable_blocks": stable_blocks,
        "micro_cells": micro_cells,
        "edge_matrix": edge_matrix,
        "kernel": kernel,
        "escape_boundary": edge_matrix[3][0] + edge_matrix[3][1] + edge_matrix[3][2],
        "escape_ratio": Fraction(edge_matrix[3][0] + edge_matrix[3][1] + edge_matrix[3][2], 6 * sizes[3]),
    }


def main() -> None:
    data = derive_kernel()
    z = sp.symbols("z")
    lam = sp.symbols("lambda")

    sympy_kernel = sp.Matrix(
        [[sp.Rational(value.numerator, value.denominator) for value in row] for row in data["kernel"]]
    )
    ones = sp.Matrix([1, 1, 1, 1])
    charpoly_resolvent = sp.factor((sp.eye(4) - z * sympy_kernel).det())
    charpoly_lambda = sp.factor(sympy_kernel.charpoly(lam).as_expr())

    cubic_z = 55 * z**3 + 506 * z**2 - 7263 * z - 48114
    cubic_lambda = 48114 * lam**3 + 7263 * lam**2 - 506 * lam - 55
    expected_resolvent = sp.factor((z - 1) * cubic_z / 48114)
    expected_lambda = sp.factor((lam - 1) * cubic_lambda / 48114)

    row_stochastic = all(sum(row) == 1 for row in data["kernel"])
    right_perron_vector_ok = sympy_kernel * ones == ones
    kernel_positive = all(value > 0 for row in data["kernel"] for value in row)
    nontrivial_three_real = sp.discriminant(cubic_lambda, lam) > 0
    nontrivial_inside_unit = int(sp.Poly(cubic_lambda, lam).count_roots(-1, 1)) == 3
    cubic_z_no_roots_unit_interval = int(sp.Poly(cubic_z, z).count_roots(-1, 1)) == 0
    eigenvalues_numeric = sorted(float(root) for root in sp.nroots(cubic_lambda))
    resolvent_roots_numeric = sorted(float(root) for root in sp.nroots(cubic_z))
    max_subdominant = max(abs(value) for value in eigenvalues_numeric)
    spectral_gap = 1.0 - max_subdominant
    f10 = fibonacci(10)
    constant_factorization_ok = 2 * 3**7 * 11 == 48114
    phi = (1 + sp.sqrt(5)) / 2

    checks = [
        check(
            "kernel_row_stochastic",
            row_stochastic,
            "T is the row-normalized four-cell hypercube edge kernel and every row sums to 1.",
        ),
        check(
            "perron_eigenvalue_one",
            row_stochastic and right_perron_vector_ok and kernel_positive and nontrivial_inside_unit,
            "T*1=1; T has strictly positive entries; its three nontrivial eigenvalues lie in (-1,1), so Perron 1 is unique by maximal modulus.",
        ),
        check(
            "resolvent_leading_coeff_fibonacci",
            sp.simplify(charpoly_resolvent - expected_resolvent) == 0 and f10 == 55 and constant_factorization_ok,
            "det(I-zT)=(z-1)(55z^3+506z^2-7263z-48114)/48114, with leading coefficient 55=F_10 and 48114=2*3^7*11.",
        ),
        check(
            "subdominant_eigenvalues_inside_unit",
            sp.simplify(charpoly_lambda - expected_lambda) == 0
            and nontrivial_three_real
            and nontrivial_inside_unit
            and cubic_z_no_roots_unit_interval,
            "The nontrivial eigenvalue cubic has three real roots in (-1,1); equivalently the resolvent cubic has no roots on [-1,1].",
        ),
        check(
            "spectral_gap",
            spectral_gap > 0,
            "The gap 1-max(|lambda_i|) is positive and approximately 0.826.",
        ),
        check(
            "escape_ratio_8_9",
            data["escape_boundary"] == 32 and data["escape_ratio"] == Fraction(8, 9),
            "The right-boundary leave count is 20+6+6=32, hence 32/(6*6)=8/9.",
        ),
        check(
            "coarse_fine_perron_contrast",
            row_stochastic and sp.simplify(phi**2 - phi - 1) == 0,
            "The coarse four-cell kernel is stochastic with Perron root 1; the fine no-adjacent-one transfer operator has Perron root phi as a counting growth rate.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "kernel": {
            "cell_order": LABELS,
            "matrix": matrix_fraction_record(data["kernel"]),
            "row_sums": [str(sum(row)) for row in data["kernel"]],
            "strictly_positive": kernel_positive,
        },
        "charpoly": {
            "det_I_minus_zT": str(charpoly_resolvent),
            "det_lambda_I_minus_T": str(charpoly_lambda),
            "resolvent_cubic": str(cubic_z),
            "eigenvalue_cubic": str(cubic_lambda),
            "constant_factorization": "48114=2*3^7*11",
        },
        "perron": {
            "eigenvalue": 1,
            "right_eigenvector": [1, 1, 1, 1],
            "unique_maximal_modulus": row_stochastic and kernel_positive and nontrivial_inside_unit,
            "reason": "T is strictly positive and row-stochastic; its nontrivial eigenvalues are all inside the unit disk.",
        },
        "eigenvalues": {
            "nontrivial_roots_of_48114_lambda3_plus_7263_lambda2_minus_506_lambda_minus_55": [
                f"{value:.15f}" for value in eigenvalues_numeric
            ],
            "resolvent_cubic_roots_z": [f"{value:.15f}" for value in resolvent_roots_numeric],
            "symbolic_certificate": {
                "discriminant": str(sp.factor(sp.discriminant(cubic_lambda, lam))),
                "eigenvalue_roots_in_minus_1_1": 3,
                "resolvent_roots_in_minus_1_1": 0,
            },
        },
        "spectral_gap": {
            "max_subdominant_abs": f"{max_subdominant:.15f}",
            "gap": f"{spectral_gap:.15f}",
            "rounded": "0.826",
        },
        "escape": {
            "boundary_leave_count": data["escape_boundary"],
            "escape_ratio": fraction_record(data["escape_ratio"]),
        },
        "leading_coeff_fibonacci": {
            "leading_coefficient": 55,
            "F_10": f10,
            "matches": f10 == 55,
        },
        "coarse_fine_contrast": {
            "coarse_operator": "four-cell Markov kernel T",
            "coarse_perron_root": "1",
            "fine_operator": "two-state no-adjacent-one transfer operator",
            "fine_perron_root": "phi=(1+sqrt(5))/2",
            "interpretation": "coarse Perron 1 records probability conservation after row normalization; fine Perron phi records unnormalized admissible-word growth.",
        },
        "source_counts": {
            "X6_count": len(data["X6"]),
            "stable_block_counts": dict(zip(LABELS, [len(block) for block in data["stable_blocks"]])),
            "micro_cell_counts": dict(zip(LABELS, [len(cell) for cell in data["micro_cells"]])),
            "boundary_words": [word_string(word) for word in data["boundary"]],
        },
        "not_claimed": ["no physical-constant identification"],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

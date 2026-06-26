#!/usr/bin/env python3
"""Forward arithmetic link between the Window6 Green response and SNF torsion.

All quantities are computed from finite Window6 predicates, exact rational
linear algebra, integer factorization, and Smith normal form. No physical
constant identification is made.
"""

from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Any

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


LABELS = ["U_2", "U_1", "U_L", "U_R"]
FIB_WEIGHTS = (1, 2, 3, 5, 8, 13)
TORSION_PRIME = 571
SNF_INVARIANT = 123336


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def factor_record(value: int) -> dict[str, int]:
    return {str(prime): exponent for prime, exponent in sorted(sp.factorint(value).items())}


def matrix_record(matrix: sp.Matrix) -> list[list[int]]:
    return [[int(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


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


def derive_green_response() -> dict[str, Any]:
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

    z = sp.symbols("z")
    sympy_kernel = sp.Matrix(
        [[sp.Rational(value.numerator, value.denominator) for value in row] for row in kernel]
    )
    pi = [sp.Rational(size, 64) for size in sizes]
    f_r = sp.Matrix([-pi[3], -pi[3], -pi[3], 1 - pi[3]])
    resolvent = sp.eye(4) - z * sympy_kernel
    chi_r = sp.factor((f_r.T * sp.diag(*pi) * resolvent.inv() * f_r)[0])
    delta_r = sp.factor(2 * (chi_r - chi_r.subs(z, 0)))

    return {
        "z": z,
        "cell_sizes": dict(zip(LABELS, sizes)),
        "edge_matrix": edge_matrix,
        "kernel": kernel,
        "Delta_R": delta_r,
        "Delta_R_1": sp.factor(delta_r.subs(z, 1)),
        "det_I_minus_zT": sp.factor(resolvent.det()),
    }


def reduced_laplacian_from_edge_matrix(edge_matrix: list[list[int]]) -> sp.Matrix:
    adjacency = sp.Matrix(
        [
            [0 if row == column else edge_matrix[row][column] for column in range(4)]
            for row in range(4)
        ]
    )
    degree = sp.diag(*[sum(adjacency[row, column] for column in range(4)) for row in range(4)])
    laplacian = degree - adjacency
    reduced = laplacian.copy()
    reduced.row_del(3)
    reduced.col_del(3)
    return reduced


def main() -> None:
    green = derive_green_response()
    delta_r_1 = green["Delta_R_1"]
    delta_fraction = Fraction(int(delta_r_1.p), int(delta_r_1.q))
    denominator_factors = sp.factorint(delta_fraction.denominator)
    numerator_factors = sp.factorint(delta_fraction.numerator)
    denominator_odd_primes = sorted(prime for prime in denominator_factors if prime % 2 == 1)

    laplacian = reduced_laplacian_from_edge_matrix(green["edge_matrix"])
    snf_matrix = smith_normal_form(laplacian, domain=sp.ZZ)
    snf_diagonal = [abs(int(snf_matrix[index, index])) for index in range(min(snf_matrix.rows, snf_matrix.cols))]
    snf_max = max(snf_diagonal)
    snf_factors = sp.factorint(snf_max)
    snf_primes = set(snf_factors)
    denominator_primes = set(denominator_factors)
    common_primes = sorted(snf_primes & denominator_primes)
    common_large_odd_primes = sorted(prime for prime in common_primes if prime > 3 and prime % 2 == 1)

    expected_delta = sp.Rational(26401, 2**13 * TORSION_PRIME)
    expected_det = sp.factor(
        (green["z"] - 1)
        * (55 * green["z"] ** 3 + 506 * green["z"] ** 2 - 7263 * green["z"] - 48114)
        / 48114
    )

    checks = [
        check(
            "delta_r_one_value",
            delta_r_1 == expected_delta,
            "Delta_R(1) is forward-computed from the finite Green resolvent and equals 26401/(2^13*571).",
        ),
        check(
            "delta_r_one_denominator_prime_571",
            denominator_factors == {2: 13, TORSION_PRIME: 1}
            and numerator_factors == {17: 1, 1553: 1}
            and denominator_odd_primes == [TORSION_PRIME],
            "The reduced denominator factors as 2^13*571; the numerator factors as 17*1553; the only odd denominator prime is 571.",
        ),
        check(
            "laplacian_snf_invariant_571",
            snf_diagonal == [1, 1, SNF_INVARIANT]
            and snf_max == SNF_INVARIANT
            and snf_factors == {2: 3, 3: 3, TORSION_PRIME: 1},
            "The reduced Laplacian carrier has Smith normal form diag(1,1,123336), and 123336=2^3*3^3*571.",
        ),
        check(
            "common_torsion_prime",
            common_large_odd_primes == [TORSION_PRIME],
            "The prime 571 divides both the Delta_R(1) denominator and the maximal Smith invariant; it is their unique common odd prime above 3.",
        ),
        check(
            "resolvent_link",
            sp.simplify(green["det_I_minus_zT"] - expected_det) == 0
            and common_large_odd_primes == [TORSION_PRIME],
            "Delta_R(z)=2(chi_R(z)-chi_R(0)) is computed through (I-zT)^(-1); the torsion prime 571 carried by the Laplacian/SNF endpoint also appears in the boundary resolvent denominator at z=1.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "delta_r_1": fraction_record(delta_fraction),
        "factorizations": {
            "delta_r_1_numerator": factor_record(delta_fraction.numerator),
            "delta_r_1_denominator": factor_record(delta_fraction.denominator),
            "snf_max_invariant": factor_record(snf_max),
        },
        "green_resolvent": {
            "Delta_R_z": str(green["Delta_R"]),
            "det_I_minus_zT": str(green["det_I_minus_zT"]),
            "cell_sizes": green["cell_sizes"],
            "edge_matrix": green["edge_matrix"],
        },
        "snf": {
            "reduced_laplacian_from_edge_matrix": matrix_record(laplacian),
            "smith_normal_form": matrix_record(snf_matrix),
            "diagonal": snf_diagonal,
            "max_invariant": snf_max,
        },
        "common_prime": {
            "prime": TORSION_PRIME,
            "delta_r_1_denominator_divisible": delta_fraction.denominator % TORSION_PRIME == 0,
            "snf_max_invariant_divisible": snf_max % TORSION_PRIME == 0,
            "common_primes": common_primes,
            "common_large_odd_primes": common_large_odd_primes,
            "interpretation": "571 is the shared torsion prime between the reduced Laplacian SNF endpoint and the Green boundary resolvent denominator.",
        },
        "not_claimed": ["no physical-constant identification"],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

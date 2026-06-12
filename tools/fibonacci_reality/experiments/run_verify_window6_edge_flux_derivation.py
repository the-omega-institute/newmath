#!/usr/bin/env python3
"""Forward finite certificate for the Window6 edge-flux and Green response.

Forbidden: do not infer the block predicate from target sizes; do not infer T from Delta_R(z);
do not use alpha or any physical constant. All quantities are forward-enumerated from finite predicates.
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
    return {"name": name, "passed": passed, "reason": reason}


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def matrix_fraction_record(matrix: list[list[Fraction]]) -> list[list[dict[str, int]]]:
    return [[fraction_record(value) for value in row] for row in matrix]


def sympy_fraction_matrix_record(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


def word_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def v6(word: tuple[int, ...]) -> int:
    return sum(bit * FIB_WEIGHTS[index] for index, bit in enumerate(word))


def fib(index: int) -> int:
    if index < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    if index == 0:
        return 0
    previous, current = 1, 1
    if index <= 2:
        return 1
    for _ in range(3, index + 1):
        previous, current = current, previous + current
    return current


def foldbin_fiber(word: tuple[int, ...]) -> set[int]:
    fiber: set[int] = set()
    for c7, c8, c9 in product((0, 1), repeat=3):
        if c7 * c8 or c8 * c9 or word[5] * c7:
            continue
        value = v6(word) + 21 * c7 + 34 * c8 + 55 * c9
        if value <= 63:
            fiber.add(value)
    return fiber


def derive() -> dict[str, Any]:
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

    pi = [Fraction(size, 64) for size in sizes]
    escape_boundary = edge_matrix[3][0] + edge_matrix[3][1] + edge_matrix[3][2]
    escape_ratio = Fraction(escape_boundary, 6 * sizes[3])
    chi_r0 = pi[3] * (1 - pi[3])

    z = sp.symbols("z")
    sympy_kernel = sp.Matrix(
        [[sp.Rational(value.numerator, value.denominator) for value in row] for row in kernel]
    )
    resolvent_denominator = sp.eye(4) - z * sympy_kernel
    sympy_pi = [sp.Rational(value.numerator, value.denominator) for value in pi]
    f_r = sp.Matrix([-sympy_pi[3], -sympy_pi[3], -sympy_pi[3], 1 - sympy_pi[3]])
    chi_r = sp.factor((f_r.T * sp.diag(*sympy_pi) * resolvent_denominator.inv() * f_r)[0])
    delta_r = sp.factor(2 * (chi_r - chi_r.subs(z, 0)))
    charpoly = sp.factor(resolvent_denominator.det())

    return {
        "X6": x6,
        "boundary": boundary,
        "stable_blocks": stable_blocks,
        "micro_cells": micro_cells,
        "edge_matrix": edge_matrix,
        "kernel": kernel,
        "pi": pi,
        "escape_boundary": escape_boundary,
        "escape_ratio": escape_ratio,
        "chi_R_0": Fraction(int(chi_r.subs(z, 0).p), int(chi_r.subs(z, 0).q)),
        "chi_R_0_direct": chi_r0,
        "Delta_R": delta_r,
        "Delta_R_0": sp.factor(delta_r.subs(z, 0)),
        "Delta_R_1": sp.factor(delta_r.subs(z, 1)),
        "charpoly": charpoly,
        "z": z,
    }


def main() -> None:
    data = derive()
    z = data["z"]
    lam = sp.symbols("lam")

    expected_edge_matrix = [[28, 63, 23, 20], [63, 21, 21, 6], [23, 21, 2, 6], [20, 6, 6, 2]]
    expected_delta_r = sp.factor(
        -3 * z * (1595 * z**2 + 24477 * z + 26730)
        / (512 * (55 * z**3 + 506 * z**2 - 7263 * z - 48114))
    )
    expected_charpoly = sp.factor((z - 1) * (55 * z**3 + 506 * z**2 - 7263 * z - 48114) / 48114)
    phi = sp.Rational(1, 2) * (1 + sp.sqrt(5))
    u = sp.symbols("u")
    D = sp.symbols("D")
    q0 = sp.Integer(1)
    q1 = -sp.Rational(1, 2)
    q2 = sp.Rational(8, 9)
    Q6_alpha = q0 + q1 * u + q2 * u**2
    s6 = 6 + 1
    dstar_assembly_left = sp.factor(47 + phi**-s6 * Q6_alpha.subs(u, phi**-10))
    dstar_assembly_right = sp.factor(
        47 + phi**-7 - sp.Rational(1, 2) * phi**-17 + sp.Rational(8, 9) * phi**-27
    )
    C6 = sp.Rational(1, 2) + sp.Rational(1, 4) * sp.cos(sp.pi / phi) ** 2 + 1 / (D * phi**5)
    R6_from_fibonacci = 2 * sp.pi * (fib(8) + fib(9) * C6) / (
        fib(8) * phi ** -(fib(5) + fib(2)) + fib(9) * C6 * phi ** -(fib(5) + fib(3))
    )
    R6_readout = 2 * sp.pi * (21 + 34 * C6) / (21 * phi**-6 + 34 * C6 * phi**-7)
    a0 = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 2), 0, sp.Rational(1, 2)],
            [0, 0, sp.Rational(1, 2), 0],
            [sp.Rational(1, 2), 1, 0, 0],
            [sp.Rational(1, 2), 0, 0, 0],
        ]
    )
    expected_a0_charpoly = sp.factor((lam - 1) * (2 * lam - 1) * (2 * lam + 1) ** 2 / 8)
    a0_charpoly = sp.factor(a0.charpoly(lam).as_expr())
    a0_eigenvals = a0.eigenvals()
    neghalf_kernel_rank = (a0 + sp.Rational(1, 2) * sp.eye(4)).rank()
    neghalf_geometric_multiplicity = 4 - neghalf_kernel_rank
    parry_kernel = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 4), 0, sp.Rational(1, 4)],
            [0, 0, 1, 0],
            [sp.Rational(1, 2), sp.Rational(1, 2), 0, 0],
            [1, 0, 0, 0],
        ]
    )
    parry_charpoly = sp.factor(parry_kernel.charpoly(lam).as_expr())
    parry_row_stochastic = all(sum(parry_kernel[row, column] for column in range(4)) == 1 for row in range(4))

    x6_count = len(data["X6"])
    stable_counts = [len(block) for block in data["stable_blocks"]]
    boundary_words = [word_string(word) for word in data["boundary"]]
    micro_counts = [len(cell) for cell in data["micro_cells"]]
    union_vertices = set().union(*data["micro_cells"])
    partition_ok = (
        len(union_vertices) == 64
        and union_vertices == set(range(64))
        and sum(len(cell) for cell in data["micro_cells"]) == 64
    )
    edge_count = sum(data["edge_matrix"][index][index] for index in range(4)) + sum(
        data["edge_matrix"][row][column] for row in range(4) for column in range(row + 1, 4)
    )
    kernel_stochastic = all(sum(row) == 1 for row in data["kernel"])
    stationary_pi = [
        sum(data["pi"][row] * data["kernel"][row][column] for row in range(4))
        for column in range(4)
    ]
    stationary_ok = stationary_pi == data["pi"]
    delta_r_equal = sp.simplify(data["Delta_R"] - expected_delta_r) == 0
    charpoly_equal = sp.simplify(data["charpoly"] - expected_charpoly) == 0
    fib_le_63 = [(index, fib(index)) for index in range(0, 12) if fib(index) <= 63]
    rho6 = max(index for index, value in fib_le_63 if value <= 63)

    checks = [
        check(
            "stable_blocks_9_6_3_3",
            x6_count == 21 and stable_counts == [9, 6, 3, 3] and boundary_words == ["100001", "100101", "101001"],
            "X_6 has 21 words; cyclic/boundary and weight predicates yield blocks 9,6,3,3 with boundary 100001,100101,101001",
        ),
        check(
            "micro_blocks_27_22_9_6",
            micro_counts == [27, 22, 9, 6],
            "Foldbin tail-cube fibers yield micro-cell sizes 27,22,9,6",
        ),
        check(
            "partition_of_64",
            partition_ok,
            "the four micro-cells are disjoint and cover vertices 0..63",
        ),
        check(
            "edge_matrix_E",
            data["edge_matrix"] == expected_edge_matrix and edge_count == 192,
            "Q_6 edge enumeration yields E and 192 undirected hypercube edges",
        ),
        check(
            "kernel_T_stochastic",
            kernel_stochastic,
            "T_aa=2E_aa/(6|U_a|), T_ab=E_ab/(6|U_a|) gives row sums equal to 1",
        ),
        check(
            "stationary_pi",
            stationary_ok,
            "pi=(27,22,9,6)/64 is stationary for the enumerated kernel",
        ),
        check(
            "escape_8_9",
            data["escape_boundary"] == 32 and data["escape_ratio"] == Fraction(8, 9),
            "right-boundary leave count is 20+6+6=32, so 32/(6*6)=8/9",
        ),
        check(
            "chi_R_0_87_1024",
            data["chi_R_0"] == Fraction(87, 1024) and data["chi_R_0_direct"] == Fraction(87, 1024),
            "chi_R(0)=pi_R(1-pi_R)=87/1024",
        ),
        check(
            "delta_R_0",
            data["Delta_R_0"] == 0,
            "Delta_R(0)=2(chi_R(0)-chi_R(0))=0",
        ),
        check(
            "delta_R_z_rational",
            delta_r_equal,
            "Delta_R(z) equals the rational expression obtained from the forward-enumerated T resolvent",
        ),
        check(
            "delta_R_1_571",
            data["Delta_R_1"] == sp.Rational(26401, 2**13 * 571),
            "Delta_R(1)=26401/(2^13*571)",
        ),
        check(
            "charpoly_markov",
            charpoly_equal,
            "det(I-zT)=(z-1)(55z^3+506z^2-7263z-48114)/48114",
        ),
        check(
            "coarse_residual_ledger_47",
            fib(9) + fib(7) == 47 and fib(10) - fib(6) == 47,
            "D_0=47=F_9+F_7=F_10-F_6 with F_6=8,F_7=13,F_9=34,F_10=55",
        ),
        check(
            "seam_s6_formula",
            s6 == 6 + 1 == 7,
            "s_6=m+1=7 by definition; this is not a residual-seam forcedness proof",
        ),
        check(
            "rho6_formula",
            fib(10) == 55 and fib(11) == 89 and fib(10) <= 63 < fib(11) and rho6 == 10,
            "rho_6=max{k:F_k<=2^6-1}=10 because F_10=55<=63<F_11=89; this is not a local-return forcedness proof",
        ),
        check(
            "functor_expansion",
            sp.simplify(dstar_assembly_left - dstar_assembly_right) == 0,
            "definition expansion: Rcal_6(47,Q)=47+phi^-7-(1/2)phi^-17+(8/9)phi^-27; NOT a forcedness proof",
        ),
        check(
            "R6_readout_definition",
            sp.simplify(R6_from_fibonacci - R6_readout) == 0,
            "definition expansion: R_6(D)=2*pi*(21+34 C_6(D))/(21 phi^-6+34 C_6(D) phi^-7) with C_6(D)=1/2+1/4 cos^2(pi/phi)+1/(D phi^5); no value at D*_6 is evaluated",
        ),
        check(
            "a0_charpoly",
            sp.simplify(a0_charpoly - expected_a0_charpoly) == 0,
            "the explicit paper-sourced A_0 has det(lam I - A_0)=(lam-1)(2lam-1)(2lam+1)^2/8 by exact rational linear algebra",
        ),
        check(
            "a0_spectrum",
            a0_eigenvals == {sp.Integer(1): 1, sp.Rational(1, 2): 1, sp.Rational(-1, 2): 2},
            "spec(A_0)={1,1/2,-1/2}, with algebraic multiplicity 2 at -1/2",
        ),
        check(
            "neghalf_jordan_2x2",
            neghalf_kernel_rank == 3 and neghalf_geometric_multiplicity == 1,
            "rank(A_0+(1/2)I)=3, so the -1/2 eigenspace is one-dimensional and the algebraic multiplicity two is one 2x2 Jordan block",
        ),
        check(
            "parry_kernel_same_spectrum",
            parry_row_stochastic and sp.simplify(parry_charpoly - expected_a0_charpoly) == 0,
            "the Parry kernel P is row-stochastic and has the same characteristic polynomial as A_0",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "status": status,
        "checks": checks,
        "result": {
            "anti_fit_guard": "All displayed quantities are outputs of finite predicates: X_6 enumeration, stable four-block decomposition, Foldbin tail-cube fibers, Q_6 edge enumeration, and rational Green resolvent.",
            "paper_sourced_inputs": [
                "A_0 fold-gauge operator (uniform-baseline mismatch-indicator weighted adjacency)",
            ],
            "X6_count": x6_count,
            "stable_block_counts": dict(zip(LABELS, stable_counts)),
            "boundary_words": boundary_words,
            "micro_cell_counts": dict(zip(LABELS, micro_counts)),
            "partition_vertex_count": len(union_vertices),
            "edge_count_Q6": edge_count,
            "E": data["edge_matrix"],
            "T": matrix_fraction_record(data["kernel"]),
            "pi": [fraction_record(value) for value in data["pi"]],
            "escape_boundary": data["escape_boundary"],
            "escape_ratio": fraction_record(data["escape_ratio"]),
            "chi_R_0": fraction_record(data["chi_R_0"]),
            "Delta_R_z": str(data["Delta_R"]),
            "Delta_R_0": str(data["Delta_R_0"]),
            "Delta_R_1": str(data["Delta_R_1"]),
            "Delta_R_1_denominator_factor": "2^13*571",
            "charpoly_markov": str(data["charpoly"]),
            "coarse_residual_ledger": {
                "D_0": 47,
                "F_9_plus_F_7": fib(9) + fib(7),
                "F_10_minus_F_6": fib(10) - fib(6),
            },
            "golden_local_response_indices": {
                "s_6": 7,
                "rho_6": rho6,
                "tail_bound": "F_10=55<=63<F_11=89",
            },
            "definition_ready": [
                "R_6 readout function",
                "GoldenLocalResponseFunctor_6 (rho_m=max{k:F_k<=2^m-1}, s_m=m+1)",
            ],
            "dstar_assembly_identity": (
                "D_0+phi^-7 Q(phi^-10)=47+phi^-7-(1/2)phi^-17+(8/9)phi^-27 "
                "with Q(u)=1-(1/2)u+(8/9)u^2; definition expansion only, NOT a forcedness proof"
            ),
            "R6_readout_definition": (
                "R_6(D)=2*pi*(21+34 C_6(D))/(21 phi^-6+34 C_6(D) phi^-7), "
                "C_6(D)=1/2+(1/4)cos^2(pi/phi)+1/(D phi^5); no physical readout value is evaluated"
            ),
            "a0_forward_spectral_certificate": {
                "A_0": sympy_fraction_matrix_record(a0),
                "charpoly": str(a0_charpoly),
                "spectrum_with_algebraic_multiplicity": {
                    "1": 1,
                    "1/2": 1,
                    "-1/2": 2,
                },
                "rank_A0_plus_half_I": neghalf_kernel_rank,
                "geometric_multiplicity_at_minus_half": neghalf_geometric_multiplicity,
                "jordan_statement": "-1/2 has algebraic multiplicity 2 and geometric multiplicity 1, hence one 2x2 Jordan block",
                "Parry_kernel_P": sympy_fraction_matrix_record(parry_kernel),
                "Parry_kernel_row_stochastic": parry_row_stochastic,
                "Parry_kernel_charpoly": str(parry_charpoly),
            },
            "obligations_not_verified": [
                "GoldenLocalResponseFunctor forcedness (seam/local-return/forced mapping)",
                "s_6=7 residual-seam forcedness",
                "rho_6=10 local-return forcedness",
                "Delta_R'(z)>0 monotonicity",
                "physical representation bridge R_6(D*)=alpha^-1",
            ],
            "not_claimed": [
                "GoldenLocalResponseFunctor_6 forcedness",
                "R_6(D*_6) as a physical readout",
                "physical constant identification",
            ],
        },
    }
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()

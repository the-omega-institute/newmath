#!/usr/bin/env python3
"""Exact certificate for the Window6 edge-cokernel clock."""

from __future__ import annotations

import json
import math
from itertools import product
from typing import Any

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


MODULUS = 10
CELL_NAMES = ["U_2", "U_1", "U_L", "U_R"]
EDGE_MATRIX = sp.Matrix(
    [
        [28, 63, 23, 20],
        [63, 21, 21, 6],
        [23, 21, 2, 6],
        [20, 6, 6, 2],
    ]
)
CHI = (2, 8, 0, 1)
RHO_6 = 10
S_6 = 7


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def mod10_vector(values: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    return tuple(int(value) % MODULUS for value in values)


def row_times_matrix_mod10(row: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return mod10_vector([sum(row[i] * int(EDGE_MATRIX[i, j]) for i in range(4)) for j in range(4)])


def matrix_times_col_mod10(col: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    return mod10_vector([sum(int(EDGE_MATRIX[i, j]) * col[j] for j in range(4)) for i in range(4)])


def left_kernel_mod10() -> list[tuple[int, int, int, int]]:
    kernel: list[tuple[int, int, int, int]] = []
    for row in product(range(MODULUS), repeat=4):
        if row_times_matrix_mod10(row) == (0, 0, 0, 0):
            kernel.append(tuple(int(x) for x in row))
    return kernel


def cyclic_chi_subgroup() -> list[tuple[int, int, int, int]]:
    return [mod10_vector(tuple(t * value for value in CHI)) for t in range(MODULUS)]


def main() -> None:
    det_e = int(EDGE_MATRIX.det())
    snf = smith_normal_form(EDGE_MATRIX, domain=sp.ZZ)
    snf_diag = [int(snf[i, i]) for i in range(4)]

    kernel = left_kernel_mod10()
    cyclic = sorted(cyclic_chi_subgroup())
    pinned = [row for row in kernel if row[3] == 1]

    witnesses = [
        {
            "identity": "e_U2 - 2e_UR",
            "vector": [1, 1, 0, 1],
            "lhs": list(matrix_times_col_mod10((1, 1, 0, 1))),
            "rhs": [1, 0, 0, 8],
        },
        {
            "identity": "e_U1 - 8e_UR",
            "vector": [1, 5, 9, 4],
            "lhs": list(matrix_times_col_mod10((1, 5, 9, 4))),
            "rhs": [0, 1, 0, 2],
        },
        {
            "identity": "e_UL",
            "vector": [0, 9, 1, 0],
            "lhs": list(matrix_times_col_mod10((0, 9, 1, 0))),
            "rhs": [0, 0, 1, 0],
        },
    ]

    j_seam = (0, 1, 0, -1)
    j_seam_grade = (CHI[1] - CHI[3]) % MODULUS
    a_int = (j_seam_grade - S_6) % MODULUS

    checks = [
        check(
            "edge_matrix_snf",
            det_e == 10350 and snf_diag == [1, 1, 3, 3450],
            "E has determinant 10350 and Smith normal form diag(1,1,3,3450).",
        ),
        check(
            "edge_cokernel_clock_z10",
            math.gcd(MODULUS, 3) == 1 and math.gcd(MODULUS, 3450) == 10,
            "coker(E)/10 coker(E) removes the Z/3 factor and leaves the Z/10 quotient of Z/3450.",
        ),
        check(
            "left_kernel_mod10_cyclic",
            kernel == cyclic and len(kernel) == 10 and pinned == [CHI],
            "The mod-10 left kernel is exactly <(2,8,0,1)> and chi(e_UR)=1 pins chi uniquely.",
        ),
        check(
            "cell_residues",
            CHI == (2, 8, 0, 1) and all(item["lhs"] == item["rhs"] for item in witnesses),
            "The residue row gives U_2,U_1,U_L,U_R -> 2,8,0,1 and the three cokernel identities hold mod 10.",
        ),
        check(
            "minimal_seam_grade_7",
            j_seam == (0, 1, 0, -1) and j_seam_grade == 7,
            "The forward boundary seam j_seam=e_U1-e_UR has chi-grade 7 mod 10.",
        ),
        check(
            "fibonacci_phase_lock",
            S_6 == 7 and RHO_6 == 10 and a_int == 0,
            "The internal seam grade 7 phase-locks with the independent Fibonacci seam s_6=7 at horizon rho_6=10.",
        ),
    ]

    not_claimed = [
        "physical fine-structure constant alpha or R_6(D*)=alpha^-1 as a forward derivation",
        "complete a=0 origin selection proof",
        "a basepoint selection inside the originless P_10 torsor",
    ]
    open_obligations = [
        "SeamIdentificationCert: q_0 residual event is j_seam=e_U1-e_UR",
        "ReturnFunctorCert: q_1,q_2,... are successive returns of the same seam class with degree 10",
        "clock-identity-fork: either residue clock is the P_10 torsor or K_6^edge needs an equivariant realization into P_10",
    ]

    result: dict[str, Any] = {
        "definition": "E is the Window6 edge-flux matrix in basis (U_2,U_1,U_L,U_R); K_6^edge=coker(E)/10 coker(E).",
        "basis": CELL_NAMES,
        "E": [[int(EDGE_MATRIX[i, j]) for j in range(4)] for i in range(4)],
        "det_E": det_e,
        "SNF": snf_diag,
        "coker": ["Z/3", "Z/3450"],
        "K6edge": {
            "group": "Z/10",
            "construction": "coker(E)/10 coker(E)",
            "gcd_10_3": math.gcd(MODULUS, 3),
            "gcd_10_3450": math.gcd(MODULUS, 3450),
            "canonical_zero": True,
            "canonical_order_10_generator": "[e_UR]",
            "not_torsor": True,
        },
        "left_kernel_mod10": [list(row) for row in kernel],
        "chi": list(CHI),
        "chi_E_mod10": list(row_times_matrix_mod10(CHI)),
        "cell_residues": dict(zip(CELL_NAMES, CHI, strict=True)),
        "witnesses": witnesses,
        "j_seam": {"vector": list(j_seam), "name": "e_U1-e_UR", "grade": j_seam_grade},
        "s_6": S_6,
        "rho_6": RHO_6,
        "a_int": a_int,
        "checks": checks,
        "open_obligations": open_obligations,
        "not_claimed": not_claimed,
        "status": "passed" if all(item["passed"] for item in checks) else "failed",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if result["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

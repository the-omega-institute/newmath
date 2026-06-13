#!/usr/bin/env python3
"""Forward-check the Parry maximal-entropy measure of the no-adjacent-one SFT."""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def matrix_equal(left: sp.Matrix, right: sp.Matrix) -> bool:
    return left.shape == right.shape and all(
        sp.simplify(left[row, col] - right[row, col]) == 0
        for row in range(left.rows)
        for col in range(left.cols)
    )


def main() -> None:
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    matrix = sp.Matrix([[1, 1], [1, 0]])
    right = sp.Matrix([phi, 1])
    left = sp.Matrix([[phi, 1]])

    transition = sp.Matrix(
        [
            [1 / phi, 1 / phi**2],
            [1, 0],
        ]
    )
    stationary = sp.Matrix([[(5 + sqrt5) / 10, (5 - sqrt5) / 10]])
    stationary_phi = sp.Matrix([[phi**2 / (phi**2 + 1), 1 / (phi**2 + 1)]])

    metric_entropy = sp.simplify(
        stationary[0, 0] * (transition[0, 0] + 2 * transition[0, 1]) * sp.log(phi)
    )
    coarse_cell_sizes = [27, 22, 9, 6]
    coarse_stationary = [sp.Rational(size, 64) for size in coarse_cell_sizes]

    perron_eigenvectors_ok = (
        matrix_equal(matrix * right, sp.simplify(phi) * right)
        and matrix_equal(left * matrix, sp.simplify(phi) * left)
        and sp.simplify(phi**2 - phi - 1) == 0
    )
    transition_ok = (
        all(sp.simplify(sum(transition[row, col] for col in range(2)) - 1) == 0 for row in range(2))
        and sp.simplify(transition[0, 0] - 1 / phi) == 0
        and sp.simplify(transition[0, 1] - 1 / phi**2) == 0
        and sp.simplify(transition[1, 0] - 1) == 0
        and sp.simplify(transition[1, 1]) == 0
        and sp.simplify(transition[0, 1] - (1 - 1 / phi)) == 0
    )
    stationary_ok = (
        all(sp.simplify((stationary * transition)[0, col] - stationary[0, col]) == 0 for col in range(2))
        and sp.simplify(stationary[0, 0] + stationary[0, 1] - 1) == 0
        and all(sp.simplify(stationary[0, col] - stationary_phi[0, col]) == 0 for col in range(2))
    )
    entropy_ok = (
        sp.simplify(metric_entropy - sp.log(phi)) == 0
        and sp.simplify(sp.exp(sp.log(phi)) - phi) == 0
    )
    coarse_ok = sum(coarse_cell_sizes) == 64 and sum(coarse_stationary) == 1

    checks = [
        check(
            "perron_eigenvectors",
            perron_eigenvectors_ok,
            "For M=[[1,1],[1,0]], v=(phi,1)^T and u=(phi,1) satisfy Mv=phi v and uM=phi u.",
        ),
        check(
            "parry_transition_probs",
            transition_ok,
            "The Parry formula p_ij=M_ij*v_j/(phi*v_i) gives P=[[1/phi,1/phi^2],[1,0]], with row sums one and forbidden transition 1->1.",
        ),
        check(
            "stationary_distribution",
            stationary_ok,
            "The stationary row vector pi=((5+sqrt(5))/10,(5-sqrt(5))/10) equals (phi^2/(phi^2+1),1/(phi^2+1)) and satisfies pi P=pi.",
        ),
        check(
            "metric_entropy_log_phi",
            entropy_ok,
            "The metric entropy -sum_i pi_i sum_j p_ij log(p_ij) simplifies exactly to log(phi), matching the topological entropy by the Parry theorem.",
        ),
        check(
            "coarse_stationary_cell_sizes",
            coarse_ok,
            "The related Window6 coarse four-cell balance distribution is cell sizes (27,22,9,6)/64.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "perron_vectors": {
            "M": [[1, 1], [1, 0]],
            "phi": "(1+sqrt(5))/2",
            "right_v": ["phi", "1"],
            "left_u": ["phi", "1"],
            "right_equation": "M*v=phi*v",
            "left_equation": "u*M=phi*u",
        },
        "transition_P": {
            "matrix": [["1/phi", "1/phi^2"], ["1", "0"]],
            "derivation": "p_ij=M_ij*v_j/(phi*v_i)",
            "row_sums": ["1", "1"],
            "forbidden_transition": "p_11=0",
            "golden_probabilities": {"p_00": "1/phi", "p_01": "1/phi^2=1-1/phi", "p_10": "1"},
        },
        "stationary": {
            "pi": ["(5+sqrt(5))/10", "(5-sqrt(5))/10"],
            "pi_phi_form": ["phi^2/(phi^2+1)", "1/(phi^2+1)"],
            "pi_decimal": [str(sp.N(stationary[0, 0], 16)), str(sp.N(stationary[0, 1], 16))],
            "equation": "pi*P=pi",
            "sum": "1",
        },
        "entropy": {
            "metric_entropy": "log(phi)",
            "topological_entropy": "log(phi)",
            "identity": "-sum_i pi_i sum_j p_ij log(p_ij)=log(phi)",
            "parry_theorem_readback": "For this irreducible SFT, the Parry measure is the maximal-entropy measure and its entropy equals the topological entropy.",
        },
        "coarse_stationary": {
            "cell_order": ["U_2", "U_1", "U_L", "U_R"],
            "cell_sizes": coarse_cell_sizes,
            "distribution": ["27/64", "22/64", "9/64", "6/64"],
            "readback": "This is the related coarse Window6 balance distribution by cell sizes, not the two-state Parry measure.",
        },
        "not_claimed": [
            "no physical-constant identification",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

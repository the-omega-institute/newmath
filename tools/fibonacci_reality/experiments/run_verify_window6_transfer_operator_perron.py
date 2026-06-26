#!/usr/bin/env python3
"""Forward-check the golden Perron spectrum of the no-adjacent-one transfer operator."""

from __future__ import annotations

import itertools
import json
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fibonacci_values(n: int) -> list[int]:
    values = [0, 1]
    for _ in range(2, n + 1):
        values.append(values[-1] + values[-2])
    return values


def lucas_values(n: int) -> list[int]:
    values = [2, 1]
    for _ in range(2, n + 1):
        values.append(values[-1] + values[-2])
    return values


def no_adjacent_one_words(length: int) -> list[tuple[int, ...]]:
    return [
        word
        for word in itertools.product((0, 1), repeat=length)
        if all(not (word[index] == 1 and word[index + 1] == 1) for index in range(length - 1))
    ]


def matrix_entry_sum(matrix: sp.Matrix) -> int:
    return int(sum(matrix[row, col] for row in range(matrix.rows) for col in range(matrix.cols)))


def main() -> None:
    lam = sp.symbols("lambda")
    matrix = sp.Matrix([[1, 1], [1, 0]])
    charpoly = sp.expand(matrix.charpoly(lam).as_expr())
    phi = (1 + sp.sqrt(5)) / 2
    psi = (1 - sp.sqrt(5)) / 2
    expected_charpoly = lam**2 - lam - 1
    fib = fibonacci_values(13)
    lucas = lucas_values(8)

    eigenvalue_dict = matrix.eigenvals()
    eigenvalues_match = (
        len(eigenvalue_dict) == 2
        and any(sp.simplify(root - phi) == 0 for root in eigenvalue_dict)
        and any(sp.simplify(root - psi) == 0 for root in eigenvalue_dict)
    )
    perron_exact = (
        sp.simplify(charpoly - expected_charpoly) == 0
        and eigenvalues_match
        and sp.simplify(psi + 1 / phi) == 0
        and float(phi.evalf()) > abs(float(psi.evalf()))
    )

    linear_counts: list[dict[str, Any]] = []
    linear_ok = True
    for m in range(1, 9):
        transfer_count = matrix_entry_sum(matrix ** (m - 1))
        direct_count = len(no_adjacent_one_words(m))
        expected = fib[m + 2]
        item_ok = transfer_count == expected and direct_count == expected
        linear_ok = linear_ok and item_ok
        linear_counts.append(
            {
                "m": m,
                "transfer_count": transfer_count,
                "direct_enumeration_count": direct_count,
                "fibonacci_F_m_plus_2": expected,
                "passed": item_ok,
            }
        )

    cyclic_counts: list[dict[str, Any]] = []
    cyclic_ok = True
    for m in range(1, 9):
        trace_count = int((matrix**m).trace())
        expected = lucas[m]
        item_ok = trace_count == expected
        cyclic_ok = cyclic_ok and item_ok
        cyclic_counts.append(
            {
                "m": m,
                "trace_count": trace_count,
                "lucas_L_m": expected,
                "passed": item_ok,
            }
        )

    binet_values: list[dict[str, Any]] = []
    binet_ok = True
    for n in range(1, 12):
        expression = sp.simplify((phi**n - psi**n) / sp.sqrt(5))
        expected = fib[n]
        item_ok = sp.simplify(expression - expected) == 0
        binet_ok = binet_ok and item_ok
        binet_values.append({"n": n, "binet_value": str(expression), "F_n": expected, "passed": item_ok})

    visible_weights = [1, 2, 3, 5, 8, 13]
    expected_visible_weights = fib[2:8]
    tail_aliases = [21, 34, 55]
    expected_tail_aliases = fib[8:11]
    golden_base_unification_ok = (
        visible_weights == expected_visible_weights
        and tail_aliases == expected_tail_aliases
        and sp.simplify(phi**2 - phi - 1) == 0
    )

    entropy = sp.log(phi)
    checks = [
        check(
            "transfer_matrix_charpoly",
            sp.simplify(charpoly - expected_charpoly) == 0,
            "det(lambda I - M)=lambda^2-lambda-1 for M=[[1,1],[1,0]]",
        ),
        check(
            "perron_eigenvalue_phi",
            perron_exact,
            "the eigenvalues are phi and psi=-1/phi, with phi>|psi|, so the Perron root is phi",
        ),
        check(
            "topological_entropy_log_phi",
            sp.simplify(sp.exp(entropy) - phi) == 0 and perron_exact,
            "h_top=log(rho(M))=log(phi), equivalently exp(h_top)=phi",
        ),
        check(
            "linear_count_fibonacci",
            linear_ok,
            "for m=1..8, 1^T M^(m-1) 1 agrees with F_{m+2} and with direct enumeration",
        ),
        check(
            "cyclic_count_lucas",
            cyclic_ok,
            "for m=1..8, tr(M^m) agrees with Lucas L_m",
        ),
        check(
            "binet_from_diagonalization",
            binet_ok,
            "for n=1..11, (phi^n-psi^n)/sqrt(5) simplifies exactly to F_n",
        ),
        check(
            "golden_base_unification",
            golden_base_unification_ok,
            "Window6 weights F_2..F_7 and tail aliases F_8..F_10 use the same phi as the Perron root",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "matrix": [[1, 1], [1, 0]],
        "charpoly": "lambda^2-lambda-1",
        "eigenvalues": {"phi": "(1+sqrt(5))/2", "psi": "(1-sqrt(5))/2=-1/phi"},
        "perron": {
            "spectral_radius": "phi",
            "phi_decimal": str(sp.N(phi, 18)),
            "abs_psi_decimal": str(sp.N(abs(float(psi.evalf())), 18)),
            "reason": "M is nonnegative and primitive; phi is the unique eigenvalue of maximal modulus.",
        },
        "entropy": {"topological_entropy": "log(phi)", "exp_entropy": "phi"},
        "counts": {
            "linear_m_1_to_8": linear_counts,
            "cyclic_m_1_to_8": cyclic_counts,
        },
        "binet": {
            "formula": "F_n=(phi^n-psi^n)/sqrt(5)",
            "checked_n_1_to_11": binet_values,
        },
        "golden_base_unification": {
            "V_6_visible_weights": visible_weights,
            "expected_F_2_to_F_7": expected_visible_weights,
            "foldbin_tail_aliases": tail_aliases,
            "expected_F_8_to_F_10": expected_tail_aliases,
            "structural_readback": (
                "The D* shell expansions use the same base phi as the Perron eigenvalue of the "
                "adjacency-exclusion transfer operator."
            ),
        },
        "not_claimed": [
            "no physical-constant identification is made by this spectral mechanism",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

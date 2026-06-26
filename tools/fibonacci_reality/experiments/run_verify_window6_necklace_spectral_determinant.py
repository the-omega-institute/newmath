#!/usr/bin/env python3
"""Exact certificate for the necklace spectral-determinant bridge."""

from __future__ import annotations

import json
import math
from collections import Counter
from typing import Any

import sympy as sp


VERIFY_G_MIN = 1
VERIFY_G_MAX = 10
WINDOW_N = 10


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def tuple_key(size: int, weight: int) -> str:
    return f"({size},{weight})"


def coefficient_list(poly: sp.Expr, var: sp.Symbol) -> list[int]:
    expanded = sp.Poly(sp.expand(poly), var)
    degree = expanded.degree()
    if degree < 0:
        return []
    return [int(expanded.coeff_monomial(var ** exponent)) for exponent in range(degree + 1)]


def sparse_terms(poly: sp.Expr, x: sp.Symbol, y: sp.Symbol) -> dict[str, int]:
    expanded = sp.Poly(sp.expand(poly), x, y)
    terms: dict[str, int] = {}
    for (x_power, y_power), coeff in sorted(expanded.terms(), key=lambda row: (row[0][0], row[0][1])):
        value = int(coeff)
        if value:
            terms[tuple_key(int(x_power), int(y_power))] = value
    return terms


def fibonacci_numbers(up_to: int) -> list[int]:
    values = [0, 1]
    for _ in range(2, up_to + 1):
        values.append(values[-1] + values[-2])
    return values[: up_to + 1]


def lucas_numbers(up_to: int) -> list[int]:
    values = [2, 1]
    for _ in range(2, up_to + 1):
        values.append(values[-1] + values[-2])
    return values[1 : up_to + 1]


def trace_T_power(g: int, z: sp.Symbol) -> sp.Expr:
    matrix = sp.Matrix([[1, z], [1, 0]])
    return sp.expand((matrix ** g).trace())


def primitive_poly(d: int, z: sp.Symbol) -> sp.Expr:
    total = 0
    for r in sp.divisors(d):
        r = int(r)
        total += int(sp.mobius(r)) * trace_T_power(d // r, z ** r)
    result = sp.Rational(1, d) * total
    return sp.expand(result)


def truncated_neg_log_det(det: sp.Expr, x: sp.Symbol) -> sp.Expr:
    return sp.expand(sp.series(-sp.log(det), x, 0, VERIFY_G_MAX + 1).removeO())


def trace_power_sum_log(x: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    return sp.expand(
        sum(
            sp.Rational(1, g) * trace_T_power(g, y) * x ** g
            for g in range(VERIFY_G_MIN, VERIFY_G_MAX + 1)
        )
    )


def euler_log_from_primitive_polys(x: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    total = 0
    for d in range(1, VERIFY_G_MAX + 1):
        p_d = primitive_poly(d, y)
        coeffs = coefficient_list(p_d, y)
        for s, coeff in enumerate(coeffs):
            if coeff == 0:
                continue
            for multiple in range(1, VERIFY_G_MAX // d + 1):
                total += sp.Rational(coeff, multiple) * x ** (d * multiple) * y ** (s * multiple)
    return sp.expand(total)


def newton_rhs(g: int, y: sp.Symbol) -> sp.Expr:
    total = 0
    for d in sp.divisors(g):
        d = int(d)
        total += d * primitive_poly(d, y ** (g // d))
    return sp.expand(total)


def c10_sector_terms(y: sp.Symbol) -> Counter[tuple[int, int]]:
    terms: Counter[tuple[int, int]] = Counter()
    for d in sp.divisors(WINDOW_N):
        d = int(d)
        coeffs = coefficient_list(primitive_poly(d, y), y)
        for s, coeff in enumerate(coeffs):
            if coeff:
                terms[(d, s)] += int(coeff)
    return terms


def c10_kernel_lifted_terms(y: sp.Symbol) -> Counter[tuple[int, int]]:
    terms: Counter[tuple[int, int]] = Counter()
    for d in sp.divisors(WINDOW_N):
        d = int(d)
        coeffs = coefficient_list(primitive_poly(d, y), y)
        for s, coeff in enumerate(coeffs):
            if coeff:
                terms[(d, s * (WINDOW_N // d))] += int(coeff)
    return terms


def c10_sector_factor_string(terms: Counter[tuple[int, int]]) -> str:
    pieces: list[str] = []
    for (d, s), coeff in sorted(terms.items()):
        factor = f"(1-x^{d}"
        if s:
            factor += f"*y^{s}"
        factor += ")"
        exponent = f"^{coeff}" if coeff != 1 else ""
        pieces.append(f"{factor}{exponent}")
    return "1/[" + " ".join(pieces) + "]"


def main() -> None:
    x, y = sp.symbols("x y")

    transfer = sp.Matrix([[1, y], [1, 0]])
    spectral_det = sp.expand((sp.eye(2) - x * transfer).det())
    expected_det = 1 - x - y * x ** 2

    neg_log_det = truncated_neg_log_det(spectral_det, x)
    trace_log = trace_power_sum_log(x, y)
    euler_log = euler_log_from_primitive_polys(x, y)

    newton_rows: dict[str, dict[str, Any]] = {}
    newton_matches: dict[str, bool] = {}
    for g in range(VERIFY_G_MIN, VERIFY_G_MAX + 1):
        trace_poly = trace_T_power(g, y)
        rhs_poly = newton_rhs(g, y)
        newton_rows[str(g)] = {
            "trace_coefficients": coefficient_list(trace_poly, y),
            "newton_coefficients": coefficient_list(rhs_poly, y),
            "trace_polynomial": str(trace_poly),
        }
        newton_matches[str(g)] = bool(sp.expand(trace_poly - rhs_poly) == 0)

    primitive_polys = {d: primitive_poly(d, y) for d in range(1, VERIFY_G_MAX + 1)}
    primitive_coeffs = {d: coefficient_list(poly, y) for d, poly in primitive_polys.items()}
    primitive_expected_dvd_10 = {
        1: [1],
        2: [0, 1],
        5: [0, 1, 1],
        10: [0, 1, 3, 5, 2],
    }

    sector_terms = c10_sector_terms(y)
    expected_sector_terms = Counter(
        {
            (1, 0): 1,
            (2, 1): 1,
            (5, 1): 1,
            (5, 2): 1,
            (10, 1): 1,
            (10, 2): 3,
            (10, 3): 5,
            (10, 4): 2,
        }
    )
    lifted_terms = c10_kernel_lifted_terms(y)
    expected_lifted_terms = Counter(
        {
            (1, 0): 1,
            (2, 5): 1,
            (5, 2): 1,
            (5, 4): 1,
            (10, 1): 1,
            (10, 2): 3,
            (10, 3): 5,
            (10, 4): 2,
        }
    )

    fib = fibonacci_numbers(VERIFY_G_MAX + 1)
    fibonacci_generating_series = sp.expand(
        sum(fib[g + 1] * x ** g for g in range(0, VERIFY_G_MAX + 1))
    )
    inverse_det_z1_series = sp.expand(
        sp.series(1 / spectral_det.subs(y, 1), x, 0, VERIFY_G_MAX + 1).removeO()
    )
    lucas = lucas_numbers(VERIFY_G_MAX)
    lucas_log_z1 = sp.expand(
        sum(sp.Rational(lucas[g - 1], g) * x ** g for g in range(1, VERIFY_G_MAX + 1))
    )
    neg_log_det_z1 = sp.expand(neg_log_det.subs(y, 1))

    checks = [
        check(
            "spectral_determinant",
            bool(sp.expand(spectral_det - expected_det) == 0),
            "det(I-xT(y)) for T(y)=[[1,y],[1,0]] is 1-x-y*x^2.",
        ),
        check(
            "log_det_trace_powersum",
            bool(sp.expand(neg_log_det - trace_log) == 0),
            "The x^<=10 truncation of -log det(I-xT(y)) equals sum_g tr(T(y)^g)x^g/g.",
        ),
        check(
            "newton_necklace_identity",
            all(newton_matches.values()),
            "For g=1..10, tr(T(y)^g)=sum_{d|g} d*P_d(y^(g/d)) with P_d defined by Mobius trace extraction.",
        ),
        check(
            "euler_product_is_inverse_determinant",
            bool(sp.expand(euler_log - neg_log_det) == 0),
            "The primitive-necklace Euler product has log equal to -log det(I-xT(y)) through x^10.",
        ),
        check(
            "c10_sector_euler_factor",
            sector_terms == expected_sector_terms and lifted_terms == expected_lifted_terms,
            "The d|10 Euler-factor exponents are the raw P_d coefficients, and the C_10 trace-cycle-index lift recovers the G_10 kernel terms.",
        ),
        check(
            "z1_recovers_lucas_zeta",
            bool(
                sp.expand(inverse_det_z1_series - fibonacci_generating_series) == 0
                and sp.expand(neg_log_det_z1 - lucas_log_z1) == 0
            ),
            "At y=1, det(I-xT(1))=1-x-x^2, its inverse generates F_{g+1}, and its log generates Lucas power sums through x^10.",
        ),
    ]

    not_claimed = [
        "physical fine-structure constant or external interpretation",
        "all-period full-SFT zeta claim beyond the Window6/C_10 divisor sector and same-carrier formal envelope",
    ]

    result: dict[str, Any] = {
        "definition": "T(y)=[[1,y],[1,0]], P_d(y)=(1/d) sum_{r|d} mu(r) tr(T(y^r)^(d/r)), and Z=prod_d prod_s (1-x^d y^s)^-[y^s]P_d(y).",
        "T": [[1, "y"], [1, 0]],
        "spectral_determinant": str(spectral_det),
        "inverse_spectral_determinant": "1/(1-x-y*x^2)",
        "log_det_trace_powersum_truncated_x10": sparse_terms(neg_log_det, x, y),
        "primitive_polynomials": {
            str(d): {
                "coefficients": primitive_coeffs[d],
                "polynomial": str(primitive_polys[d]),
            }
            for d in sorted(primitive_coeffs)
        },
        "primitive_polynomials_dvd_10": {
            str(d): primitive_expected_dvd_10[d] for d in sorted(primitive_expected_dvd_10)
        },
        "newton_rows": newton_rows,
        "c10_sector_euler_factor": {
            "factor": c10_sector_factor_string(sector_terms),
            "raw_exponents": {tuple_key(d, s): int(count) for (d, s), count in sorted(sector_terms.items())},
            "trace_cycle_index_lifted_exponents": {
                tuple_key(d, k): int(count) for (d, k), count in sorted(lifted_terms.items())
            },
        },
        "z1_bridge": {
            "det": "1-x-x^2",
            "inverse_series_coefficients_F_g_plus_1": [fib[g + 1] for g in range(0, VERIFY_G_MAX + 1)],
            "lucas_power_sums": {str(g): lucas[g - 1] for g in range(1, VERIFY_G_MAX + 1)},
        },
        "scope": "Window6/C_10 divisor-sector plus same-carrier formal determinant envelope; no all-period full-SFT zeta claim.",
        "nonredundant_boundary": "This certificate links primitive necklace Euler factors and Newton power sums to the weighted two-state transfer spectral determinant; existing anchors only record P_d/G_10 specializations, Perron data for T(1), Parry data, or four-cell Markov resolvents.",
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

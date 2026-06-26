#!/usr/bin/env python3
"""Exact certificate for the trace-cycle-index golden-necklace kernel."""

from __future__ import annotations

import json
import math
from collections import Counter
from typing import Any

import sympy as sp


WINDOW_N = 10
VERIFY_G_MIN = 1
VERIFY_G_MAX = 10


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


def sparse_terms(poly: sp.Expr, u: sp.Symbol, y: sp.Symbol) -> dict[str, int]:
    expanded = sp.Poly(sp.expand(poly), u, y)
    terms: dict[str, int] = {}
    for (u_power, y_power), coeff in sorted(expanded.terms(), key=lambda row: (row[0][0], row[0][1])):
        value = int(coeff)
        if value:
            terms[tuple_key(int(u_power), int(y_power))] = value
    return terms


def weighted_trace_coeff(g: int, s: int) -> int:
    if s < 0 or 2 * s > g:
        return 0
    if s == 0:
        return 1
    value = sp.Rational(g * math.comb(g - s, s), g - s)
    if value.q != 1:
        raise ValueError(f"W({g},{s}) is not integral: {value}")
    return int(value)


def weighted_trace_polynomial(g: int, z: sp.Symbol) -> sp.Expr:
    return sum(weighted_trace_coeff(g, s) * z ** s for s in range(g // 2 + 1))


def trace_T_power(g: int, z: sp.Symbol) -> sp.Expr:
    matrix = sp.Matrix([[1, z], [1, 0]])
    return sp.expand((matrix ** g).trace())


def lucas_numbers(up_to: int) -> list[int]:
    values = [2, 1]
    for _ in range(2, up_to + 1):
        values.append(values[-1] + values[-2])
    return values[1 : up_to + 1]


def primitive_poly(d: int, z: sp.Symbol) -> sp.Expr:
    total = 0
    for r in sp.divisors(d):
        r = int(r)
        total += int(sp.mobius(r)) * trace_T_power(d // r, z ** r)
    result = sp.Rational(1, d) * total
    return sp.expand(result)


def kernel_G(n: int, u: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    total = 0
    z = sp.Symbol("z")
    for d in sp.divisors(n):
        d = int(d)
        total += u ** d * primitive_poly(d, z).subs(z, y ** (n // d))
    return sp.expand(total)


def size_spectrum_from_lucas(length: int, lucas: dict[int, int]) -> dict[int, int]:
    result: dict[int, int] = {}
    for d in sp.divisors(length):
        d = int(d)
        numerator = 0
        for e in sp.divisors(d):
            e = int(e)
            numerator += int(sp.mobius(d // e)) * lucas[e]
        value = sp.Rational(numerator, d)
        if value.q != 1:
            raise ValueError(f"a({d}) is not integral: {value}")
        result[d] = int(value)
    return result


def main() -> None:
    z, u, y = sp.symbols("z u y")

    weighted_trace_rows: dict[str, dict[str, Any]] = {}
    weighted_trace_matches: dict[str, bool] = {}
    for g in range(VERIFY_G_MIN, VERIFY_G_MAX + 1):
        trace_poly = trace_T_power(g, z)
        formula_poly = weighted_trace_polynomial(g, z)
        weighted_trace_rows[str(g)] = {
            "trace_coefficients": coefficient_list(trace_poly, z),
            "formula_coefficients": coefficient_list(formula_poly, z),
            "polynomial": str(trace_poly),
        }
        weighted_trace_matches[str(g)] = bool(sp.expand(trace_poly - formula_poly) == 0)

    lucas_list = lucas_numbers(VERIFY_G_MAX)
    lucas_by_g = {g: lucas_list[g - 1] for g in range(1, VERIFY_G_MAX + 1)}
    trace_at_one = {g: int(trace_T_power(g, z).subs(z, 1)) for g in range(1, VERIFY_G_MAX + 1)}

    primitive_expected = {
        1: [1],
        2: [0, 1],
        5: [0, 1, 1],
        10: [0, 1, 3, 5, 2],
    }
    primitive_polys = {d: primitive_poly(d, z) for d in sp.divisors(WINDOW_N)}
    primitive_coeffs = {int(d): coefficient_list(poly, z) for d, poly in primitive_polys.items()}
    primitive_matches = {
        str(d): primitive_coeffs[int(d)] == coeffs for d, coeffs in primitive_expected.items()
    }

    G_10 = kernel_G(WINDOW_N, u, y)
    joint_expected = Counter(
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
    joint_from_kernel = Counter(
        {
            tuple(map(int, key.strip("()").split(","))): value
            for key, value in sparse_terms(G_10, u, y).items()
        }
    )

    weight_poly = sp.expand(G_10.subs(u, 1))
    weight_coeffs = coefficient_list(weight_poly, y)
    size_poly = sp.expand(G_10.subs(y, 1))
    size_coeffs = {power: int(sp.Poly(size_poly, u).coeff_monomial(u ** power)) for power in sp.divisors(WINDOW_N)}
    size_formula = size_spectrum_from_lucas(WINDOW_N, lucas_by_g)
    orbit_count = int(G_10.subs({u: 1, y: 1}))
    burnside_lucas = int(
        sp.Rational(
            sum(int(sp.totient(WINDOW_N // e)) * lucas_by_g[e] for e in sp.divisors(WINDOW_N)),
            WINDOW_N,
        )
    )

    not_claimed = [
        "physical fine-structure constant or any external/metrological interpretation (the trace-cycle-index kernel is a finite combinatorial generating identity over the golden no-adjacent-1 carrier, not about alpha)"
    ]

    checks = [
        check(
            "weighted_trace_identity",
            all(weighted_trace_matches.values()),
            "For g=1..10, tr(T(z)^g) equals sum_s W(g,s) z^s with T(z)=[[1,z],[1,0]], W(g,0)=1, and W(g,s)=g/(g-s)*binomial(g-s,s) for s>=1.",
        ),
        check(
            "z1_trace_is_lucas",
            trace_at_one == lucas_by_g,
            "At z=1, the weighted matrix is the core Fibonacci transfer matrix M and tr(M^g)=L_g for g=1..10.",
        ),
        check(
            "primitive_poly_mobius",
            all(primitive_matches.values()),
            "For d|10, P_d(z)=(1/d) sum_{r|d} mu(r) tr(T(z^r)^(d/r)) gives P_1=[1], P_2=[0,1], P_5=[0,1,1], P_10=[0,1,3,5,2].",
        ),
        check(
            "joint_kernel_recovers_J10",
            joint_from_kernel == joint_expected,
            "The bivariate coefficients [u^d y^k]G_10 recover the full joint table J_10(d,k).",
        ),
        check(
            "weight_marginal_recovers_N10",
            weight_coeffs == [1, 1, 4, 5, 3, 1],
            "The specialization G_10(1,y) recovers N_10(y) with coefficients [1,1,4,5,3,1].",
        ),
        check(
            "size_marginal_recovers_a_d",
            size_coeffs == size_formula == {1: 1, 2: 1, 5: 2, 10: 11},
            "The specialization G_10(u,1) recovers the Mobius-Lucas orbit-size spectrum a(d)={1:1,2:1,5:2,10:11}.",
        ),
        check(
            "orbit_count_specialization",
            orbit_count == burnside_lucas == 15,
            "The scalar specialization G_10(1,1) recovers the Burnside-Lucas orbit count 15.",
        ),
    ]

    result: dict[str, Any] = {
        "definition": "G_n(u,y)=sum_{d|n} u^d P_d(y^(n/d)), where P_d(z)=(1/d) sum_{r|d} mu(r) tr(T(z^r)^(d/r)) and T(z)=[[1,z],[1,0]].",
        "T": [[1, "z"], [1, 0]],
        "weighted_trace": {
            "W_formula": "W(g,0)=1; W(g,s)=g/(g-s)*binomial(g-s,s) for s>=1.",
            "rows": weighted_trace_rows,
            "matches": weighted_trace_matches,
        },
        "core_bridge": {
            "M": [[1, 1], [1, 0]],
            "trace_at_z1": trace_at_one,
            "lucas": lucas_by_g,
        },
        "primitive_polynomials": {
            str(d): {
                "coefficients": primitive_coeffs[int(d)],
                "polynomial": str(primitive_polys[int(d)]),
            }
            for d in sorted(primitive_coeffs)
        },
        "G_10": {
            "polynomial": str(G_10),
            "terms": sparse_terms(G_10, u, y),
        },
        "J_10": {tuple_key(d, k): int(count) for (d, k), count in sorted(joint_expected.items())},
        "N_10": weight_coeffs,
        "a_d": {str(key): value for key, value in sorted(size_coeffs.items())},
        "L": {str(key): value for key, value in sorted(lucas_by_g.items())},
        "observables_generated_by_single_kernel": {
            "joint": "J_10(d,k)=[u^d y^k]G_10(u,y)",
            "weight": "N_10(y)=G_10(1,y)",
            "size": "a(d)=[u^d]G_10(u,1)",
            "orbit_count": "15=G_10(1,1)",
        },
        "nonredundant_boundary": "The kernel is not any one marginal: it is a single trace-cycle-index generating polynomial whose four specializations recover the joint table, weight polynomial, size spectrum, and orbit count, while z=1 returns the core Fibonacci transfer matrix trace.",
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

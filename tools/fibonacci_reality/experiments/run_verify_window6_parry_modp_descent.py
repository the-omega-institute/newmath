#!/usr/bin/env python3
"""Forward-check the mod-p descent of the Parry stationary covector."""

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


def roots_mod_p(p: int) -> list[int]:
    return [r for r in range(p) if (r * r - r - 1) % p == 0]


def is_irreducible_quadratic_mod_p(p: int) -> bool:
    return roots_mod_p(p) == []


def projective_kernel_witness_mod_p(p: int, a: int) -> tuple[int, int]:
    # For a root a of x^2-x-1, the integral covector w=(a^2,1)
    # satisfies w(P-I)=0 projectively before mass-one normalization.
    return ((a * a) % p, 1 % p)


def projective_equation_holds(p: int, a: int) -> bool:
    w0, w1 = projective_kernel_witness_mod_p(p, a)
    return ((w0 + a * w1) % p == (a * w0) % p) and (w0 % p == (a * a * w1) % p)


def frobenius_conjugate_of_phi(p: int) -> tuple[int, int]:
    # In F_p[t]/(t^2-t-1), Frobenius sends t to t^p.  For inert primes it
    # equals the other root 1-t, encoded as coeffs (constant, t-coeff).
    t_power = (0, 1)

    def add(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
        return ((u[0] + v[0]) % p, (u[1] + v[1]) % p)

    def mul(u: tuple[int, int], v: tuple[int, int]) -> tuple[int, int]:
        c0 = u[0] * v[0] + u[1] * v[1]
        c1 = u[0] * v[1] + u[1] * v[0] + u[1] * v[1]
        return (c0 % p, c1 % p)

    acc = (1, 0)
    base = t_power
    exponent = p
    while exponent:
        if exponent & 1:
            acc = mul(acc, base)
        base = mul(base, base)
        exponent >>= 1
    return add(acc, (0, 0))


def main() -> None:
    x = sp.symbols("x")
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    minpoly = x**2 - x - 1
    disc = sp.discriminant(minpoly, x)

    transition = sp.Matrix(
        [
            [1 / phi, 1 / phi**2],
            [1, 0],
        ]
    )
    stationary = sp.Matrix([[(5 + sqrt5) / 10, (5 - sqrt5) / 10]])
    stationary_phi = sp.Matrix([[phi**2 / (phi**2 + 1), 1 / (phi**2 + 1)]])

    inert_primes = [2, 3, 7, 13]
    split_primes = [11, 19, 29, 31]
    split_roots = {p: roots_mod_p(p) for p in split_primes}
    inert_frobenius = {p: frobenius_conjugate_of_phi(p) for p in inert_primes}

    projective_split_ok = all(
        projective_equation_holds(p, root)
        for p, roots in split_roots.items()
        for root in roots
    )
    projective_ramified_ok = projective_equation_holds(5, 3)
    projective_inert_form_ok = all(
        frobenius == (1 % p, (-1) % p)
        for p, frobenius in inert_frobenius.items()
    )

    parry_stationary_ok = (
        all(sp.simplify((stationary * transition)[0, col] - stationary[0, col]) == 0 for col in range(2))
        and sp.simplify(stationary[0, 0] + stationary[0, 1] - 1) == 0
        and matrix_equal(stationary, stationary_phi)
    )
    minpoly_ok = sp.simplify(phi**2 - phi - 1) == 0 and disc == 5
    inert_ok = all(is_irreducible_quadratic_mod_p(p) for p in inert_primes)
    split_ok = all(len(roots_mod_p(p)) == 2 for p in split_primes)
    ramified_ok = (
        roots_mod_p(5) == [3]
        and all(((r * r - r - 1) - ((r + 2) ** 2)) % 5 == 0 for r in range(5))
        and 10 % 5 == 0
    )
    projective_ok = projective_split_ok and projective_ramified_ok and projective_inert_form_ok

    checks = [
        check(
            "parry_stationary_recall",
            parry_stationary_ok,
            "pi=((5+sqrt(5))/10,(5-sqrt(5))/10) equals (phi^2/(phi^2+1),1/(phi^2+1)) and satisfies pi*(P-I)=0.",
        ),
        check(
            "golden_minpoly_disc",
            minpoly_ok,
            "The Perron slope phi=(1+sqrt(5))/2 satisfies x^2-x-1, whose discriminant is 5.",
        ),
        check(
            "inert_primes_no_descent",
            inert_ok,
            "For p in {2,3,7,13}, x^2-x-1 has no root over F_p, so phi is not in F_p.",
        ),
        check(
            "split_primes_descend",
            split_ok,
            "For p in {11,19,29,31}, x^2-x-1 has two roots over F_p, so the normalized Parry covector descends to F_p.",
        ),
        check(
            "ramified_p5",
            ramified_ok,
            "Modulo 5, x^2-x-1=(x+2)^2 and the mass-one denominator 10 is zero, so the normalized covector is not defined over F_5.",
        ),
        check(
            "projective_kernel_survives",
            projective_ok,
            "The integral projective equation w=(phi^2,1), w0+phi*w1=phi*w0 and w0=phi^2*w1, survives reduction; inert Frobenius sends phi to 1-phi.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "stationary": {
            "pi": ["(5+sqrt(5))/10", "(5-sqrt(5))/10"],
            "pi_phi_form": ["phi^2/(phi^2+1)", "1/(phi^2+1)"],
            "transition_P": [["1/phi", "1/phi^2"], ["1", "0"]],
            "equation": "pi*(P-I)=0",
        },
        "minpoly": "x^2-x-1",
        "disc": int(disc),
        "inert_list": inert_primes,
        "inert_frobenius": {str(p): f"phi^p={c0}+{c1}*phi = 1-phi" for p, (c0, c1) in inert_frobenius.items()},
        "split_list": split_primes,
        "split_roots": {str(p): roots for p, roots in split_roots.items()},
        "ramified": 5,
        "ramified_double_root": "x=3 mod 5, equivalently x^2-x-1=(x+2)^2 over F_5",
        "normalization_denom": 10,
        "projective_kernel": {
            "integral_covector": ["phi^2", "1"],
            "relations": ["w0+phi*w1=phi*w0", "w0=phi^2*w1"],
            "survives_mod_p": "nonzero projective line survives each reduction, including p=5; mass-one normalization requires inverting phi^2+1.",
        },
        "not_claimed": [
            "physical fine-structure constant or external interpretation",
            "any claim beyond the finite arithmetic mod-p descent of the Parry stationary covector",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

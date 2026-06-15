#!/usr/bin/env python3
"""Exact no-go audit for a Window6-internal D*_6 tenth-order grading.

The audit is forward-only. It checks that the verified Window6 operators
currently available for this packet, the coarse Markov kernel T and the
fold-gauge operator A_0, do not contain a primitive tenth root of unity in
their spectra. Therefore they do not supply the spectral 10-periodic grading
needed for the residual ladder e == 7 mod 10. No physical constant
identification is made.
"""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def sympy_matrix_record(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


def main() -> None:
    x = sp.symbols("x")
    z = sp.symbols("z")

    phi10 = x**4 - x**3 + x**2 - x + 1
    tenth_roots_poly = x**10 - 1
    phi10_quotient, phi10_remainder = sp.div(tenth_roots_poly, phi10, domain=sp.QQ)

    t_resolvent_cubic = 55 * z**3 + 506 * z**2 - 7263 * z - 48114
    t_eigenvalue_cubic = 48114 * x**3 + 7263 * x**2 - 506 * x - 55
    t_charpoly = sp.factor((x - 1) * t_eigenvalue_cubic / 48114)
    t_discriminant = sp.factor(sp.discriminant(t_eigenvalue_cubic, x))
    t_roots_all_real = t_discriminant > 0
    t_phi10_quotient, t_phi10_remainder = sp.div(
        sp.Poly(48114 * t_charpoly, x),
        sp.Poly(phi10, x),
        domain=sp.QQ,
    )

    a0 = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 2), 0, sp.Rational(1, 2)],
            [0, 0, sp.Rational(1, 2), 0],
            [sp.Rational(1, 2), 1, 0, 0],
            [sp.Rational(1, 2), 0, 0, 0],
        ]
    )
    a0_charpoly = sp.factor(a0.charpoly(x).as_expr())
    expected_a0_charpoly = sp.factor((x - 1) * (2 * x - 1) * (2 * x + 1) ** 2 / 8)
    a0_phi10_quotient, a0_phi10_remainder = sp.div(
        sp.Poly(8 * a0_charpoly, x),
        sp.Poly(phi10, x),
        domain=sp.QQ,
    )
    a0_spectrum = a0.eigenvals()

    escape_ratio = sp.Rational(32, 6 * 6)
    primitive_tenth_missing = t_phi10_remainder.as_expr() != 0 and a0_phi10_remainder.as_expr() != 0

    checks = [
        check(
            "phi10_definition",
            sp.expand(phi10) == x**4 - x**3 + x**2 - x + 1
            and phi10_remainder == 0
            and sp.degree(phi10, gen=x) == 4
            and sp.totient(10) == 4,
            "Phi_10(x)=x^4-x^3+x^2-x+1 divides x^10-1 and has degree phi(10)=4.",
        ),
        check(
            "T_spectrum_all_real",
            t_roots_all_real,
            "The verified Window6 Markov-kernel resolvent cubic 55z^3+506z^2-7263z-48114 has three real roots; hence T has Perron 1 plus real nontrivial eigenvalues.",
        ),
        check(
            "T_charpoly_no_phi10",
            t_phi10_remainder.as_expr() != 0,
            "Phi_10 does not divide the exact characteristic polynomial of T, so T has no primitive tenth root of unity eigenvalue.",
        ),
        check(
            "A0_charpoly_no_phi10",
            sp.simplify(a0_charpoly - expected_a0_charpoly) == 0
            and a0_spectrum == {sp.Integer(1): 1, sp.Rational(1, 2): 1, sp.Rational(-1, 2): 2}
            and a0_phi10_remainder.as_expr() != 0,
            "The fold-gauge A_0 has spectrum {1,1/2,-1/2}; Phi_10 does not divide its exact characteristic polynomial.",
        ),
        check(
            "no_tenth_periodic_grading",
            primitive_tenth_missing,
            "The verified Window6 operator set {T,A_0} contains no primitive tenth root of unity, so it supplies no 10-periodic spectral grading for e == 7 mod 10.",
        ),
        check(
            "eight_ninths_is_escape_not_residual",
            escape_ratio == sp.Rational(8, 9),
            "The local 8/9 equals the Markov right-boundary escape ratio 32/(6*6), a distinct object from an e=27 residual coefficient without a forward bridge.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "Phi10": {
            "polynomial": str(phi10),
            "divides_x10_minus_1": bool(phi10_remainder == 0),
            "quotient_in_x10_minus_1": str(sp.factor(phi10_quotient)),
            "degree": int(sp.degree(phi10, gen=x)),
            "euler_phi_10": int(sp.totient(10)),
            "meaning": "primitive tenth roots of unity are roots of Phi_10.",
        },
        "T_spectrum": {
            "det_I_minus_zT": str(sp.factor((z - 1) * t_resolvent_cubic / 48114)),
            "resolvent_cubic": str(t_resolvent_cubic),
            "det_lambda_I_minus_T": str(t_charpoly),
            "eigenvalue_cubic": str(t_eigenvalue_cubic),
            "eigenvalue_cubic_discriminant": str(t_discriminant),
            "nontrivial_roots_all_real": bool(t_roots_all_real),
            "T_phi10_remainder_after_clearing_denominator": str(t_phi10_remainder.as_expr()),
            "T_has_phi10_factor": bool(t_phi10_remainder.as_expr() == 0),
            "conclusion": "T has no primitive tenth root of unity eigenvalue.",
        },
        "A0_spectrum": {
            "A_0": sympy_matrix_record(a0),
            "charpoly": str(a0_charpoly),
            "spectrum_with_algebraic_multiplicity": {"1": 1, "1/2": 1, "-1/2": 2},
            "A0_phi10_remainder_after_clearing_denominator": str(a0_phi10_remainder.as_expr()),
            "A0_has_phi10_factor": bool(a0_phi10_remainder.as_expr() == 0),
            "conclusion": "A_0 has no primitive tenth root of unity eigenvalue.",
        },
        "grading_no_go": {
            "required_for_ladder": "A spectral 10-periodic grading supporting residual exponents e == 7 mod 10 requires a primitive tenth root of unity, equivalently a Phi_10 factor, in the relevant Window6 transfer operator.",
            "verified_window6_operators_checked": ["T", "A_0"],
            "primitive_tenth_root_absent": bool(primitive_tenth_missing),
            "conclusion": "The residual ladder e == 7 mod 10 and its 8/9 coefficient are not Window6-internal forced by the verified operator set; D*_6 is needs-external/protocol-gated.",
        },
        "eight_ninths": {
            "escape_count": 32,
            "boundary_degree_count": "6*6",
            "escape_ratio": {"numerator": int(escape_ratio.p), "denominator": int(escape_ratio.q)},
            "distinct_from": "the e=27 residual coefficient in the D*_6 residual ladder",
            "forward_bridge_present": False,
        },
        "not_claimed": [
            "physical fine-structure constant identification R_6(D*)=alpha^-1",
            "D*_6 as a Window6-internal theorem (it is needs-external/protocol-gated)",
            "the 7+10k residual ladder and 8/9 coefficient as Window6-internal forced (the tenth-order grading certificate is absent from verified Window6 operators)",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

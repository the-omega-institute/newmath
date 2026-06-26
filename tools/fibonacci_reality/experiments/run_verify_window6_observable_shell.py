#!/usr/bin/env python3
"""Forward checks for the Window6 observable-shell readout packet."""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    pi = sp.pi
    sigma = sp.symbols("sigma", integer=True)
    c, c_star, d = sp.symbols("c c_star d", nonzero=True)
    q = sp.symbols("q", positive=True)
    formal_alpha = sp.Function("formal_alpha")

    a = sp.Integer(21)
    b = sp.Integer(34)
    kappa = sp.Rational(1, 2) + sp.Rational(1, 4) * sp.cos(pi / phi) ** 2

    def c_of(d_value: sp.Expr) -> sp.Expr:
        return kappa + 1 / (d_value * phi**5)

    def r_raw(sigma_value: sp.Expr, c_value: sp.Expr) -> sp.Expr:
        return 2 * pi * (a + b * c_value) / (
            a * phi ** (-sigma_value) + b * c_value * phi ** (-(sigma_value + 1))
        )

    def r_of(sigma_value: sp.Expr, c_value: sp.Expr) -> sp.Expr:
        return 2 * pi * phi**sigma_value * (a + b * c_value) / (a + b * c_value * phi**-1)

    d_star = sp.Integer(47) + phi**-7 - sp.Rational(1, 2) * phi**-17 + sp.Rational(8, 9) * phi**-27
    c_star_expr = c_of(d_star)
    r_0 = r_of(sp.Integer(6), c_star_expr)

    delta_phi_power = (a + b * c) / (a + b * c_star) * (a + b * c_star * phi**-1) / (a + b * c * phi**-1)
    r_0_abstract = r_of(sp.Integer(6), c_star)
    absorption_difference = sp.cancel(
        sp.together(r_of(sigma, c) - r_0_abstract * phi ** (sigma - 6) * delta_phi_power)
    )
    absorption_ok = absorption_difference == 0 or sp.simplify(absorption_difference) == 0

    test_pairs = [
        (sp.Integer(4), sp.Integer(43)),
        (sp.Integer(6), d_star),
        (sp.Integer(9), d_star + sp.Rational(3, 11) * phi**-12),
    ]
    tested_absorption_ok = True
    raw_factorization_ok = True
    for sigma_value, d_value in test_pairs:
        c_value = c_of(d_value)
        raw_difference = sp.cancel(sp.together(r_raw(sigma_value, c_value) - r_of(sigma_value, c_value)))
        raw_factorization_ok = raw_factorization_ok and (raw_difference == 0 or sp.simplify(raw_difference) == 0)
        concrete_power = delta_phi_power.subs({c: c_value, c_star: c_star_expr})
        difference = sp.cancel(
            sp.together(r_of(sigma_value, c_value) - r_0 * phi ** (sigma_value - 6) * concrete_power)
        )
        tested_absorption_ok = tested_absorption_ok and (difference == 0 or sp.simplify(difference) == 0)

    delta_r_1 = Fraction(26401, 2**13 * 571)
    d_1 = d_star + sp.Rational(delta_r_1.numerator, delta_r_1.denominator) * phi**-37
    gamma_d_expr = -sp.log(delta_phi_power.subs({c: c_of(d_1), c_star: c_star_expr})) / sp.log(phi)
    gamma_d_abs = abs(sp.N(gamma_d_expr, 90))
    gamma_d_bound_ok = bool(gamma_d_abs < sp.Float("1e-14", 90))

    gamma_ratio_identity = sp.factor(sp.together(r_0_abstract / r_of(sigma, c) - phi ** (6 - sigma) / delta_phi_power))
    gamma_definition_ok = gamma_ratio_identity == 0

    alpha_q = formal_alpha(q)
    gamma_eff = sp.log(r_0 * alpha_q) / sp.log(phi)
    beta_alpha = q * sp.diff(alpha_q, q)
    rg_difference = sp.simplify(q * sp.diff(gamma_eff, q) - beta_alpha / (alpha_q * sp.log(phi)))
    rg_dictionary_ok = rg_difference == 0

    first_pair = {"sigma": 6, "delta_sigma_d": 0, "sigma_eff": 6}
    second_pair = {"sigma": 5, "delta_sigma_d": 1, "sigma_eff": 6}
    noninjective_ok = (
        first_pair["sigma_eff"] == second_pair["sigma_eff"]
        and (first_pair["sigma"], first_pair["delta_sigma_d"])
        != (second_pair["sigma"], second_pair["delta_sigma_d"])
    )

    checks = [
        check(
            "sigma_eff_absorption_identity",
            absorption_ok and raw_factorization_ok and tested_absorption_ok,
            "R(sigma,D)=R_0*phi^(sigma-6+delta_sigma_D(D)) is verified by exact symbolic cancellation, with phi^delta expanded from the forward definition."
            if absorption_ok and raw_factorization_ok and tested_absorption_ok
            else "the absorption identity did not cancel to zero",
        ),
        check(
            "gamma_D_smallness",
            gamma_d_bound_ok,
            f"|gamma_D(1)|=|delta_sigma_D(D(1))| is below 1e-14; computed magnitude {sp.N(gamma_d_abs, 18)}"
            if gamma_d_bound_ok
            else f"|gamma_D(1)| bound failed; computed magnitude {sp.N(gamma_d_abs, 18)}",
        ),
        check(
            "gamma_eff_definition",
            gamma_definition_ok,
            "R_0/R=phi^(6-sigma_eff), so gamma_eff=log_phi(R_0/R)=6-sigma_eff by the defining logarithm."
            if gamma_definition_ok
            else "gamma_eff ratio identity did not cancel to zero",
        ),
        check(
            "rg_dictionary",
            rg_dictionary_ok,
            "For the formal relation alpha(Q)^-1=R(Q), differentiating gamma_eff=log_phi(R_0*alpha(Q)) gives d gamma_eff/d ln Q=beta_alpha/(alpha ln phi)."
            if rg_dictionary_ok
            else "the formal RG derivative identity did not simplify to zero",
        ),
        check(
            "observability_noninjective",
            noninjective_ok,
            "The distinct pairs (sigma,delta)=(6,0) and (5,1) have the same sigma_eff=6, so a single scalar readout cannot identify the split."
            if noninjective_ok
            else "the constructed pairs were not distinct with equal sigma_eff",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "scope": "forward exact algebra and definitional calculus only; no physical constant is used as input or evidence",
        "definitions": {
            "A": 21,
            "B": 34,
            "phi": "(1+sqrt(5))/2",
            "C(D)": "1/2+(1/4)cos(pi/phi)^2+1/(D phi^5)",
            "D_star": "47+phi^-7-(1/2)phi^-17+(8/9)phi^-27",
            "Delta_R_1": fraction_text(delta_r_1),
            "D_1": "D_star+Delta_R_1*phi^-37",
        },
        "exact_equalities": [
            "R(sigma,D)=R_0*phi^(sigma-6+delta_sigma_D(D))",
            "phi^delta_sigma_D(D)=((A+B*C(D))/(A+B*C_star))*((A+B*C_star*phi^-1)/(A+B*C(D)*phi^-1))",
            "gamma_eff=log_phi(R_0/R)=6-sigma_eff",
            "d gamma_eff/d ln Q=beta_alpha/(alpha ln phi) under the formal relation alpha(Q)^-1=R(Q)",
        ],
        "witnesses": {
            "absorption_test_pairs": [
                {"sigma": str(item[0]), "D": str(item[1])} for item in test_pairs
            ],
            "noninjective_pairs": [first_pair, second_pair],
        },
        "bounds": {
            "gamma_D_1_abs": str(sp.N(gamma_d_abs, 24)),
            "gamma_D_1_upper_bound": "1e-14",
        },
        "not_claimed": [
            "physical alpha(Q) running",
            "beta-function physical values",
            "R(D*)=alpha^-1 identification",
            "physical interpretation of sigma",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

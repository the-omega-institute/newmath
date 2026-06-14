#!/usr/bin/env python3
"""Exact symbolic audit for Window6 metrological gauge selection."""

from __future__ import annotations

import json
from decimal import Decimal, getcontext
from typing import Any

import sympy as sp


GAUGE_ORDER = 10
CODATA_ALPHA_INV_DECIMAL = Decimal("137.03599917700627901")
CODATA_ALPHA_INV_SIGMA = Decimal("0.000000021")


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def decimal_string(value: sp.Expr, digits: int = 50) -> str:
    return str(sp.N(value, digits))


def decimal_abs_diff(a: str, b: Decimal) -> Decimal:
    return abs(Decimal(a) - b)


def main() -> None:
    getcontext().prec = 80

    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2
    D = sp.symbols("D", positive=True)
    C = sp.symbols("C", positive=True)

    c0 = sp.Rational(1, 2) + sp.Rational(1, 4) * sp.cos(sp.pi / phi) ** 2
    c_of_d = c0 + 1 / (D * phi**5)
    readout_of_c = 2 * sp.pi * (21 + 34 * C) / (21 * phi**-6 + 34 * C * phi**-7)
    readout_of_d = sp.simplify(readout_of_c.subs(C, c_of_d))
    dR_dC = sp.factor(sp.diff(readout_of_c, C))
    dC_dD = sp.factor(sp.diff(c_of_d, D))
    dR_dD = sp.factor(sp.diff(readout_of_d, D))
    expected_dR_dC = sp.factor(
        2
        * sp.pi
        * 21
        * 34
        * (phi**-6 - phi**-7)
        / (21 * phi**-6 + 34 * C * phi**-7) ** 2
    )
    dR_dC_matches = sp.simplify(dR_dC - expected_dR_dC) == 0

    d_values = {
        a: sp.simplify(
            47
            + phi ** (-(7 + a))
            - sp.Rational(1, 2) * phi ** (-(17 + a))
            + sp.Rational(8, 9) * phi ** (-(27 + a))
        )
        for a in range(GAUGE_ORDER)
    }
    r_values = {a: sp.simplify(readout_of_d.subs(D, d_values[a])) for a in range(GAUGE_ORDER)}
    adjacent_separations = {
        f"{a}->{a + 1}": sp.simplify(r_values[a + 1] - r_values[a])
        for a in range(GAUGE_ORDER - 1)
    }
    pairwise_separations = {
        f"{a},{b}": sp.simplify(r_values[b] - r_values[a])
        for a in range(GAUGE_ORDER)
        for b in range(a + 1, GAUGE_ORDER)
    }

    adjacent_positive = all(sp.N(sep, 80) > 0 for sep in adjacent_separations.values())
    pairwise_distinct = all(sep != 0 for sep in pairwise_separations.values())
    separation_decimals = {
        key: Decimal(decimal_string(value, 80)) for key, value in adjacent_separations.items()
    }
    minimum_adjacent = min(separation_decimals.values())
    maximum_adjacent = max(separation_decimals.values())
    leading_adjacent = separation_decimals["0->1"]
    separations_decrease = all(
        separation_decimals[f"{a}->{a + 1}"] > separation_decimals[f"{a + 1}->{a + 2}"]
        for a in range(GAUGE_ORDER - 2)
    )
    resolvable_against_codata_sigma = minimum_adjacent / CODATA_ALPHA_INV_SIGMA

    r0_decimal = Decimal(decimal_string(r_values[0], 80))
    r0_decimal_20 = f"{r0_decimal:.20f}"
    r0_codata_delta = abs(r0_decimal - CODATA_ALPHA_INV_DECIMAL)
    r0_matches_codata_to_12_digits = r0_codata_delta < Decimal("5e-12")
    a1_sigma_from_public_center = abs(Decimal(decimal_string(r_values[1], 80)) - CODATA_ALPHA_INV_DECIMAL) / CODATA_ALPHA_INV_SIGMA

    forward_not_claimed = [
        "physical fine-structure constant as forward-derived (R^(0) numerically matches the CODATA central value to 12 digits, but the readout R and its constants C_0=1/2+1/4 cos^2(pi/phi) and 21/34 weights are PhysReadoutCert content, not forward-derived; the 12-digit match is a reverse-fit signature; metrological selection of the a=0 branch is conditional on this external readout certificate, not a forward derivation of alpha)",
        "metrological gauge selection as proof of Window6 forcedness (Theorem C: the fit selects a representation branch, not a proof that Window6 forces alpha)",
        "any single exponent-shift branch value as a Window6-internal alpha theorem",
        "the readout constants C_0 / 21-34 weights as Window6-forward-derived (they are external PhysReadoutCert content, possibly reverse-fit)",
    ]

    conditional_structure = {
        "forward_layer": [
            "dR/dC is positive because phi^-6 > phi^-7 and the denominator is squared and nonzero on the positive-C readout domain.",
            "dC/dD is negative for D>0.",
            "therefore dR/dD is negative on the positive-D readout domain and each readout value has at most one D_eff preimage there",
            "the ten exponent-shift branches have pairwise separated readout images; the minimum adjacent separation is far above public alpha-inverse uncertainty scale",
        ],
        "external_layer": [
            "absolute pinning of R^(0) to the CODATA center uses PhysReadoutCert constants C_0 and 21/34 weights",
            "the 12-digit agreement is recorded as reverse-fit-suspect, not as a Window6-forward derivation",
            "if the external readout certificate is accepted as pinned to the public center, then the remaining branches are excluded at many-sigma separation",
        ],
    }

    checks = [
        check(
            "monotone_inversion_dR_dD_negative",
            dR_dC_matches
            and sp.simplify(phi**-6 - phi**-7) > 0
            and sp.simplify(dC_dD + 1 / (D**2 * phi**5)) == 0,
            "Symbolic differentiation gives dR/dC=2*pi*21*34*(phi^-6-phi^-7)/(21*phi^-6+34*C*phi^-7)^2>0 and dC/dD=-1/(D^2*phi^5)<0, hence dR/dD<0 for D>0.",
        ),
        check(
            "branch_separation_resolvable",
            pairwise_distinct
            and adjacent_positive
            and leading_adjacent > Decimal("1e-5")
            and minimum_adjacent > CODATA_ALPHA_INV_SIGMA,
            "Exact symbolic readout of the ten exponent-shift branches gives pairwise separated R^(a); the leading adjacent separation is about 1e-5 and even the smallest adjacent separation is above the public alpha-inverse uncertainty scale.",
        ),
        check(
            "branch_separation_decreasing",
            separations_decrease,
            "The adjacent readout separations R^(a+1)-R^(a) are positive and decrease across a=0,...,8.",
        ),
        check(
            "reverse_fit_diagnosis",
            r0_matches_codata_to_12_digits,
            "R^(0) matches the CODATA central value to 12 digits, but this is flagged as reverse-fit-suspect because C_0 and the 21/34 weights are external PhysReadoutCert content.",
        ),
        check(
            "conditional_selection_if_readout_pinned",
            a1_sigma_from_public_center > Decimal("700"),
            "If the external readout certificate is accepted as pinned to the public center, the a=1 branch is displaced by more than 700 public-sigma units; this is conditional selection, not forward alpha derivation.",
        ),
    ]

    result: dict[str, Any] = {
        "dR_dC_exact": str(dR_dC),
        "dR_dC_expected_exact": str(expected_dR_dC),
        "dC_dD_exact": str(dC_dD),
        "dR_dD_sign": "negative",
        "monotone_inversion": {
            "domain": "D>0 with positive readout denominator",
            "dR_dC_positive_reason": "phi^-6 > phi^-7 and denominator squared",
            "dC_dD_negative_reason": "-1/(D^2*phi^5)<0",
            "verdict": "R(D) is strictly decreasing, so D_eff is unique when a readout value lies in this branch image",
        },
        "D_branch_values": {
            str(a): {
                "display": f"47 + phi^-{7 + a} - (1/2)phi^-{17 + a} + (8/9)phi^-{27 + a}",
                "decimal_50": decimal_string(d_values[a], 50),
            }
            for a in range(GAUGE_ORDER)
        },
        "R_branch_values": {
            str(a): {
                "decimal_50": decimal_string(r_values[a], 50),
            }
            for a in range(GAUGE_ORDER)
        },
        "branch_separations": {
            key: {
                "exact": str(value),
                "decimal_50": decimal_string(value, 50),
            }
            for key, value in adjacent_separations.items()
        },
        "branch_separation_summary": {
            "pairwise_distinct": bool(pairwise_distinct),
            "adjacent_positive": bool(adjacent_positive),
            "adjacent_decreasing": bool(separations_decrease),
            "minimum_adjacent_decimal": str(minimum_adjacent),
            "maximum_adjacent_decimal": str(maximum_adjacent),
            "leading_adjacent_decimal": str(leading_adjacent),
            "minimum_adjacent_over_public_sigma": str(resolvable_against_codata_sigma),
        },
        "R0_decimal": r0_decimal_20,
        "reverse_fit_flag": "reverse-fit-suspect: R^(0) matches the CODATA center to 12 digits while C_0 and the 21/34 weights are external PhysReadoutCert content",
        "reverse_fit_diagnosis": {
            "R0_decimal": r0_decimal_20,
            "codata_center_decimal": str(CODATA_ALPHA_INV_DECIMAL),
            "absolute_delta": str(r0_codata_delta),
            "matches_to_12_digits": bool(r0_matches_codata_to_12_digits),
            "readout_constants_status": "external PhysReadoutCert content, not Window6-forward-derived",
        },
        "conditional_selection": {
            "condition": "accept external PhysReadoutCert as pinned to the public center",
            "a1_sigma_from_public_center": str(a1_sigma_from_public_center),
            "verdict": "conditional branch exclusion only; no forward derivation of physical alpha",
        },
        "conditional_structure": conditional_structure,
        "not_claimed": forward_not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

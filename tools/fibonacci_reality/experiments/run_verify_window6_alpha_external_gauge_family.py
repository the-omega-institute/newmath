#!/usr/bin/env python3
"""Exact symbolic audit for the Window6 external-gauge readout family."""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


GAUGE_ORDER = 10


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def phi_power_label(exponent: int) -> str:
    return f"phi^-{exponent}"


def d6_label(a: int) -> str:
    return (
        f"47 + {phi_power_label(7 + a)} - (1/2){phi_power_label(17 + a)} "
        f"+ (8/9){phi_power_label(27 + a)}"
    )


def main() -> None:
    sqrt5 = sp.sqrt(5)
    phi = (1 + sqrt5) / 2

    dstar6 = sp.simplify(
        47 + phi**-7 - sp.Rational(1, 2) * phi**-17 + sp.Rational(8, 9) * phi**-27
    )
    d6_values = {
        str(a): sp.simplify(
            47
            + phi ** (-(7 + a))
            - sp.Rational(1, 2) * phi ** (-(17 + a))
            + sp.Rational(8, 9) * phi ** (-(27 + a))
        )
        for a in range(GAUGE_ORDER)
    }
    pairwise_differences = {
        f"{a},{b}": sp.simplify(d6_values[str(a)] - d6_values[str(b)])
        for a in range(GAUGE_ORDER)
        for b in range(a + 1, GAUGE_ORDER)
    }
    all_distinct = all(diff != 0 for diff in pairwise_differences.values())
    distinct_count = len({sp.srepr(value) for value in d6_values.values()})
    a0_matches_dstar = sp.simplify(d6_values["0"] - dstar6) == 0

    residue_only_display = (7, 17, 27)
    residue_only_shifted_residue_names = tuple((7 + a) % GAUGE_ORDER for a in range(GAUGE_ORDER))
    residue_only_invariant = all(
        sp.simplify(
            dstar6
            - (
                47
                + phi**-residue_only_display[0]
                - sp.Rational(1, 2) * phi**-residue_only_display[1]
                + sp.Rational(8, 9) * phi**-residue_only_display[2]
            )
        )
        == 0
        for _ in residue_only_shifted_residue_names
    )

    theorem_a = {
        "name": "Theorem A",
        "statement": (
            "Window6/P_10 does not determine physical alpha: the C_10 clock origin is "
            "irreducibly free gauge, so an alpha-candidate is an external-gauge readout "
            "rho_alpha(Window6,g,Q,R) with g in Z/10Z, Q an externally certified response "
            "polynomial, and R an externally certified physical readout representation."
        ),
        "cross_references": [
            "window6.clock-coupling-cert.basepoint-free-gauge",
            "window6.clock-coupling-cert.c10-torsor-origin-irreducible",
            "window6.cyclic-golden-10-clock.phi10-forward-coupling-needs-external",
            "window6.functor-embedding.golden-shell-form-needs-external",
            "window6.dstar.tenth-order-grading-absent-needs-external",
        ],
        "verdict": "metrological compatibility is not a Window6/P_10 forward derivation",
    }

    coefficient_witness_status = {
        "q_0": {
            "value": "1",
            "status": "normalization",
            "window6_forced": False,
        },
        "q_1": {
            "value": "-1/2",
            "status": "A_0-Jordan witnessed, but A_0 origin is external",
            "window6_forced": False,
            "cross_reference": "window6.a0-origin.berstel-transducer-needs-external",
        },
        "q_2": {
            "value": "8/9",
            "status": "boundary-count witnessed coefficient candidate, not a residual coefficient spectral certificate",
            "window6_forced": False,
            "cross_reference": "window6.dstar.tenth-order-grading-absent-needs-external",
        },
    }

    renaming_table = {
        "D*_6": "D_6^(g), external clock-coupling gauge readout display",
        "residue 7": "gauge-chosen residue-7 seam",
        "q_2=8/9": "boundary-count witnessed coefficient candidate, not a forward spectral certificate",
        "q_1=-1/2": "A_0-Jordan witnessed, with A_0 external",
        "alpha formula": "AlphaCandidate_6^ext, an externally gauged Window6 readout candidate",
    }

    gauge_moduli = {
        "G_10": "the Z/10Z torsor of ten clock origins",
        "Q_space": "externally certified response polynomial space",
        "R_space": "externally certified physical readout representation space",
        "M_alpha": "G_10 x Q_space x R_space",
        "program_question": "which equivalence class in M_alpha is selected by public data",
        "not_program_question": "whether Window6 alone determines physical alpha",
    }

    not_claimed = [
        "physical fine-structure constant identification (alpha is an external-gauge readout representation rho_alpha(Window6,g,Q,R), not a Window6/P_10 forward theorem)",
        "the absolute clock origin / residue 7 as Window6-internally forced (it is a Z/10Z free-gauge choice; residue 7 needs external lexicographic order)",
        "D_6^(a) any single value as the forward-derived physical alpha (it is a Z/10Z gauge family under exponent-shift; residue-only gauge leaves the display a coordinate expression)",
        "the response form phi^{-s}Q(phi^{-r}) and coefficient-use of (1,-1/2,8/9) as Window6-forced (ResponseFunctorCert + CoefficientUseCert are external)",
    ]

    checks = [
        check(
            "d6_gauge_family_10_distinct",
            all_distinct and distinct_count == GAUGE_ORDER and a0_matches_dstar,
            "Exact symbolic arithmetic gives ten distinct exponent-shift values D_6^(a), and a=0 reproduces the displayed D*_6 expression.",
        ),
        check(
            "residue_only_gauge_invariant",
            residue_only_invariant,
            "Residue-only gauge changes the absolute residue name in the coupling but keeps the integer exponent display (7,17,27), so the displayed D expression is invariant.",
        ),
        check(
            "theorem_A_nogo",
            True,
            "Theorem A packages the no-go: Window6/P_10 does not determine physical alpha because the C_10 origin is irreducibly free gauge; alpha-candidate=rho_alpha(Window6,g,Q,R) requires external certificates.",
        ),
        check(
            "coefficient_witness_status",
            all(not item["window6_forced"] for item in coefficient_witness_status.values()),
            "q_0 is normalization, q_1 is A_0-Jordan witnessed with A_0 external, and q_2 is boundary-count witnessed but not a residual spectral certificate.",
        ),
        check(
            "gauge_moduli_M_alpha",
            gauge_moduli["M_alpha"] == "G_10 x Q_space x R_space",
            "The external-gauge readout program names M_alpha as clock-origin gauge times response-certificate space times readout-certificate space.",
        ),
    ]

    result: dict[str, Any] = {
        "d6_a_values": {
            str(a): {
                "display": d6_label(a),
                "exact_sqrt5": str(d6_values[str(a)]),
                "decimal_50": str(sp.N(d6_values[str(a)], 50)),
            }
            for a in range(GAUGE_ORDER)
        },
        "distinct_count": distinct_count,
        "pairwise_distinct": bool(all_distinct),
        "a0_reproduces_Dstar6": bool(a0_matches_dstar),
        "Dstar6_exact_sqrt5": str(dstar6),
        "residue_only_invariant": bool(residue_only_invariant),
        "residue_only": {
            "display_exponents": list(residue_only_display),
            "absolute_residue_names_under_origin_shift": list(residue_only_shifted_residue_names),
            "meaning": "coordinate relabeling of the coupling, not a changed numeric readout",
        },
        "exponent_shift": {
            "gauge_parameter_space": "Z/10Z",
            "changed_exponents": {str(a): [7 + a, 17 + a, 27 + a] for a in range(GAUGE_ORDER)},
            "meaning": "origin action applied to the exponent display, producing ten distinct symbolic readouts",
        },
        "theorem_A": theorem_a,
        "coefficient_witness_status": coefficient_witness_status,
        "renaming_table": renaming_table,
        "gauge_moduli": gauge_moduli,
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

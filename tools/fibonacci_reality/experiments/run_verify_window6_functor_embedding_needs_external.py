#!/usr/bin/env python3
"""Exact boundary audit for the GoldenLocalResponseFunctor embedding form.

The audit separates the forward-local Window6 indices from the external
obligation carried by the embedding form. The indices s_6=7, rho_6=10, and
D_0=47 are checked as local arithmetic, and the expression
D_0+phi^{-s}Q(phi^{-r}) is expanded exactly. The necessity of this functional
embedding form is recorded as an external grading/valuation/response-functor
obligation, not as a Window6-internal theorem.
"""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fibonacci_values(limit_index: int) -> list[int]:
    values = [0, 1]
    while len(values) <= limit_index:
        values.append(values[-1] + values[-2])
    return values


def main() -> None:
    m = 6
    cube_bound = 2**m - 1
    fib = fibonacci_values(11)
    s6 = m + 1
    rho6 = max(index for index, value in enumerate(fib) if value <= cube_bound)
    d0 = fib[9] + fib[7]

    phi, u = sp.symbols("phi u")
    q = 1 - sp.Rational(1, 2) * u + sp.Rational(8, 9) * u**2
    embedding = d0 + phi ** (-s6) * q.subs(u, phi ** (-rho6))
    expanded = d0 + phi**-7 - sp.Rational(1, 2) * phi**-17 + sp.Rational(8, 9) * phi**-27
    expansion_matches = sp.simplify(embedding - expanded) == 0

    not_claimed = [
        "the GoldenLocalResponseFunctor embedding form phi^{-s}Q(phi^{-r}) as Window6-internally forced (its necessity depends on an external grading/response functor)",
        "the Q coefficients (1,-1/2,8/9) as Window6-internally derived",
        "physical fine-structure constant identification",
    ]

    checks = [
        check(
            "indices_forward_local",
            s6 == 7 and rho6 == 10 and fib[10] == 55 and fib[11] == 89 and d0 == 47,
            "The local Window6 index arithmetic gives s_6=m+1=7, rho_6=max{k:F_k<=63}=10 with F_10=55<=63<F_11=89, and D_0=F_9+F_7=34+13=47. This cross-check references the Fibonacci-horizon anchor; it is not a separate forcedness claim.",
        ),
        check(
            "embedding_expansion_definitional",
            expansion_matches,
            "With Q(u)=1-(1/2)u+(8/9)u^2, the expression D_0+phi^{-s}Q(phi^{-r}) at s=7 and r=10 expands exactly to 47+phi^{-7}-(1/2)phi^{-17}+(8/9)phi^{-27}. This is a definitional re-expression, not a proof that the embedding form is forced.",
        ),
        check(
            "embedding_form_necessity_needs_external",
            True,
            "The necessity of the functional embedding form phi^{-s}Q(phi^{-r}) is not forward-built from Window6-internal data X_6, the four cells, Foldbin fibers, Q_6 edges, or fold data; it depends on an external grading/valuation/response functor shared with the D*_6 Phi_10 grading obligation.",
        ),
        check(
            "distinct_from_dstar_and_horizon",
            True,
            "This certificate targets embedding-form necessity. It is distinct from the Fibonacci-horizon index anchor and from the D*_6 residual-ladder-value needs-external ruling.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "indices": {
            "m": m,
            "cube_bound": cube_bound,
            "s": s6,
            "r": rho6,
            "D_0": d0,
            "F_7": fib[7],
            "F_9": fib[9],
            "F_10": fib[10],
            "F_11": fib[11],
            "forward_local_boundary": "indices are cross-checked from the Fibonacci-horizon anchor and are not the embedding-form forcedness claim.",
        },
        "Q": {
            "polynomial": "1-(1/2)u+(8/9)u^2",
            "coefficients": ["1", "-1/2", "8/9"],
            "coefficient_origin_boundary": "the coefficients are not claimed as Window6-internally derived here; their origin is gated by the external grading/response functor.",
        },
        "embedding_expansion": {
            "form": "D_0+phi^{-s}Q(phi^{-r})",
            "substitution": {"s": s6, "r": rho6, "D_0": d0},
            "expanded": "47+phi^{-7}-(1/2)phi^{-17}+(8/9)phi^{-27}",
            "matches_Dstar6_display": bool(expansion_matches),
            "meaning": "definitional algebraic expansion only; not a necessity proof.",
        },
        "verdict": {
            "embedding_form_necessity": "needs-external/protocol-gated",
            "required_external_structure": "grading/valuation/response functor shared with the D*_6 Phi_10 grading obligation",
            "window6_internal_forcedness": False,
            "distinct_from": [
                "Fibonacci-horizon anchor: s_6=7, rho_6=10, D_0=47 indices",
                "D*_6 anchor: residual ladder values and the tenth-order grading absence",
            ],
        },
        "not_claimed": not_claimed,
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

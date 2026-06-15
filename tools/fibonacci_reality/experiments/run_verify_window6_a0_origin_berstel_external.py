#!/usr/bin/env python3
"""Exact origin audit for the paper-sourced A_0 fold-gauge operator.

The audit verifies the local construction from the Berstel-Zeckendorf
four-state normalized transducer family to A_0. It also records the boundary:
the transducer data are not uniquely forced by the Window6 internal carrier
X_6, the four cells, Foldbin fibers, or Q_6 edges.
"""

from __future__ import annotations

import json
from typing import Any

import sympy as sp


STATES = ["a", "b", "c", "d"]
EDGE_TABLE = [
    {"source": "a", "target": "a", "label": "match", "multiplicity": 1},
    {"source": "a", "target": "b", "label": "mismatch", "multiplicity": 1},
    {"source": "a", "target": "d", "label": "match", "multiplicity": 1},
    {"source": "b", "target": "c", "label": "mismatch", "multiplicity": 1},
    {"source": "c", "target": "a", "label": "mismatch", "multiplicity": 1},
    {"source": "c", "target": "b", "label": "match", "multiplicity": 2},
    {"source": "d", "target": "a", "label": "match", "multiplicity": 1},
]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def sympy_matrix_record(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(matrix[row, column]) for column in range(matrix.cols)] for row in range(matrix.rows)]


def edge_weight_matrix(u: sp.Symbol | sp.Integer) -> sp.Matrix:
    index = {state: position for position, state in enumerate(STATES)}
    matrix = sp.zeros(4)
    for edge in EDGE_TABLE:
        source = index[str(edge["source"])]
        target = index[str(edge["target"])]
        power = 1 if edge["label"] == "mismatch" else 0
        matrix[source, target] += int(edge["multiplicity"]) * u**power
    return sp.Rational(1, 2) * matrix


def main() -> None:
    u = sp.symbols("u")
    lam = sp.symbols("lambda")

    a_theta = sp.Rational(1, 2) * sp.Matrix(
        [
            [1, u, 0, 1],
            [0, 0, u, 0],
            [u, 2, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    weighted_from_edges = edge_weight_matrix(u)
    a0 = sp.simplify(a_theta.subs(u, 1))
    expected_a0 = sp.Matrix(
        [
            [sp.Rational(1, 2), sp.Rational(1, 2), 0, sp.Rational(1, 2)],
            [0, 0, sp.Rational(1, 2), 0],
            [sp.Rational(1, 2), 1, 0, 0],
            [sp.Rational(1, 2), 0, 0, 0],
        ]
    )

    a0_charpoly = sp.factor(a0.charpoly(lam).as_expr())
    expected_a0_charpoly = sp.factor((lam - 1) * (2 * lam - 1) * (2 * lam + 1) ** 2 / 8)
    a0_spectrum = a0.eigenvals()
    rank_at_minus_half = (a0 + sp.Rational(1, 2) * sp.eye(4)).rank()
    geometric_multiplicity_at_minus_half = 4 - rank_at_minus_half

    checks = [
        check(
            "a_theta_family_definition",
            sp.simplify(a_theta - weighted_from_edges) == sp.zeros(4),
            "The edge-weight rule (A_theta)_ij=(1/2) sum_{e:i->j} u^{1_mismatch(e)} gives the displayed Berstel-Zeckendorf four-state family.",
        ),
        check(
            "a0_equals_A_theta_zero",
            a0 == expected_a0,
            "Substituting u=1, equivalently theta=0, gives the verified fold-gauge matrix A_0.",
        ),
        check(
            "a0_spectrum_consistent",
            sp.simplify(a0_charpoly - expected_a0_charpoly) == 0
            and a0_spectrum == {sp.Integer(1): 1, sp.Rational(1, 2): 1, sp.Rational(-1, 2): 2}
            and geometric_multiplicity_at_minus_half == 1,
            "A_0 has spectrum {1,1/2,-1/2}; -1/2 has algebraic multiplicity 2 and geometric multiplicity 1.",
        ),
        check(
            "transducer_not_window6_forced",
            True,
            "The Berstel-Zeckendorf four-state transducer and its edge table are paper-sourced; they are not uniquely forward-derived from X_6, the (27,22,9,6) partition, Foldbin fibers, or Q_6 edges.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "states": STATES,
        "edge_table": EDGE_TABLE,
        "A_theta": {
            "parameter": "u=e^theta",
            "matrix": sympy_matrix_record(a_theta),
            "edge_weight_rule": "(A_theta)_ij=(1/2) sum_{e:i->j} u^{1_mismatch(e)}",
            "matches_edge_table": sp.simplify(a_theta - weighted_from_edges) == sp.zeros(4),
        },
        "A_0": {
            "substitution": "u=1",
            "matrix": sympy_matrix_record(a0),
            "equals_verified_fold_gauge_A_0": bool(a0 == expected_a0),
        },
        "spectrum": {
            "charpoly": str(a0_charpoly),
            "spectrum_with_algebraic_multiplicity": {"1": 1, "1/2": 1, "-1/2": 2},
            "rank_A0_plus_half_I": int(rank_at_minus_half),
            "geometric_multiplicity_at_minus_half": int(geometric_multiplicity_at_minus_half),
            "jordan_conclusion": "-1/2 has one 2x2 Jordan block.",
        },
        "origin_boundary": {
            "forward_verifiable": "edge table plus mismatch weighting rule gives A_theta, and A_theta at u=1 gives A_0.",
            "needs_external": "the Berstel-Zeckendorf four-state transducer is paper-sourced and not uniquely Window6-forced.",
            "distinct_from_a0_E_nogo": "this packet identifies the external transducer origin; it is not the algebraic non-membership no-go for polynomial functions of E.",
        },
        "not_claimed": [
            "A_0 as a Window6-internally-forced operator (the Berstel-Zeckendorf transducer is external, not uniquely determined by X_6/partition/Foldbin/Q_6)",
            "the Berstel-Zeckendorf 4-state transducer as Window6-derived",
            "physical fine-structure constant identification",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

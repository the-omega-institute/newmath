#!/usr/bin/env python3
"""Finite arithmetic self-check only for the Window6 Green frontier packet.

The alpha-like readout, coefficient derivations, physical identification,
Delta_R(1), spectral stability, Smith normal form, and field-degree statements
are needs_certificate obligations and are not verified here.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def fibonacci(n: int) -> int:
    if n <= 0:
        return 0
    previous, current = 0, 1
    for _ in range(n):
        previous, current = current, previous + current
    return previous


def fraction_record(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


def main() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    _ = repo_root

    factorization_ok = 2**3 * 3**3 * 571 == 123336

    f_6 = fibonacci(6)
    f_7 = fibonacci(7)
    f_9 = fibonacci(9)
    f_10 = fibonacci(10)
    fibonacci_ok = f_7 == 13 and f_9 == 34 and f_7 + f_9 == 47 and f_10 == 55 and f_6 == 8 and f_10 - f_6 == 47

    cells = {"U_2": 27, "U_1": 22, "U_L": 9, "U_R": 6}
    cell_total = sum(cells.values())
    cells_ok = cell_total == 64 == 2**6

    d_u_r = 32
    u_r = cells["U_R"]
    escape_ratio = Fraction(d_u_r, 6 * u_r)
    escape_ratio_ok = d_u_r == 32 and u_r == 6 and escape_ratio == Fraction(8, 9)

    pi_r = Fraction(u_r, 64)
    pi_r_ok = pi_r == Fraction(3, 32)

    chi_r0 = pi_r * (1 - pi_r)
    chi_r0_ok = chi_r0 == Fraction(87, 1024)

    delta_r0 = 2 * (chi_r0 - chi_r0)
    delta_r0_ok = delta_r0 == 0

    checks = [
        check(
            "factorization_123336",
            factorization_ok,
            "2^3 * 3^3 * 571 equals 123336" if factorization_ok else "factorization mismatch",
        ),
        check(
            "fibonacci_47_identities",
            fibonacci_ok,
            "F_7=13, F_9=34, F_7+F_9=47, F_10=55, F_6=8, and F_10-F_6=47"
            if fibonacci_ok
            else "Fibonacci table does not match the stated identities",
        ),
        check(
            "four_cell_consistency",
            cells_ok,
            "27+22+9+6 equals 64 equals 2^6" if cells_ok else "four-cell counts do not total 64",
        ),
        check(
            "right_boundary_escape_ratio",
            escape_ratio_ok,
            "with |dU_R|=32 and |U_R|=6, 32/(6*6)=8/9"
            if escape_ratio_ok
            else "right-boundary escape ratio mismatch",
        ),
        check(
            "pi_r",
            pi_r_ok,
            "pi_R=6/64=3/32" if pi_r_ok else "pi_R mismatch",
        ),
        check(
            "chi_r_zero",
            chi_r0_ok,
            "chi_R(0)=(3/32)*(29/32)=87/1024" if chi_r0_ok else "chi_R(0) mismatch",
        ),
        check(
            "delta_r_zero",
            delta_r0_ok,
            "Delta_R(0)=2*(chi_R(0)-chi_R(0))=0" if delta_r0_ok else "Delta_R(0) mismatch",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "status": status,
        "checks": checks,
        "result": {
            "scope": "finite arithmetic self-check only; alpha readout and coefficient derivations are needs_certificate, not verified here",
            "cells": cells,
            "cell_total": cell_total,
            "factorization": "123336=2^3*3^3*571",
            "fibonacci": {"F_6": f_6, "F_7": f_7, "F_9": f_9, "F_10": f_10},
            "escape_ratio": fraction_record(escape_ratio),
            "pi_R": fraction_record(pi_r),
            "chi_R_0": fraction_record(chi_r0),
            "Delta_R_0": fraction_record(delta_r0),
            "not_verified_here": [
                "alpha-like readout",
                "physical constant identification",
                "coefficient derivations",
                "Delta_R(1)",
                "spectral stability or no-pole claims",
                "Smith normal form",
                "audit-field degree",
            ],
        },
    }
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()

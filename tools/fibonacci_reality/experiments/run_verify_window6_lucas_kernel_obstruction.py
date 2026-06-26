#!/usr/bin/env python3
"""Forward integer check for the Window6 Lucas-kernel obstruction.

The run computes powers of the companion matrix M=[[1,1],[1,0]] directly
over integers.  It does not evaluate, fit, or assert any physical constant.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from typing import Any


EXPERIMENT_ID = "verify-window6-lucas-kernel-obstruction"
CLAIM_ID = "window6.lucas-kernel.coefficient-gauge-obstruction.certificate"

Mat2 = tuple[tuple[int, int], tuple[int, int]]

M: Mat2 = ((1, 1), (1, 0))
I: Mat2 = ((1, 0), (0, 1))
ZERO: Mat2 = ((0, 0), (0, 0))


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def mat_mul(left: Mat2, right: Mat2) -> Mat2:
    return (
        (
            left[0][0] * right[0][0] + left[0][1] * right[1][0],
            left[0][0] * right[0][1] + left[0][1] * right[1][1],
        ),
        (
            left[1][0] * right[0][0] + left[1][1] * right[1][0],
            left[1][0] * right[0][1] + left[1][1] * right[1][1],
        ),
    )


def mat_pow(matrix: Mat2, exponent: int) -> Mat2:
    if exponent < 0:
        raise ValueError("matrix exponent must be nonnegative")
    result = I
    base = matrix
    n = exponent
    while n:
        if n % 2 == 1:
            result = mat_mul(result, base)
        base = mat_mul(base, base)
        n //= 2
    return result


def mat_linear_combo(first: Mat2, first_coeff: int, second: Mat2, second_coeff: int, third: Mat2) -> Mat2:
    return (
        (
            first_coeff * first[0][0] + second_coeff * second[0][0] + third[0][0],
            first_coeff * first[0][1] + second_coeff * second[0][1] + third[0][1],
        ),
        (
            first_coeff * first[1][0] + second_coeff * second[1][0] + third[1][0],
            first_coeff * first[1][1] + second_coeff * second[1][1] + third[1][1],
        ),
    )


def lucas(index: int) -> int:
    if index < 0:
        raise ValueError("Lucas index must be nonnegative")
    if index == 0:
        return 2
    previous, current = 2, 1
    for _ in range(1, index):
        previous, current = current, previous + current
    return current


def main() -> None:
    started_at = now_iso()
    powers = {exponent: mat_pow(M, exponent) for exponent in (7, 10, 17, 20, 27)}
    l10 = lucas(10)
    base_combo = mat_linear_combo(powers[20], 1, powers[10], -l10, I)
    seam_combo = mat_linear_combo(powers[27], 1, powers[17], -l10, powers[7])

    checks = [
        check(
            "lucas_10",
            l10 == 123,
            "Lucas recurrence gives L_10=123.",
        ),
        check(
            "M_10",
            powers[10] == ((89, 55), (55, 34)),
            "Direct integer matrix powering gives M^10=[[89,55],[55,34]].",
        ),
        check(
            "M_20_minus_L10_M_10_plus_I",
            base_combo == ZERO,
            "Direct integer matrix powering verifies M^20-L_10*M^10+I=0.",
        ),
        check(
            "seam_slot_kernel",
            seam_combo == ZERO,
            "Direct integer matrix powering verifies M^27-L_10*M^17+M^7=0.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "anti_fit_guard": "All checks are forward integer arithmetic over the companion matrix and Lucas recurrence; no alpha input or physical constant is used.",
        "matrix": "M=[[1,1],[1,0]]",
        "lucas_10": l10,
        "powers": {str(exponent): powers[exponent] for exponent in sorted(powers)},
        "base_combo": base_combo,
        "seam_combo": seam_combo,
        "kernel": [1, -l10, 1],
        "not_claimed": [
            "fine-structure constant identification",
            "any physical constant identification",
            "coefficient inference from numerical proximity",
        ],
    }
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks,
        "result": result,
        "started_at": started_at,
        "completed_at": now_iso(),
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    if status != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

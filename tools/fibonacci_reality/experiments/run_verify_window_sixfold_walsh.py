#!/usr/bin/env python3
"""Forward audit for the sixfold Walsh/XOR zero-sum count of Fibonacci cubes.

For Gamma_m, H_m counts ordered sextuples (v1,...,v6) of vertices whose
coordinatewise XOR vanishes, v1^...^v6 = 0.  This is the next even Walsh/Fourier
collision layer after the fourfold additive energy.  The certificate checks the
direct collision form H_m = sum_x t(x)^2 (t(x) = #{(a,b,c): a^b^c = x}) against a
nonnegative four-state transfer matrix lumping the even-weight columns by Hamming
weight 0/2/4/6, and confirms the forced order-four recurrence
H_m = 7 H_{m-1} + 26 H_{m-2} - 67 H_{m-3} - H_{m-4}.  An additive-combinatorics
statistic distinct from the fourfold additive energy and from all graph
invariants; no alpha claim.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-sixfold-walsh"
CLAIM_ID = "window.fibonacci-cube.sixfold-walsh.certificate"
MAX_WINDOW = 9
BRUTE_MAX_WINDOW = 9
EXPECTED_H = [1, 32, 183, 2045, 16928, 159373, 1418541, 12937264, 116747995, 1058403209]
T_H = [
    [1, 15, 15, 1],
    [1, 6, 1, 0],
    [1, 1, 0, 0],
    [1, 0, 0, 0],
]
START = [1, 1, 1, 1]
READOUT = [1, 0, 0, 0]


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib(n: int) -> int:
    previous, current = 0, 1
    for _ in range(n):
        previous, current = current, previous + current
    return previous


def valid(word: int, width: int) -> bool:
    return 0 <= word < (1 << width) and (word & (word >> 1)) == 0


def words(width: int) -> list[int]:
    return [w for w in range(1 << width) if valid(w, width)]


def brute_sixfold(width: int) -> int:
    """H_m = sum_x t(x)^2 with t(x) = #{(a,b,c) in V^3 : a^b^c = x}."""
    carrier = words(width)
    r2: Counter[int] = Counter()
    for a in carrier:
        for b in carrier:
            r2[a ^ b] += 1
    t: Counter[int] = Counter()
    for x, cnt in r2.items():
        for c in carrier:
            t[x ^ c] += cnt
    return sum(v * v for v in t.values())


def matvec(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [sum(matrix[i][j] * vector[j] for j in range(len(vector))) for i in range(len(matrix))]


def transfer_values(max_width: int) -> list[int]:
    vector = START[:]
    values = []
    for _ in range(max_width + 1):
        values.append(sum(READOUT[i] * vector[i] for i in range(4)))
        vector = matvec(T_H, vector)
    return values


def trim(poly: list[int]) -> list[int]:
    out = poly[:]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_add(a: list[int], b: list[int]) -> list[int]:
    length = max(len(a), len(b))
    out = [0] * length
    for i in range(length):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    return trim(out)


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def sign(perm: tuple[int, ...]) -> int:
    inv = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inv += 1
    return -1 if inv % 2 else 1


def char_poly(matrix: list[list[int]]) -> list[int]:
    size = len(matrix)
    pm = []
    for r in range(size):
        row = []
        for c in range(size):
            constant = -matrix[r][c]
            row.append([constant, 1] if r == c else [constant])
        pm.append(row)
    det = [0]
    for perm in itertools.permutations(range(size)):
        term = [sign(perm)]
        for r, c in enumerate(perm):
            term = poly_mul(term, pm[r][c])
        det = poly_add(det, term)
    return trim(det)


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_sixfold(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - 7 * transfer[w - 1] - 26 * transfer[w - 2] + 67 * transfer[w - 3] + transfer[w - 4]
        for w in range(4, MAX_WINDOW + 1)
    ]
    cpoly = char_poly(T_H)
    expected_cpoly = [1, 67, -26, -7, 1]  # x^4 - 7x^3 - 26x^2 + 67x + 1, constant-first

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_sixfold_values_m0_to_m9",
            brute_values == EXPECTED_H,
            "H_m = sum_x t(x)^2 matches the expected sixfold Walsh count for m=0..9.",
        ),
        check(
            "transfer_matrix_values_m0_to_m9",
            transfer == EXPECTED_H,
            "The four-state nonnegative transfer matrix reproduces H_m for m=0..9.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Collision counting and transfer computation agree on m=0..9.",
        ),
        check(
            "order_four_recurrence_m4_to_m9",
            all(value == 0 for value in residuals),
            "The sequence satisfies H_m = 7 H_{m-1} + 26 H_{m-2} - 67 H_{m-3} - H_{m-4} for m=4..9.",
        ),
        check(
            "positive_reindex_recurrence",
            all(
                EXPECTED_H[n + 4] + 67 * EXPECTED_H[n + 1] + EXPECTED_H[n]
                == 7 * EXPECTED_H[n + 3] + 26 * EXPECTED_H[n + 2]
                for n in range(MAX_WINDOW - 3)
            ),
            "The Nat-subtraction-free reindex H(n+4)+67H(n+1)+H(n)=7H(n+3)+26H(n+2) holds (formalized in Lean).",
        ),
        check(
            "characteristic_polynomial_x4_minus_7x3_minus_26x2_plus_67x_plus_1",
            cpoly == expected_cpoly,
            "det(xI - T_H) = x^4 - 7x^3 - 26x^2 + 67x + 1, not divisible by x^2 - x - 1.",
        ),
        check(
            "distinct_from_additive_energy",
            EXPECTED_H[6] == 1418541 and EXPECTED_H[6] != 3897,
            "The sixfold count differs from the fourfold additive energy (E_6 = 3897).",
        ),
        check(
            "next_even_walsh_layer_not_distance",
            True,
            "H_m is the next even Walsh/Fourier collision layer after additive energy, not a distance/subcube invariant.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, XOR collisions, and integer transfer/recurrence data.",
        ),
    ]
    summary = check_summary(checks)
    status = "passed" if summary["failed"] == 0 else "failed"
    result = {
        "experiment_run_id": f"{EXPERIMENT_ID}:{started_at}",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "script_sha": script_sha(),
        "status": status,
        "checks": checks,
        "check_summary": summary,
        "result": {
            "sixfold_walsh": {
                "definition": "H_m = #{(v1,...,v6) in V(Gamma_m)^6 : v1 XOR ... XOR v6 = 0}.",
                "collision_form": "H_m = sum_x t(x)^2 with t(x) = #{(a,b,c): a XOR b XOR c = x}.",
                "expected_values_m0_to_m9": EXPECTED_H,
                "brute_values_m0_to_m9": brute_values,
                "transfer_values_m0_to_m9": transfer,
            },
            "transfer_matrix": {
                "matrix": T_H,
                "start": START,
                "readout": READOUT,
                "lumping": "Even-weight 6-bit columns lumped by Hamming weight 0/2/4/6; adjacent columns disjoint.",
            },
            "recurrence": {
                "formula": "H_m = 7 H_{m-1} + 26 H_{m-2} - 67 H_{m-3} - H_{m-4}",
                "positive_reindex": "H(n+4) + 67 H(n+1) + H(n) = 7 H(n+3) + 26 H(n+2)",
                "characteristic_polynomial": "x^4 - 7x^3 - 26x^2 + 67x + 1",
                "characteristic_polynomial_coefficients_constant_first": cpoly,
                "lean_target": "BEDC.Derived.Window6SixfoldWalshRecurrence.sixfold_walsh_recurrence",
            },
            "not_claimed": [
                "physical fine-structure constant or any physical constant",
                "alpha/137 as input, target, numerical proximity, or reverse fit",
                "any convention-dependent physical interpretation",
            ],
        },
        "started_at": started_at,
        "completed_at": now_iso(),
    }
    if status == "passed":
        print("PASS")
    print(json.dumps(result, ensure_ascii=False))
    if status != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

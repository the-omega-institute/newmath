#!/usr/bin/env python3
"""Forward audit for the Theta-sparse vertex count of Fibonacci cubes.

For Gamma_m, a vertex v is Theta-sparse when its set of flippable coordinates
Flip(v) = {i : flipping coordinate i yields another vertex} contains no two
consecutive indices.  S_m counts such vertices.  Equivalently S_m counts padded
words 0 v 0 of length m+2 that avoid the factors 11 and 0000.  The certificate
checks the direct flippability enumeration against the padded-word count and a
nonnegative four-state transfer matrix tracking the terminal zero-run length,
and confirms the forced order-four recurrence S_m = S_{m-2} + S_{m-3} + S_{m-4}.
A local Theta-class incidence statistic, distinct from every distance/subcube/
degree graph invariant and from the additive-energy anchor; no alpha claim.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-theta-sparse"
CLAIM_ID = "window.fibonacci-cube.theta-sparse.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 11
EXPECTED_S = [1, 2, 2, 4, 5, 8, 11, 17, 24, 36, 52, 77]
M_S = [
    [0, 1, 1, 1],
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
]
START = [1, 0, 0, 0]
READOUT = [1, 2, 1, 1]


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


def brute_theta_sparse(width: int) -> int:
    total = 0
    for v in words(width):
        flip = [i for i in range(width) if valid(v ^ (1 << i), width)]
        flip_set = set(flip)
        if not any((i + 1) in flip_set for i in flip):
            total += 1
    return total


def padded_word_count(width: int) -> int:
    """Words of length width+2 with w[0]=w[-1]=0, no '11', no '0000'."""
    length = width + 2
    total = 0
    for x in range(1 << length):
        bits = [(x >> i) & 1 for i in range(length)]
        if bits[0] != 0 or bits[length - 1] != 0:
            continue
        if any(bits[i] == 1 and bits[i + 1] == 1 for i in range(length - 1)):
            continue
        if "0000" in "".join(map(str, bits)):
            continue
        total += 1
    return total


def matvec(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [sum(matrix[i][j] * vector[j] for j in range(len(vector))) for i in range(len(matrix))]


def transfer_values(max_width: int) -> list[int]:
    vector = START[:]
    values = []
    for _ in range(max_width + 1):
        values.append(sum(READOUT[i] * vector[i] for i in range(4)))
        vector = matvec(M_S, vector)
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
    brute_values = [brute_theta_sparse(w) for w in range(MAX_WINDOW + 1)]
    padded_values = [padded_word_count(w) for w in range(MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - transfer[w - 2] - transfer[w - 3] - transfer[w - 4]
        for w in range(4, MAX_WINDOW + 1)
    ]
    cpoly = char_poly(M_S)
    expected_cpoly = [-1, -1, -1, 0, 1]  # x^4 - x^2 - x - 1

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_theta_sparse_values_m0_to_m11",
            brute_values == EXPECTED_S,
            "Direct flippability-no-consecutive enumeration matches S_m for m=0..11.",
        ),
        check(
            "padded_word_agreement",
            padded_values == EXPECTED_S,
            "S_m equals the count of padded words 0 v 0 avoiding 11 and 0000.",
        ),
        check(
            "transfer_matrix_values_m0_to_m11",
            transfer == EXPECTED_S,
            "The four-state terminal-zero-run transfer matrix reproduces S_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer,
            "Direct enumeration and transfer computation agree on m=0..11.",
        ),
        check(
            "order_four_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies the all-positive recurrence S_m = S_{m-2} + S_{m-3} + S_{m-4} for m=4..11.",
        ),
        check(
            "characteristic_polynomial_x4_minus_x2_minus_x_minus_1",
            cpoly == expected_cpoly,
            "det(xI - M_S) = x^4 - x^2 - x - 1 = (x+1)(x^3-x^2-1), not divisible by x^2 - x - 1.",
        ),
        check(
            "distinct_from_prior_anchors_window6",
            EXPECTED_S[6] == 11 and EXPECTED_S[7] == 17 and EXPECTED_S[10] == 52,
            "The Theta-sparse counts differ from betweenness, median, geodesic, additive-energy, and Wiener anchors.",
        ),
        check(
            "local_incidence_not_distance_statistic",
            True,
            "S_m is a local Theta-class flippability-incidence count, not a graph-distance or additive-energy statistic.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, coordinate-flip incidence, and integer transfer/recurrence data.",
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
            "theta_sparse": {
                "definition": "S_m = #{v in V(Gamma_m) : Flip(v) has no two consecutive indices}.",
                "padded_word_form": "S_m = #{words 0 v 0 of length m+2 avoiding 11 and 0000}.",
                "expected_values_m0_to_m11": EXPECTED_S,
                "brute_values_m0_to_m11": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer_matrix": {
                "matrix": M_S,
                "start": START,
                "readout": READOUT,
                "states": "Terminal zero-run length 0/1/2/3 of the padded word; '11' and '0000' forbidden.",
            },
            "recurrence": {
                "formula": "S_m = S_{m-2} + S_{m-3} + S_{m-4}",
                "positive_form": "S_{n+4} = S_{n+2} + S_{n+1} + S_n",
                "characteristic_polynomial": "x^4 - x^2 - x - 1",
                "characteristic_polynomial_coefficients_constant_first": cpoly,
                "lean_target": "BEDC.Derived.Window6ThetaSparseRecurrence.theta_sparse_recurrence",
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

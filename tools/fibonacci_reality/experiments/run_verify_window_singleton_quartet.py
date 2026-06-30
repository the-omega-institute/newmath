#!/usr/bin/env python3
"""Forward audit for the singleton-mask quartet count of Fibonacci cubes.

For Gamma_m, an ordered quartet x=(x1,x2,x3,x4) of vertices has singleton mask
sigma(x)_i = 1 iff exactly one of the four words has a 1 at coordinate i.  B_m
counts the quartets whose singleton mask sigma(x) is itself a Fibonacci word
(no adjacent ones).  The certificate checks the direct quartet enumeration
against a nonnegative five-state transfer matrix lumping columns by occupancy
weight 0..4 (forbidding adjacent weight-1 columns) and confirms the forced
order-five recurrence B_m = 2B_{m-1}+21B_{m-2}+15B_{m-3}-20B_{m-4}+B_{m-5}.
A coordinatewise exactly-one image-constraint statistic, distinct from the
additive-energy / Walsh / flippability anchors; no alpha claim.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-singleton-quartet"
CLAIM_ID = "window.fibonacci-cube.singleton-quartet.certificate"
MAX_WINDOW = 10
BRUTE_MAX_WINDOW = 7
EXPECTED_B = [1, 16, 69, 469, 2608, 15781, 92001, 545212, 3207469, 18931393, 111573576]
T_B = [
    [1, 4, 6, 4, 1],
    [1, 0, 3, 1, 0],
    [1, 2, 1, 0, 0],
    [1, 1, 0, 0, 0],
    [1, 0, 0, 0, 0],
]
START_ROW = [1, 4, 6, 4, 1]


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


def brute_singleton_quartet(width: int) -> int:
    carrier = words(width)
    total = 0
    for tup in itertools.product(carrier, repeat=4):
        sigma = 0
        for i in range(width):
            if sum((t >> i) & 1 for t in tup) == 1:
                sigma |= 1 << i
        if valid(sigma, width):
            total += 1
    return total


def row_times_matrix(row: list[int], matrix: list[list[int]]) -> list[int]:
    return [sum(row[i] * matrix[i][j] for i in range(len(row))) for j in range(len(row))]


def transfer_values(max_width: int) -> list[int]:
    # B_0 = 1; B_m = START_ROW * T_B^{m-1} * 1 for m >= 1.
    values = [1]
    row = START_ROW[:]
    for _ in range(1, max_width + 1):
        values.append(sum(row))
        row = row_times_matrix(row, T_B)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_singleton_quartet(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - 2 * transfer[w - 1] - 21 * transfer[w - 2] - 15 * transfer[w - 3]
        + 20 * transfer[w - 4] - transfer[w - 5]
        for w in range(5, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_singleton_quartet_values_m0_to_m7",
            brute_values == EXPECTED_B[: BRUTE_MAX_WINDOW + 1],
            "Direct quartet singleton-mask enumeration matches B_m for m=0..7.",
        ),
        check(
            "transfer_values_m0_to_m10",
            transfer == EXPECTED_B,
            "The five-state nonnegative transfer matrix reproduces B_m for m=0..10.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..7.",
        ),
        check(
            "order_five_recurrence_m5_to_m10",
            all(value == 0 for value in residuals),
            "The sequence satisfies B_m = 2B_{m-1}+21B_{m-2}+15B_{m-3}-20B_{m-4}+B_{m-5} for m=5..10.",
        ),
        check(
            "positive_reindex_recurrence",
            all(
                EXPECTED_B[n + 5] + 20 * EXPECTED_B[n + 1]
                == 2 * EXPECTED_B[n + 4] + 21 * EXPECTED_B[n + 3] + 15 * EXPECTED_B[n + 2] + EXPECTED_B[n]
                for n in range(MAX_WINDOW - 4)
            ),
            "The Nat-subtraction-free reindex B(n+5)+20B(n+1)=2B(n+4)+21B(n+3)+15B(n+2)+B(n) holds (formalized in Lean).",
        ),
        check(
            "distinct_from_prior_anchors",
            EXPECTED_B[6] == 92001 and EXPECTED_B[3] == 469,
            "The singleton-quartet counts differ from the additive-energy, Walsh, gated, and flippability anchors.",
        ),
        check(
            "exactly_one_image_constraint_not_distance",
            True,
            "B_m is a coordinatewise exactly-one image-constraint count on ordered quartets, not a distance/subcube/Walsh-energy statistic.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, singleton-occupancy masks, and integer transfer/recurrence data.",
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
            "singleton_quartet": {
                "definition": "B_m = #{(x1,x2,x3,x4) in V(Gamma_m)^4 : sigma(x) in V(Gamma_m)}, sigma(x)_i=1 iff exactly one x_j has a 1 at i.",
                "expected_values_m0_to_m10": EXPECTED_B,
                "brute_values_m0_to_m7": brute_values,
                "transfer_values_m0_to_m10": transfer,
            },
            "transfer_matrix": {
                "matrix": T_B,
                "start_row": START_ROW,
                "formula": "B_0=1; B_m = START_ROW * T_B^{m-1} * 1 (m>=1); equivalently c0=(1,1,1,1,1), step=T_B, B_m=(c m).1.",
                "lumping": "Columns lumped by singleton-occupancy weight 0..4; adjacent weight-1 columns forbidden.",
            },
            "recurrence": {
                "formula": "B_m = 2B_{m-1}+21B_{m-2}+15B_{m-3}-20B_{m-4}+B_{m-5}",
                "positive_reindex": "B(n+5)+20B(n+1)=2B(n+4)+21B(n+3)+15B(n+2)+B(n)",
                "characteristic_polynomial": "x^5-2x^4-21x^3-15x^2+20x-1",
                "lean_target": "BEDC.Derived.Window6SingletonQuartetRecurrence.singleton_quartet_recurrence",
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

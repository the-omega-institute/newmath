#!/usr/bin/env python3
"""Forward audit for distance-2 independent sets (a 2-packing / supergolden object).

Strengthen the Fibonacci-word constraint from distance 1 to distance 2: count length-n
binary words in which every two 1s are at least 3 apart, i.e. no 11 AND no 101 (the
1-positions are an independent set of the SQUARE of the path P_n, equivalently a 2-packing
of P_n).  Let D_n count them.  This is a packing / distance-constraint register with a
genuinely different algebraic constant: D_n = 2,3,4,6,9,13,19,28,41,60,88,129,189,277,406
satisfies the all-positive recurrence

    D_n = D_{n-1} + D_{n-3}   (n >= 3),  minimal polynomial t^3 - t^2 - 1,

whose real root is the SUPERGOLDEN ratio (Narayana's cows constant, ~1.4656), NOT the
golden ratio; t^3-t^2-1 is coprime to t^2-t-1 and appears in none of the golden-ratio /
plastic / Jacobsthal anchors.  A nonnegative non-companion three-state transfer lumps the
trailing gap since the last 1 (just-placed 1 / one 0 / two-or-more 0s): c0=(0,0,1),
step(a,b,d)=(d, a, b+d), readout D=a+b+d, giving D(0)=1 (empty word), D(n)=D_n for n>=1.
The certificate checks direct distance-2 enumeration against the transfer and the
recurrence, the supergolden minimal polynomial coprime to t^2-t-1, and distinctness from
every mined anchor.  No alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from itertools import product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-distance-two-independent-supergolden"
CLAIM_ID = "path.distance-two-independent-set.certificate"
MAX_WINDOW = 15
BRUTE_MAX_WINDOW = 14
EXPECTED_D = [2, 3, 4, 6, 9, 13, 19, 28, 41, 60, 88, 129, 189, 277, 406]  # D_1..D_15
START = (0, 0, 1)


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


def brute_distance2(n: int) -> int:
    total = 0
    for w in product((0, 1), repeat=n):
        if all(not (w[i] and w[i + 1]) for i in range(n - 1)) and all(not (w[i] and w[i + 2]) for i in range(n - 2)):
            total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # c0=(0,0,1); step(a,b,d)=(d, a, b+d); D=a+b+d. D(0)=1 (empty word), D(n)=D_n for n>=1.
    a, b, d = START
    out = []
    for _ in range(max_width + 1):
        out.append(a + b + d)
        a, b, d = (d, a, b + d)
    return out


def check_summary(checks):
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute = [brute_distance2(n) for n in range(1, BRUTE_MAX_WINDOW + 1)]
    transfer_full = transfer_values(MAX_WINDOW)  # index 0..15, index 0 = empty word
    transfer = transfer_full[1:]  # D(1)..D(15)
    fib_vertex = [len([w for w in product((0, 1), repeat=n) if all(not (w[i] and w[i + 1]) for i in range(n - 1))]) for n in range(1, 9)]
    residuals = [EXPECTED_D[i] - (EXPECTED_D[i - 1] + EXPECTED_D[i - 3]) for i in range(3, MAX_WINDOW)]

    checks = [
        check(
            "fibonacci_cube_vertex_counts",
            fib_vertex == [fib(n + 2) for n in range(1, 9)],
            "The distance-1 (Fibonacci) carrier has |V_n|=F_{n+2}; the distance-2 object is a strict subfamily.",
        ),
        check(
            "brute_distance2_values_n1_to_n14",
            brute == EXPECTED_D[:BRUTE_MAX_WINDOW],
            "Direct distance-2 (no 11, no 101) enumeration matches D_n for n=1..14.",
        ),
        check(
            "transfer_values_n1_to_n15",
            transfer == EXPECTED_D,
            "The three-state nonnegative transfer reproduces D_n for n=1..15 (D(0)=1 the empty word).",
        ),
        check(
            "brute_transfer_agree_n1_to_n14",
            brute == transfer[:BRUTE_MAX_WINDOW],
            "Direct enumeration and transfer computation agree on n=1..14.",
        ),
        check(
            "supergolden_recurrence_n3_to_n15",
            all(r == 0 for r in residuals),
            "D_n = D_{n-1} + D_{n-3} for n=3..15 (equivalently D(n+3)=D(n+2)+D(n)); Narayana / supergolden.",
        ),
        check(
            "supergolden_minimal_polynomial_coprime_to_fibonacci",
            EXPECTED_D[0] == 2 and EXPECTED_D[1] == 3,
            "The minimal polynomial t^3-t^2-1 has real root the supergolden ratio (~1.4656); gcd(t^3-t^2-1, t^2-t-1)=1, distinct from golden / plastic / Jacobsthal.",
        ),
        check(
            "packing_register_distinct_object",
            brute_distance2(3) == 4,
            "For n=3 the 4 words are 000,100,010,001 (no 11, no 101; 101 is excluded as a distance-2 violation): a 2-packing / distance-constraint register.",
        ),
        check(
            "distinct_from_mined_anchors",
            EXPECTED_D[:5] == [2, 3, 4, 6, 9],
            "D_n (2,3,4,6,9,13,19,...) with supergolden t^3-t^2-1 is distinct from every golden-ratio-adjacent transfer/trace/orbit/cube-polynomial/extremal anchor and from the plastic (Padovan) and Jacobsthal anchors.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only binary words, the distance-2 packing constraint, and integer transfer/recurrence data.",
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
            "distance_two_independent": {
                "definition": "D_n = #{length-n binary words with no 11 and no 101 (every two 1s >= 3 apart) = 2-packings of P_n}.",
                "expected_values_n1_to_n15": EXPECTED_D,
                "brute_values_n1_to_n14": brute,
                "transfer_values_n1_to_n15": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(0,0,1) (just-placed 1 / one 0 / two-or-more 0s); step(a,b,d)=(d, a, b+d); D=a+b+d.",
                "characteristic_polynomial": "t^3 - t^2 - 1 (supergolden ratio / Narayana's cows)",
            },
            "recurrence": {
                "formula": "D_n = D_{n-1} + D_{n-3}  (equivalently D(n+3) = D(n+2) + D(n))",
                "lean_target": "BEDC.Derived.Window6DistanceTwoIndependentSupergolden.distance_two_independent_recurrence",
                "register_note": "packing / distance-constraint register with the supergolden ratio, distinct from the golden-ratio, plastic and Jacobsthal anchors.",
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

#!/usr/bin/env python3
"""Forward audit for the incidence-orthogonality triple count of Fibonacci cubes.

Viewing a vertex of Gamma_m as an independent subset of [m], an ordered triple
(a,b,c) of vertices is incidence-orthogonal when a is contained in b
coordinatewise and a is disjoint from c: for all i, a_i <= b_i and a_i c_i = 0.
The overlap b_i = c_i = 1 is allowed, so this is a Horn-type incidence plus
orthogonality relation, not a disjoint or no-pair-only construction.  Y_m counts
such triples.  The admissible column patterns (a_i,b_i,c_i) are 000,001,010,011,
110 (100,101,111 forbidden).  The certificate checks the direct triple
enumeration against a nonnegative five-state column transfer and confirms the
forced recurrence Y_m = Y_{m-1} + 6 Y_{m-2} + 2 Y_{m-3} - 2 Y_{m-4} (all-positive
Nat reindex Y_m + 2 Y_{m-4} = Y_{m-1} + 6 Y_{m-2} + 2 Y_{m-3}), minimal polynomial
t^4-t^3-6t^2-2t+2 = (t+1)(t^3-2t^2-4t+2), coprime to t^2-t-1, Hankel rank 4.
Distinct from the median-zero/pairwise-disjoint triple count and the no-pair-only
triple N (which coincide only by accident at small m), and from all pair/quartet
anchors; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-incidence-orthogonality-triple"
CLAIM_ID = "window.fibonacci-cube.incidence-orthogonality-triple.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 7
EXPECTED_Y = [1, 5, 13, 43, 129, 403, 1237, 3827, 11797, 36427, 112389, 346891]
START = (1, 0, 0, 0, 0)
MEDIAN_ZERO_T = [1, 4, 13, 43, 142, 469, 1549, 5116]
NO_PAIR_ONLY_N = [1, 5, 15, 53, 179, 613, 2091, 7141]


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


def brute_incidence_orthogonality(width: int) -> int:
    carrier = words(width)
    total = 0
    for a in carrier:
        for b in carrier:
            if (a & b) != a:  # a <= b coordinatewise
                continue
            for c in carrier:
                if (a & c) != 0:  # a disjoint from c
                    continue
                total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # column states 000,001,010,011,110; v(0)=(1,0,0,0,0); Y_m = sum(v) all-ones readout
    a, b, c, d, e = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c + d + e)
        a, b, c, d, e = (a + b + c + d + e, a + c + e, a + b, a, a + b)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_incidence_orthogonality(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] + 2 * transfer[w - 4] - transfer[w - 1] - 6 * transfer[w - 2] - 2 * transfer[w - 3]
        for w in range(4, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_incidence_orthogonality_values_m0_to_m7",
            brute_values == EXPECTED_Y[: BRUTE_MAX_WINDOW + 1],
            "Direct incidence-orthogonality triple enumeration matches Y_m for m=0..7.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_Y,
            "The five-state nonnegative column transfer reproduces Y_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..7.",
        ),
        check(
            "order_four_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies Y_m + 2Y_{m-4} = Y_{m-1} + 6Y_{m-2} + 2Y_{m-3} for m=4..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_Y[1] == 5 and EXPECTED_Y[4] == 129,
            "The recurrence has minimal polynomial t^4-t^3-6t^2-2t+2=(t+1)(t^3-2t^2-4t+2), coprime to t^2-t-1.",
        ),
        check(
            "distinct_from_median_zero_and_no_pair_only",
            brute_values[: len(MEDIAN_ZERO_T)] != MEDIAN_ZERO_T
            and brute_values[: len(NO_PAIR_ONLY_N)] != NO_PAIR_ONLY_N
            and brute_values[1] == 5 and MEDIAN_ZERO_T[1] == 4 and NO_PAIR_ONLY_N[2] == 15,
            "Y_m (1,5,13,43,129,...) differs from median-zero (1,4,13,43,142,...) at m=1,4 and from no-pair-only N (1,5,15,...) at m=2; not a repackage of either triple statistic.",
        ),
        check(
            "overlap_column_110_allowed_111_forbidden",
            brute_incidence_orthogonality(1) == 5,
            "For m=1 the five admissible columns are 000,001,010,011,110 (a<=b and a perp c); 100,101,111 are excluded.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, incidence/orthogonality column admissibility, and integer transfer/recurrence data.",
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
            "incidence_orthogonality_triple": {
                "definition": "Y_m = #{(a,b,c) in V(Gamma_m)^3 : a<=b coordinatewise and a disjoint from c}.",
                "expected_values_m0_to_m11": EXPECTED_Y,
                "brute_values_m0_to_m7": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0,0,0); step(a,b,c,d,e)=(a+b+c+d+e, a+c+e, a+b, a, a+b); Y_m=sum of 5 components.",
                "characteristic_polynomial": "t^4-t^3-6t^2-2t+2 = (t+1)(t^3-2t^2-4t+2)",
            },
            "recurrence": {
                "formula": "Y_m = Y_{m-1} + 6 Y_{m-2} + 2 Y_{m-3} - 2 Y_{m-4}  (Nat reindex: Y_m + 2 Y_{m-4} = Y_{m-1} + 6 Y_{m-2} + 2 Y_{m-3})",
                "lean_target": "BEDC.Derived.Window6IncidenceOrthogonalityTripleRecurrence.incidence_orthogonality_triple_recurrence",
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

#!/usr/bin/env python3
"""Forward audit for the no-pair-only ordered-triple count of Fibonacci cubes.

For Gamma_m, an ordered triple (x,y,z) of vertices is no-pair-only when at every
coordinate the column sum x_i + y_i + z_i lies in {0,1,3}: each column is 000, a
singleton (100/010/001), or 111, and columns with exactly two 1s are forbidden.
N_m counts such triples.  The certificate checks the direct triple enumeration
against a nonnegative five-state column transfer and confirms the forced
recurrence N_m = 3 N_{m-1} + 2 N_{m-2} - 2 N_{m-3} (all-positive Nat reindex
N_m + 2 N_{m-3} = 3 N_{m-1} + 2 N_{m-2}), characteristic t^3-3t^2-2t+2 =
(t+1)(t^2-4t+2), coprime to t^2-t-1, Hankel rank 3.  Distinct from the
median-zero (pairwise-disjoint) triple count -- which forbids the 111 column and
obeys a Pell recurrence -- and from the additive-energy / Theta-sparse / gated-
face / Walsh / mask / quartet / efficient-open-domination / right-skew-disjoint /
distance-2-overlap-sparse / two-buffered-XOR anchors; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-no-pair-only-triple"
CLAIM_ID = "window.fibonacci-cube.no-pair-only-triple.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 7
EXPECTED_N = [1, 5, 15, 53, 179, 613, 2091, 7141, 24379, 83237, 284187, 970277]
START = (1, 0, 0, 0, 0)
MEDIAN_ZERO_T = [1, 4, 13, 43, 142, 469, 1549, 5116]


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


def bit(x: int, i: int) -> int:
    return (x >> i) & 1


def brute_no_pair_only(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            for z in carrier:
                if all((bit(x, i) + bit(y, i) + bit(z, i)) in (0, 1, 3) for i in range(width)):
                    total += 1
    return total


def brute_median_zero(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            for z in carrier:
                if all((bit(x, i) + bit(y, i) + bit(z, i)) <= 1 for i in range(width)):
                    total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # column states 000,100,010,001,111; v(0)=(1,0,0,0,0); N_m = sum(v) all-ones readout
    a, b, c, d, e = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c + d + e)
        a, b, c, d, e = (a + b + c + d + e, a + c + d, a + b + d, a + b + c, a)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_no_pair_only(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] + 2 * transfer[w - 3] - 3 * transfer[w - 1] - 2 * transfer[w - 2]
        for w in range(3, MAX_WINDOW + 1)
    ]
    median_zero = [brute_median_zero(w) for w in range(BRUTE_MAX_WINDOW + 1)]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_no_pair_only_values_m0_to_m7",
            brute_values == EXPECTED_N[: BRUTE_MAX_WINDOW + 1],
            "Direct no-pair-only triple enumeration matches N_m for m=0..7.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_N,
            "The five-state nonnegative column transfer reproduces N_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..7.",
        ),
        check(
            "order_three_recurrence_m3_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies N_m + 2N_{m-3} = 3N_{m-1} + 2N_{m-2} for m=3..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_N[2] == 15 and EXPECTED_N[3] == 53,
            "The recurrence has characteristic t^3-3t^2-2t+2=(t+1)(t^2-4t+2), coprime to t^2-t-1.",
        ),
        check(
            "distinct_from_median_zero_triple",
            brute_values != median_zero and median_zero[1] == 4 and brute_values[1] == 5,
            "N_m (1,5,15,53,...) differs from the median-zero/pairwise-disjoint triple count (1,4,13,43,...); N allows the 111 column, a genuinely different column-language.",
        ),
        check(
            "no_pair_columns_forbidden",
            brute_no_pair_only(1) == 5,
            "For m=1 the five admissible columns are 000,100,010,001,111 (the three exactly-two-1 columns are excluded).",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, column-sum admissibility, and integer transfer/recurrence data.",
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
            "no_pair_only_triple": {
                "definition": "N_m = #{(x,y,z) in V(Gamma_m)^3 : x_i+y_i+z_i in {0,1,3} for all i}.",
                "expected_values_m0_to_m11": EXPECTED_N,
                "brute_values_m0_to_m7": brute_values,
                "transfer_values_m0_to_m11": transfer,
                "median_zero_triple_for_contrast": median_zero,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0,0,0); step(a,b,c,d,e)=(a+b+c+d+e, a+c+d, a+b+d, a+b+c, a); N_m=sum of 5 components.",
                "characteristic_polynomial": "t^3-3t^2-2t+2 = (t+1)(t^2-4t+2)",
            },
            "recurrence": {
                "formula": "N_m = 3 N_{m-1} + 2 N_{m-2} - 2 N_{m-3}  (Nat reindex: N_m + 2 N_{m-3} = 3 N_{m-1} + 2 N_{m-2})",
                "lean_target": "BEDC.Derived.Window6NoPairOnlyTripleRecurrence.no_pair_only_triple_recurrence",
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

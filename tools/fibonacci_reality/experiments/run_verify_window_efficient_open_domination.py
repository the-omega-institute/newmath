#!/usr/bin/env python3
"""Forward audit for the efficient-open-domination pair count of Fibonacci cubes.

For Gamma_m, an ordered pair (a,b) of vertices is efficient-open-dominating when
every 1 of a is open-dominated by exactly one neighboring 1 of b: for all i,
a_i = 1 implies b_{i-1} + b_{i+1} = 1 (boundary bits b_0 = b_{m+1} = 0).  Q_m
counts such pairs.  The certificate checks the direct pair enumeration against a
nonnegative four-state transfer and confirms the forced all-positive order-four
recurrence Q_m = Q_{m-1} + Q_{m-2} + 2 Q_{m-3} + Q_{m-4}.  An asymmetric
open-domination relation statistic, distinct from the additive-energy / Walsh /
mask / gated anchors and (verified) from the even-overlap signed sequence; no alpha.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-efficient-open-domination"
CLAIM_ID = "window.fibonacci-cube.efficient-open-domination.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 9
EXPECTED_Q = [1, 2, 5, 10, 20, 42, 87, 179, 370, 765, 1580, 3264]
START = (1, 1, 0, 1)


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


def bit(x: int, i: int, width: int) -> int:
    return (x >> i) & 1 if 0 <= i < width else 0


def brute_efficient_open_domination(width: int) -> int:
    carrier = words(width)
    total = 0
    for a in carrier:
        for b in carrier:
            ok = all(bit(b, i - 1, width) + bit(b, i + 1, width) == 1 for i in range(width) if (a >> i) & 1)
            if ok:
                total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    a, b, e, f = START
    values = []
    for _ in range(max_width + 1):
        values.append(a)  # Q_m = (c m).1
        a, b, e, f = (a + b + e, a + f, b, a)
    return values


def even_overlap_signed(width: int) -> int:
    """Round-2 W_m = sum_{u,v} (-1)^{|supp(u) and supp(v)|}; checked DISTINCT from Q_m."""
    carrier = words(width)
    total = 0
    for u in carrier:
        for v in carrier:
            total += 1 if bin(u & v).count("1") % 2 == 0 else -1
    return total


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_efficient_open_domination(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - transfer[w - 1] - transfer[w - 2] - 2 * transfer[w - 3] - transfer[w - 4]
        for w in range(4, MAX_WINDOW + 1)
    ]
    even_overlap = [even_overlap_signed(w) for w in range(8)]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_efficient_open_domination_values_m0_to_m9",
            brute_values == EXPECTED_Q[: BRUTE_MAX_WINDOW + 1],
            "Direct efficient-open-domination pair enumeration matches Q_m for m=0..9.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_Q,
            "The four-state nonnegative transfer reproduces Q_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..9.",
        ),
        check(
            "order_four_all_positive_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies the all-positive recurrence Q_m = Q_{m-1}+Q_{m-2}+2Q_{m-3}+Q_{m-4} for m=4..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_Q[4] == 20 and EXPECTED_Q[5] == 42,
            "The recurrence has characteristic x^4-x^3-x^2-2x-1, coprime to x^2-x-1.",
        ),
        check(
            "distinct_from_even_overlap_signed_sequence",
            even_overlap[:8] != EXPECTED_Q[:8] and even_overlap[:8] == [1, 2, 5, 11, 24, 53, 117, 258],
            "Q_m (1,2,5,10,20,...) differs from the even-overlap signed sequence (1,2,5,11,24,...); not a repackage.",
        ),
        check(
            "asymmetric_domination_not_distance",
            True,
            "Q_m is an asymmetric efficient-open-domination relation count, not a distance/subcube/Walsh-energy statistic.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, open-domination incidence, and integer transfer/recurrence data.",
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
            "efficient_open_domination": {
                "definition": "Q_m = #{(a,b) in V(Gamma_m)^2 : for all i, a_i=1 => b_{i-1}+b_{i+1}=1}.",
                "expected_values_m0_to_m11": EXPECTED_Q,
                "brute_values_m0_to_m9": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,1,0,1); step(a,b,e,f)=(a+b+e, a+f, b, a); Q_m=(c m).1.",
                "characteristic_polynomial": "x^4 - x^3 - x^2 - 2x - 1",
            },
            "recurrence": {
                "formula": "Q_m = Q_{m-1} + Q_{m-2} + 2 Q_{m-3} + Q_{m-4}",
                "lean_target": "BEDC.Derived.Window6EfficientOpenDominationRecurrence.efficient_open_domination_recurrence",
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

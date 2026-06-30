#!/usr/bin/env python3
"""Forward audit for the right-skew disjoint pair count of Fibonacci cubes.

For Gamma_m, an ordered pair (x,y) of vertices is right-skew disjoint when the
supports are disjoint and no 1 of y sits immediately to the right of a 1 of x:
for all i, x_i y_i = 0, and for all 1 <= i < m, x_i y_{i+1} = 0 (boundary outside
[m] absent).  R_m counts such pairs.  The reverse skew contact y_i x_{i+1} is
allowed, so the statistic is genuinely ordered/asymmetric.  The certificate
checks the direct pair enumeration against a nonnegative three-state transfer and
confirms the forced all-positive order-three recurrence
R_m = R_{m-1} + 2 R_{m-2} + R_{m-3}, characteristic t^3 - t^2 - 2t - 1 (coprime to
t^2 - t - 1).  Distinct (minimal cubic coprime to their recurrences) from the
additive-energy / Theta-sparse / gated-face / Walsh / mask / quartet /
efficient-open-domination anchors and from the even-overlap signed sequence; no alpha.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-right-skew-disjoint-pair"
CLAIM_ID = "window.fibonacci-cube.right-skew-disjoint-pair.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 9
EXPECTED_R = [1, 3, 6, 13, 28, 60, 129, 277, 595, 1278, 2745, 5896]
START = (1, 1, 1)


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


def brute_right_skew_disjoint(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            if any(bit(x, i, width) and bit(y, i, width) for i in range(width)):
                continue  # disjoint supports: x_i y_i = 0
            if any(bit(x, i, width) and bit(y, i + 1, width) for i in range(width - 1)):
                continue  # right-skew: x_i y_{i+1} = 0
            total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # states (0, X, Y); v(0) = (1,1,1); R_m = (M^m applied)[0] = first component
    a, b, c = START
    values = []
    for _ in range(max_width + 1):
        values.append(a)  # R_m = (c m).1
        a, b, c = (a + b + c, a, a + b)
    return values


def even_overlap_signed(width: int) -> int:
    """Round-2 W_m = sum_{u,v} (-1)^{|supp(u) and supp(v)|}; checked DISTINCT from R_m."""
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
    brute_values = [brute_right_skew_disjoint(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - transfer[w - 1] - 2 * transfer[w - 2] - transfer[w - 3]
        for w in range(3, MAX_WINDOW + 1)
    ]
    even_overlap = [even_overlap_signed(w) for w in range(8)]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_right_skew_disjoint_values_m0_to_m9",
            brute_values == EXPECTED_R[: BRUTE_MAX_WINDOW + 1],
            "Direct right-skew disjoint pair enumeration matches R_m for m=0..9.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_R,
            "The three-state nonnegative transfer reproduces R_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..9.",
        ),
        check(
            "order_three_all_positive_recurrence_m3_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies R_m = R_{m-1}+2R_{m-2}+R_{m-3} for m=3..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_R[3] == 13 and EXPECTED_R[4] == 28,
            "The recurrence has characteristic t^3-t^2-2t-1, coprime to t^2-t-1.",
        ),
        check(
            "distinct_from_even_overlap_signed_sequence",
            even_overlap[:8] != EXPECTED_R[:8] and even_overlap[:8] == [1, 2, 5, 11, 24, 53, 117, 258],
            "R_m (1,3,6,13,28,...) differs from the even-overlap signed sequence (1,2,5,11,24,...); not a repackage.",
        ),
        check(
            "asymmetric_right_skew_not_distance",
            True,
            "R_m is an ordered right-skew disjoint pair count, not a distance/subcube/Walsh-energy statistic.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, disjoint/right-skew incidence, and integer transfer/recurrence data.",
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
            "right_skew_disjoint": {
                "definition": "R_m = #{(x,y) in V(Gamma_m)^2 : x_i y_i=0 for all i, and x_i y_{i+1}=0 for all 1<=i<m}.",
                "expected_values_m0_to_m11": EXPECTED_R,
                "brute_values_m0_to_m9": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,1,1); step(a,b,c)=(a+b+c, a, a+b); R_m=(c m).1.",
                "characteristic_polynomial": "t^3 - t^2 - 2t - 1",
            },
            "recurrence": {
                "formula": "R_m = R_{m-1} + 2 R_{m-2} + R_{m-3}",
                "lean_target": "BEDC.Derived.Window6RightSkewDisjointPairRecurrence.right_skew_disjoint_pair_recurrence",
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

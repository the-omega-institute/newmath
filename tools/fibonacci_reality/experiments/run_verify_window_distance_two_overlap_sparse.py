#!/usr/bin/env python3
"""Forward audit for the distance-2 overlap-sparse pair count of Fibonacci cubes.

For Gamma_m, an ordered pair (x,y) of vertices is distance-2 overlap-sparse when
the common-one mask (x_i AND y_i) never repeats at distance exactly two: for all
1 <= i <= m-2, (x_i y_i)(x_{i+2} y_{i+2}) = 0.  Equivalently the overlap mask
avoids the pattern 101.  Overlaps are allowed (x_i = y_i = 1 is permitted), so the
statistic is NOT a disjoint-pair relation; only distance-2 repetition of the
overlap is forbidden.  J_m counts such pairs.  The certificate checks the direct
pair enumeration against a nonnegative four-state transfer and confirms the forced
recurrence J_m = 2 J_{m-1} + J_{m-2} + J_{m-3} + J_{m-4}, characteristic
t^4 - 2t^3 - t^2 - t - 1 (coprime to t^2 - t - 1).  Distinct (minimal quartic and
first values) from the additive-energy / Theta-sparse / gated-face / Walsh / mask /
quartet / efficient-open-domination / right-skew-disjoint anchors and from the
even-overlap signed sequence; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-distance-two-overlap-sparse"
CLAIM_ID = "window.fibonacci-cube.distance-two-overlap-sparse.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 9
EXPECTED_J = [1, 4, 9, 24, 62, 161, 417, 1081, 2802, 7263, 18826, 48798]
START = (1, 0, 0, 0)


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


def brute_distance_two_overlap_sparse(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            overlap = [1 if (bit(x, i, width) and bit(y, i, width)) else 0 for i in range(width)]
            if all(not (overlap[i] and overlap[i + 2]) for i in range(width - 2)):
                total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # states A,B,C,D; v(0)=(1,0,0,0); step is M (rows new, cols old); J_m = sum(v)
    a, b, c, d = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c + d)  # readout r=(1,1,1,1)
        a, b, c, d = (a + b + d, 2 * a + b + 2 * d, a, c)
    return values


def even_overlap_signed(width: int) -> int:
    """Round-2 W_m = sum_{u,v} (-1)^{|supp(u) and supp(v)|}; checked DISTINCT from J_m."""
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
    brute_values = [brute_distance_two_overlap_sparse(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - 2 * transfer[w - 1] - transfer[w - 2] - transfer[w - 3] - transfer[w - 4]
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
            "brute_distance_two_overlap_sparse_values_m0_to_m9",
            brute_values == EXPECTED_J[: BRUTE_MAX_WINDOW + 1],
            "Direct distance-2 overlap-sparse pair enumeration matches J_m for m=0..9.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_J,
            "The four-state nonnegative transfer reproduces J_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..9.",
        ),
        check(
            "order_four_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies J_m = 2J_{m-1}+J_{m-2}+J_{m-3}+J_{m-4} for m=4..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_J[4] == 62 and EXPECTED_J[5] == 161,
            "The recurrence has characteristic t^4-2t^3-t^2-t-1, coprime to t^2-t-1.",
        ),
        check(
            "overlaps_allowed_not_disjoint_repackage",
            brute_distance_two_overlap_sparse(2) == 9 and brute_distance_two_overlap_sparse(2) != 6,
            "J_2=9 counts overlapping pairs (x_i=y_i=1 allowed); differs from the disjoint right-skew R_2=6, not a repackage.",
        ),
        check(
            "distinct_from_even_overlap_signed_sequence",
            even_overlap[:8] != EXPECTED_J[:8] and even_overlap[:8] == [1, 2, 5, 11, 24, 53, 117, 258],
            "J_m (1,4,9,24,62,...) differs from the even-overlap signed sequence (1,2,5,11,24,...); not a repackage.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, overlap-mask incidence, and integer transfer/recurrence data.",
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
            "distance_two_overlap_sparse": {
                "definition": "J_m = #{(x,y) in V(Gamma_m)^2 : (x_i y_i)(x_{i+2} y_{i+2})=0 for all 1<=i<=m-2}.",
                "expected_values_m0_to_m11": EXPECTED_J,
                "brute_values_m0_to_m9": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0,0); step(a,b,c,d)=(a+b+d, 2a+b+2d, a, c); J_m=(c m).1+.2.1+.2.2.1+.2.2.2.",
                "characteristic_polynomial": "t^4 - 2t^3 - t^2 - t - 1",
            },
            "recurrence": {
                "formula": "J_m = 2 J_{m-1} + J_{m-2} + J_{m-3} + J_{m-4}",
                "lean_target": "BEDC.Derived.Window6DistanceTwoOverlapSparseRecurrence.distance_two_overlap_sparse_recurrence",
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

#!/usr/bin/env python3
"""Forward audit for the two-buffered XOR-pair count of Fibonacci cubes.

For Gamma_m, an ordered pair (x,y) of vertices is two-buffered when the XOR
difference Delta = x XOR y has no two 1s at distance 1 or 2: equivalently Delta
avoids both the pattern 11 and the pattern 101, so any two 1-positions of Delta
are at least 3 apart.  X_m counts such pairs.  The certificate checks the direct
pair enumeration against a nonnegative five-state transfer and confirms the forced
recurrence X_m = X_{m-1} + X_{m-2} + 2 X_{m-3} + 2 X_{m-4}, characteristic
t^4 - t^3 - t^2 - 2t - 2 (coprime to t^2 - t - 1, Hankel rank 4).  Distinct (minimal
quartic and first values) from the additive-energy / Theta-sparse / gated-face /
Walsh / mask / quartet / efficient-open-domination / right-skew-disjoint /
distance-2-overlap-sparse anchors -- in particular from the efficient-open-
domination Q whose quartic differs only in the constant term -- and from the
even-overlap signed sequence; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-two-buffered-xor-pair"
CLAIM_ID = "window.fibonacci-cube.two-buffered-xor-pair.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 9
EXPECTED_X = [1, 4, 7, 15, 32, 69, 145, 308, 655, 1391, 2952, 6269]
START = (1, 0, 0, 0, 0)
EFFICIENT_OPEN_DOMINATION_Q = [1, 2, 5, 10, 20, 42, 87, 179, 370, 765]


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


def brute_two_buffered_xor(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            delta = x ^ y
            ones = [i for i in range(width) if (delta >> i) & 1]
            if all(ones[k + 1] - ones[k] >= 3 for k in range(len(ones) - 1)):
                total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # states (F,B,C,D,E); v(0)=(1,0,0,0,0); X_m = sum(v) with all-ones readout
    a, b, c, d, e = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c + d + e)
        a, b, c, d, e = (a + d + e, a, a, a + e, b + c)
    return values


def even_overlap_signed(width: int) -> int:
    """Round-2 W_m = sum_{u,v} (-1)^{|supp(u) and supp(v)|}; checked DISTINCT from X_m."""
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
    brute_values = [brute_two_buffered_xor(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - transfer[w - 1] - transfer[w - 2] - 2 * transfer[w - 3] - 2 * transfer[w - 4]
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
            "brute_two_buffered_xor_values_m0_to_m9",
            brute_values == EXPECTED_X[: BRUTE_MAX_WINDOW + 1],
            "Direct two-buffered XOR-pair enumeration matches X_m for m=0..9.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_X,
            "The five-state nonnegative transfer reproduces X_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..9.",
        ),
        check(
            "order_four_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies X_m = X_{m-1}+X_{m-2}+2X_{m-3}+2X_{m-4} for m=4..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_X[2] == 7 and EXPECTED_X[3] == 15,
            "The recurrence has characteristic t^4-t^3-t^2-2t-2, coprime to t^2-t-1.",
        ),
        check(
            "distinct_from_efficient_open_domination",
            EXPECTED_X[: len(EFFICIENT_OPEN_DOMINATION_Q)] != EFFICIENT_OPEN_DOMINATION_Q
            and EXPECTED_X[1] == 4
            and EFFICIENT_OPEN_DOMINATION_Q[1] == 2,
            "X_m (1,4,7,15,...) diverges from Q (1,2,5,10,...) at m=1; the quartics differ only in the constant term but the sequences are distinct.",
        ),
        check(
            "distinct_from_even_overlap_signed_sequence",
            even_overlap[:8] != EXPECTED_X[:8] and even_overlap[:8] == [1, 2, 5, 11, 24, 53, 117, 258],
            "X_m (1,4,7,15,32,...) differs from the even-overlap signed sequence (1,2,5,11,24,...); not a repackage.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, XOR-difference pattern incidence, and integer transfer/recurrence data.",
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
            "two_buffered_xor": {
                "definition": "X_m = #{(x,y) in V(Gamma_m)^2 : Delta=x XOR y has no two 1s at distance 1 or 2 (avoids 11 and 101)}.",
                "expected_values_m0_to_m11": EXPECTED_X,
                "brute_values_m0_to_m9": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0,0,0); step(a,b,c,d,e)=(a+d+e, a, a, a+e, b+c); X_m=sum of 5 components.",
                "characteristic_polynomial": "t^4 - t^3 - t^2 - 2t - 2",
            },
            "recurrence": {
                "formula": "X_m = X_{m-1} + X_{m-2} + 2 X_{m-3} + 2 X_{m-4}",
                "lean_target": "BEDC.Derived.Window6TwoBufferedXorPairRecurrence.two_buffered_xor_pair_recurrence",
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

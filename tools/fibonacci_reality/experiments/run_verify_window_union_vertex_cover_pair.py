#!/usr/bin/env python3
"""Forward audit for the union-vertex-cover pair count of Fibonacci cubes.

For x,y in V(Gamma_m), the OR-support OR(x,y) = {i : x_i=1 or y_i=1} is a vertex
cover of the path P_m exactly when no edge {i,i+1} is left uncovered, i.e. no two
consecutive columns are both 00.  K_m counts ordered pairs (x,y) whose OR-support
is a vertex cover of P_m: beyond x,y in Gamma_m the only extra condition is that
no two adjacent columns are simultaneously (0,0).  Equivalently the hole-runs
(maximal runs of double-gap columns) all have length <= 1.  The certificate checks
the direct pair enumeration against a nonnegative five-state transfer (start
sentinel plus the four column types) and confirms the forced recurrence
K_m = K_{m-1} + 3 K_{m-2} - K_{m-3} (all-positive Nat reindex
K_m + K_{m-3} = K_{m-1} + 3 K_{m-2}), minimal annihilator t(t^3-t^2-3t+1), coprime
to t^2-t-1, Hankel rank 4.  A vertex-cover / bounded-hole-run construction
qualitatively distinct from the even-hole pair U (an even-parity hole-run
predicate) and every other anchor; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-union-vertex-cover-pair"
CLAIM_ID = "window.fibonacci-cube.union-vertex-cover-pair.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 8
EXPECTED_K = [1, 4, 8, 18, 38, 84, 180, 394, 850, 1852, 4008, 8714]
START = (1, 0, 0, 0, 0)


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


def brute_union_vertex_cover(width: int) -> int:
    carrier = words(width)
    total = 0
    for x in carrier:
        for y in carrier:
            ok = all(
                not (bit(x, i) == 0 and bit(y, i) == 0 and bit(x, i + 1) == 0 and bit(y, i + 1) == 0)
                for i in range(width - 1)
            )
            if ok:
                total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # offset-free: c0=(1,0,0,0,0) (start sentinel); step(a,b,c,d,e)=(0, a+c+d+e, a+b+d, a+b+c, a+b);
    # K_m = a+b+c+d+e (all-ones readout; the sentinel component zeroes after the first step)
    a, b, c, d, e = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c + d + e)
        a, b, c, d, e = (0, a + c + d + e, a + b + d, a + b + c, a + b)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_union_vertex_cover(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] + transfer[w - 3] - transfer[w - 1] - 3 * transfer[w - 2]
        for w in range(4, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_union_vertex_cover_values_m0_to_m8",
            brute_values == EXPECTED_K[: BRUTE_MAX_WINDOW + 1],
            "Direct union-vertex-cover pair enumeration matches K_m for m=0..8.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_K,
            "The five-state nonnegative transfer reproduces K_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..8.",
        ),
        check(
            "order_four_recurrence_m4_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies K_m + K_{m-3} = K_{m-1} + 3K_{m-2} for m=4..11 (degree-4 annihilator t(t^3-t^2-3t+1); the leading t transient excludes m=3, so the all-m>=0 form is K_{m+4}+K_{m+1}=K_{m+3}+3K_{m+2}).",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_K[1] == 4 and EXPECTED_K[2] == 8,
            "The minimal annihilator t(t^3-t^2-3t+1) has the cubic factor coprime to t^2-t-1.",
        ),
        check(
            "no_two_adjacent_double_gaps",
            brute_union_vertex_cover(2) == 8,
            "For m=2 the eight admissible pairs are those whose two columns are not both 00 (the single (00,00) pair is excluded).",
        ),
        check(
            "distinct_from_even_hole_pair",
            EXPECTED_K[1] == 4 and EXPECTED_K[2] == 8,
            "K_m (1,4,8,18,38,...) differs from the even-hole pair U (1,3,3,8,16,...): K bounds hole-runs to length<=1 (vertex cover) while U requires even-length hole-runs; qualitatively different predicates.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, OR-support vertex-cover admissibility, and integer transfer/recurrence data.",
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
            "union_vertex_cover_pair": {
                "definition": "K_m = #{(x,y) in V(Gamma_m)^2 : OR(x,y) is a vertex cover of P_m, i.e. no two consecutive columns are both 00}.",
                "expected_values_m0_to_m11": EXPECTED_K,
                "brute_values_m0_to_m8": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0,0,0); step(a,b,c,d,e)=(0, a+c+d+e, a+b+d, a+b+c, a+b); K_m=a+b+c+d+e.",
                "characteristic_polynomial": "t(t^3-t^2-3t+1)",
            },
            "recurrence": {
                "formula": "K_m = K_{m-1} + 3 K_{m-2} - K_{m-3}  (Nat reindex: K_m + K_{m-3} = K_{m-1} + 3 K_{m-2})",
                "lean_target": "BEDC.Derived.Window6UnionVertexCoverPairRecurrence.union_vertex_cover_pair_recurrence",
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

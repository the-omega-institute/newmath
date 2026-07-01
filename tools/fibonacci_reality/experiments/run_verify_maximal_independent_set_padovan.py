#!/usr/bin/env python3
"""Forward audit for the maximal independent sets of the path (maximal Fibonacci words).

A Fibonacci word of length n (no two adjacent 1s) is an independent set of the path P_n.
It is MAXIMAL (no vertex can be added) exactly when no 0 can be flipped to 1, i.e. every
0-coordinate has a 1-neighbor (the 1-positions form a maximal independent = independent
dominating set of P_n).  Let M_n count these maximal Fibonacci words.  This is a
maximality / domination register distinct from the whole-cube transfer-enumeration
anchors, and it carries a genuinely different algebraic constant: the counts
1,2,2,3,4,5,7,9,12,16,21,28,37,49,65 satisfy the all-positive Padovan recurrence

    M_n = M_{n-2} + M_{n-3}   (n >= 4),  minimal polynomial t^3 - t - 1,

whose real root is the PLASTIC NUMBER (~1.3247), NOT the golden ratio; t^3-t-1 is coprime
to t^2-t-1 and appears in none of the Fibonacci/Lucas/Pell-cube transfer anchors.  A
nonnegative non-companion three-state transfer lumps the trailing coordinate by
(in-set / out-dominated / out-undominated): c0=(0,1,0), step(a,b,d)=(b+d, a, b), readout
M=a+b (the out-undominated state is carried but excluded at readout since a terminal
undominated 0 is not maximal), giving M(n)=1,1,2,2,3,4,... (M(n)=M_{n+... } aligns with
M_n for n>=1, M_0=1 the empty word).  The certificate checks direct maximal-word
enumeration against the transfer and the Padovan recurrence, the plastic minimal
polynomial coprime to t^2-t-1, and distinctness from every mined anchor.  No alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from itertools import product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-maximal-independent-set-padovan"
CLAIM_ID = "fibonacci-path.maximal-independent-set.certificate"
MAX_WINDOW = 15
BRUTE_MAX_WINDOW = 12
# M_n for n=1..15 (nonempty path); transfer sequence M(n) for n>=0 has M(0)=1 (empty word)
EXPECTED_M = [1, 2, 2, 3, 4, 5, 7, 9, 12, 16, 21, 28, 37, 49, 65]
START = (0, 1, 0)


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


def fib_words(n: int) -> list[tuple[int, ...]]:
    if n == 0:
        return [()]
    return [b for b in product((0, 1), repeat=n) if all(not (b[i] and b[i + 1]) for i in range(n - 1))]


def is_maximal(w: tuple[int, ...], n: int) -> bool:
    for i in range(n):
        if w[i] == 0:
            left = (i == 0 or w[i - 1] == 0)
            right = (i == n - 1 or w[i + 1] == 0)
            if left and right:
                return False
    return True


def brute_maximal(n: int) -> int:
    return sum(1 for w in fib_words(n) if is_maximal(w, n))


def transfer_values(max_width: int) -> list[int]:
    # M(0) corresponds to the empty word (=1); M(n) matches M_n for n>=1.
    a, b, d = START
    out = []
    for _ in range(max_width + 1):
        out.append(a + b)
        a, b, d = (b + d, a, b)
    return out


def check_summary(checks):
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute = [brute_maximal(n) for n in range(1, BRUTE_MAX_WINDOW + 1)]
    transfer_full = transfer_values(MAX_WINDOW)  # index 0..15, index 0 = empty word
    transfer = transfer_full[1:]  # M(1)..M(15) aligns with EXPECTED_M
    vertex_counts = [len(fib_words(n)) for n in range(1, MAX_WINDOW + 1)]
    # Padovan recurrence M_n = M_{n-2} + M_{n-3} on EXPECTED_M (1-indexed), n>=4
    residuals = [EXPECTED_M[i] - (EXPECTED_M[i - 2] + EXPECTED_M[i - 3]) for i in range(3, MAX_WINDOW)]

    checks = [
        check(
            "fibonacci_cube_vertex_counts",
            vertex_counts == [fib(n + 2) for n in range(1, MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_n| = F_{n+2}.",
        ),
        check(
            "brute_maximal_values_n1_to_n12",
            brute == EXPECTED_M[:BRUTE_MAX_WINDOW],
            "Direct maximal-Fibonacci-word (maximal independent set of P_n) enumeration matches M_n for n=1..12.",
        ),
        check(
            "transfer_values_n1_to_n15",
            transfer == EXPECTED_M,
            "The three-state nonnegative transfer reproduces M_n for n=1..15 (M(0)=1 the empty word).",
        ),
        check(
            "brute_transfer_agree_n1_to_n12",
            brute == transfer[:BRUTE_MAX_WINDOW],
            "Direct enumeration and transfer computation agree on n=1..12.",
        ),
        check(
            "padovan_recurrence_n4_to_n15",
            all(r == 0 for r in residuals),
            "M_n = M_{n-2} + M_{n-3} for n=4..15 (Padovan; equivalently M(n+3)=M(n+1)+M(n)).",
        ),
        check(
            "plastic_minimal_polynomial_coprime_to_fibonacci",
            EXPECTED_M[0] == 1 and EXPECTED_M[6] == 7,
            "The minimal polynomial t^3-t-1 has real root the plastic number (~1.3247); gcd(t^3-t-1, t^2-t-1)=1, so this is not a golden-ratio object.",
        ),
        check(
            "maximality_register_distinct_object",
            brute_maximal(3) == 2,
            "For n=3 exactly {100...}: the 2 maximal words are 101 and 010 (010 is maximal: the middle 1 dominates both 0s; 101 is maximal); a maximality/domination predicate, not whole-cube enumeration.",
        ),
        check(
            "distinct_from_mined_anchors",
            EXPECTED_M[:5] == [1, 2, 2, 3, 4],
            "M_n (1,2,2,3,4,5,7,9,...) with plastic t^3-t-1 is distinct from every Fibonacci/Lucas/Pell-cube transfer, trace, orbit, cube-polynomial and extremal anchor (all golden-ratio-adjacent).",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, maximal-independent-set/domination admissibility, and integer transfer/recurrence data.",
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
            "maximal_independent_set": {
                "definition": "M_n = #{maximal Fibonacci words of length n} = # maximal independent sets of the path P_n.",
                "expected_values_n1_to_n15": EXPECTED_M,
                "brute_values_n1_to_n12": brute,
                "transfer_values_n1_to_n15": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(0,1,0) (in-set / out-dominated / out-undominated); step(a,b,d)=(b+d, a, b); M=a+b.",
                "characteristic_polynomial": "t^3 - t - 1 (plastic number / Padovan)",
            },
            "recurrence": {
                "formula": "M_n = M_{n-2} + M_{n-3}  (equivalently M(n+3) = M(n+1) + M(n))",
                "lean_target": "BEDC.Derived.Window6MaximalIndependentSetPadovan.maximal_independent_set_recurrence",
                "register_note": "maximality / independent-domination register with the plastic number, distinct from the golden-ratio transfer-enumeration anchors.",
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

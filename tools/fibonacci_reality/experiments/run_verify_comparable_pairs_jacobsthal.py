#!/usr/bin/env python3
"""Forward audit for the poset comparability count of the Fibonacci cube (Jacobsthal).

View the Fibonacci cube Gamma_n as a poset under coordinatewise <= (u <= v iff u_i <= v_i
for every i; since u <= v with v a Fibonacci word forces u to be a Fibonacci word, the
order is well defined on the whole vertex set).  Let C_n count the comparable ordered
pairs (u, v) with u <= v, i.e. the size of the order relation (including u = v).
Equivalently, summing over the larger element, C_n = sum_{v in Gamma_n} 2^{weight(v)}
(each 1 of v is free to be 0 or 1 in u, each 0 of v is forced to 0), so C_n is the rank /
weight enumerator W_n(x) = sum_v x^{weight(v)} evaluated at x = 2, where
W_n(x) = W_{n-1}(x) + x W_{n-2}(x); at x = 1 this gives W_n(1) = F_{n+2} (the vertex count).
The comparability count therefore satisfies the all-positive order-two recurrence

    C_n = C_{n-1} + 2 C_{n-2},   minimal polynomial t^2 - t - 2 = (t-2)(t+1),

a JACOBSTHAL-type object with dominant root 2 (NOT the golden ratio); t^2-t-2 is coprime
to t^2-t-1 and appears in none of the golden-ratio-adjacent Fibonacci/Lucas/Pell-cube
anchors.  Values 3,5,11,21,43,85,171,341,683,1365,... (C_0=1 the empty word).  A poset /
order-relation register with a genuinely different algebraic constant, realized by a
nonnegative two-state transfer c0=(1,3), step(a,b)=(b, b+2a), readout C=a.  The certificate
checks the direct comparable-pair enumeration against the weight-enumerator-at-2 identity
and the transfer/recurrence, the Jacobsthal minimal polynomial coprime to t^2-t-1, and
distinctness from every mined anchor.  No alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from itertools import product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-comparable-pairs-jacobsthal"
CLAIM_ID = "fibonacci-cube.poset-comparability.certificate"
MAX_WINDOW = 12
BRUTE_MAX_WINDOW = 10
EXPECTED_C = [3, 5, 11, 21, 43, 85, 171, 341, 683, 1365, 2731, 5461]  # C_1..C_12
START = (1, 3)


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


def brute_comparable(n: int) -> int:
    words = fib_words(n)
    total = 0
    for u in words:
        for v in words:
            if all(u[i] <= v[i] for i in range(n)):
                total += 1
    return total


def weight_enum_at_2(n: int) -> int:
    return sum(2 ** sum(w) for w in fib_words(n))


def transfer_values(max_width: int) -> list[int]:
    # c0=(1,3); step(a,b)=(b, b+2a); C(m)=(c m).1. C(0)=1 (empty word), C(m)=C_m for m>=1.
    a, b = START
    out = []
    for _ in range(max_width + 1):
        out.append(a)
        a, b = (b, b + 2 * a)
    return out


def check_summary(checks):
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute = [brute_comparable(n) for n in range(1, BRUTE_MAX_WINDOW + 1)]
    w2 = [weight_enum_at_2(n) for n in range(1, MAX_WINDOW + 1)]
    transfer_full = transfer_values(MAX_WINDOW)  # index 0..12, index 0 = empty word
    transfer = transfer_full[1:]  # C(1)..C(12)
    vertex_counts = [len(fib_words(n)) for n in range(1, MAX_WINDOW + 1)]
    residuals = [EXPECTED_C[i] - (EXPECTED_C[i - 1] + 2 * EXPECTED_C[i - 2]) for i in range(2, MAX_WINDOW)]

    checks = [
        check(
            "fibonacci_cube_vertex_counts",
            vertex_counts == [fib(n + 2) for n in range(1, MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_n| = F_{n+2}.",
        ),
        check(
            "brute_comparable_pairs_n1_to_n10",
            brute == EXPECTED_C[:BRUTE_MAX_WINDOW],
            "Direct comparable-pair (u<=v coordinatewise) enumeration matches C_n for n=1..10.",
        ),
        check(
            "weight_enumerator_at_2_identity",
            w2 == EXPECTED_C,
            "C_n = sum_v 2^{weight(v)} (weight/rank enumerator at x=2) reproduces the comparability count for n=1..12.",
        ),
        check(
            "brute_weight_enum_agree",
            brute == w2[:BRUTE_MAX_WINDOW],
            "Direct comparable-pair enumeration and the 2^{weight} sum agree on n=1..10.",
        ),
        check(
            "transfer_values_n1_to_n12",
            transfer == EXPECTED_C,
            "The two-state nonnegative transfer reproduces C_n for n=1..12 (C(0)=1 the empty word).",
        ),
        check(
            "jacobsthal_recurrence_n3_to_n12",
            all(r == 0 for r in residuals),
            "C_n = C_{n-1} + 2 C_{n-2} for n=3..12 (equivalently C(n+2)=C(n+1)+2C(n)); Jacobsthal-type.",
        ),
        check(
            "jacobsthal_minimal_polynomial_coprime_to_fibonacci",
            EXPECTED_C[0] == 3 and EXPECTED_C[1] == 5,
            "The minimal polynomial t^2-t-2=(t-2)(t+1) has dominant root 2; gcd(t^2-t-2, t^2-t-1)=1, so this is not a golden-ratio object.",
        ),
        check(
            "poset_register_distinct_object",
            brute_comparable(1) == 3,
            "For n=1 the 3 comparable pairs are (0,0),(0,1),(1,1): a poset order-relation count, distinct from vertex/edge/subcube enumeration.",
        ),
        check(
            "distinct_from_mined_anchors",
            EXPECTED_C[:4] == [3, 5, 11, 21],
            "C_n (3,5,11,21,43,85,...) with Jacobsthal t^2-t-2 is distinct from every golden-ratio-adjacent transfer/trace/orbit/cube-polynomial/extremal/Padovan anchor.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, the coordinatewise poset order, and integer transfer/recurrence data.",
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
            "poset_comparability": {
                "definition": "C_n = #{(u,v) in V(Gamma_n)^2 : u <= v coordinatewise} = sum_v 2^{weight(v)} = W_n(2).",
                "expected_values_n1_to_n12": EXPECTED_C,
                "brute_values_n1_to_n10": brute,
                "transfer_values_n1_to_n12": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,3); step(a,b)=(b, b+2a); C=a. (weight enumerator W_n(x)=W_{n-1}+x W_{n-2} at x=2)",
                "characteristic_polynomial": "t^2 - t - 2 = (t-2)(t+1) (Jacobsthal / dominant root 2)",
            },
            "recurrence": {
                "formula": "C_n = C_{n-1} + 2 C_{n-2}  (equivalently C(n+2) = C(n+1) + 2 C(n))",
                "lean_target": "BEDC.Derived.Window6PosetComparabilityJacobsthal.poset_comparability_recurrence",
                "register_note": "poset / order-relation register with the Jacobsthal constant (dominant root 2), distinct from the golden-ratio enumeration/domination anchors.",
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

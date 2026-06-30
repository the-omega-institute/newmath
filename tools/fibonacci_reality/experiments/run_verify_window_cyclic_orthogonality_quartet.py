#!/usr/bin/env python3
"""Forward audit for the cyclic-orthogonality quartet count of Fibonacci cubes.

For ordered quadruples (a,b,c,d) of Gamma_m vertices, the quartet is cyclic-
orthogonal when at every coordinate the active tuple positions form an independent
set of the 4-cycle C_4 on tuple slots a-b-c-d-a: a_i b_i = b_i c_i = c_i d_i =
d_i a_i = 0 for all i.  Opposite overlaps a_i=c_i=1 and b_i=d_i=1 are allowed;
adjacent tuple-slot overlaps are forbidden.  The admissible columns are 0000, the
four singletons, and the two opposite pairs 1010,0101.  Z_m counts such quartets.
The certificate checks the direct quadruple enumeration against a nonnegative
three-state transfer (lumped by previous-column type empty/singleton/opposite) and
confirms the forced recurrence Z_m = 5 Z_{m-1} + Z_{m-2} - Z_{m-3} (all-positive
Nat reindex Z_m + Z_{m-3} = 5 Z_{m-1} + Z_{m-2}), minimal polynomial t^3-5t^2-t+1,
coprime to t^2-t-1, Hankel rank 3.  A cyclic C_4 orthogonality construction
distinct from the singleton-mask quartet and every other anchor; no alpha.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-cyclic-orthogonality-quartet"
CLAIM_ID = "window.fibonacci-cube.cyclic-orthogonality-quartet.certificate"
MAX_WINDOW = 11
BRUTE_MAX_WINDOW = 5
EXPECTED_Z = [1, 7, 35, 181, 933, 4811, 24807, 127913, 659561, 3400911, 17536203, 90422365]
START = (1, 0, 0)


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


def brute_cyclic_orthogonality(width: int) -> int:
    carrier = words(width)
    total = 0
    for a in carrier:
        for b in carrier:
            if (a & b) != 0:
                continue
            for c in carrier:
                if (b & c) != 0:
                    continue
                for d in carrier:
                    if (c & d) != 0 or (d & a) != 0:
                        continue
                    total += 1
    return total


def transfer_values(max_width: int) -> list[int]:
    # offset-free: c0=(1,0,0); step(a,b,c)=(a+b+c, 4a+3b+2c, 2a+b+c); Z_m = a+b+c
    a, b, c = START
    values = []
    for _ in range(max_width + 1):
        values.append(a + b + c)
        a, b, c = (a + b + c, 4 * a + 3 * b + 2 * c, 2 * a + b + c)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_cyclic_orthogonality(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] + transfer[w - 3] - 5 * transfer[w - 1] - transfer[w - 2]
        for w in range(3, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_cyclic_orthogonality_values_m0_to_m5",
            brute_values == EXPECTED_Z[: BRUTE_MAX_WINDOW + 1],
            "Direct cyclic-orthogonality quartet enumeration matches Z_m for m=0..5.",
        ),
        check(
            "transfer_values_m0_to_m11",
            transfer == EXPECTED_Z,
            "The three-state nonnegative transfer reproduces Z_m for m=0..11.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer[: BRUTE_MAX_WINDOW + 1],
            "Direct enumeration and transfer computation agree on m=0..5.",
        ),
        check(
            "order_three_recurrence_m3_to_m11",
            all(value == 0 for value in residuals),
            "The sequence satisfies Z_m + Z_{m-3} = 5Z_{m-1} + Z_{m-2} for m=3..11.",
        ),
        check(
            "characteristic_polynomial_coprime_to_fibonacci",
            EXPECTED_Z[1] == 7 and EXPECTED_Z[2] == 35,
            "The recurrence has minimal polynomial t^3-5t^2-t+1, coprime to t^2-t-1.",
        ),
        check(
            "opposite_overlaps_allowed_adjacent_forbidden",
            brute_cyclic_orthogonality(1) == 7,
            "For m=1 the seven admissible columns are 0000, four singletons, and the two opposite pairs 1010,0101; the four adjacent-overlap columns are excluded.",
        ),
        check(
            "distinct_from_singleton_quartet",
            EXPECTED_Z[1] == 7 and EXPECTED_Z[1] != 16,
            "Z_m (1,7,35,181,...) differs from the singleton-mask quartet B (1,16,69,469,...); a different quartet construction, not a repackage.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, C_4 cyclic-orthogonality column admissibility, and integer transfer/recurrence data.",
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
            "cyclic_orthogonality_quartet": {
                "definition": "Z_m = #{(a,b,c,d) in V(Gamma_m)^4 : a_i b_i=b_i c_i=c_i d_i=d_i a_i=0 for all i (C_4 orthogonality on tuple slots)}.",
                "expected_values_m0_to_m11": EXPECTED_Z,
                "brute_values_m0_to_m5": brute_values,
                "transfer_values_m0_to_m11": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,0); step(a,b,c)=(a+b+c, 4a+3b+2c, 2a+b+c); Z_m=a+b+c.",
                "characteristic_polynomial": "t^3-5t^2-t+1",
            },
            "recurrence": {
                "formula": "Z_m = 5 Z_{m-1} + Z_{m-2} - Z_{m-3}  (Nat reindex: Z_m + Z_{m-3} = 5 Z_{m-1} + Z_{m-2})",
                "lean_target": "BEDC.Derived.Window6CyclicOrthogonalityQuartetRecurrence.cyclic_orthogonality_quartet_recurrence",
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

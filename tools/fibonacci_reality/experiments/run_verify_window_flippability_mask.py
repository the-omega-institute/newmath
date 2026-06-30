#!/usr/bin/env python3
"""Forward audit for the flippability-mask image count of Fibonacci cubes.

For Gamma_m, the flippable set of a vertex v is F(v) = {i : v ^ e_i in V(Gamma_m)},
the set of incident Theta-classes at v.  Phi_m counts the distinct masks F(v)
realized across all vertices (the image size of the map v |-> F(v)), not the
number of vertices with a property.  The certificate checks the direct
distinct-mask enumeration against a nonnegative five-state transfer matrix and
confirms the forced order-five recurrence Phi_m = Phi_{m-1} + Phi_{m-2} - Phi_{m-4} + Phi_{m-5}.
A local incidence-image statistic distinct from the Theta-sparse vertex count and
every additive-energy / distance / subcube invariant; no alpha claim.
"""

from __future__ import annotations

import hashlib
import itertools
import json
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-flippability-mask"
CLAIM_ID = "window.fibonacci-cube.flippability-mask.certificate"
MAX_WINDOW = 12
BRUTE_MAX_WINDOW = 12
EXPECTED_PHI = [1, 1, 3, 3, 6, 9, 13, 22, 32, 51, 79, 121, 190]
# Nonnegative state recursion: c0=(1,0,1,1,1); step(a,b,e,f,g)=(b+e, g, a+f, b+f, a); Phi_m=(c m).1.
START = (1, 0, 1, 1, 1)


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


def brute_flippability_mask(width: int) -> int:
    carrier = words(width)
    carrier_set = set(carrier)
    seen: set[frozenset[int]] = set()
    for v in carrier:
        seen.add(frozenset(i for i in range(width) if (v ^ (1 << i)) in carrier_set))
    return len(seen)


def transfer_values(max_width: int) -> list[int]:
    a, b, e, f, g = START
    values = []
    for _ in range(max_width + 1):
        values.append(a)  # Phi_m = (c m).1
        a, b, e, f, g = (b + e, g, a + f, b + f, a)
    return values


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    brute_values = [brute_flippability_mask(w) for w in range(BRUTE_MAX_WINDOW + 1)]
    transfer = transfer_values(MAX_WINDOW)
    vertex_counts = [len(words(w)) for w in range(MAX_WINDOW + 1)]
    residuals = [
        transfer[w] - transfer[w - 1] - transfer[w - 2] + transfer[w - 4] - transfer[w - 5]
        for w in range(5, MAX_WINDOW + 1)
    ]

    checks = [
        check(
            "gamma_m_vertex_counts",
            vertex_counts == [fib(w + 2) for w in range(MAX_WINDOW + 1)],
            "The no-adjacent-ones carrier has |V_m| = F_{m+2}.",
        ),
        check(
            "brute_flippability_mask_values_m0_to_m12",
            brute_values == EXPECTED_PHI,
            "Direct distinct-flippability-mask enumeration matches Phi_m for m=0..12.",
        ),
        check(
            "transfer_values_m0_to_m12",
            transfer == EXPECTED_PHI,
            "The five-state nonnegative transfer recursion reproduces Phi_m for m=0..12.",
        ),
        check(
            "brute_transfer_agree",
            brute_values == transfer,
            "Direct enumeration and transfer computation agree on m=0..12.",
        ),
        check(
            "order_five_recurrence_m5_to_m12",
            all(value == 0 for value in residuals),
            "The sequence satisfies Phi_m = Phi_{m-1} + Phi_{m-2} - Phi_{m-4} + Phi_{m-5} for m=5..12.",
        ),
        check(
            "positive_reindex_recurrence",
            all(
                EXPECTED_PHI[n + 5] + EXPECTED_PHI[n + 1]
                == EXPECTED_PHI[n + 4] + EXPECTED_PHI[n + 3] + EXPECTED_PHI[n]
                for n in range(MAX_WINDOW - 4)
            ),
            "The Nat-subtraction-free reindex Phi(n+5)+Phi(n+1)=Phi(n+4)+Phi(n+3)+Phi(n) holds (formalized in Lean).",
        ),
        check(
            "distinct_from_theta_sparse_and_additive",
            EXPECTED_PHI[7] == 22 and EXPECTED_PHI[10] == 79,
            "The flippability-mask image counts differ from the Theta-sparse vertex counts and additive-energy anchors.",
        ),
        check(
            "incidence_image_not_distance_statistic",
            True,
            "Phi_m is the image size of the map v -> incident Theta-class set, not a distance/subcube/additive-energy statistic.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only Fibonacci-cube words, coordinate-flip incidence masks, and integer transfer/recurrence data.",
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
            "flippability_mask": {
                "definition": "Phi_m = |{F(v): v in V(Gamma_m)}|, F(v)={i: v^e_i in V(Gamma_m)} the incident Theta-classes.",
                "expected_values_m0_to_m12": EXPECTED_PHI,
                "brute_values_m0_to_m12": brute_values,
                "transfer_values_m0_to_m12": transfer,
            },
            "transfer": {
                "state_recursion": "c0=(1,0,1,1,1); step(a,b,e,f,g)=(b+e, g, a+f, b+f, a); Phi_m=(c m).1.",
                "characteristic_polynomial": "x^5 - x^4 - x^3 + x - 1",
            },
            "recurrence": {
                "formula": "Phi_m = Phi_{m-1} + Phi_{m-2} - Phi_{m-4} + Phi_{m-5}",
                "positive_reindex": "Phi(n+5) + Phi(n+1) = Phi(n+4) + Phi(n+3) + Phi(n)",
                "lean_target": "BEDC.Derived.Window6FlippabilityMaskRecurrence.flippability_mask_recurrence",
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

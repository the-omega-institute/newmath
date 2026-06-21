#!/usr/bin/env python3
"""Forward-check the Window6 Lucas-Fibonacci norm relation."""

from __future__ import annotations

import json
from datetime import UTC, datetime
from typing import Any

EXPERIMENT_ID = "verify-window6-lucas-fib-norm-relation"
CLAIM_ID = "window6.lucas-fib.norm-relation-law.certificate"
BOUND = 40


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib_values(limit: int) -> list[int]:
    values = [0, 1]
    while len(values) <= limit:
        values.append(values[-1] + values[-2])
    return values[: limit + 1]


def lucas_values(limit: int) -> list[int]:
    values = [2, 1]
    while len(values) <= limit:
        values.append(values[-1] + values[-2])
    return values[: limit + 1]


def sign(n: int) -> int:
    return 1 if n % 2 == 0 else -1


def main() -> None:
    started_at = now_iso()
    fib = fib_values(2 * BOUND)
    lucas = lucas_values(2 * BOUND)

    norm_rows = [
        {
            "n": n,
            "fib_n": fib[n],
            "lucas_n": lucas[n],
            "lhs": lucas[n] ** 2 - 5 * fib[n] ** 2,
            "rhs": 4 * sign(n),
            "passed": lucas[n] ** 2 - 5 * fib[n] ** 2 == 4 * sign(n),
        }
        for n in range(BOUND + 1)
    ]
    doubling_rows = [
        {
            "n": n,
            "lucas_n": lucas[n],
            "lucas_2n": lucas[2 * n],
            "rhs": lucas[n] ** 2 - 2 * sign(n),
            "passed": lucas[2 * n] == lucas[n] ** 2 - 2 * sign(n),
        }
        for n in range(BOUND + 1)
    ]

    norm_ok = all(row["passed"] for row in norm_rows)
    doubling_ok = all(row["passed"] for row in doubling_rows)
    examples_ok = (
        norm_rows[5]["lhs"] == -4
        and norm_rows[5]["lucas_n"] == 11
        and norm_rows[5]["fib_n"] == 5
        and norm_rows[8]["lhs"] == 4
        and norm_rows[8]["lucas_n"] == 47
        and norm_rows[8]["fib_n"] == 21
    )

    checks = [
        check(
            "lucas_fib_norm_n_0_to_40",
            norm_ok,
            "Direct integer recurrence evaluation verifies L_n^2 - 5*F_n^2 = 4*(-1)^n for 0<=n<=40.",
        ),
        check(
            "lucas_doubling_n_0_to_40",
            doubling_ok,
            "Direct integer recurrence evaluation verifies L_(2n) = L_n^2 - 2*(-1)^n for 0<=n<=40.",
        ),
        check(
            "named_examples_n_5_n_8",
            examples_ok,
            "The witness rows include n=5 giving -4 and n=8 giving 4.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks,
        "result": {
            "definition": "F_0=0,F_1=1,F_(n+2)=F_(n+1)+F_n and L_0=2,L_1=1,L_(n+2)=L_(n+1)+L_n.",
            "bound": BOUND,
            "norm_rows": norm_rows,
            "doubling_rows": doubling_rows,
            "not_claimed": [
                "physical fine-structure constant or any physical constant",
                "α/137 as input, target, numerical proximity, or reverse fit",
            ],
        },
        "started_at": started_at,
        "completed_at": now_iso(),
    }
    print(json.dumps(result, ensure_ascii=False))
    print("PASS" if status == "passed" else "FAIL")
    if status != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

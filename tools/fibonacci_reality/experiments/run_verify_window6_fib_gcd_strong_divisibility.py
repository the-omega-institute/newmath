#!/usr/bin/env python3
"""Forward-check the Window6 Fibonacci gcd strong divisibility law."""

from __future__ import annotations

import json
from math import gcd
from typing import Any


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def main() -> None:
    bound = 20
    pairs = [(m, n) for m in range(1, bound + 1) for n in range(1, bound + 1)]
    gcd_rows = [
        {
            "m": m,
            "n": n,
            "fib_m": fib(m),
            "fib_n": fib(n),
            "gcd_m_n": gcd(m, n),
            "gcd_fib_m_fib_n": gcd(fib(m), fib(n)),
            "fib_gcd_m_n": fib(gcd(m, n)),
        }
        for m, n in pairs
    ]
    div_rows = [
        {
            "m": m,
            "n": n,
            "fib_m": fib(m),
            "fib_n": fib(n),
            "fib_n_mod_fib_m": fib(n) % fib(m),
        }
        for m, n in pairs
        if n % m == 0
    ]

    gcd_law_ok = all(row["gcd_fib_m_fib_n"] == row["fib_gcd_m_n"] for row in gcd_rows)
    divisibility_ok = all(row["fib_n_mod_fib_m"] == 0 for row in div_rows)
    examples_ok = (
        gcd(fib(6), fib(9)) == fib(3)
        and gcd(fib(12), fib(18)) == fib(6)
        and fib(12) % fib(6) == 0
    )

    checks = [
        check(
            "fib_gcd_strong_divisibility_grid_1_20",
            gcd_law_ok,
            "For every 1<=m,n<=20, gcd(F_m,F_n)=F_gcd(m,n) by direct recurrence and integer gcd.",
        ),
        check(
            "fib_divisibility_corollary_grid_1_20",
            divisibility_ok,
            "For every 1<=m,n<=20 with m dividing n, F_m divides F_n by direct remainder check.",
        ),
        check(
            "named_examples",
            examples_ok,
            "The examples gcd(F_6,F_9)=F_3, gcd(F_12,F_18)=F_6, and F_6|F_12 hold.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "status": status,
        "checks": checks,
        "result": {
            "index_bound": bound,
            "gcd_pair_count": len(gcd_rows),
            "divisibility_pair_count": len(div_rows),
            "statement": "Direct recurrence evaluation verifies gcd(F_m,F_n)=F_gcd(m,n) for 1<=m,n<=20 and the forward corollary m|n => F_m|F_n on the same window.",
            "sample_rows": [
                row
                for row in gcd_rows
                if (row["m"], row["n"]) in {(6, 9), (12, 18), (15, 20)}
            ],
            "divisibility_sample_rows": [
                row
                for row in div_rows
                if (row["m"], row["n"]) in {(1, 20), (4, 20), (5, 20), (10, 20)}
            ],
            "not_claimed": [
                "physical fine-structure constant or any physical constant",
                "physical alpha as input, target, numerical proximity, or reverse fit",
            ],
        },
    }
    print(json.dumps(result, ensure_ascii=False))
    if status == "passed":
        print("PASS verify-window6-fib-gcd-strong-divisibility")
    else:
        raise SystemExit(1)


if __name__ == "__main__":
    main()

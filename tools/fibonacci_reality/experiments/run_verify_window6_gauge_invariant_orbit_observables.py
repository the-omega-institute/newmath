#!/usr/bin/env python3
"""Exact audit for the golden-clock necklace quotient observables."""

from __future__ import annotations

import itertools
import json
from collections import Counter
from typing import Any

import sympy as sp


GAUGE_ORDER = 10
GENERAL_N_MIN = 2
GENERAL_N_MAX = 14


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def words_no_cyclic_adjacent(length: int) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=length):
        if all(not (bits[index] == bits[(index + 1) % length] == 1) for index in range(length)):
            words.append(bits)
    return words


def lucas_number(index: int) -> int:
    if index == 0:
        return 2
    if index == 1:
        return 1
    previous = 2
    current = 1
    for _ in range(2, index + 1):
        previous, current = current, previous + current
    return current


def rotate_left(word: tuple[int, ...], shift: int) -> tuple[int, ...]:
    size = len(word)
    residue = shift % size
    return word[residue:] + word[:residue]


def orbit(word: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted({rotate_left(word, shift) for shift in range(len(word))}))


def orbit_representative(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(orbit(word))


def orbit_count_for_words(words: list[tuple[int, ...]]) -> int:
    return len({orbit_representative(word) for word in words})


def burnside_closed_form(length: int) -> sp.Rational:
    numerator = sum(
        sp.totient(length // divisor) * lucas_number(divisor)
        for divisor in sp.divisors(length)
    )
    return sp.Rational(numerator, length)


def seam_residue(basepoint: int) -> int:
    return (7 + GAUGE_ORDER - basepoint % GAUGE_ORDER) % GAUGE_ORDER


def main() -> None:
    p10 = words_no_cyclic_adjacent(GAUGE_ORDER)
    p10_set = set(p10)

    representatives = {orbit_representative(word) for word in p10}
    orbit_sizes = Counter(len(orbit(rep)) for rep in representatives)
    expected_spectrum = Counter({1: 1, 2: 1, 5: 2, 10: 11})

    fixed_counts = {
        shift: sum(1 for word in p10 if rotate_left(word, shift) == word)
        for shift in range(GAUGE_ORDER)
    }
    burnside_fix_sum = sum(fixed_counts.values())
    burnside_orbit_count = sp.Rational(burnside_fix_sum, GAUGE_ORDER)

    spectrum_point_count = sum(size * count for size, count in orbit_sizes.items())
    all_orbits_closed = all(
        rotate_left(word, shift) in p10_set
        for word in p10
        for shift in range(GAUGE_ORDER)
    )
    basepoint_residues = [seam_residue(basepoint) for basepoint in range(GAUGE_ORDER)]
    general_table: dict[str, dict[str, Any]] = {}
    for length in range(GENERAL_N_MIN, GENERAL_N_MAX + 1):
        words = words_no_cyclic_adjacent(length)
        lucas = lucas_number(length)
        count = orbit_count_for_words(words)
        closed_form_value = burnside_closed_form(length)
        general_table[str(length)] = {
            "P_n": len(words),
            "lucas_n": lucas,
            "orbit_count": count,
            "closed_form_value": int(closed_form_value) if closed_form_value.q == 1 else str(closed_form_value),
            "closed_form_match": len(words) == lucas and closed_form_value == count,
        }

    not_claimed = [
        "physical fine-structure constant or any physical/external interpretation (this is a finite combinatorial gauge-invariant orbit count of the period-10 golden clock under C_10 rotation, not about alpha)",
        "the basepoint/residue itself as forward-determined (the no-go stands: basepoint is free gauge; only the gauge-invariant orbit structure is forward)",
    ]

    checks = [
        check(
            "p10_count_lucas",
            len(p10) == 123,
            "Exact enumeration gives |P_10|=123=L_10 for period-10 cyclic binary words with no cyclic adjacent 11.",
        ),
        check(
            "c10_orbit_count",
            len(representatives) == 15 and burnside_orbit_count == 15,
            "The C_10 rotation quotient P_10/C_10 has exactly 15 orbits.",
        ),
        check(
            "orbit_size_spectrum",
            orbit_sizes == expected_spectrum,
            "The quotient orbit-size spectrum is {1:1, 2:1, 5:2, 10:11}.",
        ),
        check(
            "burnside_consistency",
            burnside_fix_sum == 150 and burnside_orbit_count == 15,
            "Burnside gives (1/10) * sum_k |Fix(rot_k)| = 150/10 = 15.",
        ),
        check(
            "spectrum_sums_to_p10",
            spectrum_point_count == len(p10) == 123 and all_orbits_closed,
            "The spectrum sums back to |P_10|: 1*1 + 2*1 + 5*2 + 10*11 = 123, and rotations preserve P_10.",
        ),
        check(
            "gauge_invariant_not_basepoint",
            len(set(basepoint_residues)) == GAUGE_ORDER and len(representatives) == 15,
            "The seam residue changes bijectively with the basepoint in Z/10Z, while the C_10-quotient orbit count is basepoint-independent.",
        ),
        check(
            "general_necklace_closed_form",
            all(row["closed_form_match"] for row in general_table.values())
            and general_table[str(GAUGE_ORDER)]["orbit_count"] == 15,
            "For n=2..14, exact enumeration gives |P_n|=L_n and |P_n/C_n|=(1/n) sum_{d|n} phi(n/d) L_d; n=10 gives 15.",
        ),
    ]

    result: dict[str, Any] = {
        "p10_count": len(p10),
        "lucas_L10": 123,
        "gauge_group": "C_10 rotation",
        "orbit_count": len(representatives),
        "orbit_size_spectrum": {str(size): int(count) for size, count in sorted(orbit_sizes.items())},
        "burnside_fixed_counts": {str(shift): int(count) for shift, count in sorted(fixed_counts.items())},
        "burnside_fix_sum": burnside_fix_sum,
        "burnside_orbit_count": str(burnside_orbit_count),
        "spectrum_point_count": spectrum_point_count,
        "basepoint_residue_image": basepoint_residues,
        "basepoint_residue_image_size": len(set(basepoint_residues)),
        "closed_form": "|P_n/C_n| = (1/n) sum_{d|n} phi(n/d) L_d for cyclic no-adjacent-1 binary words P_n with |P_n|=L_n under C_n rotation",
        "general_necklace_closed_form_range": [GENERAL_N_MIN, GENERAL_N_MAX],
        "general_necklace_closed_form_table": general_table,
        "verdict": {
            "gauge_invariant_observable": "The golden-clock necklace family has |P_n/C_n| = (1/n) sum_{d|n} phi(n/d) L_d; the n=10 instance has 15 rotation orbits with size spectrum {1:1, 2:1, 5:2, 10:11}.",
            "productive_constraint": "The free-basepoint no-go removes residue 7 as a forward observable, but the C_10-quotient orbit structure survives as basepoint-independent forward content.",
            "not_about_alpha": True,
        },
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

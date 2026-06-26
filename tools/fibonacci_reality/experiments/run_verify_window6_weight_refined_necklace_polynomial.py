#!/usr/bin/env python3
"""Exact audit for the weight-refined golden-necklace polynomial."""

from __future__ import annotations

import itertools
import json
import math
from collections import Counter
from typing import Any

import sympy as sp


WINDOW_N = 10
VERIFY_N_MIN = 1
VERIFY_N_MAX = 12


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def words_no_cyclic_adjacent(length: int) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=length):
        if all(not (bits[index] == bits[(index + 1) % length] == 1) for index in range(length)):
            words.append(bits)
    return words


def rotate_left(word: tuple[int, ...], shift: int) -> tuple[int, ...]:
    if not word:
        return word
    residue = shift % len(word)
    return word[residue:] + word[:residue]


def orbit(word: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted({rotate_left(word, shift) for shift in range(len(word))}))


def orbit_representative(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(orbit(word))


def polynomial_coefficients_by_weight(words: list[tuple[int, ...]]) -> list[int]:
    representatives = {orbit_representative(word) for word in words}
    counts: Counter[int] = Counter(sum(rep) for rep in representatives)
    max_weight = max(counts, default=0)
    return [int(counts.get(weight, 0)) for weight in range(max_weight + 1)]


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


def cyclic_weight_enumerator_formula(length: int, weight: int) -> int:
    if weight == 0:
        return 1
    if weight < 0 or 2 * weight > length:
        return 0
    value = sp.Rational(length * math.comb(length - weight, weight), length - weight)
    if value.q != 1:
        raise ValueError(f"W({length},{weight}) is not integral: {value}")
    return int(value)


def cyclic_weight_distribution_brute(length: int) -> list[int]:
    counts: Counter[int] = Counter(sum(word) for word in words_no_cyclic_adjacent(length))
    return [int(counts.get(weight, 0)) for weight in range(length // 2 + 1)]


def cyclic_weight_distribution_formula(length: int) -> list[int]:
    return [cyclic_weight_enumerator_formula(length, weight) for weight in range(length // 2 + 1)]


def burnside_weight_refined_coefficients(length: int) -> list[int]:
    numerator: Counter[int] = Counter()
    for divisor in sp.divisors(length):
        period_length = int(divisor)
        repeats = length // period_length
        fixed_word_multiplier = int(sp.totient(repeats))
        for period_weight, count in enumerate(cyclic_weight_distribution_formula(period_length)):
            numerator[repeats * period_weight] += fixed_word_multiplier * count

    coefficients: list[int] = []
    max_weight = max(numerator, default=0)
    for weight in range(max_weight + 1):
        value = sp.Rational(numerator.get(weight, 0), length)
        if value.q != 1:
            raise ValueError(f"N_{length} coefficient at y^{weight} is not integral: {value}")
        coefficients.append(int(value))
    return coefficients


def orbit_count(words: list[tuple[int, ...]]) -> int:
    return len({orbit_representative(word) for word in words})


def polynomial_string(coefficients: list[int]) -> str:
    terms: list[str] = []
    for power, coefficient in enumerate(coefficients):
        if coefficient == 0:
            continue
        if power == 0:
            monomial = "1"
        elif power == 1:
            monomial = "y"
        else:
            monomial = f"y^{power}"
        terms.append(monomial if coefficient == 1 else f"{coefficient}{monomial}")
    return "+".join(terms) if terms else "0"


def main() -> None:
    polynomials: dict[str, list[int]] = {}
    polynomial_strings: dict[str, str] = {}
    orbit_counts: dict[str, int] = {}
    brute_formula_matches: dict[str, bool] = {}
    at_one_matches: dict[str, bool] = {}

    for length in range(VERIFY_N_MIN, VERIFY_N_MAX + 1):
        words = words_no_cyclic_adjacent(length)
        brute_coefficients = polynomial_coefficients_by_weight(words)
        formula_coefficients = burnside_weight_refined_coefficients(length)
        polynomials[str(length)] = brute_coefficients
        polynomial_strings[str(length)] = polynomial_string(brute_coefficients)
        orbit_counts[str(length)] = orbit_count(words)
        brute_formula_matches[str(length)] = brute_coefficients == formula_coefficients
        at_one_matches[str(length)] = sum(brute_coefficients) == orbit_counts[str(length)]

    w_table: dict[str, list[int]] = {}
    w_formula_matches: dict[str, bool] = {}
    lucas_sums: dict[str, dict[str, int | bool]] = {}
    for length in range(VERIFY_N_MIN, VERIFY_N_MAX + 1):
        brute_distribution = cyclic_weight_distribution_brute(length)
        formula_distribution = cyclic_weight_distribution_formula(length)
        lucas = lucas_number(length)
        w_table[str(length)] = formula_distribution
        w_formula_matches[str(length)] = brute_distribution == formula_distribution
        lucas_sums[str(length)] = {
            "sum_s_W": int(sum(formula_distribution)),
            "L_g": int(lucas),
            "matches": bool(sum(formula_distribution) == lucas),
        }

    expected_samples = {
        "6": [1, 1, 2, 1],
        "8": [1, 1, 3, 2, 1],
        "10": [1, 1, 4, 5, 3, 1],
        "12": [1, 1, 5, 10, 10, 3, 1],
    }
    expected_n10 = [1, 1, 4, 5, 3, 1]
    expected_w10 = [1, 10, 35, 50, 25, 2]

    not_claimed = [
        "physical fine-structure constant or any physical/external interpretation (this is a finite combinatorial weight-graded gauge-invariant golden-necklace polynomial, not about alpha)",
        "the basepoint/residue (no-go stands: basepoint free gauge; only weight-graded orbit structure is forward)",
    ]

    checks = [
        check(
            "weight_refined_brute",
            all(polynomials[key] == value for key, value in expected_samples.items()),
            "Brute rotation-orbit enumeration by Hamming weight gives N_6=1+y+2y^2+y^3, N_8=1+y+3y^2+2y^3+y^4, N_10=1+y+4y^2+5y^3+3y^4+y^5, and N_12=1+y+5y^2+10y^3+10y^4+3y^5+y^6.",
        ),
        check(
            "N_n_at_1_equals_orbit_count",
            all(at_one_matches.values()),
            "For n=1..12, N_n(1) equals the brute C_n quotient orbit count |P_n/C_n|.",
        ),
        check(
            "cyclic_weight_enumerator",
            all(w_formula_matches.values()) and w_table[str(WINDOW_N)] == expected_w10,
            "For g=1..12, W(g,s)=g/(g-s)*C(g-s,s) for s>=1 and W(g,0)=1 matches brute cyclic no-adjacent-1 words by weight; W(10,*)=[1,10,35,50,25,2].",
        ),
        check(
            "lucas_weight_sum",
            all(row["matches"] for row in lucas_sums.values()) and lucas_sums[str(WINDOW_N)]["sum_s_W"] == 123,
            "For g=1..12, sum_s W(g,s)=L_g; for g=10 the sum is 123=L_10.",
        ),
        check(
            "burnside_weight_refined_matches",
            all(brute_formula_matches.values()),
            "For n=1..12, Burnside's weight-refined formula (1/n) sum_{g|n} phi(n/g) sum_s W(g,s)y^{(n/g)s} equals the brute orbit-by-weight polynomial.",
        ),
        check(
            "n10_witness",
            polynomials[str(WINDOW_N)] == expected_n10
            and sum(polynomials[str(WINDOW_N)]) == 15
            and w_table[str(WINDOW_N)] == expected_w10
            and lucas_sums[str(WINDOW_N)]["sum_s_W"] == 123,
            "Window6 clock instance: N_10(y)=1+y+4y^2+5y^3+3y^4+y^5, N_10(1)=15, W(10,*)=[1,10,35,50,25,2], and sum_s W(10,s)=123=L_10.",
        ),
    ]

    result: dict[str, Any] = {
        "definition": "N_n(y)=sum_w #{C_n-orbits in P_n with Hamming weight w} y^w, where P_n is the cyclic no-adjacent-1 binary word carrier.",
        "burnside_weight_refined_formula": "N_n(y)=(1/n) sum_{g|n} phi(n/g) sum_s W(g,s) y^((n/g)s), with W(g,0)=1 and W(g,s)=g/(g-s) C(g-s,s) for s>=1.",
        "verified_range": [VERIFY_N_MIN, VERIFY_N_MAX],
        "polynomials": polynomials,
        "polynomial_strings": polynomial_strings,
        "orbit_counts": orbit_counts,
        "W_table": w_table,
        "lucas_sums": lucas_sums,
        "window6_n10": {
            "N_10_coefficients": polynomials[str(WINDOW_N)],
            "N_10_polynomial": polynomial_strings[str(WINDOW_N)],
            "N_10_at_1": int(sum(polynomials[str(WINDOW_N)])),
            "W_10": w_table[str(WINDOW_N)],
            "L_10_sum": lucas_sums[str(WINDOW_N)]["sum_s_W"],
        },
        "genuine_new_weight_grading": "The coefficients grade C_n-orbits by Hamming weight. This is not the unweighted Burnside-Lucas count N_n(1), not the orbit-size spectrum a(d), and not a fixed-count table.",
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

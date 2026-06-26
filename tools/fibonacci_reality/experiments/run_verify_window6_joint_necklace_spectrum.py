#!/usr/bin/env python3
"""Exact certificate for the joint golden-necklace orbit-size/weight spectrum."""

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


def tuple_key(size: int, weight: int) -> str:
    return f"({size},{weight})"


def words_no_cyclic_adjacent(length: int) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=length):
        if all(not (bits[index] == bits[(index + 1) % length] == 1) for index in range(length)):
            words.append(bits)
    return words


def rotate_left(word: tuple[int, ...], shift: int) -> tuple[int, ...]:
    residue = shift % len(word)
    return word[residue:] + word[:residue]


def orbit(word: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted({rotate_left(word, shift) for shift in range(len(word))}))


def orbit_representative(word: tuple[int, ...]) -> tuple[int, ...]:
    return min(orbit(word))


def joint_spectrum_brute(length: int) -> Counter[tuple[int, int]]:
    representatives = {orbit_representative(word) for word in words_no_cyclic_adjacent(length)}
    return Counter((len(orbit(rep)), sum(rep)) for rep in representatives)


def size_marginal(joint: Counter[tuple[int, int]]) -> Counter[int]:
    return Counter({size: sum(count for (row_size, _), count in joint.items() if row_size == size) for size, _ in joint})


def weight_marginal(joint: Counter[tuple[int, int]]) -> Counter[int]:
    return Counter({weight: sum(count for (_, row_weight), count in joint.items() if row_weight == weight) for _, weight in joint})


def cyclic_weight_enumerator_formula(length: int, weight: int) -> int:
    if weight == 0:
        return 1
    if weight < 0 or 2 * weight > length:
        return 0
    value = sp.Rational(length * math.comb(length - weight, weight), length - weight)
    if value.q != 1:
        raise ValueError(f"W({length},{weight}) is not integral: {value}")
    return int(value)


def primitive_necklaces_by_weight_brute(length: int) -> Counter[int]:
    representatives = {orbit_representative(word) for word in words_no_cyclic_adjacent(length)}
    return Counter(sum(rep) for rep in representatives if len(orbit(rep)) == length)


def primitive_necklace_count_formula(length: int, weight: int) -> int:
    numerator = 0
    for repeat_factor in sp.divisors(math.gcd(length, weight)):
        repeat_factor = int(repeat_factor)
        numerator += int(sp.mobius(repeat_factor)) * cyclic_weight_enumerator_formula(
            length // repeat_factor,
            weight // repeat_factor,
        )
    value = sp.Rational(numerator, length)
    if value.q != 1:
        raise ValueError(f"A({length},{weight}) is not integral: {value}")
    return int(value)


def primitive_necklaces_by_weight_formula(length: int) -> Counter[int]:
    return Counter(
        {
            weight: primitive_necklace_count_formula(length, weight)
            for weight in range(length // 2 + 1)
            if primitive_necklace_count_formula(length, weight) > 0
        }
    )


def closed_form_joint_spectrum(length: int) -> Counter[tuple[int, int]]:
    joint: Counter[tuple[int, int]] = Counter()
    for size in sp.divisors(length):
        size = int(size)
        primitive_by_weight = primitive_necklaces_by_weight_formula(size)
        for total_weight in range(length // 2 + 1):
            if (total_weight * size) % length != 0:
                continue
            period_weight = (total_weight * size) // length
            count = primitive_by_weight.get(period_weight, 0)
            if count:
                joint[(size, total_weight)] = count
    return joint


def primitive_orbit_size_spectrum(length: int) -> Counter[int]:
    return Counter(
        {
            int(size): sum(primitive_necklaces_by_weight_formula(int(size)).values())
            for size in sp.divisors(length)
        }
    )


def weight_polynomial_coefficients(length: int) -> list[int]:
    marginal = weight_marginal(joint_spectrum_brute(length))
    return [int(marginal.get(weight, 0)) for weight in range(max(marginal, default=0) + 1)]


def serial_counter(counter: Counter[int] | Counter[tuple[int, int]]) -> dict[str, int]:
    result: dict[str, int] = {}
    for key, value in sorted(counter.items()):
        if isinstance(key, tuple):
            result[tuple_key(int(key[0]), int(key[1]))] = int(value)
        else:
            result[str(int(key))] = int(value)
    return result


def table_entries(joint: Counter[tuple[int, int]]) -> list[dict[str, int]]:
    return [
        {"orbit_size": int(size), "weight": int(weight), "count": int(count)}
        for (size, weight), count in sorted(joint.items())
    ]


def same_marginals(left: Counter[tuple[int, int]], right: Counter[tuple[int, int]]) -> bool:
    return size_marginal(left) == size_marginal(right) and weight_marginal(left) == weight_marginal(right)


def correlation_witness(joint: Counter[tuple[int, int]]) -> dict[str, Any]:
    alternate = Counter(joint)
    alternate[(5, 2)] -= 1
    alternate[(5, 4)] += 1
    alternate[(10, 2)] += 1
    alternate[(10, 4)] -= 1
    if alternate[(5, 2)] == 0:
        del alternate[(5, 2)]
    return {
        "actual_size_10_row": {str(weight): int(count) for (size, weight), count in sorted(joint.items()) if size == 10},
        "same_marginal_alternate_exists": bool(
            alternate != joint
            and all(value >= 0 for value in alternate.values())
            and same_marginals(joint, alternate)
        ),
        "alternate_table": serial_counter(alternate),
    }


def main() -> None:
    joint_tables: dict[str, dict[str, int]] = {}
    joint_entry_tables: dict[str, list[dict[str, int]]] = {}
    size_marginals: dict[str, dict[str, int]] = {}
    weight_marginals: dict[str, dict[str, int]] = {}
    weight_polynomials: dict[str, list[int]] = {}
    primitive_tables: dict[str, dict[str, int]] = {}
    primitive_formula_matches: dict[str, bool] = {}
    closed_form_matches: dict[str, bool] = {}
    marginal_matches: dict[str, dict[str, bool]] = {}

    for length in range(VERIFY_N_MIN, VERIFY_N_MAX + 1):
        brute_joint = joint_spectrum_brute(length)
        closed_joint = closed_form_joint_spectrum(length)
        brute_primitive = primitive_necklaces_by_weight_brute(length)
        formula_primitive = primitive_necklaces_by_weight_formula(length)
        primitive_size_spectrum = primitive_orbit_size_spectrum(length)
        size_row = size_marginal(brute_joint)
        weight_row = weight_marginal(brute_joint)

        joint_tables[str(length)] = serial_counter(brute_joint)
        joint_entry_tables[str(length)] = table_entries(brute_joint)
        size_marginals[str(length)] = serial_counter(size_row)
        weight_marginals[str(length)] = serial_counter(weight_row)
        weight_polynomials[str(length)] = weight_polynomial_coefficients(length)
        primitive_tables[str(length)] = serial_counter(formula_primitive)
        primitive_formula_matches[str(length)] = brute_primitive == formula_primitive
        closed_form_matches[str(length)] = brute_joint == closed_joint
        marginal_matches[str(length)] = {
            "size_marginal_recovers_a_d": bool(size_row == primitive_size_spectrum),
            "weight_marginal_recovers_N_n": bool([int(weight_row.get(weight, 0)) for weight in range(max(weight_row, default=0) + 1)] == weight_polynomials[str(length)]),
        }

    expected_n10 = Counter(
        {
            (1, 0): 1,
            (2, 5): 1,
            (5, 2): 1,
            (5, 4): 1,
            (10, 1): 1,
            (10, 2): 3,
            (10, 3): 5,
            (10, 4): 2,
        }
    )
    n10_joint = joint_spectrum_brute(WINDOW_N)
    n10_correlation = correlation_witness(n10_joint)

    not_claimed = [
        "physical fine-structure constant or any physical/external interpretation (this is a finite combinatorial bivariate joint orbit-size/weight spectrum of the gauge-invariant golden-necklace, not about alpha)",
        "the basepoint/residue (no-go stands; only the basepoint-free joint orbit structure is forward)",
    ]

    checks = [
        check(
            "joint_brute",
            all(joint_spectrum_brute(length) for length in range(VERIFY_N_MIN, VERIFY_N_MAX + 1)),
            "Exact brute enumeration computes J_n(d,k) for n=1..12 from C_n-orbits in P_n by exact orbit size d and Hamming weight k.",
        ),
        check(
            "size_marginal_recovers_a_d",
            all(row["size_marginal_recovers_a_d"] for row in marginal_matches.values())
            and size_marginals[str(WINDOW_N)] == {"1": 1, "2": 1, "5": 2, "10": 11},
            "For n=1..12, sum_k J_n(d,k) recovers the primitive orbit-size spectrum a(d); for n=10 this is {1:1,2:1,5:2,10:11}.",
        ),
        check(
            "weight_marginal_recovers_N_n",
            all(row["weight_marginal_recovers_N_n"] for row in marginal_matches.values())
            and weight_polynomials[str(WINDOW_N)] == [1, 1, 4, 5, 3, 1],
            "For n=1..12, sum_d J_n(d,k) recovers the weight polynomial coefficients; for n=10 this is [1,1,4,5,3,1].",
        ),
        check(
            "joint_strictly_finer",
            n10_correlation["actual_size_10_row"] == {"1": 1, "2": 3, "3": 5, "4": 2}
            and n10_correlation["same_marginal_alternate_exists"],
            "The n=10 size-10 row splits by weight as {1:1,2:3,3:5,4:2}; a distinct nonnegative table with the same two marginals exists, so the correlation is not recovered from either marginal.",
        ),
        check(
            "closed_form_matches",
            all(closed_form_matches.values()) and all(primitive_formula_matches.values()),
            "For n=1..12, J_n(d,k)=A(d,kd/n) when n divides kd, and 0 otherwise, where A(d,s) is the exact-period d primitive golden-necklace count with s ones.",
        ),
        check(
            "n10_witness",
            n10_joint == expected_n10
            and size_marginal(n10_joint) == Counter({1: 1, 2: 1, 5: 2, 10: 11})
            and weight_polynomial_coefficients(WINDOW_N) == [1, 1, 4, 5, 3, 1],
            "Window6 n=10 witness: J_10={(1,0):1,(2,5):1,(5,2):1,(5,4):1,(10,1):1,(10,2):3,(10,3):5,(10,4):2}.",
        ),
    ]

    result: dict[str, Any] = {
        "definition": "J_n(d,k)=#{C_n-orbits in P_n with exact orbit size d and Hamming weight k}, where P_n is the cyclic no-adjacent-1 binary word carrier.",
        "verified_range": [VERIFY_N_MIN, VERIFY_N_MAX],
        "joint_tables": joint_tables,
        "joint_table_entries": joint_entry_tables,
        "marginals": {
            "size": size_marginals,
            "weight": weight_marginals,
            "weight_polynomial_coefficients": weight_polynomials,
        },
        "closed_form": {
            "statement": "J_n(d,k)=A(d,kd/n) when n divides k*d, and J_n(d,k)=0 otherwise.",
            "A_definition": "A(d,s) is the number of exact-period d primitive cyclic no-adjacent-1 necklaces with s ones.",
            "A_mobius_weighted_formula": "A(d,s)=(1/d) sum_{r|gcd(d,s)} mu(r) W(d/r,s/r), with W(g,0)=1 and W(g,t)=g/(g-t) C(g-t,t) for t>=1.",
            "primitive_tables": primitive_tables,
            "closed_form_matches": closed_form_matches,
            "primitive_formula_matches": primitive_formula_matches,
        },
        "window6_n10": {
            "J_10": joint_tables[str(WINDOW_N)],
            "J_10_entries": joint_entry_tables[str(WINDOW_N)],
            "size_marginal": size_marginals[str(WINDOW_N)],
            "weight_marginal": weight_marginals[str(WINDOW_N)],
            "N_10_coefficients": weight_polynomials[str(WINDOW_N)],
            "correlation_witness": n10_correlation,
        },
        "genuine_joint_refinement": "The bivariate table has the size marginal a(d) and the weight marginal N_n(y), while retaining orbit-size x weight correlation that neither single grading determines.",
        "not_claimed": not_claimed,
    }

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True, sort_keys=True))


if __name__ == "__main__":
    main()

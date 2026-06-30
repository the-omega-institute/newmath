#!/usr/bin/env python3
"""BC2 killed-walk spectrum structural comparison.

This experiment compares the bio codon-Q6 killed-walk operator with the
Window6 Fibonacci-cube killed-walk operator.  It is intentionally standalone:
no numpy, no sympy, and no dependency on the bio data snapshot.
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from fractions import Fraction
from typing import Iterable


EXPERIMENT_ID = "bc2_killed_walk_spectrum"
CLAIM_ID = "bridge.window6_codon_q6.killed_walk_spectral_correspondence"

BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
BITS_TO_BASE = {bits: base for base, bits in BASE_TO_BITS.items()}
REASSIGNMENT_CODONS = {
    "UGA",
    "UAG",
    "UAA",
    "AUA",
    "AGA",
    "AGG",
    "AAA",
    "CUG",
    "CUU",
    "CUC",
    "CUA",
    "UCA",
    "UUA",
}

BIO_TARGETS = {
    "lambda_M": 0.6752479308830213,
    "lambda_R": 0.4758352843197002,
    "mu": 3.051487585298128,
}
FLOAT_TOL = 1e-10


def emit(status: str, **kwargs: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kwargs)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_to_q6(codon: str) -> tuple[int, ...]:
    codon = codon.upper().replace("T", "U")
    if len(codon) != 3:
        raise ValueError(f"codon must have length 3: {codon!r}")
    bits: list[int] = []
    for base in codon:
        if base not in BASE_TO_BITS:
            raise ValueError(f"invalid RNA base in codon {codon!r}")
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def q6_to_codon(bits: tuple[int, ...]) -> str:
    if len(bits) != 6:
        raise ValueError(f"Q6 coordinate must have length 6: {bits!r}")
    codon = []
    for offset in range(0, 6, 2):
        pair = (int(bits[offset]), int(bits[offset + 1]))
        if pair not in BITS_TO_BASE:
            raise ValueError(f"invalid bit pair {pair!r} in {bits!r}")
        codon.append(BITS_TO_BASE[pair])
    return "".join(codon)


def bit_tuples(length: int) -> list[tuple[int, ...]]:
    return list(itertools.product((0, 1), repeat=length))


def median_closure(codons: set[str]) -> set[str]:
    points = {codon_to_q6(codon) for codon in codons}
    if not points:
        return set()
    unary = [{point[axis] for point in points} for axis in range(6)]
    binary = {
        (left, right): {(point[left], point[right]) for point in points}
        for left in range(6)
        for right in range(left + 1, 6)
    }
    closure = set()
    for bits in bit_tuples(6):
        if any(bits[axis] not in unary[axis] for axis in range(6)):
            continue
        if any((bits[left], bits[right]) not in allowed for (left, right), allowed in binary.items()):
            continue
        closure.add(q6_to_codon(bits))
    return closure


def fibonacci_cube(length: int) -> set[tuple[int, ...]]:
    return {
        word
        for word in bit_tuples(length)
        if all(not (word[index] == 1 and word[index + 1] == 1) for index in range(length - 1))
    }


def adjacency_matrix(points: Iterable[tuple[int, ...]]) -> list[list[int]]:
    ordered = sorted(points)
    if not ordered:
        return []
    dimension = len(ordered[0])
    index = {point: pos for pos, point in enumerate(ordered)}
    matrix = [[0 for _ in ordered] for _ in ordered]
    for row, point in enumerate(ordered):
        for axis in range(dimension):
            neighbor = list(point)
            neighbor[axis] = 1 - neighbor[axis]
            col = index.get(tuple(neighbor))
            if col is not None:
                matrix[row][col] = 1
    return matrix


def spectral_radius_adjacency(points: Iterable[tuple[int, ...]], iterations: int = 5000, tolerance: float = 1e-14) -> float:
    matrix = adjacency_matrix(points)
    n = len(matrix)
    if n == 0:
        return 0.0
    vector = [1.0 / n for _ in range(n)]
    previous = 0.0
    for _ in range(iterations):
        next_vector = [sum(matrix[row][col] * vector[col] for col in range(n)) for row in range(n)]
        norm = math.sqrt(sum(value * value for value in next_vector))
        if norm == 0.0:
            return 0.0
        next_vector = [value / norm for value in next_vector]
        numerator = 0.0
        for row in range(n):
            row_sum = sum(matrix[row][col] * next_vector[col] for col in range(n))
            numerator += next_vector[row] * row_sum
        if abs(numerator - previous) < tolerance:
            return numerator
        previous = numerator
        vector = next_vector
    return previous


def spectral_radius_killed_walk(codons: set[str]) -> float:
    return spectral_radius_adjacency(codon_to_q6(codon) for codon in codons) / 6.0


def radial_polynomial(mu: float) -> float:
    return mu**6 - 12.0 * mu**4 + 26.0 * mu**2 - 9.0


def matmul_fraction(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    rows = len(left)
    cols = len(right[0])
    inner = len(right)
    return [
        [sum(left[row][mid] * right[mid][col] for mid in range(inner)) for col in range(cols)]
        for row in range(rows)
    ]


def characteristic_polynomial_high(matrix: list[list[int]]) -> list[int]:
    """Return det(xI-A) as integer coefficients from high degree to constant."""
    n = len(matrix)
    if n == 0:
        return [1]
    a = [[Fraction(value) for value in row] for row in matrix]
    b = [[Fraction(1 if row == col else 0) for col in range(n)] for row in range(n)]
    coeffs: list[Fraction] = [Fraction(1)]
    for step in range(1, n + 1):
        ab = matmul_fraction(a, b)
        coeff = -sum(ab[index][index] for index in range(n)) / step
        coeffs.append(coeff)
        b = [[ab[row][col] + (coeff if row == col else 0) for col in range(n)] for row in range(n)]
    result: list[int] = []
    for coeff in coeffs:
        if coeff.denominator != 1:
            raise ArithmeticError(f"non-integral characteristic coefficient: {coeff}")
        result.append(int(coeff))
    return result


def high_to_low(coeffs: list[int | Fraction]) -> list[Fraction]:
    return [Fraction(coeff) for coeff in reversed(coeffs)]


def trim_low(poly: list[Fraction]) -> list[Fraction]:
    result = poly[:]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def divmod_low(numerator: list[Fraction], denominator: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    num = trim_low(numerator)
    den = trim_low(denominator)
    if den == [Fraction(0)]:
        raise ZeroDivisionError("polynomial division by zero")
    if len(num) < len(den):
        return [Fraction(0)], num
    quotient = [Fraction(0) for _ in range(len(num) - len(den) + 1)]
    remainder = num[:]
    while len(remainder) >= len(den) and remainder != [Fraction(0)]:
        degree = len(remainder) - len(den)
        scale = remainder[-1] / den[-1]
        quotient[degree] = scale
        for index, value in enumerate(den):
            remainder[index + degree] -= scale * value
        remainder = trim_low(remainder)
    return trim_low(quotient), trim_low(remainder)


def gcd_low(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    a = trim_low(left)
    b = trim_low(right)
    while b != [Fraction(0)]:
        _, remainder = divmod_low(a, b)
        a, b = b, remainder
    lead = a[-1]
    return [coeff / lead for coeff in a]


def polynomial_divides_high(poly_high: list[int], factor_high: list[int]) -> bool:
    _, remainder = divmod_low(high_to_low(poly_high), high_to_low(factor_high))
    return remainder == [Fraction(0)]


def gcd_degree_high(left_high: list[int], right_high: list[int]) -> int:
    gcd = gcd_low(high_to_low(left_high), high_to_low(right_high))
    return len(gcd) - 1


def apply_cube_automorphism(
    points: set[tuple[int, ...]], permutation: tuple[int, ...], flips: tuple[int, ...]
) -> set[tuple[int, ...]]:
    return {tuple(point[permutation[index]] ^ flips[index] for index in range(len(permutation))) for point in points}


def cube_automorphism_equal(left: set[tuple[int, ...]], right: set[tuple[int, ...]]) -> dict[str, object]:
    if not left or not right:
        return {"matched": left == right, "reason": "empty-set direct comparison"}
    if len(left) != len(right):
        return {"matched": False, "reason": "cardinality differs"}
    dimension = len(next(iter(left)))
    if any(len(point) != dimension for point in left | right):
        return {"matched": False, "reason": "dimension is not uniform"}
    if any(len(point) != dimension for point in right):
        return {"matched": False, "reason": "dimension differs"}
    for permutation in itertools.permutations(range(dimension)):
        for flips in itertools.product((0, 1), repeat=dimension):
            if apply_cube_automorphism(left, permutation, flips) == right:
                return {"matched": True, "permutation": permutation, "flips": flips}
    return {"matched": False, "reason": "no coordinate permutation/bit-flip maps the sets"}


def same_polynomial(left: list[int], right: list[int]) -> bool:
    return left == right


def format_poly_high(coeffs: list[int], variable: str = "x") -> str:
    if coeffs == [0]:
        return "0"
    terms = []
    degree = len(coeffs) - 1
    for index, coeff in enumerate(coeffs):
        if coeff == 0:
            continue
        power = degree - index
        abs_coeff = abs(coeff)
        if power == 0:
            body = str(abs_coeff)
        elif power == 1:
            body = variable if abs_coeff == 1 else f"{abs_coeff}*{variable}"
        else:
            body = f"{variable}^{power}" if abs_coeff == 1 else f"{abs_coeff}*{variable}^{power}"
        if not terms:
            terms.append(body if coeff > 0 else f"-{body}")
        else:
            terms.append((" + " if coeff > 0 else " - ") + body)
    return "".join(terms) if terms else "0"


def main() -> None:
    r_codons = set(REASSIGNMENT_CODONS)
    m_codons = median_closure(r_codons)
    r_points = {codon_to_q6(codon) for codon in r_codons}
    m_points = {codon_to_q6(codon) for codon in m_codons}
    gamma6 = fibonacci_cube(6)
    gamma5 = fibonacci_cube(5)

    rho_r = spectral_radius_adjacency(r_points)
    rho_m = spectral_radius_adjacency(m_points)
    rho_gamma6 = spectral_radius_adjacency(gamma6)
    rho_gamma5 = spectral_radius_adjacency(gamma5)
    lambda_r = rho_r / 6.0
    lambda_m = rho_m / 6.0
    lambda_gamma6 = rho_gamma6 / 6.0
    lambda_gamma5 = rho_gamma5 / 6.0
    mu = 6.0 * lambda_m - 1.0
    radial_value = radial_polynomial(mu)
    phi = (1.0 + math.sqrt(5.0)) / 2.0

    char_m = characteristic_polynomial_high(adjacency_matrix(m_points))
    char_r = characteristic_polynomial_high(adjacency_matrix(r_points))
    char_gamma6 = characteristic_polynomial_high(adjacency_matrix(gamma6))
    char_gamma5 = characteristic_polynomial_high(adjacency_matrix(gamma5))
    radial_mu_poly = [1, 0, -12, 0, 26, 0, -9]
    radial_shifted_for_adjacency = [1, -6, 3, 28, -31, -10, 6]

    automorphism_m_gamma6 = cube_automorphism_equal(m_points, gamma6)
    char_m_equals_gamma6 = same_polynomial(char_m, char_gamma6)
    char_r_equals_gamma5 = same_polynomial(char_r, char_gamma5)
    radial_divides_m = polynomial_divides_high(char_m, radial_shifted_for_adjacency)
    radial_divides_gamma6 = polynomial_divides_high(char_gamma6, radial_shifted_for_adjacency)
    radial_divides_gamma5 = polynomial_divides_high(char_gamma5, radial_shifted_for_adjacency)
    golden_char = [1, -1, -1]
    golden_divides_m = polynomial_divides_high(char_m, golden_char)
    golden_divides_r = polynomial_divides_high(char_r, golden_char)
    golden_divides_gamma6 = polynomial_divides_high(char_gamma6, golden_char)
    golden_divides_gamma5 = polynomial_divides_high(char_gamma5, golden_char)

    bio_self_checks = [
        abs(lambda_m - BIO_TARGETS["lambda_M"]) < FLOAT_TOL,
        abs(lambda_r - BIO_TARGETS["lambda_R"]) < FLOAT_TOL,
        abs(mu - BIO_TARGETS["mu"]) < FLOAT_TOL,
        abs(radial_value) < 1e-8,
        len(m_codons) == 20,
        len(r_codons) == 13,
    ]

    checks = [
        {
            "name": "bio_operator_self_check",
            "passed": all(bio_self_checks),
            "respects_structure_both_sides": False,
            "necessity_argument": True,
            "details": {
                "R_size": len(r_codons),
                "M_size": len(m_codons),
                "lambda_M": lambda_m,
                "lambda_R": lambda_r,
                "mu": mu,
                "radial_polynomial_value": radial_value,
                "expected": BIO_TARGETS,
            },
            "reason": "The vendored codon-Q6 median closure and induced-subgraph killed-walk operator reproduce the bio scalars.",
        },
        {
            "name": "window6_fibonacci_cube_operator",
            "passed": len(gamma6) == 21 and len(gamma5) == 13,
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "Gamma6_size": len(gamma6),
                "Gamma5_size": len(gamma5),
                "rho_A_Gamma6": rho_gamma6,
                "rho_A_Gamma5": rho_gamma5,
                "lambda_Gamma6_killed_by_6": lambda_gamma6,
                "lambda_Gamma5_killed_by_6": lambda_gamma5,
                "golden_perron_phi": phi,
                "golden_transfer_charpoly": "lambda^2-lambda-1",
            },
            "reason": "The Window side uses the same induced-hypercube adjacency form, with the codon normalization 1/6 for cross-side comparison.",
        },
        {
            "name": "M_equals_Gamma6_under_cube_automorphism",
            "passed": bool(automorphism_m_gamma6["matched"]),
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "M_size": len(m_points),
                "Gamma6_size": len(gamma6),
                "cube_automorphism_test": automorphism_m_gamma6,
            },
            "reason": "A 6-cube coordinate permutation/bit-flip preserves vertex cardinality, so 20 versus 21 already forbids equality.",
        },
        {
            "name": "M_and_Gamma6_same_adjacency_charpoly",
            "passed": char_m_equals_gamma6,
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "rho_A_M": rho_m,
                "rho_A_Gamma6": rho_gamma6,
                "lambda_M": lambda_m,
                "lambda_Gamma6_killed_by_6": lambda_gamma6,
                "charpoly_M": format_poly_high(char_m),
                "charpoly_Gamma6": format_poly_high(char_gamma6),
                "common_factor_degree": gcd_degree_high(char_m, char_gamma6),
            },
            "reason": "The exact adjacency characteristic polynomials are different; in particular their Perron roots are different.",
        },
        {
            "name": "R_and_Gamma5_same_adjacency_charpoly",
            "passed": char_r_equals_gamma5,
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "R_size": len(r_points),
                "Gamma5_size": len(gamma5),
                "rho_A_R": rho_r,
                "rho_A_Gamma5": rho_gamma5,
                "lambda_R": lambda_r,
                "lambda_Gamma5_killed_by_6": lambda_gamma5,
                "charpoly_R": format_poly_high(char_r),
                "charpoly_Gamma5": format_poly_high(char_gamma5),
                "common_factor_degree": gcd_degree_high(char_r, char_gamma5),
            },
            "reason": "Even where the vertex counts both equal 13, the exact adjacency characteristic polynomials differ.",
        },
        {
            "name": "bio_radial_cubic_relation_vs_window_graphs",
            "passed": radial_divides_gamma6 or radial_divides_gamma5,
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "radial_mu_polynomial": format_poly_high(radial_mu_poly, "mu"),
                "adjacency_shifted_factor": format_poly_high(radial_shifted_for_adjacency),
                "divides_charpoly_M": radial_divides_m,
                "divides_charpoly_Gamma6": radial_divides_gamma6,
                "divides_charpoly_Gamma5": radial_divides_gamma5,
                "gcd_degree_with_Gamma6": gcd_degree_high(char_gamma6, radial_shifted_for_adjacency),
                "gcd_degree_with_Gamma5": gcd_degree_high(char_gamma5, radial_shifted_for_adjacency),
            },
            "reason": "The bio radial cubic becomes a factor of charpoly(A_M) after the shift x=mu+1, but it is not a factor of the Window Gamma6 or Gamma5 adjacency characteristic polynomial.",
        },
        {
            "name": "golden_transfer_factor_relation",
            "passed": golden_divides_m or golden_divides_r,
            "respects_structure_both_sides": True,
            "necessity_argument": True,
            "details": {
                "golden_transfer_charpoly": format_poly_high(golden_char),
                "divides_charpoly_M": golden_divides_m,
                "divides_charpoly_R": golden_divides_r,
                "divides_charpoly_Gamma6": golden_divides_gamma6,
                "divides_charpoly_Gamma5": golden_divides_gamma5,
                "mu": mu,
                "lambda_M": lambda_m,
                "phi": phi,
                "numeric_gaps": {
                    "abs_mu_minus_phi_squared": abs(mu - phi**2),
                    "abs_mu_minus_phi_cubed_over_sqrt5": abs(mu - (phi**3 / math.sqrt(5.0))),
                    "abs_lambda_M_minus_phi_over_2": abs(lambda_m - phi / 2.0),
                },
            },
            "reason": "The golden transfer factor is present in Gamma5 but not in the bio M or R adjacency spectra; nearby decimal expressions are not structural identities.",
        },
    ]

    if not all(bio_self_checks):
        emit(
            "needs_derivation",
            checks=checks,
            note="The vendored bio killed-walk implementation did not reproduce the reference scalars, so the structural comparison is not trustworthy.",
        )

    structural_forcing = (
        bool(automorphism_m_gamma6["matched"])
        and char_m_equals_gamma6
        and (radial_divides_gamma6 or radial_divides_gamma5)
        and (golden_divides_m or golden_divides_r)
    )
    if structural_forcing:
        emit(
            "certified",
            checks=checks,
            note="The bio and Window killed-walk spectra are structurally forced by the same induced graph data.",
        )

    emit(
        "refuted",
        checks=checks,
        results={
            "bio": {
                "R_codons": sorted(r_codons),
                "M_codons": sorted(m_codons),
                "rho_A_R": rho_r,
                "rho_A_M": rho_m,
                "lambda_R": lambda_r,
                "lambda_M": lambda_m,
                "mu": mu,
                "radial_polynomial_value": radial_value,
            },
            "window": {
                "Gamma6_size": len(gamma6),
                "Gamma5_size": len(gamma5),
                "rho_A_Gamma6": rho_gamma6,
                "rho_A_Gamma5": rho_gamma5,
                "lambda_Gamma6_killed_by_6": lambda_gamma6,
                "lambda_Gamma5_killed_by_6": lambda_gamma5,
                "golden_perron_phi": phi,
            },
        },
        note=(
            "BC2-R1 is refuted: the operators have the same induced-subgraph killed-walk form, "
            "but the bio sets and Window Fibonacci cubes are not the same cube-embedded graph, "
            "their exact adjacency characteristic polynomials differ, and the bio radial factor "
            "does not occur in the Window graph spectra."
        ),
    )


if __name__ == "__main__":
    main()

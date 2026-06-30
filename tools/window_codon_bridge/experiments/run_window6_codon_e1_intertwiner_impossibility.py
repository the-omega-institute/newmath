#!/usr/bin/env python3
"""Window6-to-codon adjacency-intertwiner impossibility certificate.

The certificate is standalone and exact for the discrete decision.  It builds
the length-6 Fibonacci cube and the H(3,4) codon Hamming graph, computes the
Window6 characteristic polynomial over the integers, and checks that it is
coprime to the codon graph characteristic polynomial.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
import json
import math
import sys


EXPERIMENT_ID = "window6_codon_e1_intertwiner_impossibility"
CLAIM_ID = "bridge.window6_codon_q6.intertwiner_impossibility"
BASES = ("U", "C", "A", "G")
H34_EIGENVALUES = (9, 5, 1, -3)
H34_EIGENSPACE_DIMS = (1, 9, 27, 27)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "refuted") else 3)


def fail(reason: str, checks: list[str] | None = None, **fields: object) -> None:
    emit("failed", checks=checks or [], reason=reason, **fields)


def no_adjacent_ones(word: tuple[int, ...]) -> bool:
    return all(not (word[index] == 1 and word[index + 1] == 1) for index in range(len(word) - 1))


def hamming_distance(left: tuple[object, ...] | str, right: tuple[object, ...] | str) -> int:
    return sum(1 for a, b in zip(left, right) if a != b)


def adjacency_matrix(vertices: list[tuple[object, ...] | str]) -> list[list[int]]:
    n = len(vertices)
    matrix = [[0 for _ in range(n)] for _ in range(n)]
    for left, right in combinations(range(n), 2):
        if hamming_distance(vertices[left], vertices[right]) == 1:
            matrix[left][right] = 1
            matrix[right][left] = 1
    return matrix


def edge_count(matrix: list[list[int]]) -> int:
    return sum(sum(row) for row in matrix) // 2


def degree_sequence(matrix: list[list[int]]) -> list[int]:
    return [sum(row) for row in matrix]


def identity_fraction(n: int) -> list[list[Fraction]]:
    return [[Fraction(1 if row == col else 0) for col in range(n)] for row in range(n)]


def matmul_fraction(left: list[list[Fraction]], right: list[list[Fraction]]) -> list[list[Fraction]]:
    rows = len(left)
    cols = len(right[0])
    inner = len(right)
    return [
        [sum(left[row][mid] * right[mid][col] for mid in range(inner)) for col in range(cols)]
        for row in range(rows)
    ]


def characteristic_polynomial_high(matrix: list[list[int]]) -> list[int]:
    """Return det(xI - A), with coefficients from highest degree to constant."""
    n = len(matrix)
    if n == 0:
        return [1]
    a = [[Fraction(value) for value in row] for row in matrix]
    b = identity_fraction(n)
    coeffs: list[Fraction] = [Fraction(1)]
    for step in range(1, n + 1):
        ab = matmul_fraction(a, b)
        coeff = -sum(ab[index][index] for index in range(n)) / step
        coeffs.append(coeff)
        if step < n:
            b = [
                [
                    ab[row][col] + (coeff if row == col else Fraction(0))
                    for col in range(n)
                ]
                for row in range(n)
            ]
    if any(coeff.denominator != 1 for coeff in coeffs):
        raise AssertionError(f"non-integral characteristic coefficient: {coeffs}")
    return [int(coeff) for coeff in coeffs]


def poly_eval_high(coeffs: list[int], value: int) -> int:
    result = 0
    for coeff in coeffs:
        result = result * value + coeff
    return result


def poly_mul_high(left: list[int], right: list[int]) -> list[int]:
    result = [0 for _ in range(len(left) + len(right) - 1)]
    for i, left_coeff in enumerate(left):
        for j, right_coeff in enumerate(right):
            result[i + j] += left_coeff * right_coeff
    return result


def poly_pow_linear_high(root: int, exponent: int) -> list[int]:
    result = [1]
    factor = [1, -root]
    for _ in range(exponent):
        result = poly_mul_high(result, factor)
    return result


def h34_charpoly_high() -> list[int]:
    coeffs = [1]
    for root, multiplicity in zip(H34_EIGENVALUES, H34_EIGENSPACE_DIMS):
        coeffs = poly_mul_high(coeffs, poly_pow_linear_high(root, multiplicity))
    return coeffs


def trim_low(poly: list[Fraction]) -> list[Fraction]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_divmod_low(numerator: list[Fraction], denominator: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    numerator = trim_low(numerator[:])
    denominator = trim_low(denominator[:])
    if denominator == [0]:
        raise ZeroDivisionError("polynomial division by zero")
    if len(numerator) < len(denominator):
        return [Fraction(0)], numerator
    quotient = [Fraction(0) for _ in range(len(numerator) - len(denominator) + 1)]
    remainder = numerator[:]
    divisor_lead = denominator[-1]
    while len(remainder) >= len(denominator) and remainder != [0]:
        scale_degree = len(remainder) - len(denominator)
        scale = remainder[-1] / divisor_lead
        quotient[scale_degree] = scale
        for index, coeff in enumerate(denominator):
            remainder[index + scale_degree] -= scale * coeff
        trim_low(remainder)
    return trim_low(quotient), trim_low(remainder)


def poly_gcd_low(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    left = trim_low(left[:])
    right = trim_low(right[:])
    while right != [0]:
        _quotient, remainder = poly_divmod_low(left, right)
        left, right = right, remainder
    lead = left[-1]
    if lead == 0:
        return [Fraction(0)]
    return [coeff / lead for coeff in left]


def rational_rank(matrix: list[list[int]]) -> int:
    rows = [[Fraction(value) for value in row] for row in matrix]
    if not rows:
        return 0
    row_count = len(rows)
    col_count = len(rows[0])
    rank = 0
    for col in range(col_count):
        pivot = None
        for row in range(rank, row_count):
            if rows[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_value = rows[rank][col]
        rows[rank] = [value / pivot_value for value in rows[rank]]
        for row in range(row_count):
            if row == rank or rows[row][col] == 0:
                continue
            factor = rows[row][col]
            rows[row] = [
                rows[row][entry] - factor * rows[rank][entry]
                for entry in range(col_count)
            ]
        rank += 1
        if rank == row_count:
            break
    return rank


def shifted_matrix(matrix: list[list[int]], eigenvalue: int) -> list[list[int]]:
    return [
        [
            matrix[row][col] - (eigenvalue if row == col else 0)
            for col in range(len(matrix))
        ]
        for row in range(len(matrix))
    ]


def spectral_radius(matrix: list[list[int]], iterations: int = 10000, tolerance: float = 1e-14) -> float:
    n = len(matrix)
    if n == 0:
        return 0.0
    vector = [1.0 / math.sqrt(n) for _ in range(n)]
    previous = 0.0
    for _ in range(iterations):
        next_vector = [
            sum(matrix[row][col] * vector[col] for col in range(n))
            for row in range(n)
        ]
        norm = math.sqrt(sum(value * value for value in next_vector))
        if norm == 0.0:
            return 0.0
        next_vector = [value / norm for value in next_vector]
        rayleigh = sum(
            next_vector[row]
            * sum(matrix[row][col] * next_vector[col] for col in range(n))
            for row in range(n)
        )
        if abs(rayleigh - previous) < tolerance:
            return rayleigh
        previous = rayleigh
        vector = next_vector
    return previous


def build_gamma6() -> tuple[list[tuple[int, ...]], list[list[int]]]:
    vertices = [
        tuple(word)
        for word in product((0, 1), repeat=6)
        if no_adjacent_ones(tuple(word))
    ]
    vertices.sort()
    return vertices, adjacency_matrix(vertices)


def build_h34() -> tuple[list[str], list[list[int]]]:
    codons = ["".join(chars) for chars in product(BASES, repeat=3)]
    return codons, adjacency_matrix(codons)


def assert_or_fail(condition: bool, name: str, checks: list[str], reason: str) -> None:
    if condition:
        checks.append(name)
        return
    fail(reason, checks=checks)


def main() -> None:
    checks: list[str] = []
    try:
        gamma_vertices, gamma_matrix = build_gamma6()
        h34_codons, h34_matrix = build_h34()

        gamma_edges = edge_count(gamma_matrix)
        h34_edges = edge_count(h34_matrix)
        h34_degrees = degree_sequence(h34_matrix)

        assert_or_fail(len(gamma_vertices) == 21, "gamma6_vertex_count_21", checks, "Gamma6 vertex count is not 21.")
        assert_or_fail(gamma_edges == 38, "gamma6_edge_count_38", checks, "Gamma6 edge count is not 38.")
        assert_or_fail(len(h34_codons) == 64, "h34_vertex_count_64", checks, "H(3,4) vertex count is not 64.")
        assert_or_fail(h34_edges == 288, "h34_edge_count_288", checks, "H(3,4) edge count is not 288.")
        assert_or_fail(all(degree == 9 for degree in h34_degrees), "h34_degree_9_regular", checks, "H(3,4) is not 9-regular.")

        observed_dims = []
        for eigenvalue in H34_EIGENVALUES:
            rank = rational_rank(shifted_matrix(h34_matrix, eigenvalue))
            observed_dims.append(len(h34_matrix) - rank)
        assert_or_fail(
            tuple(observed_dims) == H34_EIGENSPACE_DIMS,
            "h34_exact_eigenspace_dimensions_1_9_27_27",
            checks,
            f"H(3,4) eigenspace dimensions are {observed_dims}, not {list(H34_EIGENSPACE_DIMS)}.",
        )

        gamma_charpoly = characteristic_polynomial_high(gamma_matrix)
        checks.append("gamma6_integer_charpoly")

        values_at_h_eigenvalues = {
            str(eigenvalue): poly_eval_high(gamma_charpoly, eigenvalue)
            for eigenvalue in H34_EIGENVALUES
        }
        no_shared_root = all(value != 0 for value in values_at_h_eigenvalues.values())
        checks.append("gamma6_charpoly_evaluated_at_all_h34_eigenvalues")

        h34_charpoly = h34_charpoly_high()
        gcd_poly = poly_gcd_low(
            [Fraction(coeff) for coeff in reversed(gamma_charpoly)],
            [Fraction(coeff) for coeff in reversed(h34_charpoly)],
        )
        poly_gcd_is_constant = len(gcd_poly) == 1 and gcd_poly[0] != 0
        if poly_gcd_is_constant:
            checks.append("charpoly_gcd_constant")

        shared_eigenvalue = None
        for key, value in values_at_h_eigenvalues.items():
            if value == 0:
                shared_eigenvalue = int(key)
                break

        gcd_summary = "constant 1" if poly_gcd_is_constant else f"degree {len(gcd_poly) - 1}"
        checked_eigenvalues = list(H34_EIGENVALUES)
        if no_shared_root and poly_gcd_is_constant:
            status = "certified"
            reason = (
                "For real square matrices A and B, the Sylvester intertwiner equation "
                "A_H J = J A_Gamma has a nonzero solution exactly when A_H and "
                "A_Gamma share an eigenvalue, equivalently when their characteristic "
                "polynomials have a nonconstant gcd over Q.  The H(3,4) eigenvalues "
                f"checked exactly were {checked_eigenvalues}; charpoly_Gamma6(lambda) "
                "is nonzero at each of them, and gcd(charpoly_H34, charpoly_Gamma6) "
                f"is {gcd_summary}.  This certifies only a negative closure: no "
                "nonzero adjacency-intertwiner maps Window6 Gamma6 into H(3,4), so "
                "codon E1 and every codon eigenspace are not Window6 adjacency-spectral "
                "images or quotients.  It does not assert any positive Window6-codon "
                "relation."
            )
        elif shared_eigenvalue is not None:
            status = "refuted"
            reason = (
                "The shared-eigenvalue criterion for A_H J = J A_Gamma found a shared "
                f"eigenvalue {shared_eigenvalue} among {checked_eigenvalues}; "
                f"gcd(charpoly_H34, charpoly_Gamma6) is {gcd_summary}.  A nonzero "
                "intertwiner can exist on that eigenspace.  This is not a positive "
                "Window6-codon relation by itself; it only refutes the proposed "
                "negative closure."
            )
        else:
            status = "failed"
            reason = (
                "The root-evaluation and polynomial-gcd cross-checks disagree for "
                "the shared-eigenvalue criterion; no certificate is emitted."
            )

        emit(
            status,
            gamma6_vertices=len(gamma_vertices),
            gamma6_edges=gamma_edges,
            h34_edges=h34_edges,
            h34_eigenspace_dims=observed_dims,
            h34_eigenvalues=list(H34_EIGENVALUES),
            gamma6_charpoly_coeffs=gamma_charpoly,
            charpoly_gamma6_at_H_eigenvalues=values_at_h_eigenvalues,
            poly_gcd_is_constant=poly_gcd_is_constant,
            gamma6_spectral_radius=round(spectral_radius(gamma_matrix), 12),
            shared_eigenvalue=shared_eigenvalue,
            checks=checks,
            reason=reason,
        )
    except Exception as exc:  # pragma: no cover - terminal certificate guard.
        fail(f"assertion or runtime failure: {exc}", checks=checks)


if __name__ == "__main__":
    main()

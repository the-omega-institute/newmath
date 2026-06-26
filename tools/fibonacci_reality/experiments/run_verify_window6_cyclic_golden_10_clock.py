#!/usr/bin/env python3
"""Exact audit for the cyclic golden period-10 clock boundary.

The audit separates a forward-local Phi_10 construction from the Window6
coupling obligation. Period-10 cyclic golden words carry a C_10 shift
representation with Phi_10 in its characteristic polynomial, while standard
golden transfer presentations and tensor powers have no Phi_10 factor. The
Window6 residual-to-clock coupling map is recorded as a needs-external
ClockCouplingCert obligation.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter
from typing import Any

import sympy as sp


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def words_no_adjacent(length: int, *, cyclic: bool) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=length):
        linear_ok = all(not (bits[index] == bits[index + 1] == 1) for index in range(length - 1))
        cyclic_ok = not cyclic or not (bits[-1] == bits[0] == 1)
        if linear_ok and cyclic_ok:
            words.append(bits)
    return words


def rotate_left(word: tuple[int, ...]) -> tuple[int, ...]:
    return word[1:] + word[:1]


def cycle_lengths(words: list[tuple[int, ...]]) -> Counter[int]:
    word_set = set(words)
    seen: set[tuple[int, ...]] = set()
    lengths: Counter[int] = Counter()
    for word in words:
        if word in seen:
            continue
        orbit: list[tuple[int, ...]] = []
        current = word
        while current not in orbit:
            if current not in word_set:
                raise ValueError("cyclic shift left the period word set")
            orbit.append(current)
            seen.add(current)
            current = rotate_left(current)
        lengths[len(orbit)] += 1
    return lengths


def phi_multiplicity(poly: sp.Poly, factor: sp.Poly, x: sp.Symbol) -> int:
    multiplicity = 0
    current = poly
    while True:
        quotient, remainder = sp.div(current, factor, domain=sp.QQ)
        if remainder.as_expr() != 0:
            return multiplicity
        multiplicity += 1
        current = sp.Poly(quotient.as_expr(), x)


def higher_block_matrix(length: int) -> tuple[list[tuple[int, ...]], sp.Matrix]:
    words = words_no_adjacent(length, cyclic=False)
    index = {word: position for position, word in enumerate(words)}
    matrix = sp.zeros(len(words))
    for word in words:
        source = index[word]
        for bit in (0, 1):
            target_word = word[1:] + (bit,)
            if target_word in index:
                matrix[index[target_word], source] = 1
    return words, matrix


def kronecker_power(matrix: sp.Matrix, power: int) -> sp.Matrix:
    result = matrix
    for _ in range(power - 1):
        result = sp.kronecker_product(result, matrix)
    return result


def main() -> None:
    x = sp.symbols("x")
    phi10_expr = sp.cyclotomic_poly(10, x)
    phi10 = sp.Poly(phi10_expr, x)
    lucas_10 = 123

    p10 = words_no_adjacent(10, cyclic=True)
    cycle_structure = cycle_lengths(p10)
    expected_cycle_structure = Counter({10: 11, 5: 2, 2: 1, 1: 1})
    full_charpoly = sp.Poly(
        sp.prod((x**length - 1) ** count for length, count in sorted(cycle_structure.items())),
        x,
    )
    full_phi10_multiplicity = phi_multiplicity(full_charpoly, phi10, x)

    minimal_word = tuple(int(char) for char in "0000000001")
    minimal_orbit: list[tuple[int, ...]] = []
    current = minimal_word
    while current not in minimal_orbit:
        minimal_orbit.append(current)
        current = rotate_left(current)
    shift_matrix = sp.zeros(10)
    for column in range(10):
        shift_matrix[(column + 1) % 10, column] = 1
    basis = sp.eye(10)
    v = basis[:, 0]
    ell = basis[7, :]
    indicator_sequence = [int((ell * (shift_matrix**exponent) * v)[0]) for exponent in range(40)]
    indicator_ok = all(
        value == (1 if exponent % 10 == 7 else 0)
        for exponent, value in enumerate(indicator_sequence)
    )

    higher_block_results: dict[str, Any] = {}
    higher_block_all_ok = True
    for length in range(2, 8):
        words, matrix = higher_block_matrix(length)
        charpoly_expr = sp.factor(matrix.charpoly(x).as_expr())
        expected_expr = sp.factor(x ** (len(words) - 2) * (x**2 - x - 1))
        _, phi_remainder = sp.div(sp.Poly(charpoly_expr, x), phi10, domain=sp.QQ)
        matches_standard_form = sp.expand(charpoly_expr - expected_expr) == 0
        phi10_divides = phi_remainder.as_expr() == 0
        higher_block_all_ok = higher_block_all_ok and matches_standard_form and not phi10_divides
        higher_block_results[str(length)] = {
            "word_count": len(words),
            "charpoly": str(charpoly_expr),
            "expected_form": f"x^{len(words)-2}*(x^2-x-1)",
            "matches_expected_form": bool(matches_standard_form),
            "phi10_divides": bool(phi10_divides),
            "nonzero_spectrum": ["phi", "-phi^{-1}"],
        }

    transfer_matrix = sp.Matrix([[1, 1], [1, 0]])
    tensor_results: dict[str, Any] = {}
    tensor_all_ok = True
    for power in (2, 3):
        tensor = kronecker_power(transfer_matrix, power)
        charpoly_expr = sp.factor(tensor.charpoly(x).as_expr())
        _, phi_remainder = sp.div(sp.Poly(charpoly_expr, x), phi10, domain=sp.QQ)
        eigenvals = tensor.eigenvals()
        phi10_divides = phi_remainder.as_expr() == 0
        all_real = all(sp.im(eigenvalue) == 0 for eigenvalue in eigenvals)
        tensor_all_ok = tensor_all_ok and all_real and not phi10_divides
        tensor_results[str(power)] = {
            "charpoly": str(charpoly_expr),
            "eigenvalues_with_multiplicity": {str(key): int(value) for key, value in eigenvals.items()},
            "all_real_spectrum": bool(all_real),
            "phi10_divides": bool(phi10_divides),
            "spectrum_form": "nonzero eigenvalues are products of phi and -phi^{-1}, hence real signed phi-powers",
        }

    not_claimed = [
        "physical fine-structure constant identification R_6(D*)=alpha^-1",
        "the Window6-residual-to-C10-clock coupling map iota (ClockCouplingCert placing q_0,q_1,q_2 at 7,17,27) as Window6-internally forced",
        "D*_6 as a Window6-internal theorem (it remains needs-external / clock-gated)",
    ]

    checks = [
        check(
            "P10_cyclic_enumeration",
            len(p10) == lucas_10,
            "The period-10 cyclic golden word set has |P_10|=123=L_10 by exhaustive cyclic no-adjacent-11 enumeration.",
        ),
        check(
            "P10_shift_cycle_structure",
            cycle_structure == expected_cycle_structure,
            "The cyclic left shift on P_10 has cycle-length multiset {10:11, 5:2, 2:1, 1:1}.",
        ),
        check(
            "P10_shift_charpoly_phi10",
            full_phi10_multiplicity == 11,
            "The full permutation characteristic polynomial is (x^10-1)^11 (x^5-1)^2 (x^2-1)(x-1), so Phi_10 occurs with multiplicity 11.",
        ),
        check(
            "S10_minimal_orbit_indicator",
            len(minimal_orbit) == 10
            and all(word in p10 for word in minimal_orbit)
            and sp.factor(shift_matrix.charpoly(x).as_expr()) == sp.factor(x**10 - 1)
            and indicator_ok,
            "The orbit of 0000000001 has length 10, its shift matrix has characteristic polynomial x^10-1, and e_7^T S_10^e e_0 equals 1 exactly when e == 7 mod 10 for e<40.",
        ),
        check(
            "higher_block_no_phi10",
            higher_block_all_ok,
            "For m=2..7, the standard m-block golden presentation has characteristic polynomial x^{|X_m|-2}(x^2-x-1), hence no Phi_10 factor.",
        ),
        check(
            "tensor_powers_no_phi10",
            tensor_all_ok,
            "For M^tensor k with k=2,3, the spectrum is real signed products of phi and -phi^{-1}; Phi_10 divides no tensor-power characteristic polynomial checked here.",
        ),
        check(
            "ClockCouplingCert_needs_external",
            True,
            "The remaining obligation is the external coupling map iota: Window6 residual events -> Z/10Z placing q_0,q_1,q_2 at 7,17,27 and mapping local returns by +10; it is not forced by the pure transfer/tensor golden checks.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "P10_size": len(p10),
        "Lucas_L10": lucas_10,
        "cycle_structure": {str(length): int(count) for length, count in sorted(cycle_structure.items())},
        "full_charpoly_factored": "(x^10-1)^11*(x^5-1)^2*(x^2-1)*(x-1)",
        "full_charpoly_cyclotomic_factored": str(sp.factor(full_charpoly.as_expr())),
        "phi10": str(phi10_expr),
        "phi10_divides": bool(full_phi10_multiplicity > 0),
        "phi10_multiplicity": full_phi10_multiplicity,
        "min_orbit_S10_indicator": {
            "word": "0000000001",
            "orbit_size": len(minimal_orbit),
            "shift_charpoly": str(sp.factor(shift_matrix.charpoly(x).as_expr())),
            "indicator": "e_7^T S_10^e e_0 = 1 iff e == 7 mod 10",
            "sequence_e_0_to_39": indicator_sequence,
        },
        "higher_block_charpoly_form": "for m=2..7, charpoly(B_m)=x^{|X_m|-2}(x^2-x-1)",
        "higher_block_results": higher_block_results,
        "tensor_real_spectrum": tensor_results,
        "verdict": {
            "phi10_forward_local": "Phi_10 is forward-constructible in the C_10 cyclic-shift representation of the golden-mean period-10 points P_10.",
            "pure_transfer_tensor_boundary": "Every checked standard m-block golden presentation and tensor-power golden transfer has no Phi_10 factor.",
            "ClockCouplingCert": "needs-external: iota from Window6 residual events to Z/10Z is not Window6-internally forced by these data.",
            "Dstar6_status": "needs-external / clock-gated",
        },
        "not_claimed": not_claimed,
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

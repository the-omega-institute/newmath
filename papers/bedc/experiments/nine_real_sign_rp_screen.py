#!/usr/bin/env python3
from __future__ import annotations

import json
from fractions import Fraction
from itertools import combinations
from typing import Iterable


N = 9
Support = frozenset[int]
Word = tuple[int, ...]
WINDOW_L3: tuple[Support, ...] = (
    frozenset(),
    frozenset({1, 2}),
    frozenset({1, 3}),
    frozenset({2, 3}),
)

EXPECTED_CERTIFICATES = {
    (0, 1, 2): ("det", (0, 1), Fraction(-4, 25)),
    (0, 2, 4): ("diag", (3,), Fraction(-3, 5)),
    (0, 4, 5): ("diag", (1,), Fraction(-7, 45)),
    (0, 4, 8): ("diag", (1,), Fraction(-5, 9)),
    (1, 3, 5): ("det", (0, 1), Fraction(-5, 36)),
    (1, 4, 7): ("det", (0, 1), Fraction(-1, 4)),
    (2, 3, 4): ("det", (0, 1), Fraction(-5, 36)),
    (2, 4, 6): ("diag", (2,), Fraction(-1, 9)),
    (3, 4, 5): ("det", (0, 1), Fraction(-1, 4)),
    (3, 4, 8): ("diag", (1,), Fraction(-7, 45)),
    (3, 5, 7): ("det", (0, 1), Fraction(-5, 36)),
    (4, 5, 6): ("det", (0, 1), Fraction(-5, 36)),
    (4, 6, 8): ("diag", (3,), Fraction(-3, 5)),
    (6, 7, 8): ("det", (0, 1), Fraction(-4, 25)),
}


def normalize(support: Iterable[int]) -> Support:
    values = frozenset(support)
    if not values:
        return frozenset()
    offset = min(values)
    return frozenset(value - offset for value in values)


def symmetric_difference(left: Support, right: Support) -> Support:
    return frozenset(set(left) ^ set(right))


def reflect(support: Support) -> Support:
    return frozenset(1 - site for site in support)


def word_from_negatives(negative_sites: tuple[int, int, int]) -> Word:
    negative_set = set(negative_sites)
    return tuple(-1 if site in negative_set else 1 for site in range(N))


def branch(word: Word, support: Support, residue: int) -> tuple[int, Support]:
    coefficient = 1
    carry_parity: dict[int, int] = {}
    for site in support:
        quotient, child = divmod(residue + site, N)
        coefficient *= word[child]
        carry_parity[quotient] = carry_parity.get(quotient, 0) ^ 1
    return coefficient, normalize(site for site, parity in carry_parity.items() if parity)


def carry_closure(word: Word, initial_supports: Iterable[Support]) -> list[Support]:
    seen: set[Support] = {frozenset()}
    queue: list[Support] = []
    for support in initial_supports:
        normalized = normalize(support)
        if normalized not in seen:
            seen.add(normalized)
            queue.append(normalized)

    for support in queue:
        for residue in range(N):
            _coefficient, next_support = branch(word, support, residue)
            if next_support not in seen:
                seen.add(next_support)
                queue.append(next_support)

    return sorted(
        (support for support in seen if support),
        key=lambda support: (max(support) - min(support), len(support), tuple(sorted(support))),
    )


def solve_linear_system(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    row_count = len(matrix)
    augmented = [row[:] + [vector[index]] for index, row in enumerate(matrix)]
    pivot_row = 0

    for column in range(row_count):
        pivot = None
        for row in range(pivot_row, row_count):
            if augmented[row][column] != 0:
                pivot = row
                break
        if pivot is None:
            continue

        augmented[pivot_row], augmented[pivot] = augmented[pivot], augmented[pivot_row]
        pivot_value = augmented[pivot_row][column]
        augmented[pivot_row] = [entry / pivot_value for entry in augmented[pivot_row]]

        for row in range(row_count):
            if row == pivot_row or augmented[row][column] == 0:
                continue
            factor = augmented[row][column]
            augmented[row] = [
                augmented[row][entry] - factor * augmented[pivot_row][entry]
                for entry in range(row_count + 1)
            ]

        pivot_row += 1

    if pivot_row != row_count:
        raise RuntimeError("carry recursion produced a singular linear system")

    return [augmented[row][row_count] for row in range(row_count)]


def solve_correlations(word: Word, initial_supports: Iterable[Support]) -> dict[Support, Fraction]:
    states = carry_closure(word, initial_supports)
    index = {support: offset for offset, support in enumerate(states)}
    size = len(states)
    matrix = [[Fraction(int(row == column), 1) for column in range(size)] for row in range(size)]
    vector = [Fraction(0, 1) for _ in range(size)]

    for support, row in index.items():
        for residue in range(N):
            coefficient, next_support = branch(word, support, residue)
            contribution = Fraction(coefficient, N)
            if next_support:
                matrix[row][index[next_support]] -= contribution
            else:
                vector[row] += contribution

    solution = solve_linear_system(matrix, vector)
    correlations = {support: solution[index[support]] for support in states}
    correlations[frozenset()] = Fraction(1, 1)
    return correlations


def gamma(correlations: dict[Support, Fraction], support: Iterable[int]) -> Fraction:
    return correlations[normalize(support)]


def l2_screen(word: Word) -> tuple[bool, Fraction, Fraction]:
    correlations = solve_correlations(
        word,
        (frozenset({0, 1}), frozenset({0, 1, 2, 3})),
    )
    mu = gamma(correlations, frozenset({0, 1}))
    diagonal = gamma(correlations, frozenset({0, 1, 2, 3}))
    return diagonal >= 0 and diagonal - mu * mu >= 0, mu, diagonal


def l3_entry_support(row_support: Support, column_support: Support) -> Support:
    return normalize(symmetric_difference(reflect(row_support), column_support))


def l3_matrix(word: Word) -> list[list[Fraction]]:
    initial_supports = [
        l3_entry_support(row_support, column_support)
        for row_support in WINDOW_L3
        for column_support in WINDOW_L3
    ]
    correlations = solve_correlations(word, initial_supports)
    return [
        [
            gamma(correlations, l3_entry_support(row_support, column_support))
            for column_support in WINDOW_L3
        ]
        for row_support in WINDOW_L3
    ]


def determinant(matrix: list[list[Fraction]]) -> Fraction:
    size = len(matrix)
    work = [row[:] for row in matrix]
    sign = Fraction(1, 1)
    result = Fraction(1, 1)

    for column in range(size):
        pivot = None
        for row in range(column, size):
            if work[row][column] != 0:
                pivot = row
                break
        if pivot is None:
            return Fraction(0, 1)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            sign *= -1
        pivot_value = work[column][column]
        result *= pivot_value
        for row in range(column + 1, size):
            if work[row][column] == 0:
                continue
            factor = work[row][column] / pivot_value
            for entry in range(column, size):
                work[row][entry] -= factor * work[column][entry]

    return sign * result


def principal_minor(matrix: list[list[Fraction]], indices: tuple[int, ...]) -> Fraction:
    return determinant([[matrix[row][column] for column in indices] for row in indices])


def is_symmetric(matrix: list[list[Fraction]]) -> bool:
    return all(matrix[row][column] == matrix[column][row] for row in range(4) for column in range(4))


def is_positive_semidefinite(matrix: list[list[Fraction]]) -> bool:
    for size in range(1, 5):
        for indices in combinations(range(4), size):
            if principal_minor(matrix, indices) < 0:
                return False
    return True


def failure_certificate(matrix: list[list[Fraction]]) -> tuple[str, tuple[int, ...], Fraction] | None:
    for index in range(4):
        if matrix[index][index] < 0:
            return "diag", (index,), matrix[index][index]

    for left, right in combinations(range(4), 2):
        minor = principal_minor(matrix, (left, right))
        if minor < 0:
            return "det", (left, right), minor

    for size in (3, 4):
        for indices in combinations(range(4), size):
            minor = principal_minor(matrix, indices)
            if minor < 0:
                return "det", indices, minor

    return None


def fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> int:
    total = 0
    l2_pass = 0
    l3_symmetric = 0
    l3_psd_pass = 0
    example: dict[str, str] | None = None
    certificates: dict[tuple[int, int, int], tuple[str, tuple[int, ...], Fraction]] = {}

    for negative_sites in combinations(range(N), 3):
        word = word_from_negatives(negative_sites)
        total += 1

        l2_ok, mu, diagonal = l2_screen(word)
        if l2_ok:
            l2_pass += 1
        if negative_sites == (0, 1, 3):
            example = {
                "negative_sites": str(negative_sites),
                "mu": fraction_text(mu),
                "D12": fraction_text(diagonal),
                "deficit": fraction_text(diagonal - mu * mu),
            }

        matrix = l3_matrix(word)
        if not is_symmetric(matrix):
            continue

        l3_symmetric += 1
        if is_positive_semidefinite(matrix):
            l3_psd_pass += 1
        certificate = failure_certificate(matrix)
        if certificate is None:
            raise AssertionError(f"missing PSD-failure certificate for {negative_sites}")
        certificates[negative_sites] = certificate

    expected_example = {
        "negative_sites": "(0, 1, 3)",
        "mu": "1/5",
        "D12": "1/9",
        "deficit": "16/225",
    }
    if example != expected_example:
        raise AssertionError(f"unexpected L=2 witness: {example!r}")
    if total != 84:
        raise AssertionError(f"expected 84 Q3 rows, found {total}")
    if l2_pass != 31:
        raise AssertionError(f"expected 31 L=2 passes, found {l2_pass}")
    if l3_symmetric != 14:
        raise AssertionError(f"expected 14 symmetric L=3 matrices, found {l3_symmetric}")
    if l3_psd_pass != 0:
        raise AssertionError(f"expected no L=3 PSD passes, found {l3_psd_pass}")
    if certificates != EXPECTED_CERTIFICATES:
        raise AssertionError(f"certificate table drift: {certificates!r}")

    summary = {
        "alphabet_size": N,
        "real_sign_q3_rows": total,
        "l2_pass": l2_pass,
        "l2_witness": example,
        "l3_symmetry_fail": total - l3_symmetric,
        "l3_symmetric": l3_symmetric,
        "l3_psd_pass": l3_psd_pass,
        "l3_certificates": [
            {
                "negative_sites": list(negative_sites),
                "kind": kind,
                "indices": list(indices),
                "value": fraction_text(value),
            }
            for negative_sites, (kind, indices, value) in sorted(certificates.items())
        ],
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

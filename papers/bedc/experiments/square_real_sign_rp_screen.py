#!/usr/bin/env python3
from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, isqrt, sqrt
from typing import Iterable

import numpy as np


Support = tuple[int, ...]

EXPECTED = {
    9: {"total": 84, "l3_pass": 0, "l4_pass": 0},
    16: {"total": 8008, "l3_pass": 7, "l4_pass": 0},
    25: {
        "total": 3268760,
        "l3_pass": 2784,
        "l4_pass": 0,
        "l4_nonhermitian": 2612,
        "l4_hermitian_psd_fail": 172,
    },
}

EXPECTED_N25_PSD_CERTIFICATES = Counter(
    {
        ("diag", (3,)): 76,
        ("diag", (5,)): 32,
        ("diag", (7,)): 6,
        ("det", (0, 3)): 8,
        ("det", (0, 5)): 20,
        ("det", (0, 7)): 4,
        ("det", (1, 3)): 6,
        ("det", (1, 5)): 4,
        ("det", (1, 6)): 8,
        ("det", (2, 3)): 2,
        ("det", (3, 4)): 4,
        ("det", (5, 7)): 2,
    }
)

N25_STRICT_WITNESS = (9, 11, 12, 14, 16, 18, 20, 21, 22, 23)
N25_CLOSE_HERMITIAN_WITNESS = (0, 1, 2, 3, 12, 13, 17, 18, 21, 22)


def normalize(support: Iterable[int]) -> Support:
    values = tuple(sorted(set(support)))
    if not values:
        return ()
    offset = values[0]
    return tuple(value - offset for value in values)


def reflect(support: Support) -> Support:
    return tuple(1 - site for site in support)


def symmetric_difference(left: Iterable[int], right: Iterable[int]) -> Support:
    return tuple(sorted(set(left) ^ set(right)))


def entry_support(row_support: Support, column_support: Support) -> Support:
    return normalize(symmetric_difference(reflect(row_support), column_support))


def neutral_window(length: int) -> tuple[Support, ...]:
    rows: list[Support] = [()]
    for size in range(2, length + 1, 2):
        rows.extend(tuple(support) for support in combinations(range(1, length + 1), size))
    return tuple(rows)


def mask_from_sites(sites: Iterable[int]) -> int:
    mask = 0
    for site in sites:
        mask |= 1 << site
    return mask


def combination_masks(alphabet_size: int, negative_count: int) -> np.ndarray:
    total = comb(alphabet_size, negative_count)
    masks = np.empty(total, dtype=np.uint32)
    for index, negative_sites in enumerate(combinations(range(alphabet_size), negative_count)):
        masks[index] = mask_from_sites(negative_sites)
    return masks


def branch_child_masks(alphabet_size: int, entries: Iterable[Support]) -> list[int]:
    masks: set[int] = set()
    for support in entries:
        for residue in range(alphabet_size):
            masks.add(mask_from_sites((residue + site) % alphabet_size for site in support))
    return sorted(masks)


def sign_table(words: np.ndarray, child_masks: list[int]) -> np.ndarray:
    signs = np.empty((len(child_masks), len(words)), dtype=np.int16)
    for index, child_mask in enumerate(child_masks):
        parity = np.bitwise_count(np.bitwise_and(words, np.uint32(child_mask))) & 1
        signs[index] = np.where(parity.astype(bool), -1, 1)
    return signs


def entry_branch_indices(
    alphabet_size: int,
    entries: list[Support],
    child_masks: list[int],
) -> list[tuple[list[int], list[int]]]:
    mask_index = {mask: index for index, mask in enumerate(child_masks)}
    branches: list[tuple[list[int], list[int]]] = []
    for support in entries:
        empty_branches: list[int] = []
        mu_branches: list[int] = []
        for residue in range(alphabet_size):
            child_sites: list[int] = []
            carry_parity = 0
            for site in support:
                quotient, child = divmod(residue + site, alphabet_size)
                carry_parity ^= quotient & 1
                child_sites.append(child)
            child_index = mask_index[mask_from_sites(child_sites)]
            if carry_parity:
                mu_branches.append(child_index)
            else:
                empty_branches.append(child_index)
        branches.append((empty_branches, mu_branches))
    return branches


def scaled_entry_values(
    words: np.ndarray,
    alphabet_size: int,
    entries: list[Support],
) -> tuple[np.ndarray, np.ndarray]:
    child_masks = branch_child_masks(alphabet_size, entries)
    signs = sign_table(words, child_masks)
    mask_index = {mask: index for index, mask in enumerate(child_masks)}

    closing_edge = (1 << (alphabet_size - 1)) | 1
    closing_parity = np.bitwise_count(np.bitwise_and(words, np.uint32(closing_edge))) & 1
    closing_sign = np.where(closing_parity.astype(bool), -1, 1).astype(np.int16)
    denominator = (alphabet_size - closing_sign).astype(np.int16)

    edge_masks = [(1 << site) | (1 << (site + 1)) for site in range(alphabet_size - 1)]
    mu_numerator = signs[[mask_index[edge_mask] for edge_mask in edge_masks]].sum(axis=0).astype(np.int16)
    common_denominator = (alphabet_size * denominator).astype(np.int32)

    branches = entry_branch_indices(alphabet_size, entries, child_masks)
    values = np.empty((len(entries), len(words)), dtype=np.int32)
    for index, (empty_branches, mu_branches) in enumerate(branches):
        if not entries[index]:
            values[index] = common_denominator
            continue
        empty_sum = (
            signs[empty_branches].sum(axis=0).astype(np.int32)
            if empty_branches
            else np.zeros(len(words), dtype=np.int32)
        )
        mu_sum = (
            signs[mu_branches].sum(axis=0).astype(np.int32)
            if mu_branches
            else np.zeros(len(words), dtype=np.int32)
        )
        values[index] = empty_sum * denominator.astype(np.int32) + mu_sum * mu_numerator.astype(np.int32)

    return values, common_denominator


def determinant_four_batch(matrix: np.ndarray) -> np.ndarray:
    det = np.zeros(matrix.shape[2], dtype=np.int64)
    for perm in permutations(range(4)):
        inversions = sum(1 for left in range(4) for right in range(left + 1, 4) if perm[left] > perm[right])
        term = np.ones(matrix.shape[2], dtype=np.int64)
        for row, column in enumerate(perm):
            term *= matrix[row, column].astype(np.int64)
        det += (-1 if inversions & 1 else 1) * term
    return det


def psd_four_mask(matrix: np.ndarray) -> np.ndarray:
    keep = np.ones(matrix.shape[2], dtype=bool)
    for index in range(4):
        keep &= matrix[index, index] >= 0
    for left, right in combinations(range(4), 2):
        minor = (
            matrix[left, left].astype(np.int64) * matrix[right, right].astype(np.int64)
            - matrix[left, right].astype(np.int64) * matrix[right, left].astype(np.int64)
        )
        keep &= minor >= 0
    for a, b, c in combinations(range(4), 3):
        minor = (
            matrix[a, a].astype(np.int64)
            * (
                matrix[b, b].astype(np.int64) * matrix[c, c].astype(np.int64)
                - matrix[b, c].astype(np.int64) * matrix[c, b].astype(np.int64)
            )
            - matrix[a, b].astype(np.int64)
            * (
                matrix[b, a].astype(np.int64) * matrix[c, c].astype(np.int64)
                - matrix[b, c].astype(np.int64) * matrix[c, a].astype(np.int64)
            )
            + matrix[a, c].astype(np.int64)
            * (
                matrix[b, a].astype(np.int64) * matrix[c, b].astype(np.int64)
                - matrix[b, b].astype(np.int64) * matrix[c, a].astype(np.int64)
            )
        )
        keep &= minor >= 0
    keep &= determinant_four_batch(matrix) >= 0
    return keep


def hermitian_mask(matrix: np.ndarray) -> np.ndarray:
    keep = np.ones(matrix.shape[2], dtype=bool)
    for left, right in combinations(range(matrix.shape[0]), 2):
        keep &= matrix[left, right] == matrix[right, left]
    return keep


def psd_low_certificate_counts(matrix: np.ndarray) -> Counter[tuple[str, tuple[int, ...]]]:
    active = np.ones(matrix.shape[2], dtype=bool)
    certificates: Counter[tuple[str, tuple[int, ...]]] = Counter()

    for index in range(matrix.shape[0]):
        bad = active & (matrix[index, index] < 0)
        certificates[("diag", (index,))] += int(bad.sum())
        active &= matrix[index, index] >= 0

    for left, right in combinations(range(matrix.shape[0]), 2):
        minor = (
            matrix[left, left].astype(np.int64) * matrix[right, right].astype(np.int64)
            - matrix[left, right].astype(np.int64) * matrix[right, left].astype(np.int64)
        )
        bad = active & (minor < 0)
        certificates[("det", (left, right))] += int(bad.sum())
        active &= minor >= 0

    return +certificates


def psd_low_pass_mask(matrix: np.ndarray) -> np.ndarray:
    active = np.ones(matrix.shape[2], dtype=bool)
    for index in range(matrix.shape[0]):
        active &= matrix[index, index] >= 0
    for left, right in combinations(range(matrix.shape[0]), 2):
        minor = (
            matrix[left, left].astype(np.int64) * matrix[right, right].astype(np.int64)
            - matrix[left, right].astype(np.int64) * matrix[right, left].astype(np.int64)
        )
        active &= minor >= 0
    return active


def fraction_text(numerator: int, denominator: int) -> str:
    value = Fraction(int(numerator), int(denominator))
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def tuple_from_mask(mask: int, alphabet_size: int) -> tuple[int, ...]:
    return tuple(site for site in range(alphabet_size) if (mask >> site) & 1)


def analyze_square(alphabet_size: int) -> dict[str, object]:
    root = isqrt(alphabet_size)
    if root * root != alphabet_size:
        raise ValueError("alphabet size must be a square")
    negative_count = (alphabet_size - root) // 2
    words = combination_masks(alphabet_size, negative_count)

    window_three = neutral_window(3)
    entries_three = [entry_support(row, column) for row in window_three for column in window_three]
    values_three, denominator_three = scaled_entry_values(words, alphabet_size, entries_three)
    matrix_three = values_three.reshape((len(window_three), len(window_three), len(words)))
    l3_pass_mask = hermitian_mask(matrix_three) & psd_four_mask(matrix_three)
    l3_words = words[l3_pass_mask]

    window_four = neutral_window(4)
    entries_four = [entry_support(row, column) for row in window_four for column in window_four]
    values_four, denominator_four = scaled_entry_values(l3_words, alphabet_size, entries_four)
    matrix_four = values_four.reshape((len(window_four), len(window_four), len(l3_words)))
    l4_hermitian_mask = hermitian_mask(matrix_four)
    matrix_four_hermitian = matrix_four[:, :, l4_hermitian_mask]
    l4_psd_mask = psd_low_pass_mask(matrix_four_hermitian)

    summary: dict[str, object] = {
        "alphabet_size": alphabet_size,
        "positive_entries": (alphabet_size + root) // 2,
        "negative_entries": negative_count,
        "real_sign_q3_rows": int(len(words)),
        "l3_pass": int(l3_pass_mask.sum()),
        "l4_nonhermitian": int((~l4_hermitian_mask).sum()),
        "l4_hermitian_psd_fail": int((~l4_psd_mask).sum()),
        "l4_pass": int(l4_psd_mask.sum()),
    }

    if alphabet_size == 25:
        certificate_counts = psd_low_certificate_counts(matrix_four_hermitian)
        if certificate_counts != EXPECTED_N25_PSD_CERTIFICATES:
            raise AssertionError(f"N=25 PSD certificate drift: {certificate_counts!r}")
        summary["l4_hermitian_psd_failure_certificates"] = [
            {"kind": kind, "indices": list(indices), "count": count}
            for (kind, indices), count in sorted(certificate_counts.items(), key=lambda item: (item[0][0], item[0][1]))
        ]

        strict_mask = np.uint32(mask_from_sites(N25_STRICT_WITNESS))
        strict_positions = np.where(l3_words == strict_mask)[0]
        if len(strict_positions) != 1:
            raise AssertionError("strict N=25 witness is not an L=3 survivor")
        strict_index = int(strict_positions[0])
        strict_full_index = int(np.where(words == strict_mask)[0][0])
        strict_denominator = int(denominator_three[strict_full_index])
        strict_matrix = matrix_three[:, :, strict_full_index]
        strict_l4_denominator = int(denominator_four[strict_index])
        summary["strict_l3_witness"] = {
            "negative_sites": list(N25_STRICT_WITNESS),
            "denominator": strict_denominator,
            "m3": [
                [fraction_text(strict_matrix[row, column], strict_denominator) for column in range(4)]
                for row in range(4)
            ],
            "lambda_min_exact": "(17 - sqrt(233))/25",
            "lambda_min_float": (17 - sqrt(233)) / 25,
            "l4_entry_77": fraction_text(matrix_four[7, 7, strict_index], strict_l4_denominator),
        }

        close_mask = np.uint32(mask_from_sites(N25_CLOSE_HERMITIAN_WITNESS))
        close_positions = np.where(l3_words == close_mask)[0]
        if len(close_positions) != 1:
            raise AssertionError("near-Hermitian N=25 witness is not an L=3 survivor")
        close_index = int(close_positions[0])
        close_denominator = int(denominator_four[close_index])
        summary["near_hermitian_witness"] = {
            "negative_sites": list(N25_CLOSE_HERMITIAN_WITNESS),
            "denominator": close_denominator,
            "m35": fraction_text(matrix_four[3, 5, close_index], close_denominator),
            "m53": fraction_text(matrix_four[5, 3, close_index], close_denominator),
            "difference": fraction_text(
                matrix_four[5, 3, close_index] - matrix_four[3, 5, close_index],
                close_denominator,
            ),
        }

    expected = EXPECTED[alphabet_size]
    for field, expected_value in expected.items():
        actual_value = summary[field if field != "total" else "real_sign_q3_rows"]
        if actual_value != expected_value:
            raise AssertionError(
                f"N={alphabet_size} expected {field}={expected_value}, found {actual_value}"
            )
    return summary


def main() -> int:
    payload = {
        "window_order_l4": [
            [],
            [1, 2],
            [1, 3],
            [1, 4],
            [2, 3],
            [2, 4],
            [3, 4],
            [1, 2, 3, 4],
        ],
        "screens": [analyze_square(alphabet_size) for alphabet_size in (9, 16, 25)],
    }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

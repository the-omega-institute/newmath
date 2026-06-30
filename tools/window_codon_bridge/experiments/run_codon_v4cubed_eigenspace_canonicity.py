#!/usr/bin/env python3
"""Exact codon V4-cubed character and H(3,4) eigenspace certificate."""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
import json
import sys


EXPERIMENT_ID = "codon_v4cubed_eigenspace_canonicity"
CLAIM_ID = "bridge.genetic_code.codon_v4cubed_eigenspace.canonicity"

BASES = ("A", "C", "G", "U")
CHARACTER_ORDER = ("1", "R", "W", "K")
PARTITION_ORDER = ("RY", "WS", "KM")

CHARACTERS = {
    "1": {"A": 1, "C": 1, "G": 1, "U": 1},
    "R": {"A": 1, "G": 1, "C": -1, "U": -1},
    "W": {"A": 1, "U": 1, "G": -1, "C": -1},
    "K": {"G": 1, "U": 1, "A": -1, "C": -1},
}

PARTITIONS = {
    "RY": CHARACTERS["R"],
    "WS": CHARACTERS["W"],
    "KM": CHARACTERS["K"],
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status == "certified" else 3)


def dot(left: list[int], right: list[int]) -> int:
    return sum(a * b for a, b in zip(left, right))


def mean_center(values: list[int]) -> list[Fraction]:
    mean = Fraction(sum(values), len(values))
    return [Fraction(value) - mean for value in values]


def fraction_to_json(value: Fraction) -> int | str:
    if value.denominator == 1:
        return value.numerator
    return f"{value.numerator}/{value.denominator}"


def column_rank(columns: list[list[int | Fraction]]) -> int:
    if not columns:
        return 0
    matrix = [[Fraction(columns[col][row]) for col in range(len(columns))] for row in range(len(columns[0]))]
    rank = 0
    col_count = len(columns)
    row_count = len(matrix)
    for col in range(col_count):
        pivot = None
        for row in range(rank, row_count):
            if matrix[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        pivot_value = matrix[rank][col]
        matrix[rank] = [value / pivot_value for value in matrix[rank]]
        for row in range(row_count):
            if row != rank and matrix[row][col] != 0:
                factor = matrix[row][col]
                matrix[row] = [
                    value - factor * pivot_entry
                    for value, pivot_entry in zip(matrix[row], matrix[rank])
                ]
        rank += 1
        if rank == row_count:
            break
    return rank


def codons() -> list[str]:
    return ["".join(codon) for codon in product(BASES, repeat=3)]


def hamming_distance(left: str, right: str) -> int:
    return sum(a != b for a, b in zip(left, right))


def hamming_edges(all_codons: list[str]) -> list[tuple[str, str]]:
    return [(left, right) for left, right in combinations(all_codons, 2) if hamming_distance(left, right) == 1]


def character_tensor(labels: tuple[str, str, str], all_codons: list[str]) -> list[int]:
    return [
        CHARACTERS[labels[0]][codon[0]]
        * CHARACTERS[labels[1]][codon[1]]
        * CHARACTERS[labels[2]][codon[2]]
        for codon in all_codons
    ]


def h3_tensor(labels: tuple[str, str, str], all_codons: list[str]) -> list[Fraction]:
    raw = [
        PARTITIONS[labels[0]][codon[0]]
        * PARTITIONS[labels[1]][codon[1]]
        * PARTITIONS[labels[2]][codon[2]]
        for codon in all_codons
    ]
    return mean_center(raw)


def adjacency_apply(vector: list[int], all_codons: list[str], index_by_codon: dict[str, int]) -> list[int]:
    result: list[int] = []
    for codon in all_codons:
        total = 0
        for position in range(3):
            for base in BASES:
                if base == codon[position]:
                    continue
                neighbor = codon[:position] + base + codon[position + 1 :]
                total += vector[index_by_codon[neighbor]]
        result.append(total)
    return result


def check_row(name: str, ok: bool, **fields: object) -> dict[str, object]:
    row = {"name": name, "ok": ok}
    row.update(fields)
    return row


def main() -> None:
    all_codons = codons()
    edges = hamming_edges(all_codons)
    index_by_codon = {codon: index for index, codon in enumerate(all_codons)}

    base_relation_values = {
        base: CHARACTERS["R"][base] * CHARACTERS["W"][base] * CHARACTERS["K"][base]
        for base in BASES
    }
    klein_relation_ok = all(value == -1 for value in base_relation_values.values())

    base_character_dot_products = {
        f"{left}.{right}": sum(CHARACTERS[left][base] * CHARACTERS[right][base] for base in BASES)
        for left in CHARACTER_ORDER
        for right in CHARACTER_ORDER
    }
    character_basis_orthogonal = all(
        value == (4 if left == right else 0)
        for left in CHARACTER_ORDER
        for right in CHARACTER_ORDER
        for key, value in [(f"{left}.{right}", base_character_dot_products[f"{left}.{right}"])]
    )

    tensors: dict[tuple[str, str, str], list[int]] = {
        labels: character_tensor(labels, all_codons)
        for labels in product(CHARACTER_ORDER, repeat=3)
    }
    tensor_labels = list(tensors)
    tensor_dot_products_ok = True
    tensor_norms_ok = True
    for index, left in enumerate(tensor_labels):
        left_vector = tensors[left]
        if dot(left_vector, left_vector) != 64:
            tensor_norms_ok = False
        for right in tensor_labels[index + 1 :]:
            if dot(left_vector, tensors[right]) != 0:
                tensor_dot_products_ok = False
                break
        if not tensor_dot_products_ok:
            break
    tensor_rank = column_rank(list(tensors.values()))
    character_tensor_basis_ok = tensor_dot_products_ok and tensor_norms_ok and tensor_rank == 64

    level_labels: dict[int, list[tuple[str, str, str]]] = {0: [], 1: [], 2: [], 3: []}
    for labels in tensor_labels:
        level = sum(label != "1" for label in labels)
        level_labels[level].append(labels)
    level_dims = [len(level_labels[level]) for level in range(4)]
    level_dim_formula = [1, 9, 27, 27]
    level_dims_ok = level_dims == level_dim_formula and sum(level_dims) == 64

    eigenvalue_by_level = {level: 9 - 4 * level for level in range(4)}
    eigenspace_failures: list[dict[str, object]] = []
    for level, labels_at_level in level_labels.items():
        eigenvalue = eigenvalue_by_level[level]
        for labels in labels_at_level:
            vector = tensors[labels]
            observed = adjacency_apply(vector, all_codons, index_by_codon)
            expected = [eigenvalue * value for value in vector]
            if observed != expected:
                eigenspace_failures.append(
                    {
                        "labels": list(labels),
                        "level": level,
                        "expected_eigenvalue": eigenvalue,
                    }
                )
    eigenspace_check_ok = not eigenspace_failures

    e3_labels = level_labels[3]
    e3_columns = [tensors[labels] for labels in e3_labels]
    h3_labels = list(product(PARTITION_ORDER, repeat=3))
    h3_columns = [h3_tensor(labels, all_codons) for labels in h3_labels]
    h3_raw_means = {
        "h3:" + "_".join(labels): fraction_to_json(sum(h3_tensor(labels, all_codons), Fraction(0)) / len(all_codons))
        for labels in h3_labels
    }
    h3_rank = column_rank(h3_columns)
    e3_rank = column_rank(e3_columns)
    h3_e3_combined_rank = column_rank([*e3_columns, *h3_columns])
    h3_equals_e3 = h3_rank == 27 and e3_rank == 27 and h3_e3_combined_rank == 27

    edge_count_ok = len(edges) == 64 * 9 // 2
    all_checks = [
        check_row("codon_count", len(all_codons) == 64, observed=len(all_codons), expected=64),
        check_row("hamming_edge_count", edge_count_ok, observed=len(edges), expected=288),
        check_row(
            "chemical_character_product_relation",
            klein_relation_ok,
            observed=base_relation_values,
            expected={base: -1 for base in BASES},
        ),
        check_row(
            "base_character_basis_orthogonal",
            character_basis_orthogonal,
            dot_products=base_character_dot_products,
        ),
        check_row(
            "character_tensors_orthogonal_basis",
            character_tensor_basis_ok,
            tensor_rank=tensor_rank,
            tensor_count=len(tensors),
            tensor_norms_ok=tensor_norms_ok,
            tensor_dot_products_ok=tensor_dot_products_ok,
        ),
        check_row("level_dimensions", level_dims_ok, observed=level_dims, expected=level_dim_formula),
        check_row(
            "krawtchouk_eigenspace_equations",
            eigenspace_check_ok,
            failures=eigenspace_failures[:5],
            failure_count=len(eigenspace_failures),
        ),
        check_row(
            "h3_span_equals_e3",
            h3_equals_e3,
            h3_rank=h3_rank,
            e3_rank=e3_rank,
            combined_rank=h3_e3_combined_rank,
            h3_vector_count=len(h3_columns),
            h3_means=h3_raw_means,
        ),
    ]

    certified = all(bool(row["ok"]) for row in all_checks)
    emit(
        "certified" if certified else "needs_derivation",
        klein_relation_ok=klein_relation_ok,
        character_basis_orthogonal=character_basis_orthogonal and character_tensor_basis_ok,
        level_dims=level_dims,
        krawtchouk_eigenvalues=[eigenvalue_by_level[level] for level in range(4)],
        eigenspace_check_ok=eigenspace_check_ok,
        h3_equals_E3=h3_equals_e3,
        n_codons=len(all_codons),
        n_edges=len(edges),
        checks=all_checks,
        reason=(
            "Exact integer character tensors form the H(3,4) Krawtchouk eigenspace decomposition; "
            "the bridge H3 construction is the full level-three span."
            if certified
            else "At least one exact structural check failed; see checks."
        ),
    )


if __name__ == "__main__":
    main()

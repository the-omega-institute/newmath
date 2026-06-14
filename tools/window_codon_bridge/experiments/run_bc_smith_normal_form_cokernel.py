#!/usr/bin/env python3
"""Smith-normal-form cokernel check for Window6 and codon-side matrices."""
from __future__ import annotations

from collections import Counter
from itertools import combinations, product
import json
import math
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "bc_smith_normal_form_cokernel"
CLAIM_ID = "bridge.window6_codon_q6.smith_normal_form_cokernel"
RANDOM_SEED = 906601
RANDOM_DRAWS_4 = 300
RANDOM_DRAWS_16 = 60

WINDOW_EDGE_MATRIX = [
    [28, 63, 23, 20],
    [63, 21, 21, 6],
    [23, 21, 2, 6],
    [20, 6, 6, 2],
]

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}

CODON_TO_FAMILY = {
    "UUU": "Phe", "UUC": "Phe", "UUA": "Leu", "UUG": "Leu",
    "UCU": "Ser", "UCC": "Ser", "UCA": "Ser", "UCG": "Ser",
    "UAU": "Tyr", "UAC": "Tyr", "UAA": "Stop", "UAG": "Stop",
    "UGU": "Cys", "UGC": "Cys", "UGA": "Stop", "UGG": "Trp",
    "CUU": "Leu", "CUC": "Leu", "CUA": "Leu", "CUG": "Leu",
    "CCU": "Pro", "CCC": "Pro", "CCA": "Pro", "CCG": "Pro",
    "CAU": "His", "CAC": "His", "CAA": "Gln", "CAG": "Gln",
    "CGU": "Arg", "CGC": "Arg", "CGA": "Arg", "CGG": "Arg",
    "AUU": "Ile", "AUC": "Ile", "AUA": "Ile", "AUG": "Met",
    "ACU": "Thr", "ACC": "Thr", "ACA": "Thr", "ACG": "Thr",
    "AAU": "Asn", "AAC": "Asn", "AAA": "Lys", "AAG": "Lys",
    "AGU": "Ser", "AGC": "Ser", "AGA": "Arg", "AGG": "Arg",
    "GUU": "Val", "GUC": "Val", "GUA": "Val", "GUG": "Val",
    "GCU": "Ala", "GCC": "Ala", "GCA": "Ala", "GCG": "Ala",
    "GAU": "Asp", "GAC": "Asp", "GAA": "Glu", "GAG": "Glu",
    "GGU": "Gly", "GGC": "Gly", "GGA": "Gly", "GGG": "Gly",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def smith_normal_form_diagonal(matrix: list[list[int]]) -> list[int]:
    """Return the diagonal of a Smith normal form using integer row/column moves."""
    if not matrix:
        return []
    width = len(matrix[0])
    if any(len(row) != width for row in matrix):
        raise ValueError("matrix rows have unequal lengths")

    a = [list(map(int, row)) for row in matrix]
    rows = len(a)
    cols = width
    pivot = 0

    def swap_rows(left: int, right: int) -> None:
        if left != right:
            a[left], a[right] = a[right], a[left]

    def swap_cols(left: int, right: int) -> None:
        if left != right:
            for row in range(rows):
                a[row][left], a[row][right] = a[row][right], a[row][left]

    def add_row(dst: int, src: int, coeff: int) -> None:
        if coeff:
            dst_row = a[dst]
            src_row = a[src]
            for col in range(cols):
                dst_row[col] += coeff * src_row[col]

    def add_col(dst: int, src: int, coeff: int) -> None:
        if coeff:
            for row in range(rows):
                a[row][dst] += coeff * a[row][src]

    while pivot < rows and pivot < cols:
        position = None
        best_abs = None
        for row in range(pivot, rows):
            for col in range(pivot, cols):
                value = a[row][col]
                if value and (best_abs is None or abs(value) < best_abs):
                    best_abs = abs(value)
                    position = (row, col)
        if position is None:
            break

        swap_rows(pivot, position[0])
        swap_cols(pivot, position[1])

        while True:
            if a[pivot][pivot] < 0:
                for col in range(cols):
                    a[pivot][col] = -a[pivot][col]

            moved = False
            for row in range(rows):
                if row == pivot or a[row][pivot] == 0:
                    continue
                quotient = a[row][pivot] // a[pivot][pivot]
                add_row(row, pivot, -quotient)
                if a[row][pivot] and abs(a[row][pivot]) < abs(a[pivot][pivot]):
                    swap_rows(row, pivot)
                moved = True
                break
            if moved:
                continue

            for col in range(cols):
                if col == pivot or a[pivot][col] == 0:
                    continue
                quotient = a[pivot][col] // a[pivot][pivot]
                add_col(col, pivot, -quotient)
                if a[pivot][col] and abs(a[pivot][col]) < abs(a[pivot][pivot]):
                    swap_cols(col, pivot)
                moved = True
                break
            if moved:
                continue

            divisor = a[pivot][pivot]
            offending = None
            for row in range(pivot + 1, rows):
                for col in range(pivot + 1, cols):
                    if a[row][col] % divisor:
                        offending = (row, col)
                        break
                if offending is not None:
                    break
            if offending is None:
                break

            add_row(pivot, offending[0], 1)

        pivot += 1

    diagonal = [abs(a[index][index]) for index in range(min(rows, cols))]
    nonzero = [value for value in diagonal if value]
    if not all(nonzero[index + 1] % nonzero[index] == 0 for index in range(len(nonzero) - 1)):
        raise ArithmeticError(f"SNF divisibility chain failed: {nonzero}")
    return diagonal


def determinant_bareiss(matrix: list[list[int]]) -> int:
    if not matrix:
        return 1
    if any(len(row) != len(matrix) for row in matrix):
        raise ValueError("determinant requires a square matrix")

    a = [row[:] for row in matrix]
    n = len(a)
    sign = 1
    previous = 1
    for index in range(n - 1):
        if a[index][index] == 0:
            swap = None
            for row in range(index + 1, n):
                if a[row][index] != 0:
                    swap = row
                    break
            if swap is None:
                return 0
            a[index], a[swap] = a[swap], a[index]
            sign = -sign
        pivot = a[index][index]
        for row in range(index + 1, n):
            for col in range(index + 1, n):
                a[row][col] = (a[row][col] * pivot - a[row][index] * a[index][col]) // previous
        previous = pivot
        for row in range(index + 1, n):
            a[row][index] = 0
    return sign * a[n - 1][n - 1]


def product_int(values: Iterable[int]) -> int:
    product_value = 1
    for value in values:
        product_value *= value
    return product_value


def cokernel_summary(matrix: list[list[int]]) -> dict[str, object]:
    diagonal = smith_normal_form_diagonal(matrix)
    free_rank = sum(1 for value in diagonal if value == 0)
    torsion = [value for value in diagonal if value > 1]
    finite_order = None if free_rank else product_int(torsion)
    return {
        "elementary_divisors": diagonal,
        "torsion_factors": torsion,
        "free_rank": free_rank,
        "finite_order": finite_order,
        "group": group_string(torsion, free_rank),
    }


def group_string(torsion: list[int], free_rank: int) -> str:
    parts = []
    if free_rank == 1:
        parts.append("Z")
    elif free_rank > 1:
        parts.append(f"Z^{free_rank}")
    parts.extend(f"Z/{value}Z" for value in torsion)
    return "0" if not parts else " + ".join(parts)


def isomorphic_cokernel(left: dict[str, object], right: dict[str, object]) -> bool:
    return left["free_rank"] == right["free_rank"] and left["torsion_factors"] == right["torsion_factors"]


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def q6_adjacency_matrix() -> list[list[int]]:
    size = 64
    matrix = [[0] * size for _ in range(size)]
    for vertex in range(size):
        for axis in range(6):
            matrix[vertex][vertex ^ (1 << axis)] = 1
    return matrix


def hamming_3_4_adjacency_matrix(codons: list[str]) -> list[list[int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    size = len(codons)
    matrix = [[0] * size for _ in range(size)]
    for codon in codons:
        left = index[codon]
        for position in range(3):
            for base in BASES:
                if base == codon[position]:
                    continue
                other = codon[:position] + base + codon[position + 1:]
                matrix[left][index[other]] = 1
    return matrix


def hamming_3_4_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges = []
    for codon in codons:
        left = index[codon]
        for position in range(3):
            for base in BASES:
                if base == codon[position]:
                    continue
                other = codon[:position] + base + codon[position + 1:]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


def family_quotient_laplacian(codons: list[str]) -> tuple[list[list[int]], list[list[int]], dict[str, object]]:
    families = sorted(set(CODON_TO_FAMILY.values()))
    family_index = {family: pos for pos, family in enumerate(families)}
    weighted_adjacency = [[0] * len(families) for _ in families]
    internal_edges = 0
    for left, right in hamming_3_4_edges(codons):
        left_family = CODON_TO_FAMILY[codons[left]]
        right_family = CODON_TO_FAMILY[codons[right]]
        if left_family == right_family:
            internal_edges += 1
            continue
        left_pos = family_index[left_family]
        right_pos = family_index[right_family]
        weighted_adjacency[left_pos][right_pos] += 1
        weighted_adjacency[right_pos][left_pos] += 1

    laplacian = [[0] * len(families) for _ in families]
    for row in range(len(families)):
        laplacian[row][row] = sum(weighted_adjacency[row])
        for col in range(len(families)):
            if row != col:
                laplacian[row][col] = -weighted_adjacency[row][col]

    metadata = {
        "families": families,
        "family_count": len(families),
        "inter_family_edges": sum(sum(row) for row in weighted_adjacency) // 2,
        "internal_family_edges": internal_edges,
        "removed_family_for_reduced_laplacian": families[0],
    }
    reduced = [row[1:] for row in laplacian[1:]]
    return weighted_adjacency, reduced, metadata


def random_symmetric_matrix(size: int, rng: random.Random, max_entry: int = 63) -> list[list[int]]:
    matrix = [[0] * size for _ in range(size)]
    for row in range(size):
        for col in range(row, size):
            value = rng.randint(0, max_entry)
            matrix[row][col] = value
            matrix[col][row] = value
    return matrix


def random_simple_graph_adjacency(size: int, rng: random.Random, edge_probability: float) -> list[list[int]]:
    matrix = [[0] * size for _ in range(size)]
    for left, right in combinations(range(size), 2):
        if rng.random() < edge_probability:
            matrix[left][right] = 1
            matrix[right][left] = 1
    return matrix


def random_nulls(window_torsion: list[int], codon_torsions: dict[str, list[int]]) -> dict[str, object]:
    rng = random.Random(RANDOM_SEED)

    window_order = product_int(window_torsion)
    window_hits = 0
    window_same_order = 0
    window_nontrivial_hist: Counter[int] = Counter()
    for _ in range(RANDOM_DRAWS_4):
        summary = cokernel_summary(random_symmetric_matrix(4, rng))
        torsion = list(summary["torsion_factors"])
        if summary["free_rank"] == 0 and summary["finite_order"] == window_order:
            window_same_order += 1
        if torsion == window_torsion and summary["free_rank"] == 0:
            window_hits += 1
        window_nontrivial_hist[len(torsion)] += 1

    q6_torsion = codon_torsions["q6_adjacency"]
    q6_hits = 0
    q6_same_pattern = 0
    for _ in range(RANDOM_DRAWS_16):
        summary = cokernel_summary(random_simple_graph_adjacency(16, rng, 6 / 15))
        torsion = list(summary["torsion_factors"])
        if torsion == q6_torsion:
            q6_hits += 1
        if summary["free_rank"] == 0 and len(torsion) == len(q6_torsion):
            q6_same_pattern += 1

    return {
        "window_random_4x4_symmetric_integer": {
            "draws": RANDOM_DRAWS_4,
            "entry_range": [0, 63],
            "exact_group_hits": window_hits,
            "same_order_hits": window_same_order,
            "nontrivial_factor_count_histogram": dict(sorted(window_nontrivial_hist.items())),
            "interpretation": "Window6 group is not treated as evidence merely because random hits are rare.",
        },
        "graph_adjacency_16_vertex_null_for_q6_torsion_shape": {
            "draws": RANDOM_DRAWS_16,
            "edge_probability": 6 / 15,
            "exact_q6_torsion_hits": q6_hits,
            "same_finite_full_rank_factor_count_hits": q6_same_pattern,
            "interpretation": "Small random graphs are a sanity baseline, not a certificate for the 64-vertex codon matrices.",
        },
    }


def main() -> None:
    checks: list[dict[str, object]] = []

    window_summary = cokernel_summary(WINDOW_EDGE_MATRIX)
    window_torsion = list(window_summary["torsion_factors"])
    window_det = determinant_bareiss(WINDOW_EDGE_MATRIX)
    checks.append(check_row("window_edge_matrix_snf", window_summary["elementary_divisors"], [1, 1, 3, 3450]))
    checks.append(check_row("window_edge_matrix_determinant", window_det, 10350))
    checks.append(check_row("window_cokernel_torsion", window_torsion, [3, 3450]))

    codons = codon_order()
    checks.append(check_row("codon_count", len(codons), 64))
    checks.append(check_row("codon_q6_encoding_count", len({codon_to_q6(codon) for codon in codons}), 64))
    checks.append(check_row("codon_family_count", len(set(CODON_TO_FAMILY.values())), 21))

    q6_summary = cokernel_summary(q6_adjacency_matrix())
    h34_summary = cokernel_summary(hamming_3_4_adjacency_matrix(codons))
    family_adjacency, family_reduced_laplacian, family_metadata = family_quotient_laplacian(codons)
    family_adjacency_summary = cokernel_summary(family_adjacency)
    family_laplacian_summary = cokernel_summary(family_reduced_laplacian)

    checks.append(check_row("q6_adjacency_free_rank", q6_summary["free_rank"], 20))
    checks.append(check_row("q6_adjacency_torsion_factors", q6_summary["torsion_factors"], [2] * 10 + [6, 6]))
    checks.append(check_row("hamming_3_4_adjacency_free_rank", h34_summary["free_rank"], 0))
    checks.append(check_row("hamming_3_4_adjacency_torsion_histogram", dict(Counter(h34_summary["torsion_factors"])), {3: 19, 15: 8, 45: 1}))
    checks.append(check_row("family_quotient_edge_counts", [family_metadata["inter_family_edges"], family_metadata["internal_family_edges"]], [219, 69]))
    checks.append(
        check_row(
            "family_quotient_reduced_laplacian_torsion_histogram",
            dict(Counter(family_laplacian_summary["torsion_factors"])),
            {2: 8, 4: 2, 16: 2, 32: 3, 76526146395776: 1},
        )
    )

    codon_cokernels = {
        "q6_adjacency": q6_summary,
        "hamming_3_4_adjacency": h34_summary,
        "family_quotient_adjacency": family_adjacency_summary,
        "family_quotient_reduced_laplacian": family_laplacian_summary,
    }
    isomorphic_by_candidate = {
        name: isomorphic_cokernel(window_summary, summary)
        for name, summary in codon_cokernels.items()
    }
    isomorphic = any(isomorphic_by_candidate.values())
    same_order_candidates = {
        name: summary["finite_order"] == window_summary["finite_order"]
        for name, summary in codon_cokernels.items()
    }

    codon_torsions = {name: list(summary["torsion_factors"]) for name, summary in codon_cokernels.items()}
    nulls = random_nulls(window_torsion, codon_torsions)

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            window_cokernel=window_torsion,
            codon_cokernels=codon_cokernels,
            isomorphic=False,
            checks=checks,
            nulls=nulls,
            note="Self-checks failed before the group-isomorphism verdict.",
        )

    status = "certified" if isomorphic else ("coincidence" if any(same_order_candidates.values()) else "refuted")
    note = (
        "Window6 uses the finite four-cell edge-flux matrix from the Fibonacci branch and has "
        "coker torsion Z/3Z + Z/3450Z. The canonical codon-side matrices tested here are the "
        "64-vertex Q6 adjacency, the synonymous H(3,4) adjacency, the 21-family quotient adjacency, "
        "and the 21-family reduced Laplacian. None has the same free rank and invariant-factor list, "
        "so the label-free cokernel correspondence is refuted rather than certified."
    )

    emit(
        status,
        window_cokernel=window_torsion,
        window_summary=window_summary,
        codon_cokernels=codon_cokernels,
        isomorphic=isomorphic,
        isomorphic_by_candidate=isomorphic_by_candidate,
        same_order_candidates=same_order_candidates,
        family_quotient_metadata=family_metadata,
        nulls=nulls,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

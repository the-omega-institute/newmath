#!/usr/bin/env python3
"""Two-layer fold edge-hiding extremality certificate.

The experiment is label-free after the two partitions are fixed: it uses only
the H(3,4) micrograph, block-size multisets, internal edge counts, exact
blockwise upper witnesses, and permutation nulls preserving block sizes.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, product
import json
import math
import random
import sys
from typing import Hashable, Iterable


EXPERIMENT_ID = "twolayer_fold_extremality"
CLAIM_ID = "bridge.genetic_code.twolayer_fold_edge_hiding_extremality"
RANDOM_SEED = 2061406
NULL_DRAWS = 4000

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)

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

# Entry n is the visible six-prefix of the finite no-adjacent nine-bit
# Zeckendorf representative of n in the 0..63 value window.
FOLD6_VISIBLE_PREFIX = [
    ["000000", "100000", "010000", "001000", "101000", "000100", "100100", "010100"],
    ["000010", "100010", "010010", "001010", "101010", "000001", "100001", "010001"],
    ["001001", "101001", "000101", "100101", "010101", "000000", "100000", "010000"],
    ["001000", "101000", "000100", "100100", "010100", "000010", "100010", "010010"],
    ["001010", "101010", "000000", "100000", "010000", "001000", "101000", "000100"],
    ["100100", "010100", "000010", "100010", "010010", "001010", "101010", "000001"],
    ["100001", "010001", "001001", "101001", "000101", "100101", "010101", "000000"],
    ["100000", "010000", "001000", "101000", "000100", "100100", "010100", "000010"],
]

FOLD6_TAIL_OFFSET = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21],
    [21, 21, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34],
    [34, 34, 34, 34, 34, 34, 34, 55, 55, 55, 55, 55, 55, 55, 55, 55],
]

BLOCK_UPPER_H34 = {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}

# Exact-cover witnesses for the standard-code family size multiset on H(3,4).
# Vertex index is 16 * first_base + 4 * second_base + third_base.
FAMILY_EMAX_WITNESS = [
    [0, 1, 2, 4, 5, 6],
    [3, 7, 11, 19, 23, 27],
    [8, 9, 10, 12, 13, 14],
    [15, 31, 47, 63],
    [16, 20, 24, 28],
    [17, 21, 25, 29],
    [18, 22, 26, 30],
    [32, 33, 34, 35],
    [36, 37, 38],
    [40, 41, 42],
    [39, 43],
    [44, 45],
    [46, 62],
    [48, 49],
    [50, 51],
    [52, 53],
    [54, 55],
    [56, 57],
    [58, 59],
    [60],
    [61],
]

FAMILY_EMIN_WITNESS = [
    [0, 7, 10, 13, 17, 20],
    [1, 6, 11, 12, 16, 21],
    [2, 5, 8, 15, 19, 22],
    [3, 4, 9, 14],
    [18, 23, 25, 28],
    [24, 29, 33, 36],
    [26, 31, 32, 37],
    [27, 30, 35, 38],
    [34, 39, 40],
    [41, 44, 48],
    [42, 45],
    [43, 46],
    [47, 49],
    [50, 52],
    [51, 53],
    [54, 56],
    [55, 57],
    [58, 60],
    [59, 61],
    [62],
    [63],
]


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def flat(rows: list[list[object]]) -> list[object]:
    return [item for row in rows for item in row]


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def codon_to_vertex(codon: str) -> int:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    value = 0
    for axis, bit in enumerate(bits):
        value |= bit << axis
    return value


def h34_edges() -> tuple[list[tuple[int, int]], list[tuple[int, int, int]]]:
    edges: list[tuple[int, int]] = []
    positioned: list[tuple[int, int, int]] = []
    for a, b, c in product(range(4), repeat=3):
        left = 16 * a + 4 * b + c
        for position, values in enumerate(((a, b, c), (a, b, c), (a, b, c))):
            for value in range(4):
                coords = list(values)
                if coords[position] == value:
                    continue
                coords[position] = value
                right = 16 * coords[0] + 4 * coords[1] + coords[2]
                if left < right:
                    edges.append((left, right))
                    positioned.append((left, right, position + 1))
    return edges, positioned


def h34_adjacency_masks(edges: list[tuple[int, int]]) -> list[int]:
    masks = [0] * 64
    for left, right in edges:
        masks[left] |= 1 << right
        masks[right] |= 1 << left
    return masks


def q6_edges() -> list[tuple[int, int]]:
    edges = []
    for vertex in range(64):
        for axis in range(6):
            neighbor = vertex ^ (1 << axis)
            if vertex < neighbor:
                edges.append((vertex, neighbor))
    return edges


def e_in(labels: list[Hashable], edges: Iterable[tuple[int, int]]) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def e_in_by_position(labels: list[Hashable], positioned_edges: list[tuple[int, int, int]]) -> dict[int, int]:
    counts: Counter[int] = Counter()
    for left, right, position in positioned_edges:
        if labels[left] == labels[right]:
            counts[position] += 1
    return dict(sorted(counts.items()))


def sizes_from_labels(labels: list[Hashable]) -> list[int]:
    return sorted(Counter(labels).values(), reverse=True)


def size_histogram(labels: list[Hashable]) -> dict[int, int]:
    return dict(sorted(Counter(Counter(labels).values()).items()))


def labels_from_blocks(blocks: list[list[int]], n: int = 64) -> list[int]:
    labels = [-1] * n
    for block, vertices in enumerate(blocks):
        for vertex in vertices:
            if labels[vertex] != -1:
                raise ValueError("witness blocks overlap")
            labels[vertex] = block
    if any(label < 0 for label in labels):
        raise ValueError("witness blocks do not cover the carrier")
    return labels


def box_emin_labels() -> list[int]:
    labels = [-1] * 64
    block = 0
    for residue in range(4):
        vertices = [
            vertex
            for vertex in range(64)
            if (vertex // 16 + (vertex // 4) % 4 + vertex % 4) % 4 == residue
        ]
        for offset in range(0, len(vertices), 4):
            for vertex in vertices[offset:offset + 4]:
                labels[vertex] = block
            block += 1
    if block != 16 or any(label < 0 for label in labels):
        raise RuntimeError("box e_min witness does not partition the carrier")
    return labels


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def null_stats(observed: int, values: list[int], tail: str) -> dict[str, object]:
    sorted_values = sorted(values)
    mean = sum(values) / len(values)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    if tail == "upper":
        p_value = (sum(1 for value in values if value >= observed) + 1) / (len(values) + 1)
    else:
        p_value = (sum(1 for value in values if value <= observed) + 1) / (len(values) + 1)
    return {
        "draws": len(values),
        "min": sorted_values[0],
        "max": sorted_values[-1],
        "mean": mean,
        "sd": math.sqrt(variance),
        "q05": sorted_values[int(0.05 * (len(sorted_values) - 1))],
        "q50": sorted_values[int(0.50 * (len(sorted_values) - 1))],
        "q95": sorted_values[int(0.95 * (len(sorted_values) - 1))],
        "tail": tail,
        "p_value": p_value,
    }


def sample_null(edges: list[tuple[int, int]], sizes: list[int], observed: int, rng: random.Random) -> dict[str, object]:
    values = [e_in(random_partition_by_sizes(sizes, rng), edges) for _ in range(NULL_DRAWS)]
    stats = null_stats(observed, values, "upper")
    stats["model"] = "uniform label permutation preserving only the block-size multiset"
    return stats


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def reconstruct_window_from_rules() -> tuple[list[str], list[int]]:
    labels: dict[int, str] = {}
    offsets: dict[int, int] = {}
    for bits in product((0, 1), repeat=9):
        if not no_adjacent_ones(bits):
            continue
        value = sum(bit * weight for bit, weight in zip(bits, VISIBLE_WEIGHTS + TAIL_WEIGHTS))
        if value <= 63:
            labels[value] = "".join(str(bit) for bit in bits[:6])
            offsets[value] = sum(bit * weight for bit, weight in zip(bits[6:], TAIL_WEIGHTS))
    return [labels[index] for index in range(64)], [offsets[index] for index in range(64)]


def block_upper_bound(sizes: list[int]) -> int | None:
    total = 0
    for size in sizes:
        if size not in BLOCK_UPPER_H34:
            return None
        total += BLOCK_UPPER_H34[size]
    return total


def rooted_block_upper_table(adjacency: list[int], sizes: list[int]) -> dict[int, int]:
    table: dict[int, int] = {}
    for size in sorted(set(sizes)):
        if size > 6:
            continue
        best = 0
        for tail in combinations(range(1, 64), size - 1):
            mask = 1
            for vertex in tail:
                mask |= 1 << vertex
            internal = 0
            remaining = mask
            while remaining:
                bit = remaining & -remaining
                vertex = bit.bit_length() - 1
                remaining ^= bit
                internal += (adjacency[vertex] & remaining).bit_count()
            best = max(best, internal)
        table[size] = best
    return table


def tau(observed: int, e_min: int, e_max: int) -> float | None:
    if e_max == e_min:
        return None
    return (observed - e_min) / (e_max - e_min)


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    edges, positioned_edges = h34_edges()
    adjacency = h34_adjacency_masks(edges)
    checks: list[dict[str, object]] = []

    codons = codon_order()
    box_labels = [codon[:2] for codon in codons]
    family_labels = [CODON_TO_FAMILY[codon] for codon in codons]

    box_sizes = sizes_from_labels(box_labels)
    family_sizes = sizes_from_labels(family_labels)
    exact_upper_table = rooted_block_upper_table(adjacency, sorted(set(box_sizes + family_sizes)))
    e_in_box = e_in(box_labels, edges)
    e_in_family = e_in(family_labels, edges)
    family_axis = e_in_by_position(family_labels, positioned_edges)

    box_e_min = 0
    box_e_max = block_upper_bound(box_sizes)
    family_e_max = block_upper_bound(family_sizes)
    box_emin_witness_edges = e_in(box_emin_labels(), edges)
    family_emax_labels = labels_from_blocks(FAMILY_EMAX_WITNESS)
    family_emin_labels = labels_from_blocks(FAMILY_EMIN_WITNESS)
    family_e_min = e_in(family_emin_labels, edges)
    family_emax_witness_edges = e_in(family_emax_labels, edges)

    window_fold_labels = [str(item) for item in flat(FOLD6_VISIBLE_PREFIX)]
    window_tail_labels = [int(item) for item in flat(FOLD6_TAIL_OFFSET)]
    reconstructed_fold, reconstructed_tail = reconstruct_window_from_rules()
    window_edges = q6_edges()
    window_fold_sizes = sizes_from_labels(window_fold_labels)
    window_tail_sizes = sizes_from_labels(window_tail_labels)
    window_fold_e_in = e_in(window_fold_labels, window_edges)
    window_tail_e_in = e_in(window_tail_labels, window_edges)

    checks.extend([
        check_row("codon_count", len(codons), 64),
        check_row("codon_q6_encoding_count", len({codon_to_vertex(codon) for codon in codons}), 64),
        check_row("h34_edge_count", len(edges), 288),
        check_row("h34_degree_ledger", 2 * len(edges), 64 * 9),
        check_row("rooted_block_upper_table", exact_upper_table, {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}),
        check_row("box_block_count", len(set(box_labels)), 16),
        check_row("box_size_profile", box_sizes, [4] * 16),
        check_row("box_e_in", e_in_box, 96),
        check_row("box_e_max_upper", box_e_max, 96),
        check_row("box_e_min_witness", box_emin_witness_edges, 0),
        check_row("family_block_count", len(set(family_labels)), 21),
        check_row("family_size_histogram", size_histogram(family_labels), {1: 2, 2: 9, 3: 2, 4: 5, 6: 3}),
        check_row("family_e_in", e_in_family, 69),
        check_row("family_e_in_by_position", family_axis, {1: 4, 2: 1, 3: 64}),
        check_row("family_e_max_upper", family_e_max, 72),
        check_row("family_e_max_witness", family_emax_witness_edges, 72),
        check_row("family_e_min_witness", family_e_min, 0),
        check_row("family_tau_bc7_reproduction", round(tau(e_in_family, family_e_min, family_e_max or -1) or -1, 6), 0.958333),
        check_row("window_fold_reconstruction", window_fold_labels, reconstructed_fold),
        check_row("window_tail_reconstruction", window_tail_labels, reconstructed_tail),
        check_row("window_q6_edge_count", len(window_edges), 192),
        check_row("window_fold_size_histogram", size_histogram(window_fold_labels), {2: 8, 3: 4, 4: 9}),
        check_row("window_fold_e_in", window_fold_e_in, 0),
    ])

    exact_bounds_available = box_e_max is not None and family_e_max is not None and all(row["ok"] for row in checks)
    if not exact_bounds_available:
        emit(
            "needs_derivation",
            tau_box=None,
            tau_family=None,
            e_in_box=e_in_box,
            e_max_box=box_e_max,
            box_null_p=None,
            family_null_p=None,
            iteration_certified=False,
            checks=checks,
            note="Exact e_max or self-check derivation failed.",
        )

    tau_box = tau(e_in_box, box_e_min, int(box_e_max))
    tau_family = tau(e_in_family, family_e_min, int(family_e_max))
    box_null = sample_null(edges, box_sizes, e_in_box, rng)
    family_null = sample_null(edges, family_sizes, e_in_family, rng)

    window_fold_e_max = block_upper_bound(window_fold_sizes)
    window_tail_e_max = None
    window_fold_tau = tau(window_fold_e_in, 0, int(window_fold_e_max)) if window_fold_e_max is not None else None
    window_tail_tau = None

    box_extreme = tau_box == 1.0 and box_null["p_value"] <= 0.01
    family_extreme = tau_family is not None and tau_family >= 0.95 and family_null["p_value"] <= 0.01
    iteration_certified = bool(box_extreme and family_extreme)

    if iteration_certified:
        status = "certified"
        note = (
            "Statement is restricted to iteration of two edge-hiding extremes: "
            "the first-two-base box layer attains the exact size-4x16 maximum, "
            "and the family layer is within three edges of the exact family-profile "
            "maximum while lying in the extreme upper tail of the same-size null. "
            "No isomorphism or biological forcing claim is made."
        )
    elif box_extreme or family_extreme:
        status = "coincidence"
        note = "Only one of the two layers passes the extremal edge-hiding gate."
    else:
        status = "refuted"
        note = "Neither layer pair satisfies the two-layer extremal edge-hiding gate."

    emit(
        status,
        tau_box=tau_box,
        tau_family=tau_family,
        e_in_box=e_in_box,
        e_max_box=box_e_max,
        e_min_box=box_e_min,
        e_in_family=e_in_family,
        e_max_family=family_e_max,
        e_min_family=family_e_min,
        box_null_p=box_null["p_value"],
        family_null_p=family_null["p_value"],
        iteration_certified=iteration_certified,
        nulls={
            "box_same_size_permutation": box_null,
            "family_same_size_permutation": family_null,
        },
        compound_gate={
            "box_tau_is_exact_endpoint": tau_box == 1.0,
            "family_tau_at_least_0_95": tau_family is not None and tau_family >= 0.95,
            "box_upper_tail_p_at_most_0_01": box_null["p_value"] <= 0.01,
            "family_upper_tail_p_at_most_0_01": family_null["p_value"] <= 0.01,
        },
        window6_contrast={
            "source": "origin/fibonacci forced_window_structure vendored table, read-only",
            "fold6_size_profile": window_fold_sizes,
            "fold6_e_in": window_fold_e_in,
            "fold6_e_max_upper": window_fold_e_max,
            "fold6_tau_edge_hiding": window_fold_tau,
            "foldbin_tail_size_profile": window_tail_sizes,
            "foldbin_tail_e_in": window_tail_e_in,
            "foldbin_tail_e_max_upper": window_tail_e_max,
            "foldbin_tail_tau_edge_hiding": window_tail_tau,
        },
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

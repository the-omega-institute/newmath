#!/usr/bin/env python3
"""BC11 partition-quotient lattice check for Window6 and codon Q6.

The test compares partition-pair geometry, not the number of blocks.  The
reported size vectors are audit data; the null verdict uses meet/join geometry,
VI, equitable defects, boundary profiles, and quotient-Laplacian Smith factors.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
import random
import sys
from typing import Hashable, Iterable


EXPERIMENT_ID = "bc11_partition_quotient_wobble_foldbin"
CLAIM_ID = "bridge.window6_codon_q6.partition_quotient_wobble_foldbin"
RANDOM_SEED = 110611
NULL_DRAWS = 8

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)

VENDOR_NOTE = (
    "Window6 partitions are reconstructed from origin/feat/fibonacci_reality-"
    "deepening forced_window_structure: Fold6 is the visible six-prefix fiber; "
    "Zyl is the finite Zeckendorf/Foldbin tail-offset cylinder partition on the "
    "same 0..63 value carrier. Codon family blocks are used only as unlabeled "
    "standard-code fibers."
)

# Unlabeled standard-code fibers.  The Fxx names are arbitrary local block tags;
# they intentionally do not encode amino-acid names.
CODON_FAMILY_BLOCKS = [
    ("UUU", "UUC"),
    ("UUA", "UUG", "CUU", "CUC", "CUA", "CUG"),
    ("UCU", "UCC", "UCA", "UCG", "AGU", "AGC"),
    ("UAU", "UAC"),
    ("UAA", "UAG", "UGA"),
    ("UGU", "UGC"),
    ("UGG",),
    ("CCU", "CCC", "CCA", "CCG"),
    ("CAU", "CAC"),
    ("CAA", "CAG"),
    ("CGU", "CGC", "CGA", "CGG", "AGA", "AGG"),
    ("AUU", "AUC", "AUA"),
    ("AUG",),
    ("ACU", "ACC", "ACA", "ACG"),
    ("AAU", "AAC"),
    ("AAA", "AAG"),
    ("GUU", "GUC", "GUA", "GUG"),
    ("GCU", "GCC", "GCA", "GCG"),
    ("GAU", "GAC"),
    ("GAA", "GAG"),
    ("GGU", "GGC", "GGA", "GGG"),
]


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def vertex_bits(vertex: int) -> tuple[int, ...]:
    return tuple((vertex >> axis) & 1 for axis in range(6))


def int_from_bits(bits: Iterable[int]) -> int:
    value = 0
    for axis, bit in enumerate(bits):
        value |= int(bit) << axis
    return value


def codon_to_vertex(codon: str) -> int:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return int_from_bits(bits)


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def q6_edges() -> list[tuple[int, int]]:
    edges = []
    for vertex in range(64):
        for axis in range(6):
            neighbor = vertex ^ (1 << axis)
            if vertex < neighbor:
                edges.append((vertex, neighbor))
    return edges


def reconstruct_window_partitions() -> tuple[list[str], list[str], dict[str, object]]:
    fold_labels: dict[int, str] = {}
    zyl_labels: dict[int, str] = {}
    foldbin_fibers: dict[str, set[str]] = defaultdict(set)
    cylinder_fibers: dict[str, set[str]] = defaultdict(set)
    values = []

    for bits in product((0, 1), repeat=9):
        if not no_adjacent_ones(bits):
            continue
        visible = bits[:6]
        tail = bits[6:]
        value = sum(bit * weight for bit, weight in zip(bits, VISIBLE_WEIGHTS + TAIL_WEIGHTS))
        if value > 63:
            continue
        visible_label = "".join(str(bit) for bit in visible)
        tail_offset = sum(bit * weight for bit, weight in zip(tail, TAIL_WEIGHTS))
        tail_label = f"T{tail_offset:02d}"
        fold_labels[value] = visible_label
        zyl_labels[value] = tail_label
        foldbin_fibers[visible_label].add("".join(str(bit) for bit in tail))
        cylinder_fibers[visible_label].add("".join(str(bit) for bit in tail))
        values.append(value)

    fold = [fold_labels[index] for index in range(64)]
    zyl = [zyl_labels[index] for index in range(64)]
    witness = {
        "value_bijection": sorted(values) == list(range(64)),
        "foldbin_equals_zeckendorf_cylinder_by_visible_prefix": foldbin_fibers == cylinder_fibers,
        "tail_offset_support": sorted(set(zyl)),
    }
    return fold, zyl, witness


def reconstruct_codon_partitions() -> tuple[list[str], list[str]]:
    box = [""] * 64
    family = [""] * 64
    for codon in codon_order():
        vertex = codon_to_vertex(codon)
        box[vertex] = "B" + codon[:2]
    seen_codons = set()
    for index, block in enumerate(CODON_FAMILY_BLOCKS):
        label = f"F{index:02d}"
        for codon in block:
            vertex = codon_to_vertex(codon)
            family[vertex] = label
            seen_codons.add(codon)
    if seen_codons != set(codon_order()) or any(label == "" for label in box + family):
        raise RuntimeError("codon family blocks do not partition Q6")
    return box, family


def canonical_labels(labels: list[Hashable]) -> list[int]:
    members: dict[Hashable, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        members[label].append(index)
    ordered = sorted(members, key=lambda label: (min(members[label]), len(members[label]), str(label)))
    relabel = {label: index for index, label in enumerate(ordered)}
    return [relabel[label] for label in labels]


def blocks(labels: list[int]) -> dict[int, list[int]]:
    result: dict[int, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        result[label].append(index)
    return dict(result)


def block_sizes(labels: list[int]) -> list[int]:
    return sorted(len(members) for members in blocks(labels).values())


class DSU:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))

    def find(self, value: int) -> int:
        while self.parent[value] != value:
            self.parent[value] = self.parent[self.parent[value]]
            value = self.parent[value]
        return value

    def union(self, left: int, right: int) -> None:
        root_left = self.find(left)
        root_right = self.find(right)
        if root_left != root_right:
            self.parent[root_right] = root_left


def meet_partition(left: list[int], right: list[int]) -> list[int]:
    return canonical_labels([(a, b) for a, b in zip(left, right)])


def join_partition(left: list[int], right: list[int]) -> list[int]:
    dsu = DSU(len(left))
    for labels in (left, right):
        for members in blocks(labels).values():
            first = members[0]
            for member in members[1:]:
                dsu.union(first, member)
    return canonical_labels([dsu.find(index) for index in range(len(left))])


def entropy(labels: list[int]) -> float:
    total = len(labels)
    return -sum((count / total) * math.log2(count / total) for count in Counter(labels).values())


def variation_of_information(left: list[int], right: list[int]) -> float:
    total = len(left)
    left_counts = Counter(left)
    right_counts = Counter(right)
    joint = Counter(zip(left, right))
    mutual = 0.0
    for (a, b), count in joint.items():
        mutual += (count / total) * math.log2((count * total) / (left_counts[a] * right_counts[b]))
    return entropy(left) + entropy(right) - 2.0 * mutual


def adjacency_from_edges(edges: list[tuple[int, int]], n: int = 64) -> list[list[int]]:
    adjacency = [[] for _ in range(n)]
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    return adjacency


def boundary_profile(labels: list[int], edges: list[tuple[int, int]]) -> list[int]:
    labels = canonical_labels(labels)
    profile = [0 for _ in blocks(labels)]
    for left, right in edges:
        a = labels[left]
        b = labels[right]
        if a != b:
            profile[a] += 1
            profile[b] += 1
    return sorted(profile)


def quotient_laplacian(labels: list[int], edges: list[tuple[int, int]]) -> list[list[int]]:
    labels = canonical_labels(labels)
    k = len(set(labels))
    cross = [[0 for _ in range(k)] for _ in range(k)]
    for left, right in edges:
        a = labels[left]
        b = labels[right]
        if a != b:
            cross[a][b] += 1
            cross[b][a] += 1
    lap = [[0 for _ in range(k)] for _ in range(k)]
    for row in range(k):
        degree = sum(cross[row])
        lap[row][row] = degree
        for col in range(k):
            if row != col:
                lap[row][col] = -cross[row][col]
    return lap


def equitable_defect(labels: list[int], edges: list[tuple[int, int]]) -> dict[str, object]:
    labels = canonical_labels(labels)
    adjacency = adjacency_from_edges(edges)
    by_block = blocks(labels)
    k = len(by_block)
    target_blocks = sorted(by_block)
    total_range = 0
    max_range = 0
    witness = None
    for source in sorted(by_block):
        rows = []
        for vertex in by_block[source]:
            counts = Counter(labels[neighbor] for neighbor in adjacency[vertex])
            rows.append([counts[target] for target in target_blocks])
        for target_index, target in enumerate(target_blocks):
            values = [row[target_index] for row in rows]
            delta = max(values) - min(values)
            total_range += delta
            if delta > max_range:
                max_range = delta
                witness = {"source_block": source, "target_block": target, "range": delta}
    normalized = total_range / (6.0 * k * k) if k else 0.0
    return {
        "total_range": total_range,
        "max_range": max_range,
        "normalized": round(normalized, 12),
        "witness": witness,
    }


def smith_normal_form_diagonal(matrix: list[list[int]]) -> list[int]:
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
            for col in range(cols):
                a[dst][col] += coeff * a[src][col]

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


def partition_summary(labels: list[int], edges: list[tuple[int, int]]) -> dict[str, object]:
    labels = canonical_labels(labels)
    lap = quotient_laplacian(labels, edges)
    snf = smith_normal_form_diagonal(lap)
    return {
        "block_sizes_sorted": block_sizes(labels),
        "block_count": len(set(labels)),
        "boundary_profile": boundary_profile(labels, edges),
        "equitable_defect": equitable_defect(labels, edges),
        "quotient_laplacian_snf": snf,
        "snf_torsion_factors": [value for value in snf if value > 1],
        "snf_free_rank": sum(1 for value in snf if value == 0),
    }


def pair_signature(
    left_raw: list[Hashable],
    right_raw: list[Hashable],
    edges: list[tuple[int, int]],
    names: tuple[str, str],
) -> dict[str, object]:
    left = canonical_labels(left_raw)
    right = canonical_labels(right_raw)
    meet = meet_partition(left, right)
    join = join_partition(left, right)
    parts = {
        names[0]: partition_summary(left, edges),
        names[1]: partition_summary(right, edges),
        "meet": partition_summary(meet, edges),
        "join": partition_summary(join, edges),
    }
    return {
        "partition_names": list(names),
        "VI": round(variation_of_information(left, right), 12),
        "parts": parts,
        "reported_not_scored": {
            "P_block_sizes": parts[names[0]]["block_sizes_sorted"],
            "Q_block_sizes": parts[names[1]]["block_sizes_sorted"],
        },
    }


def vector_distance(left: list[float], right: list[float]) -> float:
    n = max(len(left), len(right))
    padded_left = left + [0.0] * (n - len(left))
    padded_right = right + [0.0] * (n - len(right))
    scale = 1.0 + sum(abs(value) for value in padded_left) + sum(abs(value) for value in padded_right)
    return sum(abs(a - b) for a, b in zip(padded_left, padded_right)) / scale


def log_vector(values: list[int]) -> list[float]:
    return [math.log1p(value) for value in values]


def signature_distances(left: dict[str, object], right: dict[str, object]) -> dict[str, float]:
    left_parts = left["parts"]
    right_parts = right["parts"]
    left_names = list(left["partition_names"]) + ["meet", "join"]
    right_names = list(right["partition_names"]) + ["meet", "join"]
    meet_join = 0.0
    boundary = 0.0
    equitable = 0.0
    snf = 0.0
    for left_name, right_name in zip(left_names, right_names):
        lpart = left_parts[left_name]
        rpart = right_parts[right_name]
        if left_name in ("meet", "join"):
            meet_join += vector_distance(
                [float(value) for value in lpart["block_sizes_sorted"]],
                [float(value) for value in rpart["block_sizes_sorted"]],
            )
        boundary += vector_distance(
            [float(value) for value in lpart["boundary_profile"]],
            [float(value) for value in rpart["boundary_profile"]],
        )
        equitable += abs(
            float(lpart["equitable_defect"]["normalized"])
            - float(rpart["equitable_defect"]["normalized"])
        )
        snf += vector_distance(
            log_vector(list(lpart["quotient_laplacian_snf"])),
            log_vector(list(rpart["quotient_laplacian_snf"])),
        )
    vi = abs(float(left["VI"]) - float(right["VI"])) / 6.0
    components = {
        "meet_join": meet_join / 2.0,
        "VI": vi,
        "equitable_defect": equitable / 4.0,
        "boundary_profile": boundary / 4.0,
        "quotient_snf": snf / 4.0,
    }
    components["total_geometry"] = (
        components["meet_join"]
        + components["VI"]
        + components["equitable_defect"]
        + components["boundary_profile"]
        + components["quotient_snf"]
    )
    return {key: round(value, 12) for key, value in components.items()}


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def empirical_lower_tail(observed: float, values: list[float]) -> dict[str, object]:
    ordered = sorted(values)
    n = len(values)
    return {
        "draws": n,
        "min": round(ordered[0], 12),
        "q05": round(ordered[int(0.05 * (n - 1))], 12),
        "median": round(ordered[int(0.50 * (n - 1))], 12),
        "q95": round(ordered[int(0.95 * (n - 1))], 12),
        "max": round(ordered[-1], 12),
        "mean": round(sum(values) / n, 12),
        "p_value_lower": (sum(1 for value in values if value <= observed + 1e-12) + 1) / (n + 1),
    }


def null_report(
    target: dict[str, object],
    left_sizes: list[int],
    right_sizes: list[int],
    names: tuple[str, str],
    edges: list[tuple[int, int]],
    observed: dict[str, float],
    rng: random.Random,
) -> dict[str, object]:
    component_values: dict[str, list[float]] = {key: [] for key in observed}
    for _ in range(NULL_DRAWS):
        left = random_partition_by_sizes(left_sizes, rng)
        right = random_partition_by_sizes(right_sizes, rng)
        sigma = pair_signature(left, right, edges, names)
        distances = signature_distances(target, sigma)
        for key, value in distances.items():
            component_values[key].append(value)
    return {
        key: empirical_lower_tail(observed[key], values)
        for key, values in component_values.items()
    }


def q6_automorphism_with_map(labels: list[Hashable], axes: list[int], flips: list[int]) -> list[Hashable]:
    transformed = [None for _ in range(64)]
    for vertex, label in enumerate(labels):
        bits = list(vertex_bits(vertex))
        image_bits = [bits[axes[index]] ^ flips[index] for index in range(6)]
        transformed[int_from_bits(image_bits)] = label
    return list(transformed)


def random_q6_automorphism(labels: list[Hashable], rng: random.Random) -> list[Hashable]:
    axes = list(range(6))
    rng.shuffle(axes)
    flips = [rng.randrange(2) for _ in range(6)]
    return q6_automorphism_with_map(labels, axes, flips)


def check_row(name: str, ok: bool, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": bool(ok), "observed": observed, "expected": expected}


def status_from_nulls(nulls: dict[str, object]) -> tuple[str, str]:
    critical = ("meet_join", "equitable_defect", "boundary_profile", "quotient_snf")
    p_codon = {
        key: float(nulls["codon_preserve_box_family_sizes"][key]["p_value_lower"])
        for key in critical + ("total_geometry",)
    }
    p_window = {
        key: float(nulls["window_preserve_fold_zyl_sizes"][key]["p_value_lower"])
        for key in critical + ("total_geometry",)
    }
    certified = (
        p_codon["total_geometry"] <= 0.05
        and p_window["total_geometry"] <= 0.05
        and all(p_codon[key] <= 0.10 and p_window[key] <= 0.10 for key in critical)
    )
    refuted = (
        p_codon["meet_join"] > 0.25
        and p_window["meet_join"] > 0.25
        and p_codon["boundary_profile"] > 0.25
        and p_window["boundary_profile"] > 0.25
    )
    if certified:
        return "certified", "geometry falls in the extreme lower tail on both size-preserving null sides"
    if refuted:
        return "refuted", "meet/join and boundary-profile geometry are not lower-tail special on either null side"
    return "coincidence", "some structure is visible, but the full meet/join-boundary-equitable-SNF certificate is incomplete"


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    edges = q6_edges()
    window_fold, window_zyl, window_witness = reconstruct_window_partitions()
    codon_box, codon_family = reconstruct_codon_partitions()

    sigma_window = pair_signature(window_fold, window_zyl, edges, ("fold", "zyl"))
    sigma_codon = pair_signature(codon_box, codon_family, edges, ("box", "family"))
    observed_distances = signature_distances(sigma_window, sigma_codon)

    auto_rng = random.Random(RANDOM_SEED + 1)
    auto_axes = list(range(6))
    auto_rng.shuffle(auto_axes)
    auto_flips = [auto_rng.randrange(2) for _ in range(6)]
    codon_box_auto = q6_automorphism_with_map(codon_box, auto_axes, auto_flips)
    codon_family_auto = q6_automorphism_with_map(codon_family, auto_axes, auto_flips)
    sigma_codon_auto = pair_signature(codon_box_auto, codon_family_auto, edges, ("box", "family"))

    checks = [
        check_row("q6_edge_count", len(edges) == 192, len(edges), 192),
        check_row("window_value_bijection_0_to_63", bool(window_witness["value_bijection"]), True, True),
        check_row(
            "window_foldbin_equals_zeckendorf_cylinder_by_visible_prefix",
            bool(window_witness["foldbin_equals_zeckendorf_cylinder_by_visible_prefix"]),
            True,
            True,
        ),
        check_row(
            "window_fold_fiber_histogram",
            dict(sorted(Counter(Counter(window_fold).values()).items())) == {2: 8, 3: 4, 4: 9},
            dict(sorted(Counter(Counter(window_fold).values()).items())),
            {2: 8, 3: 4, 4: 9},
        ),
        check_row(
            "window_zyl_block_sizes",
            block_sizes(canonical_labels(window_zyl)) == [9, 13, 21, 21],
            block_sizes(canonical_labels(window_zyl)),
            [9, 13, 21, 21],
        ),
        check_row(
            "codon_box_block_sizes",
            block_sizes(canonical_labels(codon_box)) == [4] * 16,
            block_sizes(canonical_labels(codon_box)),
            [4] * 16,
        ),
        check_row(
            "codon_family_size_histogram_unlabeled",
            dict(sorted(Counter(Counter(codon_family).values()).items())) == {1: 2, 2: 9, 3: 2, 4: 5, 6: 3},
            dict(sorted(Counter(Counter(codon_family).values()).items())),
            {1: 2, 2: 9, 3: 2, 4: 5, 6: 3},
        ),
        check_row(
            "codon_family_labels_are_unlabeled",
            all(label.startswith("F") for label in set(codon_family)),
            sorted(set(codon_family))[:4],
            "all labels start with F",
        ),
        check_row(
            "snf_self_check",
            smith_normal_form_diagonal([[2, 4], [6, 8]]) == [2, 4],
            smith_normal_form_diagonal([[2, 4], [6, 8]]),
            [2, 4],
        ),
        check_row(
            "codon_q6_automorphism_invariance",
            signature_distances(sigma_codon, sigma_codon_auto)["total_geometry"] == 0.0,
            signature_distances(sigma_codon, sigma_codon_auto)["total_geometry"],
            0.0,
        ),
    ]

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            sigma_window=sigma_window,
            sigma_codon=sigma_codon,
            nulls={},
            checks=checks,
            note="self-check failed before null interpretation",
        )

    window_fold_sizes = block_sizes(canonical_labels(window_fold))
    window_zyl_sizes = block_sizes(canonical_labels(window_zyl))
    codon_box_sizes = block_sizes(canonical_labels(codon_box))
    codon_family_sizes = block_sizes(canonical_labels(codon_family))

    nulls = {
        "codon_preserve_box_family_sizes": null_report(
            sigma_window,
            codon_box_sizes,
            codon_family_sizes,
            ("box_null", "family_null"),
            edges,
            observed_distances,
            rng,
        ),
        "window_preserve_fold_zyl_sizes": null_report(
            sigma_codon,
            window_fold_sizes,
            window_zyl_sizes,
            ("fold_null", "zyl_null"),
            edges,
            observed_distances,
            rng,
        ),
        "scoring_contract": {
            "block_count_used_for_status": False,
            "raw_P_Q_block_sizes_reported_only": True,
            "tail": "lower distance is more bridge-like",
            "draws_per_side": NULL_DRAWS,
        },
    }
    status, reason = status_from_nulls(nulls)
    note = (
        VENDOR_NOTE
        + " Verdict reason: "
        + reason
        + ". The distance score excludes raw P/Q block-size equality and therefore does not certify a 64-to-21 count match."
    )
    emit(
        status,
        sigma_window=sigma_window,
        sigma_codon=sigma_codon,
        distances=observed_distances,
        nulls=nulls,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

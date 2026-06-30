#!/usr/bin/env python3
"""BC16/BC17 halfbox extremality and strict Fibonacci-tower audit.

The codon family partition is represented only as 21 unlabeled fibers.  The
audit uses the H(3,4) codon micrograph, coordinate partitions, wobble R/Y
partitions, and meet/join operations on finite partitions.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, product
import json
import random
import sys
from typing import Hashable, Iterable


EXPERIMENT_ID = "bc1617_halfbox_fibonacci_tower"
CLAIM_ID = "bridge.genetic_code.halfbox_fibonacci_tower"
RANDOM_SEED = 161734
NULL_DRAWS = 1000
K1_DRAWS = 300
K1_STEPS = 220

BASES = ("U", "C", "A", "G")
RY_CLASS = {"U": "Y", "C": "Y", "A": "R", "G": "R"}
FIBONACCI_TARGETS = (13, 21, 34, 55)

# Unlabeled standard-code fibers.  The local F labels are assigned at runtime;
# these tuples are only the block membership data on the 64 codon carrier.
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


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def h34_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    for codon in codons:
        left = index[codon]
        for position in range(3):
            for base in BASES:
                if base == codon[position]:
                    continue
                other = codon[:position] + base + codon[position + 1 :]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


def canonical_labels(labels: Iterable[Hashable]) -> list[int]:
    label_list = list(labels)
    members: dict[Hashable, list[int]] = defaultdict(list)
    for index, label in enumerate(label_list):
        members[label].append(index)
    ordered = sorted(members, key=lambda label: (min(members[label]), len(members[label]), str(label)))
    relabel = {label: index for index, label in enumerate(ordered)}
    return [relabel[label] for label in label_list]


def key(labels: list[int]) -> tuple[int, ...]:
    return tuple(canonical_labels(labels))


def blocks(labels: list[int]) -> dict[int, list[int]]:
    result: dict[int, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        result[label].append(index)
    return dict(result)


def block_count(labels: list[int]) -> int:
    return len(set(labels))


def size_profile(labels: list[int]) -> dict[int, int]:
    return dict(sorted(Counter(len(members) for members in blocks(labels).values()).items()))


def internal_edges(labels: list[int], edges: Iterable[tuple[int, int]]) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def profile_edge_upper(labels: list[int]) -> int:
    upper_by_size = {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}
    return sum(upper_by_size[len(members)] for members in blocks(labels).values())


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
    return canonical_labels((a, b) for a, b in zip(left, right))


def join_partition(left: list[int], right: list[int]) -> list[int]:
    dsu = DSU(len(left))
    for labels in (left, right):
        for members in blocks(labels).values():
            first = members[0]
            for member in members[1:]:
                dsu.union(first, member)
    return canonical_labels(dsu.find(index) for index in range(len(left)))


def coordinate_partition(codons: list[str], positions: tuple[int, ...]) -> list[int]:
    return canonical_labels(tuple(codon[position] for position in positions) for codon in codons)


def ry_partition(codons: list[str], position: int) -> list[int]:
    return canonical_labels(RY_CLASS[codon[position]] for codon in codons)


def family_partition(codons: list[str]) -> list[int]:
    labels = [-1] * len(codons)
    index = {codon: pos for pos, codon in enumerate(codons)}
    seen: set[str] = set()
    for block_index, block in enumerate(CODON_FAMILY_BLOCKS):
        for codon in block:
            labels[index[codon]] = block_index
            seen.add(codon)
    if seen != set(codons) or any(label < 0 for label in labels):
        raise RuntimeError("family blocks do not partition the codon carrier")
    return canonical_labels(labels)


def seed_partitions(codons: list[str], family: list[int]) -> dict[str, list[int]]:
    p1 = coordinate_partition(codons, (0,))
    p2 = coordinate_partition(codons, (1,))
    p3 = coordinate_partition(codons, (2,))
    p12 = coordinate_partition(codons, (0, 1))
    p13 = coordinate_partition(codons, (0, 2))
    p23 = coordinate_partition(codons, (1, 2))
    ry1 = ry_partition(codons, 0)
    ry2 = ry_partition(codons, 1)
    ry3 = ry_partition(codons, 2)
    h = meet_partition(p12, ry3)
    return {
        "P1": p1,
        "P2": p2,
        "P3": p3,
        "P12": p12,
        "P13": p13,
        "P23": p23,
        "RY1": ry1,
        "RY2": ry2,
        "RY3": ry3,
        "H": h,
        "F": family,
    }


def generated_pairwise_partitions(seeds: dict[str, list[int]]) -> dict[tuple[int, ...], dict[str, object]]:
    generated: dict[tuple[int, ...], dict[str, object]] = {}

    def add(name: str, labels: list[int]) -> None:
        partition_key = key(labels)
        if partition_key not in generated:
            generated[partition_key] = {
                "labels": list(partition_key),
                "block_count": block_count(list(partition_key)),
                "operations": [],
            }
        operations = generated[partition_key]["operations"]
        assert isinstance(operations, list)
        operations.append(name)

    for name, labels in seeds.items():
        add(name, labels)
    for left_name, right_name in combinations(sorted(seeds), 2):
        left = seeds[left_name]
        right = seeds[right_name]
        add(f"{left_name} meet {right_name}", meet_partition(left, right))
        add(f"{left_name} join {right_name}", join_partition(left, right))
    return generated


def refines(fine: list[int], coarse: list[int]) -> bool:
    mapping: dict[int, int] = {}
    for a, b in zip(fine, coarse):
        if a in mapping and mapping[a] != b:
            return False
        mapping[a] = b
    return True


def strict_fib_chain_score(generated: dict[tuple[int, ...], dict[str, object]]) -> int:
    fib_parts = [
        (int(row["block_count"]), list(row["labels"]))
        for row in generated.values()
        if int(row["block_count"]) in FIBONACCI_TARGETS
    ]
    fib_parts.sort(key=lambda item: item[0])
    best = [1 for _ in fib_parts]
    for right in range(len(fib_parts)):
        for left in range(right):
            left_count, left_labels = fib_parts[left]
            right_count, right_labels = fib_parts[right]
            if left_count < right_count and refines(right_labels, left_labels):
                best[right] = max(best[right], best[left] + 1)
    return max(best, default=0)


def natural_appearance(generated: dict[tuple[int, ...], dict[str, object]]) -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    by_count: dict[int, list[str]] = defaultdict(list)
    for row in generated.values():
        count = int(row["block_count"])
        operations = [str(name) for name in row["operations"]]
        by_count[count].extend(operations)

    for target in FIBONACCI_TARGETS:
        operations = sorted(by_count.get(target, []))
        if operations:
            rows[str(target)] = {
                "natural": True,
                "operations": operations,
                "closest": [],
            }
            continue
        distances = sorted((abs(count - target), count) for count in by_count)
        nearest_distance = distances[0][0]
        nearest_counts = sorted({count for distance, count in distances if distance == nearest_distance})
        closest: list[dict[str, object]] = []
        for count in nearest_counts:
            closest.append({"block_count": count, "operations": sorted(by_count[count])[:8]})
        rows[str(target)] = {"natural": False, "operations": [], "closest": closest}
    return rows


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def null_tail_p(observed: int, values: list[int], tail: str) -> float:
    if tail == "upper":
        hits = sum(1 for value in values if value >= observed)
    else:
        hits = sum(1 for value in values if value <= observed)
    return (hits + 1) / (len(values) + 1)


def sample_k0_null(k_labels: list[int], edges: list[tuple[int, int]], rng: random.Random) -> dict[str, object]:
    observed = internal_edges(k_labels, edges)
    sizes = sorted((len(members) for members in blocks(k_labels).values()), reverse=True)
    values = [internal_edges(random_partition_by_sizes(sizes, rng), edges) for _ in range(NULL_DRAWS)]
    return {
        "model": "random partition with K block-size profile 2^30,1^4",
        "draws": len(values),
        "observed": observed,
        "max_possible": profile_edge_upper(k_labels),
        "sample_min": min(values),
        "sample_max": max(values),
        "p_e_in_ge_observed": null_tail_p(observed, values, "upper"),
    }


def sample_k1_null(
    family: list[int],
    halfbox: list[int],
    edges: list[tuple[int, int]],
    rng: random.Random,
) -> dict[str, object]:
    current = family[:]
    current_edges = internal_edges(current, edges)
    values_size: list[int] = []
    values_extreme: list[int] = []
    accepted = 0
    threshold = 69
    for _ in range(K1_DRAWS):
        for _ in range(K1_STEPS):
            left = rng.randrange(len(current))
            right = rng.randrange(len(current))
            if current[left] == current[right]:
                continue
            candidate = current[:]
            candidate[left], candidate[right] = candidate[right], candidate[left]
            candidate_edges = internal_edges(candidate, edges)
            if candidate_edges >= threshold:
                current = candidate
                current_edges = candidate_edges
                accepted += 1
        meet = meet_partition(halfbox, current)
        meet_edges = internal_edges(meet, edges)
        values_size.append(block_count(meet))
        values_extreme.append(int(block_count(meet) == 34 and meet_edges == profile_edge_upper(meet)))
    event_hits = sum(values_extreme)
    return {
        "model": "fixed H; label-swap walk preserving family size profile and e_in(F') >= 69",
        "draws": K1_DRAWS,
        "steps_per_draw": K1_STEPS,
        "accepted_swaps": accepted,
        "final_e_in_F_prime": current_edges,
        "observed_meet_size": 34,
        "p_meet_size_eq_34_and_tau_eq_1": (event_hits + 1) / (K1_DRAWS + 1),
        "meet_size_histogram": dict(sorted(Counter(values_size).items())),
    }


def sample_tower_null(
    codons: list[str],
    family: list[int],
    observed_score: int,
    rng: random.Random,
) -> dict[str, object]:
    sizes = sorted((len(members) for members in blocks(family).values()), reverse=True)
    scores: list[int] = []
    full_hits = 0
    for _ in range(NULL_DRAWS):
        random_family = random_partition_by_sizes(sizes, rng)
        generated = generated_pairwise_partitions(seed_partitions(codons, random_family))
        present = {int(row["block_count"]) for row in generated.values()}
        score = sum(1 for target in FIBONACCI_TARGETS if target in present)
        scores.append(score)
        full_hits += int(all(target in present for target in FIBONACCI_TARGETS))
    return {
        "model": "random unlabeled family partition with the standard family size profile; canonical seeds plus pairwise meet/join",
        "draws": len(scores),
        "observed_score": observed_score,
        "score_histogram": dict(sorted(Counter(scores).items())),
        "p_score_ge_observed": null_tail_p(observed_score, scores, "upper"),
        "p_full_tower": (full_hits + 1) / (NULL_DRAWS + 1),
    }


def known_layer_checks(generated: dict[tuple[int, ...], dict[str, object]]) -> list[dict[str, object]]:
    by_operation: dict[str, int] = {}
    for row in generated.values():
        count = int(row["block_count"])
        for operation in row["operations"]:
            by_operation[str(operation)] = count
    return [
        check_row("B_size_P12", by_operation.get("P12"), 16),
        check_row("F_size", by_operation.get("F"), 21),
        check_row("M_size_P12_meet_F", by_operation.get("F meet P12"), 25),
        check_row("H_size", by_operation.get("H"), 32),
        check_row("K_size_H_meet_F", by_operation.get("F meet H"), 34),
        check_row("B_join_F_size", by_operation.get("F join P12"), 12),
        check_row("H_join_F_size", by_operation.get("F join H"), 19),
        check_row("F_meet_P3_size", by_operation.get("F meet P3"), 57),
    ]


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    codons = codon_order()
    edges = h34_edges(codons)
    family = family_partition(codons)
    seeds = seed_partitions(codons, family)
    halfbox = seeds["H"]
    k_partition = meet_partition(halfbox, family)
    generated = generated_pairwise_partitions(seeds)
    appearance = natural_appearance(generated)
    observed_tower_score = sum(
        1 for target in FIBONACCI_TARGETS if appearance[str(target)]["natural"]
    )
    chain_score = strict_fib_chain_score(generated)

    h_e_in = internal_edges(halfbox, edges)
    k_e_in = internal_edges(k_partition, edges)
    h_upper = profile_edge_upper(halfbox)
    k_upper = profile_edge_upper(k_partition)
    tau_h = 1.0 if h_e_in == h_upper and h_upper > 0 else None
    tau_k = 1.0 if k_e_in == k_upper and k_upper > 0 else None

    checks = [
        check_row("codon_count", len(codons), 64),
        check_row("h34_edge_count", len(edges), 288),
        check_row("family_count", block_count(family), 21),
        check_row("family_size_profile", size_profile(family), {1: 2, 2: 9, 3: 2, 4: 5, 6: 3}),
        check_row("family_e_in", internal_edges(family, edges), 69),
        check_row("family_profile_edge_upper", profile_edge_upper(family), 72),
        check_row("H_size", block_count(halfbox), 32),
        check_row("H_size_profile", size_profile(halfbox), {2: 32}),
        check_row("H_e_in", h_e_in, 32),
        check_row("H_e_max", h_upper, 32),
        check_row("K_size", block_count(k_partition), 34),
        check_row("K_size_profile", size_profile(k_partition), {1: 4, 2: 30}),
        check_row("K_e_in", k_e_in, 30),
        check_row("K_e_max", k_upper, 30),
        check_row("tau_H", tau_h, 1.0),
        check_row("tau_K", tau_k, 1.0),
    ]
    checks.extend(known_layer_checks(generated))

    k0_null = sample_k0_null(k_partition, edges, rng)
    k1_null = sample_k1_null(family, halfbox, edges, rng)
    tower_null = sample_tower_null(codons, family, observed_tower_score, rng)
    tower_null_p = float(tower_null["p_score_ge_observed"])

    all_checks_ok = all(bool(row["ok"]) for row in checks)
    all_fib_natural = all(appearance[str(target)]["natural"] for target in FIBONACCI_TARGETS)
    certified = (
        all_checks_ok
        and tau_h == 1.0
        and tau_k == 1.0
        and all_fib_natural
        and chain_score == len(FIBONACCI_TARGETS)
        and tower_null_p <= 0.05
    )

    if not all_checks_ok:
        status = "needs_derivation"
        note = "self-check failed before the BC16/BC17 verdict"
    elif tau_k != 1.0:
        status = "refuted"
        note = "K=H meet F is not an exact halfbox-fragment endpoint"
    elif certified:
        status = "certified"
        note = "BC16 exact extremality and BC17 full natural Fibonacci tower are both certified"
    else:
        status = "coincidence"
        note = (
            "BC16 exact halfbox extremality is a hard endpoint fact; BC17 is not "
            "a certified Fibonacci tower because only 21 and 34 appear naturally "
            "under the preregistered canonical operations"
        )

    emit(
        status,
        tau_H=tau_h,
        tau_K=tau_k,
        H_size=block_count(halfbox),
        K_size=block_count(k_partition),
        e_in_H=h_e_in,
        e_in_K=k_e_in,
        e_max_H=h_upper,
        e_max_K=k_upper,
        fibonacci_natural_appearance=appearance,
        strict_comparable_chain_score=chain_score,
        tower_null_p=tower_null_p,
        nulls={
            "K0_same_K_size_profile": k0_null,
            "K1_fixed_H_edge_conditioned_family": k1_null,
            "T0_family_size_profile_tower": tower_null,
        },
        generated_nontrivial_block_counts=sorted(
            count
            for count in {int(row["block_count"]) for row in generated.values()}
            if 1 < count < 64
        ),
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

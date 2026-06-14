#!/usr/bin/env python3
"""BC15 fold-layer zig-zag edge-hiding extremality certificate.

The certificate is deliberately narrow.  It fixes the standard codon family
partition and the first-two-base box partition on H(3,4), then evaluates the
label-free internal-edge functional on the zig-zag

    B <- M = B meet F -> F.

It does not claim a monotone quotient tower, an isomorphism, biological
forcing, or live-usage evidence.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
import math
import random
import sys
from typing import Hashable, Iterable


EXPERIMENT_ID = "bc15_foldlayer_zigzag_extremality"
CLAIM_ID = "bridge.genetic_code.foldlayer_zigzag_extremality"
RANDOM_SEED = 150615
NULL_DRAWS = 4000

BASES = ("U", "C", "A", "G")

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

H34_BLOCK_UPPER = {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def h34_edges() -> tuple[list[tuple[int, int]], list[tuple[int, int, int]]]:
    edges: list[tuple[int, int]] = []
    positioned: list[tuple[int, int, int]] = []
    for a, b, c in product(range(4), repeat=3):
        left = 16 * a + 4 * b + c
        for position in range(3):
            coords = [a, b, c]
            for value in range(4):
                if coords[position] == value:
                    continue
                other = coords[:]
                other[position] = value
                right = 16 * other[0] + 4 * other[1] + other[2]
                if left < right:
                    edges.append((left, right))
                    positioned.append((left, right, position + 1))
    return edges, positioned


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


def block_upper_bound(sizes: list[int]) -> int | None:
    total = 0
    for size in sizes:
        if size not in H34_BLOCK_UPPER:
            return None
        total += H34_BLOCK_UPPER[size]
    return total


def line_clique_upper_bound(sizes: list[int]) -> int:
    return sum(size * (size - 1) // 2 for size in sizes)


def tau(observed: int, e_min: int, e_max: int) -> float | None:
    if e_max == e_min:
        return None
    return (observed - e_min) / (e_max - e_min)


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def null_stats(observed: int, values: list[int], tail: str) -> dict[str, object]:
    sorted_values = sorted(values)
    mean = sum(values) / len(values)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1) if len(values) > 1 else 0.0
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


def sample_same_profile_null(
    edges: list[tuple[int, int]],
    sizes: list[int],
    observed: int,
    rng: random.Random,
) -> dict[str, object]:
    values = [e_in(random_partition_by_sizes(sizes, rng), edges) for _ in range(NULL_DRAWS)]
    stats = null_stats(observed, values, "upper")
    stats["model"] = "uniform label permutation preserving only the 25-block M size profile"
    stats["endpoint_is_absolute_upper"] = observed == line_clique_upper_bound(sizes)
    return stats


def random_box_conditioned_m_labels(
    box_to_vertices: dict[str, list[int]],
    box_to_fragment_sizes: dict[str, list[int]],
    rng: random.Random,
) -> list[str]:
    labels = [""] * 64
    for box in sorted(box_to_vertices):
        vertices = box_to_vertices[box][:]
        rng.shuffle(vertices)
        cursor = 0
        for local_block, size in enumerate(box_to_fragment_sizes[box]):
            label = f"{box}:{local_block}"
            for vertex in vertices[cursor:cursor + size]:
                labels[vertex] = label
            cursor += size
    if any(label == "" for label in labels):
        raise RuntimeError("incomplete box-conditioned M partition")
    return labels


def sample_box_conditioned_null(
    edges: list[tuple[int, int]],
    box_to_vertices: dict[str, list[int]],
    box_to_fragment_sizes: dict[str, list[int]],
    observed: int,
    rng: random.Random,
) -> dict[str, object]:
    values = [
        e_in(random_box_conditioned_m_labels(box_to_vertices, box_to_fragment_sizes, rng), edges)
        for _ in range(NULL_DRAWS)
    ]
    stats = null_stats(observed, values, "upper")
    stats["model"] = (
        "fixed first-two-base boxes; each box is randomly cut with the observed "
        "local fragment size profile, without family labels"
    )
    stats["all_draws_endpoint"] = min(values) == observed and max(values) == observed
    return stats


def labels_to_blocks(labels: list[Hashable]) -> dict[Hashable, list[int]]:
    blocks: dict[Hashable, list[int]] = defaultdict(list)
    for vertex, label in enumerate(labels):
        blocks[label].append(vertex)
    return blocks


def edge_count_between(left: list[int], right: list[int], edge_set: set[tuple[int, int]]) -> int:
    count = 0
    for a in left:
        for b in right:
            edge = (a, b) if a < b else (b, a)
            if edge in edge_set:
                count += 1
    return count


def family_merge_increment(
    family_labels: list[str],
    meet_labels: list[tuple[str, str]],
    edges: list[tuple[int, int]],
) -> int:
    return e_in(family_labels, edges) - e_in(meet_labels, edges)


def exact_f_given_m_null(
    meet_labels: list[tuple[str, str]],
    edges: list[tuple[int, int]],
    observed_increment: int,
) -> dict[str, object]:
    blocks = labels_to_blocks(meet_labels)
    fragments = sorted(blocks, key=lambda label: (len(blocks[label]), str(label)))
    sizes = {index: len(blocks[label]) for index, label in enumerate(fragments)}
    edge_set = set(edges)
    between: dict[tuple[int, int], int] = {}
    for left, right in combinations(range(len(fragments)), 2):
        between[(left, right)] = edge_count_between(blocks[fragments[left]], blocks[fragments[right]], edge_set)

    by_size: dict[int, list[int]] = defaultdict(list)
    for index, size in sizes.items():
        by_size[size].append(index)

    values: Counter[int] = Counter()
    total = 0
    size4 = by_size[4]
    size2 = by_size[2]
    size1 = by_size[1]
    for fours in combinations(size4, 3):
        for twos_for_sixes in combinations(size2, 3):
            remaining_twos = [item for item in size2 if item not in twos_for_sixes]
            for paired_twos in permutations(twos_for_sixes):
                six_increment = 0
                for four, two in zip(fours, paired_twos):
                    edge = (four, two) if four < two else (two, four)
                    six_increment += between[edge]
                for two in remaining_twos:
                    for one in size1:
                        edge = (one, two) if one < two else (two, one)
                        values[six_increment + between[edge]] += 1
                        total += 1

    expanded: list[int] = []
    for value, count in values.items():
        expanded.extend([value] * count)
    stats = null_stats(observed_increment, expanded, "upper")
    stats["draws"] = total
    stats["model"] = (
        "exact coarsening null from 25 M fragments to the observed 21-family size "
        "profile: three 4+2 merges and one 2+1 merge"
    )
    stats["support_counts"] = dict(sorted(values.items()))
    stats["exact_enumeration"] = True
    return stats


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[dict[str, object]] = []

    codons = codon_order()
    edges, positioned_edges = h34_edges()
    box_labels = [codon[:2] for codon in codons]
    family_labels = [CODON_TO_FAMILY[codon] for codon in codons]
    meet_labels = [(box_labels[index], family_labels[index]) for index in range(len(codons))]

    box_sizes = sizes_from_labels(box_labels)
    family_sizes = sizes_from_labels(family_labels)
    meet_sizes = sizes_from_labels(meet_labels)

    e_in_box = e_in(box_labels, edges)
    e_in_meet = e_in(meet_labels, edges)
    e_in_family = e_in(family_labels, edges)

    box_e_min = 0
    meet_e_min = 0
    family_e_min = 0
    box_e_max = line_clique_upper_bound(box_sizes)
    meet_e_max = line_clique_upper_bound(meet_sizes)
    family_e_max = block_upper_bound(family_sizes)

    family_axis = e_in_by_position(family_labels, positioned_edges)
    meet_axis = e_in_by_position(meet_labels, positioned_edges)
    box_axis = e_in_by_position(box_labels, positioned_edges)
    merge_increment = family_merge_increment(family_labels, meet_labels, edges)

    blocks_by_box = labels_to_blocks(box_labels)
    meet_blocks = labels_to_blocks(meet_labels)
    box_to_fragment_sizes: dict[str, list[int]] = defaultdict(list)
    for box, family in meet_blocks:
        box_to_fragment_sizes[box].append(len(meet_blocks[(box, family)]))
    box_to_fragment_sizes = {box: sorted(sizes, reverse=True) for box, sizes in box_to_fragment_sizes.items()}

    tau_box = tau(e_in_box, box_e_min, box_e_max)
    tau_meet = tau(e_in_meet, meet_e_min, meet_e_max)
    tau_family = tau(e_in_family, family_e_min, int(family_e_max) if family_e_max is not None else -1)

    checks.extend([
        check_row("codon_count", len(codons), 64),
        check_row("codon_family_table_count", len(CODON_TO_FAMILY), 64),
        check_row("h34_edge_count", len(edges), 288),
        check_row("h34_degree_ledger", 2 * len(edges), 64 * 9),
        check_row("box_block_count", len(set(box_labels)), 16),
        check_row("box_size_profile", size_histogram(box_labels), {4: 16}),
        check_row("box_e_in", e_in_box, 96),
        check_row("box_e_max", box_e_max, 96),
        check_row("box_tau", tau_box, 1.0),
        check_row("meet_block_count", len(set(meet_labels)), 25),
        check_row("meet_size_profile", size_histogram(meet_labels), {1: 3, 2: 13, 3: 1, 4: 8}),
        check_row("meet_e_in", e_in_meet, 64),
        check_row("meet_e_max", meet_e_max, 64),
        check_row("meet_tau", tau_meet, 1.0),
        check_row("family_block_count", len(set(family_labels)), 21),
        check_row("family_size_profile", size_histogram(family_labels), {1: 2, 2: 9, 3: 2, 4: 5, 6: 3}),
        check_row("family_e_in", e_in_family, 69),
        check_row("family_e_max", family_e_max, 72),
        check_row("family_tau_rounded", round(float(tau_family), 4) if tau_family is not None else None, 0.9583),
        check_row("box_e_in_by_position", box_axis, {3: 96}),
        check_row("meet_e_in_by_position", meet_axis, {3: 64}),
        check_row("family_e_in_by_position", family_axis, {1: 4, 2: 1, 3: 64}),
        check_row("family_minus_meet_increment", merge_increment, 5),
        check_row("r_retain_numerator_denominator", [e_in_meet, e_in_box], [64, 96]),
        check_row("r_cross_numerator_denominator", [e_in_family - e_in_meet, int(family_e_max) - e_in_meet], [5, 8]),
        check_row(
            "box_local_fragment_profiles",
            dict(sorted((box, tuple(sizes)) for box, sizes in box_to_fragment_sizes.items())),
            {
                "AA": (2, 2), "AC": (4,), "AG": (2, 2), "AU": (3, 1),
                "CA": (2, 2), "CC": (4,), "CG": (4,), "CU": (4,),
                "GA": (2, 2), "GC": (4,), "GG": (4,), "GU": (4,),
                "UA": (2, 2), "UC": (4,), "UG": (2, 1, 1), "UU": (2, 2),
            },
        ),
    ])

    if family_e_max is None or not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            T_codon=None,
            tau_B=tau_box,
            tau_M=tau_meet,
            tau_F=tau_family,
            e_in={"B": e_in_box, "M": e_in_meet, "F": e_in_family},
            r_retain="2/3",
            r_cross="5/8",
            null_M0_p=None,
            null_M1_p=None,
            null_FgivenM_p=None,
            checks=checks,
            note="Self-check failed before the BC15 certificate gate.",
        )

    null_m0 = sample_same_profile_null(edges, meet_sizes, e_in_meet, rng)
    null_m1 = sample_box_conditioned_null(edges, blocks_by_box, box_to_fragment_sizes, e_in_meet, rng)
    null_f_given_m = exact_f_given_m_null(meet_labels, edges, merge_increment)

    certified = (
        tau_box == 1.0
        and tau_meet == 1.0
        and tau_family is not None
        and round(tau_family, 4) == 0.9583
        and e_in_family == e_in_meet + 5
        and null_m0["p_value"] <= 0.01
        and bool(null_m1["all_draws_endpoint"])
        and null_f_given_m["p_value"] <= 0.10
    )
    if certified:
        status = "certified"
        note = (
            "Certified zig-zag extremality, not a monotone quotient tower: 64->16 "
            "box and 64->25 box-family fragments are exact edge-hiding extrema; "
            "the 21-family layer is near-max with deficit 3. The ratios 2/3 and "
            "5/8 are honest ratio-of-edge-counts only, not Fibonacci evidence. "
            "The exact F|M coarsening null puts the final merge in the upper "
            "tail at the 10% level. No isomorphism, biological forcing, or "
            "live-usage claim is made."
        )
    elif tau_box == 1.0 or tau_meet == 1.0 or (tau_family is not None and tau_family >= 0.95):
        status = "coincidence"
        note = (
            "At least one layer retains the edge-hiding pattern, but the full "
            "BC15 zig-zag gate is not certified."
        )
    else:
        status = "refuted"
        note = "The B/M/F fold-layer edge-hiding extremality gate is not met."

    emit(
        status,
        T_codon=[1, 1, 0.9583],
        tau_B=tau_box,
        tau_M=tau_meet,
        tau_F=round(float(tau_family), 4) if tau_family is not None else None,
        e_in={"B": e_in_box, "M": e_in_meet, "F": e_in_family},
        e_max={"B": box_e_max, "M": meet_e_max, "F": family_e_max},
        e_min={"B": box_e_min, "M": meet_e_min, "F": family_e_min},
        deficit_F=int(family_e_max) - e_in_family,
        r_retain="2/3",
        r_cross="5/8",
        ratio_interpretation="ratio-of-edge-counts; honest, non-forcing",
        null_M0_p=null_m0["p_value"],
        null_M1_p=null_m1["p_value"],
        null_FgivenM_p=null_f_given_m["p_value"],
        nulls={
            "M0_same_fragment_size_profile": null_m0,
            "M1_box_conditioned_local_profiles": null_m1,
            "F_given_M_exact_family_size_coarsening": null_f_given_m,
        },
        zig_zag={
            "B_not_nested_in_F": True,
            "F_not_nested_in_B": True,
            "shape": "B <- M=B meet F -> F",
            "monotone_quotient_tower": False,
        },
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

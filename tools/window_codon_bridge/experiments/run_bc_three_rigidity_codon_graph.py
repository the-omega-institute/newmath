#!/usr/bin/env python3
"""Window6 three-rigidity graph against the codon family quotient graph.

The experiment is deliberately label-free.  It compares the quotient simple
graphs by invariants that survive arbitrary node relabeling: size, degree
sequence, distance distribution, automorphism order, WL discreteness, and the
exact adjacency characteristic polynomial.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from itertools import product
import json
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "bc_three_rigidity_codon_graph"
CLAIM_ID = "bridge.window6_codon_q6.three_rigidity_codon_graph"
RANDOM_SEED = 612021
NULL_DRAWS = 2200
SWAPS_PER_DRAW = 650

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)

# Entry n gives the visible six-prefix of the no-adjacent nine-bit
# Zeckendorf representative of n in the 0..63 value window.  This is the same
# finite Fold6 vendor table used by the local BC6/BC7 scripts.
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


def flat(rows: list[list[str]]) -> list[str]:
    return [item for row in rows for item in row]


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def reconstruct_window_from_rules() -> list[str]:
    labels: dict[int, str] = {}
    for bits in product((0, 1), repeat=9):
        if not no_adjacent_ones(bits):
            continue
        value = sum(bit * weight for bit, weight in zip(bits, VISIBLE_WEIGHTS + TAIL_WEIGHTS))
        if value <= 63:
            labels[value] = "".join(str(bit) for bit in bits[:6])
    return [labels[index] for index in range(64)]


def q6_edges() -> list[tuple[int, int]]:
    edges = []
    for vertex in range(64):
        for axis in range(6):
            other = vertex ^ (1 << axis)
            if vertex < other:
                edges.append((vertex, other))
    return edges


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def quotient_graph(labels: list[str], edges: Iterable[tuple[int, int]]) -> tuple[list[str], set[tuple[int, int]]]:
    names = sorted(set(labels))
    index = {name: pos for pos, name in enumerate(names)}
    quotient_edges: set[tuple[int, int]] = set()
    for left, right in edges:
        a = index[labels[left]]
        b = index[labels[right]]
        if a != b:
            quotient_edges.add((a, b) if a < b else (b, a))
    return names, quotient_edges


def codon_hamming_edges(codons: list[str]) -> list[tuple[int, int]]:
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


def adjacency_masks(n: int, edges: Iterable[tuple[int, int]]) -> list[int]:
    masks = [0] * n
    for left, right in edges:
        masks[left] |= 1 << right
        masks[right] |= 1 << left
    return masks


def edge_set_from_masks(masks: list[int]) -> set[tuple[int, int]]:
    edges = set()
    for left, mask in enumerate(masks):
        for right in range(left + 1, len(masks)):
            if (mask >> right) & 1:
                edges.add((left, right))
    return edges


def degree_sequence(masks: list[int]) -> list[int]:
    return sorted(mask.bit_count() for mask in masks)


def distance_profile(masks: list[int]) -> tuple[int | None, dict[str, int]]:
    n = len(masks)
    distribution: Counter[int] = Counter()
    diameter = 0
    for source in range(n):
        distances = [-1] * n
        distances[source] = 0
        queue = deque([source])
        while queue:
            vertex = queue.popleft()
            mask = masks[vertex]
            for other in range(n):
                if ((mask >> other) & 1) and distances[other] < 0:
                    distances[other] = distances[vertex] + 1
                    queue.append(other)
        if any(distance < 0 for distance in distances):
            return None, {}
        for target in range(source + 1, n):
            distribution[distances[target]] += 1
            diameter = max(diameter, distances[target])
    return diameter, {str(key): distribution[key] for key in sorted(distribution)}


def wl_colors(masks: list[int], seed_colors: list[int] | None = None) -> list[int]:
    n = len(masks)
    colors = seed_colors[:] if seed_colors is not None else [mask.bit_count() for mask in masks]
    while True:
        signatures = []
        for vertex in range(n):
            neighbor_colors = Counter(colors[other] for other in range(n) if (masks[vertex] >> other) & 1)
            signatures.append((colors[vertex], tuple(sorted(neighbor_colors.items()))))
        palette: dict[tuple[object, ...], int] = {}
        new_colors = []
        for signature in signatures:
            if signature not in palette:
                palette[signature] = len(palette)
            new_colors.append(palette[signature])
        if new_colors == colors:
            return colors
        colors = new_colors


def automorphism_order(masks: list[int], cap: int = 1000000) -> int:
    n = len(masks)
    colors = wl_colors(masks)
    if len(set(colors)) == n:
        return 1
    color_classes: dict[int, list[int]] = defaultdict(list)
    for vertex, color in enumerate(colors):
        color_classes[color].append(vertex)
    base_candidates = [set(color_classes[colors[vertex]]) for vertex in range(n)]
    assigned = [-1] * n
    used = [False] * n
    order: list[int] = []

    def recurse(total_so_far: int) -> int:
        if total_so_far > cap:
            return total_so_far
        if len(order) == n:
            return total_so_far + 1
        best_vertex = -1
        best_options: list[int] | None = None
        for vertex in range(n):
            if assigned[vertex] >= 0:
                continue
            options = []
            for image in base_candidates[vertex]:
                if used[image]:
                    continue
                ok = True
                for old_vertex in order:
                    old_image = assigned[old_vertex]
                    if ((masks[vertex] >> old_vertex) & 1) != ((masks[image] >> old_image) & 1):
                        ok = False
                        break
                if ok:
                    options.append(image)
            if best_options is None or len(options) < len(best_options):
                best_vertex = vertex
                best_options = options
                if len(options) <= 1:
                    break
        if not best_options:
            return total_so_far
        total = total_so_far
        for image in best_options:
            assigned[best_vertex] = image
            used[image] = True
            order.append(best_vertex)
            total = recurse(total)
            order.pop()
            used[image] = False
            assigned[best_vertex] = -1
            if total > cap:
                break
        return total

    count = recurse(0)
    return count if count <= cap else cap + 1


def matmul(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    n = len(left)
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        row = out[i]
        for k in range(n):
            value = left[i][k]
            if value == 0:
                continue
            right_row = right[k]
            for j in range(n):
                row[j] += value * right_row[j]
    return out


def characteristic_polynomial(masks: list[int]) -> list[int]:
    n = len(masks)
    matrix = [[1 if (masks[i] >> j) & 1 else 0 for j in range(n)] for i in range(n)]
    helper = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    coeffs = [1]
    for step in range(1, n + 1):
        product_matrix = matmul(matrix, helper)
        trace = sum(product_matrix[i][i] for i in range(n))
        if trace % step != 0:
            raise ArithmeticError("nonintegral Faddeev-LeVerrier coefficient")
        coeff = -trace // step
        coeffs.append(coeff)
        helper = product_matrix
        for i in range(n):
            helper[i][i] += coeff
    return coeffs


def spectral_moments(masks: list[int], max_power: int = 8) -> list[int]:
    n = len(masks)
    matrix = [[1 if (masks[i] >> j) & 1 else 0 for j in range(n)] for i in range(n)]
    power = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    moments = []
    for _ in range(max_power):
        power = matmul(power, matrix)
        moments.append(sum(power[i][i] for i in range(n)))
    return moments


def graph_summary(name: str, labels: list[str], edges: set[tuple[int, int]]) -> dict[str, object]:
    masks = adjacency_masks(len(labels), edges)
    diameter, distances = distance_profile(masks)
    colors = wl_colors(masks)
    charpoly = characteristic_polynomial(masks)
    return {
        "name": name,
        "node_count": len(labels),
        "edge_count": len(edges),
        "degree_sequence": degree_sequence(masks),
        "diameter": diameter,
        "distance_distribution": distances,
        "automorphism_order": automorphism_order(masks),
        "wl_color_class_sizes": sorted(Counter(colors).values()),
        "wl_discrete": len(set(colors)) == len(labels),
        "spectral_moments_1_to_8": spectral_moments(masks),
        "charpoly_coefficients_desc": charpoly,
        "charpoly_head": charpoly[:8],
        "charpoly_tail": charpoly[-8:],
    }


def canonical_comparison(left: dict[str, object], right: dict[str, object]) -> tuple[list[str], list[str], dict[str, bool]]:
    keys = [
        "node_count",
        "edge_count",
        "degree_sequence",
        "diameter",
        "distance_distribution",
        "automorphism_order",
        "wl_discrete",
        "spectral_moments_1_to_8",
        "charpoly_coefficients_desc",
    ]
    flags = {key: left[key] == right[key] for key in keys}
    shared = [key for key in keys if flags[key]]
    differing = [key for key in keys if not flags[key]]
    return shared, differing, flags


def randomize_by_edge_swaps(masks: list[int], rng: random.Random, swaps: int) -> list[int]:
    edges = list(edge_set_from_masks(masks))
    edge_set = set(edges)
    n = len(masks)
    attempts = 0
    accepted = 0
    max_attempts = swaps * 25
    while accepted < swaps and attempts < max_attempts:
        attempts += 1
        first = rng.randrange(len(edges))
        second = rng.randrange(len(edges))
        if first == second:
            continue
        a, b = edges[first]
        c, d = edges[second]
        if len({a, b, c, d}) < 4:
            continue
        if rng.randrange(2):
            x, y = tuple(sorted((a, c)))
            u, v = tuple(sorted((b, d)))
        else:
            x, y = tuple(sorted((a, d)))
            u, v = tuple(sorted((b, c)))
        if x == y or u == v or (x, y) in edge_set or (u, v) in edge_set or (x, y) == (u, v):
            continue
        old_first = edges[first]
        old_second = edges[second]
        edge_set.remove(old_first)
        edge_set.remove(old_second)
        edge_set.add((x, y))
        edge_set.add((u, v))
        edges[first] = (x, y)
        edges[second] = (u, v)
        accepted += 1
    return adjacency_masks(n, edge_set)


def cheap_profile(masks: list[int]) -> dict[str, object]:
    diameter, distances = distance_profile(masks)
    colors = wl_colors(masks)
    return {
        "node_count": len(masks),
        "edge_count": sum(mask.bit_count() for mask in masks) // 2,
        "degree_sequence": degree_sequence(masks),
        "diameter": diameter,
        "distance_distribution": distances,
        "automorphism_order": automorphism_order(masks),
        "wl_discrete": len(set(colors)) == len(masks),
    }


def null_comparison(
    window_masks: list[int],
    codon_masks: list[int],
    observed_score: int,
    rng: random.Random,
) -> dict[str, object]:
    score_histogram: Counter[int] = Counter()
    shared_histogram: Counter[str] = Counter()
    for _ in range(NULL_DRAWS):
        rw = cheap_profile(randomize_by_edge_swaps(window_masks, rng, SWAPS_PER_DRAW))
        rc = cheap_profile(randomize_by_edge_swaps(codon_masks, rng, SWAPS_PER_DRAW))
        score = 0
        for key in (
            "node_count",
            "edge_count",
            "degree_sequence",
            "diameter",
            "distance_distribution",
            "automorphism_order",
            "wl_discrete",
        ):
            if rw[key] == rc[key]:
                score += 1
                shared_histogram[key] += 1
        score_histogram[score] += 1
    tail = sum(count for score, count in score_histogram.items() if score >= observed_score)
    return {
        "model": "separate double-edge-swap nulls preserving each observed graph degree sequence",
        "draws": NULL_DRAWS,
        "swaps_per_draw": SWAPS_PER_DRAW,
        "observed_cheap_shared_score": observed_score,
        "score_histogram": {str(key): score_histogram[key] for key in sorted(score_histogram)},
        "shared_frequency": {
            key: shared_histogram[key] / NULL_DRAWS
            for key in sorted(shared_histogram)
        },
        "p_ge_observed_score": (tail + 1) / (NULL_DRAWS + 1),
    }


def spectral_sample_reconstructability(
    masks: list[int],
    observed_moments: list[int],
    rng: random.Random,
    observed_charpoly: list[int],
    draws: int = 240,
) -> dict[str, object]:
    moment_collisions = 0
    charpoly_collisions = 0
    for _ in range(draws):
        randomized = randomize_by_edge_swaps(masks, rng, SWAPS_PER_DRAW)
        if spectral_moments(randomized) == observed_moments:
            moment_collisions += 1
        if characteristic_polynomial(randomized) == observed_charpoly:
            charpoly_collisions += 1
    return {
        "method": "sampled degree-sequence rewires compared by exact characteristic polynomial",
        "draws": draws,
        "moment_signature": "trace(A^k), k=1..8",
        "moment_collisions": moment_collisions,
        "charpoly_collisions": charpoly_collisions,
        "unique_spectrum_in_sample": charpoly_collisions == 0,
        "exhaustive_ds_claim": False,
    }


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[dict[str, object]] = []

    window_vertex_labels = flat(FOLD6_VISIBLE_PREFIX)
    reconstructed_window = reconstruct_window_from_rules()
    window_labels, window_edges = quotient_graph(window_vertex_labels, q6_edges())

    codons = codon_order()
    codon_vertex_labels = [CODON_TO_FAMILY[codon] for codon in codons]
    codon_labels, codon_edges = quotient_graph(codon_vertex_labels, codon_hamming_edges(codons))

    window_summary = graph_summary("window6_type_quotient", window_labels, window_edges)
    codon_summary = graph_summary("codon_family_quotient", codon_labels, codon_edges)

    checks.append(check_row("window_fold6_reconstruction", window_vertex_labels, reconstructed_window))
    checks.append(check_row("window_q6_micro_edge_count", len(q6_edges()), 192))
    checks.append(check_row("window_family_count", len(window_labels), 21))
    checks.append(check_row("window_quotient_edge_count", len(window_edges), 93))
    checks.append(check_row("window_diameter", window_summary["diameter"], 3))
    checks.append(check_row("window_automorphism_order", window_summary["automorphism_order"], 1))
    checks.append(check_row("codon_to_q6_bijection_count", len({codon_to_q6(codon) for codon in codons}), 64))
    checks.append(check_row("codon_hamming_micro_edge_count", len(codon_hamming_edges(codons)), 288))
    checks.append(check_row("codon_family_count", len(codon_labels), 21))
    checks.append(check_row("codon_quotient_edge_count", len(codon_edges), 85))
    checks.append(check_row("codon_diameter", codon_summary["diameter"], 3))
    checks.append(check_row("codon_automorphism_order", codon_summary["automorphism_order"], 1))
    checks.append(check_row("window_charpoly_c2_is_minus_edges", window_summary["charpoly_coefficients_desc"][2], -93))
    checks.append(check_row("codon_charpoly_c2_is_minus_edges", codon_summary["charpoly_coefficients_desc"][2], -85))

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            window_graph=window_summary,
            codon_graph=codon_summary,
            shared_invariants=[],
            differing_invariants=[],
            invariant_agreement={},
            null_p=None,
            null={},
            spectral_reconstructability={},
            checks=checks,
            note="self-check failed before the rigidity comparison was accepted",
        )

    shared, differing, agreement = canonical_comparison(window_summary, codon_summary)
    observed_cheap_score = sum(
        1
        for key in (
            "node_count",
            "edge_count",
            "degree_sequence",
            "diameter",
            "distance_distribution",
            "automorphism_order",
            "wl_discrete",
        )
        if agreement[key]
    )
    null = null_comparison(
        adjacency_masks(len(window_labels), window_edges),
        adjacency_masks(len(codon_labels), codon_edges),
        observed_cheap_score,
        rng,
    )
    spectral_reconstructability = {
        "window_graph": spectral_sample_reconstructability(
            adjacency_masks(len(window_labels), window_edges),
            window_summary["spectral_moments_1_to_8"],
            rng,
            window_summary["charpoly_coefficients_desc"],
        ),
        "codon_graph": spectral_sample_reconstructability(
            adjacency_masks(len(codon_labels), codon_edges),
            codon_summary["spectral_moments_1_to_8"],
            rng,
            codon_summary["charpoly_coefficients_desc"],
        ),
    }

    rigidity_refuted = any(
        not agreement[key]
        for key in (
            "edge_count",
            "degree_sequence",
            "distance_distribution",
            "spectral_moments_1_to_8",
            "charpoly_coefficients_desc",
        )
    )
    certified = (
        not rigidity_refuted
        and agreement["automorphism_order"]
        and window_summary["automorphism_order"] == 1
        and null["p_ge_observed_score"] <= 0.05
    )
    status = "certified" if certified else ("refuted" if rigidity_refuted else "coincidence")

    note = (
        "The two quotient graphs share 21 nodes, diameter 3, WL-discrete color "
        "refinement, and trivial automorphism group.  They do not share edge "
        "count, degree sequence, pair-distance distribution, spectral moments, "
        "or exact adjacency characteristic polynomial.  Since the characteristic "
        "polynomial already separates them at the lambda^(n-2) coefficient "
        "(-|E|), the proposed rigidity-equivalence is refuted rather than "
        "certified.  The null is degree-sequence preserving on each side; a "
        "single common degree-sequence null is impossible because the observed "
        "degree sequences and edge counts differ."
    )

    emit(
        status,
        window_graph=window_summary,
        codon_graph=codon_summary,
        shared_invariants=shared,
        differing_invariants=differing,
        invariant_agreement=agreement,
        null_p=null["p_ge_observed_score"],
        null=null,
        spectral_reconstructability=spectral_reconstructability,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

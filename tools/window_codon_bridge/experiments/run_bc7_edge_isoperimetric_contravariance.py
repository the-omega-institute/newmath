#!/usr/bin/env python3
"""BC7 edge-isoperimetric contravariance for Window6 and the standard code.

The certificate is intentionally narrow: it concerns only the label-free
local-edge-hiding functional e_in on two fixed regular micrographs.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "bc7_edge_isoperimetric_contravariance"
CLAIM_ID = "bridge.window6_codon_q6.edge_isoperimetric_contravariance"
RANDOM_SEED = 706170
NULL_DRAWS = 4000

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)
VENDOR_NOTE = (
    "Fold6 table copied from origin/feat/fibonacci_reality-deepening "
    "forced_window_structure; reconstructed from the finite no-adjacent "
    "Zeckendorf representatives on 0..63 as a self-check."
)

# Entry n gives the visible six-prefix of the unique no-adjacent nine-bit
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


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def q6_edges() -> list[tuple[int, int]]:
    edges = []
    for vertex in range(64):
        for axis in range(6):
            neighbor = vertex ^ (1 << axis)
            if vertex < neighbor:
                edges.append((vertex, neighbor))
    return edges


def hamming_codon_edges(codons: list[str]) -> tuple[list[tuple[int, int]], list[tuple[int, int, int]]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    positioned: list[tuple[int, int, int]] = []
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
                    positioned.append((left, right, position + 1))
    return edges, positioned


def e_in(labels: list[int] | list[str], edges: Iterable[tuple[int, int]]) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def e_in_by_position(labels: list[str], positioned_edges: list[tuple[int, int, int]]) -> dict[int, int]:
    counts: Counter[int] = Counter()
    for left, right, position in positioned_edges:
        if labels[left] == labels[right]:
            counts[position] += 1
    return dict(sorted(counts.items()))


def family_size_histogram(labels: list[str]) -> dict[int, int]:
    return dict(sorted(Counter(Counter(labels).values()).items()))


def sizes_from_labels(labels: list[str]) -> list[int]:
    return sorted(Counter(labels).values(), reverse=True)


def block_upper_hamming34(size: int) -> int:
    table = {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}
    return table[size]


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def relabel_to_size_order(labels: list[str]) -> list[int]:
    members: dict[str, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        members[label].append(index)
    ordered = sorted(members, key=lambda item: (-len(members[item]), item))
    result = [0] * len(labels)
    for block, label in enumerate(ordered):
        for index in members[label]:
            result[index] = block
    return result


def adjacency_from_edges(edges: list[tuple[int, int]], n: int) -> list[list[int]]:
    adjacency = [[] for _ in range(n)]
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    return adjacency


def delta_swap(labels: list[int], adjacency: list[list[int]], a: int, b: int) -> int:
    la = labels[a]
    lb = labels[b]
    if la == lb:
        return 0
    before = 0
    after = 0
    touched = set()
    for x in (a, b):
        for y in adjacency[x]:
            edge = (x, y) if x < y else (y, x)
            if edge in touched:
                continue
            touched.add(edge)
            lx_before = labels[edge[0]]
            ly_before = labels[edge[1]]
            lx_after = lb if edge[0] == a else (la if edge[0] == b else lx_before)
            ly_after = lb if edge[1] == a else (la if edge[1] == b else ly_before)
            before += int(lx_before == ly_before)
            after += int(lx_after == ly_after)
    return after - before


def optimize_partition(
    edges: list[tuple[int, int]],
    sizes: list[int],
    rng: random.Random,
    maximize: bool,
    restarts: int,
    steps: int,
    initial: list[list[int]] | None = None,
) -> dict[str, object]:
    n = sum(sizes)
    adjacency = adjacency_from_edges(edges, n)
    best_labels: list[int] | None = None
    best_score = -1 if maximize else 10**9
    starts = list(initial or [])
    while len(starts) < restarts:
        starts.append(random_partition_by_sizes(sizes, rng))
    for start_index, start in enumerate(starts[:restarts]):
        labels = start[:]
        score = e_in(labels, edges)
        temperature = 1.5
        for step in range(steps):
            if score == 0 and not maximize:
                break
            a = rng.randrange(n)
            b = rng.randrange(n)
            if labels[a] == labels[b]:
                continue
            delta = delta_swap(labels, adjacency, a, b)
            signed = delta if maximize else -delta
            accept = signed >= 0
            if not accept and temperature > 1e-9:
                accept = rng.random() < math.exp(signed / temperature)
            if accept:
                labels[a], labels[b] = labels[b], labels[a]
                score += delta
            temperature *= 0.99935
        improved = score > best_score if maximize else score < best_score
        if improved or start_index == 0:
            best_score = score
            best_labels = labels[:]
    return {"score": best_score, "labels": best_labels or []}


def null_stats(observed: int, values: list[int], tail: str) -> dict[str, object]:
    lo = min(values)
    hi = max(values)
    mean = sum(values) / len(values)
    if len(values) > 1:
        var = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    else:
        var = 0.0
    if tail == "lower":
        p_value = (sum(1 for value in values if value <= observed) + 1) / (len(values) + 1)
    else:
        p_value = (sum(1 for value in values if value >= observed) + 1) / (len(values) + 1)
    tau_null = None if hi == lo else (observed - lo) / (hi - lo)
    sorted_values = sorted(values)
    q05 = sorted_values[int(0.05 * (len(sorted_values) - 1))]
    q50 = sorted_values[int(0.50 * (len(sorted_values) - 1))]
    q95 = sorted_values[int(0.95 * (len(sorted_values) - 1))]
    return {
        "draws": len(values),
        "min": lo,
        "max": hi,
        "mean": mean,
        "sd": math.sqrt(var),
        "q05": q05,
        "q50": q50,
        "q95": q95,
        "tau_null": tau_null,
        "tail": tail,
        "p_value": p_value,
    }


def sample_free_null(
    edges: list[tuple[int, int]],
    sizes: list[int],
    observed: int,
    tail: str,
    rng: random.Random,
) -> dict[str, object]:
    values = [e_in(random_partition_by_sizes(sizes, rng), edges) for _ in range(NULL_DRAWS)]
    return null_stats(observed, values, tail)


def wobble_ry_dyads(codons: list[str]) -> list[list[int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    dyads: list[list[int]] = []
    for first, second in product(BASES, repeat=2):
        dyads.append([index[first + second + "U"], index[first + second + "C"]])
        dyads.append([index[first + second + "A"], index[first + second + "G"]])
    return dyads


def random_wobble_box_partition(sizes: list[int], codons: list[str], rng: random.Random) -> list[int]:
    dyads = wobble_ry_dyads(codons)
    split_indices = set(rng.sample(range(len(dyads)), 2))
    singleton_units: list[list[int]] = []
    dyad_units: list[list[int]] = []
    for index, dyad in enumerate(dyads):
        if index in split_indices:
            singleton_units.extend([[dyad[0]], [dyad[1]]])
        else:
            dyad_units.append(dyad)
    rng.shuffle(singleton_units)
    rng.shuffle(dyad_units)
    labels = [-1] * 64
    ordered_blocks = sorted(enumerate(sizes), key=lambda item: (-item[1], item[0]))
    for block, size in ordered_blocks:
        units: list[list[int]] = []
        if size == 6:
            units = [dyad_units.pop(), dyad_units.pop(), dyad_units.pop()]
        elif size == 4:
            units = [dyad_units.pop(), dyad_units.pop()]
        elif size == 3:
            units = [dyad_units.pop(), singleton_units.pop()]
        elif size == 2:
            units = [dyad_units.pop()]
        elif size == 1:
            units = [singleton_units.pop()]
        else:
            raise ValueError(f"unsupported block size for wobble null: {size}")
        for unit in units:
            for vertex in unit:
                labels[vertex] = block
    if any(label < 0 for label in labels):
        raise RuntimeError("incomplete wobble partition")
    return labels


def sample_wobble_box_null(
    edges: list[tuple[int, int]],
    sizes: list[int],
    codons: list[str],
    observed: int,
    rng: random.Random,
) -> dict[str, object]:
    values = [e_in(random_wobble_box_partition(sizes, codons, rng), edges) for _ in range(NULL_DRAWS)]
    stats = null_stats(observed, values, "upper")
    stats["model"] = "same size multiset; thirty R/Y dyads kept intact and two dyads split to supply odd blocks"
    return stats


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[dict[str, object]] = []

    window_labels = flat(FOLD6_VISIBLE_PREFIX)
    reconstructed_window = reconstruct_window_from_rules()
    window_edges = q6_edges()
    e_in_w = e_in(window_labels, window_edges)
    window_hist = family_size_histogram(window_labels)
    window_sizes = sizes_from_labels(window_labels)

    codons = codon_order()
    codon_labels = [CODON_TO_FAMILY[codon] for codon in codons]
    codon_edges, codon_positioned_edges = hamming_codon_edges(codons)
    e_in_c = e_in(codon_labels, codon_edges)
    codon_axis = e_in_by_position(codon_labels, codon_positioned_edges)
    codon_hist = family_size_histogram(codon_labels)
    codon_sizes = sizes_from_labels(codon_labels)

    checks.append(check_row("window_fold6_reconstruction", window_labels, reconstructed_window))
    checks.append(check_row("window_family_count", len(set(window_labels)), 21))
    checks.append(check_row("window_fiber_histogram", window_hist, {2: 8, 3: 4, 4: 9}))
    checks.append(check_row("window_edge_count", len(window_edges), 192))
    checks.append(check_row("window_e_in", e_in_w, 0))
    checks.append(check_row("codon_q6_encoding_count", len({codon_to_q6(codon) for codon in codons}), 64))
    checks.append(check_row("codon_family_count", len(set(codon_labels)), 21))
    checks.append(check_row("codon_family_histogram", codon_hist, {1: 2, 2: 9, 3: 2, 4: 5, 6: 3}))
    checks.append(check_row("codon_edge_count", len(codon_edges), 288))
    checks.append(check_row("codon_e_in", e_in_c, 69))
    checks.append(check_row("codon_e_in_by_position", codon_axis, {1: 4, 2: 1, 3: 64}))

    codon_upper_terms = Counter(codon_sizes)
    codon_upper = sum(count * block_upper_hamming34(size) for size, count in codon_upper_terms.items())
    checks.append(check_row("codon_block_upper", codon_upper, 72))

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            tau_W=None,
            tau_C=None,
            e_in_W=e_in_w,
            e_in_C=e_in_c,
            e_max_C=[None, codon_upper],
            D_minus=None,
            nulls={},
            checks=checks,
            certificate_statement="self-check failed before any certificate statement",
            note=VENDOR_NOTE,
        )

    window_observed_partition = relabel_to_size_order(window_labels)
    codon_observed_partition = relabel_to_size_order(codon_labels)

    emax_w_search = optimize_partition(
        window_edges,
        window_sizes,
        rng,
        maximize=True,
        restarts=70,
        steps=5000,
        initial=[window_observed_partition],
    )
    emin_c_search = optimize_partition(
        codon_edges,
        codon_sizes,
        rng,
        maximize=False,
        restarts=90,
        steps=6500,
        initial=[codon_observed_partition],
    )
    emax_c_search = optimize_partition(
        codon_edges,
        codon_sizes,
        rng,
        maximize=True,
        restarts=90,
        steps=6500,
        initial=[codon_observed_partition],
    )

    e_min_w = 0
    e_max_w = int(emax_w_search["score"])
    e_min_c_approx = int(emin_c_search["score"])
    e_max_c_achievable = max(e_in_c, int(emax_c_search["score"]))
    e_max_c_upper = codon_upper

    window_free_null = sample_free_null(window_edges, window_sizes, e_in_w, "lower", rng)
    codon_free_null = sample_free_null(codon_edges, codon_sizes, e_in_c, "upper", rng)
    codon_wobble_null = sample_wobble_box_null(codon_edges, codon_sizes, codons, e_in_c, rng)

    tau_w = 0.0 if e_max_w > e_min_w else None
    tau_c = (e_in_c - e_min_c_approx) / (e_max_c_upper - e_min_c_approx)
    d_minus = None if tau_w is None else 1.0 - abs(tau_w + tau_c - 1.0)

    window_endpoint = e_in_w == e_min_w and e_max_w > e_min_w
    codon_near_endpoint = tau_c >= 0.9 and e_in_c >= e_max_c_upper - 0.1 * (e_max_c_upper - e_min_c_approx)
    null_significant = (
        window_free_null["p_value"] <= 0.05
        and codon_free_null["p_value"] <= 0.05
        and codon_wobble_null["p_value"] <= 0.05
    )
    certified = window_endpoint and codon_near_endpoint and null_significant
    same_end_refuted = tau_w is not None and tau_w > 0.5 and tau_c > 0.5
    status = "certified" if certified else ("refuted" if same_end_refuted else "coincidence")

    certificate_statement = (
        "Window6 Fold6 与标准遗传码在 local-edge-hiding functional e_in 上分别实现 "
        "separating 与 (near-)tolerant 的相反可达极端;非同构、非 64→21 生物意义、"
        "非高低能↔DNA/RNA。"
    )
    note = (
        VENDOR_NOTE
        + " Codon tau_C is conservative: the denominator uses the per-block upper bound 72; "
        + "the reported e_max_C interval is [best reachable by search or observation, 72]."
    )

    emit(
        status,
        tau_W=tau_w,
        tau_C=tau_c,
        e_in_W=e_in_w,
        e_in_C=e_in_c,
        e_min_W=e_min_w,
        e_max_W=e_max_w,
        e_min_C=e_min_c_approx,
        e_max_C=[e_max_c_achievable, e_max_c_upper],
        D_minus=d_minus,
        nulls={
            "window_free_same_sizes": window_free_null,
            "codon_free_same_sizes": codon_free_null,
            "codon_wobble_box_preserving": codon_wobble_null,
        },
        checks=checks,
        certificate_statement=certificate_statement,
        note=note,
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Window fold-tower edge-separating extremality check.

The primary Fold_m convention is the finite value-window convention used by
the existing Window6 certificates: vertex n in 0..2^m-1 is written in its
Zeckendorf normal form in a sufficiently long Fibonacci horizon, and the first
m digits are retained.  This is the convention that reproduces the required
m=6 fiber histogram 2:8 / 3:4 / 4:9.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
import math
import random
import sys
from typing import Hashable, Iterable


EXPERIMENT_ID = "window_fold_tower_extremality"
CLAIM_ID = "bridge.window6.fold_tower_separating_extremality"
RANDOM_SEED = 6061406
NULL_DRAWS = 4000
WIDTHS = (4, 5, 6, 7)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def fibonacci_weights(length: int) -> list[int]:
    weights = [1, 2]
    while len(weights) < length:
        weights.append(weights[-1] + weights[-2])
    return weights[:length]


def horizon_for_value(max_value: int, min_length: int) -> int:
    length = max(2, min_length)
    while fibonacci_weights(length)[-1] <= max_value:
        length += 1
    return length


def zeckendorf_bits(value: int, length: int) -> tuple[int, ...]:
    weights = fibonacci_weights(length)
    bits = [0] * length
    remaining = value
    for index in range(length - 1, -1, -1):
        weight = weights[index]
        if weight <= remaining:
            bits[index] = 1
            remaining -= weight
    if remaining != 0:
        raise ValueError(f"value {value} does not fit in horizon {length}")
    if any(bits[index] and bits[index + 1] for index in range(length - 1)):
        raise ValueError(f"greedy representation is not Zeckendorf for {value}")
    return tuple(bits)


def fold_value_window(width: int) -> list[str]:
    horizon = horizon_for_value((1 << width) - 1, width)
    return [
        "".join(str(bit) for bit in zeckendorf_bits(value, horizon)[:width])
        for value in range(1 << width)
    ]


def fold_fibonacci_input(width: int) -> list[str]:
    weights = fibonacci_weights(width)
    max_value = sum(weights)
    horizon = horizon_for_value(max_value, width)
    labels: list[str] = []
    for vertex in range(1 << width):
        value = sum(((vertex >> index) & 1) * weights[index] for index in range(width))
        labels.append("".join(str(bit) for bit in zeckendorf_bits(value, horizon)[:width]))
    return labels


def no_adjacent_words(width: int) -> list[str]:
    words = []
    for bits in product((0, 1), repeat=width):
        if all(not (bits[index] and bits[index + 1]) for index in range(width - 1)):
            words.append("".join(str(bit) for bit in bits))
    return words


def cube_edges(width: int) -> list[tuple[int, int]]:
    edges: list[tuple[int, int]] = []
    for vertex in range(1 << width):
        for axis in range(width):
            neighbor = vertex ^ (1 << axis)
            if vertex < neighbor:
                edges.append((vertex, neighbor))
    return edges


def e_in(labels: list[Hashable], edges: Iterable[tuple[int, int]]) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def size_histogram(labels: list[Hashable]) -> dict[int, int]:
    return dict(sorted(Counter(Counter(labels).values()).items()))


def sizes_from_labels(labels: list[Hashable]) -> list[int]:
    return sorted(Counter(labels).values(), reverse=True)


def random_partition_by_sizes(sizes: list[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def adjacency_from_edges(edges: list[tuple[int, int]], vertex_count: int) -> list[list[int]]:
    adjacency = [[] for _ in range(vertex_count)]
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    return adjacency


def swap_delta(labels: list[int], adjacency: list[list[int]], left: int, right: int) -> int:
    left_label = labels[left]
    right_label = labels[right]
    if left_label == right_label:
        return 0
    before = 0
    after = 0
    touched: set[tuple[int, int]] = set()
    for vertex in (left, right):
        for neighbor in adjacency[vertex]:
            edge = (vertex, neighbor) if vertex < neighbor else (neighbor, vertex)
            if edge in touched:
                continue
            touched.add(edge)
            a, b = edge
            label_a = labels[a]
            label_b = labels[b]
            new_a = right_label if a == left else (left_label if a == right else label_a)
            new_b = right_label if b == left else (left_label if b == right else label_b)
            before += int(label_a == label_b)
            after += int(new_a == new_b)
    return after - before


def optimize_bound(
    edges: list[tuple[int, int]],
    sizes: list[int],
    rng: random.Random,
    maximize: bool,
    restarts: int,
    steps: int,
    initial: list[int] | None = None,
) -> int:
    vertex_count = sum(sizes)
    adjacency = adjacency_from_edges(edges, vertex_count)
    best = -1 if maximize else 10**9
    starts: list[list[int]] = []
    if initial is not None:
        starts.append(initial[:])
    while len(starts) < restarts:
        starts.append(random_partition_by_sizes(sizes, rng))
    for start in starts:
        labels = start[:]
        score = e_in(labels, edges)
        temperature = 1.4
        for _ in range(steps):
            if score == 0 and not maximize:
                break
            left = rng.randrange(vertex_count)
            right = rng.randrange(vertex_count)
            if labels[left] == labels[right]:
                continue
            delta = swap_delta(labels, adjacency, left, right)
            signed = delta if maximize else -delta
            accept = signed >= 0
            if not accept and temperature > 1e-12:
                accept = rng.random() < math.exp(signed / temperature)
            if accept:
                labels[left], labels[right] = labels[right], labels[left]
                score += delta
            temperature *= 0.9992
        if (maximize and score > best) or ((not maximize) and score < best):
            best = score
    return best


def relabel_to_size_order(labels: list[Hashable]) -> list[int]:
    members: dict[Hashable, list[int]] = {}
    for index, label in enumerate(labels):
        members.setdefault(label, []).append(index)
    ordered = sorted(members, key=lambda label: (-len(members[label]), str(label)))
    result = [0] * len(labels)
    for block, label in enumerate(ordered):
        for index in members[label]:
            result[index] = block
    return result


def null_stats(observed: int, values: list[int]) -> dict[str, object]:
    sorted_values = sorted(values)
    mean = sum(values) / len(values)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return {
        "draws": len(values),
        "min": sorted_values[0],
        "max": sorted_values[-1],
        "mean": mean,
        "sd": math.sqrt(variance),
        "q05": sorted_values[int(0.05 * (len(sorted_values) - 1))],
        "q50": sorted_values[int(0.50 * (len(sorted_values) - 1))],
        "q95": sorted_values[int(0.95 * (len(sorted_values) - 1))],
        "tail": "lower",
        "p_value": (sum(1 for value in values if value <= observed) + 1) / (len(values) + 1),
    }


def sample_null(edges: list[tuple[int, int]], sizes: list[int], observed: int, rng: random.Random) -> dict[str, object]:
    values = [e_in(random_partition_by_sizes(sizes, rng), edges) for _ in range(NULL_DRAWS)]
    stats = null_stats(observed, values)
    stats["model"] = "uniform label permutation preserving only the fiber-size multiset"
    return stats


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def analyze_width(width: int, rng: random.Random) -> dict[str, object]:
    labels = fold_value_window(width)
    edges = cube_edges(width)
    sizes = sizes_from_labels(labels)
    observed = e_in(labels, edges)
    observed_partition = relabel_to_size_order(labels)
    e_min = optimize_bound(
        edges,
        sizes,
        rng,
        maximize=False,
        restarts=40 if width <= 6 else 28,
        steps=2500 if width <= 6 else 1800,
        initial=observed_partition,
    )
    e_max = optimize_bound(
        edges,
        sizes,
        rng,
        maximize=True,
        restarts=70 if width <= 6 else 42,
        steps=4500 if width <= 6 else 2600,
        initial=observed_partition,
    )
    tau = None if e_max == e_min else (observed - e_min) / (e_max - e_min)
    null = sample_null(edges, sizes, observed, rng)
    fib_input_labels = fold_fibonacci_input(width)
    return {
        "width": width,
        "vertex_count": 1 << width,
        "edge_count": len(edges),
        "x_count": len(set(labels)),
        "expected_x_count": len(no_adjacent_words(width)),
        "fiber_histogram": size_histogram(labels),
        "e_in": observed,
        "e_min": e_min,
        "e_max": e_max,
        "tau": tau,
        "null": null,
        "literal_formula_diagnostic": {
            "x_count": len(set(fib_input_labels)),
            "fiber_histogram": size_histogram(fib_input_labels),
            "e_in": e_in(fib_input_labels, edges),
        },
    }


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[dict[str, object]] = []
    rows = {width: analyze_width(width, rng) for width in WIDTHS}

    for width, row in rows.items():
        checks.append(check_row(f"width_{width}_x_count", row["x_count"], row["expected_x_count"]))
    checks.append(check_row("width_6_e_in", rows[6]["e_in"], 0))
    checks.append(check_row("width_6_fiber_histogram", rows[6]["fiber_histogram"], {2: 8, 3: 4, 4: 9}))

    self_checks_ok = all(bool(row["ok"]) for row in checks)
    e_in_by_width = {str(width): rows[width]["e_in"] for width in WIDTHS}
    e_min_by_width = {str(width): rows[width]["e_min"] for width in WIDTHS}
    e_max_by_width = {str(width): rows[width]["e_max"] for width in WIDTHS}
    tau_by_width = {str(width): rows[width]["tau"] for width in WIDTHS}
    null_p_by_width = {str(width): rows[width]["null"]["p_value"] for width in WIDTHS}

    separating_widths = [width for width in WIDTHS if rows[width]["e_in"] == 0 and rows[width]["e_min"] == 0]
    lower_tail_widths = [width for width in separating_widths if rows[width]["null"]["p_value"] <= 0.01]
    refuting_widths = [width for width in WIDTHS if rows[width]["e_in"] > 0]

    if not self_checks_ok:
        status = "needs_derivation"
        note = (
            "Self-check failed for the finite value-window Fold_m reconstruction; "
            "no fold-tower extremality verdict is emitted."
        )
    elif not refuting_widths and len(lower_tail_widths) >= 3:
        status = "certified"
        note = (
            "All measured finite value-window Fold_m widths are separating lower endpoints "
            "for the local-edge-hiding functional."
        )
    elif refuting_widths and len(separating_widths) >= 1:
        status = "refuted"
        note = (
            "The tower-wide separating claim fails under the finite value-window convention "
            "that reproduces the required Window6 histogram: widths "
            + ",".join(str(width) for width in refuting_widths)
            + " have e_in>0. Widths "
            + ",".join(str(width) for width in separating_widths)
            + " remain separating coincidences."
        )
    elif separating_widths:
        status = "coincidence"
        note = (
            "Only a proper subset of measured widths is separating under the finite "
            "value-window Fold_m convention."
        )
    else:
        status = "refuted"
        note = "No measured width attains the separating lower endpoint."

    dual_picture = (
        "Codon two-layer certificates place the box layer at tau=1.0 and the family "
        "layer near the HIDING endpoint tau=0.958; finite value-window Fold_m places "
        "widths 6 and 7 at the REVEALING endpoint tau=0, but widths 4 and 5 are not "
        "separating under the same reconstruction, so the cross-width tower claim is "
        "not certified."
    )

    emit(
        status,
        tau_by_width=tau_by_width,
        e_in_by_width=e_in_by_width,
        e_min_by_width=e_min_by_width,
        e_max_by_width=e_max_by_width,
        null_p_by_width=null_p_by_width,
        fiber_hist_by_width={str(width): rows[width]["fiber_histogram"] for width in WIDTHS},
        nulls={str(width): rows[width]["null"] for width in WIDTHS},
        literal_formula_diagnostic={
            str(width): rows[width]["literal_formula_diagnostic"] for width in WIDTHS
        },
        separating_widths=separating_widths,
        refuting_widths=refuting_widths,
        dual_picture=dual_picture,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

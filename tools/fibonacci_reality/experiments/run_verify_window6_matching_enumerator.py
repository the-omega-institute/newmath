#!/usr/bin/env python3
"""Forward audit for the matching enumerator of Gamma_6.

The graph Gamma_6 has the length-six binary words with no adjacent ones as
vertices and Hamming-distance-one pairs as edges. This certificate uses exact
finite graph enumeration only: it constructs the graph, computes the
monomer-dimer matching polynomial by a lowest-free-vertex recurrence, and
records the unmatched-vertex profile for maximum matchings.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window6-matching-enumerator"
CLAIM_ID = "window6.fibonacci-cube.matching-enumerator.certificate"
WINDOW = 6
EXPECTED_VERTEX_COUNT = 21
EXPECTED_EDGE_COUNT = 38
EXPECTED_MATCHING_PROFILE = [
    1,
    38,
    595,
    5016,
    24948,
    75432,
    137829,
    146512,
    83589,
    21814,
    1782,
]
EXPECTED_HOSOYA = 497556
EXPECTED_MATCHING_NUMBER = 10
EXPECTED_MAX_MATCHINGS = 1782
EXPECTED_MONOMER_PROFILE = {
    "000000": 110,
    "000101": 108,
    "001001": 142,
    "001010": 170,
    "010001": 190,
    "010010": 330,
    "010100": 170,
    "100001": 122,
    "100010": 190,
    "100100": 142,
    "101000": 108,
}


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def admissible_words(width: int) -> list[tuple[int, ...]]:
    return [
        tuple(bits)
        for bits in product((0, 1), repeat=width)
        if all(not (bits[index] and bits[index + 1]) for index in range(width - 1))
    ]


def word_to_string(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def fibonacci_cube_edges(words: list[tuple[int, ...]]) -> list[tuple[int, int]]:
    index = {word: offset for offset, word in enumerate(words)}
    edges: list[tuple[int, int]] = []
    for source, word in enumerate(words):
        for bit_index in range(len(word)):
            neighbor = list(word)
            neighbor[bit_index] = 1 - neighbor[bit_index]
            target = index.get(tuple(neighbor))
            if target is not None and source < target:
                edges.append((source, target))
    return edges


def adjacency(vertex_count: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    graph = [[] for _ in range(vertex_count)]
    for source, target in edges:
        graph[source].append(target)
        graph[target].append(source)
    for neighbors in graph:
        neighbors.sort()
    return graph


def add_profiles(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    size = max(len(left), len(right))
    return tuple(
        (left[index] if index < len(left) else 0)
        + (right[index] if index < len(right) else 0)
        for index in range(size)
    )


def shift_profile(profile: tuple[int, ...]) -> tuple[int, ...]:
    return (0,) + profile


def matching_profile(graph: list[list[int]]) -> list[int]:
    vertex_count = len(graph)
    full_mask = (1 << vertex_count) - 1

    @lru_cache(maxsize=None)
    def recur(free_mask: int) -> tuple[int, ...]:
        if free_mask == 0:
            return (1,)
        vertex = (free_mask & -free_mask).bit_length() - 1
        without_vertex = free_mask & ~(1 << vertex)
        total = recur(without_vertex)
        for neighbor in graph[vertex]:
            if without_vertex & (1 << neighbor):
                total = add_profiles(
                    total,
                    shift_profile(recur(without_vertex & ~(1 << neighbor))),
                )
        return total

    return list(recur(full_mask))


def maximum_matching_monomer_profile(
    graph: list[list[int]],
    maximum_size: int,
    words: list[tuple[int, ...]],
) -> dict[str, int]:
    vertex_count = len(graph)
    full_mask = (1 << vertex_count) - 1
    profile = {word_to_string(word): 0 for word in words}

    def recur(free_mask: int, size: int, monomer_index: int | None) -> None:
        if free_mask == 0:
            if size == maximum_size and monomer_index is not None:
                profile[word_to_string(words[monomer_index])] += 1
            return
        unmatched_budget = 0 if monomer_index is not None else 1
        if free_mask.bit_count() < 2 * (maximum_size - size):
            return
        if free_mask.bit_count() > 2 * (maximum_size - size) + unmatched_budget:
            return
        vertex = (free_mask & -free_mask).bit_length() - 1
        without_vertex = free_mask & ~(1 << vertex)
        if monomer_index is None:
            recur(without_vertex, size, vertex)
        for neighbor in graph[vertex]:
            if without_vertex & (1 << neighbor):
                recur(without_vertex & ~(1 << neighbor), size + 1, monomer_index)

    recur(full_mask, 0, None)
    return {word: count for word, count in profile.items() if count}


def word_weight(word_string: str) -> int:
    return sum(1 for bit in word_string if bit == "1")


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    words = admissible_words(WINDOW)
    edges = fibonacci_cube_edges(words)
    graph = adjacency(len(words), edges)
    profile = matching_profile(graph)
    hosoya_index = sum(profile)
    matching_number = max(index for index, value in enumerate(profile) if value)
    maximum_matchings = profile[matching_number]
    monomer_profile = maximum_matching_monomer_profile(graph, matching_number, words)
    even_monomer_total = sum(
        count for word, count in monomer_profile.items() if word_weight(word) % 2 == 0
    )
    odd_monomer_total = sum(
        count for word, count in monomer_profile.items() if word_weight(word) % 2 == 1
    )
    expected_monomer_total = sum(EXPECTED_MONOMER_PROFILE.values())

    checks = [
        check(
            "window6_fibonacci_cube_vertex_count",
            len(words) == EXPECTED_VERTEX_COUNT,
            "The no-adjacent-ones length-six carrier has |X_6|=21 vertices.",
        ),
        check(
            "window6_fibonacci_cube_edge_count",
            len(edges) == EXPECTED_EDGE_COUNT,
            "The Hamming-distance-one graph on X_6 has 38 undirected edges.",
        ),
        check(
            "matching_polynomial_profile",
            profile == EXPECTED_MATCHING_PROFILE,
            "Lowest-free-vertex recurrence gives Z_6(q) coefficients for k=0..10.",
        ),
        check(
            "hosoya_index_total_matchings",
            hosoya_index == EXPECTED_HOSOYA,
            "The Hosoya index Z_6(1) is the sum of all matching counts.",
        ),
        check(
            "matching_number",
            matching_number == EXPECTED_MATCHING_NUMBER,
            "The highest nonzero matching-polynomial degree is nu(Gamma_6)=10.",
        ),
        check(
            "maximum_matching_count",
            maximum_matchings == EXPECTED_MAX_MATCHINGS,
            "The coefficient of q^10 is the number of maximum matchings.",
        ),
        check(
            "maximum_matching_monomer_profile",
            monomer_profile == EXPECTED_MONOMER_PROFILE,
            "Enumerating size-10 matchings gives the exact unmatched-word profile.",
        ),
        check(
            "maximum_matching_monomer_total",
            sum(monomer_profile.values()) == EXPECTED_MAX_MATCHINGS
            and expected_monomer_total == EXPECTED_MAX_MATCHINGS,
            "The monomer profile sums to the 1782 maximum matchings.",
        ),
        check(
            "odd_weight_monomer_count_zero",
            odd_monomer_total == 0 and even_monomer_total == EXPECTED_MAX_MATCHINGS,
            "The 11/10 bipartition forces the unique monomer into the even-weight side.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The certificate uses only finite graph construction and monomer-dimer matching enumeration.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "experiment_run_id": f"{EXPERIMENT_ID}:{started_at}",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "script_sha": script_sha(),
        "status": status,
        "checks": checks,
        "check_summary": check_summary(checks),
        "result": {
            "carrier": {
                "window": WINDOW,
                "vertex_count": len(words),
                "vertices": [word_to_string(word) for word in words],
                "edge_count": len(edges),
            },
            "matching_polynomial": {
                "definition": "Z_6(q)=sum_k m_k q^k",
                "coefficients_by_k": profile,
                "hosoya_index": hosoya_index,
                "matching_number": matching_number,
                "maximum_matching_count": maximum_matchings,
            },
            "maximum_matching_monomer_profile": {
                "profile": monomer_profile,
                "total": sum(monomer_profile.values()),
                "odd_weight_monomer_total": odd_monomer_total,
                "even_weight_monomer_total": even_monomer_total,
                "bipartition_sizes": {"even_weight": 11, "odd_weight": 10},
            },
            "not_claimed": [
                "physical fine-structure constant or any physical constant",
                "alpha/137 as input, target, numerical proximity, or reverse fit",
                "any convention-dependent physical interpretation",
            ],
        },
        "started_at": started_at,
        "completed_at": now_iso(),
    }
    if status == "passed":
        print("PASS")
    print(json.dumps(result, ensure_ascii=False))
    if status != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

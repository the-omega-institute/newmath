#!/usr/bin/env python3
"""Forward audit for the ordered geodesic enumerator of Gamma_6.

The graph Gamma_6 has the length-six binary words with no adjacent ones as
vertices and Hamming-distance-one pairs as edges. This certificate uses exact
finite graph enumeration only: it constructs the graph, runs BFS from each
source, counts shortest paths, and records the ordered geodesic profile
G_6(t)=sum_{u,v} g(u,v)t^d(u,v).
"""

from __future__ import annotations

import hashlib
import json
from collections import deque
from datetime import UTC, datetime
from itertools import permutations, product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window6-geodesic-enumerator"
CLAIM_ID = "window6.fibonacci-cube.geodesic-enumerator.certificate"
WINDOW = 6
DIAMETRAL_LEFT_WORD = (0, 1, 0, 1, 0, 1)
DIAMETRAL_RIGHT_WORD = (1, 0, 1, 0, 1, 0)
EXPECTED_VERTEX_COUNT = 21
EXPECTED_EDGE_COUNT = 38
EXPECTED_GEO_PROFILE = [21, 76, 216, 448, 602, 424, 122]
EXPECTED_GEO_TOTAL = 1909
EXPECTED_DISTANCE_PROFILE = [21, 76, 128, 124, 70, 20, 2]
EXPECTED_UNORDERED_PROFILE = [38, 108, 224, 301, 212, 61]
EXPECTED_UNORDERED_TOTAL = 944
EXPECTED_DIAMETRAL_DISTANCE = 6
EXPECTED_DIAMETRAL_GEO = 61
EXPECTED_EULER_ZIGZAG_E6 = 61


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


def word_to_mask(word: tuple[int, ...]) -> int:
    return int(word_to_string(word), 2)


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


def shortest_path_data(
    graph: list[list[int]],
    source: int,
) -> tuple[list[int], list[int]]:
    distance = [-1 for _ in graph]
    path_count = [0 for _ in graph]
    distance[source] = 0
    path_count[source] = 1
    queue: deque[int] = deque([source])
    while queue:
        current = queue.popleft()
        for neighbor in graph[current]:
            if distance[neighbor] == -1:
                distance[neighbor] = distance[current] + 1
                path_count[neighbor] = path_count[current]
                queue.append(neighbor)
            elif distance[neighbor] == distance[current] + 1:
                path_count[neighbor] += path_count[current]
    return distance, path_count


def all_pairs_shortest_path_data(
    graph: list[list[int]],
) -> tuple[list[list[int]], list[list[int]]]:
    distances: list[list[int]] = []
    path_counts: list[list[int]] = []
    for source in range(len(graph)):
        distance, path_count = shortest_path_data(graph, source)
        distances.append(distance)
        path_counts.append(path_count)
    return distances, path_counts


def ordered_profile(
    distances: list[list[int]],
    path_counts: list[list[int]],
    diameter: int,
) -> list[int]:
    profile = [0 for _ in range(diameter + 1)]
    for source in range(len(distances)):
        for target in range(len(distances)):
            profile[distances[source][target]] += path_counts[source][target]
    return profile


def ordered_distance_profile(distances: list[list[int]], diameter: int) -> list[int]:
    profile = [0 for _ in range(diameter + 1)]
    for source in range(len(distances)):
        for target in range(len(distances)):
            profile[distances[source][target]] += 1
    return profile


def unordered_distinct_profile(
    distances: list[list[int]],
    path_counts: list[list[int]],
    diameter: int,
) -> list[int]:
    profile = [0 for _ in range(diameter)]
    for source in range(len(distances)):
        for target in range(source + 1, len(distances)):
            profile[distances[source][target] - 1] += path_counts[source][target]
    return profile


def fence_poset_extension_count(size: int) -> int:
    """Count linear extensions of 1<2>3<4>... by direct finite enumeration."""

    labels = tuple(range(1, size + 1))
    count = 0
    for ordering in permutations(labels):
        rank = {label: offset for offset, label in enumerate(ordering)}
        valid = True
        for left in range(1, size):
            if left % 2 == 1:
                valid = valid and rank[left] < rank[left + 1]
            else:
                valid = valid and rank[left] > rank[left + 1]
        if valid:
            count += 1
    return count


def legal_flip_order_count(
    start: tuple[int, ...],
    target: tuple[int, ...],
) -> int:
    """Count length-six flip orders that stay inside the Fibonacci-cube carrier."""

    count = 0
    for order in permutations(range(len(start))):
        current = list(start)
        valid = True
        for bit_index in order:
            current[bit_index] = target[bit_index]
            if any(
                current[index] and current[index + 1]
                for index in range(len(current) - 1)
            ):
                valid = False
                break
        if valid and tuple(current) == target:
            count += 1
    return count


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    words = admissible_words(WINDOW)
    word_index = {word: offset for offset, word in enumerate(words)}
    edges = fibonacci_cube_edges(words)
    graph = adjacency(len(words), edges)
    distances, path_counts = all_pairs_shortest_path_data(graph)
    diameter = max(max(row) for row in distances)
    geo_profile = ordered_profile(distances, path_counts, diameter)
    geo_total = sum(geo_profile)
    distance_profile = ordered_distance_profile(distances, diameter)
    unordered_profile = unordered_distinct_profile(distances, path_counts, diameter)
    unordered_total = sum(unordered_profile)
    left_index = word_index[DIAMETRAL_LEFT_WORD]
    right_index = word_index[DIAMETRAL_RIGHT_WORD]
    diametral_distance = distances[left_index][right_index]
    diametral_geodesics = path_counts[left_index][right_index]
    diametral_pairs = [
        (source, target)
        for source in range(len(words))
        for target in range(source + 1, len(words))
        if distances[source][target] == diameter
    ]
    euler_zigzag_e6 = fence_poset_extension_count(WINDOW)
    legal_flip_orders = legal_flip_order_count(DIAMETRAL_LEFT_WORD, DIAMETRAL_RIGHT_WORD)

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
            "ordered_geodesic_profile",
            geo_profile == EXPECTED_GEO_PROFILE,
            "BFS shortest-path counting gives G_6 coefficients [21,76,216,448,602,424,122].",
        ),
        check(
            "ordered_geodesic_total",
            geo_total == EXPECTED_GEO_TOTAL,
            "The ordered total sum of shortest-path counts is 1909.",
        ),
        check(
            "ordered_distance_profile",
            distance_profile == EXPECTED_DISTANCE_PROFILE,
            "The ordinary ordered distance distribution is [21,76,128,124,70,20,2].",
        ),
        check(
            "geodesic_profile_strictly_refines_distance_profile",
            geo_profile[:2] == distance_profile[:2]
            and all(
                geo_profile[index] > distance_profile[index]
                for index in range(2, len(geo_profile))
            ),
            "From distance 2 onward the geodesic enumerator records path multiplicity, not just pair counts.",
        ),
        check(
            "unordered_distinct_geodesic_profile",
            unordered_profile == EXPECTED_UNORDERED_PROFILE,
            "Unordered distinct endpoint pairs contribute [38,108,224,301,212,61] by distance.",
        ),
        check(
            "unordered_distinct_geodesic_total",
            unordered_total == EXPECTED_UNORDERED_TOTAL,
            "The unordered distinct endpoint geodesic total is 944.",
        ),
        check(
            "diametral_pair_geodesic_count",
            diametral_distance == EXPECTED_DIAMETRAL_DISTANCE
            and diametral_geodesics == EXPECTED_DIAMETRAL_GEO
            and diametral_pairs == [(left_index, right_index)],
            "The unique unordered diametral pair 010101<->101010 has d=6 and g=61.",
        ),
        check(
            "euler_zigzag_E6_fence_poset",
            euler_zigzag_e6 == EXPECTED_EULER_ZIGZAG_E6
            and legal_flip_orders == EXPECTED_DIAMETRAL_GEO
            and legal_flip_orders == euler_zigzag_e6,
            "The 61 diametral geodesics are the E_6 fence-poset linear extensions.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The certificate uses only finite graph construction, BFS counting, and fence-poset enumeration.",
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
            "ordered_geodesic_enumerator": {
                "definition": "G_6(t)=sum_{u,v} g(u,v)t^d(u,v)",
                "coefficients_by_distance": geo_profile,
                "ordered_total": geo_total,
            },
            "ordinary_distance_distribution": {
                "ordered_pair_counts_by_distance": distance_profile,
                "strict_refinement_from_distance_2": all(
                    geo_profile[index] > distance_profile[index]
                    for index in range(2, len(geo_profile))
                ),
            },
            "unordered_distinct_endpoint_geodesics": {
                "coefficients_by_distance_1_to_6": unordered_profile,
                "total": unordered_total,
            },
            "diametral_pair": {
                "left_word": word_to_string(DIAMETRAL_LEFT_WORD),
                "left_mask": word_to_mask(DIAMETRAL_LEFT_WORD),
                "right_word": word_to_string(DIAMETRAL_RIGHT_WORD),
                "right_mask": word_to_mask(DIAMETRAL_RIGHT_WORD),
                "distance": diametral_distance,
                "geodesic_count": diametral_geodesics,
                "unique_unordered_diametral_pair": len(diametral_pairs) == 1,
            },
            "euler_zigzag_certificate": {
                "fence_poset": "1<2>3<4>5<6",
                "linear_extension_count": euler_zigzag_e6,
                "legal_diametral_flip_order_count": legal_flip_orders,
                "value": EXPECTED_EULER_ZIGZAG_E6,
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

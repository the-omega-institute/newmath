#!/usr/bin/env python3
"""Forward audit for diff-run geodesic counts in Fibonacci cubes.

For Gamma_m, vertices are length-m binary words with no adjacent ones and
edges join Hamming-distance-one words. This certificate checks that the number
of shortest paths between any two vertices factors over maximal consecutive
runs of differing coordinates: free interleaving between separated runs and
Euler-zigzag counts inside each run.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections import deque
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window-geodesic-run-factorization"
CLAIM_ID = "window.fibonacci-cube.geodesic-run-factorization.certificate"
MIN_WINDOW = 2
MAX_WINDOW = 7
EXPECTED_EULER_ZIGZAG_PREFIX = [1, 1, 1, 2, 5, 16, 61, 272]
EXPECTED_TOTAL_ORDERED_PAIRS = 1864
EXPECTED_WINDOW6_GEODESIC_PROFILE = [21, 76, 216, 448, 602, 424, 122]
EXAMPLE_WINDOW = 4
EXAMPLE_LEFT = "0101"
EXAMPLE_RIGHT = "1000"
EXAMPLE_COUNT = 3
DIAMETRAL_WINDOW = 6
DIAMETRAL_LEFT = "010101"
DIAMETRAL_RIGHT = "101010"
EXPECTED_DIAMETRAL_COUNT = 61


def now_iso() -> str:
    return datetime.now(UTC).isoformat()


def script_sha() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def fib(n: int) -> int:
    if n < 0:
        raise ValueError("Fibonacci index must be nonnegative")
    previous, current = 0, 1
    for _ in range(n):
        previous, current = current, previous + current
    return previous


def euler_zigzag_numbers(max_index: int) -> list[int]:
    """Compute A_n by the Entringer-Seidel boustrophedon triangle."""

    if max_index < 0:
        raise ValueError("Euler zigzag index must be nonnegative")
    triangle: list[list[int]] = [[1]]
    for row_index in range(1, max_index + 1):
        row = [0 for _ in range(row_index + 1)]
        for column in range(1, row_index + 1):
            row[column] = row[column - 1] + triangle[row_index - 1][row_index - column]
        triangle.append(row)
    return [row[-1] for row in triangle]


def coord_mask(coord: int, width: int) -> int:
    if coord < 0 or coord >= width:
        raise ValueError("coordinate out of range")
    return 1 << (width - 1 - coord)


def valid(word: int, width: int) -> bool:
    limit_mask = (1 << width) - 1
    return 0 <= word <= limit_mask and (word & (word >> 1)) == 0


def fibonacci_cube_words(width: int) -> list[int]:
    return [word for word in range(1 << width) if valid(word, width)]


def word_to_string(word: int, width: int) -> str:
    return format(word, f"0{width}b")


def parse_word(text: str) -> int:
    return int(text, 2)


def adjacency(words: list[int], width: int) -> list[list[int]]:
    index = {word: offset for offset, word in enumerate(words)}
    graph = [[] for _ in words]
    for source, word in enumerate(words):
        for coord in range(width):
            target = index.get(word ^ coord_mask(coord, width))
            if target is not None:
                graph[source].append(target)
        graph[source].sort()
    return graph


def shortest_path_data(graph: list[list[int]], source: int) -> tuple[list[int], list[int]]:
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


def diff_run_lengths(left: int, right: int, width: int) -> list[int]:
    lengths: list[int] = []
    current_length = 0
    for coord in range(width):
        differs = bool((left ^ right) & coord_mask(coord, width))
        if differs:
            current_length += 1
        elif current_length:
            lengths.append(current_length)
            current_length = 0
    if current_length:
        lengths.append(current_length)
    return lengths


def multinomial(total: int, parts: list[int]) -> int:
    numerator = math.factorial(total)
    denominator = 1
    for part in parts:
        denominator *= math.factorial(part)
    return numerator // denominator


def formula_n(left: int, right: int, width: int, zigzag: list[int]) -> int:
    run_lengths = diff_run_lengths(left, right, width)
    total = sum(run_lengths)
    value = multinomial(total, run_lengths)
    for length in run_lengths:
        value *= zigzag[length]
    return value


def profile_by_distance(
    distances: list[list[int]],
    path_counts: list[list[int]],
) -> list[int]:
    diameter = max(max(row) for row in distances)
    profile = [0 for _ in range(diameter + 1)]
    for source in range(len(distances)):
        for target in range(len(distances)):
            profile[distances[source][target]] += path_counts[source][target]
    return profile


def formula_profile_by_distance(words: list[int], width: int, zigzag: list[int]) -> list[int]:
    diameter = width
    profile = [0 for _ in range(diameter + 1)]
    for left in words:
        for right in words:
            distance = len(
                [
                    coord
                    for coord in range(width)
                    if (left ^ right) & coord_mask(coord, width)
                ]
            )
            profile[distance] += formula_n(left, right, width, zigzag)
    while len(profile) > 1 and profile[-1] == 0:
        profile.pop()
    return profile


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    zigzag = euler_zigzag_numbers(MAX_WINDOW)
    vertex_counts: dict[int, int] = {}
    pair_counts: dict[int, int] = {}
    mismatch_examples: list[dict[str, Any]] = []
    distance_profiles: dict[int, list[int]] = {}
    formula_distance_profiles: dict[int, list[int]] = {}

    for width in range(MIN_WINDOW, MAX_WINDOW + 1):
        words = fibonacci_cube_words(width)
        graph = adjacency(words, width)
        distances, path_counts = all_pairs_shortest_path_data(graph)
        vertex_counts[width] = len(words)
        pair_counts[width] = len(words) * len(words)
        distance_profiles[width] = profile_by_distance(distances, path_counts)
        formula_distance_profiles[width] = formula_profile_by_distance(words, width, zigzag)
        for source, left in enumerate(words):
            for target, right in enumerate(words):
                expected = formula_n(left, right, width, zigzag)
                observed = path_counts[source][target]
                if observed != expected:
                    mismatch_examples.append(
                        {
                            "m": width,
                            "u": word_to_string(left, width),
                            "v": word_to_string(right, width),
                            "bfs": observed,
                            "formula": expected,
                            "diff_runs": diff_run_lengths(left, right, width),
                        }
                    )
                    break
            if mismatch_examples:
                break

    example_left = parse_word(EXAMPLE_LEFT)
    example_right = parse_word(EXAMPLE_RIGHT)
    example_value = formula_n(example_left, example_right, EXAMPLE_WINDOW, zigzag)
    example_runs = diff_run_lengths(example_left, example_right, EXAMPLE_WINDOW)
    diametral_words = fibonacci_cube_words(DIAMETRAL_WINDOW)
    diametral_index = {word: offset for offset, word in enumerate(diametral_words)}
    diametral_graph = adjacency(diametral_words, DIAMETRAL_WINDOW)
    diametral_distances, diametral_path_counts = all_pairs_shortest_path_data(diametral_graph)
    diametral_left = parse_word(DIAMETRAL_LEFT)
    diametral_right = parse_word(DIAMETRAL_RIGHT)
    diametral_source = diametral_index[diametral_left]
    diametral_target = diametral_index[diametral_right]
    diametral_count = diametral_path_counts[diametral_source][diametral_target]
    diametral_distance = diametral_distances[diametral_source][diametral_target]
    total_ordered_pairs = sum(pair_counts.values())

    checks = [
        check(
            "euler_zigzag_seidel_prefix",
            zigzag == EXPECTED_EULER_ZIGZAG_PREFIX,
            "The Entringer-Seidel triangle gives A_0..A_7=[1,1,1,2,5,16,61,272].",
        ),
        check(
            "gamma_m_vertex_counts_m2_to_m7",
            all(vertex_counts[width] == fib(width + 2) for width in vertex_counts),
            "The no-adjacent-ones carrier has |V_m|=F_{m+2} for m=2..7.",
        ),
        check(
            "all_pairs_total_1864_m2_to_m7",
            total_ordered_pairs == EXPECTED_TOTAL_ORDERED_PAIRS,
            "The exhaustive ordered endpoint audit covers sum_m |V_m|^2=1864 pairs for m=2..7.",
        ),
        check(
            "bfs_formula_all_pairs_m2_to_m7",
            not mismatch_examples,
            "BFS shortest-path counts match multinomial(diff-runs)*prod A_run for every ordered pair.",
        ),
        check(
            "example_0101_to_1000_gamma4_count_3",
            example_runs == [2, 1] and example_value == EXAMPLE_COUNT,
            "In Gamma_4, 0101->1000 has diff runs (2,1) and N=3.",
        ),
        check(
            "diametral_gamma6_single_run_A6",
            diametral_distance == DIAMETRAL_WINDOW
            and diff_run_lengths(diametral_left, diametral_right, DIAMETRAL_WINDOW)
            == [DIAMETRAL_WINDOW]
            and diametral_count == EXPECTED_DIAMETRAL_COUNT
            and diametral_count == zigzag[DIAMETRAL_WINDOW],
            "The Gamma_6 pair 010101<->101010 is the single-run case and has A_6=61 geodesics.",
        ),
        check(
            "window6_distance_aggregated_profile_reproduces_anchor",
            distance_profiles[6] == EXPECTED_WINDOW6_GEODESIC_PROFILE
            and formula_distance_profiles[6] == EXPECTED_WINDOW6_GEODESIC_PROFILE,
            "Summing the per-pair formula by distance in m=6 reproduces [21,76,216,448,602,424,122].",
        ),
        check(
            "per_pair_generating_law_not_window6_repackage",
            not mismatch_examples
            and distance_profiles[6] == EXPECTED_WINDOW6_GEODESIC_PROFILE
            and total_ordered_pairs > pair_counts[6],
            "The certificate checks every endpoint pair across m=2..7; the m=6 profile is only its aggregate.",
        ),
        check(
            "formula_profile_matches_bfs_profile_m2_to_m7",
            all(
                distance_profiles[width] == formula_distance_profiles[width]
                for width in range(MIN_WINDOW, MAX_WINDOW + 1)
            ),
            "The closed formula and BFS agree after distance aggregation in every checked window.",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The audit uses only finite Fibonacci-cube graphs, BFS shortest-path counts, and integer Euler-zigzag numbers.",
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
                "window_range": [MIN_WINDOW, MAX_WINDOW],
                "vertex_counts": {str(width): count for width, count in vertex_counts.items()},
                "ordered_pair_counts": {str(width): count for width, count in pair_counts.items()},
                "total_ordered_pairs": total_ordered_pairs,
            },
            "formula": {
                "statement": "N(u,v)=multinomial(d;ell_1,...,ell_r)*prod_j A_{ell_j}.",
                "diff_runs": "ell_j are maximal consecutive runs of coordinates where u and v differ.",
                "zigzag_numbers": {str(index): value for index, value in enumerate(zigzag)},
            },
            "all_pair_audit": {
                "mismatches": mismatch_examples,
                "checked_windows": list(range(MIN_WINDOW, MAX_WINDOW + 1)),
            },
            "example": {
                "window": EXAMPLE_WINDOW,
                "u": EXAMPLE_LEFT,
                "v": EXAMPLE_RIGHT,
                "diff_runs": example_runs,
                "formula_count": example_value,
            },
            "diametral_special_case": {
                "window": DIAMETRAL_WINDOW,
                "u": DIAMETRAL_LEFT,
                "v": DIAMETRAL_RIGHT,
                "distance": diametral_distance,
                "diff_runs": diff_run_lengths(
                    diametral_left, diametral_right, DIAMETRAL_WINDOW
                ),
                "bfs_count": diametral_count,
                "A_6": zigzag[DIAMETRAL_WINDOW],
            },
            "window6_anchor_reproduction": {
                "bfs_distance_aggregated_profile": distance_profiles[6],
                "formula_distance_aggregated_profile": formula_distance_profiles[6],
                "interpretation": "The per-pair all-m formula generates the Window6 ordered geodesic profile rather than repackaging it.",
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

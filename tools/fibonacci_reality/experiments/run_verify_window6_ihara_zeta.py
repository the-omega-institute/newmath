#!/usr/bin/env python3
"""Forward audit for the Ihara-Hashimoto zeta invariant of Gamma_6.

The graph Gamma_6 has the length-six binary words with no adjacent ones as
vertices and Hamming-distance-one pairs as edges. This certificate uses exact
finite graph enumeration only: it constructs the Hashimoto non-backtracking
operator, recovers det(I-uB_6) from integer traces, verifies the stated
factorization, checks Bass' determinant formula, and records non-backtracking
closed-walk data.
"""

from __future__ import annotations

import hashlib
import json
from datetime import UTC, datetime
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any

EXPERIMENT_ID = "verify-window6-ihara-zeta"
CLAIM_ID = "window6.fibonacci-cube.ihara-zeta.certificate"
WINDOW = 6
EXPECTED_VERTEX_COUNT = 21
EXPECTED_EDGE_COUNT = 38
EXPECTED_DIRECTED_EDGE_COUNT = 76
EXPECTED_BETTI = 18
EXPECTED_ZETA_INV_COEFFS = [
    1,
    0,
    0,
    0,
    -44,
    0,
    -164,
    0,
    82,
    0,
    1336,
    0,
    846,
    0,
    -4572,
    0,
    -267,
    0,
    20372,
    0,
    -12630,
    0,
    -99836,
    0,
    -121973,
    0,
    -23160,
    0,
    1307734,
    0,
    2837184,
    0,
    -2746116,
    0,
    -11511240,
    0,
    -25340560,
    0,
    -18607404,
    0,
    310126528,
    0,
    335604280,
    0,
    -2064320142,
    0,
    -952059020,
    0,
    9276844953,
    0,
    -2795606604,
    0,
    -26468665854,
    0,
    29966111020,
    0,
    35616935139,
    0,
    -102853454232,
    0,
    54395104890,
    0,
    101943620936,
    0,
    -226919884299,
    0,
    226550007072,
    0,
    -141271850880,
    0,
    58319089920,
    0,
    -15642464256,
    0,
    2488320000,
    0,
    -179159040,
]
EXPECTED_P = [1, 10, 49, 162, 434, 1050, 2273, 4128, 5376, 3456]
EXPECTED_Q = [
    1,
    8,
    -2,
    -350,
    -2541,
    -10696,
    -32073,
    -73376,
    -128427,
    -162816,
    -132480,
    -51840,
]
EXPECTED_TRACE_PROFILE = {4: 176, 6: 984, 8: 7088, 10: 58800, 12: 448664}
EXPECTED_PRIMITIVE_COUNTS = {4: 44, 6: 164, 8: 864, 10: 5880, 12: 37292}


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


def adjacency_matrix(graph: list[list[int]]) -> list[list[int]]:
    matrix = [[0 for _ in graph] for _ in graph]
    for source, neighbors in enumerate(graph):
        for target in neighbors:
            matrix[source][target] = 1
    return matrix


def directed_edges(edges: list[tuple[int, int]]) -> list[tuple[int, int]]:
    arcs: list[tuple[int, int]] = []
    for source, target in edges:
        arcs.append((source, target))
        arcs.append((target, source))
    return arcs


def hashimoto_transition_rows(arcs: list[tuple[int, int]]) -> list[list[int]]:
    by_origin: dict[int, list[int]] = {}
    reverse_index = {(target, source): offset for offset, (source, target) in enumerate(arcs)}
    for offset, (source, _target) in enumerate(arcs):
        by_origin.setdefault(source, []).append(offset)
    rows: list[list[int]] = []
    for source, target in arcs:
        reverse = reverse_index[(source, target)]
        rows.append(
            [
                next_arc
                for next_arc in by_origin[target]
                if next_arc != reverse
            ]
        )
    return rows


def sparse_right_multiply(
    matrix: list[list[int]],
    transition_rows: list[list[int]],
) -> list[list[int]]:
    size = len(matrix)
    product_matrix = [[0 for _ in range(size)] for _ in range(size)]
    for row_index, row in enumerate(matrix):
        out_row = product_matrix[row_index]
        for mid_index, value in enumerate(row):
            if value:
                for column_index in transition_rows[mid_index]:
                    out_row[column_index] += value
    return product_matrix


def hashimoto_power_traces(
    transition_rows: list[list[int]],
    max_power: int,
) -> dict[int, int]:
    size = len(transition_rows)
    power = [[1 if row == column else 0 for column in range(size)] for row in range(size)]
    traces: dict[int, int] = {}
    for exponent in range(1, max_power + 1):
        power = sparse_right_multiply(power, transition_rows)
        traces[exponent] = sum(power[index][index] for index in range(size))
    return traces


def det_i_minus_ub_coefficients(traces: dict[int, int], degree: int) -> list[int]:
    coeffs = [1]
    for exponent in range(1, degree + 1):
        numerator = -sum(
            coeffs[exponent - trace_power] * traces[trace_power]
            for trace_power in range(1, exponent + 1)
        )
        if numerator % exponent != 0:
            raise ValueError(f"Newton coefficient at degree {exponent} is not integral")
        coeffs.append(numerator // exponent)
    return coeffs


def poly_mul(left: list[int], right: list[int]) -> list[int]:
    product_coeffs = [0 for _ in range(len(left) + len(right) - 1)]
    for left_degree, left_coeff in enumerate(left):
        for right_degree, right_coeff in enumerate(right):
            product_coeffs[left_degree + right_degree] += left_coeff * right_coeff
    return product_coeffs


def poly_pow(base: list[int], exponent: int) -> list[int]:
    result = [1]
    factor = base[:]
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = poly_mul(result, factor)
        factor = poly_mul(factor, factor)
        remaining >>= 1
    return result


def lift_s_to_u_squared(coeffs: list[int]) -> list[int]:
    lifted = [0 for _ in range(2 * len(coeffs) - 1)]
    for degree, coeff in enumerate(coeffs):
        lifted[2 * degree] = coeff
    return lifted


def factorization_rhs() -> list[int]:
    return poly_mul(
        poly_mul(poly_pow([1, 0, -1], EXPECTED_BETTI), lift_s_to_u_squared(EXPECTED_P)),
        lift_s_to_u_squared(EXPECTED_Q),
    )


def expected_bass_polynomial() -> list[int]:
    return poly_mul(
        poly_mul([1, 0, -1], lift_s_to_u_squared(EXPECTED_P)),
        lift_s_to_u_squared(EXPECTED_Q),
    )


def bareiss_det(matrix: list[list[int]]) -> int:
    work = [row[:] for row in matrix]
    size = len(work)
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        if work[pivot_index][pivot_index] == 0:
            swap_index = None
            for candidate in range(pivot_index + 1, size):
                if work[candidate][pivot_index] != 0:
                    swap_index = candidate
                    break
            if swap_index is None:
                return 0
            work[pivot_index], work[swap_index] = work[swap_index], work[pivot_index]
            sign *= -1
        pivot = work[pivot_index][pivot_index]
        for row_index in range(pivot_index + 1, size):
            for column_index in range(pivot_index + 1, size):
                work[row_index][column_index] = (
                    work[row_index][column_index] * pivot
                    - work[row_index][pivot_index] * work[pivot_index][column_index]
                ) // previous
        previous = pivot
        for clear_index in range(pivot_index + 1, size):
            work[clear_index][pivot_index] = 0
            work[pivot_index][clear_index] = 0
    return sign * work[size - 1][size - 1]


def bass_matrix_at(graph: list[list[int]], u_value: int) -> list[list[int]]:
    size = len(graph)
    matrix = [[0 for _ in range(size)] for _ in range(size)]
    for row in range(size):
        degree = len(graph[row])
        for column in range(size):
            if row == column:
                matrix[row][column] = 1 + u_value * u_value * (degree - 1)
            elif column in graph[row]:
                matrix[row][column] = -u_value
    return matrix


def interpolate_integer_polynomial(values: list[int]) -> list[int]:
    degree = len(values) - 1
    coeffs = [Fraction(0) for _ in range(degree + 1)]
    for point, value in enumerate(values):
        basis = [Fraction(1)]
        denominator = Fraction(1)
        for other in range(degree + 1):
            if other == point:
                continue
            basis = [Fraction(0) - other * basis[0]] + [
                basis[index - 1] - other * basis[index]
                for index in range(1, len(basis))
            ] + [basis[-1]]
            denominator *= point - other
        scale = Fraction(value, 1) / denominator
        for index, basis_coeff in enumerate(basis):
            coeffs[index] += scale * basis_coeff
    integer_coeffs: list[int] = []
    for coeff in coeffs:
        if coeff.denominator != 1:
            raise ValueError("Interpolated Bass coefficient is not integral")
        integer_coeffs.append(coeff.numerator)
    while len(integer_coeffs) > 1 and integer_coeffs[-1] == 0:
        integer_coeffs.pop()
    return integer_coeffs


def mobius(number: int) -> int:
    remaining = number
    prime = 2
    factors = 0
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            factors += 1
            if remaining % prime == 0:
                return 0
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        factors += 1
    return -1 if factors % 2 else 1


def divisors(number: int) -> list[int]:
    return [candidate for candidate in range(1, number + 1) if number % candidate == 0]


def primitive_cycle_counts(traces: dict[int, int], lengths: list[int]) -> dict[int, int]:
    counts: dict[int, int] = {}
    for length in lengths:
        total = sum(mobius(divisor) * traces[length // divisor] for divisor in divisors(length))
        if total % length != 0:
            raise ValueError(f"Primitive count at length {length} is not integral")
        counts[length] = total // length
    return counts


def check_summary(checks: list[dict[str, Any]]) -> dict[str, int]:
    passed = sum(1 for item in checks if item["passed"])
    total = len(checks)
    return {"total": total, "passed": passed, "failed": total - passed}


def main() -> None:
    started_at = now_iso()
    words = admissible_words(WINDOW)
    edges = fibonacci_cube_edges(words)
    graph = adjacency(len(words), edges)
    adjacency_mat = adjacency_matrix(graph)
    arcs = directed_edges(edges)
    transition_rows = hashimoto_transition_rows(arcs)
    traces = hashimoto_power_traces(transition_rows, EXPECTED_DIRECTED_EDGE_COUNT)
    zeta_inv_coeffs = det_i_minus_ub_coefficients(traces, EXPECTED_DIRECTED_EDGE_COUNT)
    rhs_coeffs = factorization_rhs()
    bass_expected = expected_bass_polynomial()
    bass_values = [
        bareiss_det(bass_matrix_at(graph, u_value))
        for u_value in range(len(bass_expected))
    ]
    bass_coeffs = interpolate_integer_polynomial(bass_values)
    primitive_counts = primitive_cycle_counts(traces, list(EXPECTED_PRIMITIVE_COUNTS))
    betti = len(edges) - len(words) + 1
    odd_trace_zero = all(traces[index] == 0 for index in range(1, 77, 2))
    odd_coeff_zero = all(
        coeff == 0 for degree, coeff in enumerate(zeta_inv_coeffs) if degree % 2 == 1
    )

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
            "hashimoto_directed_edge_count",
            len(arcs) == EXPECTED_DIRECTED_EDGE_COUNT,
            "Orienting the 38 undirected edges gives 76 directed edges.",
        ),
        check(
            "first_betti_number",
            betti == EXPECTED_BETTI,
            "The circuit rank is |E|-|V|+1=38-21+1=18.",
        ),
        check(
            "hashimoto_zeta_inverse_coefficients",
            zeta_inv_coeffs == EXPECTED_ZETA_INV_COEFFS,
            "Newton identities applied to tr(B_6^k), k=1..76, recover det(I-uB_6).",
        ),
        check(
            "zeta_inverse_even_polynomial_bipartite",
            odd_trace_zero and odd_coeff_zero,
            "The bipartite Fibonacci cube has zero odd non-backtracking traces and odd coefficients.",
        ),
        check(
            "ihara_hashimoto_factorization",
            rhs_coeffs == zeta_inv_coeffs and rhs_coeffs == EXPECTED_ZETA_INV_COEFFS,
            "The product (1-u^2)^18 P(u^2)Q(u^2) expands to det(I-uB_6).",
        ),
        check(
            "factor_polynomial_degrees",
            len(EXPECTED_P) == 10
            and EXPECTED_P[-1] != 0
            and len(EXPECTED_Q) == 12
            and EXPECTED_Q[-1] != 0
            and len(rhs_coeffs) == EXPECTED_DIRECTED_EDGE_COUNT + 1,
            "The P and Q factors have s-degrees 9 and 11 and total u-degree 76.",
        ),
        check(
            "nonbacktracking_odd_traces_zero",
            odd_trace_zero,
            "All odd tr(B_6^k) vanish for k=1,3,...,75.",
        ),
        check(
            "nonbacktracking_even_trace_profile",
            {length: traces[length] for length in EXPECTED_TRACE_PROFILE}
            == EXPECTED_TRACE_PROFILE,
            "The trace profile at k=4,6,8,10,12 is (176,984,7088,58800,448664).",
        ),
        check(
            "primitive_closed_cycle_counts",
            primitive_counts == EXPECTED_PRIMITIVE_COUNTS,
            "Mobius inversion gives primitive counts C_4,C_6,C_8,C_10,C_12.",
        ),
        check(
            "bass_determinant_factorization",
            bass_coeffs == bass_expected,
            "Integer-point Bareiss determinants interpolate to (1-u^2)P(u^2)Q(u^2).",
        ),
        check(
            "bass_ihara_formula",
            poly_mul(poly_pow([1, 0, -1], EXPECTED_BETTI - 1), bass_coeffs)
            == EXPECTED_ZETA_INV_COEFFS,
            "Bass' formula gives det(I-uB_6)=(1-u^2)^17 det(I-uA_6+u^2(D_6-I)).",
        ),
        check(
            "no_physical_alpha_input_or_readout",
            True,
            "The certificate uses only finite graph construction, integer matrices, and polynomial identities.",
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
                "directed_edge_count": len(arcs),
                "first_betti_number": betti,
            },
            "hashimoto_operator": {
                "definition": "B_6[e,f]=1 iff term(e)=orig(f) and f is not reverse(e)",
                "matrix_size": [len(arcs), len(arcs)],
                "row_sums": [len(row) for row in transition_rows],
            },
            "zeta_inverse": {
                "definition": "zeta_Gamma6(u)^-1=det(I_76-uB_6)",
                "coefficients_u_0_to_76": zeta_inv_coeffs,
                "factorization": {
                    "form": "(1-u^2)^18 P(u^2) Q(u^2)",
                    "P_coefficients_s_0_to_9": EXPECTED_P,
                    "Q_coefficients_s_0_to_11": EXPECTED_Q,
                },
            },
            "bass_determinant": {
                "definition": "det(I_21-uA_6+u^2(D_6-I_21))",
                "coefficients": bass_coeffs,
                "factorization": "(1-u^2) P(u^2) Q(u^2)",
            },
            "closed_walk_traces": {
                "odd_traces_zero": odd_trace_zero,
                "selected_even_traces": {
                    str(length): traces[length] for length in EXPECTED_TRACE_PROFILE
                },
                "primitive_counts": {
                    str(length): primitive_counts[length]
                    for length in EXPECTED_PRIMITIVE_COUNTS
                },
            },
            "adjacency_matrix": adjacency_mat,
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

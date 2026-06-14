#!/usr/bin/env python3
"""BC10 mod-3 edge-flux obstruction versus codon reading-frame phase class.

The test is deliberately cohomological.  It compares Z3-valued 1-cochains
through their class in C^1/im d^0, not through a count of three phases.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import permutations, product
import json
import math
import random
import sys
from pathlib import Path
from typing import Callable, Iterable


EXPERIMENT_ID = "bc10_mod3_flux_frame_obstruction"
CLAIM_ID = "bridge.window6_codon_q6.mod3_flux_frame_obstruction"
DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 310611
NULL_DRAWS = 8000

WINDOW_EDGE_MATRIX = [
    [28, 63, 23, 20],
    [63, 21, 21, 6],
    [23, 21, 2, 6],
    [20, 6, 6, 2],
]
WINDOW_CELL_NAMES = ("U_2", "U_1", "U_L", "U_R")

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
BASE_WEIGHT_Q6 = {"U": 0, "C": 1, "A": 1, "G": 2}

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


def mod3(value: int) -> int:
    return value % 3


def gf3_inv(value: int) -> int:
    value %= 3
    if value == 1:
        return 1
    if value == 2:
        return 2
    raise ZeroDivisionError("0 has no inverse in GF(3)")


def gf3_rref(matrix: list[list[int]]) -> tuple[list[list[int]], list[int]]:
    rows = [row[:] for row in matrix]
    if not rows:
        return [], []
    row_count = len(rows)
    col_count = len(rows[0])
    pivots: list[int] = []
    pivot_row = 0
    for col in range(col_count):
        found = None
        for row in range(pivot_row, row_count):
            if rows[row][col] % 3:
                found = row
                break
        if found is None:
            continue
        rows[pivot_row], rows[found] = rows[found], rows[pivot_row]
        inv = gf3_inv(rows[pivot_row][col])
        rows[pivot_row] = [(value * inv) % 3 for value in rows[pivot_row]]
        for row in range(row_count):
            if row == pivot_row:
                continue
            factor = rows[row][col] % 3
            if factor:
                rows[row] = [(a - factor * b) % 3 for a, b in zip(rows[row], rows[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break
    return rows, pivots


def gf3_rank(matrix: list[list[int]]) -> int:
    _, pivots = gf3_rref(matrix)
    return len(pivots)


def gf3_nullspace(matrix: list[list[int]]) -> list[list[int]]:
    if not matrix:
        return []
    rref, pivots = gf3_rref(matrix)
    col_count = len(matrix[0])
    pivot_set = set(pivots)
    basis = []
    for free_col in range(col_count):
        if free_col in pivot_set:
            continue
        vector = [0] * col_count
        vector[free_col] = 1
        for row, pivot_col in enumerate(pivots):
            vector[pivot_col] = (-rref[row][free_col]) % 3
        basis.append(vector)
    return basis


def gf3_solve(matrix: list[list[int]], rhs: list[int]) -> list[int] | None:
    augmented = [row[:] + [value % 3] for row, value in zip(matrix, rhs)]
    rref, pivots = gf3_rref(augmented)
    col_count = len(matrix[0]) if matrix else 0
    for row in rref:
        if all(value % 3 == 0 for value in row[:col_count]) and row[col_count] % 3:
            return None
    solution = [0] * col_count
    for row, pivot_col in enumerate(pivots):
        if pivot_col < col_count:
            solution[pivot_col] = rref[row][col_count] % 3
    return solution


def incidence_matrix(vertex_count: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    matrix = []
    for left, right in edges:
        row = [0] * vertex_count
        row[left] = (row[left] - 1) % 3
        row[right] = (row[right] + 1) % 3
        matrix.append(row)
    return matrix


def exact_cochains(vertex_count: int, edges: list[tuple[int, int]]) -> list[list[int]]:
    exact = []
    seen = set()
    for potential in product((0, 1, 2), repeat=vertex_count):
        cochain = tuple((potential[right] - potential[left]) % 3 for left, right in edges)
        if cochain not in seen:
            seen.add(cochain)
            exact.append(list(cochain))
    return exact


def connected_components(vertex_count: int, edges: list[tuple[int, int]]) -> int:
    parent = list(range(vertex_count))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(left: int, right: int) -> None:
        root_left = find(left)
        root_right = find(right)
        if root_left != root_right:
            parent[root_right] = root_left

    for left, right in edges:
        union(left, right)
    return len({find(index) for index in range(vertex_count)})


def cochain_profile(vertex_count: int, edges: list[tuple[int, int]], tau: list[int]) -> dict[str, object]:
    matrix = incidence_matrix(vertex_count, edges)
    exact = gf3_solve(matrix, [value % 3 for value in tau])
    rank_b = gf3_rank(matrix)
    components = connected_components(vertex_count, edges)
    h_dim = len(edges) - rank_b
    exact_space = exact_cochains(vertex_count, edges)
    harmonic = min(
        ([(value - exact_value) % 3 for value, exact_value in zip(tau, exact_part)] for exact_part in exact_space),
        key=lambda item: (sum(1 for value in item if value % 3), item),
    )

    norm_tau = sum(1 for value in tau if value % 3)
    norm_h = sum(1 for value in harmonic if value % 3)
    return {
        "edge_count": len(edges),
        "vertex_count": vertex_count,
        "component_count": components,
        "coboundary_rank": rank_b,
        "r3": h_dim,
        "exact": exact is not None,
        "nonzero_class": exact is None,
        "h_weight": norm_h,
        "tau_weight": norm_tau,
        "T3": 0.0 if norm_tau == 0 else norm_h / norm_tau,
        "phase_balance": dict(sorted(Counter(value % 3 for value in tau).items())),
    }


def path_integral(
    edge_index: dict[tuple[int, int], int],
    tau: list[int],
    cycle: list[int],
) -> int:
    total = 0
    for left, right in zip(cycle, cycle[1:] + cycle[:1]):
        if (left, right) in edge_index:
            total += tau[edge_index[(left, right)]]
        elif (right, left) in edge_index:
            total -= tau[edge_index[(right, left)]]
        else:
            raise ValueError(f"cycle uses missing edge {(left, right)!r}")
    return total % 3


def directed_cycle_multiset(vertex_count: int, edges: list[tuple[int, int]], tau: list[int]) -> list[int]:
    edge_index = {edge: index for index, edge in enumerate(edges)}
    values = []
    for vertex in range(vertex_count):
        if (vertex, vertex) in edge_index:
            values.append(tau[edge_index[(vertex, vertex)]] % 3)
    for length in range(2, min(vertex_count, 4) + 1):
        for cycle in permutations(range(vertex_count), length):
            if min(cycle) != cycle[0]:
                continue
            if cycle[1] > cycle[-1]:
                continue
            try:
                values.append(path_integral(edge_index, tau, list(cycle)))
            except ValueError:
                continue
    return sorted(values)


def dihedral_orbit(values: list[int]) -> list[list[int]]:
    n = len(values)
    rotations = [values[index:] + values[:index] for index in range(n)]
    reversed_values = list(reversed(values))
    rotations += [reversed_values[index:] + reversed_values[:index] for index in range(n)]
    return sorted({tuple(item) for item in rotations})


def canonical_phase(values: list[int]) -> list[int]:
    return list(dihedral_orbit([value % 3 for value in values])[0])


def tail_ge(observed: float, values: list[float]) -> float:
    return (sum(1 for value in values if value >= observed - 1e-15) + 1) / (len(values) + 1)


def tail_le(observed: float, values: list[float]) -> float:
    return (sum(1 for value in values if value <= observed + 1e-15) + 1) / (len(values) + 1)


def determinant_bareiss(matrix: list[list[int]]) -> int:
    if any(len(row) != len(matrix) for row in matrix):
        raise ValueError("determinant requires a square matrix")
    a = [row[:] for row in matrix]
    n = len(a)
    previous = 1
    sign = 1
    for index in range(n - 1):
        if a[index][index] == 0:
            swap = None
            for row in range(index + 1, n):
                if a[row][index] != 0:
                    swap = row
                    break
            if swap is None:
                return 0
            a[index], a[swap] = a[swap], a[index]
            sign = -sign
        pivot = a[index][index]
        for row in range(index + 1, n):
            for col in range(index + 1, n):
                a[row][col] = (a[row][col] * pivot - a[row][index] * a[index][col]) // previous
        previous = pivot
        for row in range(index + 1, n):
            a[row][index] = 0
    return sign * a[n - 1][n - 1]


def transpose(matrix: list[list[int]]) -> list[list[int]]:
    return [list(col) for col in zip(*matrix)]


def window_edges_and_tau() -> tuple[list[tuple[int, int]], list[int]]:
    edges = []
    tau = []
    for left, row in enumerate(WINDOW_EDGE_MATRIX):
        for right, value in enumerate(row):
            if value:
                edges.append((left, right))
                tau.append(value % 3)
    return edges, tau


def window_sigma() -> dict[str, object]:
    edges, tau = window_edges_and_tau()
    profile = cochain_profile(len(WINDOW_EDGE_MATRIX), edges, tau)
    reduced = [[value % 3 for value in row] for row in WINDOW_EDGE_MATRIX]
    left_kernel = gf3_nullspace(transpose(reduced))
    witness = min((vector for vector in left_kernel if any(vector)), default=[])
    annihilates_rows = [
        sum(witness[col] * reduced[row][col] for col in range(len(reduced))) % 3
        for row in range(len(reduced))
    ] if witness else []
    cycle_integrals = directed_cycle_multiset(len(WINDOW_EDGE_MATRIX), edges, tau)
    profile.update(
        {
            "source": "forced_window_structure finite four-cell edge-flux matrix",
            "cell_order": list(WINDOW_CELL_NAMES),
            "determinant": determinant_bareiss(WINDOW_EDGE_MATRIX),
            "determinant_mod3": determinant_bareiss(WINDOW_EDGE_MATRIX) % 3,
            "left_kernel_dimension": len(left_kernel),
            "left_kernel_witness": witness,
            "left_kernel_annihilates_rows": annihilates_rows,
            "tau": tau,
            "phase_orientation": canonical_phase(tau),
            "cycle_integral_multiset": dict(sorted(Counter(cycle_integrals).items())),
        }
    )
    return profile


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def load_vectors() -> list[dict[str, object]]:
    data = json.loads(DATA_PATH.read_text())
    if data.get("schema") != "codon_q6_selection_vectors.v1":
        raise ValueError(f"unexpected data schema: {data.get('schema')!r}")
    rows = []
    for row in data["vectors"]:
        codon = str(row["codon"])
        bits = tuple(int(bit) for bit in row["q6_bits"])
        if bits != codon_to_q6(codon):
            raise ValueError(f"codon/q6 mismatch for {codon}")
        if CODON_TO_FAMILY[codon] != ("Stop" if row["amino_acid"] == "*" else CODON_TO_FAMILY[codon]):
            raise ValueError(f"codon family table mismatch for {codon}")
        rows.append(dict(row))
    if len(rows) != 64:
        raise ValueError(f"expected 64 vectors, got {len(rows)}")
    return rows


def f3_unit(rows: list[dict[str, object]]) -> float:
    positives = sorted({abs(float(row["f3_loading"])) for row in rows if row.get("f3_loading")})
    if not positives:
        raise ValueError("f3_loading vector is empty")
    return positives[0]


def row_f3_int(row: dict[str, object], unit: float) -> int | None:
    value = row.get("f3_loading")
    if value is None:
        return None
    return int(round(float(value) / unit))


def phase_flux_from_rows(rows: list[dict[str, object]]) -> list[int]:
    unit = f3_unit(rows)
    tau = []
    for phase in range(3):
        total = 0
        for row in rows:
            value = row_f3_int(row, unit)
            if value is None:
                continue
            codon = str(row["codon"])
            total += value * BASE_WEIGHT_Q6[codon[phase]]
        tau.append(total % 3)
    return tau


def codon_sigma(rows: list[dict[str, object]]) -> dict[str, object]:
    tau = phase_flux_from_rows(rows)
    edges = [(0, 1), (1, 2), (2, 0)]
    profile = cochain_profile(3, edges, tau)
    cycle_integrals = [sum(tau) % 3]
    unit = f3_unit(rows)
    phase_integer_totals = []
    for phase in range(3):
        total = 0
        for row in rows:
            value = row_f3_int(row, unit)
            if value is not None:
                total += value * BASE_WEIGHT_Q6[str(row["codon"])[phase]]
        phase_integer_totals.append(total)
    profile.update(
        {
            "source": "codon_q6_selection_vectors.f3_loading aggregated by codon position",
            "edge_model": "position cycle C3 with Q6 base Hamming-weight coefficients",
            "tau": tau,
            "phase_integer_totals": phase_integer_totals,
            "f3_unit": unit,
            "sense_values": sum(1 for row in rows if row.get("f3_loading") is not None),
            "missing_f3_codons": [str(row["codon"]) for row in rows if row.get("f3_loading") is None],
            "phase_orientation": canonical_phase(tau),
            "cycle_integral_multiset": dict(sorted(Counter(cycle_integrals).items())),
        }
    )
    return profile


def random_cochain_same_support_and_flux(tau: list[int], rng: random.Random) -> list[int]:
    support = [index for index, value in enumerate(tau) if value % 3]
    total = sum(tau) % 3
    candidate = [0] * len(tau)
    for _ in range(1000):
        for index in support:
            candidate[index] = rng.choice((1, 2))
        if sum(candidate) % 3 == total:
            return candidate[:]
    while True:
        for index in support:
            candidate[index] = rng.choice((1, 2))
        if sum(candidate) % 3 == total:
            return candidate[:]


def random_degree_preserving_directed_rewire(edges: list[tuple[int, int]], rng: random.Random) -> list[tuple[int, int]]:
    lefts = [left for left, _ in edges]
    rights = [right for _, right in edges]
    rng.shuffle(rights)
    return list(zip(lefts, rights))


def window_null(window: dict[str, object], rng: random.Random) -> dict[str, object]:
    edges, tau = window_edges_and_tau()
    observed_t3 = float(window["T3"])
    observed_nonzero = bool(window["nonzero_class"])
    rewired_t3 = []
    rewired_nonzero = 0
    random_t3 = []
    random_nonzero = 0
    for _ in range(NULL_DRAWS):
        rewired_edges = random_degree_preserving_directed_rewire(edges, rng)
        rewired_profile = cochain_profile(len(WINDOW_EDGE_MATRIX), rewired_edges, tau)
        rewired_t3.append(float(rewired_profile["T3"]))
        rewired_nonzero += int(bool(rewired_profile["nonzero_class"]))

        random_tau = random_cochain_same_support_and_flux(tau, rng)
        random_profile = cochain_profile(len(WINDOW_EDGE_MATRIX), edges, random_tau)
        random_t3.append(float(random_profile["T3"]))
        random_nonzero += int(bool(random_profile["nonzero_class"]))
    return {
        "degree_preserving_rewire": {
            "draws": NULL_DRAWS,
            "p_T3_ge_observed": tail_ge(observed_t3, rewired_t3),
            "nonzero_class_rate": rewired_nonzero / NULL_DRAWS,
            "observed_nonzero_class": observed_nonzero,
        },
        "same_support_total_flux_random_cochain": {
            "draws": NULL_DRAWS,
            "p_T3_ge_observed": tail_ge(observed_t3, random_t3),
            "nonzero_class_rate": random_nonzero / NULL_DRAWS,
            "observed_nonzero_class": observed_nonzero,
        },
    }


def permuted_loading_rows(rows: list[dict[str, object]], rng: random.Random) -> list[dict[str, object]]:
    values = [row.get("f3_loading") for row in rows]
    rng.shuffle(values)
    out = []
    for row, value in zip(rows, values):
        new_row = dict(row)
        new_row["f3_loading"] = value
        out.append(new_row)
    return out


def wobble_preserving_rows(rows: list[dict[str, object]], rng: random.Random) -> list[dict[str, object]]:
    by_third: dict[str, list[object]] = defaultdict(list)
    for row in rows:
        by_third[str(row["codon"])[2]].append(row.get("f3_loading"))
    for values in by_third.values():
        rng.shuffle(values)
    cursors = {base: 0 for base in BASES}
    out = []
    for row in rows:
        base = str(row["codon"])[2]
        new_row = dict(row)
        new_row["f3_loading"] = by_third[base][cursors[base]]
        cursors[base] += 1
        out.append(new_row)
    return out


def family_preserving_rows(rows: list[dict[str, object]], rng: random.Random) -> list[dict[str, object]]:
    by_family: dict[str, list[object]] = defaultdict(list)
    for row in rows:
        by_family[CODON_TO_FAMILY[str(row["codon"])]].append(row.get("f3_loading"))
    for values in by_family.values():
        rng.shuffle(values)
    cursors = {family: 0 for family in by_family}
    out = []
    for row in rows:
        family = CODON_TO_FAMILY[str(row["codon"])]
        new_row = dict(row)
        new_row["f3_loading"] = by_family[family][cursors[family]]
        cursors[family] += 1
        out.append(new_row)
    return out


def phase_label_canonical_t3(tau: list[int]) -> float:
    best = 0.0
    edges = [(0, 1), (1, 2), (2, 0)]
    for perm in dihedral_orbit([0, 1, 2]):
        permuted = [0, 0, 0]
        for old, new in enumerate(perm):
            permuted[new] = tau[old]
        best = max(best, float(cochain_profile(3, edges, permuted)["T3"]))
    return best


def codon_null(rows: list[dict[str, object]], codon: dict[str, object], rng: random.Random) -> dict[str, object]:
    observed_t3 = float(codon["T3"])
    observed_integral = sum(int(value) for value in codon["tau"]) % 3
    null_specs: list[tuple[str, Callable[[list[dict[str, object]], random.Random], list[dict[str, object]]]]] = [
        ("frame_destroying_usage_preserving", permuted_loading_rows),
        ("wobble_preserving", wobble_preserving_rows),
        ("family_preserving", family_preserving_rows),
    ]
    result: dict[str, object] = {}
    for name, sampler in null_specs:
        t3_values = []
        integral_hits = 0
        nonzero = 0
        for _ in range(NULL_DRAWS):
            sampled = sampler(rows, rng)
            tau = phase_flux_from_rows(sampled)
            profile = cochain_profile(3, [(0, 1), (1, 2), (2, 0)], tau)
            t3_values.append(float(profile["T3"]))
            integral_hits += int(sum(tau) % 3 == observed_integral)
            nonzero += int(bool(profile["nonzero_class"]))
        result[name] = {
            "draws": NULL_DRAWS,
            "p_T3_ge_observed": tail_ge(observed_t3, t3_values),
            "p_T3_le_observed": tail_le(observed_t3, t3_values),
            "nonzero_class_rate": nonzero / NULL_DRAWS,
            "same_cycle_integral_rate": integral_hits / NULL_DRAWS,
        }
    result["phase_label_D3_quotient"] = {
        "observed_phase_orientation": codon["phase_orientation"],
        "observed_T3_after_D3_quotient": phase_label_canonical_t3([int(value) for value in codon["tau"]]),
        "allowed_orientations": dihedral_orbit([int(value) for value in codon["tau"]]),
    }
    return result


def signatures_compatible(window: dict[str, object], codon: dict[str, object]) -> bool:
    window_integrals = {int(key): value for key, value in window["cycle_integral_multiset"].items()}
    codon_integrals = {int(key): value for key, value in codon["cycle_integral_multiset"].items()}
    nonzero_window = {key for key, count in window_integrals.items() if key % 3 and count}
    nonzero_codon = {key for key, count in codon_integrals.items() if key % 3 and count}
    return bool(nonzero_window) and bool(nonzero_codon)


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    rows = load_vectors()

    window = window_sigma()
    codon = codon_sigma(rows)
    nulls = {
        "window": window_null(window, rng),
        "codon": codon_null(rows, codon, rng),
    }

    checks = [
        check_row("window_edge_matrix_determinant", window["determinant"], 10350),
        check_row("window_det_mod3_zero", window["determinant_mod3"], 0),
        check_row("window_left_kernel_annihilates_rows", window["left_kernel_annihilates_rows"], [0, 0, 0, 0]),
        check_row("window_obstruction_class_nonzero", window["nonzero_class"], True),
        check_row("codon_vector_count", len(rows), 64),
        check_row("codon_q6_encoding_count", len({codon_to_q6(str(row["codon"])) for row in rows}), 64),
        check_row("codon_f3_sense_value_count", codon["sense_values"], 61),
        check_row("codon_obstruction_class_nonzero", codon["nonzero_class"], True),
    ]

    codon_tail_extreme = all(
        nulls["codon"][name]["p_T3_ge_observed"] <= 0.05
        for name in ("frame_destroying_usage_preserving", "wobble_preserving", "family_preserving")
    )
    compatible = signatures_compatible(window, codon)
    both_nonzero = bool(window["nonzero_class"]) and bool(codon["nonzero_class"])
    self_checks_ok = all(row["ok"] for row in checks)

    if not self_checks_ok:
        status = "needs_derivation"
        note = "Self-checks failed; the cohomology verdict is not emitted as evidence."
    elif both_nonzero and codon_tail_extreme and compatible:
        status = "certified"
        note = (
            "Both sides carry nonzero Z3 cohomology classes. The codon f3 phase class is "
            "tested on the position cycle after D3 phase quotienting and lies in the extreme "
            "tail of the usage-, wobble-, and family-preserving nulls."
        )
    elif both_nonzero and compatible:
        status = "coincidence"
        note = (
            "Both sides have nonzero mod-3 cohomology classes and compatible nonzero cycle "
            "integrals, but the codon harmonic fraction is not extreme against every stricter "
            "codon null. This is obstruction-level similarity, not a certified bridge."
        )
    else:
        status = "refuted"
        note = (
            "The mod-3 cohomology obstruction required by the design is absent on at least one "
            "side or the cycle-integral multisets are incompatible."
        )

    emit(
        status,
        sigma3_window=window,
        sigma3_codon=codon,
        nulls=nulls,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Trace-deflated orientation test for edge-hiding versus codon-E1 usage."""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
from pathlib import Path
import random
import sys
from typing import Any

import run_bypass_conductance_extremality as omega
import run_codon_e1_heldout_crossorganism_gate as e1_base


EXPERIMENT_ID = "edge_hiding_e1_orientation_same_signal"
CLAIM_ID = "bridge.genetic_code.edge_hiding_e1_orientation.same_signal"

N_BOOTSTRAP = 10000
BOOTSTRAP_SEED_PREFIX = "edge_hiding_e1_orientation_same_signal.cluster_bootstrap"
ALPHA = 0.01
TOL = 1.0e-10


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def check_row(name: str, ok: bool, **fields: object) -> dict[str, object]:
    row = {"name": name, "ok": bool(ok)}
    row.update(fields)
    return row


def stable_seed(text: str) -> int:
    import hashlib

    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def sample_std(values: list[float], center: float) -> float:
    if len(values) < 2:
        return 0.0
    return math.sqrt(sum((value - center) * (value - center) for value in values) / (len(values) - 1))


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        raise ValueError("cannot take percentile of an empty list")
    position = (len(ordered) - 1) * q
    low = int(math.floor(position))
    high = int(math.ceil(position))
    if low == high:
        return ordered[low]
    return ordered[low] * (high - position) + ordered[high] * (position - low)


def hamming_distance(left: str, right: str) -> int:
    return sum(a != b for a, b in zip(left, right))


def h34_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    for codon in codons:
        left = index[codon]
        for pos in range(3):
            for base in e1_base.BASES:
                if base == codon[pos]:
                    continue
                other = codon[:pos] + base + codon[pos + 1 :]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


Matrix = list[list[float]]
Vector = list[float]


def zeros(rows: int, cols: int) -> Matrix:
    return [[0.0 for _ in range(cols)] for _ in range(rows)]


def identity(size: int) -> Matrix:
    return [[1.0 if row == col else 0.0 for col in range(size)] for row in range(size)]


def transpose(matrix: Matrix) -> Matrix:
    return [list(column) for column in zip(*matrix)]


def dot(left: Vector, right: Vector) -> float:
    return sum(a * b for a, b in zip(left, right))


def matmul(left: Matrix, right: Matrix) -> Matrix:
    right_t = transpose(right)
    return [[dot(row, column) for column in right_t] for row in left]


def matvec(matrix: Matrix, vector: Vector) -> Vector:
    return [dot(row, vector) for row in matrix]


def matadd(left: Matrix, right: Matrix, scale_right: float = 1.0) -> Matrix:
    return [
        [a + scale_right * b for a, b in zip(left_row, right_row)]
        for left_row, right_row in zip(left, right)
    ]


def matscale(matrix: Matrix, scale: float) -> Matrix:
    return [[scale * value for value in row] for row in matrix]


def outer(left: Vector, right: Vector) -> Matrix:
    return [[a * b for b in right] for a in left]


def trace(matrix: Matrix) -> float:
    return sum(matrix[index][index] for index in range(len(matrix)))


def max_abs_matrix(matrix: Matrix) -> float:
    return max(abs(value) for row in matrix for value in row)


def max_abs_matrix_diff(left: Matrix, right: Matrix) -> float:
    return max(abs(a - b) for left_row, right_row in zip(left, right) for a, b in zip(left_row, right_row))


def matrix_sum(matrices: list[Matrix]) -> Matrix:
    if not matrices:
        raise ValueError("cannot sum an empty matrix list")
    out = zeros(len(matrices[0]), len(matrices[0][0]))
    for matrix in matrices:
        out = matadd(out, matrix)
    return out


def jacobi_eigen_symmetric(matrix: Matrix, tol: float = 1.0e-12, max_sweeps: int = 300) -> tuple[Vector, Matrix]:
    size = len(matrix)
    work = [row[:] for row in matrix]
    vectors = identity(size)
    for _sweep in range(max_sweeps):
        pivot_row = 0
        pivot_col = 1 if size > 1 else 0
        pivot_abs = 0.0
        for row in range(size):
            for col in range(row + 1, size):
                value = abs(work[row][col])
                if value > pivot_abs:
                    pivot_abs = value
                    pivot_row = row
                    pivot_col = col
        if pivot_abs <= tol:
            break

        app = work[pivot_row][pivot_row]
        aqq = work[pivot_col][pivot_col]
        apq = work[pivot_row][pivot_col]
        tau = (aqq - app) / (2.0 * apq)
        tangent = math.copysign(1.0 / (abs(tau) + math.sqrt(1.0 + tau * tau)), tau)
        cosine = 1.0 / math.sqrt(1.0 + tangent * tangent)
        sine = tangent * cosine

        for index in range(size):
            if index == pivot_row or index == pivot_col:
                continue
            aip = work[index][pivot_row]
            aiq = work[index][pivot_col]
            work[index][pivot_row] = cosine * aip - sine * aiq
            work[pivot_row][index] = work[index][pivot_row]
            work[index][pivot_col] = sine * aip + cosine * aiq
            work[pivot_col][index] = work[index][pivot_col]

        work[pivot_row][pivot_row] = cosine * cosine * app - 2.0 * sine * cosine * apq + sine * sine * aqq
        work[pivot_col][pivot_col] = sine * sine * app + 2.0 * sine * cosine * apq + cosine * cosine * aqq
        work[pivot_row][pivot_col] = 0.0
        work[pivot_col][pivot_row] = 0.0

        for index in range(size):
            vip = vectors[index][pivot_row]
            viq = vectors[index][pivot_col]
            vectors[index][pivot_row] = cosine * vip - sine * viq
            vectors[index][pivot_col] = sine * vip + cosine * viq

    return [work[index][index] for index in range(size)], vectors


def symmetric_pseudoinverse(matrix: Matrix, tol: float = 1.0e-11) -> tuple[Matrix, int, Vector]:
    eigenvalues, eigenvectors_by_row = jacobi_eigen_symmetric(matrix)
    max_eigenvalue = max((abs(value) for value in eigenvalues), default=0.0)
    cutoff = max(tol, max_eigenvalue * 1.0e-10)
    out = zeros(len(matrix), len(matrix))
    rank = 0
    for column, eigenvalue in enumerate(eigenvalues):
        if eigenvalue <= cutoff:
            continue
        rank += 1
        vector = [eigenvectors_by_row[row][column] for row in range(len(matrix))]
        component = matscale(outer(vector, vector), 1.0 / eigenvalue)
        out = matadd(out, component)
    return out, rank, eigenvalues


def build_l_matrix(full_codons: list[str], sense_codons: list[str]) -> Matrix:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = e1_base.families_by_aa(sense_codons)
    columns: list[list[float]] = []
    for full_column in e1_base.e1_character_basis(full_codons):
        restricted = [full_column[full_index[codon]] for codon in sense_codons]
        columns.append(e1_base.project_syn(restricted, families, sense_index))
    return transpose(columns)


def projector_checks(u1: Matrix, codons: list[str]) -> dict[str, object]:
    p1 = matmul(u1, transpose(u1))
    max_formula_error = 0.0
    for left, codon_left in enumerate(codons):
        for right, codon_right in enumerate(codons):
            expected = (9.0 - 4.0 * hamming_distance(codon_left, codon_right)) / 64.0
            max_formula_error = max(max_formula_error, abs(float(p1[left][right]) - expected))
    return {
        "max_abs_p1_formula_error": round_float(max_formula_error, 14),
        "ok": max_formula_error <= 1.0e-12,
    }


def build_omega_states() -> dict[str, Any]:
    codons = omega.codon_order()
    families = omega.family_order(codons)
    labels = omega.standard_labels(codons, families)
    q6_edges, neighbors = omega.q6_edges_and_neighbors(codons)
    edge_set = {(left, right) for left, right, _orbit in q6_edges}
    atoms = omega.box_wobble_atoms(codons, labels)
    atom_sizes = [len(atom) for atom in atoms]
    vertex_to_atom = [-1] * len(codons)
    for atom_index, atom in enumerate(atoms):
        for vertex in atom:
            vertex_to_atom[vertex] = atom_index

    pair_profiles = omega.atom_pair_edge_profiles(atoms, vertex_to_atom, q6_edges)
    observed_groups = omega.observed_atom_groups(labels, vertex_to_atom, len(atoms))
    observed_signature = omega.state_signature(observed_groups, atom_sizes, pair_profiles)
    base_states = omega.enumerate_conditioned_states(atom_sizes, pair_profiles, observed_signature)
    observed_state = tuple(sorted(tuple(sorted(group)) for group in observed_groups))

    all_base_groups = sorted({group for state in base_states for group in state})
    descriptor_cache = {
        group: omega.full_group_descriptor(group, atoms, atom_sizes, pair_profiles, q6_edges, neighbors, edge_set)
        for group in all_base_groups
    }
    observed_full_signature = omega.full_state_signature(observed_state, descriptor_cache)
    states = [
        state
        for state in base_states
        if omega.full_state_signature(state, descriptor_cache) == observed_full_signature
    ]

    stop_label = families.index("Stop")
    stop_group = next(
        group
        for group in observed_groups
        if any(labels[vertex] == stop_label for atom in group for vertex in atoms[atom])
    )
    stop_descriptor = descriptor_cache[stop_group]
    stop_candidates_by_state = Counter(
        sum(1 for group in state if descriptor_cache[group] == stop_descriptor)
        for state in states
    )
    observed_state_index = states.index(observed_state) if observed_state in states else -1
    return {
        "codons": codons,
        "families": families,
        "labels": labels,
        "atoms": atoms,
        "states": states,
        "base_states": base_states,
        "observed_state": observed_state,
        "observed_state_index": observed_state_index,
        "descriptor_cache": descriptor_cache,
        "stop_descriptor": stop_descriptor,
        "stop_candidates_by_state": dict(sorted(stop_candidates_by_state.items())),
        "atom_sizes": atom_sizes,
    }


def group_edge_data(
    group: tuple[int, ...],
    atoms: list[tuple[int, ...]],
    edges: list[tuple[int, int]],
    edge_contrib: dict[tuple[int, int], Matrix],
) -> tuple[Matrix, int]:
    vertices = set(omega.group_vertices(group, atoms))
    matrix = zeros(9, 9)
    edge_count = 0
    for left, right in edges:
        if left in vertices and right in vertices:
            matrix = matadd(matrix, edge_contrib[(left, right)])
            edge_count += 1
    return matrix, edge_count


def orientation_kernel(edge_matrix: Matrix, e_in: int, p_source: Matrix) -> tuple[Matrix | None, float]:
    c_matrix = matadd(edge_matrix, matscale(identity(9), -((5.0 * float(e_in)) / 288.0)))
    restricted = matmul(matmul(p_source, c_matrix), p_source)
    b_matrix = matadd(restricted, matscale(p_source, -(trace(restricted) / 6.0)))
    b_square = matmul(b_matrix, b_matrix)
    denom = trace(b_square)
    if denom <= TOL:
        return None, denom
    return matscale(b_square, 1.0 / denom), denom


def panel_paths() -> tuple[Path, Path]:
    root = Path(__file__).resolve().parents[1] / "synced"
    return root / "codon_e1_heldout_panel.json", root / "codon_e1_transport_panel.json"


def load_domain_entries(sense_codons: list[str]) -> tuple[dict[str, list[dict[str, Any]]], list[dict[str, object]]]:
    heldout_path, transport_path = panel_paths()
    with heldout_path.open("r", encoding="utf-8") as handle:
        heldout = json.load(handle)
    with transport_path.open("r", encoding="utf-8") as handle:
        transport = json.load(handle)

    checks = [
        check_row("heldout_panel_codon_order", heldout.get("sense_codon_order_rna") == sense_codons),
        check_row("transport_panel_codon_order", transport.get("sense_codon_order_rna") == sense_codons),
    ]

    by_domain: dict[str, list[dict[str, Any]]] = {"bacteria": [], "archaea": [], "eukaryota": []}
    for entry in heldout.get("organisms", []):
        if not isinstance(entry, dict):
            continue
        by_domain["bacteria"].append(
            {
                "domain": "bacteria",
                "name": entry.get("organism_slug"),
                "genus": entry.get("genus"),
                "codon_counts_rna": entry.get("codon_counts_rna"),
                "total_sense": entry.get("total_sense_codons"),
            }
        )
    for entry in transport.get("organisms", []):
        if not isinstance(entry, dict):
            continue
        domain = entry.get("domain")
        if domain not in {"archaea", "eukaryota"}:
            continue
        organism = str(entry.get("organism", ""))
        by_domain[str(domain)].append(
            {
                "domain": domain,
                "name": organism,
                "genus": entry.get("genus") or organism.split()[0].lower(),
                "codon_counts_rna": entry.get("codon_counts_rna"),
                "total_sense": entry.get("total_sense"),
            }
        )

    for domain, entries in by_domain.items():
        counts_ok = all(
            isinstance(entry.get("codon_counts_rna"), dict)
            and set(entry["codon_counts_rna"]) == set(sense_codons)
            and int(entry.get("total_sense") or 0) > 0
            and sum(int(entry["codon_counts_rna"][codon]) for codon in sense_codons)
            == int(entry.get("total_sense") or 0)
            for entry in entries
        )
        checks.append(check_row(f"{domain}_panel_entries", bool(entries) and counts_ok, n=len(entries)))
    return by_domain, checks


def organism_source_matrices(
    entries: list[dict[str, Any]],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
    l_pinv: Matrix,
) -> tuple[dict[str, list[Matrix]], list[dict[str, object]]]:
    checks: list[dict[str, object]] = []
    by_genus: dict[str, list[Matrix]] = defaultdict(list)
    max_family_mean = 0.0
    zero_sources: list[str] = []
    for entry in entries:
        counts = entry["codon_counts_rna"]
        total = int(entry["total_sense"])
        raw = [float(counts[codon]) / total for codon in sense_codons]
        residual = e1_base.project_syn(raw, families, sense_index)
        max_family_mean = max(max_family_mean, e1_base.max_abs_family_mean(residual, families, sense_index))
        source = matvec(l_pinv, residual)
        norm_sq = dot(source, source)
        if norm_sq <= TOL:
            zero_sources.append(str(entry.get("name")))
            continue
        by_genus[str(entry["genus"])].append(matscale(outer(source, source), 1.0 / norm_sq))
    checks.append(
        check_row(
            "d_resid4_synonymous_mean_zero",
            max_family_mean <= 1.0e-12,
            max_abs_family_mean=round_float(max_family_mean, 14),
        )
    )
    checks.append(check_row("nonzero_source_coordinates", not zero_sources, zero_source_entries=zero_sources))
    return dict(by_genus), checks


def sigma_from_genus_matrices(genus_matrices: dict[str, list[Matrix]]) -> Matrix:
    if not genus_matrices:
        raise ValueError("empty genus matrix table")
    sigma = zeros(9, 9)
    for genus in sorted(genus_matrices):
        sigma = matadd(sigma, matscale(matrix_sum(genus_matrices[genus]), 1.0 / len(genus_matrices[genus])))
    sigma = matscale(sigma, 1.0 / len(genus_matrices))
    return sigma


def bootstrap_lower95_excess(
    domain: str,
    genus_matrices: dict[str, list[Matrix]],
    observed_kernel: Matrix,
    null_mean: float,
) -> float:
    rng = random.Random(stable_seed(f"{BOOTSTRAP_SEED_PREFIX}.{domain}"))
    genera = sorted(genus_matrices)
    genus_sigmas = {
        genus: matscale(matrix_sum(matrices), 1.0 / len(matrices))
        for genus, matrices in genus_matrices.items()
    }
    values: list[float] = []
    for _ in range(N_BOOTSTRAP):
        sigma = zeros(9, 9)
        for _slot in genera:
            sigma = matadd(sigma, genus_sigmas[rng.choice(genera)])
        sigma = matscale(sigma, 1.0 / len(genera))
        values.append(trace(matmul(sigma, observed_kernel)) - null_mean)
    return percentile(values, 0.025)


def summarize_null(values: list[float], observed: float) -> dict[str, object]:
    center = mean(values)
    sd = sample_std(values, center)
    ordered = sorted(values)
    return {
        "mean": round_float(center),
        "std": round_float(sd),
        "min": round_float(ordered[0]),
        "median": round_float(ordered[len(ordered) // 2]),
        "max": round_float(ordered[-1]),
        "ge_observed": sum(value >= observed - 1.0e-12 for value in values),
        "le_observed": sum(value <= observed + 1.0e-12 for value in values),
    }


def main() -> None:
    checks: list[dict[str, object]] = []
    try:
        full_codons = e1_base.codon_order()
        sense_codons = e1_base.sense_codon_order()
        sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
        families = e1_base.families_by_aa(sense_codons)

        u1 = transpose(e1_base.e1_character_basis(full_codons))
        p1_check = projector_checks(u1, full_codons)
        p1_fields = {key: value for key, value in p1_check.items() if key != "ok"}
        checks.append(check_row("E1_projector_formula", bool(p1_check["ok"]), **p1_fields))

        l_matrix = build_l_matrix(full_codons, sense_codons)
        l_t = transpose(l_matrix)
        gram = matmul(l_t, l_matrix)
        gram_pinv, l_rank, gram_eigenvalues = symmetric_pseudoinverse(gram)
        l_pinv = matmul(gram_pinv, l_t)
        p_source = matmul(l_pinv, l_matrix)
        p_idempotent = max_abs_matrix_diff(matmul(p_source, p_source), p_source)
        p_symmetric = max_abs_matrix_diff(p_source, transpose(p_source))
        checks.extend(
            [
                check_row(
                    "L_rank",
                    l_rank == 6,
                    rank=l_rank,
                    expected=6,
                    gram_eigenvalues=[round_float(value, 14) for value in sorted(gram_eigenvalues, reverse=True)],
                ),
                check_row(
                    "source_projector_orthogonal",
                    p_idempotent <= 1.0e-9 and p_symmetric <= 1.0e-9,
                    idempotent_max_abs=round_float(p_idempotent, 14),
                    symmetric_max_abs=round_float(p_symmetric, 14),
                ),
            ]
        )

        domain_entries, panel_checks = load_domain_entries(sense_codons)
        checks.extend(panel_checks)

        omega_data = build_omega_states()
        if omega_data["codons"] != full_codons:
            checks.append(check_row("codon_order_consistent", False))
        else:
            checks.append(check_row("codon_order_consistent", True))
        states: list[tuple[tuple[int, ...], ...]] = omega_data["states"]
        observed_state = omega_data["observed_state"]
        descriptor_cache = omega_data["descriptor_cache"]
        stop_descriptor = omega_data["stop_descriptor"]
        atoms = omega_data["atoms"]

        checks.extend(
            [
                check_row(
                    "component_conditioned_exact_omega",
                    len(states) > 0,
                    omega_size=len(states),
                    base_omega_size=len(omega_data["base_states"]),
                ),
                check_row(
                    "observed_state_in_omega",
                    int(omega_data["observed_state_index"]) >= 0,
                    observed_state_index=omega_data["observed_state_index"],
                ),
                check_row(
                    "stop_fiber_descriptor_unique",
                    omega_data["stop_candidates_by_state"] == {1: len(states)},
                    matches_per_state=omega_data["stop_candidates_by_state"],
                ),
            ]
        )

        if not all(row["ok"] for row in checks):
            emit(
                "needs_derivation",
                checks=checks,
                domains={},
                omega_size=len(states) if "states" in locals() else None,
                reason="A required construction check failed before the statistic was evaluated.",
            )

        edge_contrib: dict[tuple[int, int], Matrix] = {}
        for left, right in h34_edges(full_codons):
            left_row = u1[left]
            right_row = u1[right]
            edge_contrib[(left, right)] = matadd(outer(left_row, right_row), outer(right_row, left_row))

        all_groups = sorted({group for state in states for group in state})
        group_cache = {
            group: group_edge_data(group, atoms, list(edge_contrib), edge_contrib)
            for group in all_groups
        }

        def state_edge_matrix(state: tuple[tuple[int, ...], ...]) -> tuple[Matrix, int]:
            matrix = zeros(9, 9)
            edge_count = 0
            for group in state:
                if descriptor_cache[group] == stop_descriptor:
                    continue
                group_matrix, group_edges = group_cache[group]
                matrix = matadd(matrix, group_matrix)
                edge_count += group_edges
            return matrix, edge_count

        observed_edge_matrix, observed_e_in = state_edge_matrix(observed_state)
        trace_identity_lhs = trace(observed_edge_matrix)
        trace_identity_rhs = (5.0 / 32.0) * float(observed_e_in)
        identity_error = abs(trace_identity_lhs - trace_identity_rhs)
        checks.append(
            check_row(
                "standard_code_E1_trace_identity",
                identity_error <= 1.0e-10,
                e_in=observed_e_in,
                lhs=round_float(trace_identity_lhs, 14),
                rhs=round_float(trace_identity_rhs, 14),
                abs_error=round_float(identity_error, 14),
            )
        )
        observed_kernel, observed_denominator = orientation_kernel(observed_edge_matrix, observed_e_in, p_source)
        checks.append(
            check_row(
                "standard_code_B_nonzero",
                observed_kernel is not None,
                tr_B2=round_float(observed_denominator, 14),
            )
        )
        if observed_kernel is None or not checks[-2]["ok"]:
            emit(
                "needs_derivation",
                checks=checks,
                domains={},
                omega_size=len(states),
                reason="The algebraic identity check failed or the standard orientation operator is zero.",
            )

        sigma_by_domain: dict[str, Matrix] = {}
        genus_matrices_by_domain: dict[str, dict[str, list[Matrix]]] = {}
        domain_setup: dict[str, dict[str, object]] = {}
        for domain in ("bacteria", "archaea", "eukaryota"):
            genus_matrices, domain_checks = organism_source_matrices(
                domain_entries[domain], sense_codons, families, sense_index, l_pinv
            )
            checks.extend(
                {**row, "name": f"{domain}_{row['name']}"}
                for row in domain_checks
            )
            genus_matrices_by_domain[domain] = genus_matrices
            sigma_by_domain[domain] = sigma_from_genus_matrices(genus_matrices)
            domain_setup[domain] = {
                "n_organisms": len(domain_entries[domain]),
                "n_genera": len(genus_matrices),
                "cluster_sizes": {genus: len(genus_matrices[genus]) for genus in sorted(genus_matrices)},
            }

        if not all(row["ok"] for row in checks):
            emit(
                "needs_derivation",
                checks=checks,
                domains=domain_setup,
                omega_size=len(states),
                reason="A biological panel check failed before null evaluation.",
            )

        null_values = {domain: [] for domain in ("bacteria", "archaea", "eukaryota")}
        observed_values = {
            domain: trace(matmul(sigma_by_domain[domain], observed_kernel))
            for domain in ("bacteria", "archaea", "eukaryota")
        }
        degenerate_states = 0
        for state in states:
            edge_matrix, edge_count = state_edge_matrix(state)
            kernel, _denominator = orientation_kernel(edge_matrix, edge_count, p_source)
            if kernel is None:
                degenerate_states += 1
                continue
            for domain in ("bacteria", "archaea", "eukaryota"):
                null_values[domain].append(trace(matmul(sigma_by_domain[domain], kernel)))

        checks.append(
            check_row(
                "null_non_degenerate",
                degenerate_states == 0 and all(len(values) >= 5000 for values in null_values.values()),
                degenerate_states=degenerate_states,
                nondegenerate_draws={domain: len(values) for domain, values in null_values.items()},
            )
        )
        if not checks[-1]["ok"]:
            emit(
                "needs_derivation",
                checks=checks,
                domains=domain_setup,
                omega_size=len(states),
                reason="The conditioned null did not provide enough non-degenerate orientation operators.",
            )

        domain_results: dict[str, dict[str, object]] = {}
        significantly_opposite = False
        all_exceptional_positive = True
        any_positive_excess = False
        for domain in ("bacteria", "archaea", "eukaryota"):
            values = null_values[domain]
            observed = observed_values[domain]
            null_mean = mean(values)
            null_std = sample_std(values, null_mean)
            upper_p = sum(value >= observed - 1.0e-12 for value in values) / len(values)
            lower_p = sum(value <= observed + 1.0e-12 for value in values) / len(values)
            lo95 = bootstrap_lower95_excess(domain, genus_matrices_by_domain[domain], observed_kernel, null_mean)
            excess = observed - null_mean
            exceptional_positive = upper_p <= ALPHA and lo95 > 0.0 and excess > 0.0
            opposite = lower_p <= ALPHA and excess < 0.0
            significantly_opposite = significantly_opposite or opposite
            all_exceptional_positive = all_exceptional_positive and exceptional_positive
            any_positive_excess = any_positive_excess or excess > 0.0
            domain_results[domain] = {
                **domain_setup[domain],
                "T_same": round_float(observed),
                "null_mean": round_float(null_mean),
                "null_std": round_float(null_std),
                "one_sided_p": round_float(upper_p),
                "lower_tail_p": round_float(lower_p),
                "bootstrap_lower95_excess": round_float(lo95),
                "excess": round_float(excess),
                "verdict": (
                    "exceptional_positive"
                    if exceptional_positive
                    else ("significantly_opposite" if opposite else "not_exceptional")
                ),
                "null_summary": summarize_null(values, observed),
            }

        if all_exceptional_positive and not significantly_opposite:
            status = "certified"
            reason = (
                "All three domains have upper-tail orientation alignment at p<=0.01 with positive "
                "cluster-bootstrap lower-95% excess under the trace-deflated exact null."
            )
        elif significantly_opposite or not all_exceptional_positive:
            status = "refuted"
            reason = (
                "At least one domain is not an exceptional positive upper-tail alignment after "
                "deflating the algebraically forced E1 trace and conditioning on the exact null."
            )
        elif any_positive_excess:
            status = "coincidence"
            reason = "The observed positive excess is typical under the conditioned null."
        else:
            status = "refuted"
            reason = "The orientation-alignment statistic does not support a same-signal interpretation."

        emit(
            status,
            T_same_by_domain=domain_results,
            omega_size=len(states),
            null_method="exact_enumeration",
            null_draws=len(states),
            conditions_out=[
                "box",
                "wobble",
                "edge_margins",
                "boundary_degrees",
                "component_structure",
                "composition_by_atom_size",
            ],
            standard_code={
                "e_in": observed_e_in,
                "tr_B2": round_float(observed_denominator, 14),
                "trace_identity_lhs": round_float(trace_identity_lhs, 14),
                "trace_identity_rhs": round_float(trace_identity_rhs, 14),
            },
            checks=checks,
            threshold={"upper_tail_alpha": ALPHA, "bootstrap_lower95_excess": ">0 in each domain"},
            reason=reason,
        )
    except Exception as exc:
        checks.append(check_row("exception_free", False, exception=type(exc).__name__, message=str(exc)))
        emit(
            "needs_derivation",
            checks=checks,
            domains={},
            omega_size=None,
            reason="An exception prevented evaluation of the statistic.",
        )


if __name__ == "__main__":
    main()

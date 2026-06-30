#!/usr/bin/env python3
"""Cross-box square-motif residual extremality for the standard code.

The null is the label-free regrouping space of the 25 fixed box/wobble atoms,
conditioned on the standard global assembly signatures and on the per-fiber
cross-atom synonymous-edge profile by box/wobble-preserving edge orbit.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, product
import json
import math
import sys


EXPERIMENT_ID = "square_motif_residual_extremality"
CLAIM_ID = "bridge.genetic_code.square_motif_residual.extremality"
NULL_SEED = None
NULL_DRAWS = None
EXTREME_ALPHA = 0.01
ZERO_TOL = 1e-10

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": "00", "C": "01", "A": "10", "G": "11"}
BOX_AXES = frozenset(range(4))
WOBBLE_AXES = frozenset(range(4, 6))
EDGE_ORBITS = ("box_axis", "wobble_axis")
FACE_ORBITS = ("box_box", "box_wobble", "wobble_wobble")
MOTIF_TYPES = (
    "4",
    "3+1",
    "2+2_adj",
    "2+2_alt",
    "2+1+1_adj",
    "2+1+1_opp",
    "1+1+1+1",
)
SYN_BOUNDARY_EDGES_BY_MOTIF = {
    "4": 4,
    "3+1": 2,
    "2+2_adj": 2,
    "2+2_alt": 0,
    "2+1+1_adj": 1,
    "2+1+1_opp": 0,
    "1+1+1+1": 0,
}

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
    sys.exit(0 if status in ("certified", "coincidence", "refuted") else 3)


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def codon_bits(codon: str) -> str:
    return "".join(BASE_TO_BITS[base] for base in codon)


def family_order(codons: list[str]) -> list[str]:
    counts = Counter(CODON_TO_FAMILY[codon] for codon in codons)
    return sorted(counts, key=lambda family: (-counts[family], family))


def standard_labels(codons: list[str], families: list[str]) -> list[int]:
    by_family = {family: index for index, family in enumerate(families)}
    return [by_family[CODON_TO_FAMILY[codon]] for codon in codons]


def edge_orbit(axis: int) -> int:
    return 0 if axis in BOX_AXES else 1


def face_orbit(axis_a: int, axis_b: int) -> int:
    in_box_a = axis_a in BOX_AXES
    in_box_b = axis_b in BOX_AXES
    if in_box_a and in_box_b:
        return 0
    if in_box_a or in_box_b:
        return 1
    return 2


def q6_edges(codons: list[str]) -> list[tuple[int, int, int]]:
    bitwords = [codon_bits(codon) for codon in codons]
    by_bits = {word: index for index, word in enumerate(bitwords)}
    edges: list[tuple[int, int, int]] = []
    for index, word in enumerate(bitwords):
        for axis in range(6):
            flipped = word[:axis] + ("1" if word[axis] == "0" else "0") + word[axis + 1:]
            other = by_bits[flipped]
            if index < other:
                edges.append((index, other, edge_orbit(axis)))
    return edges


def box_wobble_atoms(codons: list[str], labels: list[int]) -> list[tuple[int, ...]]:
    atoms: dict[tuple[str, int], list[int]] = {}
    for index, codon in enumerate(codons):
        atoms.setdefault((codon[:2], labels[index]), []).append(index)
    return [
        tuple(indices)
        for _, indices in sorted(atoms.items(), key=lambda item: (item[0][0], min(item[1])))
    ]


def atom_pair_edge_profiles(
    atoms: list[tuple[int, ...]],
    vertex_to_atom: list[int],
    edges: list[tuple[int, int, int]],
) -> dict[tuple[int, int], tuple[int, int]]:
    profiles = {(left, right): [0, 0] for left in range(len(atoms)) for right in range(left + 1, len(atoms))}
    for vertex_a, vertex_b, orbit in edges:
        atom_a = vertex_to_atom[vertex_a]
        atom_b = vertex_to_atom[vertex_b]
        if atom_a == atom_b:
            continue
        key = (atom_a, atom_b) if atom_a < atom_b else (atom_b, atom_a)
        profiles[key][orbit] += 1
    return {key: tuple(value) for key, value in profiles.items()}


def group_descriptor(group: tuple[int, ...], atom_sizes: list[int], pair_profiles: dict[tuple[int, int], tuple[int, int]]) -> tuple[tuple[int, ...], tuple[int, int]]:
    sizes = tuple(sorted((atom_sizes[atom] for atom in group), reverse=True))
    if len(group) == 1:
        return sizes, (0, 0)
    if len(group) == 2:
        return sizes, pair_profiles[tuple(sorted(group))]
    raise ValueError("the standard assembly signature contains no group with more than two atoms")


def state_signature(
    groups: tuple[tuple[int, ...], ...],
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[tuple[int, ...], tuple[int, int]], ...]:
    return tuple(sorted(group_descriptor(group, atom_sizes, pair_profiles) for group in groups))


def observed_atom_groups(labels: list[int], vertex_to_atom: list[int], atom_count: int) -> tuple[tuple[int, ...], ...]:
    by_label: dict[int, set[int]] = defaultdict(set)
    for vertex, label in enumerate(labels):
        by_label[label].add(vertex_to_atom[vertex])
    groups = tuple(sorted(tuple(sorted(atoms)) for atoms in by_label.values()))
    if sorted(atom for group in groups for atom in group) != list(range(atom_count)):
        raise RuntimeError("observed atom groups do not cover the atom set")
    return groups


def enumerate_conditioned_states(
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
    observed_signature: tuple[tuple[tuple[int, ...], tuple[int, int]], ...],
) -> list[tuple[tuple[int, ...], ...]]:
    by_size: dict[int, list[int]] = defaultdict(list)
    for atom, size in enumerate(atom_sizes):
        by_size[size].append(atom)

    quartets = by_size[4]
    triplets = by_size[3]
    doublets = by_size[2]
    singlets = by_size[1]
    if len(triplets) != 1:
        raise RuntimeError("unexpected standard atom size signature")

    required_pair_descriptors = Counter(
        descriptor for descriptor in observed_signature if len(descriptor[0]) == 2
    )
    states: set[tuple[tuple[int, ...], ...]] = set()

    quartet_doublet_pairs = [
        (quartet, doublet, group_descriptor((quartet, doublet), atom_sizes, pair_profiles))
        for quartet in quartets
        for doublet in doublets
    ]
    doublet_singlet_pairs = [
        (doublet, singlet, group_descriptor((doublet, singlet), atom_sizes, pair_profiles))
        for doublet in doublets
        for singlet in singlets
    ]

    def choose_quartet_doublet_pairs(
        start: int,
        chosen: list[tuple[int, int]],
        used_quartets: set[int],
        used_doublets: set[int],
        remaining: Counter[tuple[tuple[int, ...], tuple[int, int]]],
    ) -> None:
        if len(chosen) == 3:
            for doublet, singlet, descriptor in doublet_singlet_pairs:
                if doublet in used_doublets:
                    continue
                if remaining[descriptor] <= 0:
                    continue
                next_remaining = remaining.copy()
                next_remaining[descriptor] -= 1
                if any(value != 0 for value in next_remaining.values()):
                    continue
                multi_groups = [tuple(sorted(pair)) for pair in chosen]
                multi_groups.append(tuple(sorted((doublet, singlet))))
                used_atoms = {atom for group in multi_groups for atom in group}
                singletons = [(atom,) for atom in range(len(atom_sizes)) if atom not in used_atoms]
                groups = tuple(sorted(multi_groups + singletons))
                if state_signature(groups, atom_sizes, pair_profiles) == observed_signature:
                    states.add(groups)
            return

        for index in range(start, len(quartet_doublet_pairs)):
            quartet, doublet, descriptor = quartet_doublet_pairs[index]
            if quartet in used_quartets or doublet in used_doublets:
                continue
            if remaining[descriptor] <= 0:
                continue
            next_remaining = remaining.copy()
            next_remaining[descriptor] -= 1
            choose_quartet_doublet_pairs(
                index + 1,
                chosen + [(quartet, doublet)],
                used_quartets | {quartet},
                used_doublets | {doublet},
                next_remaining,
            )

    choose_quartet_doublet_pairs(0, [], set(), set(), required_pair_descriptors.copy())
    return sorted(states)


def q6_square_faces(
    codons: list[str],
    vertex_to_atom: list[int],
) -> list[tuple[int, tuple[int, int, int, int], tuple[int, int, int, int]]]:
    bitwords = [codon_bits(codon) for codon in codons]
    by_bits = {word: index for index, word in enumerate(bitwords)}
    faces: list[tuple[int, tuple[int, int, int, int], tuple[int, int, int, int]]] = []
    for axis_a, axis_b in combinations(range(6), 2):
        free_axes = {axis_a, axis_b}
        fixed_axes = [axis for axis in range(6) if axis not in free_axes]
        for fixed_values in product("01", repeat=4):
            bits = ["0"] * 6
            for axis, value in zip(fixed_axes, fixed_values):
                bits[axis] = value
            base = "".join(bits)
            word_a = base[:axis_a] + "1" + base[axis_a + 1:]
            word_ab = word_a[:axis_b] + "1" + word_a[axis_b + 1:]
            word_b = base[:axis_b] + "1" + base[axis_b + 1:]
            vertices = (by_bits[base], by_bits[word_a], by_bits[word_ab], by_bits[word_b])
            atom_tuple = tuple(vertex_to_atom[vertex] for vertex in vertices)
            if len(set(atom_tuple)) == 1:
                continue
            faces.append((face_orbit(axis_a, axis_b), vertices, atom_tuple))
    return faces


def motif_type(labels: tuple[int, int, int, int]) -> str:
    positions_by_label: dict[int, list[int]] = defaultdict(list)
    for position, label in enumerate(labels):
        positions_by_label[label].append(position)
    sizes = sorted((len(positions) for positions in positions_by_label.values()), reverse=True)
    if sizes == [4]:
        return "4"
    if sizes == [3, 1]:
        return "3+1"
    if sizes == [2, 2]:
        positions = next(iter(positions_by_label.values()))
        return "2+2_alt" if abs(positions[0] - positions[1]) == 2 else "2+2_adj"
    if sizes == [2, 1, 1]:
        pair_positions = next(positions for positions in positions_by_label.values() if len(positions) == 2)
        return "2+1+1_opp" if abs(pair_positions[0] - pair_positions[1]) == 2 else "2+1+1_adj"
    return "1+1+1+1"


def atom_labels_for_state(groups: tuple[tuple[int, ...], ...], atom_count: int) -> list[int]:
    atom_labels = [-1] * atom_count
    for block, group in enumerate(groups):
        for atom in group:
            atom_labels[atom] = block
    if any(label < 0 for label in atom_labels):
        raise RuntimeError("state leaves an atom unlabeled")
    return atom_labels


def motif_vector(
    atom_labels: list[int],
    faces: list[tuple[int, tuple[int, int, int, int], tuple[int, int, int, int]]],
) -> tuple[int, ...]:
    counts = [0] * (len(FACE_ORBITS) * len(MOTIF_TYPES))
    for orbit, _vertices, atom_tuple in faces:
        labels = tuple(atom_labels[atom] for atom in atom_tuple)
        motif = motif_type(labels)
        counts[orbit * len(MOTIF_TYPES) + MOTIF_TYPES.index(motif)] += 1
    return tuple(counts)


def diagonal_recovery_count(vector: tuple[int, ...]) -> int:
    total = 0
    for orbit in range(len(FACE_ORBITS)):
        base = orbit * len(MOTIF_TYPES)
        total += vector[base + MOTIF_TYPES.index("2+2_alt")]
        total += vector[base + MOTIF_TYPES.index("2+1+1_opp")]
    return total


def matrix_rows_for_edge_margins() -> list[list[float]]:
    rows: list[list[float]] = []
    dimension = len(FACE_ORBITS) * len(MOTIF_TYPES)
    for orbit in range(len(FACE_ORBITS)):
        row = [0.0] * dimension
        for motif_index, motif in enumerate(MOTIF_TYPES):
            row[orbit * len(MOTIF_TYPES) + motif_index] = float(SYN_BOUNDARY_EDGES_BY_MOTIF[motif])
        rows.append(row)
    return rows


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def orthonormal_basis(rows: list[list[float]], tol: float = 1e-12) -> list[list[float]]:
    basis: list[list[float]] = []
    for row in rows:
        vector = [float(value) for value in row]
        for existing in basis:
            scale = dot(vector, existing)
            vector = [value - scale * base for value, base in zip(vector, existing)]
        norm = math.sqrt(dot(vector, vector))
        if norm > tol:
            basis.append([value / norm for value in vector])
    return basis


def residualize(vector: tuple[int, ...], row_basis: list[list[float]]) -> list[float]:
    residual = [float(value) for value in vector]
    for basis_vector in row_basis:
        scale = dot(residual, basis_vector)
        residual = [value - scale * base for value, base in zip(residual, basis_vector)]
    return residual


def rank_pivots(matrix: list[list[float]], tol: float = 1e-9) -> tuple[int, list[int]]:
    work = [row[:] for row in matrix]
    rows = len(work)
    cols = len(work[0]) if rows else 0
    pivot_columns: list[int] = []
    row = 0
    for col in range(cols):
        pivot = max(range(row, rows), key=lambda candidate: abs(work[candidate][col]), default=row)
        if row >= rows or abs(work[pivot][col]) <= tol:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        scale = work[row][col]
        work[row] = [value / scale for value in work[row]]
        for other in range(rows):
            if other == row:
                continue
            factor = work[other][col]
            if abs(factor) > tol:
                work[other] = [value - factor * base for value, base in zip(work[other], work[row])]
        pivot_columns.append(col)
        row += 1
        if row == rows:
            break
    return len(pivot_columns), pivot_columns


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    return [list(column) for column in zip(*matrix)]


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [dot(row, vector) for row in matrix]


def mat_mul(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    right_t = transpose(right)
    return [[dot(row, column) for column in right_t] for row in left]


def solve_linear(matrix: list[list[float]], rhs: list[float], tol: float = 1e-10) -> list[float]:
    size = len(matrix)
    work = [matrix[row][:] + [rhs[row]] for row in range(size)]
    for col in range(size):
        pivot = max(range(col, size), key=lambda row: abs(work[row][col]))
        if abs(work[pivot][col]) <= tol:
            raise ArithmeticError("singular restricted covariance")
        work[col], work[pivot] = work[pivot], work[col]
        scale = work[col][col]
        work[col] = [value / scale for value in work[col]]
        for row in range(size):
            if row == col:
                continue
            factor = work[row][col]
            if abs(factor) > tol:
                work[row] = [value - factor * base for value, base in zip(work[row], work[col])]
    return [work[row][-1] for row in range(size)]


def covariance_matrix(values: list[list[float]], mean: list[float]) -> list[list[float]]:
    count = len(values)
    dimension = len(mean)
    covariance = [[0.0 for _ in range(dimension)] for _ in range(dimension)]
    if count <= 1:
        return covariance
    for vector in values:
        centered = [value - center for value, center in zip(vector, mean)]
        for row in range(dimension):
            left = centered[row]
            if abs(left) <= ZERO_TOL:
                continue
            for col in range(row, dimension):
                covariance[row][col] += left * centered[col]
    scale = 1.0 / (count - 1)
    for row in range(dimension):
        for col in range(row, dimension):
            covariance[row][col] *= scale
            covariance[col][row] = covariance[row][col]
    return covariance


def jacobi_eigen_symmetric(
    matrix: list[list[float]],
    tol: float = 1e-11,
    max_sweeps: int = 200,
) -> tuple[list[float], list[list[float]]]:
    size = len(matrix)
    work = [row[:] for row in matrix]
    vectors = [[1.0 if row == col else 0.0 for col in range(size)] for row in range(size)]

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

    values = [work[index][index] for index in range(size)]
    return values, vectors


def mahalanobis_factory(covariance: list[list[float]]) -> tuple[int, list[tuple[float, list[float]]]]:
    eigenvalues, eigenvectors_by_row = jacobi_eigen_symmetric(covariance)
    max_eigenvalue = max((abs(value) for value in eigenvalues), default=0.0)
    cutoff = max(1e-9, max_eigenvalue * 1e-10)
    directions: list[tuple[float, list[float]]] = []
    for column, eigenvalue in enumerate(eigenvalues):
        if eigenvalue <= cutoff:
            continue
        direction = [eigenvectors_by_row[row][column] for row in range(len(eigenvectors_by_row))]
        directions.append((eigenvalue, direction))
    return len(directions), directions


def mahalanobis_squared(
    vector: list[float],
    mean: list[float],
    rank: int,
    directions: list[tuple[float, list[float]]],
) -> float:
    if rank == 0:
        return 0.0
    centered = [value - center for value, center in zip(vector, mean)]
    value = 0.0
    for eigenvalue, direction in directions:
        coordinate = dot(centered, direction)
        value += coordinate * coordinate / eigenvalue
    return 0.0 if abs(value) <= 1e-9 else value


def summarize_residual_variance(covariance: list[list[float]]) -> dict[str, object]:
    diagonal = [max(0.0, covariance[index][index]) for index in range(len(covariance))]
    nonzero = [value for value in diagonal if value > ZERO_TOL]
    return {
        "trace": round(sum(diagonal), 12),
        "nonzero_coordinate_count": len(nonzero),
        "max_coordinate_variance": round(max(nonzero), 12) if nonzero else 0.0,
    }


def round_float(value: float | None) -> float | None:
    if value is None:
        return None
    return float(f"{value:.12g}")


def motif_orbit_table(vector: tuple[int, ...]) -> dict[str, dict[str, int]]:
    table: dict[str, dict[str, int]] = {}
    for orbit, orbit_name in enumerate(FACE_ORBITS):
        base = orbit * len(MOTIF_TYPES)
        table[orbit_name] = {
            motif: vector[base + motif_index]
            for motif_index, motif in enumerate(MOTIF_TYPES)
        }
    return table


def main() -> None:
    codons = codon_order()
    families = family_order(codons)
    labels = standard_labels(codons, families)
    edges = q6_edges(codons)
    atoms = box_wobble_atoms(codons, labels)
    atom_sizes = [len(atom) for atom in atoms]
    vertex_to_atom = [-1] * len(codons)
    for atom_index, atom in enumerate(atoms):
        for vertex in atom:
            vertex_to_atom[vertex] = atom_index
    pair_profiles = atom_pair_edge_profiles(atoms, vertex_to_atom, edges)
    observed_groups = observed_atom_groups(labels, vertex_to_atom, len(atoms))
    observed_signature = state_signature(observed_groups, atom_sizes, pair_profiles)
    states = enumerate_conditioned_states(atom_sizes, pair_profiles, observed_signature)
    observed_group_key = tuple(sorted(tuple(sorted(group)) for group in observed_groups))
    observed_state_index = states.index(observed_group_key) if observed_group_key in states else -1

    faces = q6_square_faces(codons, vertex_to_atom)
    face_orbit_counts = Counter(FACE_ORBITS[orbit] for orbit, _vertices, _atom_tuple in faces)
    row_basis = orthonormal_basis(matrix_rows_for_edge_margins())

    motif_vectors: list[tuple[int, ...]] = []
    residual_vectors: list[list[float]] = []
    observed_vector: tuple[int, ...] | None = None
    for state in states:
        atom_labels = atom_labels_for_state(state, len(atoms))
        vector = motif_vector(atom_labels, faces)
        motif_vectors.append(vector)
        residual_vectors.append(residualize(vector, row_basis))
        if state == observed_group_key:
            observed_vector = vector

    if observed_vector is None:
        emit(
            "needs_derivation",
            omega_nontrivial=False,
            omega_size_or_bound=len(states),
            n_cross_box_squares=len(faces),
            motif_orbit_count=len(FACE_ORBITS),
            residual_dim=0,
            residual_variance={},
            T_obs=None,
            p_value=None,
            null_method="exact_enumeration",
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            diagonal_recovery_faces=None,
            conditions_out=["e_in", "box", "wobble", "edge_margins"],
            checks=[{"name": "observed_state_in_conditioned_null", "ok": False}],
            reason="The standard atom regrouping was not found in the conditioned null; the null construction is invalid.",
        )

    distinct_motif_vectors = len(set(motif_vectors))
    omega_nontrivial = len(states) > 1 and distinct_motif_vectors > 1
    observed_residual = residualize(observed_vector, row_basis)
    mean = [
        sum(vector[index] for vector in residual_vectors) / len(residual_vectors)
        for index in range(len(residual_vectors[0]))
    ]
    covariance = covariance_matrix(residual_vectors, mean)
    residual_rank, covariance_directions = mahalanobis_factory(covariance)
    residual_variance = summarize_residual_variance(covariance)
    t_obs = mahalanobis_squared(observed_residual, mean, residual_rank, covariance_directions)
    null_t_values = [
        mahalanobis_squared(vector, mean, residual_rank, covariance_directions)
        for vector in residual_vectors
    ]
    p_value = sum(1 for value in null_t_values if value + 1e-9 >= t_obs) / len(null_t_values)
    diagonal_faces = diagonal_recovery_count(observed_vector)

    checks = [
        {"name": "codon_count", "ok": len(codons) == 64, "observed": len(codons), "expected": 64},
        {"name": "q6_edge_count", "ok": len(edges) == 192, "observed": len(edges), "expected": 192},
        {"name": "family_count", "ok": len(families) == 21, "observed": len(families), "expected": 21},
        {
            "name": "atom_count",
            "ok": len(atoms) == 25,
            "observed": len(atoms),
            "expected": 25,
            "atom_size_multiset": sorted(atom_sizes, reverse=True),
        },
        {
            "name": "observed_state_in_conditioned_null",
            "ok": observed_state_index >= 0,
            "observed_state_index": observed_state_index,
        },
        {
            "name": "conditioned_null_exact_enumeration",
            "ok": len(states) > 0,
            "omega_size": len(states),
            "method": "direct enumeration of all label-free atom regroupings with standard assembly-signature and edge-profile descriptors",
        },
        {
            "name": "orbit_count_gate",
            "ok": omega_nontrivial,
            "distinct_square_motif_vectors": distinct_motif_vectors,
            "interpretation": "distinct label-free motif vectors certify at least two box/wobble-preserving automorphism orbits in the conditioned null",
        },
        {
            "name": "edge_margin_projection_rank",
            "ok": len(row_basis) == len(FACE_ORBITS),
            "rank": len(row_basis),
            "rows": len(FACE_ORBITS),
        },
        {
            "name": "residual_covariance_rank",
            "ok": residual_rank > 0,
            "rank": residual_rank,
        },
    ]

    if not all(check["ok"] for check in checks[:6]):
        status = "needs_derivation"
        reason = "A construction check failed before the residual statistic could be interpreted."
    elif len(states) == 1 or not omega_nontrivial:
        status = "coincidence"
        reason = (
            "conditioned null is a single orbit or has no detected label-free square-motif variation; "
            "all route-one functionals are forced on this conditioning"
        )
    elif residual_rank == 0 or residual_variance["trace"] <= ZERO_TOL:
        status = "coincidence"
        reason = (
            "P_square m_square has zero variance on the conditioned null; square structure is "
            "algebraically forced by box/wobble and edge margins"
        )
    elif p_value <= EXTREME_ALPHA:
        status = "certified"
        reason = (
            "The standard code is an extreme upper-tail outlier for the predeclared omnibus "
            f"square-motif residual statistic under exact Ω_BW,E enumeration (p={round_float(p_value)})."
        )
    else:
        status = "coincidence"
        reason = (
            "The conditioned null is non-trivial and the residual has nonzero variance, but the "
            f"standard code is not an extreme omnibus outlier (p={round_float(p_value)})."
        )

    emit(
        status,
        omega_nontrivial=omega_nontrivial,
        omega_size_or_bound=len(states),
        n_cross_box_squares=len(faces),
        motif_orbit_count=len(FACE_ORBITS),
        residual_dim=residual_rank,
        residual_variance=residual_variance,
        T_obs=round_float(t_obs),
        p_value=round_float(p_value),
        null_method="exact_enumeration",
        null_seed=NULL_SEED,
        null_draws=NULL_DRAWS,
        diagonal_recovery_faces=diagonal_faces,
        conditions_out=["e_in", "box", "wobble", "edge_margins"],
        checks=checks,
        reason=reason,
        threshold={"omnibus_upper_tail_alpha": EXTREME_ALPHA},
        automorphism_structure={
            "vertex_model": "Q6 with codon bases encoded as two bits each",
            "edge_orbits": list(EDGE_ORBITS),
            "face_orbits": list(FACE_ORBITS),
            "box_axes": sorted(BOX_AXES),
            "wobble_axes": sorted(WOBBLE_AXES),
        },
        observed_assembly_signature_counts={
            str(signature): count for signature, count in sorted(Counter(observed_signature).items())
        },
        observed_motif_census=motif_orbit_table(observed_vector),
        face_orbit_counts=dict(sorted(face_orbit_counts.items())),
        null_t_summary={
            "min": round_float(min(null_t_values)),
            "mean": round_float(sum(null_t_values) / len(null_t_values)),
            "max": round_float(max(null_t_values)),
            "ge_observed": sum(1 for value in null_t_values if value + 1e-9 >= t_obs),
        },
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Shared codon topology references for BioReality experiments."""
from __future__ import annotations

import json
from pathlib import Path


BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
BITS_TO_BASE = {bits: base for base, bits in BASE_TO_BITS.items()}
BASES = "UCAG"

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"


def codon_to_q6(codon: str) -> tuple[int, ...]:
    codon = codon.upper().replace("T", "U")
    if len(codon) != 3:
        raise ValueError(f"codon must have length 3: {codon!r}")
    bits = []
    for base in codon:
        if base not in BASE_TO_BITS:
            raise ValueError(f"invalid RNA base in codon {codon!r}")
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def q6_to_codon(bits: tuple[int, ...]) -> str:
    if len(bits) != 6:
        raise ValueError(f"Q6 coordinate must have length 6: {bits!r}")
    codon = []
    for offset in range(0, 6, 2):
        pair = (int(bits[offset]), int(bits[offset + 1]))
        if pair not in BITS_TO_BASE:
            raise ValueError(f"invalid bit pair {pair!r} in {bits!r}")
        codon.append(BITS_TO_BASE[pair])
    return "".join(codon)


def all_codons() -> list[str]:
    data = load_code_data()
    return list(data["codon_order"])


def wobble_partner(codon: str) -> str:
    bits = list(codon_to_q6(codon))
    bits[5] = 1 - bits[5]
    return q6_to_codon(tuple(bits))


def load_code_data() -> dict:
    return json.loads(DATA_PATH.read_text())


def validate_code_data(data: dict) -> None:
    codons = data.get("codon_order")
    tables = data.get("tables")
    if not isinstance(codons, list) or len(codons) != 64:
        raise ValueError("codon_order must contain 64 codons")
    if codons != [a + b + c for a in BASES for b in BASES for c in BASES]:
        raise ValueError("codon_order does not match NCBI UCAG order")
    if not isinstance(tables, list) or not tables:
        raise ValueError("tables must be a non-empty list")
    for table in tables:
        aa = table.get("aa")
        starts = table.get("starts")
        if len(aa) != 64 or len(starts) != 64:
            raise ValueError(f"table {table.get('table_id')} has non-64 rows")


def table_by_id(data: dict, table_id: int) -> dict:
    for table in data["tables"]:
        if table["table_id"] == table_id:
            return table
    raise ValueError(f"missing translation table {table_id}")


def translation_map(table: dict, codons: list[str]) -> dict[str, str]:
    aa = table["aa"]
    if len(aa) != len(codons):
        raise ValueError(f"table {table.get('table_id')} row length does not match codons")
    return {codon: aa[index] for index, codon in enumerate(codons)}


def reassignment_set(data: dict) -> set[str]:
    validate_code_data(data)
    codons = data["codon_order"]
    standard = translation_map(table_by_id(data, 1), codons)
    changed = set()
    for table in data["tables"]:
        if table["table_id"] == 1:
            continue
        mapping = translation_map(table, codons)
        for codon in codons:
            if mapping[codon] != standard[codon]:
                changed.add(codon)
    return changed


def expected_r_set() -> set[str]:
    return {"UGA", "UAG", "UAA", "AUA", "AGA", "AGG", "AAA", "CUG", "CUU", "CUC", "CUA", "UCA", "UUA"}


def motif_rhs() -> set[str]:
    rhs = set()
    rhs.update("CU" + z for z in BASES)
    rhs.update("AG" + z for z in "AG")
    rhs.update("U" + y + "A" for y in BASES)
    rhs.update(x + y + "A" for x in "UA" for y in "UA")
    rhs.update("UA" + z for z in "AG")
    return rhs


def punctured_cube_rhs() -> set[str]:
    rhs = {x + y + "A" for x in "UA" for y in BASES}
    rhs.discard("ACA")
    rhs.update("CU" + z for z in BASES)
    rhs.update({"UAG", "AGG"})
    return rhs


def wnr_union_cun() -> set[str]:
    rhs = {x + y + z for x in "UA" for y in BASES for z in "AG"}
    rhs.update("CU" + z for z in BASES)
    return rhs


def q5_projection(codon: str) -> tuple[int, ...]:
    bits = codon_to_q6(codon)
    return bits[:5]


def expected_projected_m() -> set[tuple[int, ...]]:
    codons = {x + y + z for x in "UA" for y in BASES for z in "AG"}
    codons.update("CU" + z for z in BASES)
    return {q5_projection(codon) for codon in codons}


def median_bits(x: tuple[int, ...], y: tuple[int, ...], z: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(1 if x[i] + y[i] + z[i] >= 2 else 0 for i in range(len(x)))


def median_closure(codons: set[str]) -> set[str]:
    points = {codon_to_q6(codon) for codon in codons}
    if not points:
        return set()
    unary = [{point[axis] for point in points} for axis in range(6)]
    binary = {}
    for left in range(6):
        for right in range(left + 1, 6):
            binary[(left, right)] = {(point[left], point[right]) for point in points}
    closure = set()
    for bits in bit_tuples(6):
        if any(bits[axis] not in unary[axis] for axis in range(6)):
            continue
        if any((bits[left], bits[right]) not in allowed for (left, right), allowed in binary.items()):
            continue
        closure.add(q6_to_codon(bits))
    return closure


def hamming(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return sum(1 for i, j in zip(a, b) if i != j)


def boundary(codons: set[str]) -> set[str]:
    inside = {codon_to_q6(codon) for codon in codons}
    all_bits = {codon_to_q6(codon) for codon in all_codons()}
    outside_boundary = set()
    for bits in inside:
        for i in range(6):
            neighbor = list(bits)
            neighbor[i] = 1 - neighbor[i]
            neighbor_tuple = tuple(neighbor)
            if neighbor_tuple in all_bits and neighbor_tuple not in inside:
                outside_boundary.add(neighbor_tuple)
    return {q6_to_codon(bits) for bits in outside_boundary}


def cubical_f_vector(codons: set[str], dimension: int = 6) -> list[int]:
    points = {codon_to_q6(codon) for codon in codons}
    counts = []
    for face_dim in range(dimension + 1):
        count = 0
        variable_masks = combinations(range(dimension), face_dim)
        for variable_axes in variable_masks:
            variable_set = set(variable_axes)
            fixed_axes = [axis for axis in range(dimension) if axis not in variable_set]
            for fixed_values in bit_tuples(len(fixed_axes)):
                face_points = set()
                for variable_values in bit_tuples(face_dim):
                    bits = [0] * dimension
                    fixed_index = 0
                    variable_index = 0
                    for axis in range(dimension):
                        if axis in variable_set:
                            bits[axis] = variable_values[variable_index]
                            variable_index += 1
                        else:
                            bits[axis] = fixed_values[fixed_index]
                            fixed_index += 1
                    face_points.add(tuple(bits))
                if face_points.issubset(points):
                    count += 1
        counts.append(count)
    return counts


def projected_f_vector(q5_points: set[tuple[int, ...]]) -> list[int]:
    return cubical_f_vector_bits(q5_points, 5)


def cubical_f_vector_bits(points: set[tuple[int, ...]], dimension: int) -> list[int]:
    counts = []
    for face_dim in range(dimension + 1):
        count = 0
        for variable_axes in combinations(range(dimension), face_dim):
            variable_set = set(variable_axes)
            fixed_axes = [axis for axis in range(dimension) if axis not in variable_set]
            for fixed_values in bit_tuples(len(fixed_axes)):
                face_points = set()
                for variable_values in bit_tuples(face_dim):
                    bits = [0] * dimension
                    fixed_index = 0
                    variable_index = 0
                    for axis in range(dimension):
                        if axis in variable_set:
                            bits[axis] = variable_values[variable_index]
                            variable_index += 1
                        else:
                            bits[axis] = fixed_values[fixed_index]
                            fixed_index += 1
                    face_points.add(tuple(bits))
                if face_points.issubset(points):
                    count += 1
        counts.append(count)
    return counts


def bit_tuples(length: int) -> list[tuple[int, ...]]:
    if length == 0:
        return [()]
    smaller = bit_tuples(length - 1)
    return [prefix + (bit,) for prefix in smaller for bit in (0, 1)]


def combinations(items, size: int):
    items = list(items)
    if size == 0:
        return [()]
    if size > len(items):
        return []
    result = []

    def rec(start: int, chosen: list[int]) -> None:
        if len(chosen) == size:
            result.append(tuple(chosen))
            return
        for index in range(start, len(items)):
            chosen.append(items[index])
            rec(index + 1, chosen)
            chosen.pop()

    rec(0, [])
    return result


def spectral_radius_killed_walk(codons: set[str], iterations: int = 5000, tolerance: float = 1e-14) -> float:
    points = sorted(codon_to_q6(codon) for codon in codons)
    n = len(points)
    vector = [1.0 / n for _ in range(n)]
    index = {point: i for i, point in enumerate(points)}
    neighbors = []
    for point in points:
        row = []
        for axis in range(6):
            neighbor = list(point)
            neighbor[axis] = 1 - neighbor[axis]
            neighbor_tuple = tuple(neighbor)
            if neighbor_tuple in index:
                row.append(index[neighbor_tuple])
        neighbors.append(row)
    previous = 0.0
    for _ in range(iterations):
        next_vector = [0.0] * n
        for row_index, row_neighbors in enumerate(neighbors):
            weight = vector[row_index] / 6.0
            for col_index in row_neighbors:
                next_vector[col_index] += weight
        norm = sum(value * value for value in next_vector) ** 0.5
        if norm == 0.0:
            return 0.0
        next_vector = [value / norm for value in next_vector]
        numerator = 0.0
        for row_index, row_neighbors in enumerate(neighbors):
            row_sum = sum(next_vector[col_index] for col_index in row_neighbors) / 6.0
            numerator += next_vector[row_index] * row_sum
        if abs(numerator - previous) < tolerance:
            return numerator
        previous = numerator
        vector = next_vector
    return previous


def median(values: list[int]) -> float:
    if not values:
        raise ValueError("median of empty list")
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return float(ordered[middle])
    return (ordered[middle - 1] + ordered[middle]) / 2.0

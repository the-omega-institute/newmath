#!/usr/bin/env python3
"""Semipartial H3 residual-specificity test for d_resid4."""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
import pathlib
import random
import sys


EXPERIMENT_ID = "h3_residual_specificity"
CLAIM_ID = "bridge.genetic_code.h3_residual_specificity"
DEFAULT_NULL_REPS = 50000
SELFTEST_NULL_REPS = 80
EPS = 1.0e-12
TOL = 1.0e-10
FROBENIUS_TOL = 1.0e-8
PERMUTATION_SEED_MATERIAL = "H3ResidualSpecificity_d_resid4_v1"

BASES = ("A", "C", "G", "U")
CHEMICAL_CHARACTERS = {
    "R": {"A": 1.0, "G": 1.0, "C": -1.0, "U": -1.0},
    "W": {"A": 1.0, "U": 1.0, "G": -1.0, "C": -1.0},
    "K": {"G": 1.0, "U": 1.0, "A": -1.0, "C": -1.0},
}
CHARACTER_ORDER = ("1", "R", "W", "K")

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_h3_necessitation_cert as route_s  # noqa: E402


def repo_root() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[3]


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def stable_seed(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:16], "big")


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def add(left: list[float], right: list[float]) -> list[float]:
    return [left[index] + right[index] for index in range(len(left))]


def sub(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def scale(factor: float, vector: list[float]) -> list[float]:
    return [factor * value for value in vector]


def unit(vector: list[float]) -> list[float] | None:
    value = norm(vector)
    if value <= EPS:
        return None
    return [entry / value for entry in vector]


def median(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def modified_gram_schmidt(columns: list[list[float]], tol: float = TOL) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        residual = [float(value) for value in column]
        for q in basis:
            coeff = dot(residual, q)
            if coeff:
                for index, value in enumerate(q):
                    residual[index] -= coeff * value
        residual_norm = norm(residual)
        if residual_norm > tol:
            basis.append([value / residual_norm for value in residual])
    return basis


def project(vector: list[float], basis: list[list[float]]) -> list[float]:
    out = [0.0 for _ in vector]
    for q in basis:
        coeff = dot(vector, q)
        if coeff:
            for index, value in enumerate(q):
                out[index] += coeff * value
    return out


def residual(vector: list[float], basis: list[list[float]]) -> list[float]:
    return sub(vector, project(vector, basis))


def frobenius_projector_difference2(left: list[list[float]], right: list[list[float]]) -> float:
    total = 0.0
    dim = len(left[0]) if left else (len(right[0]) if right else 0)
    for index in range(dim):
        e = [0.0 for _ in range(dim)]
        e[index] = 1.0
        diff = sub(project(e, left), project(e, right))
        total += dot(diff, diff)
    return total


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def character_value(label: str, base: str) -> float:
    if label == "1":
        return 1.0
    return CHEMICAL_CHARACTERS[label][base]


def character_tensor(labels: tuple[str, str, str], codons: list[str]) -> list[float]:
    return [
        character_value(labels[0], codon[0])
        * character_value(labels[1], codon[1])
        * character_value(labels[2], codon[2])
        for codon in codons
    ]


def eigenspace_columns(codons: list[str]) -> dict[int, list[list[float]]]:
    by_level: dict[int, list[list[float]]] = {0: [], 1: [], 2: [], 3: []}
    for labels in product(CHARACTER_ORDER, repeat=3):
        level = sum(label != "1" for label in labels)
        by_level[level].append(character_tensor(labels, codons))
    return by_level


def families_by_aa(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[code[codon]].append(codon)
    return dict(families)


def aa_indicator_columns(code: dict[str, str], codons: list[str]) -> list[list[float]]:
    columns: list[list[float]] = []
    for aa in sorted({code[codon] for codon in codons}):
        columns.append([1.0 if code[codon] == aa else 0.0 for codon in codons])
    return columns


def synonym_contrast_columns(codons: list[str], families: dict[str, list[str]]) -> list[list[float]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    columns: list[list[float]] = []
    for aa in sorted(families):
        family = sorted(families[aa])
        if len(family) < 2:
            continue
        reference = family[-1]
        for codon in family[:-1]:
            vector = [0.0 for _ in codons]
            vector[index[codon]] = 1.0
            vector[index[reference]] = -1.0
            columns.append(vector)
    return columns


def codon_basic_control_columns(code: dict[str, str], codons: list[str]) -> list[list[float]]:
    aa_columns = aa_indicator_columns(code, codons)
    q_support = {
        codon
        for vector in route_s.q_vectors(codons).values()
        for codon, value in vector.items()
        if abs(value) > 0.0
    }
    return aa_columns + [
        [1.0 if codon[2] in {"G", "C"} else 0.0 for codon in codons],
        [1.0 for _ in codons],
        [1.0 if codon in q_support else 0.0 for codon in codons],
    ]


class Geometry:
    def __init__(self, code: dict[str, str], codons: list[str]) -> None:
        self.code = code
        self.codons = codons
        self.families = families_by_aa(code, codons)
        self.aa_basis = modified_gram_schmidt(aa_indicator_columns(code, codons))
        self.w_basis = modified_gram_schmidt(synonym_contrast_columns(codons, self.families))
        control_columns = [self.project_w(column) for column in codon_basic_control_columns(code, codons)]
        self.basic_control_basis = modified_gram_schmidt(control_columns)
        self.q0w_basis = modified_gram_schmidt([self.q0(column) for column in self.w_basis])
        degree_columns = eigenspace_columns(codons)
        self.l12_basis = modified_gram_schmidt([self.q0(column) for column in degree_columns[1] + degree_columns[2]])
        self.l3_basis = modified_gram_schmidt([self.q0(column) for column in degree_columns[3]])
        self.l123_basis = modified_gram_schmidt(self.l12_basis + self.l3_basis)
        self.r3_given_12 = len(self.l123_basis) - len(self.l12_basis)
        self.r12_given_3 = len(self.l123_basis) - len(self.l3_basis)
        self.frob_3_given_12 = frobenius_projector_difference2(self.l123_basis, self.l12_basis)
        self.frob_12_given_3 = frobenius_projector_difference2(self.l123_basis, self.l3_basis)

    def project_w(self, vector: list[float]) -> list[float]:
        return residual(vector, self.aa_basis)

    def q0(self, vector: list[float]) -> list[float]:
        return residual(self.project_w(vector), self.basic_control_basis)

    def normalize_q0(self, vector: list[float]) -> list[float] | None:
        projected = self.q0(vector)
        return unit(projected)

    def project_l123(self, vector: list[float]) -> list[float]:
        return project(vector, self.l123_basis)

    def project_u3_given_12(self, vector: list[float]) -> list[float]:
        return sub(project(vector, self.l123_basis), project(vector, self.l12_basis))

    def project_u12_given_3(self, vector: list[float]) -> list[float]:
        return sub(project(vector, self.l123_basis), project(vector, self.l3_basis))

    def identifiability(self) -> dict[str, object]:
        checks = {
            "rank_W_is_41": len(self.w_basis) == 41,
            "rank_Q0W_at_least_30": len(self.q0w_basis) >= 30,
            "rank_L3_positive": len(self.l3_basis) > 0,
            "rank_L12_positive": len(self.l12_basis) > 0,
            "rank_L123_strictly_expands": len(self.l123_basis) > max(len(self.l3_basis), len(self.l12_basis)),
            "rank_U3_given_12_at_least_4": self.r3_given_12 >= 4,
            "rank_U12_given_3_at_least_4": self.r12_given_3 >= 4,
            "frob_U3_given_12_positive": self.frob_3_given_12 > FROBENIUS_TOL,
            "frob_U12_given_3_positive": self.frob_12_given_3 > FROBENIUS_TOL,
        }
        verdict = "ok" if all(checks.values()) else ("needs_derivation" if self.r3_given_12 == 0 or self.r12_given_3 == 0 else "failed")
        return {
            "verdict": verdict,
            "checks": checks,
            "rank_W": len(self.w_basis),
            "rank_Q0W": len(self.q0w_basis),
            "rank_L12": len(self.l12_basis),
            "rank_L3": len(self.l3_basis),
            "rank_L123": len(self.l123_basis),
            "r3_given_12": self.r3_given_12,
            "r12_given_3": self.r12_given_3,
            "frobenius2_U3_given_12": self.frob_3_given_12,
            "frobenius2_U12_given_3": self.frob_12_given_3,
        }


def conserved_energy(rows: list[list[float]], projector) -> float:
    n = len(rows)
    if n < 2:
        return 0.0
    projected = [projector(row) for row in rows]
    total = 0.0
    for i in range(n):
        for j in range(n):
            if i != j:
                total += dot(projected[i], projected[j])
    return total / (n * (n - 1))


def ratio_value(a3: float, a12: float) -> float:
    if a12 > 0.0:
        return a3 / a12
    if a3 > 0.0:
        return math.inf
    return 0.0


def score_rows(rows: list[list[float]], geometry: Geometry) -> dict[str, object]:
    c3 = conserved_energy(rows, geometry.project_u3_given_12)
    c12 = conserved_energy(rows, geometry.project_u12_given_3)
    c123 = conserved_energy(rows, geometry.project_l123)
    a3 = c3 / geometry.r3_given_12 if geometry.r3_given_12 > 0 else 0.0
    a12 = c12 / geometry.r12_given_3 if geometry.r12_given_3 > 0 else 0.0
    advantage = a3 - a12
    return {
        "C_U3_given_12": c3,
        "C_U12_given_3": c12,
        "C_L123": c123,
        "a3": a3,
        "a12": a12,
        "A_obs": advantage,
        "R_obs": ratio_value(a3, a12),
    }


def organism_advantages(rows: list[list[float]], names: list[str], geometry: Geometry) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    projected_3 = [geometry.project_u3_given_12(row) for row in rows]
    projected_12 = [geometry.project_u12_given_3(row) for row in rows]
    n = len(rows)
    for i, name in enumerate(names):
        centroid_3 = [0.0 for _ in rows[0]]
        centroid_12 = [0.0 for _ in rows[0]]
        for j in range(n):
            if i == j:
                continue
            centroid_3 = add(centroid_3, projected_3[j])
            centroid_12 = add(centroid_12, projected_12[j])
        centroid_3 = scale(1.0 / (n - 1), centroid_3)
        centroid_12 = scale(1.0 / (n - 1), centroid_12)
        a_i = dot(projected_3[i], centroid_3) / geometry.r3_given_12 - dot(projected_12[i], centroid_12) / geometry.r12_given_3
        out.append({"organism": name, "A_i": a_i, "positive": a_i > 0.0})
    return out


def delete_one_scores(rows: list[list[float]], names: list[str], geometry: Geometry) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for i, name in enumerate(names):
        subset = [row for j, row in enumerate(rows) if j != i]
        score = score_rows(subset, geometry)
        out.append(
            {
                "deleted_organism": name,
                "A_obs_without_i": score["A_obs"],
                "R_obs_without_i": score["R_obs"],
                "positive": float(score["A_obs"]) > 0.0,
            }
        )
    return out


def permuted_rows(rows: list[list[float]], geometry: Geometry, rng: random.Random) -> list[list[float]]:
    index = {codon: pos for pos, codon in enumerate(geometry.codons)}
    mapping = {codon: codon for codon in geometry.codons}
    for family in geometry.families.values():
        if len(family) < 2:
            continue
        source = sorted(family)
        target = list(source)
        rng.shuffle(target)
        for src, dst in zip(source, target):
            mapping[src] = dst
    out: list[list[float]] = []
    for row in rows:
        shuffled = [0.0 for _ in row]
        for src, dst in mapping.items():
            shuffled[index[dst]] = row[index[src]]
        normalized = geometry.normalize_q0(shuffled)
        if normalized is None:
            raise RuntimeError("permuted Q0 row collapsed")
        out.append(normalized)
    return out


def permutation_null(
    rows: list[list[float]],
    geometry: Geometry,
    reps: int,
    raw_rows: list[list[float]] | None = None,
) -> dict[str, object]:
    observed = float(score_rows(rows, geometry)["A_obs"])
    source_rows = raw_rows if raw_rows is not None else rows
    rng = random.Random(stable_seed(PERMUTATION_SEED_MATERIAL))
    values: list[float] = []
    exceed = 0
    for _rep in range(reps):
        value = float(score_rows(permuted_rows(source_rows, geometry, rng), geometry)["A_obs"])
        values.append(value)
        if value >= observed:
            exceed += 1
    p_value = (1 + exceed) / (reps + 1)
    return {
        "B": reps,
        "seed": f"sha256({PERMUTATION_SEED_MATERIAL})",
        "p_one_sided": p_value,
        "exceedances": exceed,
        "null_min": min(values) if values else None,
        "null_max": max(values) if values else None,
        "null_mean": sum(values) / len(values) if values else None,
        "values": values,
    }


def verdict_for(
    *,
    identifiability: dict[str, object],
    score: dict[str, object],
    p_value: float,
    organism_rows: list[dict[str, object]],
    delete_rows: list[dict[str, object]],
) -> str:
    if identifiability["verdict"] != "ok":
        return str(identifiability["verdict"])
    a3 = float(score["a3"])
    a12 = float(score["a12"])
    advantage = float(score["A_obs"])
    ratio = float(score["R_obs"])
    c3 = float(score["C_U3_given_12"])
    c123 = float(score["C_L123"])
    organism_positive = sum(1 for row in organism_rows if row["positive"])
    delete_positive = sum(1 for row in delete_rows if row["positive"])
    median_delete_ratio = median([float(row["R_obs_without_i"]) for row in delete_rows])
    c3_share_ok = c123 <= 0.0 or c3 >= 0.10 * c123
    if (
        a3 > 0.0
        and advantage > 0.0
        and ratio >= 2.0
        and p_value <= 0.01
        and organism_positive >= 10
        and delete_positive >= 10
        and median_delete_ratio >= 1.5
        and c3_share_ok
    ):
        return "passed"
    if (
        a3 <= 0.0
        or advantage <= 0.0
        or ratio <= 1.0
        or p_value >= 0.20
        or organism_positive < 8
        or delete_positive < 8
    ):
        return "failed"
    if (
        a3 > 0.0
        and advantage > 0.0
        and ratio > 1.0
        and (
            0.01 < p_value < 0.20
            or organism_positive in {8, 9}
            or delete_positive in {8, 9}
            or 1.0 <= median_delete_ratio < 1.5
        )
    ):
        return "needs_more_organisms"
    return "failed"


def build_real_inputs() -> tuple[Geometry, list[str], list[list[float]], list[list[float]], list[dict[str, object]]]:
    repo = repo_root()
    code = route_s.standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    geometry = Geometry(code, codons)
    aa_order = route_s.standard_amino_acids(code, codons)
    fibers = route_s.fibers_for(code, codons)
    syn_columns = route_s.synonymous_contrast_columns(fibers=fibers)
    f3_projected = route_s.project_syn(route_s.q_vectors(codons)["f3_stress"], fibers)
    f3_direction = route_s.f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
    if f3_direction is None:
        raise RuntimeError("could not build f3 direction")
    raw_rows = [
        route_s.load_organism_direction(
            repo=repo,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            fibers=fibers,
            syn_columns=syn_columns,
            f3_direction=f3_direction,
        )
        for organism in route_s.ORGANISMS
    ]
    names: list[str] = []
    rows: list[list[float]] = []
    raw_codon_rows: list[list[float]] = []
    for row in raw_rows:
        if row.get("status") != "computed" or not isinstance(row.get("d_resid4"), list):
            continue
        codon_vector = route_s.contrast_to_codon_vector(row["d_resid4"], codons, fibers, syn_columns)  # type: ignore[arg-type]
        normalized = geometry.normalize_q0(codon_vector)
        if normalized is None:
            continue
        names.append(str(row["organism"]))
        raw_codon_rows.append(codon_vector)
        rows.append(normalized)
    return geometry, names, rows, raw_codon_rows, raw_rows


def run_certificate(null_reps: int) -> dict[str, object]:
    geometry, names, rows, raw_codon_rows, raw_rows = build_real_inputs()
    identifiability = geometry.identifiability()
    if identifiability["verdict"] != "ok":
        return {
            "verdict": identifiability["verdict"],
            "n_organisms": len(rows),
            "organisms": names,
            "identifiability": identifiability,
        }
    score = score_rows(rows, geometry)
    organism_rows = organism_advantages(rows, names, geometry)
    delete_rows = delete_one_scores(rows, names, geometry)
    null = permutation_null(rows, geometry, null_reps, raw_codon_rows)
    verdict = verdict_for(
        identifiability=identifiability,
        score=score,
        p_value=float(null["p_one_sided"]),
        organism_rows=organism_rows,
        delete_rows=delete_rows,
    )
    return {
        "verdict": verdict,
        "n_organisms": len(rows),
        "organisms": names,
        "skipped": [row for row in raw_rows if row.get("status") != "computed"],
        "identifiability": identifiability,
        "score": score,
        "permutation_null": null,
        "organism_stability": {
            "per_organism": organism_rows,
            "positive_count": sum(1 for row in organism_rows if row["positive"]),
        },
        "delete_one_stability": {
            "per_deleted_organism": delete_rows,
            "positive_count": sum(1 for row in delete_rows if row["positive"]),
            "median_R_obs_without_i": median([float(row["R_obs_without_i"]) for row in delete_rows]),
        },
        "reuse_path": "d_resid4 extraction, organism loading, and contrast-to-codon conversion reuse run_h3_necessitation_cert.py; semipartial H3 test is local.",
    }


def synthetic_geometry(dim: int, l12_dim: int, shared_dim: int, u3_dim: int, u12_dim: int) -> Geometry:
    obj = object.__new__(Geometry)
    obj.code = {str(index): "X" for index in range(dim)}
    obj.codons = [str(index) for index in range(dim)]
    obj.families = {"X": obj.codons}
    standard = []
    for index in range(dim):
        e = [0.0 for _ in range(dim)]
        e[index] = 1.0
        standard.append(e)
    obj.w_basis = standard
    obj.q0w_basis = standard
    obj.aa_basis = []
    obj.basic_control_basis = []
    shared = standard[:shared_dim]
    u12 = standard[shared_dim : shared_dim + u12_dim]
    u3 = standard[shared_dim + u12_dim : shared_dim + u12_dim + u3_dim]
    obj.l12_basis = modified_gram_schmidt(shared + u12)
    obj.l3_basis = modified_gram_schmidt(shared + u3)
    obj.l123_basis = modified_gram_schmidt(shared + u12 + u3)
    obj.r3_given_12 = len(obj.l123_basis) - len(obj.l12_basis)
    obj.r12_given_3 = len(obj.l123_basis) - len(obj.l3_basis)
    obj.frob_3_given_12 = frobenius_projector_difference2(obj.l123_basis, obj.l12_basis)
    obj.frob_12_given_3 = frobenius_projector_difference2(obj.l123_basis, obj.l3_basis)
    return obj


def gaussian_vector(dim: int, rng: random.Random) -> list[float]:
    values: list[float] = []
    while len(values) < dim:
        u1 = max(rng.random(), 1.0e-12)
        u2 = rng.random()
        radius = math.sqrt(-2.0 * math.log(u1))
        angle = 2.0 * math.pi * u2
        values.append(radius * math.cos(angle))
        if len(values) < dim:
            values.append(radius * math.sin(angle))
    return values


def synthetic_rows(
    geometry: Geometry,
    signal: list[float],
    *,
    noise_scale: float,
    material: str,
    n: int = 12,
) -> tuple[list[str], list[list[float]]]:
    names = [f"org_{index}" for index in range(n)]
    rows: list[list[float]] = []
    signal_unit = unit(signal)
    if signal_unit is None:
        raise AssertionError("synthetic signal collapsed")
    for index in range(n):
        rng = random.Random(stable_seed(f"{material}|{index}"))
        noise = unit(gaussian_vector(len(signal), rng)) or [0.0 for _ in signal]
        row = unit(add(signal_unit, scale(noise_scale, noise)))
        if row is None:
            raise AssertionError("synthetic row collapsed")
        rows.append(row)
    return names, rows


def verdict_without_null(geometry: Geometry, names: list[str], rows: list[list[float]], p_value: float) -> str:
    identifiability = geometry.identifiability()
    if identifiability["verdict"] != "ok":
        return str(identifiability["verdict"])
    return verdict_for(
        identifiability=identifiability,
        score=score_rows(rows, geometry),
        p_value=p_value,
        organism_rows=organism_advantages(rows, names, geometry),
        delete_rows=delete_one_scores(rows, names, geometry),
    )


def assert_conserved_energy_math() -> None:
    geometry = synthetic_geometry(8, 4, 1, 4, 3)
    rows = [
        unit([1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]) or [],
        unit([1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]) or [],
        unit([1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]) or [],
    ]
    c3 = conserved_energy(rows, geometry.project_u3_given_12)
    if abs(c3 - 0.5) > 1.0e-9:
        raise AssertionError(f"conserved-energy calculation drifted: {c3}")


def assert_permutation_null_logic() -> None:
    geometry = synthetic_geometry(8, 4, 1, 4, 3)
    geometry.families = {"X": geometry.codons[:4], "Y": geometry.codons[4:]}
    rows = [unit([1.0, -1.0, 0.5, -0.5, 0.25, -0.25, 0.75, -0.75]) or [] for _ in range(3)]
    rng = random.Random(17)
    permuted = permuted_rows(rows, geometry, rng)
    for row in permuted:
        if abs(norm(row) - 1.0) > 1.0e-9:
            raise AssertionError("permuted row was not normalized")
    null = permutation_null(rows, geometry, 3)
    if null["B"] != 3 or not (0.0 < float(null["p_one_sided"]) <= 1.0):
        raise AssertionError("permutation-null p-value logic drifted")


def selftest() -> None:
    planted_geometry = synthetic_geometry(41, 32, 20, 9, 12)
    u3_signal = planted_geometry.l123_basis[-1]
    names, rows = synthetic_rows(planted_geometry, u3_signal, noise_scale=0.02, material="planted")
    planted_verdict = verdict_without_null(planted_geometry, names, rows, 0.005)
    shared_signal = planted_geometry.l123_basis[0]
    shared_names, shared_rows = synthetic_rows(planted_geometry, shared_signal, noise_scale=0.02, material="shared")
    shared_verdict = verdict_without_null(planted_geometry, shared_names, shared_rows, 0.005)
    collapsed_geometry = synthetic_geometry(41, 41, 41, 0, 0)
    collapsed_names, collapsed_rows = synthetic_rows(collapsed_geometry, collapsed_geometry.l123_basis[0], noise_scale=0.0, material="collapsed")
    collapsed_verdict = verdict_without_null(collapsed_geometry, collapsed_names, collapsed_rows, 0.005)
    random_geometry = synthetic_geometry(41, 32, 20, 9, 12)
    random_names = [f"org_{index}" for index in range(12)]
    random_rows = [unit(gaussian_vector(41, random.Random(stable_seed(f"random|{index}")))) or [] for index in range(12)]
    random_verdict = verdict_without_null(random_geometry, random_names, random_rows, 0.50)
    more_verdict = verdict_without_null(planted_geometry, names, rows, 0.05)
    weak_verdict = verdict_without_null(planted_geometry, names, rows, 0.25)
    assert_conserved_energy_math()
    assert_permutation_null_logic()
    if planted_verdict != "passed":
        raise AssertionError(f"planted E3-unique synthetic did not pass: {planted_verdict}")
    if shared_verdict == "passed":
        raise AssertionError("shared-geometry synthetic was credited as passed")
    if collapsed_verdict != "needs_derivation":
        raise AssertionError(f"collapsed spaces did not refuse: {collapsed_verdict}")
    if random_verdict != "failed":
        raise AssertionError(f"random synthetic did not fail: {random_verdict}")
    if more_verdict != "needs_more_organisms":
        raise AssertionError(f"directional synthetic did not exercise needs_more_organisms: {more_verdict}")
    if weak_verdict != "failed":
        raise AssertionError(f"hard-negative synthetic did not fail: {weak_verdict}")
    print(
        json.dumps(
            {
                "ok": True,
                "verdicts": {
                    "planted_E3_unique": planted_verdict,
                    "shared_geometry": shared_verdict,
                    "collapsed": collapsed_verdict,
                    "random": random_verdict,
                    "directional": more_verdict,
                    "hard_negative": weak_verdict,
                },
            },
            sort_keys=False,
            separators=(",", ":"),
        )
    )


def main() -> None:
    if "--selftest" in sys.argv:
        selftest()
        return
    null_reps = DEFAULT_NULL_REPS
    for arg in sys.argv[1:]:
        if arg.startswith("--null-reps="):
            null_reps = int(arg.split("=", 1)[1])
    result = run_certificate(null_reps)
    verdict = str(result["verdict"])
    status = verdict if verdict in {"passed", "failed", "needs_more_organisms", "needs_derivation"} else "failed"
    emit(status, result=result)


if __name__ == "__main__":
    main()

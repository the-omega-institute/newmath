#!/usr/bin/env python3
"""E2-unique concentration test for d_resid4 low-order conserved geometry."""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
import pathlib
import random
import statistics
import sys


EXPERIMENT_ID = "e2_unique_concentration"
CLAIM_ID = "bridge.genetic_code.e2_unique_concentration"
DEFAULT_NULL_REPS = 50000
SELFTEST_NULL_REPS = 80
EPS = 1.0e-12
TOL = 1.0e-10
FROBENIUS_TOL = 1.0e-8
RANK_SHARE_BASELINE = 8.0 / 12.0
PERMUTATION_SEED_MATERIAL = "E2UniqueConcentration_d_resid4_v1"

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
    sys.exit(0 if status == "passed" else (2 if status in {"failed", "gate_failed"} else 3))


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


def variance(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return statistics.pvariance(values)


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


def frobenius_operator_norm(operator, dim: int) -> float:
    total = 0.0
    for index in range(dim):
        e = [0.0 for _ in range(dim)]
        e[index] = 1.0
        value = operator(e)
        total += dot(value, value)
    return math.sqrt(total)


def frobenius_difference(left, right, dim: int) -> float:
    return frobenius_operator_norm(lambda x: sub(left(x), right(x)), dim)


def projector_idempotence(projector, dim: int) -> float:
    return frobenius_difference(lambda x: projector(projector(x)), projector, dim)


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
        self.l1_basis = modified_gram_schmidt([self.q0(column) for column in degree_columns[1]])
        self.l2_basis = modified_gram_schmidt([self.q0(column) for column in degree_columns[2]])
        self.l3_basis = modified_gram_schmidt([self.q0(column) for column in degree_columns[3]])
        self.v_basis = modified_gram_schmidt(self.l1_basis + self.l2_basis + self.l3_basis)
        self.l23_basis = modified_gram_schmidt(self.l2_basis + self.l3_basis)
        self.l13_basis = modified_gram_schmidt(self.l1_basis + self.l3_basis)
        self.rank_u1_given_23 = len(self.v_basis) - len(self.l23_basis)
        self.rank_u12_given_3 = len(self.v_basis) - len(self.l3_basis)
        self.rank_u2_given_13 = len(self.v_basis) - len(self.l13_basis)
        self.rank_uamb = self.rank_u12_given_3 - self.rank_u2_given_13

    def project_w(self, vector: list[float]) -> list[float]:
        return residual(vector, self.aa_basis)

    def q0(self, vector: list[float]) -> list[float]:
        return residual(self.project_w(vector), self.basic_control_basis)

    def normalize_q0(self, vector: list[float]) -> tuple[list[float] | None, float]:
        projected = self.q0(vector)
        value = norm(projected)
        if value <= EPS:
            return None, value
        return [entry / value for entry in projected], value

    def project_v(self, vector: list[float]) -> list[float]:
        return project(vector, self.v_basis)

    def project_l3(self, vector: list[float]) -> list[float]:
        return project(vector, self.l3_basis)

    def project_l13(self, vector: list[float]) -> list[float]:
        return project(vector, self.l13_basis)

    def project_u12_given_3(self, vector: list[float]) -> list[float]:
        return sub(project(vector, self.v_basis), project(vector, self.l3_basis))

    def project_u2_given_13(self, vector: list[float]) -> list[float]:
        return sub(project(vector, self.v_basis), project(vector, self.l13_basis))

    def project_uamb(self, vector: list[float]) -> list[float]:
        return sub(self.project_u12_given_3(vector), self.project_u2_given_13(vector))

    def projector_sanity(self) -> dict[str, float]:
        dim = len(self.codons)
        return {
            "P_U2_idempotence_F": projector_idempotence(self.project_u2_given_13, dim),
            "P_U12_idempotence_F": projector_idempotence(self.project_u12_given_3, dim),
            "P_Uamb_idempotence_F": projector_idempotence(self.project_uamb, dim),
            "P_U2_P_Uamb_F": frobenius_operator_norm(lambda x: self.project_u2_given_13(self.project_uamb(x)), dim),
            "P_U2_plus_P_Uamb_minus_P_U12_F": frobenius_difference(
                lambda x: add(self.project_u2_given_13(x), self.project_uamb(x)),
                self.project_u12_given_3,
                dim,
            ),
            "P_U12_P_U2_minus_P_U2_F": frobenius_difference(
                lambda x: self.project_u12_given_3(self.project_u2_given_13(x)),
                self.project_u2_given_13,
                dim,
            ),
        }

    def identifiability(self) -> dict[str, object]:
        sanity = self.projector_sanity()
        ranks = {
            "rank_W": len(self.w_basis),
            "rank_Q0W": len(self.q0w_basis),
            "rank_L1": len(self.l1_basis),
            "rank_L2": len(self.l2_basis),
            "rank_L3": len(self.l3_basis),
            "rank_V": len(self.v_basis),
            "rank_L23": len(self.l23_basis),
            "rank_L13": len(self.l13_basis),
            "rank_U1_given_23": self.rank_u1_given_23,
            "rank_U12_given_3": self.rank_u12_given_3,
            "rank_U2_given_13": self.rank_u2_given_13,
            "rank_Uamb": self.rank_uamb,
        }
        rank_checks = {
            "rank_W_is_41": ranks["rank_W"] == 41,
            "rank_Q0W_is_39": ranks["rank_Q0W"] == 39,
            "rank_L1_is_5": ranks["rank_L1"] == 5,
            "rank_L2_is_21": ranks["rank_L2"] == 21,
            "rank_L3_is_27": ranks["rank_L3"] == 27,
            "rank_V_is_39": ranks["rank_V"] == 39,
            "rank_L23_is_39": ranks["rank_L23"] == 39,
            "rank_L13_is_31": ranks["rank_L13"] == 31,
            "rank_U1_given_23_is_0": ranks["rank_U1_given_23"] == 0,
            "rank_U12_given_3_is_12": ranks["rank_U12_given_3"] == 12,
            "rank_U2_given_13_is_8": ranks["rank_U2_given_13"] == 8,
            "rank_Uamb_is_4": ranks["rank_Uamb"] == 4,
        }
        sanity_checks = {name: value < FROBENIUS_TOL for name, value in sanity.items()}
        minimal_carrier = self.rank_u2_given_13 >= 4 and self.rank_uamb >= 1
        verdict = "ok" if all(rank_checks.values()) and all(sanity_checks.values()) else "needs_derivation"
        if not minimal_carrier:
            verdict = "needs_derivation"
        return {
            "verdict": verdict,
            **ranks,
            "rank_checks": rank_checks,
            "projector_sanity": sanity,
            "projector_checks": sanity_checks,
            "minimal_carrier_identifiable": minimal_carrier,
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


def ratio_value(a2: float, a_amb: float) -> float:
    if a_amb > 0.0:
        return a2 / a_amb
    if a2 > 0.0:
        return math.inf
    return 0.0


def score_rows(rows: list[list[float]], geometry: Geometry) -> dict[str, object]:
    c12 = conserved_energy(rows, geometry.project_u12_given_3)
    c2 = conserved_energy(rows, geometry.project_u2_given_13)
    camb = c12 - c2
    rank_u2 = geometry.rank_u2_given_13
    rank_uamb = geometry.rank_uamb
    a2 = c2 / rank_u2 if rank_u2 > 0 else 0.0
    a_amb = camb / rank_uamb if rank_uamb > 0 else 0.0
    return {
        "C12": c12,
        "C2": c2,
        "Camb": camb,
        "F_obs": c2 / c12 if c12 > 0.0 else -math.inf,
        "a2": a2,
        "a_amb": a_amb,
        "A_obs": a2 - a_amb,
        "R_obs": ratio_value(a2, a_amb),
    }


def organism_advantages(rows: list[list[float]], names: list[str], geometry: Geometry) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    projected_u2 = [geometry.project_u2_given_13(row) for row in rows]
    projected_uamb = [geometry.project_uamb(row) for row in rows]
    n = len(rows)
    for i, name in enumerate(names):
        centroid_u2 = [0.0 for _ in rows[0]]
        centroid_uamb = [0.0 for _ in rows[0]]
        for j in range(n):
            if i == j:
                continue
            centroid_u2 = add(centroid_u2, projected_u2[j])
            centroid_uamb = add(centroid_uamb, projected_uamb[j])
        centroid_u2 = scale(1.0 / (n - 1), centroid_u2)
        centroid_uamb = scale(1.0 / (n - 1), centroid_uamb)
        a_i = dot(projected_u2[i], centroid_u2) / geometry.rank_u2_given_13
        a_i -= dot(projected_uamb[i], centroid_uamb) / geometry.rank_uamb
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
                "F_obs_without_i": score["F_obs"],
                "R_obs_without_i": score["R_obs"],
                "positive": float(score["A_obs"]) > 0.0,
            }
        )
    return out


def finite_float(value: object) -> bool:
    return isinstance(value, (int, float)) and math.isfinite(float(value))


def canonical_float(value: float) -> str:
    return format(value, ".17g")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def matrix_sha(rows: list[list[float]], row_names: list[str], col_names: list[str]) -> str:
    parts = ["organism\t" + "\t".join(col_names)]
    for name, row in zip(row_names, rows):
        parts.append(name + "\t" + "\t".join(canonical_float(value) for value in row))
    return sha256_text("\n".join(parts) + "\n")


def code_sha(code: dict[str, str], codons: list[str]) -> str:
    return sha256_text("\n".join(f"{codon}\t{code[codon]}" for codon in codons) + "\n")


def controls_sha(geometry: Geometry) -> str:
    labels = ["AA_basis", "basic_control_basis", "Q0W_basis"]
    blocks = [
        geometry.aa_basis,
        geometry.basic_control_basis,
        geometry.q0w_basis,
    ]
    parts: list[str] = []
    for label, block in zip(labels, blocks):
        parts.append(label)
        for vector in block:
            parts.append("\t".join(canonical_float(value) for value in vector))
    return sha256_text("\n".join(parts) + "\n")


def manifest_for(
    *,
    code: dict[str, str],
    codons: list[str],
    names: list[str],
    raw_rows: list[list[float]],
    geometry: Geometry,
) -> dict[str, str]:
    return {
        "d_resid4_matrix_sha256": matrix_sha(raw_rows, names, codons),
        "codon_order_sha256": sha256_text("\n".join(codons) + "\n"),
        "organism_order_sha256": sha256_text("\n".join(names) + "\n"),
        "standard_code_table_sha256": code_sha(code, codons),
        "Q0_basic_control_vectors_sha256": controls_sha(geometry),
    }


def permuted_rows(
    source_rows: list[list[float]],
    geometry: Geometry,
    rng: random.Random,
) -> tuple[list[list[float]], tuple[tuple[str, str], ...]]:
    index = {codon: pos for pos, codon in enumerate(geometry.codons)}
    mapping = {codon: codon for codon in geometry.codons}
    for aa, family in sorted(geometry.families.items()):
        source = sorted(family)
        if len(source) < 2:
            continue
        target = list(source)
        rng.shuffle(target)
        for src, dst in zip(source, target):
            mapping[src] = dst
    out: list[list[float]] = []
    for row in source_rows:
        shuffled = [0.0 for _ in row]
        for src, dst in mapping.items():
            shuffled[index[dst]] = row[index[src]]
        normalized, _qnorm = geometry.normalize_q0(shuffled)
        if normalized is None:
            raise RuntimeError("permuted Q0 row collapsed")
        out.append(normalized)
    signature = tuple(sorted(mapping.items()))
    return out, signature


def permutation_null(
    rows: list[list[float]],
    geometry: Geometry,
    reps: int,
    raw_rows: list[list[float]] | None = None,
) -> dict[str, object]:
    observed = score_rows(rows, geometry)
    observed_a = float(observed["A_obs"])
    observed_f = float(observed["F_obs"])
    source_rows = raw_rows if raw_rows is not None else rows
    rng = random.Random(stable_seed(PERMUTATION_SEED_MATERIAL))
    a_values: list[float] = []
    f_values: list[float] = []
    r_values: list[float] = []
    c12_values: list[float] = []
    c2_values: list[float] = []
    camb_values: list[float] = []
    distinct: set[tuple[tuple[str, str], ...]] = set()
    exceed_a = 0
    exceed_f = 0
    for _rep in range(reps):
        permuted, signature = permuted_rows(source_rows, geometry, rng)
        distinct.add(signature)
        score = score_rows(permuted, geometry)
        a_value = float(score["A_obs"])
        f_value = float(score["F_obs"])
        a_values.append(a_value)
        f_values.append(f_value)
        r_values.append(float(score["R_obs"]))
        c12_values.append(float(score["C12"]))
        c2_values.append(float(score["C2"]))
        camb_values.append(float(score["Camb"]))
        if a_value >= observed_a:
            exceed_a += 1
        if f_value >= observed_f:
            exceed_f += 1
    finite_f = [value for value in f_values if math.isfinite(value)]
    return {
        "B": reps,
        "seed": f"sha256({PERMUTATION_SEED_MATERIAL})",
        "completed_permutations": reps,
        "distinct_global_synonymous_label_permutations": len(distinct),
        "p_A": (1 + exceed_a) / (reps + 1),
        "p_F": (1 + exceed_f) / (reps + 1),
        "exceedances_A": exceed_a,
        "exceedances_F": exceed_f,
        "var_A_null": variance(a_values),
        "var_F_null_finite": variance(finite_f),
        "null_min_A": min(a_values) if a_values else None,
        "null_max_A": max(a_values) if a_values else None,
        "null_mean_A": sum(a_values) / len(a_values) if a_values else None,
        "null_min_F": min(finite_f) if finite_f else None,
        "null_max_F": max(finite_f) if finite_f else None,
        "null_mean_F": sum(finite_f) / len(finite_f) if finite_f else None,
        "values_A": a_values,
        "values_F": f_values,
        "values_R": r_values,
        "values_C12": c12_values,
        "values_C2": c2_values,
        "values_Camb": camb_values,
    }


def null_gates(null: dict[str, object], expected_reps: int) -> dict[str, object]:
    return {
        "B_completed": int(null.get("completed_permutations", 0)) == expected_reps,
        "distinct_permutations": int(null.get("distinct_global_synonymous_label_permutations", 0)) >= min(40000, expected_reps),
        "var_A_positive": float(null.get("var_A_null", 0.0)) > 0.0,
        "var_F_positive": float(null.get("var_F_null_finite", 0.0)) > 0.0,
    }


def data_gates(
    *,
    code: dict[str, str],
    codons: list[str],
    names: list[str],
    rows: list[list[float]],
    raw_rows: list[list[float]],
    q0_norms: list[float],
) -> dict[str, object]:
    finite = all(finite_float(value) for row in raw_rows for value in row)
    all_survive = all(value > 1.0e-10 for value in q0_norms)
    norm_ratio = min(q0_norms) / median(q0_norms) if q0_norms and median(q0_norms) > 0.0 else 0.0
    standard_sense_only = len(codons) == 61 and all(code[codon] != "*" for codon in codons)
    checks = {
        "exactly_12_organisms": len(rows) == 12 and len(names) == 12,
        "exactly_61_sense_codons": all(len(row) == 61 for row in raw_rows) and len(codons) == 61,
        "standard_code_sense_codons_only": standard_sense_only,
        "finite_numeric_values_only": finite,
        "q0_norms_survive": all_survive,
        "q0_min_over_median_at_least_0_05": norm_ratio >= 0.05,
    }
    return {"verdict": "ok" if all(checks.values()) else "data_gate_failed", "checks": checks, "q0_norms": q0_norms, "q0_min_over_median": norm_ratio}


def verdict_for(
    *,
    preflight_ok: bool,
    preflight_label: str,
    score: dict[str, object],
    null: dict[str, object],
    organism_rows: list[dict[str, object]],
    delete_rows: list[dict[str, object]],
) -> str:
    if not preflight_ok:
        return preflight_label
    c12 = float(score["C12"])
    c2 = float(score["C2"])
    advantage = float(score["A_obs"])
    f_obs = float(score["F_obs"])
    ratio = float(score["R_obs"])
    p_a = float(null["p_A"])
    p_f = float(null["p_F"])
    organism_positive = sum(1 for row in organism_rows if row["positive"])
    delete_positive = sum(1 for row in delete_rows if row["positive"])
    median_delete_f = median([float(row["F_obs_without_i"]) for row in delete_rows])
    median_delete_r = median([float(row["R_obs_without_i"]) for row in delete_rows])
    if (
        c12 > 0.0
        and c2 > 0.0
        and advantage > 0.0
        and f_obs >= 0.80
        and ratio >= 2.0
        and p_a <= 0.01
        and p_f <= 0.01
        and organism_positive >= 10
        and delete_positive >= 10
        and median_delete_f >= 0.75
        and median_delete_r >= 1.5
    ):
        return "certified_E2_unique_low_order"
    if (
        c12 <= 0.0
        or c2 <= 0.0
        or advantage <= 0.0
        or f_obs <= RANK_SHARE_BASELINE
        or ratio <= 1.0
        or organism_positive < 7
        or delete_positive < 7
    ):
        return "refuted"
    directional = c12 > 0.0 and c2 > 0.0 and advantage > 0.0 and f_obs > RANK_SHARE_BASELINE and ratio > 1.0
    if directional and (
        0.01 < p_a < 0.20
        or 0.01 < p_f < 0.20
        or organism_positive in {8, 9}
        or delete_positive in {8, 9}
        or 0.70 <= f_obs < 0.80
        or 1.25 <= ratio < 2.0
    ):
        return "needs_more_organisms"
    if directional:
        return "coincidence_mixed_low_order"
    return "refuted"


def build_real_inputs() -> tuple[Geometry, list[str], list[list[float]], list[list[float]], list[float], list[dict[str, object]], dict[str, str]]:
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
    loaded_rows = [
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
    q0_norms: list[float] = []
    for row in loaded_rows:
        if row.get("status") != "computed" or not isinstance(row.get("d_resid4"), list):
            continue
        codon_vector = route_s.contrast_to_codon_vector(row["d_resid4"], codons, fibers, syn_columns)  # type: ignore[arg-type]
        normalized, q0_norm = geometry.normalize_q0(codon_vector)
        if normalized is None:
            continue
        names.append(str(row["organism"]))
        raw_codon_rows.append(codon_vector)
        rows.append(normalized)
        q0_norms.append(q0_norm)
    manifest = manifest_for(code=code, codons=codons, names=names, raw_rows=raw_codon_rows, geometry=geometry)
    return geometry, names, rows, raw_codon_rows, q0_norms, loaded_rows, manifest


def run_certificate(null_reps: int) -> dict[str, object]:
    geometry, names, rows, raw_codon_rows, q0_norms, loaded_rows, manifest = build_real_inputs()
    code = geometry.code
    codons = geometry.codons
    data_gate = data_gates(code=code, codons=codons, names=names, rows=rows, raw_rows=raw_codon_rows, q0_norms=q0_norms)
    identifiability = geometry.identifiability()
    preflight_label = "ok"
    if data_gate["verdict"] != "ok":
        preflight_label = "data_gate_failed"
    elif identifiability["verdict"] != "ok":
        preflight_label = "needs_derivation"
    if preflight_label != "ok":
        return {
            "verdict": preflight_label,
            "n_organisms": len(rows),
            "organisms": names,
            "data_gate": data_gate,
            "identifiability": identifiability,
            "sha256_manifest": manifest,
            "skipped": [row for row in loaded_rows if row.get("status") != "computed"],
        }
    score = score_rows(rows, geometry)
    organism_rows = organism_advantages(rows, names, geometry)
    delete_rows = delete_one_scores(rows, names, geometry)
    null = permutation_null(rows, geometry, null_reps, raw_codon_rows)
    gates = null_gates(null, null_reps)
    preflight_ok = all(gates.values())
    verdict = verdict_for(
        preflight_ok=preflight_ok,
        preflight_label="data_gate_failed",
        score=score,
        null=null,
        organism_rows=organism_rows,
        delete_rows=delete_rows,
    )
    return {
        "verdict": verdict,
        "n_organisms": len(rows),
        "organisms": names,
        "skipped": [row for row in loaded_rows if row.get("status") != "computed"],
        "sha256_manifest": manifest,
        "data_gate": data_gate,
        "identifiability": identifiability,
        "score": score,
        "permutation_null": null,
        "null_gates": gates,
        "organism_stability": {
            "per_organism": organism_rows,
            "positive_count": sum(1 for row in organism_rows if row["positive"]),
        },
        "delete_one_stability": {
            "per_deleted_organism": delete_rows,
            "positive_count": sum(1 for row in delete_rows if row["positive"]),
            "median_F_obs_without_i": median([float(row["F_obs_without_i"]) for row in delete_rows]),
            "median_R_obs_without_i": median([float(row["R_obs_without_i"]) for row in delete_rows]),
        },
        "reuse_path": "d_resid4 extraction and contrast-to-codon conversion reuse run_h3_necessitation_cert.py; E2 concentration geometry is local.",
    }


def synthetic_geometry(
    *,
    dim: int = 24,
    shared_l1_l3_dim: int = 10,
    u2_dim: int = 8,
    uamb_dim: int = 4,
) -> Geometry:
    obj = object.__new__(Geometry)
    obj.code = {str(index): "X" for index in range(dim)}
    obj.codons = [str(index) for index in range(dim)]
    obj.families = {"X": obj.codons}
    standard = []
    for index in range(dim):
        e = [0.0 for _ in range(dim)]
        e[index] = 1.0
        standard.append(e)
    shared = standard[:shared_l1_l3_dim]
    u2 = standard[shared_l1_l3_dim : shared_l1_l3_dim + u2_dim]
    uamb = standard[shared_l1_l3_dim + u2_dim : shared_l1_l3_dim + u2_dim + uamb_dim]
    obj.aa_basis = []
    obj.w_basis = standard
    obj.basic_control_basis = []
    obj.q0w_basis = standard
    obj.l1_basis = shared[: min(5, len(shared))]
    obj.l3_basis = modified_gram_schmidt(shared)
    obj.l2_basis = modified_gram_schmidt(u2 + uamb)
    obj.v_basis = modified_gram_schmidt(shared + u2 + uamb)
    obj.l23_basis = list(obj.v_basis)
    obj.l13_basis = modified_gram_schmidt(shared + uamb)
    obj.rank_u1_given_23 = len(obj.v_basis) - len(obj.l23_basis)
    obj.rank_u12_given_3 = len(obj.v_basis) - len(obj.l3_basis)
    obj.rank_u2_given_13 = len(obj.v_basis) - len(obj.l13_basis)
    obj.rank_uamb = obj.rank_u12_given_3 - obj.rank_u2_given_13
    return obj


def degenerate_geometry() -> Geometry:
    return synthetic_geometry(dim=12, shared_l1_l3_dim=10, u2_dim=1, uamb_dim=0)


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


def synthetic_component(projector, dim: int, material: str) -> list[float]:
    rng = random.Random(stable_seed(material))
    for attempt in range(32):
        projected = projector(gaussian_vector(dim, rng))
        normalized = unit(projected)
        if normalized is not None:
            return normalized
        rng = random.Random(stable_seed(f"{material}|{attempt}"))
    raise AssertionError("synthetic component collapsed")


def combine_components(
    geometry: Geometry,
    u2_signal: list[float],
    uamb_signal: list[float],
    u2_weight: float,
    uamb_weight: float,
    noise_scale: float,
    material: str,
    index: int,
) -> list[float]:
    rng = random.Random(stable_seed(f"{material}|{index}"))
    noise = unit(gaussian_vector(len(geometry.codons), rng)) or [0.0 for _ in geometry.codons]
    row = add(scale(u2_weight, u2_signal), scale(uamb_weight, uamb_signal))
    row = add(row, scale(noise_scale, noise))
    normalized = unit(row)
    if normalized is None:
        raise AssertionError("synthetic row collapsed")
    return normalized


def synthetic_rows(
    geometry: Geometry,
    *,
    u2_weight: float,
    uamb_weight: float,
    noise_scale: float,
    material: str,
    n: int = 12,
) -> tuple[list[str], list[list[float]]]:
    names = [f"org_{index}" for index in range(n)]
    dim = len(geometry.codons)
    u2_signal = synthetic_component(geometry.project_u2_given_13, dim, f"{material}|u2")
    if geometry.rank_uamb > 0:
        uamb_signal = synthetic_component(geometry.project_uamb, dim, f"{material}|uamb")
    else:
        uamb_signal = [0.0 for _ in geometry.codons]
    rows = [
        combine_components(geometry, u2_signal, uamb_signal, u2_weight, uamb_weight, noise_scale, material, index)
        for index in range(n)
    ]
    return names, rows


def synthetic_identifiability(geometry: Geometry) -> dict[str, object]:
    minimal = geometry.rank_u2_given_13 >= 4 and geometry.rank_uamb >= 1
    return {"verdict": "ok" if minimal else "needs_derivation"}


def verdict_without_real_null(
    geometry: Geometry,
    names: list[str],
    rows: list[list[float]],
    p_a: float,
    p_f: float,
    *,
    force_preflight: str = "ok",
) -> str:
    if force_preflight != "ok":
        return force_preflight
    ident = synthetic_identifiability(geometry)
    if ident["verdict"] != "ok":
        return "needs_derivation"
    return verdict_for(
        preflight_ok=True,
        preflight_label="ok",
        score=score_rows(rows, geometry),
        null={"p_A": p_a, "p_F": p_f},
        organism_rows=organism_advantages(rows, names, geometry),
        delete_rows=delete_one_scores(rows, names, geometry),
    )


def assert_projector_math() -> None:
    geometry = synthetic_geometry()
    sanity = geometry.projector_sanity()
    if any(value > 1.0e-9 for value in sanity.values()):
        raise AssertionError(f"synthetic projectors failed sanity: {sanity}")
    for basis in geometry.v_basis:
        diff = sub(geometry.project_u12_given_3(geometry.project_u2_given_13(basis)), geometry.project_u2_given_13(basis))
        if norm(diff) > 1.0e-9:
            raise AssertionError("U2 was not nested in U12")


def assert_score_math() -> None:
    geometry = synthetic_geometry()
    row = unit(add(scale(2.0, geometry.v_basis[10]), geometry.v_basis[18])) or []
    rows = [row, row, row]
    score = score_rows(rows, geometry)
    c2 = float(score["C2"])
    c12 = float(score["C12"])
    camb = float(score["Camb"])
    if abs(c12 - (c2 + camb)) > 1.0e-9:
        raise AssertionError("C12 split drifted")
    if abs(float(score["F_obs"]) - c2 / c12) > 1.0e-9:
        raise AssertionError("F_obs calculation drifted")
    if abs(float(score["a2"]) - c2 / 8.0) > 1.0e-9:
        raise AssertionError("a2 calculation drifted")
    if abs(float(score["a_amb"]) - camb / 4.0) > 1.0e-9:
        raise AssertionError("a_amb calculation drifted")


def assert_conserved_energy_math() -> None:
    geometry = synthetic_geometry()
    row = unit(geometry.v_basis[10]) or []
    rows = [row, row, row]
    c2 = conserved_energy(rows, geometry.project_u2_given_13)
    if abs(c2 - 1.0) > 1.0e-9:
        raise AssertionError(f"conserved-energy calculation drifted: {c2}")


def assert_permutation_null_logic() -> None:
    code = {"0": "X", "1": "X", "2": "X", "3": "X", "4": "Y", "5": "Y", "6": "Y", "7": "Y"}
    codons = list(code)
    geometry = object.__new__(Geometry)
    geometry.code = code
    geometry.codons = codons
    geometry.families = families_by_aa(code, codons)
    standard = []
    for index in range(len(codons)):
        e = [0.0 for _ in codons]
        e[index] = 1.0
        standard.append(e)
    geometry.aa_basis = []
    geometry.w_basis = standard
    geometry.basic_control_basis = []
    geometry.q0w_basis = standard
    geometry.l1_basis = []
    geometry.l2_basis = standard[:4]
    geometry.l3_basis = standard[4:]
    geometry.v_basis = standard
    geometry.l13_basis = standard[4:]
    geometry.l23_basis = standard
    geometry.rank_u1_given_23 = 0
    geometry.rank_u12_given_3 = 4
    geometry.rank_u2_given_13 = 4
    geometry.rank_uamb = 0
    rows = [unit([1.0, -1.0, 0.5, -0.5, 0.25, -0.25, 0.75, -0.75]) or [] for _ in range(3)]
    rng = random.Random(17)
    permuted, signature = permuted_rows(rows, geometry, rng)
    if not signature:
        raise AssertionError("permutation signature missing")
    for row in permuted:
        if abs(norm(row) - 1.0) > 1.0e-9:
            raise AssertionError("permuted row was not normalized")


def selftest() -> None:
    geometry = synthetic_geometry()
    names, planted_rows = synthetic_rows(geometry, u2_weight=1.0, uamb_weight=0.01, noise_scale=0.001, material="planted")
    planted_score = score_rows(planted_rows, geometry)
    planted_verdict = verdict_without_real_null(geometry, names, planted_rows, 0.005, 0.005)
    iso_names, iso_rows = synthetic_rows(geometry, u2_weight=1.0, uamb_weight=0.7, noise_scale=0.02, material="isotropic")
    iso_verdict = verdict_without_real_null(geometry, iso_names, iso_rows, 0.25, 0.25)
    amb_names, amb_rows = synthetic_rows(geometry, u2_weight=0.01, uamb_weight=1.0, noise_scale=0.001, material="amb")
    amb_verdict = verdict_without_real_null(geometry, amb_names, amb_rows, 0.005, 0.005)
    deg = degenerate_geometry()
    deg_names, deg_rows = synthetic_rows(deg, u2_weight=1.0, uamb_weight=0.0, noise_scale=0.0, material="deg")
    deg_verdict = verdict_without_real_null(deg, deg_names, deg_rows, 0.005, 0.005)
    weak_verdict = verdict_without_real_null(geometry, names, planted_rows, 0.05, 0.05)
    gate_verdict = verdict_without_real_null(geometry, names, planted_rows, 0.005, 0.005, force_preflight="data_gate_failed")
    assert_projector_math()
    assert_score_math()
    assert_conserved_energy_math()
    assert_permutation_null_logic()
    if planted_verdict != "certified_E2_unique_low_order" or float(planted_score["F_obs"]) <= 0.8:
        raise AssertionError(f"planted E2-unique synthetic did not certify: {planted_verdict}, {planted_score}")
    if iso_verdict != "coincidence_mixed_low_order":
        raise AssertionError(f"isotropic low-order synthetic did not land as coincidence: {iso_verdict}")
    if amb_verdict != "refuted":
        raise AssertionError(f"ambiguous-residue synthetic did not refute: {amb_verdict}")
    if deg_verdict != "needs_derivation":
        raise AssertionError(f"degenerate synthetic did not refuse: {deg_verdict}")
    if weak_verdict != "needs_more_organisms":
        raise AssertionError(f"directional weak-null synthetic did not request more organisms: {weak_verdict}")
    if gate_verdict != "data_gate_failed":
        raise AssertionError(f"gate failure verdict missing: {gate_verdict}")
    print(
        json.dumps(
            {
                "ok": True,
                "verdicts": {
                    "planted_E2_unique": planted_verdict,
                    "isotropic_low_order": iso_verdict,
                    "ambiguous_residue": amb_verdict,
                    "degenerate": deg_verdict,
                    "directional_weak_null": weak_verdict,
                    "gate_failed": gate_verdict,
                },
                "planted_score": planted_score,
                "selftest_null_reps_supported": SELFTEST_NULL_REPS,
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
    status = "passed" if verdict == "certified_E2_unique_low_order" else ("failed" if verdict in {"refuted", "coincidence_mixed_low_order", "data_gate_failed"} else verdict)
    emit(status, result=result)


if __name__ == "__main__":
    main()

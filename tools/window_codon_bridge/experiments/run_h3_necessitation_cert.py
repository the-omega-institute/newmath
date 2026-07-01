#!/usr/bin/env python3
"""Held-out controlled-H3 localization test for B*_Q6 d_resid4."""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
import pathlib
import random
import sys


EXPERIMENT_ID = "h3_necessitation_cert"
CLAIM_ID = "bridge.genetic_code.h3_necessitation_cert"

BASES = ("A", "C", "G", "U")
CHEMICAL_CHARACTERS = {
    "R": {"A": 1.0, "G": 1.0, "C": -1.0, "U": -1.0},
    "W": {"A": 1.0, "U": 1.0, "G": -1.0, "C": -1.0},
    "K": {"G": 1.0, "U": 1.0, "A": -1.0, "C": -1.0},
}
CHARACTER_ORDER = ("1", "R", "W", "K")
LAMBDA_BY_LEVEL = (9, 5, 1, -3)
EXPECTED_DIMS = (1, 9, 27, 27)
MIN_ORGANISMS = 6
DEFAULT_NULL_REPS = 1000
SELFTEST_NULL_REPS = 80
EPS = 1.0e-12
MGS_TOL = 1.0e-10
MARGIN = 0.02
ALPHA = 0.05
TRNA_ORGANISM = {
    "escherichia_coli_k12_mg1655": "escherichia_coli",
}

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}


def repo_root() -> pathlib.Path:
    return pathlib.Path(__file__).resolve().parents[3]


BIO_EXPERIMENT_DIR = repo_root() / "tools" / "bio_reality" / "experiments"
if str(BIO_EXPERIMENT_DIR) not in sys.path:
    sys.path.insert(0, str(BIO_EXPERIMENT_DIR))

from run_b_star_q6_f3_stress_cross_organism_powered import vector_dot  # noqa: E402
from run_b_star_q6_f3_stress_strength_driver_powered import synonymous_contrast_columns  # noqa: E402
from run_b_star_q6_organism_specificity_meta_powered import ORGANISMS  # noqa: E402
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_optimality_axis_sufficiency_powered import orthonormal_basis, usage_frequency_axis  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import matrix_column, residualize, standard_amino_acids  # noqa: E402
from run_b_star_q6_third_axis_identity_powered import contrast_direction_from_codon_values  # noqa: E402
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM  # noqa: E402
from run_b_star_q6_translation_survival_powered import fibers_for, project_syn, q_vectors, standard_code  # noqa: E402
from run_b_star_q6_universal_core_is_trna_adaptation_powered import codon_w_values, load_trna_records, trna_contrast_direction  # noqa: E402
from run_b_star_q6_universal_optimal_residual_axis_powered import fit_optimal_direction, load_json, organism_rows, unit_vector, vector_norm  # noqa: E402
from run_b_star_q6_universal_optimal_two_axis_closure_powered import residual_after_basis  # noqa: E402


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def stable_seed(*parts: object) -> int:
    material = "|".join(str(part) for part in parts)
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:16], "big")


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def median(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def percentile(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm2(vector: list[float]) -> float:
    return dot(vector, vector)


def norm(vector: list[float]) -> float:
    return math.sqrt(norm2(vector))


def cosine(left: list[float], right: list[float]) -> float:
    denom = norm(left) * norm(right)
    if denom <= EPS:
        return 0.0
    return dot(left, right) / denom


def add_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] + right[index] for index in range(len(left))]


def scale_vector(scale: float, vector: list[float]) -> list[float]:
    return [scale * value for value in vector]


def modified_gram_schmidt(columns: list[list[float]], tol: float = MGS_TOL) -> list[list[float]]:
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


def project_onto_basis(vector: list[float], basis: list[list[float]]) -> list[float]:
    projected = [0.0 for _ in vector]
    for q in basis:
        coeff = dot(vector, q)
        if coeff:
            for index, value in enumerate(q):
                projected[index] += coeff * value
    return projected


def residualize_vector(vector: list[float], basis: list[list[float]]) -> list[float]:
    projected = project_onto_basis(vector, basis)
    return [vector[index] - projected[index] for index in range(len(vector))]


def residualize_columns(columns: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    return [residualize_vector(column, basis) for column in columns]


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def sense_codon_order() -> list[str]:
    return [codon for codon in codon_order() if CODON_TO_AA[codon] != "*"]


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


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


def hamming_adjacency_apply(vector: list[float], codons: list[str], index: dict[str, int]) -> list[float]:
    out: list[float] = []
    for codon in codons:
        total = 0.0
        for pos in range(3):
            for base in BASES:
                if base != codon[pos]:
                    neighbor = codon[:pos] + base + codon[pos + 1 :]
                    total += vector[index[neighbor]]
        out.append(total)
    return out


def structural_checks() -> dict[str, object]:
    codons = codon_order()
    index = {codon: pos for pos, codon in enumerate(codons)}
    columns = eigenspace_columns(codons)
    ranks = [len(modified_gram_schmidt(columns[level])) for level in range(4)]
    eigen_ok = True
    max_defect = 0.0
    for level in range(4):
        eigenvalue = LAMBDA_BY_LEVEL[level]
        for column in columns[level]:
            applied = hamming_adjacency_apply(column, codons, index)
            defect = max(abs(applied[pos] - eigenvalue * column[pos]) for pos in range(len(codons)))
            max_defect = max(max_defect, defect)
            if defect > 1.0e-9:
                eigen_ok = False
    return {
        "level_dimensions": ranks,
        "expected_dimensions": list(EXPECTED_DIMS),
        "dimensions_ok": ranks == list(EXPECTED_DIMS),
        "krawtchouk_eigenvalues": list(LAMBDA_BY_LEVEL),
        "e3_eigenvalue": LAMBDA_BY_LEVEL[3],
        "eigen_equations_ok": eigen_ok,
        "max_eigen_defect": max_defect,
    }


def contrast_to_codon_vector(
    direction: list[float],
    codons: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
) -> list[float]:
    loadings = {codon: 0.0 for codon in codons}
    for coefficient, column in zip(direction, syn_columns):
        positive = str(column["positive_codon"])
        negative = str(column["negative_codon"])
        loadings[positive] += coefficient
        loadings[negative] -= coefficient
    projected = project_syn(loadings, fibers)
    return [projected[codon] for codon in codons]


def codon_to_contrast_vector(
    values: list[float],
    codons: list[str],
    syn_columns: list[dict[str, object]],
) -> list[float]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    return [values[index[str(column["positive_codon"])]] - values[index[str(column["negative_codon"])]] for column in syn_columns]


def codon_columns_to_contrast(
    columns: list[list[float]],
    codons: list[str],
    syn_columns: list[dict[str, object]],
) -> list[list[float]]:
    return [codon_to_contrast_vector(column, codons, syn_columns) for column in columns]


def matrix_rank(columns: list[list[float]]) -> int:
    return len(modified_gram_schmidt(columns))


def random_gaussian_vector(dim: int, rng: random.Random) -> list[float]:
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


def random_rank_basis(dim: int, rank: int, material: str) -> list[list[float]]:
    rng = random.Random(stable_seed(EXPERIMENT_ID, material))
    return modified_gram_schmidt([random_gaussian_vector(dim, rng) for _ in range(rank)])


def deterministic_permutation(items: list[str], material: str) -> list[str]:
    rng = random.Random(stable_seed(EXPERIMENT_ID, material))
    out = list(items)
    rng.shuffle(out)
    return out


def permute_within_families(
    vector: list[float],
    codons: list[str],
    families: dict[str, list[str]],
    material: str,
    *,
    preserve_box_wobble: bool,
) -> list[float]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    out = list(vector)
    for aa, family in sorted(families.items()):
        if aa == "*" or len(family) < 2:
            continue
        groups: dict[object, list[str]] = defaultdict(list)
        for codon in family:
            key: object = (codon[:2], codon[2] in {"A", "G"}) if preserve_box_wobble else "all"
            groups[key].append(codon)
        for key, group in sorted(groups.items(), key=lambda item: str(item[0])):
            if len(group) < 2:
                continue
            shuffled = deterministic_permutation(sorted(group), f"{material}|{aa}|{key}")
            source_values = [vector[index[codon]] for codon in sorted(group)]
            for codon, value in zip(shuffled, source_values):
                out[index[codon]] = value
    return out


def low_order_basis(
    codons: list[str],
    syn_columns: list[dict[str, object]],
    controls: list[list[float]],
    target_rank: int,
) -> list[list[float]]:
    columns_by_level = eigenspace_columns(codons)
    columns = codon_columns_to_contrast(columns_by_level[1] + columns_by_level[2], codons, syn_columns)
    residualized = residualize_columns(columns, modified_gram_schmidt(controls))
    return modified_gram_schmidt(residualized)[:target_rank]


def controlled_h3_basis(
    codons: list[str],
    syn_columns: list[dict[str, object]],
    controls: list[list[float]],
) -> tuple[list[list[float]], dict[str, object]]:
    h3_columns = codon_columns_to_contrast(eigenspace_columns(codons)[3], codons, syn_columns)
    raw_rank = matrix_rank(h3_columns)
    control_basis = modified_gram_schmidt(controls)
    residualized = residualize_columns(h3_columns, control_basis)
    basis = modified_gram_schmidt(residualized)
    return basis, {
        "raw_E3_restricted_rank": raw_rank,
        "control_rank": len(control_basis),
        "controlled_H3_rank": len(basis),
        "ambient_synonymous_contrast_rank": len(syn_columns),
        "expected_random_squared_projection": None if not syn_columns else len(basis) / len(syn_columns),
        "trap_note": "A random vector already projects by rank/ambient dimension; held-out cosine and null beating are required.",
    }


def vector_summary(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "p95": percentile(values, 0.95) if values else None,
    }


def heldout_cosines(directions: dict[str, list[float]], projection_basis: list[list[float]]) -> dict[str, object]:
    per_org: dict[str, float] = {}
    names = sorted(directions)
    for name in names:
        others = [directions[other] for other in names if other != name]
        if not others:
            per_org[name] = 0.0
            continue
        avg = [sum(vector[index] for vector in others) / len(others) for index in range(len(others[0]))]
        predicted = project_onto_basis(avg, projection_basis)
        per_org[name] = cosine(predicted, directions[name])
    values = [per_org[name] for name in names]
    return {"per_organism": per_org, "values": values, "mean": mean(values), "median": median(values)}


def null_summary(observed: float, values: list[float]) -> dict[str, object]:
    p_upper = (sum(value >= observed for value in values) + 1) / (len(values) + 1) if values else 1.0
    null_mean = mean(values)
    return {
        **vector_summary(values),
        "p_upper": p_upper,
        "excess_over_null_mean": observed - null_mean,
        "beats_with_margin": observed >= null_mean + MARGIN,
        "significant": p_upper <= ALPHA,
    }


def verdict_for(observed: float, nulls: dict[str, dict[str, object]], n_organisms: int, heldout_values: list[float]) -> str:
    if n_organisms < MIN_ORGANISMS:
        return "needs_more_organisms"
    if len(heldout_values) >= 2:
        avg = mean(heldout_values)
        sd = math.sqrt(sum((value - avg) ** 2 for value in heldout_values) / (len(heldout_values) - 1))
        if sd > max(0.35, 2.5 * abs(avg)):
            return "needs_more_organisms"
    gates = [
        bool(row.get("beats_with_margin")) and bool(row.get("significant")) and observed > float(row.get("mean", 0.0))
        for row in nulls.values()
    ]
    return "passed" if all(gates) else "failed"


def build_controls(
    *,
    codons: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
    organism_axes: dict[str, dict[str, list[float]]],
) -> list[list[float]]:
    controls: list[list[float]] = []
    controls.append(contrast_direction_from_codon_values({codon: 1.0 if codon[2] in {"G", "C"} else 0.0 for codon in codons}, syn_columns) or [0.0 for _ in syn_columns])
    controls.append(f3_direction)
    q_support = {codon for vector in q_vectors(codons).values() for codon, value in vector.items() if abs(value) > 0.0}
    controls.append(contrast_direction_from_codon_values({codon: 1.0 if codon in q_support else 0.0 for codon in codons}, syn_columns) or [0.0 for _ in syn_columns])
    for axes in organism_axes.values():
        controls.append(axes["d_tRNA"])
        controls.append(axes["d_usage"])
    return controls


def load_organism_direction(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
) -> dict[str, object]:
    cds_path = repo / "tools" / "fibonacci_reality" / "data" / f"cds_codon_abundance_{organism}.json"
    if not cds_path.exists():
        cds_path = repo / "tools" / "bio_reality" / "data" / f"cds_codon_abundance_{organism}.json"
    if not cds_path.exists():
        return {"organism": organism, "status": "needs_data", "reason": "missing cds_codon_abundance"}
    trna_organism = TRNA_ORGANISM.get(organism, organism)
    trna_path = repo / "tools" / "bio_reality" / "data" / f"gtrnadb_trna_all_copy_{trna_organism}.json"
    trna_summary_path = repo / "tools" / "bio_reality" / "data" / f"trna_gene_copy_{trna_organism}.json"
    if not trna_path.exists() and not trna_summary_path.exists():
        return {"organism": organism, "status": "needs_data", "reason": "missing tRNA payload for d_tRNA"}
    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "CDS payload is not an object"}
    syn_raw, y_raw, controls, gc3, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    if len(y_raw) < MIN_PROTEINS_PER_ORGANISM:
        return {"organism": organism, "status": "needs_data", "reason": "join below gate", "n_join": len(y_raw), "data_summary": data_summary}
    trna_records, trna_source_summary = load_trna_records(repo, trna_organism)
    weights, _raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    usage_direction, usage_summary = usage_frequency_axis(
        payload=payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    if trna_direction is None or usage_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "known axis unavailable", "n_join": len(y_raw)}
    three_axis_basis, basis_summary = orthonormal_basis(
        [("d_tRNA", trna_direction), ("d_f3", f3_direction), ("d_usage", usage_direction)]
    )
    if three_axis_basis is None:
        return {"organism": organism, "status": "needs_data", "reason": "known-axis basis collapsed", "n_join": len(y_raw)}
    syn_residualized, rank_controls_syn = residualize(syn_raw, controls)
    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y = matrix_column(y_residualized, 0)
    if vector_dot(y, y) <= EPS:
        return {"organism": organism, "status": "needs_data", "reason": "zero abundance residual", "n_join": len(y_raw)}
    optimal_direction, fit_summary = fit_optimal_direction(syn_residualized, y)
    if optimal_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "d_opt unavailable", "fit_summary": fit_summary, "n_join": len(y_raw)}
    d_resid4, captured_fraction, coefficients = residual_after_basis(optimal_direction, three_axis_basis)
    if d_resid4 is None:
        return {"organism": organism, "status": "needs_data", "reason": "d_resid4 collapsed", "n_join": len(y_raw)}
    return {
        "organism": organism,
        "status": "computed",
        "n_join": len(y_raw),
        "trna_organism": trna_organism,
        "gc3": gc3,
        "d_resid4": d_resid4,
        "axes": {"d_tRNA": trna_direction, "d_f3": f3_direction, "d_usage": usage_direction},
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "captured_fraction_span_tRNA_f3_usage": captured_fraction,
        "known_axis_projection_coefficients": coefficients,
        "known_axis_basis_summary": basis_summary,
        "data_summary": data_summary,
        "usage_axis_summary": usage_summary,
        "trna_source_summary": trna_source_summary,
        "tai_weight_summary": tai_summary,
    }


def run_certificate(null_reps: int) -> dict[str, object]:
    repo = repo_root()
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    aa_order = standard_amino_acids(code, codons)
    fibers = fibers_for(code, codons)
    syn_columns = synonymous_contrast_columns(fibers=fibers)
    f3_projected = project_syn(q_vectors(codons)["f3_stress"], fibers)
    f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
    if f3_direction is None:
        raise RuntimeError("could not build f3 direction")
    rows = [
        load_organism_direction(
            repo=repo,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            fibers=fibers,
            syn_columns=syn_columns,
            f3_direction=f3_direction,
        )
        for organism in ORGANISMS
    ]
    computed = [row for row in rows if row.get("status") == "computed" and isinstance(row.get("d_resid4"), list)]
    directions = {str(row["organism"]): row["d_resid4"] for row in computed}  # type: ignore[dict-item]
    organism_axes = {str(row["organism"]): row["axes"] for row in computed if isinstance(row.get("axes"), dict)}  # type: ignore[dict-item]
    controls = build_controls(codons=codons, fibers=fibers, syn_columns=syn_columns, f3_direction=f3_direction, organism_axes=organism_axes)
    h3_basis, h3_diag = controlled_h3_basis(codons, syn_columns, controls)
    controlled_directions = {name: residualize_vector(vector, modified_gram_schmidt(controls)) for name, vector in directions.items()}
    observed = heldout_cosines(controlled_directions, h3_basis)
    observed_mean = float(observed["mean"])
    rank = len(h3_basis)
    ambient = len(syn_columns)
    null_values: dict[str, list[float]] = {name: [] for name in ["N1_random_rank", "N2_within_aa_permutation", "N3_box_wobble_preserving_shuffle", "N4_E1_E2_low_order", "N5_known_axis_residual_baseline"]}
    low_basis = low_order_basis(codons, syn_columns, controls, rank)
    control_basis = modified_gram_schmidt(controls)
    known_axis_basis = modified_gram_schmidt([axis for axes in organism_axes.values() for axis in axes.values()])
    names = sorted(controlled_directions)
    for rep in range(null_reps):
        null_values["N1_random_rank"].append(float(heldout_cosines(controlled_directions, random_rank_basis(ambient, rank, f"N1|{rep}"))["mean"]))
        for null_name, preserve in [("N2_within_aa_permutation", False), ("N3_box_wobble_preserving_shuffle", True)]:
            permuted: dict[str, list[float]] = {}
            for name in names:
                codon_vec = contrast_to_codon_vector(directions[name], codons, fibers, syn_columns)
                shuffled = permute_within_families(codon_vec, codons, fibers, f"{null_name}|{name}|{rep}", preserve_box_wobble=preserve)
                permuted[name] = residualize_vector(codon_to_contrast_vector(shuffled, codons, syn_columns), control_basis)
            null_values[null_name].append(float(heldout_cosines(permuted, h3_basis)["mean"]))
        null_values["N4_E1_E2_low_order"].append(float(heldout_cosines(controlled_directions, low_basis)["mean"]))
        null_values["N5_known_axis_residual_baseline"].append(float(heldout_cosines(controlled_directions, known_axis_basis)["mean"]))
    nulls = {name: null_summary(observed_mean, values) for name, values in null_values.items()}
    final_verdict = verdict_for(observed_mean, nulls, len(computed), observed["values"])  # type: ignore[arg-type]
    return {
        "verdict": final_verdict,
        "n_organisms": len(computed),
        "organisms": sorted(directions),
        "skipped": [row for row in rows if row.get("status") != "computed"],
        "structural_checks": structural_checks(),
        "h3_diagnostics": h3_diag,
        "known_control_rank": len(control_basis),
        "random_projection_trap": {
            "ambient_rank": ambient,
            "controlled_H3_rank": rank,
            "expected_random_squared_projection_rank_over_ambient": None if ambient == 0 else rank / ambient,
            "warning": "Projection fraction alone is not evidence; this script gates on held-out cross-organism cosine against null distributions.",
        },
        "observed_heldout": observed,
        "nulls": nulls,
        "null_distributions": null_values,
        "per_organism_diagnostics": [
            {
                "organism": row["organism"],
                "n_join": row["n_join"],
                "gc3": row["gc3"],
                "captured_fraction_span_tRNA_f3_usage": row["captured_fraction_span_tRNA_f3_usage"],
                "rank_controls_syn": row["rank_controls_syn"],
                "rank_controls_y": row["rank_controls_y"],
            }
            for row in computed
        ],
        "reuse_path": "Route-S d_resid4 helpers imported by sys.path; H3/null code local to this script.",
    }


def synthetic_panel(in_h3: bool, reps: int) -> tuple[str, dict[str, object]]:
    dim = 41
    controls: list[list[float]] = []
    basis_seed = random_rank_basis(dim, 26, "selftest-h3-basis")
    rng = random.Random(stable_seed(EXPERIMENT_ID, "selftest", in_h3))
    signal = random_gaussian_vector(dim, rng)
    signal = project_onto_basis(signal, basis_seed) if in_h3 else residualize_vector(signal, basis_seed)
    signal_unit = unit_vector(signal) or signal
    directions: dict[str, list[float]] = {}
    for idx in range(8):
        noise = random_gaussian_vector(dim, random.Random(stable_seed(EXPERIMENT_ID, "noise", in_h3, idx)))
        noise = scale_vector(0.05 if in_h3 else 1.0, unit_vector(noise) or noise)
        vector = add_vectors(signal_unit if in_h3 else scale_vector(0.05, signal_unit), noise)
        directions[f"org_{idx}"] = unit_vector(vector) or vector
    observed = heldout_cosines(directions, basis_seed)
    observed_mean = float(observed["mean"])
    null_values = [float(heldout_cosines(directions, random_rank_basis(dim, len(basis_seed), f"selftest-null|{in_h3}|{rep}"))["mean"]) for rep in range(reps)]
    nulls = {"N1_random_rank": null_summary(observed_mean, null_values)}
    verdict = verdict_for(observed_mean, nulls, len(directions), observed["values"])  # type: ignore[arg-type]
    return verdict, {"observed": observed, "null": nulls["N1_random_rank"]}


def synthetic_small_panel() -> str:
    basis = random_rank_basis(41, 26, "selftest-small-h3-basis")
    directions = {
        f"small_{idx}": basis[idx][:]
        for idx in range(3)
    }
    observed = heldout_cosines(directions, basis)
    nulls = {"N1_random_rank": {"mean": -1.0, "beats_with_margin": True, "significant": True}}
    return verdict_for(float(observed["mean"]), nulls, len(directions), observed["values"])  # type: ignore[arg-type]


def selftest() -> None:
    structural = structural_checks()
    if not structural["dimensions_ok"] or not structural["eigen_equations_ok"] or structural["e3_eigenvalue"] != -3:
        raise AssertionError("H3 structural checks failed")
    planted_verdict, planted = synthetic_panel(True, SELFTEST_NULL_REPS)
    random_verdict, random_case = synthetic_panel(False, SELFTEST_NULL_REPS)
    small_verdict = synthetic_small_panel()
    if planted_verdict != "passed":
        raise AssertionError(f"planted H3 synthetic panel did not pass: {planted_verdict}")
    if random_verdict == "passed":
        raise AssertionError("random synthetic panel passed against N1")
    if small_verdict != "needs_more_organisms":
        raise AssertionError(f"small synthetic panel did not exercise needs_more_organisms: {small_verdict}")
    print(json.dumps({"ok": True, "structural": structural, "synthetic_planted": planted, "synthetic_random": random_case, "verdicts": {"planted": planted_verdict, "random": random_verdict, "small": small_verdict}}, sort_keys=False))


def main() -> None:
    if "--selftest" in sys.argv:
        selftest()
        return
    null_reps = DEFAULT_NULL_REPS
    for arg in sys.argv[1:]:
        if arg.startswith("--null-reps="):
            null_reps = int(arg.split("=", 1)[1])
    result = run_certificate(null_reps)
    status = "passed" if result["verdict"] == "passed" else ("failed" if result["verdict"] == "failed" else "needs_more_organisms")
    emit(status, result=result)


if __name__ == "__main__":
    main()

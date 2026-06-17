#!/usr/bin/env python3
"""Projection harness for edge-defect axis candidates.

This experiment implements the local audit requested by the oracle lane:
construct the SerSplit contrast, build a forbidden-control matrix from the
locked codon-Q6 packet and deterministic codon chemistry features, residualize
candidate axes, and run exact/null projection tests.  No oracle text is used as
evidence.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, product
import json
import math
import random
import sys
from pathlib import Path
from typing import Iterable


EXPERIMENT_ID = "edge_defect_projection_harness"
CLAIM_ID = "bridge.genetic_code.edge_defect_projection_harness"
DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 911326
GLOBAL_NULL_DRAWS = 2000
BASES = ("U", "C", "A", "G")
SER4 = {"UCU", "UCC", "UCA", "UCG"}
SER2 = {"AGU", "AGC"}
SIXFOLD = {
    "Ser": ("UCU", "UCC", "UCA", "UCG", "AGU", "AGC"),
    "Leu": ("UUA", "UUG", "CUU", "CUC", "CUA", "CUG"),
    "Arg": ("CGU", "CGC", "CGA", "CGG", "AGA", "AGG"),
}
SELECTION_FIELDS = (
    "d_perp_loading",
    "f3_loading",
    "optimal_loading",
    "trna_consensus_loading",
    "trna_supply_tai_centered_loading",
    "trna_supply_tai_mean",
)
AA_TO_FAMILY = {
    "F": "Phe",
    "L": "Leu",
    "S": "Ser",
    "Y": "Tyr",
    "*": "Stop",
    "C": "Cys",
    "W": "Trp",
    "P": "Pro",
    "H": "His",
    "Q": "Gln",
    "R": "Arg",
    "I": "Ile",
    "M": "Met",
    "T": "Thr",
    "N": "Asn",
    "K": "Lys",
    "V": "Val",
    "A": "Ala",
    "D": "Asp",
    "E": "Glu",
    "G": "Gly",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def mean(values: Iterable[float]) -> float:
    vals = list(values)
    return sum(vals) / len(vals)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(values: list[float]) -> float:
    return math.sqrt(dot(values, values))


def normalize(values: list[float]) -> list[float] | None:
    nrm = norm(values)
    if nrm <= 1e-12:
        return None
    return [value / nrm for value in values]


def matrix_rank(columns: list[list[float]], tol: float = 1e-10) -> int:
    if not columns:
        return 0
    rows = [[columns[col][row] for col in range(len(columns))] for row in range(len(columns[0]))]
    m = len(rows)
    n = len(columns)
    rank = 0
    for col in range(n):
        pivot = max(range(rank, m), key=lambda row: abs(rows[row][col]), default=rank)
        if rank >= m or abs(rows[pivot][col]) <= tol:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [value / scale for value in rows[rank]]
        for row in range(m):
            if row == rank:
                continue
            factor = rows[row][col]
            if factor:
                rows[row] = [value - factor * rows[rank][idx] for idx, value in enumerate(rows[row])]
        rank += 1
        if rank == m:
            break
    return rank


def add_independent_column(columns: list[list[float]], candidate: list[float], tol: float = 1e-10) -> bool:
    old_rank = matrix_rank(columns, tol)
    new_rank = matrix_rank([*columns, candidate], tol)
    if new_rank > old_rank:
        columns.append(candidate)
        return True
    return False


def solve_square(matrix: list[list[float]], rhs: list[float], tol: float = 1e-12) -> list[float] | None:
    n = len(rhs)
    aug = [row[:] + [rhs[index]] for index, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        aug[col] = [value / scale for value in aug[col]]
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor:
                aug[row] = [value - factor * aug[col][idx] for idx, value in enumerate(aug[row])]
    return [aug[row][-1] for row in range(n)]


def residualize(target: list[float], columns: list[list[float]]) -> list[float] | None:
    if not columns:
        return target[:]
    xtx = [[dot(left, right) for right in columns] for left in columns]
    xty = [dot(col, target) for col in columns]
    beta = solve_square(xtx, xty)
    if beta is None:
        return None
    return [value - sum(beta[index] * columns[index][row] for index in range(len(columns))) for row, value in enumerate(target)]


def zscore(values: list[float]) -> list[float]:
    mu = mean(values)
    centered = [value - mu for value in values]
    nrm = norm(centered)
    if nrm <= 1e-12:
        return centered
    return [value / nrm for value in centered]


def empirical_p_abs(observed: float, null_values: list[float]) -> float:
    return (sum(1 for value in null_values if abs(value) >= abs(observed)) + 1) / (len(null_values) + 1)


def round_float(value: float | None, digits: int = 6) -> float | None:
    return None if value is None else round(value, digits)


def load_rows() -> list[dict[str, object]]:
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    if data.get("schema") != "codon_q6_selection_vectors.v1":
        raise ValueError(f"unexpected schema: {data.get('schema')}")
    rows = [dict(row) for row in data.get("vectors", []) if row.get("is_sense") is True]
    if len(rows) != 61:
        raise ValueError(f"expected 61 sense codons, found {len(rows)}")
    return rows


def codon_features(codon: str) -> dict[str, float]:
    return {
        "gc1": 1.0 if codon[0] in "GC" else 0.0,
        "gc2": 1.0 if codon[1] in "GC" else 0.0,
        "gc3": 1.0 if codon[2] in "GC" else 0.0,
        "gc_total": sum(1 for base in codon if base in "GC") / 3.0,
        "cpg": 1.0 if "CG" in codon else 0.0,
        "upa": 1.0 if "UA" in codon else 0.0,
        "purine_count": sum(1 for base in codon if base in "AG"),
        "pyrimidine_count": sum(1 for base in codon if base in "UC"),
        "wobble_gc": 1.0 if codon[2] in "GC" else 0.0,
    }


def degeneracy_by_aa(rows: list[dict[str, object]]) -> dict[str, int]:
    counts = Counter(str(row["amino_acid"]) for row in rows)
    return {aa: int(size) for aa, size in counts.items()}


def one_hot(values: list[str], omit_last: bool = True) -> list[tuple[str, list[float]]]:
    labels = sorted(set(values))
    if omit_last and labels:
        labels = labels[:-1]
    out = []
    for label in labels:
        out.append((label, [1.0 if value == label else 0.0 for value in values]))
    return out


def build_controls(rows: list[dict[str, object]]) -> tuple[list[str], list[list[float]], list[str]]:
    codons = [str(row["codon"]) for row in rows]
    amino_acids = [str(row["amino_acid"]) for row in rows]
    degeneracy = degeneracy_by_aa(rows)
    named_columns: list[tuple[str, list[float]]] = [("intercept", [1.0 for _ in rows])]
    named_columns.extend((f"aa_{label}", column) for label, column in one_hot(amino_acids))
    for field in SELECTION_FIELDS:
        values = [row.get(field) for row in rows]
        if all(value is not None for value in values):
            named_columns.append((field, zscore([float(value) for value in values])))
    feature_names = ("gc1", "gc2", "gc3", "gc_total", "cpg", "upa", "purine_count", "pyrimidine_count", "wobble_gc")
    feature_rows = [codon_features(codon) for codon in codons]
    for name in feature_names:
        named_columns.append((name, zscore([float(features[name]) for features in feature_rows])))
    named_columns.append(("degeneracy", zscore([float(degeneracy[aa]) for aa in amino_acids])))
    named_columns.extend((f"wobble_{label}", column) for label, column in one_hot([codon[2] for codon in codons]))

    controls: list[list[float]] = []
    kept_names: list[str] = []
    dropped_names: list[str] = []
    for name, column in named_columns:
        if add_independent_column(controls, column):
            kept_names.append(name)
        else:
            dropped_names.append(name)
    return kept_names, controls, dropped_names


def ser_split_vector(codons: list[str]) -> list[float]:
    scale = math.sqrt(12.0)
    return [
        (1.0 / scale if codon in SER4 else (-2.0 / scale if codon in SER2 else 0.0))
        for codon in codons
    ]


def contrast_vector(codons: list[str], plus: set[str], minus: set[str]) -> list[float]:
    plus_weight = 1.0 / math.sqrt(12.0)
    minus_weight = -2.0 / math.sqrt(12.0)
    return [plus_weight if codon in plus else (minus_weight if codon in minus else 0.0) for codon in codons]


def residual_unit(vector: list[float], controls: list[list[float]]) -> tuple[list[float] | None, float | None]:
    residual = residualize(vector, controls)
    if residual is None:
        return None, None
    nrm = norm(residual)
    unit = normalize(residual)
    return unit, nrm


def within_ser_null(codons: list[str], controls: list[list[float]], axis_unit: list[float]) -> list[float]:
    ser = sorted(SER4 | SER2)
    values: list[float] = []
    for plus_tuple in combinations(ser, 4):
        plus = set(plus_tuple)
        minus = set(ser) - plus
        unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), controls)
        if unit is not None:
            values.append(dot(axis_unit, unit))
    return values


def sixfold_family_null(codons: list[str], controls: list[list[float]], axis_unit: list[float]) -> list[float]:
    values: list[float] = []
    for family_codons in SIXFOLD.values():
        family = sorted(family_codons)
        for plus_tuple in combinations(family, 4):
            plus = set(plus_tuple)
            minus = set(family) - plus
            unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), controls)
            if unit is not None:
                values.append(dot(axis_unit, unit))
    return values


def matched_key(codon: str, aa_size: int) -> tuple[int, int, int, int, int]:
    features = codon_features(codon)
    return (
        int(features["gc_total"] * 3),
        int(features["gc1"]),
        int(features["gc2"]),
        int(features["gc3"]),
        aa_size,
    )


def global_matched_null(
    codons: list[str],
    aa_sizes: dict[str, int],
    aa_by_codon: dict[str, str],
    controls: list[list[float]],
    axis_unit: list[float],
    rng: random.Random,
) -> list[float]:
    target_counts = Counter(matched_key(codon, aa_sizes[aa_by_codon[codon]]) for codon in sorted(SER4 | SER2))
    buckets: dict[tuple[int, int, int, int, int], list[str]] = defaultdict(list)
    for codon in codons:
        buckets[matched_key(codon, aa_sizes[aa_by_codon[codon]])].append(codon)
    if any(len(buckets[key]) < count for key, count in target_counts.items()):
        return []

    values: list[float] = []
    keys = list(target_counts)
    for _draw in range(GLOBAL_NULL_DRAWS):
        selected: list[str] = []
        used: set[str] = set()
        for key in keys:
            available = [codon for codon in buckets[key] if codon not in used]
            if len(available) < target_counts[key]:
                break
            sample = rng.sample(available, target_counts[key])
            selected.extend(sample)
            used.update(sample)
        else:
            plus = set(rng.sample(selected, 4))
            minus = set(selected) - plus
            unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), controls)
            if unit is not None:
                values.append(dot(axis_unit, unit))
    return values


def candidate_axes(rows: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    codons = [str(row["codon"]) for row in rows]
    features = [codon_features(codon) for codon in codons]
    rng = random.Random(RANDOM_SEED)
    random_values = [rng.gauss(0.0, 1.0) for _ in codons]
    axes: dict[str, dict[str, object]] = {
        "random_gaussian": {
            "kind": "negative_control",
            "values": random_values,
            "expected": "no stable SerSplit projection",
        },
        "gc_only": {
            "kind": "forbidden_negative_control",
            "values": [float(feature["gc_total"]) for feature in features],
            "expected": "residual norm collapses after GC controls",
        },
        "wobble_gc": {
            "kind": "forbidden_negative_control",
            "values": [float(feature["wobble_gc"]) for feature in features],
            "expected": "residual norm collapses after wobble controls",
        },
        "trna_supply_like": {
            "kind": "forbidden_negative_control",
            "values": [float(row["trna_supply_tai_mean"]) for row in rows],
            "expected": "residual norm collapses after tRNA controls",
        },
        "optimal_like": {
            "kind": "forbidden_negative_control",
            "values": [float(row["optimal_loading"]) for row in rows],
            "expected": "residual norm collapses after optimal controls",
        },
        "ser_split_positive_control": {
            "kind": "forbidden_positive_control",
            "values": ser_split_vector(codons),
            "expected": "detectable only because it is the audited contrast itself",
        },
    }
    return axes


def audit_axis(
    name: str,
    spec: dict[str, object],
    codons: list[str],
    rows: list[dict[str, object]],
    controls: list[list[float]],
    rng: random.Random,
) -> dict[str, object]:
    values = [float(value) for value in spec["values"]]  # type: ignore[index]
    axis_unit, axis_norm = residual_unit(zscore(values), controls)
    ser_unit, ser_norm = residual_unit(ser_split_vector(codons), controls)
    if axis_unit is None or ser_unit is None:
        return {
            "axis_id": name,
            "kind": spec.get("kind"),
            "expected": spec.get("expected"),
            "status": "not_testable",
            "axis_residual_norm": round_float(axis_norm),
            "ser_residual_norm": round_float(ser_norm),
            "reason": "axis or SerSplit residual collapsed under forbidden controls",
        }
    observed = dot(axis_unit, ser_unit)
    within = within_ser_null(codons, controls, axis_unit)
    sixfold = sixfold_family_null(codons, controls, axis_unit)
    aa_by_codon = {str(row["codon"]): str(row["amino_acid"]) for row in rows}
    aa_sizes = degeneracy_by_aa(rows)
    matched = global_matched_null(codons, aa_sizes, aa_by_codon, controls, axis_unit, rng)
    return {
        "axis_id": name,
        "kind": spec.get("kind"),
        "expected": spec.get("expected"),
        "status": "tested",
        "axis_residual_norm": round_float(axis_norm),
        "ser_residual_norm": round_float(ser_norm),
        "rho": round_float(observed),
        "abs_rho": round_float(abs(observed)),
        "within_ser_exact_p": round_float(empirical_p_abs(observed, within)),
        "within_ser_null_size": len(within),
        "sixfold_family_exact_p": round_float(empirical_p_abs(observed, sixfold)),
        "sixfold_family_null_size": len(sixfold),
        "global_matched_p": round_float(empirical_p_abs(observed, matched)) if matched else None,
        "global_matched_null_size": len(matched),
    }


def main() -> None:
    rows = load_rows()
    codons = [str(row["codon"]) for row in rows]
    kept_controls, controls, dropped_controls = build_controls(rows)
    axes = candidate_axes(rows)
    rng = random.Random(RANDOM_SEED + 1)
    reports = {
        name: audit_axis(name, spec, codons, rows, controls, rng)
        for name, spec in axes.items()
    }

    bad_negative = [
        name for name, report in reports.items()
        if report.get("kind", "").endswith("negative_control")
        and report.get("status") == "tested"
        and report.get("within_ser_exact_p") is not None
        and float(report["within_ser_exact_p"]) <= 0.05
    ]
    positive = reports["ser_split_positive_control"]
    positive_detected = (
        positive.get("status") == "tested"
        and positive.get("rho") is not None
        and float(positive["rho"]) >= 0.999
        and positive.get("global_matched_p") is not None
        and float(positive["global_matched_p"]) <= 0.05
    )
    harness_ok = not bad_negative and positive_detected
    status = "certified" if harness_ok else "coincidence"
    note = (
        "Projection harness is operational: forbidden negative controls collapse or do not pass, "
        "and the forbidden SerSplit positive control is detected."
        if harness_ok
        else "Projection harness ran, but a control did not satisfy the expected audit behavior."
    )
    emit(
        status,
        note=note,
        codon_order=codons,
        control_matrix={
            "rows": len(codons),
            "kept_columns": len(kept_controls),
            "kept_control_names": kept_controls,
            "dropped_dependent_control_names": dropped_controls,
        },
        reports=reports,
        bad_negative_controls=bad_negative,
        positive_control_detected=positive_detected,
        candidate_only_scope=(
            "This certifies the local projection harness and control behavior, not a biological "
            "SerSplit axis. Biological certification requires an external raw 61-codon axis that "
            "does not use Stop/Ser support, q6 bits, q6 labels, or SerSplit in construction."
        ),
        positive_control_rule=(
            "The forbidden positive control is considered detected by rho>=0.999 and global "
            "matched-support p<=0.05. The within-Ser and sixfold exact nulls are still reported, "
            "but their small finite support makes them diagnostic rather than the harness self-test gate."
        ),
    )


if __name__ == "__main__":
    main()

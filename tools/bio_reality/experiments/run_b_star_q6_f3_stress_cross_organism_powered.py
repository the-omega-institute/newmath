#!/usr/bin/env python3
"""Cross-organism held-out test of B*_Q6 f3_stress against protein abundance."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_b_star_q6_organism_specificity_meta_powered import ORGANISMS
from run_b_star_q6_protein_omics_survival_powered import (
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM
from run_b_star_q6_translation_survival_powered import (
    Q9_FAMILIES,
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_f3_stress_cross_organism_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_stress_cross_organism.b_star_q6_generality_powered"

F3_COORDINATE = "f3_stress"
FOLD_COUNT = 5
PERMUTATION_COUNT = 120
MIN_TESTED_ORGANISMS = 3
SEED = "sha256:b_star_q6_f3_stress_cross_organism_powered:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        swap = stable_int(f"{material}|index={index}|n={n}") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def deterministic_folds(n: int, material: str, fold_count: int) -> list[list[int]]:
    order = deterministic_permutation(n, material)
    folds = [[] for _ in range(fold_count)]
    for position, row_index in enumerate(order):
        folds[position % fold_count].append(row_index)
    return folds


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def cv_r2_single_predictor(x: list[float], y: list[float], folds: list[list[int]]) -> float:
    if len(x) != len(y):
        raise ValueError("predictor and target lengths differ")
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return 0.0
    all_indices = set(range(len(y)))
    sse = 0.0
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        x_train_energy = sum(x[index] * x[index] for index in train_indices)
        if x_train_energy <= EPS:
            slope = 0.0
        else:
            slope = sum(x[index] * y[index] for index in train_indices) / x_train_energy
        for index in test_indices:
            residual = y[index] - slope * x[index]
            sse += residual * residual
    return 1.0 - sse / y_energy


def full_sample_slope(x: list[float], y: list[float]) -> float:
    x_energy = vector_dot(x, x)
    if x_energy <= EPS:
        return 0.0
    return vector_dot(x, y) / x_energy


def controls_for_counts(
    *,
    counts: dict[str, int],
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    total: int,
    cds_len_nt: float,
) -> list[float]:
    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("amino-acid count total must be positive")
    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    return (
        [1.0, math.log(cds_len_nt), math.log(total), gc3]
        + [aa_counts[aa] / aa_total for aa in aa_order]
    )


def organism_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    f3_projected: dict[str, float],
) -> tuple[list[float], list[float], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    x_rows: list[float] = []
    y_rows: list[float] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    f3_norm = math.sqrt(sum(f3_projected[codon] * f3_projected[codon] for codon in codons))
    if f3_norm <= EPS:
        raise ValueError("projected f3_stress vector has zero norm")

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append(sum(frequencies[codon] * f3_projected[codon] for codon in codons) / f3_norm)
        y_rows.append(math.log10(abundance))
        z_rows.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=cds_len_nt,
            )
        )

    return x_rows, y_rows, z_rows, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(x_rows),
        "skipped_records": skipped,
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    f3_projected: dict[str, float],
) -> dict[str, object]:
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    proteomics_path = data_dir / f"proteomics_abundance_{organism}.json"
    if not cds_path.exists() or not proteomics_path.exists():
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance or proteomics_abundance JSON",
            "cds_exists": cds_path.exists(),
            "proteomics_exists": proteomics_path.exists(),
        }

    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "cds payload is not an object"}
    proteomics_payload = load_json(proteomics_path)
    proteomics_n = proteomics_payload.get("n_proteins") if isinstance(proteomics_payload, dict) else None

    x_raw, y_raw, controls, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        f3_projected=f3_projected,
    )
    n_join = len(x_raw)
    base = {
        "organism": organism,
        "status": "needs_data",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "data_summary": data_summary,
    }
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        base["reason"] = f"join below gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}"
        return base

    x_residualized, rank_controls_x = residualize([[value] for value in x_raw], controls)
    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    x = matrix_column(x_residualized, 0)
    y = matrix_column(y_residualized, 0)
    if vector_dot(x, x) <= EPS or vector_dot(y, y) <= EPS:
        base["reason"] = "zero residual energy for f3_stress or abundance after controls"
        base["rank_controls_x"] = rank_controls_x
        base["rank_controls_y"] = rank_controls_y
        return base

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    held_out_r2 = cv_r2_single_predictor(x, y, folds)
    slope = full_sample_slope(x, y)

    null_r2: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(n_join, f"{SEED}|{organism}|permute_y|trial={trial}")
        y_permuted = [y[permutation[index]] for index in range(n_join)]
        null_r2.append(cv_r2_single_predictor(x, y_permuted, folds))
    null95 = percentile_nearest_rank(null_r2, 0.95)
    real = held_out_r2 > null95
    direction = "positive" if slope > 0.0 else ("negative" if slope < 0.0 else "zero")

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "held_out_r2": held_out_r2,
        "null95": null95,
        "real": real,
        "effect_slope": slope,
        "effect_direction": direction,
        "fold_count": FOLD_COUNT,
        "permutation_count": PERMUTATION_COUNT,
        "rank_controls_x": rank_controls_x,
        "rank_controls_y": rank_controls_y,
        "residual_f3_energy": vector_dot(x, x),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
    }


def direction_summary(rows: list[dict[str, object]], only_real: bool) -> dict[str, object]:
    selected = [
        row for row in rows
        if row.get("status") == "computed" and (not only_real or row.get("real") is True)
    ]
    counts = {"positive": 0, "negative": 0, "zero": 0}
    organisms_by_direction = {"positive": [], "negative": [], "zero": []}
    for row in selected:
        direction = str(row.get("effect_direction", "zero"))
        if direction not in counts:
            direction = "zero"
        counts[direction] += 1
        organisms_by_direction[direction].append(str(row["organism"]))
    total = len(selected)
    if total == 0:
        return {
            "basis": "real_organisms" if only_real else "tested_organisms",
            "n": 0,
            "majority_direction": None,
            "majority_fraction": None,
            "counts": counts,
            "organisms_by_direction": organisms_by_direction,
        }
    majority_direction = max(counts, key=lambda key: (counts[key], key))
    return {
        "basis": "real_organisms" if only_real else "tested_organisms",
        "n": total,
        "majority_direction": majority_direction,
        "majority_fraction": counts[majority_direction] / total,
        "counts": counts,
        "organisms_by_direction": organisms_by_direction,
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                f3_projected=f3_projected,
            )
            for organism in ORGANISMS
        ]
        tested_rows = [row for row in per_organism if row.get("status") == "computed"]
        organisms_tested = len(tested_rows)
        real_rows = [row for row in tested_rows if row.get("real") is True]
        organisms_real = len(real_rows)
        real_threshold = max(MIN_TESTED_ORGANISMS, math.ceil(organisms_tested / 2))
        generalizes = organisms_tested >= MIN_TESTED_ORGANISMS and organisms_real >= real_threshold

        direction_all = direction_summary(tested_rows, only_real=False)
        direction_real = direction_summary(tested_rows, only_real=True)
        direction_consistency_passed = (
            direction_real["majority_fraction"] is not None
            and float(direction_real["majority_fraction"]) >= 0.75
        )

        if organisms_tested < MIN_TESTED_ORGANISMS:
            status = "needs_data"
        else:
            status = "passed" if generalizes else "failed"

        checks = {
            "cross_organism_computed": {
                "passed": organisms_tested >= MIN_TESTED_ORGANISMS,
                "organisms_tested": organisms_tested,
                "minimum": MIN_TESTED_ORGANISMS,
            },
            "f3_generalizes": {
                "passed": generalizes,
                "organisms_real": organisms_real,
                "organisms_tested": organisms_tested,
                "threshold": real_threshold,
                "rule": "passed iff organisms_real >= max(3, ceil(organisms_tested/2))",
            },
            "direction_consistency": {
                "passed": direction_consistency_passed,
                "real_organism_direction_summary": direction_real,
                "tested_organism_direction_summary": direction_all,
            },
        }

        emit(
            status,
            seed=SEED,
            fold_count=FOLD_COUNT,
            permutation_count=PERMUTATION_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_tested=organisms_tested,
            organisms_real=organisms_real,
            real_threshold=real_threshold,
            generality_call=(
                "f3_stress_generalizes"
                if status == "passed"
                else ("needs_data" if status == "needs_data" else "yeast_specific_or_sparse_cross_organism_support")
            ),
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor": "per-gene f3_stress synonymous-family coordinate from projected Q9_FAMILIES first-minus-last codon weights",
                "residualization": "full-sample residualization of both f3_stress and log10 abundance against the same controls before held-out f3-only CV",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            f3_definition={
                "coordinate": F3_COORDINATE,
                "raw_rule": "for each Q9_FAMILIES synonymous block, add +1 to first listed RNA codon and -1 to last listed RNA codon, then project within amino-acid synonymous fibers",
                "raw_families": Q9_FAMILIES,
                "projected_norm2": sum(f3_projected[codon] * f3_projected[codon] for codon in codons),
            },
            per_organism=per_organism,
            direction_consistency={
                "real_organisms": direction_real,
                "tested_organisms": direction_all,
            },
            checks=checks,
            cannot_claim=[
                "cross-organism association is not causal evidence",
                "this experiment has no phylogenetic comparative correction",
                "controls are sequence-derived basics only; species-specific TE, stability, and turnover controls are unavailable here",
                "a failed call is evidence against broad generality under this held-out/null gate, not proof that no species-specific mechanism exists",
            ],
        )
    except Exception as exc:
        emit(
            "needs_data",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "cross_organism_computed": {"passed": False},
                "f3_generalizes": {"passed": False},
                "direction_consistency": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

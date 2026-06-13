#!/usr/bin/env python3
"""Empirical biological-signature test for the Window6 boundary set R."""

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

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    controls_for_counts,
    vector_dot,
)
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    ORGANISMS,
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import (  # noqa: E402
    MIN_PROTEINS_PER_ORGANISM,
)
from run_b_star_q6_translation_survival_powered import (  # noqa: E402
    fibers_for,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_boundary_set_biological_signature_powered"
CLAIM_ID = "h3.cross_layer_relation.boundary_set_biological_signature.b_star_q6_window6_R_powered"

R_BOUNDARY_CODONS = [
    "AAA",
    "AGA",
    "AGG",
    "AUA",
    "CUA",
    "CUC",
    "CUG",
    "CUU",
    "UAA",
    "UAG",
    "UCA",
    "UGA",
    "UUA",
]
R_SENSE_CODONS = ["AAA", "AGA", "AGG", "AUA", "CUA", "CUC", "CUG", "CUU", "UCA", "UUA"]
R_STOP_CODONS = ["UAA", "UAG", "UGA"]

PERMUTATION_COUNT = 1000
MIN_COMPLETE_ORGANISMS = 10
SIGNIFICANCE_ALPHA = 0.05
CONSISTENT_DIRECTION_FRACTION = 0.75
SEED = "sha256:b_star_q6_boundary_set_biological_signature_powered:deterministic"
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


def sign_label(value: float, eps: float = EPS) -> str:
    if value > eps:
        return "preferred"
    if value < -eps:
        return "avoided"
    return "zero"


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def partial_corr_from_residuals(x: list[float], y: list[float]) -> float:
    x_energy = vector_dot(x, x)
    y_energy = vector_dot(y, y)
    denom = math.sqrt(x_energy * y_energy)
    if denom <= EPS:
        return 0.0
    return vector_dot(x, y) / denom


def validate_boundary_set(code: dict[str, str]) -> dict[str, object]:
    missing = [codon for codon in R_BOUNDARY_CODONS if codon not in code]
    stop_mismatch = [codon for codon in R_STOP_CODONS if code.get(codon) != "*"]
    sense_mismatch = [codon for codon in R_SENSE_CODONS if code.get(codon) == "*"]
    duplicate_count = len(R_BOUNDARY_CODONS) - len(set(R_BOUNDARY_CODONS))
    if missing or stop_mismatch or sense_mismatch or duplicate_count:
        raise ValueError(
            "invalid Window6 R definition: "
            f"missing={missing}, stop_mismatch={stop_mismatch}, "
            f"sense_mismatch={sense_mismatch}, duplicate_count={duplicate_count}"
        )
    return {
        "R_boundary_codons": R_BOUNDARY_CODONS,
        "R_sense_codons": R_SENSE_CODONS,
        "R_stop_codons": R_STOP_CODONS,
        "R_boundary_size": len(R_BOUNDARY_CODONS),
        "R_sense_size": len(R_SENSE_CODONS),
        "R_stop_size": len(R_STOP_CODONS),
    }


def organism_records(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
) -> tuple[list[dict[str, int]], list[float], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    count_rows: list[dict[str, int]] = []
    y_rows: list[float] = []
    control_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

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

        count_rows.append(counts)
        y_rows.append(math.log10(abundance))
        control_rows.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=cds_len_nt,
            )
        )

    return count_rows, y_rows, control_rows, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def codon_preference_scores(
    *,
    count_rows: list[dict[str, int]],
    y_rows: list[float],
    control_rows: list[list[float]],
    codons: list[str],
    fibers: dict[str, list[str]],
) -> tuple[dict[str, float], dict[str, dict[str, object]], int, int]:
    scores: dict[str, float] = {codon: 0.0 for codon in codons}
    metadata: dict[str, dict[str, object]] = {}
    estimated_count = 0
    total_family_positive_observations = 0
    codon_index = {codon: index for index, codon in enumerate(codons)}
    codon_to_aa = {
        codon: aa
        for aa, family in fibers.items()
        for codon in family
    }
    family_presence = {
        aa: sum(1 for counts in count_rows if sum(counts[codon] for codon in family) > 0)
        for aa, family in fibers.items()
    }
    total_family_positive_observations = sum(family_presence.values())

    x_raw: list[list[float]] = []
    for counts in count_rows:
        row = [0.0 for _ in codons]
        for aa, family in fibers.items():
            family_total = sum(counts[codon] for codon in family)
            if family_total <= 0:
                continue
            for codon in family:
                row[codon_index[codon]] = counts[codon] / family_total
        x_raw.append(row)

    x_residualized, rank_controls_x = residualize(x_raw, control_rows)
    y_residualized, rank_controls_y = residualize([[value] for value in y_rows], control_rows)
    y = matrix_column(y_residualized, 0)
    y_energy = vector_dot(y, y)

    for codon in codons:
        aa = codon_to_aa[codon]
        family = sorted(fibers[aa])
        x = matrix_column(x_residualized, codon_index[codon])
        x_energy = vector_dot(x, x)
        score = partial_corr_from_residuals(x, y)
        scores[codon] = score
        estimable = x_energy > EPS and y_energy > EPS
        if estimable:
            estimated_count += 1
        metadata[codon] = {
            "aa": aa,
            "family": family,
            "n_family_rows": family_presence[aa],
            "missing_family_rows_encoded_as_zero": len(count_rows) - family_presence[aa],
            "estimable": estimable,
            "rank_controls_frequency": rank_controls_x,
            "rank_controls_abundance": rank_controls_y,
            "residual_frequency_energy": x_energy,
            "residual_abundance_energy": y_energy,
        }

    return scores, metadata, estimated_count, total_family_positive_observations


def subset_diff(scores: dict[str, float], selected: set[str], universe: list[str]) -> float:
    selected_values = [scores[codon] for codon in universe if codon in selected]
    complement_values = [scores[codon] for codon in universe if codon not in selected]
    return mean(selected_values) - mean(complement_values)


def permutation_test(
    *,
    scores: dict[str, float],
    universe: list[str],
    r_codons: list[str],
    organism: str,
) -> dict[str, object]:
    r_set = set(r_codons)
    r_mean = mean([scores[codon] for codon in r_codons])
    non_r_codons = [codon for codon in universe if codon not in r_set]
    non_r_mean = mean([scores[codon] for codon in non_r_codons])
    observed = r_mean - non_r_mean

    null_diffs: list[float] = []
    k = len(r_codons)
    for trial in range(PERMUTATION_COUNT):
        order = deterministic_permutation(
            len(universe),
            f"{SEED}|{organism}|boundary_subset|trial={trial}",
        )
        subset = {universe[index] for index in order[:k]}
        null_diffs.append(subset_diff(scores, subset, universe))

    extreme_two_sided = sum(1 for value in null_diffs if abs(value) >= abs(observed) - EPS)
    if observed > EPS:
        extreme_directional = sum(1 for value in null_diffs if value >= observed - EPS)
    elif observed < -EPS:
        extreme_directional = sum(1 for value in null_diffs if value <= observed + EPS)
    else:
        extreme_directional = len(null_diffs)
    perm_p = (extreme_two_sided + 1) / (len(null_diffs) + 1)
    directional_p = (extreme_directional + 1) / (len(null_diffs) + 1)
    sorted_null = sorted(null_diffs)
    lower_index = max(0, math.ceil(0.025 * len(sorted_null)) - 1)
    upper_index = max(0, math.ceil(0.975 * len(sorted_null)) - 1)

    return {
        "R_mean": r_mean,
        "nonR_mean": non_r_mean,
        "diff": observed,
        "direction": sign_label(observed),
        "perm_p": perm_p,
        "directional_perm_p": directional_p,
        "significant": perm_p <= SIGNIFICANCE_ALPHA,
        "null_mean": mean(null_diffs),
        "null_025": sorted_null[lower_index],
        "null_975": sorted_null[upper_index],
    }


def top_bottom_codons(scores: dict[str, float], limit: int = 8) -> dict[str, list[dict[str, object]]]:
    ordered = sorted(scores.items(), key=lambda item: item[1])
    return {
        "most_avoided": [{"codon": codon, "score": score} for codon, score in ordered[:limit]],
        "most_preferred": [{"codon": codon, "score": score} for codon, score in reversed(ordered[-limit:])],
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
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

    count_rows, y_rows, controls, data_summary = organism_records(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
    )
    n_join = len(y_rows)
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

    scores, score_metadata, estimable_count, total_family_rows = codon_preference_scores(
        count_rows=count_rows,
        y_rows=y_rows,
        control_rows=controls,
        codons=codons,
        fibers=fibers,
    )
    comparison = permutation_test(
        scores=scores,
        universe=codons,
        r_codons=R_SENSE_CODONS,
        organism=organism,
    )
    non_r_codons = [codon for codon in codons if codon not in set(R_SENSE_CODONS)]

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "R_mean": comparison["R_mean"],
        "nonR_mean": comparison["nonR_mean"],
        "diff": comparison["diff"],
        "perm_p": comparison["perm_p"],
        "directional_perm_p": comparison["directional_perm_p"],
        "direction": comparison["direction"],
        "significant": comparison["significant"],
        "permutation_count": PERMUTATION_COUNT,
        "null_mean": comparison["null_mean"],
        "null_025": comparison["null_025"],
        "null_975": comparison["null_975"],
        "R_codon_scores": {codon: scores[codon] for codon in R_SENSE_CODONS},
        "nonR_codon_count": len(non_r_codons),
        "sense_codon_count": len(codons),
        "estimable_codon_count": estimable_count,
        "nonestimable_codons": [
            codon for codon in codons
            if score_metadata[codon].get("estimable") is not True
        ],
        "total_family_positive_observations": total_family_rows,
        "codon_preference_scores": scores,
        "codon_score_metadata": score_metadata,
        "top_bottom_codons": top_bottom_codons(scores),
        "data_summary": data_summary,
    }


def direction_summary(rows: list[dict[str, object]], significant_only: bool) -> dict[str, object]:
    selected = [
        row for row in rows
        if row.get("status") == "computed"
        and (not significant_only or row.get("significant") is True)
    ]
    counts = {"preferred": 0, "avoided": 0, "zero": 0}
    organisms_by_direction = {"preferred": [], "avoided": [], "zero": []}
    for row in selected:
        direction = str(row.get("direction", "zero"))
        if direction not in counts:
            direction = "zero"
        counts[direction] += 1
        organisms_by_direction[direction].append(str(row["organism"]))

    total = len(selected)
    if total == 0:
        return {
            "basis": "significant_organisms" if significant_only else "computed_organisms",
            "n": 0,
            "majority_direction": None,
            "majority_count": 0,
            "majority_fraction": None,
            "counts": counts,
            "organisms_by_direction": organisms_by_direction,
        }

    majority_direction = max(counts, key=lambda key: (counts[key], key))
    majority_count = counts[majority_direction]
    return {
        "basis": "significant_organisms" if significant_only else "computed_organisms",
        "n": total,
        "majority_direction": majority_direction,
        "majority_count": majority_count,
        "majority_fraction": majority_count / total,
        "counts": counts,
        "organisms_by_direction": organisms_by_direction,
    }


def compact_per_organism(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for row in rows:
        if row.get("status") != "computed":
            out.append(row)
            continue
        out.append(
            {
                "organism": row["organism"],
                "status": row["status"],
                "n_join": row["n_join"],
                "R_mean": row["R_mean"],
                "nonR_mean": row["nonR_mean"],
                "diff": row["diff"],
                "perm_p": row["perm_p"],
                "directional_perm_p": row["directional_perm_p"],
                "direction": row["direction"],
                "significant": row["significant"],
                "R_codon_scores": row["R_codon_scores"],
                "estimable_codon_count": row["estimable_codon_count"],
                "nonestimable_codons": row["nonestimable_codons"],
                "top_bottom_codons": row["top_bottom_codons"],
            }
        )
    return sorted(out, key=lambda item: str(item["organism"]))


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        boundary_definition = validate_boundary_set(code)

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                fibers=fibers,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        significant = [row for row in computed if row.get("significant") is True]
        n_significant = len(significant)
        significant_threshold = math.ceil(n_computed / 2) if n_computed else 0

        all_direction_summary = direction_summary(computed, significant_only=False)
        significant_direction_summary = direction_summary(computed, significant_only=True)
        majority_direction = significant_direction_summary["majority_direction"]
        majority_count = int(significant_direction_summary["majority_count"])
        majority_fraction = significant_direction_summary["majority_fraction"]
        direction_consistent = (
            majority_direction in {"preferred", "avoided"}
            and majority_fraction is not None
            and float(majority_fraction) >= CONSISTENT_DIRECTION_FRACTION
            and majority_count >= significant_threshold
        )

        enough_data = n_computed >= MIN_COMPLETE_ORGANISMS
        signature_passed = (
            enough_data
            and n_significant >= significant_threshold
            and direction_consistent
        )

        if not enough_data:
            status = "needs_data"
        else:
            status = "passed" if signature_passed else "failed"

        checks = {
            "per_codon_preference_computed": {
                "passed": enough_data,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "organisms_requested": len(ORGANISMS),
                "sense_codon_count": len(codons),
                "R_sense_codon_count": len(R_SENSE_CODONS),
            },
            "R_signature_vs_null": {
                "passed": n_significant >= significant_threshold if enough_data else False,
                "significant_organisms": n_significant,
                "organisms_computed": n_computed,
                "threshold": significant_threshold,
                "alpha_two_sided": SIGNIFICANCE_ALPHA,
                "permutation_count": PERMUTATION_COUNT,
            },
            "cross_organism_consistency": {
                "passed": direction_consistent if enough_data else False,
                "rule": "among significant organisms, majority direction fraction >= 0.75 and the majority direction covers at least ceil(n_computed/2) organisms",
                "significant_direction_summary": significant_direction_summary,
                "all_computed_direction_summary": all_direction_summary,
                "minimum_consistent_fraction": CONSISTENT_DIRECTION_FRACTION,
            },
        }

        emit(
            status,
            seed=SEED,
            permutation_count=PERMUTATION_COUNT,
            alpha_two_sided=SIGNIFICANCE_ALPHA,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            organisms_significant=n_significant,
            significant_threshold=significant_threshold,
            boundary_definition=boundary_definition,
            biological_signature_call=(
                "Window6 boundary R has a cross-organism abundance-preference signature"
                if status == "passed"
                else (
                    "needs_data"
                    if status == "needs_data"
                    else "R is not distinguished from non-R sense codons under this abundance-preference test"
                )
            ),
            controls_used={
                "target": "log10(abundance_ppm)",
                "codon_preference_score": "Pearson correlation between residualized same-family codon frequency and residualized log10 protein abundance; family-internal frequency is 0 for genes without that amino-acid family, with amino-acid composition included as controls",
                "R_test_statistic": "mean preference score of 10 R-sense codons minus mean preference score of all non-R sense codons",
                "null": "deterministic SHA256-seeded random same-size subsets of sense codons; two-sided permutation p uses abs(diff)",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            cross_organism_consistency={
                "significant_organisms": significant_direction_summary,
                "all_computed_organisms": all_direction_summary,
            },
            per_organism=compact_per_organism(per_organism),
            checks=checks,
            cannot_claim=[
                "this is an association test, not causal evidence for codon effects",
                "the fixed R set is tested as a codon-membership label only; no external Window6 constants or usage-derived fitting enter R",
                "there is no phylogenetic comparative correction, so cross-organism counts are descriptive",
                "a failed call means no systematic biological signature under this abundance-preference gate, not proof that R has no other empirical correlate",
            ],
        )
    except Exception as exc:
        emit(
            "needs_data",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "per_codon_preference_computed": {"passed": False},
                "R_signature_vs_null": {"passed": False},
                "cross_organism_consistency": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

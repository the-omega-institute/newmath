#!/usr/bin/env python3
"""Position-aware B*_Q6 boundary-response audit against ordered CDS and TE."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_positional_boundary_response_powered"
CLAIM_ID = "h3.cross_layer_relation.positional_boundary_response.b_star_q6_translation_efficiency_powered"

PERMUTATION_COUNT = 240
MIN_OCCURRENCES_PER_COORDINATE = 2000
MIN_TE_GENES_PER_STRATUM = 500
NULL_SUBSAMPLE_MAX_ROWS = 8000
LAMBDA_DL = 0.01
MODEL_DF = 2
EPS = 1e-12

YEAST_ORDERED_CDS = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
ECOLI_ORDERED_CDS = "tools/bio_reality/data/cds_ordered_sequences_escherichia_coli_k12_mg1655.json"
YEAST_POSITIONAL_PROFILE = "tools/bio_reality/data/cds_positional_codon_profile_saccharomyces_cerevisiae.json"
YEAST_TE = "tools/bio_reality/data/riboseq_translation_efficiency_saccharomyces_cerevisiae.json"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_number(value):
        raise ValueError(f"{field} must be a finite number")
    return float(value)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def dna_codon(codon: str) -> str:
    return codon.replace("U", "T")


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code_rna = standard_code(repo)
    codons_rna = [codon for codon in sorted(code_rna) if code_rna[codon] != "*"]
    fibers_rna = fibers_for(code_rna, codons_rna)
    q_projected_rna = {name: project_syn(vector, fibers_rna) for name, vector in q_vectors(codons_rna).items()}
    codons_dna = [dna_codon(codon) for codon in codons_rna]
    q_projected_dna = {
        name: {dna_codon(codon): value for codon, value in vector.items()}
        for name, vector in q_projected_rna.items()
    }
    return {
        "codons_dna": codons_dna,
        "q_projected_dna": q_projected_dna,
        "q_names": list(q_projected_dna),
    }


def validate_required_files(repo: pathlib.Path) -> list[str]:
    required = [YEAST_ORDERED_CDS, ECOLI_ORDERED_CDS, YEAST_POSITIONAL_PROFILE, YEAST_TE, "tools/bio_reality/data/ncbi_genetic_codes.json"]
    return [path for path in required if not (repo / path).exists()]


def schema_summary(repo: pathlib.Path) -> dict[str, object]:
    out: dict[str, object] = {}
    for rel in [YEAST_ORDERED_CDS, ECOLI_ORDERED_CDS, YEAST_POSITIONAL_PROFILE, YEAST_TE]:
        payload = load_json(repo / rel)
        if not isinstance(payload, dict):
            raise ValueError(f"{rel} must contain a JSON object")
        item: dict[str, object] = {"keys": list(payload.keys())}
        if isinstance(payload.get("cds"), list):
            cds = payload["cds"]
            item["cds_count"] = len(cds)
            item["cds_sample_keys"] = list(cds[0].keys()) if cds and isinstance(cds[0], dict) else []
        if isinstance(payload.get("genes"), list):
            genes = payload["genes"]
            item["gene_count"] = len(genes)
            item["gene_sample_keys"] = list(genes[0].keys()) if genes and isinstance(genes[0], dict) else []
        if isinstance(payload.get("align_5prime"), dict):
            item["align_5prime_family_count"] = len(payload["align_5prime"])
            item["align_5prime_window_codons"] = payload.get("align_5prime_window_codons")
        if isinstance(payload.get("align_3prime"), dict):
            item["align_3prime_family_count"] = len(payload["align_3prime"])
            item["align_3prime_window_codons"] = payload.get("align_3prime_window_codons")
        item["sha256"] = payload.get("sha256")
        out[rel] = item
    return out


def iter_position_rows(
    cds_records: list[dict[str, object]],
    q_vector: dict[str, float],
    *,
    allowed_gene_ids: set[str] | None = None,
) -> tuple[list[tuple[float, float, str]], dict[str, object]]:
    support = {codon for codon, value in q_vector.items() if abs(value) > EPS}
    rows: list[tuple[float, float, str]] = []
    genes_considered = 0
    genes_with_support = 0
    skipped = {
        "non_object": 0,
        "missing_gene_id": 0,
        "gene_not_in_filter": 0,
        "bad_codon_list": 0,
        "short_cds": 0,
    }
    for item in cds_records:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        if allowed_gene_ids is not None and gene_id not in allowed_gene_ids:
            skipped["gene_not_in_filter"] += 1
            continue
        codons = item.get("codons")
        if not isinstance(codons, list) or any(not isinstance(codon, str) for codon in codons):
            skipped["bad_codon_list"] += 1
            continue
        n_codons = len(codons)
        if n_codons < 2:
            skipped["short_cds"] += 1
            continue
        genes_considered += 1
        had_support = False
        scale = 1.0 / (n_codons - 1)
        for index, codon in enumerate(codons):
            value = q_vector.get(codon)
            if value is None or abs(value) <= EPS:
                continue
            rows.append((index * scale, value, gene_id))
            had_support = True
        if had_support:
            genes_with_support += 1
    return rows, {
        "n_occurrences": len(rows),
        "genes_considered": genes_considered,
        "genes_with_coordinate_support": genes_with_support,
        "support_codons": sorted(support),
        "skipped": skipped,
    }


def normal_equation_fit(rows: list[tuple[float, float, str]]) -> dict[str, object]:
    if len(rows) < MODEL_DF:
        return {
            "status": "needs_data",
            "reason": f"n_occurrences={len(rows)} below model df={MODEL_DF}",
            "n_occurrences": len(rows),
        }
    x11 = x12 = x22 = 0.0
    b1 = b2 = 0.0
    y_sum = 0.0
    y2_sum = 0.0
    for rho, value, _gene_id in rows:
        x1 = rho
        x2 = rho * rho
        x11 += x1 * x1
        x12 += x1 * x2
        x22 += x2 * x2
        b1 += x1 * value
        b2 += x2 * value
        y_sum += value
        y2_sum += value * value
    det = x11 * x22 - x12 * x12
    if abs(det) <= EPS:
        return {"status": "needs_data", "reason": "singular rho/rho^2 normal equation", "n_occurrences": len(rows)}
    c1 = (b1 * x22 - b2 * x12) / det
    c2 = (x11 * b2 - x12 * b1) / det
    fitted_norm2 = 0.0
    sse = 0.0
    residual_sum = 0.0
    n = len(rows)
    base = y_sum / n
    centered_total = 0.0
    for rho, value, _gene_id in rows:
        fitted = c1 * rho + c2 * rho * rho
        fitted_norm2 += fitted * fitted
        residual = value - fitted
        sse += residual * residual
        residual_sum += residual
        centered_total += (value - base) * (value - base)
    epsilon = math.sqrt(fitted_norm2 / n)
    signed_endpoint_response = c1 + c2
    r2_about_zero = 0.0 if y2_sum <= EPS else max(0.0, min(1.0, fitted_norm2 / y2_sum))
    r2_centered = 0.0 if centered_total <= EPS else max(0.0, min(1.0, 1.0 - sse / centered_total))
    return {
        "status": "computed",
        "n_occurrences": n,
        "base_g": base,
        "c1": c1,
        "c2": c2,
        "epsilon": epsilon,
        "signed_endpoint_response": signed_endpoint_response,
        "abs_endpoint_response": abs(signed_endpoint_response),
        "mean_residual_after_boundary_fit": residual_sum / n,
        "r2_about_zero": r2_about_zero,
        "r2_centered": r2_centered,
        "sse_per_occurrence": sse / n,
        "model": "R_g(rho)=base_g + c1*rho + c2*rho^2 + U_g; fit is on synonymous residual support occurrences with base_g reported separately",
    }


def normal_equation_fit_xy(rhos: list[float], values: list[float]) -> float | None:
    if len(rhos) != len(values) or len(rhos) < MODEL_DF:
        return None
    x11 = x12 = x22 = 0.0
    b1 = b2 = 0.0
    for rho, value in zip(rhos, values):
        x1 = rho
        x2 = rho * rho
        x11 += x1 * x1
        x12 += x1 * x2
        x22 += x2 * x2
        b1 += x1 * value
        b2 += x2 * value
    det = x11 * x22 - x12 * x12
    if abs(det) <= EPS:
        return None
    c1 = (b1 * x22 - b2 * x12) / det
    c2 = (x11 * b2 - x12 * b1) / det
    fitted_norm2 = 0.0
    for rho in rhos:
        fitted = c1 * rho + c2 * rho * rho
        fitted_norm2 += fitted * fitted
    return math.sqrt(fitted_norm2 / len(rhos))


def deterministic_subsample_rows(
    rows: list[tuple[float, float, str]],
    *,
    coordinate: str,
    organism: str,
    max_rows: int,
) -> list[tuple[float, float, str]]:
    if len(rows) <= max_rows:
        return list(rows)
    keyed = []
    for index, row in enumerate(rows):
        material = f"{EXPERIMENT_ID}|subsample|{organism}|{coordinate}|{index}|{row[2]}|{row[0]:.12g}|{row[1]:.12g}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        keyed.append((int.from_bytes(digest[:8], "big"), row))
    keyed.sort(key=lambda item: item[0])
    return [row for _key, row in keyed[:max_rows]]


def gcd(left: int, right: int) -> int:
    while right:
        left, right = right, left % right
    return abs(left)


def affine_permutation_parameters(n: int, material_prefix: str) -> tuple[int, int]:
    digest = hashlib.sha256(f"{material_prefix}|{n}".encode("utf-8")).digest()
    step = 1 + (int.from_bytes(digest[:8], "big") % max(1, n - 1))
    while gcd(step, n) != 1:
        step += 1
        if step >= n:
            step = 1
    offset = int.from_bytes(digest[8:16], "big") % n
    return step, offset


def permutation_null95(
    rows: list[tuple[float, float, str]],
    *,
    coordinate: str,
    organism: str,
) -> dict[str, object]:
    null_rows = deterministic_subsample_rows(rows, coordinate=coordinate, organism=organism, max_rows=NULL_SUBSAMPLE_MAX_ROWS)
    if len(null_rows) < MODEL_DF:
        return {
            "permutation_count": 0,
            "null95": 0.0,
            "null_mean": 0.0,
            "null_rows_used": len(null_rows),
            "null_model": "not computed: too few rows after deterministic subsample",
        }
    rhos = [rho for rho, _value, _gene_id in null_rows]
    values = [value for _rho, value, _gene_id in null_rows]
    null_scores: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        step, offset = affine_permutation_parameters(len(null_rows), f"{EXPERIMENT_ID}|position_label_null|{organism}|{coordinate}|trial={trial}")
        permuted_rhos = [rhos[(step * index + offset) % len(null_rows)] for index in range(len(null_rows))]
        epsilon = normal_equation_fit_xy(permuted_rhos, values)
        if epsilon is not None:
            null_scores.append(epsilon)
    return {
        "permutation_count": len(null_scores),
        "null95": percentile_nearest_rank(null_scores, 0.95),
        "null_mean": sum(null_scores) / len(null_scores) if null_scores else 0.0,
        "null_rows_used": len(null_rows),
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|position_label_null|organism|coordinate|trial|index|n",
        "null_model": "deterministic permutation of normalized CDS position labels against fixed B*_Q6 residual values; no biological window constant is preset",
    }


def support_cosine_for_fit(q_vector: dict[str, float], fit: dict[str, object]) -> tuple[float, str | None]:
    support_values = [value for value in q_vector.values() if abs(value) > EPS]
    support_norm = math.sqrt(sum(value * value for value in support_values))
    response = float(fit.get("signed_endpoint_response", 0.0))
    response_norm = abs(response)
    if support_norm <= EPS:
        return 0.0, "zero_coordinate_support"
    if response_norm <= EPS:
        return 0.0, "zero_boundary_response"
    boundary_vector = [response * value for value in support_values]
    boundary_norm = math.sqrt(sum(value * value for value in boundary_vector))
    if boundary_norm <= EPS:
        return 0.0, "zero_boundary_vector"
    value = sum(boundary_vector[index] * support_values[index] for index in range(len(support_values))) / (boundary_norm * support_norm)
    if -1.0 - 1e-8 <= value < -1.0:
        value = -1.0
    if 1.0 < value <= 1.0 + 1e-8:
        value = 1.0
    return value, None


def analyze_coordinate(
    *,
    organism: str,
    coordinate: str,
    cds_records: list[dict[str, object]],
    q_vector: dict[str, float],
    allowed_gene_ids: set[str] | None = None,
) -> dict[str, object]:
    rows, row_summary = iter_position_rows(cds_records, q_vector, allowed_gene_ids=allowed_gene_ids)
    if len(rows) < MIN_OCCURRENCES_PER_COORDINATE:
        return {
            "coordinate": coordinate,
            "organism": organism,
            "status": "needs_data",
            "reason": f"n_occurrences={len(rows)} below honest gate {MIN_OCCURRENCES_PER_COORDINATE}",
            **row_summary,
        }
    fit = normal_equation_fit(rows)
    if fit.get("status") != "computed":
        return {"coordinate": coordinate, "organism": organism, **row_summary, **fit}
    null = permutation_null95(rows, coordinate=coordinate, organism=organism)
    c_h, c_h_note = support_cosine_for_fit(q_vector, fit)
    raw_margin = float(fit["epsilon"]) - float(null["null95"])
    score = raw_margin - LAMBDA_DL * MODEL_DF
    null95_pass = raw_margin > 0.0
    dl_pass = score > 0.0
    c_h_pass = c_h > 0.0
    return {
        "coordinate": coordinate,
        "organism": organism,
        "status": "computed",
        **row_summary,
        "fit": fit,
        "permutation_null": null,
        "Null95_pass": null95_pass,
        "lambda_DL": LAMBDA_DL,
        "DL": MODEL_DF,
        "description_length_penalized_score": score,
        "DL_pass": dl_pass,
        "C_H": c_h,
        "C_H_note": c_h_note,
        "C_H_pass": c_h_pass,
        "gate_pass": null95_pass and dl_pass and c_h_pass,
        "mechanism_interpretation": mechanism_interpretation(float(fit["c1"]), float(fit["c2"]), float(fit["signed_endpoint_response"])),
    }


def mechanism_interpretation(c1: float, c2: float, endpoint: float) -> str:
    if abs(endpoint) <= EPS:
        return "flat fitted endpoint; no directional mechanism interpretation is supported"
    curvature = "convex" if c2 > 0 else "concave" if c2 < 0 else "linear"
    if abs(c1) >= abs(c2):
        emphasis = "5prime-to-CDS trend is dominated by the linear term"
    else:
        emphasis = "curvature contributes more than the linear term"
    direction = "positive" if endpoint > 0 else "negative"
    return (
        f"{direction} endpoint response with {curvature} quadratic shape; {emphasis}. "
        "Candidate mechanisms remain descriptive: 5prime translational ramp, wobble-seam preference near initiation, ribosome accommodation boundary, or 3prime stop-proximal composition."
    )


def load_ordered_cds(repo: pathlib.Path, rel: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    payload = load_json(repo / rel)
    if not isinstance(payload, dict) or not isinstance(payload.get("cds"), list):
        raise ValueError(f"{rel} must contain a cds list")
    records = [item for item in payload["cds"] if isinstance(item, dict)]
    return records, {
        "path": rel,
        "organism": payload.get("organism"),
        "organism_label": payload.get("organism_label"),
        "n_cds_reported": payload.get("n_cds"),
        "n_cds_loaded": len(records),
        "sha256": payload.get("sha256"),
        "source_name": payload.get("source_name"),
    }


def te_strata(repo: pathlib.Path) -> dict[str, object]:
    payload = load_json(repo / YEAST_TE)
    if not isinstance(payload, dict) or not isinstance(payload.get("genes"), list):
        raise ValueError(f"{YEAST_TE} must contain genes list")
    values: list[tuple[str, float]] = []
    skipped = {"non_object": 0, "missing_gene_id": 0, "nonpositive_te": 0}
    for item in payload["genes"]:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        te = item.get("translation_efficiency")
        if not finite_number(te) or float(te) <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        values.append((gene_id, float(te)))
    values.sort(key=lambda item: item[1])
    if len(values) < 2 * MIN_TE_GENES_PER_STRATUM:
        return {"status": "needs_data", "reason": f"positive TE genes below {2 * MIN_TE_GENES_PER_STRATUM}", "n_positive_te": len(values), "skipped": skipped}
    midpoint = len(values) // 2
    low = values[:midpoint]
    high = values[-midpoint:]
    return {
        "status": "computed",
        "n_positive_te": len(values),
        "low_gene_ids": {gene_id for gene_id, _te in low},
        "high_gene_ids": {gene_id for gene_id, _te in high},
        "summary": {
            "path": YEAST_TE,
            "sha256": payload.get("sha256"),
            "study_ref": payload.get("study_ref"),
            "te_definition": payload.get("te_definition"),
            "n_positive_te": len(values),
            "split": "lower half vs upper half by measured ribo-seq translation_efficiency",
            "low_te_range": [low[0][1], low[-1][1]],
            "high_te_range": [high[0][1], high[-1][1]],
            "median_te": values[midpoint][1],
            "skipped": skipped,
        },
    }


def te_stratified_comparison(
    *,
    yeast_records: list[dict[str, object]],
    q_projected: dict[str, dict[str, float]],
    strata: dict[str, object],
) -> dict[str, object]:
    if strata.get("status") != "computed":
        return {"status": "needs_data", "reason": strata.get("reason"), "te_summary": strata}
    low_ids = strata["low_gene_ids"]
    high_ids = strata["high_gene_ids"]
    if not isinstance(low_ids, set) or not isinstance(high_ids, set):
        raise ValueError("TE strata gene-id sets malformed")
    by_coordinate: dict[str, object] = {}
    diffs: list[float] = []
    high_stronger = 0
    computed = 0
    for coordinate, q_vector in q_projected.items():
        low = analyze_coordinate(
            organism="saccharomyces_cerevisiae.low_TE",
            coordinate=coordinate,
            cds_records=yeast_records,
            q_vector=q_vector,
            allowed_gene_ids=low_ids,
        )
        high = analyze_coordinate(
            organism="saccharomyces_cerevisiae.high_TE",
            coordinate=coordinate,
            cds_records=yeast_records,
            q_vector=q_vector,
            allowed_gene_ids=high_ids,
        )
        low_eps = low.get("fit", {}).get("epsilon") if isinstance(low.get("fit"), dict) else None
        high_eps = high.get("fit", {}).get("epsilon") if isinstance(high.get("fit"), dict) else None
        diff = None
        ratio = None
        if finite_number(low_eps) and finite_number(high_eps):
            computed += 1
            diff = float(high_eps) - float(low_eps)
            ratio = float(high_eps) / (float(low_eps) + EPS)
            diffs.append(diff)
            if diff > 0:
                high_stronger += 1
        by_coordinate[coordinate] = {
            "low_TE": low,
            "high_TE": high,
            "epsilon_high_minus_low": diff,
            "epsilon_high_over_low": ratio,
            "high_TE_boundary_stronger": bool(diff is not None and diff > 0.0),
        }
    mean_diff = sum(diffs) / len(diffs) if diffs else 0.0
    return {
        "status": "computed" if computed else "needs_data",
        "te_summary": strata["summary"],
        "n_coordinates_compared": computed,
        "coordinates_high_TE_stronger": high_stronger,
        "mean_epsilon_high_minus_low": mean_diff,
        "by_coordinate": by_coordinate,
        "interpretation": (
            "High-vs-low TE comparison is descriptive stratification by measured ribo-seq translation efficiency; "
            "it does not prove that position-specific codon residuals cause TE."
        ),
    }


def analyze_organism_all(
    *,
    organism: str,
    records: list[dict[str, object]],
    q_projected: dict[str, dict[str, float]],
) -> dict[str, object]:
    by_coordinate = {
        coordinate: analyze_coordinate(
            organism=organism,
            coordinate=coordinate,
            cds_records=records,
            q_vector=q_vector,
        )
        for coordinate, q_vector in q_projected.items()
    }
    computed = [entry for entry in by_coordinate.values() if isinstance(entry, dict) and entry.get("status") == "computed"]
    gate_pass = [entry for entry in computed if entry.get("gate_pass")]
    null_pass = [entry for entry in computed if entry.get("Null95_pass")]
    return {
        "organism": organism,
        "status": "computed" if computed else "needs_data",
        "n_coordinates": len(by_coordinate),
        "n_computed": len(computed),
        "n_Null95_pass": len(null_pass),
        "n_all_gates_pass": len(gate_pass),
        "coordinates_all_gates_pass": [entry["coordinate"] for entry in gate_pass],
        "boundary_response_by_coordinate": by_coordinate,
    }


def checks_for(
    yeast_result: dict[str, object],
    te_comparison: dict[str, object],
    ecoli_result: dict[str, object],
) -> list[dict[str, object]]:
    yeast_computed = yeast_result.get("n_computed", 0)
    yeast_null = yeast_result.get("n_Null95_pass", 0)
    yeast_gate = yeast_result.get("n_all_gates_pass", 0)
    ecoli_gate = ecoli_result.get("n_all_gates_pass", 0)
    te_by_coord = te_comparison.get("by_coordinate") if isinstance(te_comparison, dict) else None
    te_computed = te_comparison.get("n_coordinates_compared", 0) if isinstance(te_comparison, dict) else 0
    return [
        {
            "name": "ordered_cds_and_te_data_loaded",
            "passed": int(yeast_computed) > 0 and int(te_computed) > 0 and ecoli_result.get("status") == "computed",
            "actual": {
                "yeast_coordinates_computed": yeast_computed,
                "te_coordinates_compared": te_computed,
                "ecoli_coordinates_computed": ecoli_result.get("n_computed"),
            },
            "expected": "ordered yeast CDS, ordered E.coli CDS, and yeast ribo-seq TE join support at least one B*_Q6 coordinate",
        },
        {
            "name": "Null95_position_label_permutation",
            "passed": int(yeast_null) > 0,
            "actual": {
                "yeast_coordinates_passing_Null95": yeast_null,
                "permutation_count": PERMUTATION_COUNT,
                "null_subsample_max_rows": NULL_SUBSAMPLE_MAX_ROWS,
            },
            "expected": "at least one yeast B*_Q6 coordinate has observed epsilon greater than 95th percentile position-label permutation null",
        },
        {
            "name": "description_length_penalty_and_coordinate_support",
            "passed": int(yeast_gate) > 0,
            "actual": {
                "yeast_coordinates_passing_all_gates": yeast_gate,
                "lambda_DL": LAMBDA_DL,
                "DL": MODEL_DF,
                "C_H_gate": "C_H > 0",
            },
            "expected": "at least one coordinate passes Null95, lambda*DL penalty, and coordinate-support direction consistency",
        },
        {
            "name": "te_stratified_boundary_response_emitted",
            "passed": int(te_computed) > 0 and isinstance(te_by_coord, dict),
            "actual": {
                "n_coordinates_compared": te_computed,
                "coordinates_high_TE_stronger": te_comparison.get("coordinates_high_TE_stronger") if isinstance(te_comparison, dict) else None,
                "mean_epsilon_high_minus_low": te_comparison.get("mean_epsilon_high_minus_low") if isinstance(te_comparison, dict) else None,
            },
            "expected": "high-vs-low measured TE strata emit epsilon differences by coordinate",
        },
        {
            "name": "ecoli_control_emitted",
            "passed": ecoli_result.get("status") == "computed",
            "actual": {
                "ecoli_coordinates_passing_all_gates": ecoli_gate,
                "ecoli_coordinates_passing_Null95": ecoli_result.get("n_Null95_pass"),
            },
            "expected": "E.coli ordered-CDS control is run through the same B*_Q6 positional boundary-response gate",
        },
        {
            "name": "no_causal_or_constant_overclaim",
            "passed": cannot_claim() == [
                "Position-specific codon residual frequency is not direct evidence of ribosome pausing or accommodation causality.",
                "High-vs-low TE stratification is correlation with measured ribo-seq translation efficiency, not proof that B*_Q6 position structure causes TE.",
                "The quadratic boundary-response projection is descriptive and low-rank; other smooth or local models could attribute structure differently.",
                "E.coli is a control for this pipeline, not a proof that prokaryotes lack all 5prime translation-ramp structure.",
                "No Fibonacci, automath, phi, Z6, 571, 1/12, 8/9, or other preset window constant is used or supported by this experiment.",
            ],
            "actual": cannot_claim(),
            "expected": "required caveats are emitted verbatim",
        },
    ]


def cannot_claim() -> list[str]:
    return [
        "Position-specific codon residual frequency is not direct evidence of ribosome pausing or accommodation causality.",
        "High-vs-low TE stratification is correlation with measured ribo-seq translation efficiency, not proof that B*_Q6 position structure causes TE.",
        "The quadratic boundary-response projection is descriptive and low-rank; other smooth or local models could attribute structure differently.",
        "E.coli is a control for this pipeline, not a proof that prokaryotes lack all 5prime translation-ramp structure.",
        "No Fibonacci, automath, phi, Z6, 571, 1/12, 8/9, or other preset window constant is used or supported by this experiment.",
    ]


def verdict_for(yeast_result: dict[str, object], te_comparison: dict[str, object], ecoli_result: dict[str, object]) -> str:
    yeast_gate = int(yeast_result.get("n_all_gates_pass", 0))
    yeast_null = int(yeast_result.get("n_Null95_pass", 0))
    high_stronger = int(te_comparison.get("coordinates_high_TE_stronger", 0)) if isinstance(te_comparison, dict) else 0
    te_compared = int(te_comparison.get("n_coordinates_compared", 0)) if isinstance(te_comparison, dict) else 0
    ecoli_gate = int(ecoli_result.get("n_all_gates_pass", 0))
    if yeast_gate <= 0:
        return "negative: yeast B*_Q6 positional boundary response did not pass Null95 plus DL plus C_H gates; TE association is descriptive only."
    return (
        f"positive descriptive boundary response: yeast has {yeast_gate} coordinate(s) passing all gates "
        f"({yeast_null} passing Null95); high-TE epsilon exceeds low-TE epsilon in {high_stronger}/{te_compared} coordinates; "
        f"E.coli control has {ecoli_gate} coordinate(s) passing all gates."
    )


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        missing = validate_required_files(repo)
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required ordered-CDS, positional-profile, TE, or genetic-code data not present")
        schemas = schema_summary(repo)
        context = q6_context(repo)
        q_projected = context["q_projected_dna"]
        if not isinstance(q_projected, dict):
            raise ValueError("Q context malformed")
        yeast_records, yeast_data_summary = load_ordered_cds(repo, YEAST_ORDERED_CDS)
        ecoli_records, ecoli_data_summary = load_ordered_cds(repo, ECOLI_ORDERED_CDS)
        yeast_result = analyze_organism_all(
            organism="saccharomyces_cerevisiae",
            records=yeast_records,
            q_projected=q_projected,  # type: ignore[arg-type]
        )
        strata = te_strata(repo)
        te_comparison = te_stratified_comparison(
            yeast_records=yeast_records,
            q_projected=q_projected,  # type: ignore[arg-type]
            strata=strata,
        )
        ecoli_result = analyze_organism_all(
            organism="escherichia_coli_k12_mg1655",
            records=ecoli_records,
            q_projected=q_projected,  # type: ignore[arg-type]
        )
        checks = checks_for(yeast_result, te_comparison, ecoli_result)
        status = "passed" if all(check["passed"] for check in checks) else "failed"
        if int(yeast_result.get("n_computed", 0)) <= 0 or te_comparison.get("status") == "needs_data":
            status = "needs_data"
        verdict = verdict_for(yeast_result, te_comparison, ecoli_result)
        reason = None
        if status == "failed":
            reason = "data were sufficient but the yeast positional boundary-response signal did not satisfy every honest gate"
        if status == "needs_data":
            reason = "ordered-CDS or measured-TE support was insufficient for this boundary-response gate"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "statement": "Descriptive position projection: fit B*_Q6 synonymous residual coordinates along normalized CDS position and compare high-vs-low real ribo-seq TE strata; this is not causal proof.",
                "model": {
                    "equation": "R_g(rho)=base_g + epsilon_g*Q_g(rho) + U_g with fitted low-rank Q_g(rho)=c1*rho+c2*rho^2",
                    "position_coordinate": "rho = codon index / (n_codons - 1), computed from full ordered CDS with no preset biological window constant",
                    "epsilon_g": "sqrt(mean((c1*rho+c2*rho^2)^2)) over coordinate-support codon occurrences",
                    "Null95": "deterministic position-label permutation null, observed epsilon must exceed 95th percentile",
                    "lambda_DL": LAMBDA_DL,
                    "DL": MODEL_DF,
                    "C_H": "cosine-like sign agreement between fitted endpoint response and B*_Q6 coordinate support direction",
                },
                "schema_summary": schemas,
                "data_summary": {
                    "yeast_ordered_cds": yeast_data_summary,
                    "ecoli_ordered_cds": ecoli_data_summary,
                },
                "boundary_response_by_coordinate": yeast_result["boundary_response_by_coordinate"],
                "yeast_summary": {
                    key: value
                    for key, value in yeast_result.items()
                    if key != "boundary_response_by_coordinate"
                },
                "te_stratified_comparison": te_comparison,
                "ecoli_control": ecoli_result,
                "verdict": verdict,
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable ordered-CDS, TE, or positional boundary-response fit")


if __name__ == "__main__":
    main()

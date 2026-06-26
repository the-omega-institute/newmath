#!/usr/bin/env python3
"""Powered B*_Q6 per-gene survival against measured ribo-seq TE."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    frobenius2,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_survival_powered import (
    DEGENERATE_R2,
    RANK_TOL,
    SURVIVAL_EPS,
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_measured_te_survival_powered"
CLAIM_ID = "h3.cross_layer_relation.ribosome_te_survival.b_star_q6_measured_te_powered"
CONJECTURE_ID = "q6.ribosome-te-survival.with-mrna-control.cross-layer"

ORGANISMS = [
    "saccharomyces_cerevisiae",
    "escherichia_coli_k12_mg1655",
    "homo_sapiens",
    "danio_rerio",
]
MIN_ORGANISMS = 1
MIN_GENES_PER_ORGANISM = 500
MODELED_TAI_EXPERIMENT = "run_b_star_q6_translation_survival_powered.py"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0 or int(value) != value:
                raise ValueError(f"{organism}.joined[{row_index}].codon_counts.{raw_codon} must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def te_by_protein(payload: dict[str, object], organism: str) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} TE payload must contain genes list")
    out: dict[str, dict[str, float]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna": 0,
        "nonpositive_footprint": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        te = numeric(item.get("te"), f"{organism}.genes[{row_index}].te")
        mrna = numeric(item.get("mrna"), f"{organism}.genes[{row_index}].mrna")
        footprint = numeric(item.get("footprint"), f"{organism}.genes[{row_index}].footprint")
        if te <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        if mrna <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue
        if footprint <= 0.0:
            skipped["nonpositive_footprint"] += 1
            continue
        if protein_id in out:
            skipped["duplicate_protein_id"] += 1
            continue
        out[protein_id] = {"te": te, "mrna": mrna, "footprint": footprint}
    return out, {
        "n_genes_with_te_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "n_valid_te_by_protein": len(out),
        "skipped_te_records": skipped,
    }


def measured_te_rows(
    *,
    cds_payload: dict[str, object],
    te_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    te_index, te_summary = te_by_protein(te_payload, organism)

    x_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_measured_te_match": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        te_record = te_index.get(protein_id)
        if te_record is None:
            skipped["no_measured_te_match"] += 1
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
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        y_rows.append([math.log10(te_record["te"])])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )

    summary = {
        **te_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_genes": len(x_rows),
        "skipped_cds_records": skipped,
    }
    return x_rows, y_rows, z_rows, summary


def partial_r2_entries(
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], list[dict[str, object]]]:
    y_col = matrix_column(y_tilde, 0)
    y_ss = vector_dot(y_col, y_col)
    matrix: dict[str, dict[str, float]] = {}
    raw_improvement: dict[str, dict[str, float]] = {}
    survivors: list[dict[str, object]] = []
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_ss = vector_dot(x_col, x_col)
        if x_ss <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
            improvement = 0.0
            partial = 0.0
        else:
            xy = vector_dot(x_col, y_col)
            improvement = (xy * xy) / x_ss
            partial = max(0.0, min(1.0, improvement / y_ss))
        matrix[q_name] = {"log10_measured_te": partial}
        raw_improvement[q_name] = {"log10_measured_te": improvement}
        if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
            survivors.append({"q_coordinate": q_name, "readout": "log10_measured_te", "S_QT_measured": partial})
    return matrix, raw_improvement, survivors


def modeled_tai_comparison(repo: pathlib.Path) -> dict[str, object]:
    script = repo / "tools/fibonacci_reality/experiments" / MODELED_TAI_EXPERIMENT
    if not script.exists():
        return {
            "available": False,
            "reason": f"{MODELED_TAI_EXPERIMENT} is not present",
        }
    try:
        import subprocess

        completed = subprocess.run(
            [sys.executable, str(script)],
            check=False,
            cwd=str(script.parent),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except Exception as exc:
        return {
            "available": False,
            "reason": f"could not execute modeled-tAI experiment: {exc}",
        }
    if completed.returncode != 0:
        return {
            "available": False,
            "reason": "modeled-tAI experiment did not pass",
            "returncode": completed.returncode,
            "stderr": completed.stderr.strip(),
        }
    try:
        payload = json.loads(completed.stdout.strip().splitlines()[-1])
    except Exception as exc:
        return {
            "available": False,
            "reason": f"could not parse modeled-tAI JSON: {exc}",
            "stdout_prefix": completed.stdout[:500],
        }
    result = payload.get("result")
    if not isinstance(result, dict):
        return {
            "available": False,
            "reason": "modeled-tAI JSON result is missing",
        }
    surviving = result.get("surviving_coordinates")
    if not isinstance(surviving, list):
        return {
            "available": False,
            "reason": "modeled-tAI surviving_coordinates is missing",
        }
    modeled_coordinates = sorted({
        str(item.get("q_coordinate"))
        for item in surviving
        if isinstance(item, dict) and isinstance(item.get("q_coordinate"), str)
    })
    return {
        "available": True,
        "experiment_id": payload.get("experiment_id"),
        "status": payload.get("status"),
        "R2_QT_modeled": result.get("R2_QT"),
        "modeled_surviving_q_coordinates": modeled_coordinates,
        "comparison_boundary": "modeled-tAI pattern is cross-organism 9x9; measured-TE pattern here is per-organism gene-level 9x1, so comparison is coordinate-set support only, not equivalence of estimands",
        "cannot_claim": [
            "agreement would support compatibility with the modeled-tAI coordinate pattern, not causal validation",
            "disagreement records a measured-readout difference and does not falsify tAI biology by itself",
        ],
    }


def compare_with_modeled(measured_coordinates: list[str], modeled: dict[str, object]) -> dict[str, object]:
    measured_set = set(measured_coordinates)
    modeled_raw = modeled.get("modeled_surviving_q_coordinates")
    modeled_set = set(modeled_raw) if isinstance(modeled_raw, list) else set()
    overlap = sorted(measured_set & modeled_set)
    measured_only = sorted(measured_set - modeled_set)
    modeled_only = sorted(modeled_set - measured_set)
    return {
        "modeled_tai_available": bool(modeled.get("available")),
        "measured_surviving_q_coordinates": sorted(measured_set),
        "modeled_surviving_q_coordinates": sorted(modeled_set),
        "overlap_q_coordinates": overlap,
        "measured_only_q_coordinates": measured_only,
        "modeled_only_q_coordinates": modeled_only,
        "coordinate_set_consistent_with_modeled_tai": bool(modeled.get("available")) and measured_set == modeled_set,
        "interpretation": (
            "measured-TE surviving q-coordinate set matches the modeled-tAI surviving left-coordinate set"
            if bool(modelled_available := modeled.get("available")) and measured_set == modeled_set
            else (
                "modeled-tAI comparison unavailable"
                if not modelled_available
                else "measured-TE surviving q-coordinate set differs from the modeled-tAI surviving left-coordinate set"
            )
        ),
    }


def cannot_claim() -> list[str]:
    return [
        "measured TE is footprint/mRNA from one or a small number of ribo-seq studies and is already mRNA-normalized by construction",
        "the readout is condition-specific, cross-sectional, and non-causal",
        "positive S^{QT,meas} entries are codon-usage to measured-TE associations after controls, not mechanism claims",
        "this does not claim universal translation efficiency, elongation speed, protein abundance, protein function, or M^{QTP}",
        "agreement or disagreement with modeled-tAI is coordinate-pattern evidence only, not causal validation or causal falsification",
    ]


def future_required() -> list[str]:
    return [
        "matched ribo-seq TE across additional independent conditions and studies",
        "matched mRNA, ribosome footprint, and protein abundance measurements for the same genes before M^{QTP}",
        "synonymous perturbation or rescue assays before causal or mechanism statements",
        "held-out organisms or conditions before treating any coordinate pattern as stable",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for organism in ORGANISMS:
        required.append(f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local measured TE and CDS codon data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
        modeled = modeled_tai_comparison(repo)

        organism_results: dict[str, object] = {}
        loaded_organisms = 0
        loaded_data_actual: dict[str, object] = {}
        residualized_ok = True
        survival_ok = True
        powered_ok = True

        for organism in ORGANISMS:
            te_payload = load_json(repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(te_payload, dict) or not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} payloads must be JSON objects")
            x_rows, y_rows, z_rows, data_summary = measured_te_rows(
                cds_payload=cds_payload,
                te_payload=te_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            n_genes = len(x_rows)
            loaded_data_actual[organism] = {
                "n_genes_with_te_reported": te_payload.get("n_genes_with_te"),
                "ribosome_te_join_hit_rate": te_payload.get("join_hit_rate"),
                "n_cds_joined_reported": cds_payload.get("n_joined"),
                "n_genes_used": n_genes,
            }
            if n_genes >= MIN_GENES_PER_ORGANISM:
                loaded_organisms += 1
            if n_genes == 0:
                raise ValueError(f"{organism} has no usable genes after measured TE x CDS join")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            y_ss = frobenius2(y_tilde)
            explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
            r2_qt_measured = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
            sqt_matrix, raw_improvement, survivors = partial_r2_entries(x_tilde, y_tilde, q_names)
            measured_coordinates = sorted({str(item["q_coordinate"]) for item in survivors})
            modeled_contrast = compare_with_modeled(measured_coordinates, modeled)
            residual_df = n_genes - rank_z
            organism_powered = (
                n_genes >= MIN_GENES_PER_ORGANISM
                and residual_df > 10 * len(q_names)
                and rank_xtilde == len(q_names)
                and y_ss > SURVIVAL_EPS
                and r2_qt_measured < DEGENERATE_R2
            )
            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_genes and len(y_tilde) == n_genes
            survival_ok = survival_ok and math.isfinite(r2_qt_measured) and all(
                math.isfinite(value)
                for row in sqt_matrix.values()
                for value in row.values()
            )
            powered_ok = powered_ok and organism_powered

            organism_results[organism] = {
                **data_summary,
                "R2_QT_measured": r2_qt_measured,
                "sqt_measured_matrix": sqt_matrix,
                "raw_sse_improvement": raw_improvement,
                "surviving_coordinates": survivors,
                "modeled_tai_comparison": modeled_contrast,
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "q_coordinate_count": len(q_names),
                    "y_residual_energy": y_ss,
                    "explained_energy": explained,
                    "rank_tolerance": RANK_TOL,
                    "degenerate_R2_threshold": DEGENERATE_R2,
                    "powered_rank_sufficient": organism_powered,
                },
            }

        checks = [
            {
                "name": "measured_te_codon_loaded",
                "passed": loaded_organisms >= MIN_ORGANISMS,
                "actual": loaded_data_actual,
                "expected": f">= {MIN_ORGANISMS} organism with n >= {MIN_GENES_PER_ORGANISM} measured TE x CDS codon joined genes",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(len(row["sqt_measured_matrix"]) == 9 for row in organism_results.values() if isinstance(row, dict)),
                "actual": {"coordinates": q_names, "coordinate_count": len(q_projected)},
                "expected": "exactly the 9 B*_Q6 synonymous-residual coordinates reused from run_b_star_q6_translation_survival_powered.py",
            },
            {
                "name": "controls_Z_residualized",
                "passed": residualized_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "X_Q and log10 measured TE residualized within each organism against intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": powered_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism n >= 500, full 9-coordinate residual X rank, residual df comfortably above coordinate count, nonzero TE residual energy, and R2_QT_measured not saturated at 1.0",
            },
            {
                "name": "measured_te_survival_computed",
                "passed": survival_ok,
                "actual": {
                    organism: {
                        "R2_QT_measured": result["R2_QT_measured"],
                        "surviving_coordinate_count": len(result["surviving_coordinates"]),
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite per-organism R2_QT_measured and finite 9 x 1 S^{QT,meas} partial survival matrix",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "measured ribo-seq TE is mRNA-normalized but single/small-study, condition-specific, cross-sectional, non-causal, and not a mechanism claim",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; result is not promoted beyond measured TE cross-layer association"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Measured ribo-seq TE equals footprint/mRNA in the local source files, so the readout is already mRNA-normalized; this powered per-gene S^{QT,meas} reports codon residual survival against log10 measured TE after length, amino-acid composition, GC3, and M-density controls. The data are single/small-study, condition-specific, cross-sectional, and non-causal; the modeled-tAI contrast is a coordinate-pattern comparison only.",
                "readout": "log10(measured TE), where TE = ribosome footprint / mRNA from local ribosome_te_<organism>.json",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "coordinates": q_names,
                "positive_partial_r2_threshold": SURVIVAL_EPS,
                "modeled_tai_reference": modeled,
                "organisms": organism_results,
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered measured-TE survival input")


if __name__ == "__main__":
    main()

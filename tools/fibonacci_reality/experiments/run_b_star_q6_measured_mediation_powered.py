#!/usr/bin/env python3
"""Powered B*_Q6 statistical mediation using measured ribo-seq TE.

This experiment joins measured ribo-seq translation efficiency, measured
PAXdb abundance, and real CDS codon counts by protein_id. The decomposition is
cross-sectional statistical mediation only, not causal mediation.
"""

from __future__ import annotations

import json
import math
import pathlib
import subprocess
import sys
from typing import Any

from run_b_star_q6_measured_te_survival_powered import te_by_protein
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    frobenius2,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import (
    append_columns,
    coordinate_decomposition,
    incremental_r2,
    ols_coefficients,
    r2_from_design,
    summarize_routes,
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


EXPERIMENT_ID = "b_star_q6_measured_mediation_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_mediated_measured_protein_abundance.b_star_q6_measured_mqtp_powered"
CONJECTURE_ID = "q6.translation-mediated-measured.protein-abundance.cross-layer"

ORGANISMS = [
    "saccharomyces_cerevisiae",
    "escherichia_coli_k12_mg1655",
    "homo_sapiens",
    "danio_rerio",
]
MIN_PROTEINS_PER_ORGANISM = 500
MODELED_MEDIATION_EXPERIMENT = "run_b_star_q6_translation_mediation_powered.py"


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


def abundance_by_protein(payload: dict[str, object], organism: str) -> tuple[dict[str, float], dict[str, object]]:
    raw = payload.get("protein_abundance")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism} abundance payload must contain protein_abundance object")
    out: dict[str, float] = {}
    skipped = {
        "missing_protein_id": 0,
        "nonpositive_abundance": 0,
        "duplicate_protein_id": 0,
    }
    for protein_id, value in raw.items():
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        abundance = numeric(value, f"{organism}.protein_abundance.{protein_id}")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        if protein_id in out:
            skipped["duplicate_protein_id"] += 1
            continue
        out[protein_id] = abundance
    return out, {
        "n_abundance_proteins_reported": payload.get("n_proteins"),
        "paxdb_name": payload.get("paxdb_name"),
        "paxdb_publication_year": payload.get("paxdb_publication_year"),
        "n_valid_abundance_by_protein": len(out),
        "skipped_abundance_records": skipped,
    }


def measured_mediation_rows(
    *,
    cds_payload: dict[str, object],
    te_payload: dict[str, object],
    abundance_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    te_index, te_summary = te_by_protein(te_payload, organism)
    abundance_index, abundance_summary = abundance_by_protein(abundance_payload, organism)

    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_measured_te_match": 0,
        "no_abundance_match": 0,
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
        abundance = abundance_index.get(protein_id)
        if abundance is None:
            skipped["no_abundance_match"] += 1
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
        t_rows.append([math.log10(te_record["te"])])
        y_rows.append([math.log10(abundance)])

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
        **abundance_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined_three_way": len(x_rows),
        "skipped_cds_records": skipped,
    }
    return x_rows, t_rows, y_rows, z_rows, summary


def partial_r2_entries(
    *,
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
    readout: str,
    value_name: str,
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
        matrix[q_name] = {readout: partial}
        raw_improvement[q_name] = {readout: improvement}
        if partial > SURVIVAL_EPS and partial < DEGENERATE_R2:
            survivors.append({"q_coordinate": q_name, "readout": readout, value_name: partial})
    return matrix, raw_improvement, survivors


def bounded_decline_fraction(c_total: float, c_prime: float) -> tuple[float | None, float | None, str]:
    if abs(c_total) <= SURVIVAL_EPS:
        return None, None, "no_total_QP_signal"
    raw = (c_total - c_prime) / c_total
    decline = max(0.0, min(1.0, raw))
    if raw < 0.0:
        route = "suppression_or_negative_conditioning"
    elif raw <= SURVIVAL_EPS:
        route = "no_measured_decline_after_conditioning"
    elif raw < 0.5:
        route = "minor_statistical_mediation"
    else:
        route = "major_statistical_mediation"
    return raw, decline, route


def joint_measured_decomposition(
    *,
    x_tilde: list[list[float]],
    t_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    t_col = matrix_column(t_tilde, 0)
    xt_design = append_columns(x_tilde, t_tilde)
    c_total, explained_x, rank_x = r2_from_design(x_tilde, y_tilde)
    c_prime, direct_improvement, rank_xt, rank_t = incremental_r2(
        full_design=xt_design,
        base_design=t_tilde,
        response=y_tilde,
    )
    t_given_x, t_improvement, _, _ = incremental_r2(
        full_design=xt_design,
        base_design=x_tilde,
        response=y_tilde,
    )
    t_to_y, t_explained, _ = r2_from_design(t_tilde, y_tilde)
    x_to_t, x_to_t_explained, rank_x_for_t = r2_from_design(x_tilde, t_tilde)
    raw_fraction, decline_fraction, route = bounded_decline_fraction(c_total, c_prime)
    coeff_xt = ols_coefficients(xt_design, y_col) if rank_xt == len(q_names) + 1 else [0.0 for _ in range(len(q_names) + 1)]
    coeff_t_on_x = ols_coefficients(x_tilde, t_col) if rank_x == len(q_names) else [0.0 for _ in q_names]
    total_coeff = ols_coefficients(x_tilde, y_col) if rank_x == len(q_names) else [0.0 for _ in q_names]

    return {
        "decomposition_mode": "joint_9d_conditioning_on_measured_log10_TE_plus_per_coordinate_audit",
        "definition": "c is joint R2(Y_P ~ X_Q after Z); c_prime is incremental R2 of X_Q in Y_P ~ T_measured + X_Q; raw_fraction is (c - c_prime) / c; mediated_fraction_measured is the nonnegative decline proportion max(0, c - c_prime) / c.",
        "S_QP_joint_R2": c_total,
        "S_QT_measured_joint_R2": x_to_t,
        "c_total_R2_QP": c_total,
        "c_prime_direct_R2_QP_given_measured_T": c_prime,
        "indirect_R2_c_minus_c_prime": c_total - c_prime,
        "M_QTP_fraction_raw": raw_fraction,
        "mediated_fraction_measured": decline_fraction,
        "conditioning_route": route,
        "T_only_R2_to_Y": t_to_y,
        "T_incremental_R2_given_X": t_given_x,
        "X_to_T_R2_path_a_joint": x_to_t,
        "path_coefficients": {
            "a_beta_T_measured_on_X_by_coordinate": dict(zip(q_names, coeff_t_on_x)),
            "b_beta_Y_on_T_measured_given_X": coeff_xt[-1],
            "total_beta_Y_on_X_by_coordinate": dict(zip(q_names, total_coeff)),
            "direct_beta_Y_on_X_given_T_measured_by_coordinate": dict(zip(q_names, coeff_xt[:-1])),
        },
        "rank_diagnostics": {
            "rank_Xtilde": rank_x,
            "rank_Ttilde": rank_t,
            "rank_XTtilde": rank_xt,
            "rank_X_for_T": rank_x_for_t,
            "q_coordinate_count": len(q_names),
            "y_residual_energy": frobenius2(y_tilde),
            "t_residual_energy": frobenius2(t_tilde),
            "X_explained_energy_on_Y": explained_x,
            "X_direct_improvement_energy_given_T": direct_improvement,
            "T_explained_energy_on_Y": t_explained,
            "T_incremental_improvement_energy_given_X": t_improvement,
            "X_explained_energy_on_T": x_to_t_explained,
            "rank_tolerance": RANK_TOL,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
    }


def modeled_mediation_comparison(repo: pathlib.Path) -> dict[str, object]:
    script = repo / "tools/fibonacci_reality/experiments" / MODELED_MEDIATION_EXPERIMENT
    if not script.exists():
        return {"available": False, "reason": f"{MODELED_MEDIATION_EXPERIMENT} is not present"}
    completed = subprocess.run(
        [sys.executable, str(script)],
        check=False,
        cwd=str(script.parent),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if completed.returncode != 0:
        return {
            "available": False,
            "reason": "modeled mediation experiment did not pass",
            "returncode": completed.returncode,
            "stderr": completed.stderr.strip(),
        }
    try:
        payload = json.loads(completed.stdout.strip().splitlines()[-1])
    except Exception as exc:
        return {
            "available": False,
            "reason": f"could not parse modeled mediation JSON: {exc}",
            "stdout_prefix": completed.stdout[:500],
        }
    result = payload.get("result")
    if not isinstance(result, dict):
        return {"available": False, "reason": "modeled mediation JSON result is missing"}
    organisms = result.get("organisms")
    if not isinstance(organisms, dict):
        return {"available": False, "reason": "modeled mediation JSON organisms object is missing"}
    modeled: dict[str, object] = {}
    for organism in ORGANISMS:
        row = organisms.get(organism)
        if not isinstance(row, dict):
            continue
        modeled[organism] = {
            "modeled_M_QTP_fraction": row.get("M_QTP_fraction"),
            "modeled_c_total_R2_QP": row.get("c_total_R2_QP"),
            "modeled_c_prime_direct_R2_QP_given_T": row.get("c_prime_direct_R2_QP_given_T"),
            "modeled_indirect_R2_c_minus_c_prime": row.get("indirect_R2_c_minus_c_prime"),
        }
    return {
        "available": True,
        "experiment_id": payload.get("experiment_id"),
        "status": payload.get("status"),
        "comparison_boundary": "modeled tAI and measured ribo-seq TE are different translation readouts; agreement supports compatibility of statistical mediation patterns only, not causal validation.",
        "organisms": modeled,
        "cannot_claim": [
            "measured agreement with modeled tAI is not causal validation",
            "measured disagreement does not falsify translation biology by itself because datasets, conditions, and estimands differ",
        ],
    }


def compare_fraction(measured: float | None, raw: float | None, modeled: dict[str, object] | None) -> dict[str, object]:
    if modeled is None:
        return {
            "modeled_available": False,
            "interpretation": "modeled mediation comparison unavailable for this organism",
        }
    modeled_fraction = modeled.get("modeled_M_QTP_fraction")
    if not isinstance(modeled_fraction, (int, float)) or isinstance(modeled_fraction, bool):
        return {
            "modeled_available": False,
            "modeled_M_QTP_fraction": modeled_fraction,
            "interpretation": "modeled mediation fraction is unavailable or nonnumeric",
        }
    measured_value = None if measured is None else float(measured)
    raw_value = None if raw is None else float(raw)
    if measured_value is None:
        consistency = "measured_total_QP_signal_absent"
    elif measured_value >= 0.5 and float(modeled_fraction) >= 0.5:
        consistency = "both_major_statistical_mediation"
    elif measured_value < 0.5 and float(modeled_fraction) >= 0.5:
        consistency = "measured_weaker_than_modeled"
    elif measured_value >= 0.5 and float(modeled_fraction) < 0.5:
        consistency = "measured_stronger_than_modeled"
    else:
        consistency = "both_minor_or_null_statistical_mediation"
    return {
        "modeled_available": True,
        "modeled_M_QTP_fraction": float(modeled_fraction),
        "measured_mediated_fraction": measured_value,
        "measured_raw_fraction": raw_value,
        "difference_measured_minus_modeled": None if measured_value is None else measured_value - float(modeled_fraction),
        "consistency_class": consistency,
        "supports_modeled_major_mediation_pattern": consistency == "both_major_statistical_mediation",
        "interpretation": "fraction comparison is descriptive only; modeled tAI and measured TE are not the same estimand",
    }


def cannot_claim() -> list[str]:
    return [
        "M^{QTP,meas} here is a statistical mediation decomposition, not a causal mediation effect",
        "measured ribo-seq TE comes from one or a small number of local studies and is condition-specific",
        "the joined TE, PAXdb abundance, and CDS rows are cross-sectional and do not establish temporal ordering",
        "conditioning on measured TE is not a mechanism claim and does not isolate elongation, initiation, protein turnover, localization, PTM, folding, or pathway context",
        "positive measured mediated fractions do not establish synonymous-edit, perturbation, rescue, or mechanism_realization claims",
        "weak, null, or suppressive measured fractions are reported as measured-readout outcomes, not hidden or promoted",
    ]


def future_required() -> list[str]:
    return [
        "matched ribo-seq TE and PAXdb-like abundance in the same condition and biological material",
        "matched mRNA abundance controls beyond the TE ratio itself before separating abundance from expression-level confounding",
        "independent conditions and held-out studies for the same organisms",
        "synonymous perturbation or rescue assays before any causal mediation or mechanism statement",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def all_finite(values: list[object]) -> bool:
    for value in values:
        if not isinstance(value, (int, float)) or isinstance(value, bool) or not math.isfinite(float(value)):
            return False
    return True


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for organism in ORGANISMS:
        required.append(f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local measured TE, PAXdb abundance, and CDS codon data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
        modeled = modeled_mediation_comparison(repo)
        modeled_by_organism = modeled.get("organisms") if isinstance(modeled.get("organisms"), dict) else {}

        organism_results: dict[str, object] = {}
        joined_actual: dict[str, object] = {}
        residualized_ok = True
        rank_ok = True
        mediation_ok = True
        fraction_ok = True

        for organism in ORGANISMS:
            te_payload = load_json(repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
            abundance_payload = load_json(repo / f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(te_payload, dict) or not isinstance(abundance_payload, dict) or not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} payloads must be JSON objects")
            x_rows, t_rows, y_rows, z_rows, data_summary = measured_mediation_rows(
                cds_payload=cds_payload,
                te_payload=te_payload,
                abundance_payload=abundance_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            n_proteins = len(x_rows)
            if n_proteins == 0:
                raise ValueError(f"{organism} has no usable proteins after measured TE x abundance x codon join")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            t_tilde, _ = residualize(t_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            joint = joint_measured_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
            per_coordinate = coordinate_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
            route_summary = summarize_routes(per_coordinate)
            sqt_matrix, sqt_raw, sqt_survivors = partial_r2_entries(
                x_tilde=x_tilde,
                y_tilde=t_tilde,
                q_names=q_names,
                readout="log10_measured_te",
                value_name="S_QT_measured",
            )
            sqp_matrix, sqp_raw, sqp_survivors = partial_r2_entries(
                x_tilde=x_tilde,
                y_tilde=y_tilde,
                q_names=q_names,
                readout="log10_abundance_ppm",
                value_name="S_QP",
            )
            residual_df = n_proteins - rank_z
            rank_diag = joint["rank_diagnostics"]
            measured_fraction = joint["mediated_fraction_measured"]
            raw_fraction = joint["M_QTP_fraction_raw"]
            modeled_row = modeled_by_organism.get(organism) if isinstance(modeled_by_organism, dict) else None
            modeled_contrast = compare_fraction(
                float(measured_fraction) if isinstance(measured_fraction, (int, float)) else None,
                float(raw_fraction) if isinstance(raw_fraction, (int, float)) else None,
                modeled_row if isinstance(modeled_row, dict) else None,
            )

            finite_joint = all_finite(
                [
                    joint["S_QP_joint_R2"],
                    joint["S_QT_measured_joint_R2"],
                    joint["c_total_R2_QP"],
                    joint["c_prime_direct_R2_QP_given_measured_T"],
                    joint["indirect_R2_c_minus_c_prime"],
                    joint["T_only_R2_to_Y"],
                    joint["T_incremental_R2_given_X"],
                    joint["X_to_T_R2_path_a_joint"],
                ]
            )
            organism_fraction_ok = (
                isinstance(measured_fraction, (int, float))
                and not isinstance(measured_fraction, bool)
                and math.isfinite(float(measured_fraction))
                and 0.0 <= float(measured_fraction) <= 1.0
            )
            organism_powered = (
                n_proteins >= MIN_PROTEINS_PER_ORGANISM
                and residual_df > 10 * (len(q_names) + 1)
                and int(rank_diag["rank_Xtilde"]) == len(q_names)
                and int(rank_diag["rank_Ttilde"]) == 1
                and int(rank_diag["rank_XTtilde"]) == len(q_names) + 1
                and float(rank_diag["y_residual_energy"]) > SURVIVAL_EPS
                and float(rank_diag["t_residual_energy"]) > SURVIVAL_EPS
                and float(joint["c_total_R2_QP"]) > SURVIVAL_EPS
                and float(joint["c_total_R2_QP"]) < DEGENERATE_R2
                and float(joint["S_QT_measured_joint_R2"]) < DEGENERATE_R2
            )

            joined_actual[organism] = {
                "n_valid_te_by_protein": data_summary["n_valid_te_by_protein"],
                "n_valid_abundance_by_protein": data_summary["n_valid_abundance_by_protein"],
                "n_cds_joined_reported": data_summary["n_cds_joined_reported"],
                "n_joined_three_way": n_proteins,
            }
            residualized_ok = residualized_ok and rank_z > 0 and len(x_tilde) == n_proteins and len(t_tilde) == n_proteins and len(y_tilde) == n_proteins
            rank_ok = rank_ok and organism_powered
            mediation_ok = mediation_ok and finite_joint
            fraction_ok = fraction_ok and organism_fraction_ok

            organism_results[organism] = {
                **data_summary,
                "S_QT_measured": joint["S_QT_measured_joint_R2"],
                "S_QP": joint["S_QP_joint_R2"],
                "mediated_fraction_measured": joint["mediated_fraction_measured"],
                "M_QTP_fraction_raw": joint["M_QTP_fraction_raw"],
                "modeled_mediation_comparison": modeled_contrast,
                "joint_decomposition": joint,
                "per_coordinate_decomposition": per_coordinate,
                "coordinate_route_summary": route_summary,
                "sqt_measured_matrix": sqt_matrix,
                "sqt_measured_raw_improvement": sqt_raw,
                "sqt_measured_surviving_coordinates": sqt_survivors,
                "sqp_matrix": sqp_matrix,
                "sqp_raw_improvement": sqp_raw,
                "sqp_surviving_coordinates": sqp_survivors,
                "rank_diagnostics": {
                    **rank_diag,
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "powered_rank_sufficient": organism_powered,
                    "mediated_fraction_measured_in_unit_interval": organism_fraction_ok,
                },
            }

        checks = [
            {
                "name": "measured_te_abundance_codon_joined",
                "passed": all(
                    isinstance(row["n_joined_three_way"], int) and int(row["n_joined_three_way"]) >= MIN_PROTEINS_PER_ORGANISM
                    for row in joined_actual.values()
                    if isinstance(row, dict)
                ) and len(joined_actual) == len(ORGANISMS),
                "actual": joined_actual,
                "expected": f"each organism has measured TE x PAXdb abundance x CDS codon protein_id join n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals_computed",
                "passed": len(q_projected) == 9 and all(
                    len(row["sqt_measured_matrix"]) == 9 and len(row["sqp_matrix"]) == 9
                    for row in organism_results.values()
                    if isinstance(row, dict)
                ),
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
                "expected": "X_Q, log10 measured TE, and log10 abundance residualized within each organism against intercept, log length, 20 amino-acid composition controls, GC3, and M-density",
            },
            {
                "name": "powered_rank_sufficient",
                "passed": rank_ok,
                "actual": {
                    organism: result["rank_diagnostics"]
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "per-organism n >= 500, full 9-coordinate residual X rank, full X+T rank, residual df comfortably above controls plus coordinates, nonzero T/Y residual energy, and no R2 saturation at 1.0",
            },
            {
                "name": "measured_mediation_computed",
                "passed": mediation_ok and fraction_ok,
                "actual": {
                    organism: {
                        "S_QT_measured": result["S_QT_measured"],
                        "S_QP": result["S_QP"],
                        "mediated_fraction_measured": result["mediated_fraction_measured"],
                        "M_QTP_fraction_raw": result["M_QTP_fraction_raw"],
                        "mediated_fraction_measured_in_unit_interval": result["rank_diagnostics"]["mediated_fraction_measured_in_unit_interval"],
                    }
                    for organism, result in organism_results.items()
                    if isinstance(result, dict)
                },
                "expected": "finite S^{QT,meas}, S^{QP}, raw M^{QTP}, and nonnegative measured decline fraction in [0, 1] for every organism; weak or null values still pass if powered",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "statistical mediation only; measured TE is single/small-study, condition-specific, cross-sectional, non-causal, and not a mechanism claim",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "failed"
        reason = None
        if status != "passed":
            reason = "one or more honest gates failed; measured M^{QTP} is not promoted"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "Codon residual to PAXdb protein-abundance association is decomposed by conditioning on measured ribo-seq log10(TE), not modeled tAI, across yeast, E. coli, human, and danio. This is a powered cross-sectional statistical mediation decomposition and comparison to the modeled-tAI mediation result; it is non-causal and not a mechanism claim.",
                "readout_T": "log10(measured TE), where TE = ribosome footprint / mRNA from local ribosome_te_<organism>.json",
                "readout_Y": "log10(abundance_ppm) from local proteomics_abundance_<organism>.json joined by protein_id",
                "decomposition_mode": "joint 9-dimensional X_Q mediation scalar with per-coordinate decomposition audit",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "modeled_mediation_reference": modeled,
                "coordinates": q_names,
                "organisms": organism_results,
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable powered measured-TE mediation input")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Execution-vs-selection joint decomposition for yeast B*_Q6 abundance residuals."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from datetime import datetime, timezone
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_b_star_q6_context_lift_powered as context_lift
import run_b_star_q6_finite_state_dwell_transducer_powered as dwell_transducer
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_joint_te_stability_mediation_powered import yeast_join_keys
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    frobenius2,
    matrix_column,
    orthonormal_basis_from_columns,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_residual_exec_selection_joint_powered"
CLAIM_ID = "h3.cross_layer_relation.execution_selection_decomposition.b_star_q6_residual_exec_selection_joint_powered"

ORGANISM = "saccharomyces_cerevisiae"
ORGANISM_LABEL = "Saccharomyces cerevisiae"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
CDS_ABUNDANCE_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
CODON_USAGE_PATH = "tools/bio_reality/data/codon_usage_saccharomyces_cerevisiae.json"
RIBOSOME_TE_PATH = "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json"
MRNA_STABILITY_PATH = "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json"
TURNOVER_PATH = "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json"

FOLD_COUNT = 5
PERMUTATION_COUNT = 240
RIDGE = 1e-10
EPS = 1e-12
LAMBDA_DL = residual_dictionary.LAMBDA_DL
SEED = "sha256:b_star_q6_residual_exec_selection_joint_powered:deterministic"
STARTED_AT = datetime.now(timezone.utc).isoformat(timespec="seconds")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **kw: object) -> None:
    checks = kw.get("checks")
    if not isinstance(checks, list):
        checks = []
    result = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    result.update(kw)
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks,
        "result": result,
        "started_at": STARTED_AT,
        "completed_at": now_iso(),
    }
    print(json.dumps(payload, sort_keys=False, ensure_ascii=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    center = mean(values)
    return sum((value - center) * (value - center) for value in values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def single_column_matrix(values: list[float]) -> list[list[float]]:
    return [[value] for value in values]


def standardize(values: list[float]) -> tuple[list[float], dict[str, float]]:
    if not values:
        return [], {"mean": 0.0, "sd": 1.0}
    center = mean(values)
    sd = math.sqrt(variance(values))
    if sd <= EPS:
        sd = 1.0
    return [(value - center) / sd for value in values], {"mean": center, "sd": sd}


def ranks(values: list[float]) -> list[float]:
    pairs = sorted((value, index) for index, value in enumerate(values))
    out = [0.0 for _ in values]
    cursor = 0
    while cursor < len(pairs):
        end = cursor + 1
        while end < len(pairs) and pairs[end][0] == pairs[cursor][0]:
            end += 1
        rank = 0.5 * (cursor + end - 1) + 1.0
        for pos in range(cursor, end):
            out[pairs[pos][1]] = rank
        cursor = end
    return out


def pearson(left: list[float], right: list[float]) -> float:
    if len(left) != len(right) or not left:
        return 0.0
    mx = mean(left)
    my = mean(right)
    sx = sum((value - mx) * (value - mx) for value in left)
    sy = sum((value - my) * (value - my) for value in right)
    if sx <= EPS or sy <= EPS:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in zip(left, right)) / math.sqrt(sx * sy)


def spearman(left: list[float], right: list[float]) -> float:
    return pearson(ranks(left), ranks(right))


def residualize_vector_by_basis(values: list[float], basis: list[list[float]]) -> list[float]:
    out = list(values)
    for q in basis:
        coeff = sum(out[index] * q[index] for index in range(len(out)))
        if coeff == 0.0:
            continue
        for index in range(len(out)):
            out[index] -= coeff * q[index]
    return out


def partial_spearman(predictor: list[float], target: list[float], base_design: list[list[float]]) -> float:
    predictor_rank = ranks(predictor)
    target_rank = ranks(target)
    basis = orthonormal_basis_from_columns(base_design)
    predictor_residual = residualize_vector_by_basis(predictor_rank, basis)
    target_residual = residualize_vector_by_basis(target_rank, basis)
    return pearson(predictor_residual, target_residual)


def project_vector(design: list[list[float]], target: list[float]) -> tuple[list[float], float, int, list[list[float]]]:
    basis = orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = sum(target[index] * q[index] for index in range(len(target)))
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected), len(basis), basis


def prepare_models(design: list[list[float]]) -> list[dict[str, object]]:
    n = len(design)
    fold_indices = context_lift.folds_for_n(n, FOLD_COUNT)
    models: list[dict[str, object]] = []
    for test in fold_indices:
        test_set = set(test)
        train = [index for index in range(n) if index not in test_set]
        models.append(context_lift.prepare_cv_model(design, train, test))
    return models


def cv_r2_for_target(target: list[float], models: list[dict[str, object]]) -> float:
    total_ss = 0.0
    sse = 0.0
    for model in models:
        test_indices = model["test_indices"]
        if not isinstance(test_indices, list):
            raise ValueError("CV model lacks test indices")
        predictions = context_lift.predict_cv(model, target)
        for local_index, row_index in enumerate(test_indices):
            observed = target[int(row_index)]
            residual = observed - predictions[local_index]
            total_ss += observed * observed
            sse += residual * residual
    if total_ss <= EPS:
        return 0.0
    return 1.0 - sse / total_ss


def cv_delta(base_design: list[list[float]], full_design: list[list[float]], target: list[float]) -> dict[str, float]:
    base_models = prepare_models(base_design)
    full_models = prepare_models(full_design)
    base_r2 = cv_r2_for_target(target, base_models)
    full_r2 = cv_r2_for_target(target, full_models)
    delta = context_lift.cv_delta_r2_for_target(
        target=target,
        base_models=base_models,
        full_models=full_models,
    )
    return {"base_r2": base_r2, "full_r2": full_r2, "delta_r2": delta}


def direct_q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    aa_order = standard_amino_acids(code, codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
    return {
        "code": code,
        "codons": codons,
        "aa_order": aa_order,
        "q_projected": q_projected,
        "q_names": list(q_projected),
        "q_support": q_support,
    }


def codon_counts_from_record(record: dict[str, object], codons: list[str]) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError("joined CDS row lacks codon_counts")
    out = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon not in out:
            continue
        if not finite(raw_count):
            raise ValueError("codon count is not finite")
        value = float(raw_count)
        if value < 0.0 or int(value) != value:
            raise ValueError("codon count is not a non-negative integer")
        out[codon] += int(value)
    return out


def protein_to_orf_from_item(protein_id: str, item: dict[str, object]) -> str | None:
    _pid, orf, error = yeast_join_keys(item)
    if not error and isinstance(orf, str) and orf:
        return orf
    if protein_id.startswith("4932."):
        suffix = protein_id.split(".", 1)[1]
        if suffix:
            return suffix
    return None


def direct_protein_rows(repo: pathlib.Path, context: dict[str, object]) -> tuple[dict[str, dict[str, object]], dict[str, str], dict[str, object]]:
    payload = load_json(repo / CDS_ABUNDANCE_PATH)
    if not isinstance(payload, dict) or not isinstance(payload.get("joined"), list):
        raise ValueError("yeast CDS abundance payload must contain joined list")
    codons = context["codons"]
    code = context["code"]
    aa_order = context["aa_order"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    q_support = context["q_support"]
    if not isinstance(codons, list) or not isinstance(code, dict) or not isinstance(aa_order, list):
        raise ValueError("direct B*_Q6 context malformed")
    if not isinstance(q_projected, dict) or not isinstance(q_names, list) or not isinstance(q_support, set):
        raise ValueError("direct B*_Q6 context malformed")

    rows: dict[str, dict[str, object]] = {}
    protein_to_orf: dict[str, str] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "duplicate_protein_id": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
        "empty_amino_acid_counts": 0,
    }
    for row_index, item in enumerate(payload["joined"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if protein_id in rows:
            skipped["duplicate_protein_id"] += 1
            continue
        abundance = item.get("abundance_ppm")
        cds_len_nt = item.get("cds_len_nt")
        if not finite(abundance) or float(abundance) <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        if not finite(cds_len_nt) or float(cds_len_nt) <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_from_record(item, [str(codon) for codon in codons])
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {str(codon): counts[str(codon)] / total for codon in codons}
        x_row = [
            sum(frequencies[str(codon)] * float(q_projected[str(name)][str(codon)]) for codon in codons)
            / math.sqrt(sum(float(q_projected[str(name)][str(codon)]) ** 2 for codon in codons))
            for name in q_names
        ]
        aa_counts = {str(aa): 0 for aa in aa_order}
        for codon in codons:
            aa_counts[str(code[str(codon)])] += counts[str(codon)]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            skipped["empty_amino_acid_counts"] += 1
            continue
        gc3 = sum(counts[str(codon)] for codon in codons if str(codon)[2] in {"G", "C"}) / total
        m_density = sum(counts[str(codon)] for codon in q_support) / total
        z_row = [1.0, math.log(float(cds_len_nt))] + [aa_counts[str(aa)] / aa_total for aa in aa_order] + [gc3, m_density]
        rows[protein_id] = {
            "protein_id": protein_id,
            "x": x_row,
            "p": [math.log10(float(abundance))],
            "z": z_row,
        }
        orf = protein_to_orf_from_item(protein_id, item)
        if orf is not None:
            protein_to_orf[protein_id] = orf
    return rows, protein_to_orf, {
        "n_cds_joined_reported": payload.get("n_joined"),
        "cds_join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_direct_rows": len(rows),
        "n_protein_to_orf": len(protein_to_orf),
        "skipped_cds_records": skipped,
    }


def active_design_state(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
) -> dict[str, object]:
    selected_rows = [rows[protein_id] for protein_id in row_ids]
    z_rows = matrix_rows(selected_rows, "z")
    x_rows = matrix_rows(selected_rows, "x")
    p_rows = matrix_rows(selected_rows, "p")
    x_e, rank_z = residualize(x_rows, z_rows)
    p_e, _ = residualize(p_rows, z_rows)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_norm2, rank_q, q_basis = project_vector(x_e, p_col)
    p_norm2 = vector_norm2(p_col)
    if p_q_norm2 <= EPS or p_norm2 <= EPS:
        raise ValueError("P_Q or residualized protein abundance has zero energy")
    return {
        "row_ids": row_ids,
        "selected_rows": selected_rows,
        "z_rows": z_rows,
        "x_e": x_e,
        "p_e": p_e,
        "p_col": p_col,
        "P_Q": p_q,
        "P_Q_norm2": p_q_norm2,
        "P_residual_norm2": p_norm2,
        "R2_QP": p_q_norm2 / p_norm2,
        "rank_Z": rank_z,
        "rank_Q_e": rank_q,
        "q_basis": q_basis,
    }


def fit_order2_state_means(data: dict[str, object]) -> tuple[dict[int, float], float, dict[str, object]]:
    context = data["context"]
    if not isinstance(context, dict):
        raise ValueError("dwell context malformed")
    q_label_by_codon = context["q_label_by_codon"]
    if not isinstance(q_label_by_codon, dict):
        raise ValueError("q label map malformed")
    sequences = data["full_sequences"]
    event_positions = data["event_positions_by_gene"]
    y_by_gene = data["residual_y_by_gene"]
    if not isinstance(sequences, list) or not isinstance(event_positions, list) or not isinstance(y_by_gene, list):
        raise ValueError("dwell event stream malformed")
    observed_labels, _feature_by_label = dwell_transducer.head_labels_and_features(
        sequences=sequences,  # type: ignore[arg-type]
        event_positions_by_gene=event_positions,  # type: ignore[arg-type]
        q_label_by_codon=q_label_by_codon,  # type: ignore[arg-type]
        q_by_codon=context["q_by_codon"],  # type: ignore[arg-type]
    )
    stats = dwell_transducer.build_state_stats_by_order(
        observed_labels,
        event_positions,  # type: ignore[arg-type]
        y_by_gene,  # type: ignore[arg-type]
    )[2]
    totals: dict[int, list[float]] = {}
    total_count = 0
    total_sum = 0.0
    for gene_stats in stats:
        for key, (count, y_sum, _sumsq) in gene_stats.items():
            row = totals.setdefault(int(key), [0.0, 0.0])
            row[0] += int(count)
            row[1] += float(y_sum)
            total_count += int(count)
            total_sum += float(y_sum)
    fallback = total_sum / total_count if total_count > 0 else 0.0
    means = {
        key: values[1] / values[0]
        for key, values in totals.items()
        if values[0] > 0
    }
    return means, fallback, {
        "context_order": 2,
        "state_count": len(means),
        "observation_count": total_count,
        "fallback_mean": fallback,
    }


def local_dwell_by_orf(repo: pathlib.Path) -> tuple[dict[str, float], dict[str, object]]:
    data = dwell_transducer.load_event_stream(repo)
    genes = data["genes"]
    sequences = data["full_sequences"]
    if not isinstance(genes, list) or not isinstance(sequences, list):
        raise ValueError("dwell event stream lacks genes/sequences")
    means, fallback, state_summary = fit_order2_state_means(data)
    q_label_by_codon = data["context"]["q_label_by_codon"]  # type: ignore[index]
    out: dict[str, float] = {}
    skipped_unknown = 0
    length_counts: list[int] = []
    for gene_id, seq in zip(genes, sequences):
        if not isinstance(gene_id, str) or not isinstance(seq, list):
            continue
        total_dwell = 0.0
        previous = dwell_transducer.BOS
        used = 0
        for raw_codon in seq:
            codon = dna_to_rna(str(raw_codon))
            raw_label = q_label_by_codon.get(codon)
            current = dwell_transducer.UNK if raw_label is None else int(raw_label) + 2
            key = previous * dwell_transducer.STATE_BASE + current
            total_dwell += means.get(key, fallback)
            previous = current
            used += 1
            if raw_label is None:
                skipped_unknown += 1
        if used > 0:
            out[gene_id] = -total_dwell
            length_counts.append(used)
    return out, {
        "status": "computed",
        "definition": "k_tl_local_g = -sum_t d_hat_t using full-sequence order-2 finite-state dwell means fitted from residualized 5prime occupancy",
        "n_orf_with_dwell": len(out),
        "event_stream_gene_count": len(genes),
        "state_fit": state_summary,
        "alignment_summary": data.get("alignment_summary"),
        "control_summary": data.get("control_summary"),
        "min_cds_codons_scored": min(length_counts) if length_counts else 0,
        "median_cds_codons_scored": sorted(length_counts)[len(length_counts) // 2] if length_counts else 0,
        "max_cds_codons_scored": max(length_counts) if length_counts else 0,
        "unknown_codon_or_stop_positions_scored_by_fallback_label": skipped_unknown,
    }


def codon_selection_probabilities(repo: pathlib.Path, code: dict[str, str]) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(repo / CODON_USAGE_PATH)
    if not isinstance(payload, dict) or not isinstance(payload.get("codon_counts"), dict):
        raise ValueError("codon usage payload lacks codon_counts")
    counts_raw = payload["codon_counts"]
    family_totals: dict[str, float] = {}
    codon_counts: dict[str, float] = {}
    skipped = {"unknown_or_stop": 0, "nonfinite_or_negative": 0}
    for raw_codon, raw_count in counts_raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon not in code or code[codon] == "*":
            skipped["unknown_or_stop"] += 1
            continue
        if not finite(raw_count) or float(raw_count) < 0.0:
            skipped["nonfinite_or_negative"] += 1
            continue
        value = float(raw_count)
        codon_counts[codon] = codon_counts.get(codon, 0.0) + value
        family_totals[code[codon]] = family_totals.get(code[codon], 0.0) + value
    probabilities: dict[str, float] = {}
    for codon, count in codon_counts.items():
        total = family_totals.get(code[codon], 0.0)
        if total > 0.0:
            probabilities[codon] = count / total
    return probabilities, {
        "status": "computed",
        "codon_usage_path": CODON_USAGE_PATH,
        "source_name": payload.get("source_name"),
        "kazusa_taxid": payload.get("kazusa_taxid"),
        "kazusa_cds_records": payload.get("kazusa_cds_records"),
        "n_codons_with_probabilities": len(probabilities),
        "skipped_codon_usage_records": skipped,
        "definition": "P_o(c|a) is organism codon count divided by synonymous amino-acid family total; E_sel_g=sum_t -log P_o(c_t|a_t).",
    }


def selection_potential_by_orf(
    ordered_by_orf: dict[str, list[str]],
    probabilities: dict[str, float],
    code: dict[str, str],
) -> tuple[dict[str, float], dict[str, object]]:
    out: dict[str, float] = {}
    skipped = {"no_sense_codons": 0, "unknown_or_stop": 0, "missing_probability": 0}
    lengths: list[int] = []
    for orf, sequence in ordered_by_orf.items():
        energy = 0.0
        used = 0
        for raw_codon in sequence:
            codon = dna_to_rna(raw_codon)
            aa = code.get(codon)
            if aa is None or aa == "*":
                skipped["unknown_or_stop"] += 1
                continue
            prob = probabilities.get(codon)
            if prob is None or prob <= 0.0:
                skipped["missing_probability"] += 1
                continue
            energy += -math.log(prob)
            used += 1
        if used <= 0:
            skipped["no_sense_codons"] += 1
            continue
        out[orf] = energy
        lengths.append(used)
    return out, {
        "status": "computed",
        "n_orf_with_selection_potential": len(out),
        "min_sense_codons_scored": min(lengths) if lengths else 0,
        "median_sense_codons_scored": sorted(lengths)[len(lengths) // 2] if lengths else 0,
        "max_sense_codons_scored": max(lengths) if lengths else 0,
        "skipped_selection_positions_or_records": skipped,
    }


def measured_te_by_protein(repo: pathlib.Path) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(repo / RIBOSOME_TE_PATH)
    if not isinstance(payload, dict) or not isinstance(payload.get("genes"), list):
        raise ValueError("ribosome TE payload lacks genes list")
    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_protein_id": 0, "nonpositive_te": 0, "duplicate": 0}
    for item in payload["genes"]:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        te = item.get("te")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if protein_id in out:
            skipped["duplicate"] += 1
            continue
        if not finite(te) or float(te) <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        out[protein_id] = math.log10(float(te))
    return out, {
        "status": "computed",
        "n_measured_te": len(out),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "skipped_te_records": skipped,
    }


def measured_dictionary_by_protein(repo: pathlib.Path) -> tuple[dict[str, list[float]], dict[str, object]]:
    te, te_summary = measured_te_by_protein(repo)
    stability_payload = load_json(repo / MRNA_STABILITY_PATH)
    turnover_payload = load_json(repo / TURNOVER_PATH)
    stability: dict[str, float] = {}
    if isinstance(stability_payload, dict) and isinstance(stability_payload.get("records"), list):
        for item in stability_payload["records"]:
            if not isinstance(item, dict):
                continue
            orf = item.get("Syst")
            value = item.get("thalf")
            if isinstance(orf, str) and orf and finite(value) and float(value) > 0.0:
                stability[f"4932.{orf}"] = math.log10(float(value))
    turnover: dict[str, float] = {}
    raw_turnover = turnover_payload.get("protein_turnover") if isinstance(turnover_payload, dict) else None
    if isinstance(raw_turnover, dict):
        for protein_id, value in raw_turnover.items():
            if isinstance(protein_id, str) and finite(value) and float(value) > 0.0:
                turnover[protein_id] = math.log10(float(value))
    out: dict[str, list[float]] = {}
    for protein_id, te_value in te.items():
        s_value = stability.get(protein_id)
        u_value = turnover.get(protein_id)
        if s_value is None or u_value is None:
            continue
        out[protein_id] = [te_value, s_value, u_value]
    return out, {
        "status": "computed",
        "dictionary": ["measured_te", "mrna_stability", "turnover"],
        "n_measured_te": len(te),
        "n_mrna_stability": len(stability),
        "n_turnover": len(turnover),
        "n_three_way_dictionary": len(out),
        "te_summary": te_summary,
    }


def dictionary_compression_on_active_set(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    dictionary: dict[str, list[float]],
) -> dict[str, object]:
    active = [protein_id for protein_id in row_ids if protein_id in dictionary]
    if len(active) < MIN_PROTEINS_PER_ORGANISM:
        return {"status": "needs_data", "n_join": len(active), "reason": "measured dictionary join below gate"}
    state = active_design_state(rows=rows, row_ids=active)
    selected_rows = state["selected_rows"]
    z_rows = state["z_rows"]
    if not isinstance(selected_rows, list) or not isinstance(z_rows, list):
        raise ValueError("active state malformed for dictionary compression")
    z_basis = orthonormal_basis_from_columns(z_rows)
    d_rows = [dictionary[protein_id] for protein_id in active]
    d_e = residual_dictionary.residualize_with_basis(d_rows, z_basis)
    p_q = state["P_Q"]
    if not isinstance(p_q, list):
        raise ValueError("P_Q malformed for dictionary compression")
    _projection, projected_norm2, rank_d, _basis_d = project_vector(d_e, p_q)
    p_q_norm2 = float(state["P_Q_norm2"])
    coverage = projected_norm2 / p_q_norm2 if p_q_norm2 > EPS else 0.0
    return {
        "status": "computed",
        "D_o": ["measured_te", "mrna_stability", "turnover"],
        "n_join": len(active),
        "base_n": len(row_ids),
        "coverage": max(0.0, min(1.0, coverage)),
        "compressibility_C_star": max(0.0, min(1.0, coverage)),
        "unresolved_after_dictionary": max(0.0, min(1.0, 1.0 - coverage)),
        "rank_D_e": rank_d,
        "rank_Q_e": state["rank_Q_e"],
        "P_Q_norm2": p_q_norm2,
        "projected_norm2": projected_norm2,
        "definition": "C* is orthogonal projection coverage of P_Q by Z-residualized measured_te, mrna_stability, and turnover on their active join.",
    }


def residual_dictionary_compression_anchor(repo: pathlib.Path) -> dict[str, object]:
    context = residual_dictionary.q6_context(repo)
    yeast_config = next(config for config in residual_dictionary.ORGANISMS if config["key"] == ORGANISM)
    built = residual_dictionary.base_rows(repo=repo, context=context, config=yeast_config)
    if built.get("status") != "computed":
        return {"status": "needs_data", "reason": built.get("reason"), "data_summary": built}
    rows = built.get("rows")
    if not isinstance(rows, dict):
        raise ValueError("residual dictionary base rows malformed")
    residual_dictionary.attach_h_readouts(repo, ORGANISM, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    active = [
        protein_id
        for protein_id in base_ids
        if isinstance(rows[protein_id].get("t"), list)
        and isinstance(rows[protein_id].get("s"), list)
        and isinstance(rows[protein_id].get("h"), dict)
        and "turnover" in rows[protein_id]["h"]  # type: ignore[operator]
    ]
    if len(active) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "base_n": len(base_ids),
            "n_join": len(active),
            "reason": "residual dictionary three-readout join below gate",
        }
    selected_rows = [rows[protein_id] for protein_id in active]
    z_rows = matrix_rows(selected_rows, "z")
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_e = residual_dictionary.residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residual_dictionary.residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    p_q, p_q_norm2, rank_q = residual_dictionary.project_vector(x_e, matrix_column(p_e, 0))
    if p_q_norm2 <= EPS:
        raise ValueError("residual dictionary P_Q has zero energy")
    d_rows: list[list[float]] = []
    for row in selected_rows:
        h_map = row["h"]
        if not isinstance(h_map, dict):
            raise ValueError("residual dictionary h map malformed")
        d_rows.append(list(row["t"]) + list(row["s"]) + list(h_map["turnover"]))  # type: ignore[arg-type]
    d_e = residual_dictionary.residualize_with_basis(d_rows, z_basis)
    _projected, projected_norm2, rank_d = residual_dictionary.project_vector(d_e, p_q)
    coverage = projected_norm2 / p_q_norm2
    return {
        "status": "computed",
        "D_o": ["measured_te", "mrna_stability", "turnover"],
        "n_join": len(active),
        "base_n": len(base_ids),
        "coverage": max(0.0, min(1.0, coverage)),
        "compressibility_C_star": max(0.0, min(1.0, coverage)),
        "unresolved_after_dictionary": max(0.0, min(1.0, 1.0 - coverage)),
        "rank_D_e": rank_d,
        "rank_Q_e": rank_q,
        "rank_Z": len(z_basis),
        "P_Q_norm2": p_q_norm2,
        "projected_norm2": projected_norm2,
        "control_scope": "residual_dictionary base_rows controls include measured mRNA abundance and the yeast stability-required base join",
        "definition": "C* anchor: coverage of residual_dictionary P_Q by Z-residualized measured_te, mrna_stability, and turnover.",
    }


def in_sample_delta(base_design: list[list[float]], full_design: list[list[float]], target: list[float]) -> dict[str, object]:
    target_norm2 = vector_norm2(target)
    if target_norm2 <= EPS:
        return {"delta": 0.0, "base_r2": 0.0, "full_r2": 0.0, "base_rank": 0, "full_rank": 0}
    base_basis = orthonormal_basis_from_columns(base_design)
    full_basis = orthonormal_basis_from_columns(full_design)
    base_energy = sum(sum(target[index] * q[index] for index in range(len(target))) ** 2 for q in base_basis)
    full_energy = sum(sum(target[index] * q[index] for index in range(len(target))) ** 2 for q in full_basis)
    base_r2 = max(0.0, min(1.0, base_energy / target_norm2))
    full_r2 = max(0.0, min(1.0, full_energy / target_norm2))
    return {
        "delta": full_r2 - base_r2,
        "base_r2": base_r2,
        "full_r2": full_r2,
        "base_rank": len(base_basis),
        "full_rank": len(full_basis),
    }


def permutation_null(
    *,
    target: list[float],
    base_models: list[dict[str, object]],
    full_models: list[dict[str, object]],
) -> dict[str, object]:
    values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(target), f"{SEED}|joint-target-permutation|trial={trial}")
        permuted = [target[permutation[index]] for index in range(len(target))]
        values.append(
            context_lift.cv_delta_r2_for_target(
                target=permuted,
                base_models=base_models,
                full_models=full_models,
            )
        )
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_delta_r2": percentile_nearest_rank(values, 0.95),
        "null_mean_delta_r2": mean(values),
        "null_min_delta_r2": min(values) if values else 0.0,
        "null_max_delta_r2": max(values) if values else 0.0,
        "deterministic_seed": f"{SEED}|joint-target-permutation|trial|index|n",
        "null_model": "target-permutation with fixed base and joint execution-selection designs and the same deterministic 5 folds",
    }


def verdict_for(
    *,
    n: int,
    r2_qp: float,
    delta_joint: float,
    null95: float,
    dl_pass: bool,
) -> str:
    if n < 1000 or not (0.25 <= r2_qp <= 0.34):
        return "needs_data"
    if delta_joint > null95 and dl_pass and delta_joint >= 0.01:
        return "crosses_boundary"
    if delta_joint > null95 and dl_pass:
        return "bounded_descriptor_only"
    return "composition_artifact"


def main() -> None:
    repo = pathlib.Path.cwd()
    required = [
        repo / ORDERED_CDS_PATH,
        repo / CDS_ABUNDANCE_PATH,
        repo / CODON_USAGE_PATH,
        repo / dwell_transducer.OCCUPANCY_PATH,
        repo / RIBOSOME_TE_PATH,
        repo / MRNA_STABILITY_PATH,
        repo / TURNOVER_PATH,
    ]
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local yeast payload missing", missing_required_data=missing, checks=[])

    try:
        context = direct_q6_context(repo)
        rows, protein_to_orf, direct_summary = direct_protein_rows(repo, context)
        ordered_by_orf, ordered_summary = context_lift.ordered_cds_by_orf(repo)
        dwell_by_orf, dwell_summary = local_dwell_by_orf(repo)
        probabilities, codon_usage_summary = codon_selection_probabilities(repo, context["code"])  # type: ignore[arg-type]
        selection_by_orf, selection_summary = selection_potential_by_orf(
            ordered_by_orf=ordered_by_orf,
            probabilities=probabilities,
            code=context["code"],  # type: ignore[arg-type]
        )

        base_ids = sorted(rows)
        ordered_ids = [protein_id for protein_id in base_ids if protein_to_orf.get(protein_id) in ordered_by_orf]
        active_ids = [
            protein_id
            for protein_id in ordered_ids
            if protein_to_orf.get(protein_id) in dwell_by_orf
            and protein_to_orf.get(protein_id) in selection_by_orf
        ]
        if len(active_ids) < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_data",
                reason=f"execution/selection active join yielded n={len(active_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
                base_n=len(base_ids),
                ordered_join_n=len(ordered_ids),
                checks=[
                    {"name": "gene_set_sufficient", "passed": False, "n": len(active_ids), "expected": "n >= 1000"},
                    {"name": "exec_channel_built", "passed": bool(dwell_by_orf)},
                    {"name": "sel_channel_built", "passed": bool(selection_by_orf)},
                ],
            )

        full_anchor_state = active_design_state(rows=rows, row_ids=base_ids)
        active_state = active_design_state(rows=rows, row_ids=active_ids)
        target = active_state["P_Q"]
        z_rows = active_state["z_rows"]
        if not isinstance(target, list) or not isinstance(z_rows, list):
            raise ValueError("active target or base controls malformed")
        target_norm2 = vector_norm2(target)
        if target_norm2 <= EPS:
            raise ValueError("active P_Q target has zero energy")

        exec_raw = [dwell_by_orf[str(protein_to_orf[protein_id])] for protein_id in active_ids]
        sel_raw = [selection_by_orf[str(protein_to_orf[protein_id])] for protein_id in active_ids]
        exec_z, exec_stats = standardize(exec_raw)
        sel_z, sel_stats = standardize(sel_raw)
        channel_rows = [[exec_z[index], sel_z[index]] for index in range(len(active_ids))]
        exec_rows = single_column_matrix(exec_z)
        sel_rows = single_column_matrix(sel_z)

        z_basis = orthonormal_basis_from_columns(z_rows)
        exec_e = residual_dictionary.residualize_with_basis(exec_rows, z_basis)
        sel_e = residual_dictionary.residualize_with_basis(sel_rows, z_basis)
        joint_e = residual_dictionary.residualize_with_basis(channel_rows, z_basis)
        base_design = z_rows
        exec_design = append_columns(z_rows, exec_rows)
        sel_design = append_columns(z_rows, sel_rows)
        joint_design = append_columns(z_rows, channel_rows)

        exec_cv = cv_delta(base_design, exec_design, target)
        sel_cv = cv_delta(base_design, sel_design, target)
        joint_cv = cv_delta(base_design, joint_design, target)
        base_models = prepare_models(base_design)
        joint_models = prepare_models(joint_design)
        null = permutation_null(target=target, base_models=base_models, full_models=joint_models)

        in_sample_exec = in_sample_delta(base_design, exec_design, target)
        in_sample_sel = in_sample_delta(base_design, sel_design, target)
        in_sample_joint = in_sample_delta(base_design, joint_design, target)
        partial_exec = partial_spearman(exec_z, target, base_design)
        partial_sel = partial_spearman(sel_z, target, base_design)
        exec_sel_spearman = spearman(exec_z, sel_z)

        measured_te, measured_te_summary = measured_te_by_protein(repo)
        te_active_pairs = [(exec_z[index], measured_te[protein_id]) for index, protein_id in enumerate(active_ids) if protein_id in measured_te]
        exec_te_rho = spearman([pair[0] for pair in te_active_pairs], [pair[1] for pair in te_active_pairs]) if te_active_pairs else 0.0
        dictionary, dictionary_summary = measured_dictionary_by_protein(repo)
        compression = dictionary_compression_on_active_set(rows=rows, row_ids=active_ids, dictionary=dictionary)
        compression_full = dictionary_compression_on_active_set(rows=rows, row_ids=base_ids, dictionary=dictionary)
        compression_residual_dictionary_anchor = residual_dictionary_compression_anchor(repo)

        denominator = float(compression["compressibility_C_star"]) if compression.get("status") == "computed" else 0.0
        if denominator <= EPS:
            denominator = float(active_state["R2_QP"])
        delta_exec = max(0.0, float(exec_cv["delta_r2"]))
        delta_sel = max(0.0, float(sel_cv["delta_r2"]))
        delta_joint = max(0.0, float(joint_cv["delta_r2"]))
        shared = max(0.0, delta_exec + delta_sel - delta_joint)
        independent_exec = max(0.0, delta_exec - 0.5 * shared)
        independent_sel = max(0.0, delta_sel - 0.5 * shared)
        explained_joint = min(denominator, max(0.0, delta_joint))
        if independent_exec + independent_sel > explained_joint and (independent_exec + independent_sel) > EPS:
            scale = explained_joint / (independent_exec + independent_sel)
            independent_exec *= scale
            independent_sel *= scale
        unresolved = max(0.0, denominator - independent_exec - independent_sel)
        denominator_for_fraction = denominator if denominator > EPS else 1.0
        execution_fraction = independent_exec / denominator_for_fraction
        selection_fraction = independent_sel / denominator_for_fraction
        unresolved_fraction = unresolved / denominator_for_fraction

        dl_penalty = LAMBDA_DL * 2
        net_lift = float(joint_cv["delta_r2"]) - dl_penalty
        dl_pass = net_lift > 0.0
        verdict = verdict_for(
            n=len(active_ids),
            r2_qp=float(active_state["R2_QP"]),
            delta_joint=float(joint_cv["delta_r2"]),
            null95=float(null["null95_delta_r2"]),
            dl_pass=dl_pass,
        )
        status = "passed" if verdict != "needs_data" else "needs_data"
        if verdict in {"composition_artifact", "bounded_descriptor_only"}:
            status = "passed"

        dominant_channel = "execution" if independent_exec >= independent_sel else "selection"
        if delta_joint <= 0.0:
            dominant_channel = "none"
        if unresolved_fraction >= max(execution_fraction, selection_fraction):
            dominant_component = "unresolved"
        else:
            dominant_component = dominant_channel

        checks = [
            {
                "name": "pq_reconstruction_validated",
                "passed": 0.25 <= float(active_state["R2_QP"]) <= 0.34,
                "active_R2_QP": active_state["R2_QP"],
                "full_base_R2_QP": full_anchor_state["R2_QP"],
                "expected": "active/base R2_QP in 0.25-0.34; yeast full-base anchor should be close to 0.298",
            },
            {
                "name": "gene_set_sufficient",
                "passed": len(active_ids) >= 1000,
                "n": len(active_ids),
                "base_n": len(base_ids),
                "ordered_join_n": len(ordered_ids),
            },
            {
                "name": "exec_channel_built",
                "passed": len(exec_z) == len(active_ids) and math.sqrt(variance(exec_z)) > 0.0,
                "n_orf_with_dwell": dwell_summary["n_orf_with_dwell"],
                "n_active": len(active_ids),
            },
            {
                "name": "sel_channel_built",
                "passed": len(sel_z) == len(active_ids) and math.sqrt(variance(sel_z)) > 0.0,
                "n_orf_with_selection_potential": selection_summary["n_orf_with_selection_potential"],
                "n_active": len(active_ids),
            },
            {
                "name": "joint_heldout_vs_null",
                "passed": float(joint_cv["delta_r2"]) > float(null["null95_delta_r2"]),
                "heldout_delta_r2_joint": joint_cv["delta_r2"],
                "null95_delta_r2": null["null95_delta_r2"],
                "null_mean_delta_r2": null["null_mean_delta_r2"],
                "permutation_count": PERMUTATION_COUNT,
            },
            {
                "name": "dl_penalty_checked",
                "passed": dl_pass,
                "lambda_dl": LAMBDA_DL,
                "model_df": 2,
                "dl_penalty": dl_penalty,
                "net_lift_after_dl": net_lift,
            },
            {
                "name": "exec_vs_selection_verdict",
                "passed": verdict in {"crosses_boundary", "bounded_descriptor_only", "composition_artifact", "needs_data"},
                "verdict": verdict,
                "dominant_channel": dominant_channel,
                "dominant_component": dominant_component,
            },
        ]

        cannot_claim = [
            "观测性 variance-partition，不能推出因果或机制。",
            "k_tl^local 来自 weak order-2 finite-state dwell transducer；ribosome footprint occupancy 是密度代理，不是真实 elongation-rate 因果测量。",
            f"k_tl^local 与 measured TE 的 Spearman rho={exec_te_rho:.6g} 已报告；若高度相关，本实验只能说 execution≈measured-TE-like readout。",
            "E_sel 是 organism codon-preference potential，可能与 B*_Q6 同义偏好定义部分循环；已用 amino-acid composition/length/GC3/M-density 控制，但选择/执行边界不锐利。",
            "occupancy 仅覆盖部分基因；active set 是 protein abundance、ordered CDS、dwell coverage、selection potential 的交集。",
            "unresolved 大部分仍未机制化；这是 source-definition 结论的一部分，不是需要硬凑 crosses 的失败。",
        ]

        note = (
            "Step0 的 R2_QP 对账采用 direct protein-omics survival 的 canonical controls "
            "(intercept, log length, 20 amino-acid composition, GC3, M-density)，因此 full-base yeast anchor "
            "应接近 0.298。context_lift sibling 当前 base_rows 还带 measured mRNA/stability join controls，"
            "其 target 是 Z-residualized protein abundance, not Pi_Q(P_e); 本脚本显式形成 P_Q=Pi_{Q_e}P_e 后再做 execution/selection readback。"
        )

        emit(
            status,
            organism=ORGANISM_LABEL,
            organism_key=ORGANISM,
            verdict=verdict,
            n=len(active_ids),
            base_n=len(base_ids),
            ordered_cds_join_n=len(ordered_ids),
            occupancy_dwell_join_n=sum(1 for protein_id in ordered_ids if protein_to_orf.get(protein_id) in dwell_by_orf),
            active_gene_set_n=len(active_ids),
            base_R2_QP_full_gene_set=full_anchor_state["R2_QP"],
            base_R2_QP_active_gene_set=active_state["R2_QP"],
            P_Q_norm2_active=active_state["P_Q_norm2"],
            P_residual_norm2_active=active_state["P_residual_norm2"],
            rank_diagnostics={
                "rank_Z_active": active_state["rank_Z"],
                "rank_Q_e_active": active_state["rank_Q_e"],
                "rank_exec_e": len(orthonormal_basis_from_columns(exec_e)),
                "rank_sel_e": len(orthonormal_basis_from_columns(sel_e)),
                "rank_joint_exec_sel_e": len(orthonormal_basis_from_columns(joint_e)),
                "control_column_count": len(z_rows[0]) if z_rows else 0,
            },
            step0_reconstruction={
                "gene_set_n": len(active_ids),
                "full_base_gene_set_n": len(base_ids),
                "R2_QP_full_base": full_anchor_state["R2_QP"],
                "R2_QP_active": active_state["R2_QP"],
                "expected_R2_QP_anchor": 0.298,
                "anchor_valid_range": [0.25, 0.34],
                "best_dictionary_measured_te_mrna_stability_turnover_active": compression,
                "best_dictionary_measured_te_mrna_stability_turnover_full_base": compression_full,
                "residual_dictionary_C_star_anchor": compression_residual_dictionary_anchor,
                "C_star_active": compression.get("compressibility_C_star"),
                "C_star_full_base": compression_full.get("compressibility_C_star"),
                "C_star_residual_dictionary_anchor": compression_residual_dictionary_anchor.get("compressibility_C_star")
                if isinstance(compression_residual_dictionary_anchor, dict)
                else None,
            },
            step1_heldout={
                "base": "canonical Z controls only",
                "target": "P_Q = Pi_{Q_e}(P_e), with P_e residualized protein abundance",
                "delta_R2_exec": exec_cv["delta_r2"],
                "delta_R2_sel": sel_cv["delta_r2"],
                "delta_R2_joint": joint_cv["delta_r2"],
                "base_R2_exec_fit": exec_cv["base_r2"],
                "full_R2_exec_fit": exec_cv["full_r2"],
                "base_R2_sel_fit": sel_cv["base_r2"],
                "full_R2_sel_fit": sel_cv["full_r2"],
                "base_R2_joint_fit": joint_cv["base_r2"],
                "full_R2_joint_fit": joint_cv["full_r2"],
                "partial_spearman_exec_P_Q_given_base": partial_exec,
                "partial_spearman_sel_P_Q_given_base": partial_sel,
                "spearman_exec_sel": exec_sel_spearman,
                "in_sample_exec": in_sample_exec,
                "in_sample_sel": in_sample_sel,
                "in_sample_joint": in_sample_joint,
            },
            step2_decomposition={
                "denominator": "C_star active measured dictionary coverage when available, otherwise active R2_QP",
                "denominator_value": denominator,
                "execution_component_delta_r2": independent_exec,
                "selection_component_delta_r2": independent_sel,
                "unresolved_component": unresolved,
                "execution_fraction": execution_fraction,
                "selection_fraction": selection_fraction,
                "unresolved_fraction": unresolved_fraction,
                "shared_exec_sel_overlap_delta_r2": shared,
                "dominant_channel": dominant_channel,
                "dominant_component": dominant_component,
            },
            step3_null_and_penalty={
                **null,
                "lambda_dl": LAMBDA_DL,
                "model_df": 2,
                "dl_penalty": dl_penalty,
                "net_lift_after_dl": net_lift,
                "dl_penalty_cleared": dl_pass,
                "exec_measured_te_spearman": exec_te_rho,
                "exec_measured_te_join_n": len(te_active_pairs),
                "measured_te_summary": measured_te_summary,
                "dictionary_summary": dictionary_summary,
            },
            feature_summaries={
                "k_tl_local": {
                    "standardization": exec_stats,
                    "min_raw": min(exec_raw),
                    "median_raw": sorted(exec_raw)[len(exec_raw) // 2],
                    "max_raw": max(exec_raw),
                    "definition": dwell_summary["definition"],
                },
                "E_sel": {
                    "standardization": sel_stats,
                    "min_raw": min(sel_raw),
                    "median_raw": sorted(sel_raw)[len(sel_raw) // 2],
                    "max_raw": max(sel_raw),
                    "definition": codon_usage_summary["definition"],
                },
            },
            data_summary={
                "direct_protein_rows": direct_summary,
                "ordered_cds": ordered_summary,
                "finite_state_dwell": dwell_summary,
                "codon_usage": codon_usage_summary,
                "selection_potential": selection_summary,
            },
            checks=checks,
            cannot_claim=cannot_claim,
            note=note,
            decision_rule=(
                "needs_data if n<1000 or R2_QP active outside [0.25,0.34]; crosses_boundary if joint held-out delta exceeds target-permutation null95, "
                "clears lambda_DL*2, and delta>=0.01; bounded_descriptor_only if significant but below 0.01; otherwise composition_artifact."
            ),
            seed=SEED,
            fold_count=FOLD_COUNT,
            permutation_count=PERMUTATION_COUNT,
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason="execution-vs-selection joint decomposition could not be computed",
            error=str(exc),
            exception_type=exc.__class__.__name__,
            checks=[],
        )


if __name__ == "__main__":
    main()

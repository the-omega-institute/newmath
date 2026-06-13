#!/usr/bin/env python3
"""Test whether the cross-organism optimal synonymous-codon core is tRNA adaptation."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
from collections import Counter
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    controls_for_counts,
    deterministic_folds,
    full_sample_slope,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    cv_r2_multivariate,
    solve_linear_system,
    synonymous_contrast_columns,
    synonymous_contrast_row,
    xtx_xty,
)
from run_b_star_q6_organism_specificity_meta_powered import (  # noqa: E402
    ORGANISMS,
    organism_domain,
)
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
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


EXPERIMENT_ID = "b_star_q6_universal_core_is_trna_adaptation_powered"
CLAIM_ID = "h3.cross_layer_relation.universal_core_trna_adaptation.b_star_q6_optimal_direction_powered"

FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 10
MIN_MEAN_ALIGNMENT = 0.15
MIN_POSITIVE_ALIGNMENT_FRACTION = 2.0 / 3.0
MIN_TAI_SELF_R2_RATIO = 0.25
MIN_MEAN_TAI_R2 = 0.0
SEED = f"sha256:{EXPERIMENT_ID}:deterministic"
EPS = 1e-12

RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}
AA_ONE_TO_THREE = {
    "A": "Ala",
    "R": "Arg",
    "N": "Asn",
    "D": "Asp",
    "C": "Cys",
    "Q": "Gln",
    "E": "Glu",
    "G": "Gly",
    "H": "His",
    "I": "Ile",
    "L": "Leu",
    "K": "Lys",
    "M": "Met",
    "F": "Phe",
    "P": "Pro",
    "S": "Ser",
    "T": "Thr",
    "W": "Trp",
    "Y": "Tyr",
    "V": "Val",
}
AA_ALIASES = {"fMet": "Met", "iMet": "Met", "Ile2": "Ile"}
DOS_REIS_2004_WOBBLE_S = {
    ("G", "U"): 0.41,
    ("U", "G"): 0.68,
    ("I", "C"): 0.28,
    ("I", "A"): 0.9999,
    ("I", "U"): 0.0,
    ("L", "A"): 0.89,
}
HEADER_RE = re.compile(r"tRNA-([A-Za-z0-9]+)-([ACGTUNacgtun]{3})")
FALLBACK_RE = re.compile(r"\)\s+([A-Za-z0-9]+)\s+\(([ACGTUNacgtun]{3})\)")


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return 0.5 * (ordered[middle - 1] + ordered[middle])


def vector_norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def unit_vector(values: list[float]) -> list[float] | None:
    norm = vector_norm(values)
    if norm <= EPS:
        return None
    return [value / norm for value in values]


def cosine(left: list[float], right: list[float]) -> float:
    denom = vector_norm(left) * vector_norm(right)
    if denom <= EPS:
        return 0.0
    return vector_dot(left, right) / denom


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def sign_test_greater(values: list[float]) -> dict[str, object]:
    positives = sum(1 for value in values if value > EPS)
    negatives = sum(1 for value in values if value < -EPS)
    n = positives + negatives
    if n <= 0:
        return {"n_nonzero": 0, "positive": positives, "negative": negatives, "p_greater": None}
    tail = sum(math.comb(n, k) for k in range(positives, n + 1)) / (2.0**n)
    return {"n_nonzero": n, "positive": positives, "negative": negatives, "p_greater": tail}


def t_test_mean_greater_zero(values: list[float]) -> dict[str, object]:
    n = len(values)
    value_mean = mean(values)
    if n < 2 or value_mean is None:
        return {"n": n, "mean": value_mean, "sd": None, "z_approx": None, "p_greater_normal_approx": None}
    variance = sum((value - value_mean) ** 2 for value in values) / (n - 1)
    sd = math.sqrt(variance)
    if sd <= EPS:
        z = math.inf if value_mean > 0.0 else (-math.inf if value_mean < 0.0 else 0.0)
    else:
        z = value_mean / (sd / math.sqrt(n))
    p = 0.0 if z == math.inf else (1.0 if z == -math.inf else 1.0 - normal_cdf(z))
    return {"n": n, "mean": value_mean, "sd": sd, "z_approx": z, "p_greater_normal_approx": p}


def cv_r2_fixed_direction(
    x_rows: list[list[float]],
    y: list[float],
    direction: list[float],
    folds: list[list[int]],
) -> tuple[float, float]:
    x = [vector_dot(row, direction) for row in x_rows]
    slope = full_sample_slope(x, y)
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return 0.0, slope
    all_indices = set(range(len(y)))
    sse = 0.0
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        x_train_energy = sum(x[index] * x[index] for index in train_indices)
        if x_train_energy <= EPS:
            fold_slope = 0.0
        else:
            fold_slope = sum(x[index] * y[index] for index in train_indices) / x_train_energy
        for index in test_indices:
            residual = y[index] - fold_slope * x[index]
            sse += residual * residual
    return 1.0 - sse / y_energy, slope


def dna_to_rna(text: str) -> str:
    return text.upper().replace("T", "U")


def normalize_aa(label: str) -> str:
    return AA_ALIASES.get(label, label)


def records_from_gtrnadb_fasta_payload(payload: dict[str, object], source_path: str) -> tuple[list[dict[str, str]], dict[str, object]]:
    raw_text = payload.get("raw_payload_text")
    if not isinstance(raw_text, str) or not raw_text:
        raise ValueError("GtRNAdb payload lacks raw_payload_text")
    records: list[dict[str, str]] = []
    skipped: Counter[str] = Counter()
    for line in raw_text.splitlines():
        if not line.startswith(">"):
            continue
        match = HEADER_RE.search(line) or FALLBACK_RE.search(line)
        if match is None:
            skipped["unmatched_header"] += 1
            continue
        aa_label = match.group(1)
        anticodon = dna_to_rna(match.group(2))
        lower = line.lower()
        if "pseudo" in lower:
            skipped["pseudogene"] += 1
            continue
        if aa_label == "iMet":
            skipped["initiator_methionine_excluded_from_elongator_tai"] += 1
            continue
        if aa_label in {"Und", "Undet"} or "N" in anticodon:
            skipped["undetermined"] += 1
            continue
        if aa_label == "Sup" or "suppressor" in lower:
            skipped["suppressor"] += 1
            continue
        if aa_label == "SeC":
            skipped["selenocysteine"] += 1
            continue
        records.append({"aa": normalize_aa(aa_label), "aa_label": aa_label, "anticodon": anticodon})
    if not records:
        raise ValueError("no usable tRNA records in GtRNAdb FASTA payload")
    return records, {
        "trna_source_path": source_path,
        "trna_source_kind": "GtRNAdb FASTA raw_payload_text parsed locally",
        "payload_sha256": payload.get("payload_sha256"),
        "usable_tai_record_count": len(records),
        "skipped_trna_records": dict(sorted(skipped.items())),
    }


def records_from_summary_payload(payload: dict[str, object], source_path: str) -> tuple[list[dict[str, str]], dict[str, object]]:
    raw = payload.get("trna_aa_anticodon_gene_copy_counts")
    if not isinstance(raw, dict) or not raw:
        raise ValueError("summary payload lacks trna_aa_anticodon_gene_copy_counts")
    records: list[dict[str, str]] = []
    skipped: Counter[str] = Counter()
    for key, count_raw in sorted(raw.items()):
        if not isinstance(key, str) or ":" not in key:
            skipped["bad_key"] += 1
            continue
        aa_label, anticodon_raw = key.split(":", 1)
        if aa_label == "iMet":
            skipped["initiator_methionine_excluded_from_elongator_tai"] += int(count_raw) if finite_numeric(count_raw) else 1
            continue
        anticodon = dna_to_rna(anticodon_raw)
        if "N" in anticodon or len(anticodon) != 3:
            skipped["undetermined_anticodon"] += int(count_raw) if finite_numeric(count_raw) else 1
            continue
        if not finite_numeric(count_raw) or int(float(count_raw)) != float(count_raw) or int(float(count_raw)) < 0:
            skipped["bad_count"] += 1
            continue
        for _ in range(int(float(count_raw))):
            records.append({"aa": normalize_aa(aa_label), "aa_label": aa_label, "anticodon": anticodon})
    if not records:
        raise ValueError("no usable tRNA records in summary payload")
    return records, {
        "trna_source_path": source_path,
        "trna_source_kind": payload.get("source_kind", "GtRNAdb-derived summary"),
        "payload_sha256": payload.get("payload_sha256"),
        "usable_tai_record_count": len(records),
        "skipped_trna_records": dict(sorted(skipped.items())),
    }


def load_trna_records(repo: pathlib.Path, organism: str) -> tuple[list[dict[str, str]], dict[str, object]]:
    data_dir = repo / "tools/bio_reality/data"
    summary_path = data_dir / f"trna_gene_copy_{organism}.json"
    if summary_path.exists():
        payload = load_json(summary_path)
        if isinstance(payload, dict):
            try:
                return records_from_summary_payload(payload, str(summary_path.relative_to(repo)))
            except ValueError:
                pass
    fasta_path = data_dir / f"gtrnadb_trna_all_copy_{organism}.json"
    if not fasta_path.exists():
        raise FileNotFoundError(f"missing GtRNAdb tRNA payload for {organism}")
    payload = load_json(fasta_path)
    if not isinstance(payload, dict):
        raise ValueError("GtRNAdb payload must be a JSON object")
    return records_from_gtrnadb_fasta_payload(payload, str(fasta_path.relative_to(repo)))


def first_two_positions_match(codon: str, anticodon: str) -> bool:
    return RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and RNA_COMPLEMENT.get(anticodon[1]) == codon[1]


def effective_wobble_base(aa_label: str, anticodon: str) -> str:
    wobble = anticodon[0]
    if wobble == "A":
        return "I"
    if aa_label == "Ile2" and anticodon == "CAU":
        return "L"
    return wobble


def wobble_penalty(wobble: str, codon_third: str) -> float | None:
    if RNA_COMPLEMENT.get(wobble) == codon_third:
        return 0.0
    return DOS_REIS_2004_WOBBLE_S.get((wobble, codon_third))


def codon_w_values(
    *,
    code: dict[str, str],
    codons: list[str],
    records: list[dict[str, str]],
) -> tuple[dict[str, float], dict[str, float], dict[str, object]]:
    copy_counts: Counter[tuple[str, str, str]] = Counter()
    for record in records:
        aa = record.get("aa", "")
        aa_label = record.get("aa_label", "")
        anticodon = record.get("anticodon", "")
        if aa and aa_label and anticodon:
            copy_counts[(aa, aa_label, anticodon)] += 1

    raw_w: dict[str, float] = {}
    contributor_count = 0
    for codon in codons:
        aa = AA_ONE_TO_THREE[code[codon]]
        total = 0.0
        for (record_aa, aa_label, anticodon), copy in copy_counts.items():
            if record_aa != aa:
                continue
            if not first_two_positions_match(codon, anticodon):
                continue
            wobble = effective_wobble_base(aa_label, anticodon)
            penalty = wobble_penalty(wobble, codon[2])
            if penalty is None:
                continue
            contribution = (1.0 - penalty) * copy
            if contribution <= 0.0:
                continue
            total += contribution
            contributor_count += 1
        raw_w[codon] = total

    max_w = max(raw_w.values()) if raw_w else 0.0
    if max_w <= 0.0:
        raise ValueError("no nonzero tAI codon W values")
    normalized = {codon: value / max_w for codon, value in raw_w.items()}
    nonzero = [value for value in normalized.values() if value > 0.0]
    fallback = math.exp(sum(math.log(value) for value in nonzero) / len(nonzero))
    weights = {codon: (value if value > 0.0 else fallback) for codon, value in normalized.items()}
    return weights, raw_w, {
        "codon_weight_count": len(weights),
        "zero_raw_W_filled_by_geometric_mean_count": sum(1 for value in raw_w.values() if value == 0.0),
        "tai_contributor_contact_count": contributor_count,
        "min_weight": min(weights.values()),
        "max_weight": max(weights.values()),
    }


def organism_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> tuple[list[list[float]], list[float], list[list[float]], float | None, dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    syn_rows: list[list[float]] = []
    y_rows: list[float] = []
    controls: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    total_gc3_count = 0
    total_sense_count = 0
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
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        y_rows.append(math.log10(abundance))
        controls.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=cds_len_nt,
            )
        )
        total_sense_count += total
        total_gc3_count += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})

    gc3 = None if total_sense_count <= 0 else total_gc3_count / total_sense_count
    return syn_rows, y_rows, controls, gc3, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def fit_optimal_direction(syn_residualized: list[list[float]], y: list[float]) -> tuple[list[float] | None, dict[str, object]]:
    if not syn_residualized or not syn_residualized[0]:
        return None, {"ridge_step": None, "reason": "empty synonymous design"}
    xtx, xty = xtx_xty(syn_residualized, y)
    beta, ridge_step = solve_linear_system(xtx, xty)
    direction = unit_vector(beta)
    if direction is None:
        return None, {"ridge_step": ridge_step, "reason": "zero fitted coefficient norm"}
    return direction, {
        "ridge_step": ridge_step,
        "coefficient_norm": vector_norm(beta),
        "nonzero_coefficients_abs_gt_1e_12": sum(1 for value in beta if abs(value) > EPS),
    }


def trna_contrast_direction(
    *,
    weights: dict[str, float],
    syn_columns: list[dict[str, object]],
) -> list[float] | None:
    values = [
        weights[str(column["positive_codon"])] - weights[str(column["negative_codon"])]
        for column in syn_columns
    ]
    return unit_vector(values)


def universal_core(rows: list[dict[str, object]]) -> tuple[list[float] | None, dict[str, object]]:
    if not rows:
        return None, {"reason": "no computed rows"}
    p = len(rows[0]["optimal_direction"])  # type: ignore[arg-type]
    average = [0.0 for _ in range(p)]
    for row in rows:
        direction = row["optimal_direction"]
        for index in range(p):
            average[index] += direction[index]  # type: ignore[index]
    average = [value / len(rows) for value in average]
    core = unit_vector(average)
    if core is None:
        return None, {"reason": "mean direction has zero norm", "mean_direction_norm": 0.0}
    alignments = [cosine(row["optimal_direction"], core) for row in rows]  # type: ignore[arg-type]
    return core, {
        "mean_direction_norm_before_normalization": vector_norm(average),
        "mean_alignment_to_core": mean(alignments),
        "min_alignment_to_core": min(alignments),
        "max_alignment_to_core": max(alignments),
    }


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    proteomics_path = data_dir / f"proteomics_abundance_{organism}.json"
    gtrna_path = data_dir / f"gtrnadb_trna_all_copy_{organism}.json"
    trna_summary_path = data_dir / f"trna_gene_copy_{organism}.json"
    if not cds_path.exists() or not proteomics_path.exists() or (not gtrna_path.exists() and not trna_summary_path.exists()):
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance, proteomics_abundance, or GtRNAdb tRNA JSON",
            "cds_exists": cds_path.exists(),
            "proteomics_exists": proteomics_path.exists(),
            "gtrnadb_exists": gtrna_path.exists(),
            "trna_summary_exists": trna_summary_path.exists(),
        }

    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "cds payload is not an object"}
    proteomics_payload = load_json(proteomics_path)
    proteomics_n = proteomics_payload.get("n_proteins") if isinstance(proteomics_payload, dict) else None

    syn_raw, y_raw, controls, gc3, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    n_join = len(y_raw)
    base = {
        "organism": organism,
        "status": "needs_data",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "data_summary": data_summary,
    }
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        base["reason"] = f"join below gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}"
        return base

    trna_records, trna_source_summary = load_trna_records(repo, organism)
    weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    if trna_direction is None:
        base["reason"] = "zero tRNA contrast direction"
        base["trna_source_summary"] = trna_source_summary
        base["tai_weight_summary"] = tai_summary
        return base

    syn_residualized, rank_controls_syn = residualize(syn_raw, controls)
    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y = matrix_column(y_residualized, 0)
    if vector_dot(y, y) <= EPS:
        base["reason"] = "zero residual abundance energy after controls"
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        return base

    optimal_direction, fit_summary = fit_optimal_direction(syn_residualized, y)
    if optimal_direction is None:
        base["reason"] = str(fit_summary.get("reason", "could not fit optimal direction"))
        base["rank_controls_syn"] = rank_controls_syn
        base["rank_controls_y"] = rank_controls_y
        base["fit_summary"] = fit_summary
        return base

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    self_r2, self_slope = cv_r2_fixed_direction(syn_residualized, y, optimal_direction, folds)
    trna_r2, trna_slope = cv_r2_fixed_direction(syn_residualized, y, trna_direction, folds)
    alignment = cosine(optimal_direction, trna_direction)
    usable_self = max(0.0, self_r2)
    ratio = None if usable_self <= EPS else max(0.0, trna_r2) / usable_self

    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "gc3": gc3,
        "domain": organism_domain(organism),
        "optimal_direction": optimal_direction,
        "trna_direction": trna_direction,
        "cos_optimal_trna": alignment,
        "total_syn_selection_held_out_r2": total_syn_selection,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "trna_alone_held_out_r2": trna_r2,
        "trna_alone_slope": trna_slope,
        "trna_positive_r2_over_self_positive_r2": ratio,
        "fold_count": FOLD_COUNT,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "synonymous_cv_summary": syn_cv_summary,
        "residual_synonymous_columns": len(syn_columns),
        "residual_abundance_energy": vector_dot(y, y),
        "data_summary": data_summary,
        "trna_source_summary": trna_source_summary,
        "tai_weight_summary": {
            **tai_summary,
            "raw_W_by_codon": raw_w,
            "normalized_w_by_codon": weights,
        },
    }


def compact_per_organism(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    out = []
    for row in rows:
        out.append(
            {
                "organism": row["organism"],
                "domain": row["domain"],
                "gc3": row["gc3"],
                "n_join": row["n_join"],
                "cos_optimal_trna": row["cos_optimal_trna"],
                "trna_alone_R2": row["trna_alone_held_out_r2"],
                "self_R2": row["self_direction_held_out_r2"],
                "total_syn_selection_R2": row["total_syn_selection_held_out_r2"],
                "trna_positive_R2_over_self_positive_R2": row["trna_positive_r2_over_self_positive_r2"],
                "cos_trna_universal_core": row.get("cos_trna_universal_core"),
                "fit_coefficient_norm": row["fit_summary"].get("coefficient_norm"),
                "usable_tai_record_count": row["trna_source_summary"].get("usable_tai_record_count"),
                "zero_raw_W_filled_by_geometric_mean_count": row["tai_weight_summary"].get("zero_raw_W_filled_by_geometric_mean_count"),
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
        syn_columns = synonymous_contrast_columns(fibers=fibers)

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                syn_columns=syn_columns,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        if n_computed < MIN_COMPLETE_ORGANISMS:
            emit(
                "needs_data",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
                checks={
                    "directions_computed": {
                        "passed": False,
                        "organisms_computed": n_computed,
                        "minimum": MIN_COMPLETE_ORGANISMS,
                        "synonymous_design_columns": len(syn_columns),
                    },
                    "optimal_aligns_trna_sign_test": {"passed": False},
                    "trna_explains_optimal": {"passed": False},
                },
                caveats=[
                    "requires same-organism proteomics, cds_codon_abundance, and GtRNAdb/tRNA gene-copy payloads",
                    "strict same-key organism matching is used; near-name strain substitutions are not inferred",
                ],
            )

        core, core_summary = universal_core(computed)
        if core is None:
            emit(
                "failed",
                reason=str(core_summary.get("reason", "universal core unavailable")),
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=n_computed,
                checks={
                    "directions_computed": {"passed": True, "organisms_computed": n_computed},
                    "optimal_aligns_trna_sign_test": {"passed": False},
                    "trna_explains_optimal": {"passed": False},
                },
            )

        for row in computed:
            row["cos_trna_universal_core"] = cosine(row["trna_direction"], core)  # type: ignore[arg-type]
            row["cos_optimal_universal_core"] = cosine(row["optimal_direction"], core)  # type: ignore[arg-type]

        alignments = [float(row["cos_optimal_trna"]) for row in computed]
        trna_core_cosines = [float(row["cos_trna_universal_core"]) for row in computed]
        self_r2_values = [float(row["self_direction_held_out_r2"]) for row in computed]
        trna_r2_values = [float(row["trna_alone_held_out_r2"]) for row in computed]
        positive_self_r2 = [max(0.0, value) for value in self_r2_values]
        positive_trna_r2 = [max(0.0, value) for value in trna_r2_values]
        ratios = [
            float(row["trna_positive_r2_over_self_positive_r2"])
            for row in computed
            if finite_numeric(row.get("trna_positive_r2_over_self_positive_r2"))
        ]
        alignment_sign = sign_test_greater(alignments)
        alignment_t = t_test_mean_greater_zero(alignments)
        trna_core_sign = sign_test_greater(trna_core_cosines)
        trna_core_t = t_test_mean_greater_zero(trna_core_cosines)
        mean_alignment = mean(alignments)
        mean_trna_r2 = mean(trna_r2_values)
        mean_self_r2 = mean(self_r2_values)
        mean_positive_trna_r2 = mean(positive_trna_r2)
        mean_positive_self_r2 = mean(positive_self_r2)
        pooled_positive_r2_ratio = (
            None
            if mean_positive_self_r2 is None or mean_positive_self_r2 <= EPS or mean_positive_trna_r2 is None
            else mean_positive_trna_r2 / mean_positive_self_r2
        )

        alignment_passed = (
            mean_alignment is not None
            and mean_alignment > MIN_MEAN_ALIGNMENT
            and alignment_sign["p_greater"] is not None
            and float(alignment_sign["p_greater"]) <= 0.05
            and alignment_sign["positive"] >= math.ceil(MIN_POSITIVE_ALIGNMENT_FRACTION * int(alignment_sign["n_nonzero"]))
        )
        trna_explains = (
            mean_trna_r2 is not None
            and mean_trna_r2 > MIN_MEAN_TAI_R2
            and pooled_positive_r2_ratio is not None
            and pooled_positive_r2_ratio >= MIN_TAI_SELF_R2_RATIO
        )
        directions_ok = n_computed >= MIN_COMPLETE_ORGANISMS and len(syn_columns) == 41
        status = "passed" if directions_ok and alignment_passed and trna_explains else "failed"
        failed_gates = []
        if not directions_ok:
            failed_gates.append("directions_computed")
        if not alignment_passed:
            failed_gates.append("optimal_aligns_trna_sign_test")
        if not trna_explains:
            failed_gates.append("trna_explains_optimal")

        checks = {
            "directions_computed": {
                "passed": directions_ok,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
            },
            "optimal_aligns_trna_sign_test": {
                "passed": alignment_passed,
                "rule": "mean cos(optimal,tRNA) > 0.15, one-sided sign-test p<=0.05, and at least two thirds nonzero alignments positive",
                "mean_cos_optimal_trna": mean_alignment,
                "median_cos_optimal_trna": median(alignments),
                "min_cos_optimal_trna": min(alignments),
                "max_cos_optimal_trna": max(alignments),
                "sign_test_greater": alignment_sign,
                "mean_test_normal_approx": alignment_t,
            },
            "trna_explains_optimal": {
                "passed": trna_explains,
                "rule": "mean tRNA-alone held-out R2 > 0 and pooled positive tRNA/self R2 ratio >= 0.25",
                "mean_trna_alone_R2": mean_trna_r2,
                "median_trna_alone_R2": median(trna_r2_values),
                "positive_trna_alone_R2_count": sum(1 for value in trna_r2_values if value > 0.0),
                "mean_self_R2": mean_self_r2,
                "median_self_R2": median(self_r2_values),
                "mean_positive_trna_R2": mean_positive_trna_r2,
                "mean_positive_self_R2": mean_positive_self_r2,
                "pooled_positive_trna_R2_over_self_R2": pooled_positive_r2_ratio,
                "median_per_organism_positive_R2_ratio": median(ratios),
            },
        }

        emit(
            status,
            reason=None if status == "passed" else "fixed gates not cleared: " + ",".join(failed_gates),
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            synonymous_design_columns=len(syn_columns),
            payload={
                "per_organism": compact_per_organism(computed),
                "cross_species": {
                    "mean_cos_optimal_trna": mean_alignment,
                    "median_cos_optimal_trna": median(alignments),
                    "alignment_sign_test_greater": alignment_sign,
                    "alignment_mean_test_normal_approx": alignment_t,
                    "mean_trna_alone_R2": mean_trna_r2,
                    "mean_self_R2": mean_self_r2,
                    "pooled_positive_trna_R2_over_self_R2": pooled_positive_r2_ratio,
                    "mean_cos_trna_universal_core": mean(trna_core_cosines),
                    "median_cos_trna_universal_core": median(trna_core_cosines),
                    "trna_vs_universal_core_sign_test_greater": trna_core_sign,
                    "trna_vs_universal_core_mean_test_normal_approx": trna_core_t,
                },
            },
            universal_core_summary={
                **core_summary,
                "mean_cos_trna_universal_core": mean(trna_core_cosines),
                "median_cos_trna_universal_core": median(trna_core_cosines),
                "min_cos_trna_universal_core": min(trna_core_cosines),
                "max_cos_trna_universal_core": max(trna_core_cosines),
                "trna_vs_universal_core_sign_test_greater": trna_core_sign,
                "trna_vs_universal_core_mean_test_normal_approx": trna_core_t,
            },
            controls_used={
                "target": "log10(abundance_ppm)",
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous fiber",
                "optimal_direction": "full-sample least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized",
                "trna_direction": "dos Reis tAI codon weights from same-organism GtRNAdb/tRNA gene-copy records, projected as w_positive_codon - w_reference_codon on the same 41 contrasts, then unit-normalized",
                "held_out_strength": "5-fold CV R2 for a fixed one-dimensional direction with fold-local slope after residualizing target and synonymous contrasts against controls",
                "universal_core": "unit-normalized mean of computed organism optimal directions",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
                "wobble_rule": {
                    "definition": "W_codon = sum_over_same-aa isoacceptors (1-s_wobble) * tGCN when anticodon positions 2/3 pair codon positions 2/1; w_codon = W_codon / max(W); zero W filled by geometric mean of nonzero normalized W",
                    "s_values": {f"{left}:{right}": value for (left, right), value in DOS_REIS_2004_WOBBLE_S.items()},
                    "canonical_watson_crick_s": 0.0,
                    "anticodon_A_treated_as_inosine": True,
                    "initiator_iMet_excluded_from_elongator_tai": True,
                },
            },
            checks=checks,
            organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            caveats=[
                "observational abundance-associated optimal directions are not causal perturbation estimates",
                "tRNA gene copy number and dos Reis wobble penalties are proxies for supply/adaptation, not direct charged tRNA abundance",
                "strict same-key organism matching is used; near-name strain substitutions are not inferred",
                "the one-sided mean test reports a normal approximation because the standard library has no exact t CDF",
                "no phylogenetic comparative correction is applied",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "directions_computed": {"passed": False},
                "optimal_aligns_trna_sign_test": {"passed": False},
                "trna_explains_optimal": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

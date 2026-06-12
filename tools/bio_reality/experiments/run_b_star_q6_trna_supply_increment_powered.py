#!/usr/bin/env python3
"""tRNA-supply increment over the measured B*_Q6 readout dictionary.

This is an observational held-out prediction test. It asks whether a
GtRNAdb-derived tRNA gene-copy tAI readout adds predictive information for the
Z-residualized yeast protein-abundance target beyond measured TE, mRNA
stability, and protein turnover. It is not a causal pathway proof.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
from collections import Counter
from typing import Any

import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_joint_te_stability_mediation_powered import yeast_join_keys
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, codon_counts_rna, vector_dot


EXPERIMENT_ID = "b_star_q6_trna_supply_increment_powered"
CLAIM_ID = "h3.cross_layer_relation.trna_supply_increment.b_star_q6_beyond_measured_dictionary_powered"

ORGANISM = "saccharomyces_cerevisiae"
FOLD_COUNT = 5
PERMUTATION_COUNT = 120
RIDGE = 1e-8
EPS = 1e-12
SEED = f"sha256:{EXPERIMENT_ID}:fixed-readout-target-permutation"

TRNA_SUMMARY_PATH = "tools/bio_reality/data/trna_gene_copy_saccharomyces_cerevisiae.json"
GTRNADB_FASTA_PATH = "tools/bio_reality/data/gtrnadb_trna_all_copy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
CDS_ABUNDANCE_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"

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

# dos Reis et al. 2004 optimized wobble penalties, matching the local _tai.py
# convention used by sibling modeled/measured tAI experiments.
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
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def dna_to_rna(text: str) -> str:
    return text.upper().replace("T", "U")


def normalize_aa(label: str) -> str:
    return AA_ALIASES.get(label, label)


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    return residual_dictionary.residualize_with_basis(matrix, basis)


def standardize_columns(matrix: list[list[float]]) -> tuple[list[list[float]], list[dict[str, float]]]:
    if not matrix:
        return [], []
    width = len(matrix[0])
    means = [mean([row[col] for row in matrix]) for col in range(width)]
    scales: list[float] = []
    for col in range(width):
        variance = mean([(row[col] - means[col]) ** 2 for row in matrix])
        scale = math.sqrt(variance)
        scales.append(scale if scale > EPS else 1.0)
    out = [[(row[col] - means[col]) / scales[col] for col in range(width)] for row in matrix]
    return out, [{"mean": means[col], "sd": scales[col]} for col in range(width)]


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        material = f"{material_prefix}|index={index}|n={n}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def folds_for_n(n: int, fold_count: int) -> list[list[int]]:
    return [[index for index in range(n) if index % fold_count == fold] for fold in range(fold_count)]


def subset_rows(matrix: list[list[float]], indices: list[int]) -> list[list[float]]:
    return [matrix[index] for index in indices]


def subset_values(values: list[float], indices: list[int]) -> list[float]:
    return [values[index] for index in indices]


def predict_from_ridge(train_x: list[list[float]], train_y: list[float], test_x: list[list[float]]) -> list[float]:
    if not train_x:
        return [0.0 for _ in test_x]
    coeff = solve_regularized_normal_equation(train_x, train_y, ridge=RIDGE)
    return [sum(row[index] * coeff[index] for index in range(len(coeff))) for row in test_x]


def cv_r2(design: list[list[float]], target: list[float], folds: list[list[int]]) -> float:
    n = len(target)
    all_indices = list(range(n))
    sse = 0.0
    total_ss = sum(value * value for value in target)
    if total_ss <= EPS:
        return 0.0
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        predictions = predict_from_ridge(
            subset_rows(design, train_indices),
            subset_values(target, train_indices),
            subset_rows(design, test_indices),
        )
        for local_index, row_index in enumerate(test_indices):
            residual = target[row_index] - predictions[local_index]
            sse += residual * residual
    return 1.0 - sse / total_ss


def cv_delta_r2(
    base_design: list[list[float]],
    full_design: list[list[float]],
    target: list[float],
    folds: list[list[int]],
) -> tuple[float, float, float]:
    base_r2 = cv_r2(base_design, target, folds)
    full_r2 = cv_r2(full_design, target, folds)
    return full_r2 - base_r2, base_r2, full_r2


def records_from_summary_payload(payload: dict[str, object]) -> tuple[list[dict[str, str]], dict[str, object]]:
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
            skipped["initiator_methionine_excluded_from_elongator_tai"] += int(count_raw) if finite_number(count_raw) else 1
            continue
        anticodon = dna_to_rna(anticodon_raw)
        if "N" in anticodon or len(anticodon) != 3:
            skipped["undetermined_anticodon"] += int(count_raw) if finite_number(count_raw) else 1
            continue
        if not finite_number(count_raw) or int(float(count_raw)) != float(count_raw) or int(float(count_raw)) < 0:
            skipped["bad_count"] += 1
            continue
        for _ in range(int(float(count_raw))):
            records.append(
                {
                    "aa": normalize_aa(aa_label),
                    "aa_label": aa_label,
                    "anticodon": anticodon,
                    "matched": "True",
                }
            )
    if not records:
        raise ValueError("no usable tRNA records in summary payload")
    return records, {
        "trna_source_path": TRNA_SUMMARY_PATH,
        "trna_source_kind": payload.get("source_kind", "GtRNAdb-derived summary"),
        "payload_sha256": payload.get("payload_sha256"),
        "n_trna_genes_included_for_gcn": payload.get("n_trna_genes_included_for_gcn"),
        "n_trna_genes_included_for_elongator_tai": payload.get("n_trna_genes_included_for_elongator_tai"),
        "usable_tai_record_count": len(records),
        "skipped_trna_records": dict(sorted(skipped.items())),
    }


def records_from_gtrnadb_fasta_payload(payload: dict[str, object]) -> tuple[list[dict[str, str]], dict[str, object]]:
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
        records.append({"aa": normalize_aa(aa_label), "aa_label": aa_label, "anticodon": anticodon, "matched": "True"})
    if not records:
        raise ValueError("no usable tRNA records in GtRNAdb FASTA payload")
    return records, {
        "trna_source_path": GTRNADB_FASTA_PATH,
        "trna_source_kind": "GtRNAdb FASTA raw_payload_text parsed locally",
        "payload_sha256": payload.get("payload_sha256"),
        "usable_tai_record_count": len(records),
        "skipped_trna_records": dict(sorted(skipped.items())),
    }


def load_trna_records(repo: pathlib.Path) -> tuple[list[dict[str, str]], dict[str, object]]:
    summary_path = repo / TRNA_SUMMARY_PATH
    if summary_path.exists():
        payload = load_json(summary_path)
        if isinstance(payload, dict):
            try:
                return records_from_summary_payload(payload)
            except ValueError:
                pass
    fasta_path = repo / GTRNADB_FASTA_PATH
    if not fasta_path.exists():
        missing = [TRNA_SUMMARY_PATH, GTRNADB_FASTA_PATH]
        raise FileNotFoundError("missing local yeast tRNA gene-copy payloads: " + ", ".join(missing))
    payload = load_json(fasta_path)
    if not isinstance(payload, dict):
        raise ValueError("GtRNAdb payload must be a JSON object")
    return records_from_gtrnadb_fasta_payload(payload)


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
) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
    copy_counts: Counter[tuple[str, str, str]] = Counter()
    for record in records:
        aa = record.get("aa", "")
        aa_label = record.get("aa_label", "")
        anticodon = record.get("anticodon", "")
        if aa and aa_label and anticodon:
            copy_counts[(aa, aa_label, anticodon)] += 1

    raw_w: dict[str, float] = {}
    contributors: list[dict[str, object]] = []
    for codon in codons:
        aa = AA_ONE_TO_THREE[code[codon]]
        total = 0.0
        codon_contributors: list[dict[str, object]] = []
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
            codon_contributors.append(
                {
                    "aa_label": aa_label,
                    "anticodon": anticodon,
                    "effective_wobble_base": wobble,
                    "copy": copy,
                    "s": penalty,
                    "contribution": contribution,
                }
            )
        raw_w[codon] = total
        if codon_contributors:
            contributors.append({"codon": codon, "contributors": codon_contributors})

    max_w = max(raw_w.values()) if raw_w else 0.0
    if max_w <= 0.0:
        raise ValueError("no nonzero tAI codon W values")
    normalized = {codon: value / max_w for codon, value in raw_w.items()}
    nonzero = [value for value in normalized.values() if value > 0.0]
    if not nonzero:
        raise ValueError("no nonzero normalized tAI weights")
    fallback = math.exp(sum(math.log(value) for value in nonzero) / len(nonzero))
    weights = {codon: (value if value > 0.0 else fallback) for codon, value in normalized.items()}
    return weights, raw_w, contributors


def ordered_cds_by_orf(repo: pathlib.Path) -> tuple[dict[str, list[str]], dict[str, object]]:
    payload = load_json(repo / ORDERED_CDS_PATH)
    if not isinstance(payload, dict):
        raise ValueError("ordered CDS payload must be a JSON object")
    cds = payload.get("cds")
    if not isinstance(cds, list):
        raise ValueError("ordered CDS payload must contain a cds list")
    out: dict[str, list[str]] = {}
    skipped: Counter[str] = Counter()
    for item in cds:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        codons_raw = item.get("codons")
        if not isinstance(gene_id, str) or not isinstance(codons_raw, list):
            skipped["missing_gene_or_codons"] += 1
            continue
        codons = [dna_to_rna(str(codon)) for codon in codons_raw if isinstance(codon, str) and len(codon) == 3]
        if not codons:
            skipped["empty_codons"] += 1
            continue
        out[gene_id] = codons
    return out, {
        "ordered_cds_path": ORDERED_CDS_PATH,
        "ordered_cds_reported_n_cds": payload.get("n_cds"),
        "ordered_cds_indexed_orfs": len(out),
        "ordered_cds_skipped": dict(sorted(skipped.items())),
    }


def protein_to_yeast_orf(repo: pathlib.Path, rows: dict[str, dict[str, object]]) -> dict[str, str]:
    out: dict[str, str] = {}
    for protein_id in rows:
        if protein_id.startswith("4932."):
            orf = protein_id.split(".", 1)[1]
            if orf:
                out[protein_id] = orf
    path = repo / CDS_ABUNDANCE_PATH
    if not path.exists():
        return out
    payload = load_json(path)
    joined = payload.get("joined") if isinstance(payload, dict) else None
    if not isinstance(joined, list):
        return out
    for item in joined:
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or protein_id not in rows:
            continue
        _pid, orf, error = yeast_join_keys(item)
        if not error and isinstance(orf, str) and orf:
            out[protein_id] = orf
    return out


def per_gene_tai_from_ordered_cds(
    *,
    ordered_by_orf: dict[str, list[str]],
    weights: dict[str, float],
    code: dict[str, str],
) -> tuple[dict[str, float], dict[str, object]]:
    out: dict[str, float] = {}
    skipped: Counter[str] = Counter()
    for orf, gene_codons in ordered_by_orf.items():
        logs: list[float] = []
        for codon in gene_codons:
            if code.get(codon) == "*" or codon not in weights:
                continue
            value = weights[codon]
            if value <= 0.0 or not math.isfinite(value):
                skipped["nonpositive_weight"] += 1
                continue
            logs.append(math.log(value))
        if not logs:
            skipped["no_sense_codons"] += 1
            continue
        out[orf] = math.exp(sum(logs) / len(logs))
    return out, {
        "per_gene_tai_definition": "geometric mean exp(mean(log(w_codon))) over ordered CDS sense codons",
        "per_gene_tai_orfs": len(out),
        "per_gene_tai_skipped": dict(sorted(skipped.items())),
    }


def in_sample_projected_r2(design: list[list[float]], target: list[float]) -> float:
    target_norm2 = sum(value * value for value in target)
    if target_norm2 <= EPS:
        return 0.0
    basis = orthonormal_basis_from_columns(design)
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    return max(0.0, min(1.0, energy / target_norm2))


def cannot_claim() -> list[str]:
    return [
        "observational held-out prediction, not causal proof",
        "tRNA gene copy number is a proxy for tRNA abundance, not direct tRNA-seq",
        "dos Reis wobble penalties are a modeling choice",
        "measured TE, mRNA stability, turnover, proteomics, and GtRNAdb are cross-dataset joins with possible condition/platform mismatch",
        "a failed increment does not falsify tRNA biology; it means this fixed tAI readout did not clear the specified held-out/null gates beyond the measured dictionary",
    ]


def main() -> None:
    repo = pathlib.Path.cwd()
    required = [
        repo / ORDERED_CDS_PATH,
        repo / CDS_ABUNDANCE_PATH,
        repo / "tools/bio_reality/data/ncbi_genetic_codes.json",
        repo / "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json",
        repo / "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
        repo / "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json",
    ]
    if not (repo / TRNA_SUMMARY_PATH).exists() and not (repo / GTRNADB_FASTA_PATH).exists():
        required.extend([repo / TRNA_SUMMARY_PATH, repo / GTRNADB_FASTA_PATH])
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local yeast data are missing", missing_required_data=missing)

    try:
        context = residual_dictionary.q6_context(repo)
        yeast_config = next(config for config in residual_dictionary.ORGANISMS if config["key"] == ORGANISM)
        built = residual_dictionary.base_rows(repo=repo, context=context, config=yeast_config)
        if built.get("status") != "computed":
            emit("needs_data", reason=built.get("reason", "yeast base rows unavailable"), data_summary=built)
        rows = built.get("rows")
        if not isinstance(rows, dict):
            raise ValueError("yeast base rows malformed")

        attached = residual_dictionary.attach_h_readouts(repo, ORGANISM, rows)  # type: ignore[arg-type]
        code = context["code"]
        codons = context["codons"]
        if not isinstance(code, dict) or not isinstance(codons, list):
            raise ValueError("q6 context malformed")

        trna_records, trna_source_summary = load_trna_records(repo)
        weights, raw_w, contributors = codon_w_values(code=code, codons=codons, records=trna_records)  # type: ignore[arg-type]
        ordered_by_orf, ordered_summary = ordered_cds_by_orf(repo)
        tai_by_orf, tai_gene_summary = per_gene_tai_from_ordered_cds(
            ordered_by_orf=ordered_by_orf,
            weights=weights,
            code=code,  # type: ignore[arg-type]
        )
        protein_orf = protein_to_yeast_orf(repo, rows)  # type: ignore[arg-type]

        selected_ids: list[str] = []
        skipped_join: Counter[str] = Counter()
        for protein_id in sorted(rows):
            row = rows[protein_id]
            h_map = row.get("h")
            orf = protein_orf.get(protein_id)
            if not isinstance(row.get("t"), list):
                skipped_join["missing_measured_te"] += 1
                continue
            if not isinstance(row.get("s"), list):
                skipped_join["missing_mrna_stability"] += 1
                continue
            if not isinstance(h_map, dict) or "turnover" not in h_map:
                skipped_join["missing_turnover"] += 1
                continue
            if orf is None:
                skipped_join["missing_orf"] += 1
                continue
            if orf not in tai_by_orf:
                skipped_join["missing_tai"] += 1
                continue
            selected_ids.append(protein_id)

        if len(selected_ids) < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_data",
                reason=f"active yeast join yielded n={len(selected_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
                n_join=len(selected_ids),
                skipped_join=dict(sorted(skipped_join.items())),
                data_summary=built.get("summary"),
                H_source_summaries=attached.get("source_summaries") if isinstance(attached, dict) else None,
            )

        selected_rows = [rows[protein_id] for protein_id in selected_ids]  # type: ignore[index]
        z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
        p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
        target = matrix_column(p_e, 0)

        base_raw: list[list[float]] = []
        tai_raw: list[list[float]] = []
        for protein_id in selected_ids:
            row = rows[protein_id]  # type: ignore[index]
            h_map = row["h"]
            if not isinstance(h_map, dict):
                raise ValueError("row h map malformed")
            orf = protein_orf[protein_id]
            base_raw.append(
                list(row["t"])  # type: ignore[arg-type]
                + list(row["s"])  # type: ignore[arg-type]
                + list(h_map["turnover"])  # type: ignore[arg-type]
            )
            tai_raw.append([tai_by_orf[orf]])

        base_resid = residualize_with_basis(base_raw, z_basis)
        tai_resid = residualize_with_basis(tai_raw, z_basis)
        base_design, base_scaling = standardize_columns(base_resid)
        tai_design, tai_scaling = standardize_columns(tai_resid)
        full_design = append_columns(base_design, tai_design)
        folds = folds_for_n(len(selected_ids), FOLD_COUNT)

        held_out_delta_r2, base_r2, full_r2 = cv_delta_r2(base_design, full_design, target, folds)
        tai_alone_r2 = cv_r2(tai_design, target, folds)
        in_sample_delta = in_sample_projected_r2(full_design, target) - in_sample_projected_r2(base_design, target)

        null_values: list[float] = []
        for trial in range(PERMUTATION_COUNT):
            permutation = deterministic_permutation(len(target), f"{SEED}|trial={trial}")
            permuted_target = [target[permutation[index]] for index in range(len(target))]
            delta, _base_null, _full_null = cv_delta_r2(base_design, full_design, permuted_target, folds)
            null_values.append(delta)
        null95 = percentile_nearest_rank(null_values, 0.95)

        increment_exceeds_null = held_out_delta_r2 > null95
        held_out_positive = held_out_delta_r2 > 0.0
        trna_supply_computed = all(math.isfinite(value) and value > 0.0 for value in weights.values()) and all(
            math.isfinite(row[0]) and row[0] > 0.0 for row in tai_raw
        )

        checks = [
            {
                "name": "trna_supply_computed",
                "passed": trna_supply_computed,
                "actual": {
                    "usable_tai_record_count": trna_source_summary.get("usable_tai_record_count"),
                    "codon_weight_count": len(weights),
                    "per_gene_tai_joined": len(tai_raw),
                    "zero_raw_W_filled_by_geometric_mean_count": sum(1 for value in raw_w.values() if value == 0.0),
                },
                "expected": "finite positive codon tAI weights and per-gene geometric tAI values from GtRNAdb tGCN plus wobble",
            },
            {
                "name": "increment_exceeds_null",
                "passed": increment_exceeds_null,
                "actual": {"held_out_delta_r2": held_out_delta_r2, "null95": null95},
                "expected": "held_out_delta_r2 > null95 under fixed-readout target permutation null",
            },
            {
                "name": "held_out_positive",
                "passed": held_out_positive,
                "actual": held_out_delta_r2,
                "expected": "held_out_delta_r2 > 0",
            },
        ]

        status = "passed" if trna_supply_computed and increment_exceeds_null and held_out_positive else "failed"
        failed_gates = [check["name"] for check in checks if not check["passed"]]
        reason = None if status == "passed" else "tRNA supply increment did not clear every fixed gate: " + ",".join(failed_gates)

        payload = {
            "held_out_delta_r2": held_out_delta_r2,
            "null95": null95,
            "tAI_alone_r2": tai_alone_r2,
            "base_r2": base_r2,
            "full_r2": full_r2,
            "n_join": len(selected_ids),
            "wobble_rule": {
                "definition": "dos Reis tAI: W_codon = sum_over_same-aa isoacceptors (1-s_wobble) * tGCN when anticodon positions 2/3 pair codon positions 2/1; w_codon = W_codon / max(W); zero W filled by geometric mean of nonzero normalized W",
                "s_values": {f"{left}:{right}": value for (left, right), value in DOS_REIS_2004_WOBBLE_S.items()},
                "canonical_watson_crick_s": 0.0,
                "anticodon_A_treated_as_inosine": True,
                "initiator_iMet_excluded_from_elongator_tai": True,
            },
            "permutation_count": PERMUTATION_COUNT,
            "seed": SEED,
        }
        emit(
            status,
            reason=reason,
            checks=checks,
            payload=payload,
            result={
                **payload,
                "target": "log10 protein abundance residualized against sibling Z controls on the yeast join",
                "base_design": "Z-residualized and standardized measured dictionary columns: log10(measured_te), log10(mrna_stability), turnover",
                "full_design": "base_design plus Z-residualized standardized per-gene tAI geometric mean",
                "ridge": RIDGE,
                "fold_count": FOLD_COUNT,
                "fold_rule": "deterministic index modulo 5 over sorted active protein ids",
                "null_model": "fixed readouts/folds; deterministic SHA256 permutations of gene-to-target labels; statistic is held-out delta R2(full-base)",
                "null_mean": mean(null_values),
                "null_min": min(null_values) if null_values else None,
                "null_max": max(null_values) if null_values else None,
                "in_sample_delta_r2_context_only": in_sample_delta,
                "readout_scaling": {"base_columns": base_scaling, "tai_column": tai_scaling},
                "readout_names": ["measured_te", "mrna_stability", "turnover", "tAI"],
                "controls_used": residual_dictionary.controls_used(context["aa_order"]),  # type: ignore[arg-type]
                "trna_source_summary": trna_source_summary,
                "tai_weight_summary": {
                    "codon_weight_count": len(weights),
                    "raw_W_by_codon": raw_w,
                    "normalized_w_by_codon": weights,
                    "zero_raw_W_filled_by_geometric_mean_count": sum(1 for value in raw_w.values() if value == 0.0),
                    "tai_contributor_contact_count": len(contributors),
                },
                "ordered_cds_summary": ordered_summary,
                "per_gene_tai_summary": tai_gene_summary,
                "base_join_summary": built.get("summary"),
                "H_source_summaries": attached.get("source_summaries") if isinstance(attached, dict) else None,
                "active_join_skipped": dict(sorted(skipped_join.items())),
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable tRNA-supply increment input or fit")


if __name__ == "__main__":
    main()

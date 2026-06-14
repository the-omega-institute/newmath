#!/usr/bin/env python3
"""Translation-conditioned B*_Q6 boundary test for structural order.

This held-out boundary audit asks whether the 9-dimensional synonymous
B*_Q6 residual predicts per-protein structural-order proxy values after
translation controls and composition controls are already available.  The
verdict is decided only by the full-control increment:

    translation + protein length + 20 amino-acid composition + GC3 -> + B*_Q6

The structural readout here is the local data file's AlphaFold mean-pLDDT
derived "structural_order" proxy, not an experimental phenotype.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


EXPERIMENT_ID = "b_star_q6_translation_conditioned_structural_order_boundary_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_conditioned_structural_order_boundary.b_star_q6_powered"

DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
RIDGE = 1e-5
MIN_JOINED = 300
MIN_PRIMARY_ORGANISMS_FOR_CROSSES = 2
FULL_DELTA_EPS = 0.001
SIGNIFICANCE_ALPHA = 0.05

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
    },
]

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]


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
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def standard_code() -> dict[str, str]:
    raw = load_json(DATA_DIR / "ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("NCBI genetic-code payload must be an object")
    codon_order = raw.get("codon_order")
    tables = raw.get("tables")
    if not isinstance(codon_order, list) or not isinstance(tables, list):
        raise ValueError("NCBI genetic-code payload is malformed")
    table = next((item for item in tables if isinstance(item, dict) and item.get("table_id") == 1), None)
    if not isinstance(table, dict) or not isinstance(table.get("aa"), str):
        raise ValueError("standard genetic-code table is missing")
    aa = table["aa"]
    if len(codon_order) != len(aa):
        raise ValueError("standard genetic-code codon and aa rows differ in length")
    return {str(codon): aa[index] for index, codon in enumerate(codon_order)}


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def q_vectors(codons: list[str]) -> dict[str, dict[str, float]]:
    raw: dict[str, dict[str, float]] = {}
    q = zero(codons); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero(codons)
    for c in ["AGA", "AGG"]:
        q[c] = 1.0
    for c in ["CGU", "CGC", "CGA", "CGG"]:
        q[c] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for c in CUN_CODONS:
        q[c] = 0.25
    for c in UUR_CODONS:
        q[c] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for c in ["UCA", "UCG"]:
        q[c] = 0.5
    for c in ["AGU", "AGC"]:
        q[c] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for c in ["ACA", "ACG"]:
        q[c] = 0.5
    for c in ["ACU", "ACC"]:
        q[c] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def standard_amino_acids(code: dict[str, str], codons: list[str]) -> list[str]:
    aas = sorted({code[codon] for codon in codons if code[codon] != "*"})
    if len(aas) != 20:
        raise ValueError(f"standard genetic code should expose 20 amino acids, got {len(aas)}")
    return aas


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0.0 or int(value) != value:
                raise ValueError(f"{organism}.joined[{row_index}].codon_counts.{raw_codon} must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def te_indices(payload: dict[str, object], organism: str) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} TE payload must contain genes list")
    by_protein: dict[str, dict[str, float]] = {}
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
        if protein_id in by_protein:
            skipped["duplicate_protein_id"] += 1
            continue
        by_protein[protein_id] = {"te": te, "mrna": mrna, "footprint": footprint}
    return by_protein, {
        "n_genes_with_te_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_valid_te_by_protein": len(by_protein),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "skipped_te_records": skipped,
    }


def structural_order_index(payload: dict[str, object], organism: str) -> tuple[dict[str, float], dict[str, object]]:
    proteins = payload.get("proteins")
    if not isinstance(proteins, list):
        raise ValueError(f"{organism} structural-order payload must contain proteins list")
    by_protein: dict[str, float] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "invalid_structural_order": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(proteins):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        value = numeric(item.get("structural_order"), f"{organism}.proteins[{row_index}].structural_order")
        if value < 0.0 or value > 100.0:
            skipped["invalid_structural_order"] += 1
            continue
        if protein_id in by_protein:
            skipped["duplicate_protein_id"] += 1
            continue
        by_protein[protein_id] = value
    return by_protein, {
        "readout_kind": payload.get("readout_kind") or "alphafold_mean_plddt_structural_order_proxy",
        "readout_transform": "raw structural_order value on 0..100; no log/logit transform",
        "n_proteins_with_order_reported": payload.get("n_proteins_with_order"),
        "n_valid_structural_order_by_protein": len(by_protein),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "id_mapping_method": payload.get("id_mapping_method"),
        "payload_sha256": payload.get("payload_sha256"),
        "sample_source_verification": payload.get("sample_source_verification"),
        "cannot_claim_from_payload": payload.get("cannot_claim"),
        "skipped_structural_order_records": skipped,
    }


def joined_rows(
    *,
    organism: str,
    label: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    cds_payload = load_json(DATA_DIR / f"cds_codon_abundance_{organism}.json")
    te_payload = load_json(DATA_DIR / f"ribosome_te_{organism}.json")
    structural_payload = load_json(DATA_DIR / f"structural_order_{organism}.json")
    if not isinstance(cds_payload, dict) or not isinstance(te_payload, dict) or not isinstance(structural_payload, dict):
        raise ValueError(f"{organism} input payloads must be JSON objects")
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")

    te_by_protein, te_summary = te_indices(te_payload, organism)
    order_by_protein, order_summary = structural_order_index(structural_payload, organism)

    rows: list[dict[str, object]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "duplicate_protein_id": 0,
        "no_structural_order_match": 0,
        "no_te_match": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    join_sources = {"structural_order_protein_id": 0, "te_protein_id": 0}
    seen: set[str] = set()

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if protein_id in seen:
            skipped["duplicate_protein_id"] += 1
            continue
        structural_order = order_by_protein.get(protein_id)
        if structural_order is None:
            skipped["no_structural_order_match"] += 1
            continue
        join_sources["structural_order_protein_id"] += 1

        te_record = te_by_protein.get(protein_id)
        if te_record is None:
            skipped["no_te_match"] += 1
            continue
        join_sources["te_protein_id"] += 1

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
        bstar = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts")
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total

        rows.append(
            {
                "protein_id": protein_id,
                "stable_id": protein_id,
                "y": structural_order,
                "bstar": bstar,
                "translation": [
                    math.log10(abundance),
                    math.log10(te_record["te"]),
                    math.log10(te_record["mrna"]),
                    math.log10(te_record["footprint"]),
                ],
                "composition_controls": [math.log(cds_len_nt)]
                + [aa_counts[aa] / aa_total for aa in aa_order]
                + [gc3],
            }
        )
        seen.add(protein_id)

    summary = {
        "organism_label": label,
        "readout": "structural_order",
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined": len(rows),
        "join_sources": join_sources,
        "skipped_cds_records": skipped,
        "translation_summary": te_summary,
        "structural_order_summary": order_summary,
    }
    return rows, summary


def stable_hash_int(text: str) -> int:
    digest = hashlib.sha256(f"{SEED}|{text}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


def matrix_for(rows: list[dict[str, object]], feature_blocks: list[str]) -> list[list[float]]:
    matrix: list[list[float]] = []
    for row in rows:
        values: list[float] = []
        for block in feature_blocks:
            raw = row[block]
            if not isinstance(raw, list):
                raise ValueError(f"feature block {block} is not a list")
            values.extend(float(value) for value in raw)
        matrix.append(values)
    return matrix


def y_for(rows: list[dict[str, object]]) -> list[float]:
    return [float(row["y"]) for row in rows]


def deterministic_folds(rows: list[dict[str, object]], organism: str, readout: str, fold_count: int) -> list[int]:
    order = sorted(
        range(len(rows)),
        key=lambda idx: stable_hash_int(f"fold|{organism}|{readout}|{rows[idx]['stable_id']}|{idx}"),
    )
    folds = [0 for _ in rows]
    for rank, index in enumerate(order):
        folds[index] = rank % fold_count
    return folds


def train_standardize(x_train: list[list[float]]) -> tuple[list[float], list[float]]:
    if not x_train:
        return [], []
    width = len(x_train[0])
    centers: list[float] = []
    scales: list[float] = []
    for col in range(width):
        values = [row[col] for row in x_train]
        center = sum(values) / len(values)
        var = sum((value - center) * (value - center) for value in values) / max(1, len(values) - 1)
        scale = math.sqrt(var)
        if scale <= EPS:
            scale = 1.0
        centers.append(center)
        scales.append(scale)
    return centers, scales


def apply_standardize(x_rows: list[list[float]], centers: list[float], scales: list[float]) -> list[list[float]]:
    return [
        [(row[col] - centers[col]) / scales[col] for col in range(len(row))]
        for row in x_rows
    ]


def invert_matrix(matrix: list[list[float]], ridge: float = RIDGE) -> list[list[float]]:
    n = len(matrix)
    aug = []
    for row in range(n):
        left = list(matrix[row])
        left[row] += ridge
        right = [0.0 for _ in range(n)]
        right[row] = 1.0
        aug.append(left + right)
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += ridge * 100.0 + EPS
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        if abs(scale) <= EPS:
            scale = EPS if scale >= 0 else -EPS
        for item in range(2 * n):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(2 * n):
                aug[row][item] -= factor * aug[col][item]
    return [row[n:] for row in aug]


def fit_ridge(x_train: list[list[float]], y_train: list[float]) -> list[float]:
    if not x_train:
        raise ValueError("empty training matrix")
    width = len(x_train[0]) + 1
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, y in zip(x_train, y_train):
        design = [1.0] + row
        for i in range(width):
            xty[i] += design[i] * y
            for j in range(width):
                xtx[i][j] += design[i] * design[j]
    for i in range(1, width):
        xtx[i][i] += RIDGE
    inv = invert_matrix(xtx, ridge=EPS)
    return [sum(inv[row][col] * xty[col] for col in range(width)) for row in range(width)]


def predict_ridge(beta: list[float], x_rows: list[list[float]]) -> list[float]:
    return [beta[0] + sum(beta[col + 1] * row[col] for col in range(len(row))) for row in x_rows]


def r2_score(y_true: list[float], y_pred: list[float], center: float | None = None) -> float | None:
    if len(y_true) != len(y_pred) or not y_true:
        return None
    baseline = mean(y_true) if center is None else center
    if baseline is None:
        return None
    sst = sum((value - baseline) * (value - baseline) for value in y_true)
    if sst <= EPS:
        return None
    sse = sum((truth - pred) * (truth - pred) for truth, pred in zip(y_true, y_pred))
    return 1.0 - sse / sst


def pearson(y_true: list[float], y_pred: list[float]) -> float | None:
    if len(y_true) != len(y_pred) or len(y_true) < 2:
        return None
    y_mean = mean(y_true)
    p_mean = mean(y_pred)
    if y_mean is None or p_mean is None:
        return None
    num = sum((y - y_mean) * (p - p_mean) for y, p in zip(y_true, y_pred))
    den_y = math.sqrt(sum((y - y_mean) * (y - y_mean) for y in y_true))
    den_p = math.sqrt(sum((p - p_mean) * (p - p_mean) for p in y_pred))
    if den_y <= EPS or den_p <= EPS:
        return None
    return num / (den_y * den_p)


def evaluate_regression(y_true: list[float], y_pred: list[float], global_center: float) -> dict[str, object]:
    y_mean = mean(y_true)
    return {
        "n_tested": len(y_true),
        "held_out_r2": r2_score(y_true, y_pred, center=global_center),
        "pearson_r": pearson(y_true, y_pred),
        "y_mean": y_mean,
        "y_sd": None if len(y_true) < 2 or y_mean is None else math.sqrt(sum((value - y_mean) ** 2 for value in y_true) / (len(y_true) - 1)),
    }


def cross_validated_ridge(rows: list[dict[str, object]], feature_blocks: list[str], organism: str, readout: str) -> dict[str, object]:
    x_all = matrix_for(rows, feature_blocks)
    y_all = y_for(rows)
    folds = deterministic_folds(rows, organism, readout, FOLD_COUNT)
    all_true: list[float] = []
    all_pred: list[float] = []
    fold_metrics: list[dict[str, object]] = []
    global_center = float(mean(y_all))
    for fold in range(FOLD_COUNT):
        train_indices = [index for index, value in enumerate(folds) if value != fold]
        test_indices = [index for index, value in enumerate(folds) if value == fold]
        x_train_raw = [x_all[index] for index in train_indices]
        x_test_raw = [x_all[index] for index in test_indices]
        y_train = [y_all[index] for index in train_indices]
        y_test = [y_all[index] for index in test_indices]
        centers, scales = train_standardize(x_train_raw)
        x_train = apply_standardize(x_train_raw, centers, scales)
        x_test = apply_standardize(x_test_raw, centers, scales)
        beta = fit_ridge(x_train, y_train)
        pred = predict_ridge(beta, x_test)
        all_true.extend(y_test)
        all_pred.extend(pred)
        fold_metrics.append(evaluate_regression(y_test, pred, global_center))
    metrics = evaluate_regression(all_true, all_pred, global_center)
    metrics["feature_blocks"] = feature_blocks
    metrics["feature_count"] = len(x_all[0]) if x_all else 0
    metrics["fold_count"] = FOLD_COUNT
    metrics["fold_metrics"] = [
        {
            "fold": index,
            "n_tested": item["n_tested"],
            "held_out_r2": item["held_out_r2"],
            "pearson_r": item["pearson_r"],
        }
        for index, item in enumerate(fold_metrics)
    ]
    return metrics


def mean_baseline(rows: list[dict[str, object]], organism: str, readout: str) -> dict[str, object]:
    y_all = y_for(rows)
    folds = deterministic_folds(rows, organism, readout, FOLD_COUNT)
    all_true: list[float] = []
    all_pred: list[float] = []
    fold_metrics: list[dict[str, object]] = []
    global_center = float(mean(y_all))
    for fold in range(FOLD_COUNT):
        train = [y_all[index] for index, value in enumerate(folds) if value != fold]
        test = [y_all[index] for index, value in enumerate(folds) if value == fold]
        pred_value = float(mean(train))
        pred = [pred_value for _ in test]
        all_true.extend(test)
        all_pred.extend(pred)
        fold_metrics.append(evaluate_regression(test, pred, global_center))
    metrics = evaluate_regression(all_true, all_pred, global_center)
    metrics["feature_blocks"] = ["train_fold_mean_baseline"]
    metrics["feature_count"] = 0
    metrics["fold_count"] = FOLD_COUNT
    metrics["fold_metrics"] = [
        {
            "fold": index,
            "n_tested": item["n_tested"],
            "held_out_r2": item["held_out_r2"],
            "pearson_r": item["pearson_r"],
        }
        for index, item in enumerate(fold_metrics)
    ]
    return metrics


def permutation_rows(rows: list[dict[str, object]], block: str, organism: str, readout: str) -> list[dict[str, object]]:
    shuffled = [dict(row) for row in rows]
    values = [row[block] for row in rows]
    order = sorted(
        range(len(values)),
        key=lambda index: stable_hash_int(f"permute|{organism}|{readout}|{block}|{rows[index]['stable_id']}|{index}"),
    )
    permuted = [None for _ in values]
    for target_rank, source_index in enumerate(order):
        target_index = order[(target_rank + 1) % len(order)]
        permuted[target_index] = values[source_index]
    for index, value in enumerate(permuted):
        shuffled[index][block] = value
    return shuffled


def delta(newer: dict[str, object], older: dict[str, object]) -> dict[str, object]:
    r2_new = newer.get("held_out_r2")
    r2_old = older.get("held_out_r2")
    return {
        "delta_held_out_r2": None if not isinstance(r2_new, float) or not isinstance(r2_old, float) else r2_new - r2_old,
    }


def fold_deltas(newer: dict[str, object], older: dict[str, object]) -> list[float]:
    newer_folds = newer.get("fold_metrics")
    older_folds = older.get("fold_metrics")
    if not isinstance(newer_folds, list) or not isinstance(older_folds, list):
        return []
    out: list[float] = []
    for n_item, o_item in zip(newer_folds, older_folds):
        if not isinstance(n_item, dict) or not isinstance(o_item, dict):
            continue
        n_r2 = n_item.get("held_out_r2")
        o_r2 = o_item.get("held_out_r2")
        if isinstance(n_r2, float) and isinstance(o_r2, float):
            out.append(n_r2 - o_r2)
    return out


def summarize_numbers(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "positive_count": sum(1 for value in values if value > 0.0),
        "negative_count": sum(1 for value in values if value < 0.0),
    }


def exact_signflip_p_greater(values: list[float]) -> float | None:
    nonzero = [abs(value) for value in values if abs(value) > EPS]
    observed = sum(values)
    n = len(nonzero)
    if n == 0:
        return None
    if n > 22:
        positives = sum(1 for value in values if value > 0.0)
        return sum(math.comb(n, k) for k in range(positives, n + 1)) / (2 ** n)
    extreme = 0
    total = 1 << n
    for mask in range(total):
        signed = 0.0
        for bit, magnitude in enumerate(nonzero):
            signed += magnitude if (mask >> bit) & 1 else -magnitude
        if signed >= observed - EPS:
            extreme += 1
    return extreme / total


def aggregate_results(results: list[dict[str, object]]) -> dict[str, object]:
    full = [float(item["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]) for item in results]
    translation = [float(item["incremental"]["bstar_q6_given_translation_controls"]["delta_held_out_r2"]) for item in results]
    bstar = [float(item["incremental"]["bstar_q6_vs_mean_baseline"]["delta_held_out_r2"]) for item in results]
    permuted_full = [float(item["incremental"]["permuted_bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]) for item in results]
    n_total = sum(int(item["n_model_rows"]) for item in results)
    weighted_full = None if n_total <= 0 else sum(
        float(item["n_model_rows"]) * float(item["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"])
        for item in results
    ) / n_total
    weighted_permuted = None if n_total <= 0 else sum(
        float(item["n_model_rows"]) * float(item["incremental"]["permuted_bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"])
        for item in results
    ) / n_total
    fold_delta_values: list[float] = []
    permuted_fold_delta_values: list[float] = []
    for item in results:
        fold_delta_values.extend(float(value) for value in item.get("full_control_fold_deltas", []) if isinstance(value, (int, float)))
        permuted_fold_delta_values.extend(float(value) for value in item.get("permuted_full_control_fold_deltas", []) if isinstance(value, (int, float)))
    return {
        "n_primary_organisms": len(results),
        "n_total_rows": n_total,
        "bstar_q6_vs_mean_baseline_delta_r2": summarize_numbers(bstar),
        "translation_conditioned_delta_r2": summarize_numbers(translation),
        "full_control_delta_r2": summarize_numbers(full),
        "permuted_full_control_delta_r2": summarize_numbers(permuted_full),
        "weighted_full_control_delta_r2": weighted_full,
        "weighted_permuted_full_control_delta_r2": weighted_permuted,
        "full_control_fold_delta_summary": summarize_numbers(fold_delta_values),
        "permuted_full_control_fold_delta_summary": summarize_numbers(permuted_fold_delta_values),
        "full_control_signflip_p_greater_zero": exact_signflip_p_greater(fold_delta_values),
        "permuted_full_control_signflip_p_greater_zero": exact_signflip_p_greater(permuted_fold_delta_values),
        "positive_primary_organism_count": sum(1 for value in full if value > 0.0),
        "primary_organisms": [item["organism"] for item in results],
    }


def organism_call(result: dict[str, object]) -> str:
    full_delta = result["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]
    trans_delta = result["incremental"]["bstar_q6_given_translation_controls"]["delta_held_out_r2"]
    if not isinstance(full_delta, float) or not isinstance(trans_delta, float):
        return "insufficient_metric"
    if full_delta >= FULL_DELTA_EPS and trans_delta > 0.0:
        return "full_control_positive"
    if full_delta > 0.0 or trans_delta > 0.0:
        return "partial"
    return "mediated_blocked_null"


def verdict_from_aggregate(aggregate: dict[str, object]) -> str:
    n_org = int(aggregate.get("n_primary_organisms", 0))
    weighted_full = aggregate.get("weighted_full_control_delta_r2")
    weighted_permuted = aggregate.get("weighted_permuted_full_control_delta_r2")
    p_value = aggregate.get("full_control_signflip_p_greater_zero")
    positive_count = int(aggregate.get("positive_primary_organism_count", 0))
    if (
        n_org >= MIN_PRIMARY_ORGANISMS_FOR_CROSSES
        and isinstance(weighted_full, float)
        and isinstance(weighted_permuted, float)
        and isinstance(p_value, float)
        and weighted_full >= FULL_DELTA_EPS
        and weighted_full > weighted_permuted + FULL_DELTA_EPS
        and p_value <= SIGNIFICANCE_ALPHA
        and positive_count >= MIN_PRIMARY_ORGANISMS_FOR_CROSSES
    ):
        return "crosses_to_structural_order_layer"
    if positive_count > 0 or (isinstance(weighted_full, float) and weighted_full > 0.0):
        return "partial"
    return "mediated_blocked_null"


def run_organism(
    *,
    organism: str,
    label: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> dict[str, object]:
    rows, data_summary = joined_rows(
        organism=organism,
        label=label,
        code=code,
        codons=codons,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
    )
    powered = len(rows) >= MIN_JOINED
    base_result = {
        "organism": organism,
        "label": label,
        "readout": "structural_order",
        "status": "computed" if powered else "needs_data",
        "powered": powered,
        "n_model_rows": len(rows),
        "data_summary": data_summary,
        "power_note": None if powered else f"交集不足 n={len(rows)} < {MIN_JOINED}；该 organism 不进入 headline aggregate。",
    }
    if not powered:
        return base_result

    readout = "structural_order"
    baseline = mean_baseline(rows, organism, readout)
    bstar = cross_validated_ridge(rows, ["bstar"], organism, readout)
    translation = cross_validated_ridge(rows, ["translation"], organism, readout)
    translation_bstar = cross_validated_ridge(rows, ["translation", "bstar"], organism, readout)
    full = cross_validated_ridge(rows, ["translation", "composition_controls"], organism, readout)
    full_bstar = cross_validated_ridge(rows, ["translation", "composition_controls", "bstar"], organism, readout)
    composition = cross_validated_ridge(rows, ["composition_controls"], organism, readout)
    permuted_rows = permutation_rows(rows, "bstar", organism, readout)
    translation_permuted_bstar = cross_validated_ridge(permuted_rows, ["translation", "bstar"], organism, readout)
    full_permuted_bstar = cross_validated_ridge(permuted_rows, ["translation", "composition_controls", "bstar"], organism, readout)

    result = {
        **base_result,
        "metrics": {
            "mean_baseline": baseline,
            "bstar_q6_only": bstar,
            "translation_controls_only": translation,
            "translation_plus_bstar_q6": translation_bstar,
            "translation_plus_length_aa_gc_controls": full,
            "translation_plus_length_aa_gc_controls_plus_bstar_q6": full_bstar,
            "length_aa_gc_controls_only": composition,
            "translation_plus_permuted_bstar_q6": translation_permuted_bstar,
            "translation_plus_length_aa_gc_controls_plus_permuted_bstar_q6": full_permuted_bstar,
        },
        "incremental": {
            "bstar_q6_vs_mean_baseline": delta(bstar, baseline),
            "bstar_q6_given_translation_controls": delta(translation_bstar, translation),
            "bstar_q6_given_translation_length_aa_gc_controls": delta(full_bstar, full),
            "permuted_bstar_q6_given_translation_controls": delta(translation_permuted_bstar, translation),
            "permuted_bstar_q6_given_translation_length_aa_gc_controls": delta(full_permuted_bstar, full),
        },
        "full_control_fold_deltas": fold_deltas(full_bstar, full),
        "permuted_full_control_fold_deltas": fold_deltas(full_permuted_bstar, full),
    }
    result["organism_readout_call"] = organism_call(result)
    return result


def cannot_claim() -> list[str]:
    return [
        "这是横截面 held-out 预测边界实验，不是共翻译折叠机制或因果中介实验。",
        "structural_order 来自本地 AlphaFold mean-pLDDT 派生 proxy；它不是实验结构有序度、功能、适应度或表型测量。",
        "translation 控制为同一基因的 log10 protein abundance、measured TE、mRNA、footprint；不能证明翻译层已被完全观测。",
        "全控 verdict 使用 translation + protein length + 20 amino-acid composition + GC3 后的 B*_Q6 增量；只控 translation 的增量不决定 crosses。",
        "fold-level sign-flip null 和 within-organism B*_Q6 permutation 是确定性诊断，不是 phylogenetic 或 perturbational causality test。",
        "只有两个物种有本 readout；跨物种 aggregate power 有限，单物种正信号只可判 partial。",
        "若全控增量为零或为负，解释为本数据和此模型下 composition/translation 控制吸收了可见 structural-order proxy 信息，不等于真实生物信号不存在。",
    ]


def main() -> None:
    required = [DATA_DIR / "ncbi_genetic_codes.json"]
    for item in ORGANISMS:
        organism = str(item["organism"])
        required.extend(
            [
                DATA_DIR / f"cds_codon_abundance_{organism}.json",
                DATA_DIR / f"ribosome_te_{organism}.json",
                DATA_DIR / f"structural_order_{organism}.json",
            ]
        )
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local CDS/TE/structural-order data not present", missing_required_data=missing)

    try:
        code = standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        if q_names != [
            "K_AAA",
            "Arg_AGR",
            "Ile_AUA",
            "Leu_CUN_vs_UUR",
            "Leu_UUA_vs_UUG",
            "Ser_UCR_vs_AGY",
            "Ser_UCA_vs_UCG",
            "Thr_ACR_vs_ACY",
            "f3_stress",
        ]:
            raise ValueError(f"B*_Q6 coordinate order drifted: {q_names}")

        all_results: dict[str, dict[str, object]] = {}
        primary_results: list[dict[str, object]] = []
        for item in ORGANISMS:
            organism = str(item["organism"])
            label = str(item["label"])
            result = run_organism(
                organism=organism,
                label=label,
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
            )
            if result.get("powered") is True:
                result["headline_primary_readout"] = True
                primary_results.append(result)
            all_results[organism] = result

        if not primary_results:
            emit(
                "needs_data",
                reason="no organism had enough structural-order/translation/CDS overlap",
                checks=[
                    {"name": "structural_order_joined", "passed": False, "actual": all_results},
                    {"name": "bstar_q6_predicts_order", "passed": False},
                    {"name": "translation_conditioned_order_verdict", "passed": False},
                ],
            )

        aggregate = aggregate_results(primary_results)
        verdict = verdict_from_aggregate(aggregate)
        call_counts: dict[str, int] = {}
        for result in primary_results:
            call = str(result.get("organism_readout_call"))
            call_counts[call] = call_counts.get(call, 0) + 1

        joined_ok = len(primary_results) >= 1 and all(int(result.get("n_model_rows", 0)) >= MIN_JOINED for result in primary_results)
        bstar_metrics_ok = all(
            isinstance(result["incremental"]["bstar_q6_vs_mean_baseline"]["delta_held_out_r2"], float)
            for result in primary_results
        )
        boundary_ok = verdict in {"crosses_to_structural_order_layer", "mediated_blocked_null", "partial"}

        checks = [
            {
                "name": "structural_order_joined",
                "passed": joined_ok,
                "expected": f"at least one primary organism has >= {MIN_JOINED} rows after CDS/structural_order/TE join",
                "actual": {
                    organism: result.get("n_model_rows")
                    for organism, result in all_results.items()
                },
            },
            {
                "name": "bstar_q6_predicts_order",
                "passed": bstar_metrics_ok,
                "expected": "B*_Q6-only held-out R2 and delta versus train-fold mean baseline computed for every primary organism",
                "actual": aggregate["bstar_q6_vs_mean_baseline_delta_r2"],
            },
            {
                "name": "translation_conditioned_order_verdict",
                "passed": boundary_ok,
                "expected": "one of crosses_to_structural_order_layer / mediated_blocked_null / partial, decided by cross-organism full-control aggregate",
                "actual": {
                    "verdict": verdict,
                    "organism_call_counts": call_counts,
                    "aggregate_full_control_delta_r2": aggregate["full_control_delta_r2"],
                    "weighted_full_control_delta_r2": aggregate["weighted_full_control_delta_r2"],
                    "full_control_signflip_p_greater_zero": aggregate["full_control_signflip_p_greater_zero"],
                    "permuted_full_control_delta_r2": aggregate["permuted_full_control_delta_r2"],
                },
            },
        ]

        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            verdict=verdict,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_joined=MIN_JOINED,
            readout_policy={
                "configured_organisms": ORGANISMS,
                "headline_aggregate_unit": "one structural_order readout per organism",
                "readout": "structural_order from structural_order_<organism>.json",
                "readout_transform": "raw structural_order on 0..100; no log/logit transform",
                "readout_boundary": "AlphaFold mean-pLDDT derived structural-order proxy, not experimental phenotype",
            },
            controls={
                "translation": ["log10 protein abundance ppm", "log10 measured TE", "log10 measured mRNA", "log10 ribosome footprint"],
                "full_control_addons": ["natural log CDS length nt", "20 amino-acid composition fractions in sorted one-letter AA order", "GC3 fraction"],
                "aa_order": aa_order,
                "bstar_q6_coordinates": q_names,
            },
            aggregate=aggregate,
            per_organism=all_results,
            checks=checks,
            null={
                "permuted_bstar_q6": "deterministic one-step circular permutation of B*_Q6 rows within each organism before CV",
                "fold_signflip": "exact one-sided sign-flip p over primary organism full-control fold delta R2 values",
                "crosses_gate": {
                    "requires_primary_organisms_at_least": MIN_PRIMARY_ORGANISMS_FOR_CROSSES,
                    "requires_weighted_full_control_delta_r2_at_least": FULL_DELTA_EPS,
                    "requires_weighted_full_control_delta_exceeds_permuted_by": FULL_DELTA_EPS,
                    "requires_signflip_p_lte": SIGNIFICANCE_ALPHA,
                    "requires_positive_primary_organism_count_at_least": MIN_PRIMARY_ORGANISMS_FOR_CROSSES,
                },
            },
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable structural-order-boundary input or fit")


if __name__ == "__main__":
    main()

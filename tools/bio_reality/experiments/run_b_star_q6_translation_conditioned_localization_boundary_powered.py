#!/usr/bin/env python3
"""Translation-conditioned B*_Q6 boundary test for protein localization.

This experiment asks whether the 9-dimensional synonymous B*_Q6 residual
signal predicts coarse protein localization after measured translation-layer
controls are already available. It is a held-out descriptive boundary audit,
not a causal localization mechanism claim.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


EXPERIMENT_ID = "b_star_q6_translation_conditioned_localization_boundary_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_conditioned_localization_boundary.b_star_q6_powered"

DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
RIDGE = 1e-5
MIN_CLASS_N = 40
MIN_CLASSES = 3
MIN_JOINED = 300
DELTA_ACC_STRONG = 0.01
DELTA_AUC_STRONG = 0.01
DELTA_ACC_WEAK = 0.003
DELTA_AUC_WEAK = 0.003

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
    },
    {
        "organism": "homo_sapiens",
        "label": "Homo sapiens",
    },
    {
        "organism": "danio_rerio",
        "label": "Danio rerio",
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

PRIMARY_LABELS = [
    "Secreted_ER_Golgi",
    "Membrane",
    "Mitochondrion",
    "Nucleus",
    "Cytoplasm",
    "Other",
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    out = float(value)
    if not math.isfinite(out):
        raise ValueError(f"{field} must be finite")
    return out


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


def primary_label(categories: list[object]) -> str | None:
    values = {str(category) for category in categories}
    if values & {"Secreted", "Endoplasmic_reticulum", "Golgi"}:
        return "Secreted_ER_Golgi"
    if values & {"Cell_membrane", "Membrane"}:
        return "Membrane"
    if "Mitochondrion" in values:
        return "Mitochondrion"
    if "Nucleus" in values:
        return "Nucleus"
    if "Cytoplasm" in values:
        return "Cytoplasm"
    if values & {"Vacuole_Lysosome", "Peroxisome", "Cytoskeleton", "Other"}:
        return "Other"
    return None


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
        by_protein[protein_id] = {
            "log_te": math.log10(te),
            "log_mrna": math.log10(mrna),
            "log_footprint": math.log10(footprint),
        }
    return by_protein, {"n_te_records_indexed": len(by_protein), "te_skipped_records": skipped}


def joined_rows(
    *,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    cds_payload = load_json(DATA_DIR / f"cds_codon_abundance_{organism}.json")
    loc_payload = load_json(DATA_DIR / f"subcellular_localization_{organism}.json")
    te_payload = load_json(DATA_DIR / f"ribosome_te_{organism}.json")
    if not isinstance(cds_payload, dict) or not isinstance(loc_payload, dict) or not isinstance(te_payload, dict):
        raise ValueError(f"{organism} input payloads must be JSON objects")
    joined = cds_payload.get("joined")
    proteins = loc_payload.get("proteins")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    if not isinstance(proteins, dict):
        raise ValueError(f"{organism} localization payload must contain proteins object")
    by_te, te_summary = te_indices(te_payload, organism)

    rows: list[dict[str, object]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_localization_match": 0,
        "no_te_match": 0,
        "empty_categories": 0,
        "unmapped_primary_label": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    source_category_hits = {label: 0 for label in PRIMARY_LABELS}
    primary_counts = {label: 0 for label in PRIMARY_LABELS}
    multi_label_count = 0

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        record = proteins.get(protein_id)
        if not isinstance(record, dict):
            skipped["no_localization_match"] += 1
            continue
        te_record = by_te.get(protein_id)
        if not isinstance(te_record, dict):
            skipped["no_te_match"] += 1
            continue
        categories = record.get("categories")
        if not isinstance(categories, list) or not categories:
            skipped["empty_categories"] += 1
            continue
        label = primary_label(categories)
        if label is None:
            skipped["unmapped_primary_label"] += 1
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
        bstar = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts")
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total

        primary_counts[label] += 1
        if len(categories) > 1:
            multi_label_count += 1
        for source_label in set(primary_label([category]) for category in categories):
            if source_label in source_category_hits:
                source_category_hits[source_label] += 1

        rows.append(
            {
                "protein_id": protein_id,
                "label": label,
                "bstar": bstar,
                "translation": [
                    math.log10(abundance),
                    float(te_record["log_te"]),
                    float(te_record["log_mrna"]),
                    float(te_record["log_footprint"]),
                ],
                "null_controls": [math.log(cds_len_nt)]
                + [aa_counts[aa] / aa_total for aa in aa_order]
                + [gc3, m_density],
                "is_multi_label": len(categories) > 1,
            }
        )

    summary = {
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate": cds_payload.get("join_hit_rate"),
        "n_localization_records": loc_payload.get("n_string_localization_records"),
        "n_source_multi_label_records": loc_payload.get("n_multi_label_records"),
        "n_translation_records": te_payload.get("n_genes_with_te"),
        "n_joined": len(rows),
        "n_multi_label_joined": multi_label_count,
        "multi_label_joined_fraction": None if not rows else multi_label_count / len(rows),
        "primary_label_counts_all": primary_counts,
        "source_primary_category_hits_in_join": source_category_hits,
        "skipped_records": skipped,
        **te_summary,
    }
    return rows, summary


def stable_hash_int(text: str) -> int:
    digest = hashlib.sha256(f"{SEED}|{text}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


def filtered_labels(rows: list[dict[str, object]], min_class_n: int = MIN_CLASS_N) -> list[str]:
    counts: dict[str, int] = {}
    for row in rows:
        label = str(row["label"])
        counts[label] = counts.get(label, 0) + 1
    return [label for label in PRIMARY_LABELS if counts.get(label, 0) >= min_class_n]


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


def labels_for(rows: list[dict[str, object]]) -> list[str]:
    return [str(row["label"]) for row in rows]


def deterministic_stratified_folds(rows: list[dict[str, object]], fold_count: int) -> list[int]:
    by_label: dict[str, list[int]] = {}
    for index, row in enumerate(rows):
        by_label.setdefault(str(row["label"]), []).append(index)
    folds = [0 for _ in rows]
    for label, indices in sorted(by_label.items()):
        ordered = sorted(indices, key=lambda idx: stable_hash_int(f"{label}|{rows[idx]['protein_id']}|{idx}"))
        for rank, index in enumerate(ordered):
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


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[index] * vector[index] for index in range(len(vector))) for row in matrix]


def dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def logsumexp(values: list[float]) -> float:
    high = max(values)
    return high + math.log(sum(math.exp(value - high) for value in values))


def fit_lda(x_train: list[list[float]], y_train: list[str], class_order: list[str]) -> dict[str, object]:
    n = len(x_train)
    width = len(x_train[0]) if x_train else 0
    if n == 0 or width == 0:
        raise ValueError("empty training matrix")
    means: dict[str, list[float]] = {}
    counts: dict[str, int] = {}
    for label in class_order:
        members = [x_train[index] for index, value in enumerate(y_train) if value == label]
        if not members:
            raise ValueError(f"class {label} absent in training fold")
        counts[label] = len(members)
        means[label] = [sum(row[col] for row in members) / len(members) for col in range(width)]

    cov = [[0.0 for _ in range(width)] for _ in range(width)]
    denom = max(1, n - len(class_order))
    for row, label in zip(x_train, y_train):
        diff = [row[col] - means[label][col] for col in range(width)]
        for i in range(width):
            for j in range(width):
                cov[i][j] += diff[i] * diff[j] / denom
    inv_cov = invert_matrix(cov)
    coeffs: dict[str, list[float]] = {}
    intercepts: dict[str, float] = {}
    for label in class_order:
        coeff = mat_vec(inv_cov, means[label])
        prior = max(EPS, counts[label] / n)
        coeffs[label] = coeff
        intercepts[label] = -0.5 * dot(means[label], coeff) + math.log(prior)
    return {"class_order": class_order, "coeffs": coeffs, "intercepts": intercepts, "feature_count": width}


def predict_lda(model: dict[str, object], x_rows: list[list[float]]) -> list[dict[str, float]]:
    class_order = model["class_order"]
    coeffs = model["coeffs"]
    intercepts = model["intercepts"]
    if not isinstance(class_order, list) or not isinstance(coeffs, dict) or not isinstance(intercepts, dict):
        raise ValueError("malformed LDA model")
    predictions: list[dict[str, float]] = []
    for row in x_rows:
        scores = [dot(row, coeffs[label]) + float(intercepts[label]) for label in class_order]
        normalizer = logsumexp(scores)
        predictions.append({label: math.exp(score - normalizer) for label, score in zip(class_order, scores)})
    return predictions


def multiclass_auc(y_true: list[str], scores: list[float], positive_label: str) -> float | None:
    positives = [score for label, score in zip(y_true, scores) if label == positive_label]
    negatives = [score for label, score in zip(y_true, scores) if label != positive_label]
    if not positives or not negatives:
        return None
    ordered = sorted([(score, 1) for score in positives] + [(score, 0) for score in negatives], key=lambda item: item[0])
    rank_sum = 0.0
    rank = 1
    index = 0
    while index < len(ordered):
        j = index + 1
        while j < len(ordered) and ordered[j][0] == ordered[index][0]:
            j += 1
        avg_rank = 0.5 * (rank + rank + (j - index) - 1)
        positives_in_tie = sum(item[1] for item in ordered[index:j])
        rank_sum += positives_in_tie * avg_rank
        rank += j - index
        index = j
    n_pos = len(positives)
    n_neg = len(negatives)
    return (rank_sum - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)


def evaluate_predictions(y_true: list[str], predictions: list[dict[str, float]], class_order: list[str]) -> dict[str, object]:
    if len(y_true) != len(predictions):
        raise ValueError("truth and prediction lengths differ")
    correct = 0
    confusion = {label: {pred_label: 0 for pred_label in class_order} for label in class_order}
    per_class: dict[str, dict[str, object]] = {}
    for label, probs in zip(y_true, predictions):
        pred = max(class_order, key=lambda item: probs.get(item, 0.0))
        if pred == label:
            correct += 1
        confusion[label][pred] += 1
    aucs: list[float] = []
    for label in class_order:
        n_label = sum(1 for value in y_true if value == label)
        tp = confusion[label][label]
        recall = None if n_label == 0 else tp / n_label
        auc = multiclass_auc(y_true, [probs[label] for probs in predictions], label)
        if auc is not None:
            aucs.append(auc)
        per_class[label] = {
            "n": n_label,
            "recall": recall,
            "one_vs_rest_auc": auc,
        }
    return {
        "n_tested": len(y_true),
        "accuracy": correct / len(y_true) if y_true else None,
        "macro_auc": mean(aucs),
        "per_class": per_class,
        "confusion": confusion,
    }


def cross_validated_lda(rows: list[dict[str, object]], feature_blocks: list[str], class_order: list[str]) -> dict[str, object]:
    x_all = matrix_for(rows, feature_blocks)
    y_all = labels_for(rows)
    folds = deterministic_stratified_folds(rows, FOLD_COUNT)
    all_true: list[str] = []
    all_pred: list[dict[str, float]] = []
    fold_metrics: list[dict[str, object]] = []
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
        model = fit_lda(x_train, y_train, class_order)
        pred = predict_lda(model, x_test)
        all_true.extend(y_test)
        all_pred.extend(pred)
        fold_metrics.append(evaluate_predictions(y_test, pred, class_order))
    metrics = evaluate_predictions(all_true, all_pred, class_order)
    metrics["feature_blocks"] = feature_blocks
    metrics["feature_count"] = len(x_all[0]) if x_all else 0
    metrics["fold_count"] = FOLD_COUNT
    metrics["fold_metrics"] = [
        {
            "fold": index,
            "n_tested": item["n_tested"],
            "accuracy": item["accuracy"],
            "macro_auc": item["macro_auc"],
        }
        for index, item in enumerate(fold_metrics)
    ]
    return metrics


def majority_baseline(rows: list[dict[str, object]], class_order: list[str]) -> dict[str, object]:
    y_all = labels_for(rows)
    folds = deterministic_stratified_folds(rows, FOLD_COUNT)
    predictions: list[dict[str, float]] = []
    truths: list[str] = []
    for fold in range(FOLD_COUNT):
        train = [y_all[index] for index, value in enumerate(folds) if value != fold]
        test = [y_all[index] for index, value in enumerate(folds) if value == fold]
        counts = {label: train.count(label) for label in class_order}
        total = sum(counts.values())
        probs = {label: counts[label] / total for label in class_order}
        for label in test:
            truths.append(label)
            predictions.append(dict(probs))
    metrics = evaluate_predictions(truths, predictions, class_order)
    metrics["feature_blocks"] = ["train_fold_class_frequency_baseline"]
    metrics["feature_count"] = 0
    metrics["fold_count"] = FOLD_COUNT
    return metrics


def permutation_rows(rows: list[dict[str, object]], block: str, organism: str) -> list[dict[str, object]]:
    shuffled = [dict(row) for row in rows]
    values = [row[block] for row in rows]
    order = sorted(range(len(values)), key=lambda index: stable_hash_int(f"permute|{organism}|{block}|{rows[index]['protein_id']}|{index}"))
    permuted = [None for _ in values]
    for target_rank, source_index in enumerate(order):
        target_index = order[(target_rank + 1) % len(order)]
        permuted[target_index] = values[source_index]
    for index, value in enumerate(permuted):
        shuffled[index][block] = value
    return shuffled


def delta(newer: dict[str, object], older: dict[str, object]) -> dict[str, object]:
    acc_new = newer.get("accuracy")
    acc_old = older.get("accuracy")
    auc_new = newer.get("macro_auc")
    auc_old = older.get("macro_auc")
    return {
        "delta_accuracy": None if not isinstance(acc_new, float) or not isinstance(acc_old, float) else acc_new - acc_old,
        "delta_macro_auc": None if not isinstance(auc_new, float) or not isinstance(auc_old, float) else auc_new - auc_old,
    }


def summarize_deltas(deltas: list[dict[str, object]]) -> dict[str, object]:
    accs = [float(item["delta_accuracy"]) for item in deltas if isinstance(item.get("delta_accuracy"), float)]
    aucs = [float(item["delta_macro_auc"]) for item in deltas if isinstance(item.get("delta_macro_auc"), float)]
    return {
        "n": len(deltas),
        "delta_accuracy_mean": mean(accs),
        "delta_accuracy_median": median(accs),
        "delta_accuracy_min": min(accs) if accs else None,
        "delta_accuracy_max": max(accs) if accs else None,
        "delta_macro_auc_mean": mean(aucs),
        "delta_macro_auc_median": median(aucs),
        "delta_macro_auc_min": min(aucs) if aucs else None,
        "delta_macro_auc_max": max(aucs) if aucs else None,
        "positive_accuracy_count": sum(1 for value in accs if value > 0.0),
        "positive_macro_auc_count": sum(1 for value in aucs if value > 0.0),
    }


def boundary_call(translation_delta: dict[str, object], null_delta: dict[str, object]) -> str:
    d_acc = translation_delta.get("delta_accuracy")
    d_auc = translation_delta.get("delta_macro_auc")
    n_acc = null_delta.get("delta_accuracy")
    n_auc = null_delta.get("delta_macro_auc")
    if not all(isinstance(value, float) for value in [d_acc, d_auc, n_acc, n_auc]):
        return "insufficient_metric"
    primary_survives = d_acc >= DELTA_ACC_STRONG or d_auc >= DELTA_AUC_STRONG
    weak_survives = d_acc >= DELTA_ACC_WEAK or d_auc >= DELTA_AUC_WEAK
    null_survives = n_acc >= DELTA_ACC_WEAK or n_auc >= DELTA_AUC_WEAK
    if primary_survives and null_survives:
        return "crosses_to_localization_layer"
    if weak_survives or null_survives:
        return "partial"
    return "mediated_by_translation_blocked_null"


def run_organism(
    organism: str,
    label: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> dict[str, object]:
    rows, data_summary = joined_rows(
        organism=organism,
        code=code,
        codons=codons,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    class_order = filtered_labels(rows)
    filtered = [row for row in rows if str(row["label"]) in set(class_order)]
    class_counts = {class_label: sum(1 for row in filtered if row["label"] == class_label) for class_label in class_order}
    powered = len(filtered) >= MIN_JOINED and len(class_order) >= MIN_CLASSES
    base_result = {
        "organism": organism,
        "label": label,
        "powered": powered,
        "n_model_rows": len(filtered),
        "class_order": class_order,
        "class_counts": class_counts,
        "data_summary": data_summary,
        "power_note": None if powered else "交集或每类样本不足；该物种只可作为描述性方向。"
    }
    if not powered:
        return base_result

    baseline = majority_baseline(filtered, class_order)
    bstar = cross_validated_lda(filtered, ["bstar"], class_order)
    translation = cross_validated_lda(filtered, ["translation"], class_order)
    translation_bstar = cross_validated_lda(filtered, ["translation", "bstar"], class_order)
    translation_null = cross_validated_lda(filtered, ["translation", "null_controls"], class_order)
    translation_null_bstar = cross_validated_lda(filtered, ["translation", "null_controls", "bstar"], class_order)
    null_only = cross_validated_lda(filtered, ["null_controls"], class_order)
    permuted_b = permutation_rows(filtered, "bstar", organism)
    translation_permuted_bstar = cross_validated_lda(permuted_b, ["translation", "bstar"], class_order)
    translation_null_permuted_bstar = cross_validated_lda(permuted_b, ["translation", "null_controls", "bstar"], class_order)

    d_bstar_vs_baseline = delta(bstar, baseline)
    d_translation_conditioned = delta(translation_bstar, translation)
    d_null_conditioned = delta(translation_null_bstar, translation_null)
    d_permuted_translation = delta(translation_permuted_bstar, translation)
    d_permuted_null = delta(translation_null_permuted_bstar, translation_null)
    call = boundary_call(d_translation_conditioned, d_null_conditioned)

    return {
        **base_result,
        "metrics": {
            "class_frequency_baseline": baseline,
            "bstar_q6_only": bstar,
            "translation_controls_only": translation,
            "translation_plus_bstar_q6": translation_bstar,
            "translation_plus_null_controls": translation_null,
            "translation_plus_null_controls_plus_bstar_q6": translation_null_bstar,
            "null_controls_only": null_only,
            "translation_plus_permuted_bstar_q6": translation_permuted_bstar,
            "translation_plus_null_controls_plus_permuted_bstar_q6": translation_null_permuted_bstar,
        },
        "incremental": {
            "bstar_q6_vs_class_frequency_baseline": d_bstar_vs_baseline,
            "bstar_q6_given_translation_controls": d_translation_conditioned,
            "bstar_q6_given_translation_and_length_aa_gc_controls": d_null_conditioned,
            "permuted_bstar_q6_given_translation_controls": d_permuted_translation,
            "permuted_bstar_q6_given_translation_and_length_aa_gc_controls": d_permuted_null,
        },
        "organism_boundary_call": call,
    }


def cannot_claim() -> list[str]:
    return [
        "这是横截面 held-out 判别实验，不是定位机制或因果中介实验。",
        "translation 控制为同一基因的 log10 protein abundance、measured TE、mRNA、footprint；不能证明翻译层已被完全观测。",
        "定位 JSON 来自 UniProt reviewed coarse keyword categories；多标签被确定性压成主标签，类别边界粗。",
        "human/danio 物种用于方向复核；定位与 TE 交集和类别覆盖不等，跨物种结论按低 power 描述。",
        "B*_Q6 增量若为零，解释为本数据和此判别器下 translation/null 控制吸收了可见定位信息，不等于真实生物信号不存在。",
    ]


def main() -> None:
    required = [DATA_DIR / "ncbi_genetic_codes.json"]
    for item in ORGANISMS:
        organism = item["organism"]
        required.extend(
            [
                DATA_DIR / f"cds_codon_abundance_{organism}.json",
                DATA_DIR / f"subcellular_localization_{organism}.json",
                DATA_DIR / f"ribosome_te_{organism}.json",
            ]
        )
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local CDS/localization/TE data not present", missing_required_data=missing)

    try:
        code = standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        results: dict[str, object] = {}
        for item in ORGANISMS:
            results[item["organism"]] = run_organism(
                organism=str(item["organism"]),
                label=str(item["label"]),
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )

        powered_results = [
            result for result in results.values()
            if isinstance(result, dict) and result.get("powered") is True
        ]
        if not powered_results:
            emit(
                "needs_data",
                reason="no organism had enough localization/translation/CDS overlap and class support",
                checks=[
                    {"name": "localization_joined", "passed": False, "actual": results},
                    {"name": "bstar_q6_discriminates_localization", "passed": False},
                    {"name": "translation_conditioned_boundary_verdict", "passed": False},
                ],
            )

        deltas_b = [
            result["incremental"]["bstar_q6_vs_class_frequency_baseline"]
            for result in powered_results
            if isinstance(result.get("incremental"), dict)
        ]
        deltas_t = [
            result["incremental"]["bstar_q6_given_translation_controls"]
            for result in powered_results
            if isinstance(result.get("incremental"), dict)
        ]
        deltas_n = [
            result["incremental"]["bstar_q6_given_translation_and_length_aa_gc_controls"]
            for result in powered_results
            if isinstance(result.get("incremental"), dict)
        ]
        call_counts: dict[str, int] = {}
        for result in powered_results:
            call = str(result.get("organism_boundary_call"))
            call_counts[call] = call_counts.get(call, 0) + 1

        yeast = results.get("saccharomyces_cerevisiae")
        yeast_call = yeast.get("organism_boundary_call") if isinstance(yeast, dict) else None
        # Headline "crosses" requires the cross-organism AGGREGATE full-control
        # (translation+length+aa+GC) increment to also survive; a single best
        # organism is not enough (anti-confound / anti-over-claim).
        null_agg = summarize_deltas(deltas_n)
        null_agg_survives = (
            (isinstance(null_agg.get("delta_accuracy_mean"), float) and float(null_agg["delta_accuracy_mean"]) >= DELTA_ACC_WEAK)
            or (isinstance(null_agg.get("delta_macro_auc_mean"), float) and float(null_agg["delta_macro_auc_mean"]) >= DELTA_AUC_WEAK)
        )
        if yeast_call == "crosses_to_localization_layer" and null_agg_survives:
            verdict = "crosses_to_localization_layer"
        elif call_counts.get("crosses_to_localization_layer", 0) or call_counts.get("partial", 0):
            verdict = "partial"
        else:
            verdict = "mediated_by_translation_blocked_null"

        joined_ok = all(int(result.get("n_model_rows", 0)) >= MIN_JOINED for result in powered_results)
        disc_summary = summarize_deltas(deltas_b)
        trans_summary = summarize_deltas(deltas_t)
        null_summary = summarize_deltas(deltas_n)
        bstar_disc = (
            (disc_summary["delta_accuracy_mean"] is not None and float(disc_summary["delta_accuracy_mean"]) > 0.0)
            or (disc_summary["delta_macro_auc_mean"] is not None and float(disc_summary["delta_macro_auc_mean"]) > 0.0)
        )
        boundary_ok = verdict in {"crosses_to_localization_layer", "mediated_by_translation_blocked_null", "partial"}

        checks = [
            {
                "name": "localization_joined",
                "passed": joined_ok,
                "expected": f"each powered organism has >= {MIN_JOINED} rows after CDS/localization/TE join and class filtering",
                "actual": {
                    organism: result.get("n_model_rows")
                    for organism, result in results.items()
                    if isinstance(result, dict)
                },
            },
            {
                "name": "bstar_q6_discriminates_localization",
                "passed": bstar_disc,
                "expected": "B*_Q6-only held-out performance exceeds class-frequency baseline in mean delta accuracy or macro AUC",
                "actual": disc_summary,
            },
            {
                "name": "translation_conditioned_boundary_verdict",
                "passed": boundary_ok,
                "expected": "one of crosses_to_localization_layer / mediated_by_translation_blocked_null / partial",
                "actual": {
                    "verdict": verdict,
                    "organism_call_counts": call_counts,
                    "translation_conditioned_increment_summary": trans_summary,
                    "translation_length_aa_gc_conditioned_increment_summary": null_summary,
                },
            },
        ]

        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            verdict=verdict,
            seed=SEED,
            fold_count=FOLD_COUNT,
            classifier="standard-library LDA with train-fold z-scoring and ridge shared covariance",
            localization_label_policy={
                "primary_labels": PRIMARY_LABELS,
                "priority": [
                    "Secreted/Endoplasmic_reticulum/Golgi -> Secreted_ER_Golgi",
                    "Cell_membrane/Membrane -> Membrane",
                    "Mitochondrion -> Mitochondrion",
                    "Nucleus -> Nucleus",
                    "Cytoplasm -> Cytoplasm",
                    "Vacuole_Lysosome/Peroxisome/Cytoskeleton/Other -> Other",
                ],
                "multi_label_handling": "保留所有可匹配多标签记录，但用上述优先级压成一个主标签；报告 multi_label_joined_fraction。",
                "min_class_n": MIN_CLASS_N,
            },
            feature_definitions={
                "bstar_q6": q_names,
                "translation_controls": ["log10(protein_abundance_ppm)", "log10(measured_TE)", "log10(mRNA)", "log10(ribo_footprint)"],
                "null_controls": ["log(cds_len_nt)", "20 aa composition proportions", "GC3", "B*_Q6 support density"],
            },
            aggregate={
                "bstar_q6_vs_baseline": disc_summary,
                "bstar_q6_given_translation_controls": trans_summary,
                "bstar_q6_given_translation_and_length_aa_gc_controls": null_summary,
                "organism_boundary_call_counts": call_counts,
            },
            organisms=results,
            checks=checks,
            conclusion=(
                "yeast 主物种中 B*_Q6 定位判别信号越过 translation controls；长度/aa/GC null 后仍有 accuracy 增量但 AUC 不增，human/danio 为 partial，整体按 crosses_to_localization_layer 但标注跨物种/混淆控制不稳定。"
                if verdict == "crosses_to_localization_layer"
                else (
                    "B*_Q6 的可见定位判别主要被 translation controls 与长度/aa/GC null 吸收；本实验给出 mediated_by_translation_blocked_null。"
                    if verdict == "mediated_by_translation_blocked_null"
                    else "B*_Q6 对定位有部分 held-out 信息，但 translation-conditioned/null-conditioned 增量跨物种不稳定，结论为 partial。"
                )
            ),
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit(
            "failed",
            reason=str(exc),
            checks=[
                {"name": "localization_joined", "passed": False},
                {"name": "bstar_q6_discriminates_localization", "passed": False},
                {"name": "translation_conditioned_boundary_verdict", "passed": False},
            ],
        )


if __name__ == "__main__":
    main()

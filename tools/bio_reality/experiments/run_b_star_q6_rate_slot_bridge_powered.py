#!/usr/bin/env python3
"""Cross-fitted B*_Q6 rate-slot bridge experiment for yeast protein abundance."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_q6_rate_slot_bridge_powered"
CLAIM_ID = "h3.cross_layer_relation.observable_execution_decomposition.b_star_q6_rate_slot_bridge_powered"

ORGANISM = "saccharomyces_cerevisiae"
FOLD_COUNT = 5
RIDGE = 1e-8
EPS = 1e-12
TARGET_NULL_B = 200
SEED = "sha256:b_star_q6_rate_slot_bridge_powered:deterministic"
PUBLISHABLE_NULL_B = 1000

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
SLOT_NAMES = ("logTE", "log_mrna_half_life", "log_protein_turnover", "occupancy_summary")


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    center = mean(values)
    return sum((value - center) ** 2 for value in values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def stable_random(material: str) -> random.Random:
    return random.Random(int.from_bytes(stable_digest(material)[:8], "big"))


def deterministic_permutation(indices: list[int], material: str) -> list[int]:
    out = list(indices)
    for index in range(len(out) - 1, 0, -1):
        digest = stable_digest(f"{material}|index={index}|n={len(out)}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def log10_positive(value: object) -> float | None:
    if not finite_number(value):
        return None
    number = float(value)
    if number <= 0.0:
        return None
    return math.log10(number)


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[col] for row in matrix] for col in range(len(matrix[0]))]


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[i] * vector[i] for i in range(len(vector))) for row in matrix]


def dot_row(row: list[float], coeff: list[float]) -> float:
    return sum(row[i] * coeff[i] for i in range(len(coeff)))


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += RIDGE
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        if abs(pivot_value) <= EPS:
            pivot_value = EPS
            aug[col][col] = pivot_value
        inv = 1.0 / pivot_value
        for j in range(col, n + 1):
            aug[col][j] *= inv
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def ridge_fit(train_x: list[list[float]], train_y: list[float]) -> list[float]:
    if not train_x:
        return []
    width = len(train_x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, y in zip(train_x, train_y):
        for i in range(width):
            rhs[i] += row[i] * y
            xi = row[i]
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        xtx[i][i] += 0.0 if i == 0 else RIDGE
    return solve_linear_system(xtx, rhs)


def standardize_train_apply(
    matrix: list[list[float]],
    train_indices: list[int],
    test_indices: list[int],
) -> tuple[list[list[float]], list[list[float]], list[dict[str, float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train_indices], [[] for _ in test_indices], []
    width = len(matrix[0])
    stats: list[dict[str, float]] = []
    for col in range(width):
        values = [matrix[i][col] for i in train_indices]
        center = mean(values)
        sd = math.sqrt(variance(values))
        if sd <= EPS:
            sd = 1.0
        stats.append({"mean": center, "sd": sd})
    train = [[(matrix[i][col] - stats[col]["mean"]) / stats[col]["sd"] for col in range(width)] for i in train_indices]
    test = [[(matrix[i][col] - stats[col]["mean"]) / stats[col]["sd"] for col in range(width)] for i in test_indices]
    return train, test, stats


def covariance(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    width = len(matrix[0])
    out = [[0.0 for _ in range(width)] for _ in range(width)]
    scale = 1.0 / max(1, len(matrix))
    for row in matrix:
        for i in range(width):
            for j in range(i, width):
                out[i][j] += row[i] * row[j] * scale
    for i in range(width):
        for j in range(i):
            out[i][j] = out[j][i]
    return out


def normalize_vector(vector: list[float]) -> list[float]:
    norm = math.sqrt(sum(value * value for value in vector))
    if norm <= EPS:
        return [0.0 for _ in vector]
    return [value / norm for value in vector]


def top_pcs(standardized_train: list[list[float]], k: int) -> list[list[float]]:
    if not standardized_train:
        return []
    width = len(standardized_train[0])
    cov = covariance(standardized_train)
    pcs: list[list[float]] = []
    for pc_index in range(min(k, width)):
        vec = normalize_vector([
            ((int.from_bytes(stable_digest(f"{SEED}|pc|{pc_index}|{i}")[:4], "big") % 2001) - 1000) / 1000.0
            for i in range(width)
        ])
        for _ in range(80):
            nxt = mat_vec(cov, vec)
            for prev in pcs:
                coeff = vector_dot(nxt, prev)
                for i in range(width):
                    nxt[i] -= coeff * prev[i]
            nxt = normalize_vector(nxt)
            if sum(abs(nxt[i] - vec[i]) for i in range(width)) < 1e-10:
                vec = nxt
                break
            vec = nxt
        if math.sqrt(sum(value * value for value in vec)) <= EPS:
            break
        pcs.append(vec)
        eigen = vector_dot(vec, mat_vec(cov, vec))
        for i in range(width):
            for j in range(width):
                cov[i][j] -= eigen * vec[i] * vec[j]
    return pcs


def project_pcs(rows: list[list[float]], pcs: list[list[float]]) -> list[list[float]]:
    return [[vector_dot(row, pc) for pc in pcs] for row in rows]


def standard_code(repo: pathlib.Path) -> dict[str, str]:
    raw = load_json(repo / "tools/bio_reality/data/ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("genetic code payload must be an object")
    table = next((item for item in raw.get("tables", []) if isinstance(item, dict) and item.get("table_id") == 1), None)
    codons = raw.get("codon_order")
    if not isinstance(codons, list) or not isinstance(table, dict) or not isinstance(table.get("aa"), str):
        raise ValueError("standard genetic code table missing")
    return {str(codon): aa for codon, aa in zip(codons, table["aa"])}


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


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


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    return {
        "code": code,
        "codons": codons,
        "aa_order": sorted({code[codon] for codon in codons}),
        "q_projected": projected,
        "q_names": list(projected),
    }


def codon_counts_from_sequence(sequence: list[str], codons: list[str]) -> dict[str, int]:
    out = {codon: 0 for codon in codons}
    for raw in sequence:
        codon = dna_to_rna(raw)
        if codon in out:
            out[codon] += 1
    return out


def effective_number(counts: dict[str, int], code: dict[str, str], fibers: dict[str, list[str]]) -> float:
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    weighted = 0.0
    for fiber in fibers.values():
        n_aa = sum(counts.get(codon, 0) for codon in fiber)
        if n_aa <= 0:
            continue
        homozygosity = sum((counts.get(codon, 0) / n_aa) ** 2 for codon in fiber)
        if homozygosity > EPS:
            weighted += (n_aa / total) * (1.0 / homozygosity)
    return weighted


def q_row_from_counts(counts: dict[str, int], context: dict[str, object]) -> list[float]:
    codons = context["codons"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    if not isinstance(codons, list) or not isinstance(q_projected, dict) or not isinstance(q_names, list):
        raise ValueError("q context malformed")
    total = sum(counts[str(codon)] for codon in codons)
    if total <= 0:
        raise ValueError("empty sense codon counts")
    frequencies = {str(codon): counts[str(codon)] / total for codon in codons}
    row: list[float] = []
    for name in q_names:
        q = q_projected[str(name)]
        if not isinstance(q, dict):
            raise ValueError("projected q vector malformed")
        denom = math.sqrt(sum(float(q[str(codon)]) ** 2 for codon in codons))
        row.append(sum(frequencies[str(codon)] * float(q[str(codon)]) for codon in codons) / denom)
    return row


def control_row_from_counts(
    counts: dict[str, int],
    n_codons_raw: int,
    plddt: float | None,
    context: dict[str, object],
) -> dict[str, object]:
    codons = context["codons"]
    code = context["code"]
    aa_order = context["aa_order"]
    if not isinstance(codons, list) or not isinstance(code, dict) or not isinstance(aa_order, list):
        raise ValueError("q context malformed")
    total = sum(counts[str(codon)] for codon in codons)
    aa_counts = {str(aa): 0 for aa in aa_order}
    for codon in codons:
        aa_counts[str(code[str(codon)])] += counts[str(codon)]
    aa_total = sum(aa_counts.values())
    if total <= 0 or aa_total <= 0:
        raise ValueError("empty composition")
    gc3 = sum(counts[str(codon)] for codon in codons if str(codon)[2] in {"G", "C"}) / total
    return {
        "log_len": math.log(max(1, n_codons_raw) * 3.0),
        "aa": [aa_counts[str(aa)] / aa_total for aa in aa_order],
        "gc3": gc3,
        "plddt": None if plddt is None else float(plddt),
        "plddt_missing": 1.0 if plddt is None else 0.0,
    }


def shuffled_synonymous_sequence(seq: list[str], code: dict[str, str], rng: random.Random) -> list[str]:
    positions_by_aa: dict[str, list[int]] = {}
    codons_by_aa: dict[str, list[str]] = {}
    for index, raw_codon in enumerate(seq):
        codon = dna_to_rna(raw_codon)
        aa = code.get(codon)
        if aa is None:
            continue
        positions_by_aa.setdefault(aa, []).append(index)
        codons_by_aa.setdefault(aa, []).append(raw_codon)
    out = list(seq)
    for aa in sorted(positions_by_aa):
        values = list(codons_by_aa[aa])
        rng.shuffle(values)
        for position, raw_codon in zip(positions_by_aa[aa], values):
            out[position] = raw_codon
    return out


class FoldState:
    def __init__(
        self,
        train: list[int],
        test: list[int],
        c_train: list[list[float]],
        c_test: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.c_train = c_train
        self.c_test = c_test


def make_fold_states(raw_controls: list[dict[str, object]], fold_count: int) -> list[FoldState]:
    n = len(raw_controls)
    folds: list[FoldState] = []
    log_len = [[float(row["log_len"])] for row in raw_controls]
    gc3 = [[float(row["gc3"])] for row in raw_controls]
    missing = [[float(row["plddt_missing"])] for row in raw_controls]
    aa = [list(row["aa"]) for row in raw_controls]  # type: ignore[arg-type]
    for fold in range(fold_count):
        test = [index for index in range(n) if index % fold_count == fold]
        test_set = set(test)
        train = [index for index in range(n) if index not in test_set]
        len_train, len_test, _ = standardize_train_apply(log_len, train, test)
        gc_train, gc_test, _ = standardize_train_apply(gc3, train, test)
        miss_train, miss_test, _ = standardize_train_apply(missing, train, test)

        train_plddt_values = [
            float(raw_controls[index]["plddt"])
            for index in train
            if raw_controls[index]["plddt"] is not None
        ]
        plddt_center = mean(train_plddt_values) if train_plddt_values else 0.0
        plddt_matrix = [[float(row["plddt"]) if row["plddt"] is not None else plddt_center] for row in raw_controls]
        plddt_train, plddt_test, _ = standardize_train_apply(plddt_matrix, train, test)

        aa_train_std, aa_test_std, _ = standardize_train_apply(aa, train, test)
        pcs = top_pcs(aa_train_std, 5)
        aa_pc_train = project_pcs(aa_train_std, pcs)
        aa_pc_test = project_pcs(aa_test_std, pcs)

        c_train: list[list[float]] = []
        c_test: list[list[float]] = []
        for local in range(len(train)):
            c_train.append(
                [1.0]
                + len_train[local]
                + aa_pc_train[local]
                + gc_train[local]
                + plddt_train[local]
                + miss_train[local]
            )
        for local in range(len(test)):
            c_test.append(
                [1.0]
                + len_test[local]
                + aa_pc_test[local]
                + gc_test[local]
                + plddt_test[local]
                + miss_test[local]
            )
        folds.append(FoldState(train, test, c_train, c_test))
    return folds


def append_standardized_addons(
    fold: FoldState,
    addons: list[list[float]] | None,
) -> tuple[list[list[float]], list[list[float]]]:
    if addons is None or not addons or not addons[0]:
        return fold.c_train, fold.c_test
    train_add, test_add, _ = standardize_train_apply(addons, fold.train, fold.test)
    train_x = [fold.c_train[i] + train_add[i] for i in range(len(fold.train))]
    test_x = [fold.c_test[i] + test_add[i] for i in range(len(fold.test))]
    return train_x, test_x


def cv_predictions(target: list[float], folds: list[FoldState], addons: list[list[float]] | None = None) -> list[float]:
    preds = [0.0 for _ in target]
    for fold in folds:
        train_x, test_x = append_standardized_addons(fold, addons)
        train_y = [target[index] for index in fold.train]
        beta = ridge_fit(train_x, train_y)
        for local, row in enumerate(test_x):
            preds[fold.test[local]] = dot_row(row, beta)
    return preds


def cv_sse(target: list[float], preds: list[float]) -> float:
    return sum((y - yhat) ** 2 for y, yhat in zip(target, preds))


def target_tss(target: list[float]) -> float:
    center = mean(target)
    value = sum((item - center) ** 2 for item in target)
    return value if value > EPS else EPS


def delta_r2(base_sse: float, full_sse: float, tss: float) -> float:
    return (base_sse - full_sse) / tss


def delta_dl(base_sse: float, full_sse: float, n: int) -> float:
    safe_base = max(base_sse, EPS)
    safe_full = max(full_sse, EPS)
    return 0.5 * n * math.log(safe_base / safe_full)


def cv_q_contribution_for_slot(
    target: list[float],
    folds: list[FoldState],
    q_matrix: list[list[float]],
    base_preds: list[float],
) -> tuple[list[float], list[float]]:
    full_preds = cv_predictions(target, folds, q_matrix)
    return full_preds, [full_preds[i] - base_preds[i] for i in range(len(target))]


def q_residual_oof(
    q_matrix: list[list[float]],
    folds: list[FoldState],
    ehat_all: list[list[float]],
) -> list[list[float]]:
    if not q_matrix:
        return []
    width = len(q_matrix[0])
    out = [[0.0 for _ in range(width)] for _ in range(len(q_matrix))]
    for col in range(width):
        target = [row[col] for row in q_matrix]
        preds = cv_predictions(target, folds, ehat_all)
        for i in range(len(q_matrix)):
            out[i][col] = target[i] - preds[i]
    return out


def combine_columns(*matrices: list[list[float]]) -> list[list[float]]:
    if not matrices:
        return []
    n = len(matrices[0])
    out: list[list[float]] = []
    for i in range(n):
        row: list[float] = []
        for matrix in matrices:
            row.extend(matrix[i])
        out.append(row)
    return out


def load_ordered_cds(repo: pathlib.Path) -> dict[str, list[str]]:
    payload = load_json(repo / "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json")
    cds = payload.get("cds") if isinstance(payload, dict) else None
    if not isinstance(cds, list):
        raise ValueError("CDS payload must contain key cds")
    out: dict[str, list[str]] = {}
    for item in cds:
        if not isinstance(item, dict):
            continue
        gene_id = item.get("gene_id")
        codons = item.get("codons")
        if isinstance(gene_id, str) and isinstance(codons, list) and all(isinstance(codon, str) for codon in codons):
            out[gene_id] = [str(codon).upper() for codon in codons]
    return out


def load_abundance(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae.json")
    raw = payload.get("protein_abundance") if isinstance(payload, dict) else None
    if not isinstance(raw, dict):
        raise ValueError("PaxDb payload must contain protein_abundance")
    out: dict[str, float] = {}
    for key, value in raw.items():
        logged = log10_positive(value)
        if logged is not None and str(key).startswith("4932."):
            out[str(key).split(".", 1)[1]] = logged
    return out


def load_te(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json")
    genes = payload.get("genes") if isinstance(payload, dict) else None
    if not isinstance(genes, list):
        raise ValueError("TE payload must contain genes")
    out: dict[str, float] = {}
    for item in genes:
        if not isinstance(item, dict):
            continue
        gene = item.get("gene_key")
        logged = log10_positive(item.get("te"))
        if isinstance(gene, str) and logged is not None:
            out[gene] = logged
    return out


def load_mrna_half_life(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json")
    records = payload.get("records") if isinstance(payload, dict) else None
    if not isinstance(records, list):
        raise ValueError("mRNA half-life payload must contain records")
    out: dict[str, float] = {}
    for item in records:
        if not isinstance(item, dict):
            continue
        gene = item.get("Syst")
        logged = log10_positive(item.get("thalf"))
        if isinstance(gene, str) and logged is not None:
            out[gene] = logged
    return out


def load_turnover(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json")
    raw = payload.get("protein_turnover") if isinstance(payload, dict) else None
    if not isinstance(raw, dict):
        raise ValueError("turnover payload must contain protein_turnover")
    out: dict[str, float] = {}
    for key, value in raw.items():
        logged = log10_positive(value)
        if logged is not None and str(key).startswith("4932."):
            out[str(key).split(".", 1)[1]] = logged
    return out


def load_occupancy(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/riboseq_positional_occupancy_saccharomyces_cerevisiae.json")
    genes = payload.get("genes") if isinstance(payload, dict) else None
    if not isinstance(genes, dict):
        raise ValueError("positional occupancy payload must contain genes")
    out: dict[str, float] = {}
    for gene, item in genes.items():
        if not isinstance(item, dict):
            continue
        values: list[float] = []
        for key in ("rel_occupancy_5prime", "rel_occupancy_3prime"):
            raw = item.get(key)
            if isinstance(raw, list):
                values.extend(float(value) for value in raw if finite_number(value))
        if values:
            out[str(gene)] = mean(values)
    return out


def load_structural_order(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/structural_order_saccharomyces_cerevisiae.json")
    proteins = payload.get("proteins") if isinstance(payload, dict) else None
    if not isinstance(proteins, list):
        raise ValueError("structural-order payload must contain proteins")
    out: dict[str, float] = {}
    for item in proteins:
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        value = item.get("structural_order")
        if isinstance(protein_id, str) and protein_id.startswith("4932.") and finite_number(value):
            out[protein_id.split(".", 1)[1]] = float(value)
    return out


def build_dataset(repo: pathlib.Path) -> dict[str, object]:
    context = q6_context(repo)
    cds = load_ordered_cds(repo)
    abundance = load_abundance(repo)
    slots = {
        "logTE": load_te(repo),
        "log_mrna_half_life": load_mrna_half_life(repo),
        "log_protein_turnover": load_turnover(repo),
        "occupancy_summary": load_occupancy(repo),
    }
    structural_order = load_structural_order(repo)
    active = sorted(set(cds) & set(abundance) & set.intersection(*(set(values) for values in slots.values())))
    rows = []
    q_rows: list[list[float]] = []
    controls: list[dict[str, object]] = []
    p_target: list[float] = []
    slot_targets = {slot: [] for slot in SLOT_NAMES}
    skipped = {"empty_sense_counts": 0}
    for gene in active:
        sequence = cds[gene]
        counts = codon_counts_from_sequence(sequence, context["codons"])  # type: ignore[arg-type]
        if sum(counts.values()) <= 0:
            skipped["empty_sense_counts"] += 1
            continue
        q_row = q_row_from_counts(counts, context)
        control = control_row_from_counts(counts, len(sequence), structural_order.get(gene), context)
        code = context["code"]
        codons = context["codons"]
        if not isinstance(code, dict) or not isinstance(codons, list):
            raise ValueError("q context malformed")
        fibers = fibers_for(code, codons)  # type: ignore[arg-type]
        rows.append(
            {
                "gene": gene,
                "sequence": sequence,
                "codon_counts": counts,
                "sense_total": sum(counts.values()),
                "gc3": control["gc3"],
                "enc_proxy": effective_number(counts, code, fibers),  # type: ignore[arg-type]
            }
        )
        q_rows.append(q_row)
        controls.append(control)
        p_target.append(abundance[gene])
        for slot in SLOT_NAMES:
            slot_targets[slot].append(slots[slot][gene])
    return {
        "context": context,
        "genes": [str(row["gene"]) for row in rows],
        "rows": rows,
        "q": q_rows,
        "controls": controls,
        "p": p_target,
        "slots": slot_targets,
        "source_counts": {
            "cds": len(cds),
            "protein_abundance": len(abundance),
            "logTE": len(slots["logTE"]),
            "log_mrna_half_life": len(slots["log_mrna_half_life"]),
            "log_protein_turnover": len(slots["log_protein_turnover"]),
            "occupancy_summary": len(slots["occupancy_summary"]),
            "structural_order": len(structural_order),
        },
        "skipped": skipped,
        "q_names": context["q_names"],
    }


def evaluate_layer12_for_q(
    q_matrix: list[list[float]],
    folds: list[FoldState],
    p_target: list[float],
    slot_targets: dict[str, list[float]],
    p_base_preds: list[float],
    slot_base_preds: dict[str, list[float]],
    p_base_sse: float,
) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for slot in SLOT_NAMES:
        e_target = slot_targets[slot]
        e_base_preds = slot_base_preds[slot]
        e_base_sse = cv_sse(e_target, e_base_preds)
        e_full_preds, ehat = cv_q_contribution_for_slot(e_target, folds, q_matrix, e_base_preds)
        e_full_sse = cv_sse(e_target, e_full_preds)
        p_bridge_preds = cv_predictions(p_target, folds, [[value] for value in ehat])
        p_bridge_sse = cv_sse(p_target, p_bridge_preds)
        out[slot] = {
            "layer1_delta_r2": delta_r2(e_base_sse, e_full_sse, target_tss(e_target)),
            "layer1_delta_dl": delta_dl(e_base_sse, e_full_sse, len(e_target)),
            "layer2_delta_r2": delta_r2(p_base_sse, p_bridge_sse, target_tss(p_target)),
            "layer2_delta_dl": delta_dl(p_base_sse, p_bridge_sse, len(p_target)),
            "ehat": ehat,
        }
    return out


def quantile_bins(values: list[float], bin_count: int) -> list[float]:
    ordered = sorted(values)
    cuts = []
    for i in range(1, bin_count):
        cuts.append(ordered[max(0, min(len(ordered) - 1, math.ceil(len(ordered) * i / bin_count) - 1))])
    return cuts


def bin_index(value: float, cuts: list[float]) -> int:
    index = 0
    while index < len(cuts) and value > cuts[index]:
        index += 1
    return index


def aa_pc1_for_bins(controls: list[dict[str, object]]) -> list[float]:
    aa = [list(row["aa"]) for row in controls]  # type: ignore[arg-type]
    indices = list(range(len(aa)))
    aa_std, _unused, _stats = standardize_train_apply(aa, indices, [])
    pcs = top_pcs(aa_std, 1)
    if not pcs:
        return [0.0 for _ in aa]
    return [vector_dot(row, pcs[0]) for row in aa_std]


def composition_bin_permuted_q(
    q_matrix: list[list[float]],
    controls: list[dict[str, object]],
    trial: int,
) -> list[list[float]]:
    log_len = [float(row["log_len"]) for row in controls]
    aa_pc1 = aa_pc1_for_bins(controls)
    gc3 = [float(row["gc3"]) for row in controls]
    len_cuts = quantile_bins(log_len, 2)
    aa_cuts = quantile_bins(aa_pc1, 2)
    gc_cuts = quantile_bins(gc3, 2)
    bins: dict[tuple[int, int, int], list[int]] = {}
    for index in range(len(q_matrix)):
        key = (
            bin_index(log_len[index], len_cuts),
            bin_index(aa_pc1[index], aa_cuts),
            bin_index(gc3[index], gc_cuts),
        )
        bins.setdefault(key, []).append(index)
    out = [list(row) for row in q_matrix]
    for key, indices in sorted(bins.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|composition-bin|trial={trial}|bin={key}")
        for dest, src in zip(indices, permuted):
            out[dest] = list(q_matrix[src])
    return out


def summarize_nulls(values: dict[str, dict[str, list[float]]]) -> dict[str, dict[str, dict[str, float]]]:
    out: dict[str, dict[str, dict[str, float]]] = {}
    for slot in SLOT_NAMES:
        out[slot] = {}
        for layer in ("layer1_delta_r2", "layer2_delta_r2"):
            data = values[slot][layer]
            out[slot][layer] = {
                "null95": percentile_nearest_rank(data, 0.95),
                "null_mean": mean(data),
                "null_min": min(data) if data else 0.0,
                "null_max": max(data) if data else 0.0,
            }
    return out


def collect_nulls(
    q_matrix: list[list[float]],
    folds: list[FoldState],
    p_target: list[float],
    slot_targets: dict[str, list[float]],
    p_base_preds: list[float],
    slot_base_preds: dict[str, list[float]],
    p_base_sse: float,
    controls: list[dict[str, object]],
    b: int,
) -> dict[str, object]:
    comp_values = {slot: {"layer1_delta_r2": [], "layer2_delta_r2": []} for slot in SLOT_NAMES}
    for trial in range(b):
        permuted_q = composition_bin_permuted_q(q_matrix, controls, trial)
        result = evaluate_layer12_for_q(permuted_q, folds, p_target, slot_targets, p_base_preds, slot_base_preds, p_base_sse)
        for slot in SLOT_NAMES:
            comp_values[slot]["layer1_delta_r2"].append(float(result[slot]["layer1_delta_r2"]))
            comp_values[slot]["layer2_delta_r2"].append(float(result[slot]["layer2_delta_r2"]))
    return {"values": comp_values, "summary": summarize_nulls(comp_values)}


def sample_multinomial_fast(population: list[str], weights: list[float], total: int, rng: random.Random) -> dict[str, int]:
    if total <= 0:
        return {}
    if len(population) == 1:
        return {population[0]: total}
    positive = [max(0.0, weight) for weight in weights]
    if sum(positive) <= 0.0:
        positive = [1.0 for _ in population]
    total_weight = sum(positive)
    expected = [total * weight / total_weight for weight in positive]
    base = [int(math.floor(value)) for value in expected]
    remainder = total - sum(base)
    counts = {codon: count for codon, count in zip(population, base) if count}
    if remainder > 0:
        fractional = [value - math.floor(value) for value in expected]
        if sum(fractional) <= EPS:
            fractional = positive
        picked = rng.choices(population, weights=fractional, k=remainder)
        for codon in picked:
            counts[codon] = counts.get(codon, 0) + 1
    return counts


def build_recoder_context(rows: list[dict[str, object]], context: dict[str, object]) -> dict[str, object]:
    code = context["code"]
    sense_codons = context["codons"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    if not isinstance(code, dict) or not isinstance(sense_codons, list):
        raise ValueError("q context malformed")
    if not isinstance(q_projected, dict) or not isinstance(q_names, list):
        raise ValueError("q context malformed")
    fibers = fibers_for(code, sense_codons)  # type: ignore[arg-type]
    pooled = {str(codon): 1.0 for codon in sense_codons}
    for row in rows:
        counts = row["codon_counts"]
        if not isinstance(counts, dict):
            raise ValueError("row missing codon counts")
        for codon, count in counts.items():
            pooled[str(codon)] += int(count)

    fiber_parts: dict[str, dict[str, object]] = {}
    for aa, fiber in fibers.items():
        gc_codons = [codon for codon in fiber if codon[2] in {"G", "C"}]
        at_codons = [codon for codon in fiber if codon[2] not in {"G", "C"}]
        fiber_parts[aa] = {
            "fiber": fiber,
            "gc_codons": gc_codons,
            "gc_weights": [pooled[codon] for codon in gc_codons],
            "at_codons": at_codons,
            "at_weights": [pooled[codon] for codon in at_codons],
            "fiber_weights": [pooled[codon] for codon in fiber],
        }

    q_arrays: list[dict[str, object]] = []
    for name in q_names:
        qvec = q_projected[str(name)]
        if not isinstance(qvec, dict):
            raise ValueError("projected q vector malformed")
        q_arrays.append(
            {
                "name": str(name),
                "denom": math.sqrt(sum(float(qvec[str(codon)]) ** 2 for codon in sense_codons)),
                "weights": qvec,
            }
        )

    row_specs: list[dict[str, object]] = []
    for row in rows:
        original_counts = row["codon_counts"]
        if not isinstance(original_counts, dict):
            raise ValueError("row missing codon counts")
        tasks: list[tuple[list[str], list[float], int]] = []
        aa_counts: dict[str, int] = {}
        gc3_by_aa: dict[str, int] = {}
        for aa, fiber in fibers.items():
            parts = fiber_parts[aa]
            n_gc = sum(int(original_counts[codon]) for codon in fiber if codon[2] in {"G", "C"})
            n_at = sum(int(original_counts[codon]) for codon in fiber if codon[2] not in {"G", "C"})
            aa_counts[aa] = n_gc + n_at
            gc3_by_aa[aa] = n_gc
            if n_gc:
                gc_codons = parts["gc_codons"]
                gc_weights = parts["gc_weights"]
                if isinstance(gc_codons, list) and isinstance(gc_weights, list) and gc_codons:
                    tasks.append((gc_codons, gc_weights, n_gc))
                else:
                    tasks.append((parts["fiber"], parts["fiber_weights"], n_gc))  # type: ignore[arg-type]
            if n_at:
                at_codons = parts["at_codons"]
                at_weights = parts["at_weights"]
                if isinstance(at_codons, list) and isinstance(at_weights, list) and at_codons:
                    tasks.append((at_codons, at_weights, n_at))
                else:
                    tasks.append((parts["fiber"], parts["fiber_weights"], n_at))  # type: ignore[arg-type]
        row_specs.append(
            {
                "tasks": tasks,
                "sense_total": int(row["sense_total"]),
                "gc3": float(row["gc3"]),
                "enc_proxy": float(row["enc_proxy"]),
                "aa_counts": aa_counts,
                "gc3_by_aa": gc3_by_aa,
            }
        )
    return {
        "code": code,
        "sense_codons": sense_codons,
        "fibers": fibers,
        "q_arrays": q_arrays,
        "row_specs": row_specs,
    }


def synonymous_recoded_q(
    recoder: dict[str, object],
    rng: random.Random,
) -> tuple[list[list[float]], dict[str, float]]:
    code = recoder["code"]
    sense_codons = recoder["sense_codons"]
    fibers = recoder["fibers"]
    q_arrays = recoder["q_arrays"]
    row_specs = recoder["row_specs"]
    if not isinstance(code, dict) or not isinstance(sense_codons, list) or not isinstance(fibers, dict):
        raise ValueError("recoder malformed")
    if not isinstance(q_arrays, list) or not isinstance(row_specs, list):
        raise ValueError("recoder malformed")

    gc3_abs_diffs: list[float] = []
    enc_rel_diffs: list[float] = []
    aa_count_errors: list[float] = []
    per_aa_gc3_errors: list[float] = []
    out: list[list[float]] = []
    for spec in row_specs:
        if not isinstance(spec, dict):
            raise ValueError("recoder row spec malformed")
        new_counts = {str(codon): 0 for codon in sense_codons}
        tasks = spec["tasks"]
        if not isinstance(tasks, list):
            raise ValueError("recoder task list malformed")
        for task in tasks:
            population, weights, total_for_task = task
            sampled_map = sample_multinomial_fast(population, weights, int(total_for_task), rng)
            for codon, count in sampled_map.items():
                new_counts[codon] = new_counts.get(codon, 0) + count

        total = int(spec["sense_total"])
        if total <= 0 or sum(new_counts.values()) != total:
            raise ValueError("synonymous recoding changed sense codon total")
        gc3_new = sum(new_counts[codon] for codon in sense_codons if codon[2] in {"G", "C"}) / total
        gc3_abs_diffs.append(abs(gc3_new - float(spec["gc3"])))
        enc_new = effective_number(new_counts, code, fibers)  # type: ignore[arg-type]
        enc_old = float(spec["enc_proxy"])
        if enc_old > EPS:
            enc_rel_diffs.append(abs(enc_new - enc_old) / enc_old)

        aa_counts_old = spec["aa_counts"]
        gc3_by_aa_old = spec["gc3_by_aa"]
        if not isinstance(aa_counts_old, dict) or not isinstance(gc3_by_aa_old, dict):
            raise ValueError("recoder constraints malformed")
        max_aa_error = 0
        max_gc3_by_aa_error = 0
        for aa, fiber in fibers.items():
            aa_new = sum(new_counts[codon] for codon in fiber)
            gc3_aa_new = sum(new_counts[codon] for codon in fiber if codon[2] in {"G", "C"})
            max_aa_error = max(max_aa_error, abs(aa_new - int(aa_counts_old[aa])))
            max_gc3_by_aa_error = max(max_gc3_by_aa_error, abs(gc3_aa_new - int(gc3_by_aa_old[aa])))
        aa_count_errors.append(float(max_aa_error))
        per_aa_gc3_errors.append(float(max_gc3_by_aa_error))

        q_row: list[float] = []
        for q_item in q_arrays:
            if not isinstance(q_item, dict) or not isinstance(q_item["weights"], dict):
                raise ValueError("recoder q array malformed")
            qvec = q_item["weights"]
            denom = float(q_item["denom"])
            q_row.append(sum(new_counts[codon] * float(qvec[codon]) for codon in sense_codons) / total / denom)
        out.append(q_row)

    return out, {
        "mean_abs_gc3_error": mean(gc3_abs_diffs),
        "p95_abs_gc3_error": percentile_nearest_rank(gc3_abs_diffs, 0.95),
        "max_abs_gc3_error": max(gc3_abs_diffs) if gc3_abs_diffs else 0.0,
        "mean_relative_enc_proxy_error": mean(enc_rel_diffs),
        "p95_relative_enc_proxy_error": percentile_nearest_rank(enc_rel_diffs, 0.95),
        "mean_max_aa_count_error": mean(aa_count_errors),
        "max_aa_count_error": max(aa_count_errors) if aa_count_errors else 0.0,
        "mean_max_per_aa_gc3_count_error": mean(per_aa_gc3_errors),
        "max_per_aa_gc3_count_error": max(per_aa_gc3_errors) if per_aa_gc3_errors else 0.0,
    }


def synonymous_recoding_nulls(
    rows: list[dict[str, object]],
    q_matrix: list[list[float]],
    context: dict[str, object],
    folds: list[FoldState],
    p_target: list[float],
    slot_targets: dict[str, list[float]],
    p_base_preds: list[float],
    slot_base_preds: dict[str, list[float]],
    p_base_sse: float,
    b: int,
) -> tuple[dict[str, dict[str, dict[str, float]]], dict[str, object]]:
    null_values = {slot: {"layer1_delta_r2": [], "layer2_delta_r2": []} for slot in SLOT_NAMES}
    recoder = build_recoder_context(rows, context)
    diagnostics: list[dict[str, float]] = []
    max_abs_q_delta = 0.0
    changed_trials = 0
    for trial in range(b):
        rng = stable_random(f"{SEED}|synonymous-recoding|trial={trial}")
        recoded_q, diag = synonymous_recoded_q(recoder, rng)
        diagnostics.append(diag)
        trial_max = 0.0
        for recoded_row, observed_row in zip(recoded_q, q_matrix):
            for left, right in zip(recoded_row, observed_row):
                trial_max = max(trial_max, abs(left - right))
        max_abs_q_delta = max(max_abs_q_delta, trial_max)
        if trial_max > 1e-12:
            changed_trials += 1
        result = evaluate_layer12_for_q(recoded_q, folds, p_target, slot_targets, p_base_preds, slot_base_preds, p_base_sse)
        for slot in SLOT_NAMES:
            null_values[slot]["layer1_delta_r2"].append(float(result[slot]["layer1_delta_r2"]))
            null_values[slot]["layer2_delta_r2"].append(float(result[slot]["layer2_delta_r2"]))
    return summarize_nulls(null_values), {
        "actual_B": b,
        "null_degenerate": False,
        "null_model": "amino-acid sequence preserved; per-amino-acid GC3-ending counts preserved exactly; codons resampled from pooled synonymous usage; ENC proxy monitored",
        "max_abs_q_delta_after_recoding": max_abs_q_delta,
        "trials_with_q_changed": changed_trials,
        "constraint_diagnostics_mean_over_nulls": {
            "mean_abs_gc3_error": mean([d["mean_abs_gc3_error"] for d in diagnostics]),
            "p95_abs_gc3_error": mean([d["p95_abs_gc3_error"] for d in diagnostics]),
            "max_abs_gc3_error": max((d["max_abs_gc3_error"] for d in diagnostics), default=0.0),
            "mean_relative_enc_proxy_error": mean([d["mean_relative_enc_proxy_error"] for d in diagnostics]),
            "p95_relative_enc_proxy_error": mean([d["p95_relative_enc_proxy_error"] for d in diagnostics]),
            "mean_max_aa_count_error": mean([d["mean_max_aa_count_error"] for d in diagnostics]),
            "max_aa_count_error": max((d["max_aa_count_error"] for d in diagnostics), default=0.0),
            "mean_max_per_aa_gc3_count_error": mean([d["mean_max_per_aa_gc3_count_error"] for d in diagnostics]),
            "max_per_aa_gc3_count_error": max((d["max_per_aa_gc3_count_error"] for d in diagnostics), default=0.0),
        },
    }


def synonymous_shuffle_nulls(
    rows: list[dict[str, object]],
    q_matrix: list[list[float]],
    context: dict[str, object],
    observed_layer12: dict[str, dict[str, object]],
    b: int,
) -> tuple[dict[str, dict[str, dict[str, float]]], dict[str, object]]:
    code = context["code"]
    codons = context["codons"]
    if not isinstance(code, dict) or not isinstance(codons, list):
        raise ValueError("q context malformed")
    max_abs_delta = 0.0
    null_values = {slot: {"layer1_delta_r2": [], "layer2_delta_r2": []} for slot in SLOT_NAMES}
    for trial in range(b):
        trial_invariant = True
        for index, row in enumerate(rows):
            seq = row["sequence"]
            gene = row["gene"]
            if not isinstance(seq, list) or not isinstance(gene, str):
                raise ValueError("row malformed")
            shuffled = shuffled_synonymous_sequence(seq, code, stable_random(f"{SEED}|synonymous|trial={trial}|gene={gene}"))  # type: ignore[arg-type]
            counts = codon_counts_from_sequence(shuffled, codons)  # type: ignore[arg-type]
            shuffled_q = q_row_from_counts(counts, context)
            for left, right in zip(shuffled_q, q_matrix[index]):
                delta = abs(left - right)
                max_abs_delta = max(max_abs_delta, delta)
                if delta > 1e-12:
                    trial_invariant = False
        if not trial_invariant:
            raise ValueError("within-gene synonymous shuffle changed count-based Q9 coordinates unexpectedly")
        for slot in SLOT_NAMES:
            null_values[slot]["layer1_delta_r2"].append(float(observed_layer12[slot]["layer1_delta_r2"]))
            null_values[slot]["layer2_delta_r2"].append(float(observed_layer12[slot]["layer2_delta_r2"]))
    return summarize_nulls(null_values), {
        "actual_B": b,
        "max_abs_q_delta_after_shuffle": max_abs_delta,
        "invariant": max_abs_delta <= 1e-12,
        "null_degenerate": True,
        "reason": "shuffled_synonymous_sequence permutes existing synonymous codons within each gene; after recomputing Q9 from codon counts, the count-based Q coordinates are unchanged for every shuffle trial",
    }


def layer3_decomposition(
    q_matrix: list[list[float]],
    layer12: dict[str, dict[str, object]],
    folds: list[FoldState],
    p_target: list[float],
    p_base_preds: list[float],
) -> dict[str, object]:
    p_base_sse = cv_sse(p_target, p_base_preds)
    p_full_q_preds = cv_predictions(p_target, folds, q_matrix)
    p_full_q_sse = cv_sse(p_target, p_full_q_preds)

    ehat_all = [[float(layer12[slot]["ehat"][index]) for slot in SLOT_NAMES] for index in range(len(p_target))]  # type: ignore[index]
    p_exec_preds = cv_predictions(p_target, folds, ehat_all)
    p_exec_sse = cv_sse(p_target, p_exec_preds)

    q_resid = q_residual_oof(q_matrix, folds, ehat_all)
    p_exec_resid_preds = cv_predictions(p_target, folds, combine_columns(ehat_all, q_resid))
    p_exec_resid_sse = cv_sse(p_target, p_exec_resid_preds)

    full_delta_dl = delta_dl(p_base_sse, p_full_q_sse, len(p_target))
    exec_delta_dl = delta_dl(p_base_sse, p_exec_sse, len(p_target))
    unresolved_delta_dl = delta_dl(p_exec_sse, p_exec_resid_sse, len(p_target))
    total_with_resid_delta_dl = delta_dl(p_base_sse, p_exec_resid_sse, len(p_target))
    return {
        "full_pq_delta_r2": delta_r2(p_base_sse, p_full_q_sse, target_tss(p_target)),
        "observed_execution_delta_r2": delta_r2(p_base_sse, p_exec_sse, target_tss(p_target)),
        "unresolved_direct_delta_r2_increment": delta_r2(p_exec_sse, p_exec_resid_sse, target_tss(p_target)),
        "full_pq_delta_dl": full_delta_dl,
        "observed_execution_delta_dl": exec_delta_dl,
        "unresolved_direct_delta_dl": unresolved_delta_dl,
        "total_with_q_resid_delta_dl": total_with_resid_delta_dl,
        "observed_execution_over_full_delta_dl": exec_delta_dl / full_delta_dl if abs(full_delta_dl) > EPS else 0.0,
        "sse": {
            "C": p_base_sse,
            "C_plus_Q": p_full_q_sse,
            "C_plus_Ehat_all": p_exec_sse,
            "C_plus_Ehat_all_plus_Q_resid": p_exec_resid_sse,
        },
    }


def main() -> None:
    started = time.time()
    try:
        repo = pathlib.Path.cwd()
        data = build_dataset(repo)
        genes = data["genes"]
        q_matrix = data["q"]
        controls = data["controls"]
        p_target = data["p"]
        slot_targets = data["slots"]
        rows = data["rows"]
        context = data["context"]
        if not isinstance(genes, list) or not isinstance(q_matrix, list) or not isinstance(controls, list):
            raise ValueError("dataset malformed")
        if not isinstance(p_target, list) or not isinstance(slot_targets, dict) or not isinstance(rows, list):
            raise ValueError("dataset malformed")
        if len(genes) < 200:
            emit("needs_data", checks=[], reason=f"active all-slot join too small: n={len(genes)}")

        folds = make_fold_states(controls, FOLD_COUNT)  # type: ignore[arg-type]
        p_base_preds = cv_predictions(p_target, folds)  # type: ignore[arg-type]
        p_base_sse = cv_sse(p_target, p_base_preds)  # type: ignore[arg-type]
        slot_base_preds = {
            slot: cv_predictions(slot_targets[slot], folds)  # type: ignore[index]
            for slot in SLOT_NAMES
        }

        layer12 = evaluate_layer12_for_q(
            q_matrix,  # type: ignore[arg-type]
            folds,
            p_target,  # type: ignore[arg-type]
            slot_targets,  # type: ignore[arg-type]
            p_base_preds,
            slot_base_preds,
            p_base_sse,
        )
        layer3 = layer3_decomposition(q_matrix, layer12, folds, p_target, p_base_preds)  # type: ignore[arg-type]

        actual_b = TARGET_NULL_B
        comp_nulls = collect_nulls(
            q_matrix,  # type: ignore[arg-type]
            folds,
            p_target,  # type: ignore[arg-type]
            slot_targets,  # type: ignore[arg-type]
            p_base_preds,
            slot_base_preds,
            p_base_sse,
            controls,  # type: ignore[arg-type]
            actual_b,
        )
        recoding_summary, recoding_verification = synonymous_recoding_nulls(
            rows,  # type: ignore[arg-type]
            q_matrix,  # type: ignore[arg-type]
            context,  # type: ignore[arg-type]
            folds,
            p_target,  # type: ignore[arg-type]
            slot_targets,  # type: ignore[arg-type]
            p_base_preds,
            slot_base_preds,
            p_base_sse,
            actual_b,
        )
        shuffle_summary, shuffle_verification = synonymous_shuffle_nulls(
            rows,  # type: ignore[arg-type]
            q_matrix,  # type: ignore[arg-type]
            context,  # type: ignore[arg-type]
            layer12,
            actual_b,
        )

        comp_summary = comp_nulls["summary"]
        if not isinstance(comp_summary, dict) or not isinstance(recoding_summary, dict):
            raise ValueError("effective null summary malformed")

        slot_results: dict[str, object] = {}
        certified_slots: list[str] = []
        for slot in SLOT_NAMES:
            l1 = float(layer12[slot]["layer1_delta_r2"])
            l2 = float(layer12[slot]["layer2_delta_r2"])
            l1_comp95 = float(comp_summary[slot]["layer1_delta_r2"]["null95"])  # type: ignore[index]
            l2_comp95 = float(comp_summary[slot]["layer2_delta_r2"]["null95"])  # type: ignore[index]
            l1_recode95 = float(recoding_summary[slot]["layer1_delta_r2"]["null95"])
            l2_recode95 = float(recoding_summary[slot]["layer2_delta_r2"]["null95"])
            l1_shuffle95 = float(shuffle_summary[slot]["layer1_delta_r2"]["null95"])
            l2_shuffle95 = float(shuffle_summary[slot]["layer2_delta_r2"]["null95"])
            slot_dl_drop = float(layer12[slot]["layer2_delta_dl"]) > 0.0
            certified = (
                l1 > l1_comp95
                and l1 > l1_recode95
                and l2 > l2_comp95
                and l2 > l2_recode95
                and slot_dl_drop
            )
            if certified:
                certified_slots.append(slot)
            slot_results[slot] = {
                "layer1_q_to_slot_heldout_delta_r2": l1,
                "layer1_delta_dl": layer12[slot]["layer1_delta_dl"],
                "layer1_null95": {
                    "composition_bin_permutation": l1_comp95,
                    "synonymous_recoding": l1_recode95,
                },
                "layer2_ehat_q_to_p_heldout_delta_r2": l2,
                "layer2_delta_dl": layer12[slot]["layer2_delta_dl"],
                "layer2_null95": {
                    "composition_bin_permutation": l2_comp95,
                    "synonymous_recoding": l2_recode95,
                },
                "diagnostic_degenerate_within_gene_synonymous_shuffle_null95": {
                    "layer1_delta_r2": l1_shuffle95,
                    "layer2_delta_r2": l2_shuffle95,
                    "used_in_verdict_gate": False,
                },
                "execution_certified_j": certified,
                "slot_enters_with_total_dl_drop": slot_dl_drop,
            }

        final_conclusion = "observable_execution_subblock" if certified_slots else "unresolved_needs_external"
        checks = [
            {
                "name": "q9_and_controls_assembled",
                "passed": True,
                "q_dim": len(q_matrix[0]) if q_matrix else 0,  # type: ignore[index]
                "controls": ["log_CDS_length", "train_fold_aa_composition_PCs_5", "GC3", "pLDDT_mean_imputed_train_fold", "pLDDT_missing_indicator"],
                "payload_keys_confirmed": {
                    "cds": "cds",
                    "P": "protein_abundance",
                    "TE": "genes",
                    "mRNA_half_life": "records",
                    "protein_turnover": "protein_turnover",
                    "occupancy": "genes",
                    "structural_order": "proteins",
                },
            },
            {
                "name": "gene_level_folds",
                "passed": True,
                "fold_count": FOLD_COUNT,
                "helper": "deterministic sorted-gene index modulo fold_count, matching sibling folds_for_n semantics",
                "fold_sizes": [len(fold.test) for fold in folds],
            },
            {
                "name": "layer1_slot_readability",
                "passed": True,
                "slots": {slot: slot_results[slot] for slot in SLOT_NAMES},
            },
            {
                "name": "layer2_oof_bridge_no_mediation",
                "passed": True,
                "rule": "Ehat_j(Q) is generated on held-out genes as CV prediction(C+Q)-prediction(C), then used in a separate held-out P model",
            },
            {
                "name": "layer3_pq_decomposition",
                "passed": True,
                "layer3": layer3,
            },
            {
                "name": "two_class_nulls",
                "passed": True,
                "actual_B": {
                    "composition_bin_permutation": actual_b,
                    "synonymous_recoding": actual_b,
                },
                "publishable_B": PUBLISHABLE_NULL_B,
                "composition_bin_axes": ["log_CDS_length", "global_aa_PC1", "GC3"],
                "baseline_bin_axis": "not_used_no_independent_baseline_available",
                "synonymous_recoding": recoding_verification,
                "diagnostic_degenerate_within_gene_synonymous_shuffle": shuffle_verification,
            },
            {
                "name": "execution_decomposition_verdict",
                "passed": True,
                "certified_slots": certified_slots,
                "final_conclusion": final_conclusion,
                "gate": "Layer1 Q->E_j held-out delta_R2 and Layer2 Ehat_j(Q)->P held-out delta_R2 must both exceed composition-bin and synonymous-recoding null95, and the slot must enter with positive total DL drop; degenerate within-gene synonymous shuffle is diagnostic only",
            },
        ]

        emit(
            "passed",
            checks=checks,
            organism="Saccharomyces cerevisiae",
            n_genes=len(genes),
            q_names=data.get("q_names"),
            source_counts=data.get("source_counts"),
            layer1_layer2_by_slot=slot_results,
            layer3=layer3,
            nulls={
                "actual_B": {
                    "composition_bin_permutation": actual_b,
                    "synonymous_recoding": actual_b,
                    "diagnostic_degenerate_within_gene_synonymous_shuffle": actual_b,
                },
                "composition_bin_permutation": comp_summary,
                "synonymous_recoding": recoding_summary,
                "synonymous_recoding_verification": recoding_verification,
                "diagnostic_degenerate_within_gene_synonymous_shuffle": shuffle_summary,
                "diagnostic_degenerate_within_gene_synonymous_shuffle_verification": shuffle_verification,
                "publishable_B": PUBLISHABLE_NULL_B,
            },
            certified_slots=certified_slots,
            final_conclusion=final_conclusion,
            verdict=(
                "observable_execution_subblock: at least one observed rate proxy slot passed both effective null classes"
                if certified_slots
                else "unresolved_needs_external: current observed proxy slots do not certify an execution subblock under both effective null classes"
            ),
            cannot_claim=[
                "rate proxies come from different experimental conditions and are not causal rate-function identification",
                "held-out bridge prediction is a cross-fitted mediation-style decomposition, not intervention evidence",
                "occupancy_summary is a local ribosome occupancy proxy, not a direct dwell-time or elongation-rate measurement",
                "synonymous-recoding preserves amino-acid sequence and per-amino-acid GC3-ending counts but remains a proxy null, not a causal intervention",
                "within-gene synonymous shuffle preserves codon counts, so count-based Q9 is invariant under that null and it is diagnostic only",
            ],
            runtime_sec=round(time.time() - started, 3),
            seed=SEED,
        )
    except Exception as exc:
        emit(
            "failed",
            checks=[],
            reason=f"{type(exc).__name__}: {exc}",
            runtime_sec=round(time.time() - started, 3),
        )


if __name__ == "__main__":
    main()

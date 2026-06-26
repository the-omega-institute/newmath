#!/usr/bin/env python3
"""Structure-gated synonymous placement test for B*_Q6 in yeast."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_q6_structure_gated_placement_powered"
CLAIM_ID = "h3.cross_layer_relation.structure_gated_placement.b_star_q6_structure_gated_placement_powered"

ORGANISM = "saccharomyces_cerevisiae"
FOLD_COUNT = 5
ACTUAL_B = 100
RIDGE = 1e-6
EPS = 1e-12
SMOOTH_WINDOW = 5
LAG_GRID = (0, 20, 40)
SEED = "sha256:b_star_q6_structure_gated_placement_powered:deterministic"
LOW_PLDDT_CUTOFF = 0.70

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
TARGETS = ("logTE", "log_mrna_half_life")


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
    return sum((value - center) * (value - center) for value in values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(indices: list[int], material: str) -> list[int]:
    out = list(indices)
    for index in range(len(out) - 1, 0, -1):
        digest = stable_digest(f"{material}|index={index}|n={len(out)}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def stable_offset(n: int, material: str) -> int:
    if n <= 1:
        return 0
    return 1 + (int.from_bytes(stable_digest(material)[:8], "big") % (n - 1))


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def rna_to_dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def log10_positive(value: object) -> float | None:
    if not finite_number(value):
        return None
    number = float(value)
    if number <= 0.0:
        return None
    return math.log10(number)


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[i] * vector[i] for i in range(len(vector))) for row in matrix]


def normalize_vector(vector: list[float]) -> list[float]:
    norm = math.sqrt(sum(value * value for value in vector))
    if norm <= EPS:
        return [0.0 for _ in vector]
    return [value / norm for value in vector]


def covariance(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    width = len(matrix[0])
    out = [[0.0 for _ in range(width)] for _ in range(width)]
    scale = 1.0 / max(1, len(matrix))
    for row in matrix:
        for i in range(width):
            xi = row[i]
            for j in range(i, width):
                out[i][j] += xi * row[j] * scale
    for i in range(width):
        for j in range(i):
            out[i][j] = out[j][i]
    return out


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


def standardize_train_apply(
    matrix: list[list[float]],
    train_indices: list[int],
    test_indices: list[int],
) -> tuple[list[list[float]], list[list[float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train_indices], [[] for _ in test_indices]
    width = len(matrix[0])
    centers: list[float] = []
    scales: list[float] = []
    for col in range(width):
        values = [matrix[i][col] for i in train_indices]
        center = mean(values)
        sd = math.sqrt(variance(values))
        if sd <= EPS:
            sd = 1.0
        centers.append(center)
        scales.append(sd)
    train = [[(matrix[i][col] - centers[col]) / scales[col] for col in range(width)] for i in train_indices]
    test = [[(matrix[i][col] - centers[col]) / scales[col] for col in range(width)] for i in test_indices]
    return train, test


def cholesky_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    jitter = 0.0
    for attempt in range(7):
        try:
            lower = [[0.0 for _ in range(n)] for _ in range(n)]
            for i in range(n):
                for j in range(i + 1):
                    value = matrix[i][j] + (jitter if i == j else 0.0)
                    for k in range(j):
                        value -= lower[i][k] * lower[j][k]
                    if i == j:
                        if value <= EPS:
                            raise ValueError("non-positive definite")
                        lower[i][j] = math.sqrt(value)
                    else:
                        lower[i][j] = value / lower[j][j]
            y = [0.0 for _ in range(n)]
            for i in range(n):
                value = rhs[i]
                for k in range(i):
                    value -= lower[i][k] * y[k]
                y[i] = value / lower[i][i]
            x = [0.0 for _ in range(n)]
            for i in range(n - 1, -1, -1):
                value = y[i]
                for k in range(i + 1, n):
                    value -= lower[k][i] * x[k]
                x[i] = value / lower[i][i]
            return x
        except ValueError:
            jitter = 1e-8 if attempt == 0 else jitter * 10.0
    return gaussian_solve(matrix, rhs)


def gaussian_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += RIDGE
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col] if abs(aug[col][col]) > EPS else EPS
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


def ridge_fit(train_x: list[list[float]], train_y: list[float], ridge: float = RIDGE) -> list[float]:
    if not train_x:
        return []
    width = len(train_x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, y in zip(train_x, train_y):
        for i in range(width):
            xi = row[i]
            rhs[i] += xi * y
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        xtx[i][i] += 0.0 if i == 0 else ridge
    return cholesky_solve(xtx, rhs)


def dot_row(row: list[float], coeff: list[float]) -> float:
    return sum(row[i] * coeff[i] for i in range(len(coeff)))


def standard_code(repo: pathlib.Path) -> dict[str, str]:
    raw = load_json(repo / "tools/bio_reality/data/ncbi_genetic_codes.json")
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


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def q9_context(repo: pathlib.Path) -> dict[str, object]:
    code_rna = standard_code(repo)
    codons_rna = [codon for codon in sorted(code_rna) if code_rna[codon] != "*"]
    fibers_rna = fibers_for(code_rna, codons_rna)
    projected = {name: project_syn(vector, fibers_rna) for name, vector in q_vectors(codons_rna).items()}
    q_dna: dict[str, tuple[float, ...]] = {}
    q_names = list(projected)
    for codon in codons_rna:
        values: list[float] = []
        for name in q_names:
            vec = projected[name]
            denom = math.sqrt(sum(float(vec[c]) * float(vec[c]) for c in codons_rna))
            values.append(float(vec[codon]) / denom if denom > EPS else 0.0)
        q_dna[rna_to_dna(codon)] = tuple(values)
    return {
        "code_dna": {rna_to_dna(codon): aa for codon, aa in code_rna.items()},
        "sense_codons_dna": sorted(q_dna),
        "aa_order": sorted({aa for aa in code_rna.values() if aa != "*"}),
        "q_by_codon": q_dna,
        "q_names": q_names,
    }


def moving_average(values: list[float], window: int) -> list[float]:
    if not values:
        return []
    radius = window // 2
    out: list[float] = []
    prefix = [0.0]
    for value in values:
        prefix.append(prefix[-1] + value)
    n = len(values)
    for i in range(n):
        lo = max(0, i - radius)
        hi = min(n, i + radius + 1)
        out.append((prefix[hi] - prefix[lo]) / (hi - lo))
    return out


def boundary_weights(s_values: list[float]) -> list[float]:
    smoothed = moving_average(s_values, SMOOTH_WINDOW)
    out = [0.0 for _ in smoothed]
    for i in range(len(smoothed)):
        if len(smoothed) == 1:
            out[i] = 0.0
        elif i == 0:
            out[i] = abs(smoothed[1] - smoothed[0])
        elif i == len(smoothed) - 1:
            out[i] = abs(smoothed[-1] - smoothed[-2])
        else:
            out[i] = abs((smoothed[i + 1] - smoothed[i - 1]) * 0.5)
    return out


def feature_pack_from_q_and_weights(
    q_stream: list[tuple[float, ...]],
    low_high_weights: list[float],
    b_weights: list[float],
    include_qglobal: bool,
) -> dict[int | str, list[float]]:
    n = min(len(q_stream), len(low_high_weights), len(b_weights))
    if n <= 0:
        zero9 = [0.0] * 9
        return {"low_minus_high": zero9, 0: zero9, 20: zero9, 40: zero9, "qglobal": zero9}
    scale = 1.0 / n
    qglobal = [0.0] * 9
    low_minus_high = [0.0] * 9
    lagged = {lag: [0.0] * 9 for lag in LAG_GRID}
    for i in range(n):
        q = q_stream[i]
        low_weight = low_high_weights[i] * scale
        if include_qglobal:
            qglobal[0] += q[0] * scale; qglobal[1] += q[1] * scale; qglobal[2] += q[2] * scale
            qglobal[3] += q[3] * scale; qglobal[4] += q[4] * scale; qglobal[5] += q[5] * scale
            qglobal[6] += q[6] * scale; qglobal[7] += q[7] * scale; qglobal[8] += q[8] * scale
        low_minus_high[0] += q[0] * low_weight; low_minus_high[1] += q[1] * low_weight; low_minus_high[2] += q[2] * low_weight
        low_minus_high[3] += q[3] * low_weight; low_minus_high[4] += q[4] * low_weight; low_minus_high[5] += q[5] * low_weight
        low_minus_high[6] += q[6] * low_weight; low_minus_high[7] += q[7] * low_weight; low_minus_high[8] += q[8] * low_weight
        for lag in LAG_GRID:
            source = i - lag
            if source >= 0:
                ql = q_stream[source]
                weight = b_weights[i] * scale
                acc = lagged[lag]
                acc[0] += ql[0] * weight; acc[1] += ql[1] * weight; acc[2] += ql[2] * weight
                acc[3] += ql[3] * weight; acc[4] += ql[4] * weight; acc[5] += ql[5] * weight
                acc[6] += ql[6] * weight; acc[7] += ql[7] * weight; acc[8] += ql[8] * weight
    return {
        "low_minus_high": low_minus_high,
        0: lagged[0],
        20: lagged[20],
        40: lagged[40],
        "qglobal": qglobal,
    }


def feature_pack_from_q_and_s(q_stream: list[tuple[float, ...]], s_values: list[float], include_qglobal: bool = True) -> dict[int | str, list[float]]:
    n = min(len(q_stream), len(s_values))
    s = s_values[:n]
    return feature_pack_from_q_and_weights(q_stream, [1.0 - 2.0 * value for value in s], boundary_weights(s), include_qglobal)


def raw_feature_matrices(packs: list[dict[int | str, list[float]]]) -> dict[int | str, list[list[float]]]:
    out: dict[int | str, list[list[float]]] = {"low_minus_high": [], "qglobal": []}
    for lag in LAG_GRID:
        out[lag] = []
    for pack in packs:
        out["low_minus_high"].append(list(pack["low_minus_high"]))  # type: ignore[arg-type]
        out["qglobal"].append(list(pack["qglobal"]))  # type: ignore[arg-type]
        for lag in LAG_GRID:
            out[lag].append(list(pack[lag]))  # type: ignore[arg-type]
    return out


def addons_for_lag(matrices: dict[int | str, list[list[float]]], lag: int) -> list[list[float]]:
    low_high = matrices["low_minus_high"]
    boundary = matrices[lag]
    return [list(low_high[i]) + list(boundary[i]) for i in range(len(low_high))]  # type: ignore[index]


def load_ordered_cds(repo: pathlib.Path) -> tuple[dict[str, list[str]], dict[str, int]]:
    payload = load_json(repo / "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json")
    cds = payload.get("cds") if isinstance(payload, dict) else None
    if not isinstance(cds, list):
        raise ValueError("CDS payload must contain key cds")
    out: dict[str, list[str]] = {}
    raw_n: dict[str, int] = {}
    for item in cds:
        if not isinstance(item, dict):
            continue
        gene_id = item.get("gene_id")
        codons = item.get("codons")
        n_codons = item.get("n_codons")
        if isinstance(gene_id, str) and isinstance(codons, list) and all(isinstance(codon, str) for codon in codons):
            out[gene_id] = [str(codon).upper() for codon in codons]
            raw_n[gene_id] = int(n_codons) if isinstance(n_codons, int) else len(codons)
    return out, raw_n


def load_plddt(repo: pathlib.Path) -> dict[str, list[float]]:
    payload = load_json(repo / "tools/bio_reality/data/structural_order_per_residue_saccharomyces_cerevisiae.json")
    raw = payload.get("per_residue_plddt") if isinstance(payload, dict) else None
    if not isinstance(raw, dict):
        raise ValueError("pLDDT payload must contain per_residue_plddt")
    out: dict[str, list[float]] = {}
    for gene, values in raw.items():
        if isinstance(gene, str) and isinstance(values, list):
            cleaned = [max(0.0, min(100.0, float(value))) for value in values if finite_number(value)]
            if cleaned:
                out[gene] = cleaned
    return out


def load_te(repo: pathlib.Path) -> dict[str, float]:
    payload = load_json(repo / "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json")
    genes = payload.get("genes") if isinstance(payload, dict) else None
    if not isinstance(genes, list):
        raise ValueError("TE payload must contain genes")
    out: dict[str, float] = {}
    for item in genes:
        if isinstance(item, dict):
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
        if isinstance(item, dict):
            gene = item.get("Syst")
            logged = log10_positive(item.get("thalf"))
            if isinstance(gene, str) and logged is not None:
                out[gene] = logged
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


def codon_counts(sequence: list[str], sense_codons: list[str]) -> dict[str, int]:
    out = {codon: 0 for codon in sense_codons}
    for raw in sequence:
        codon = raw.upper()
        if codon in out:
            out[codon] += 1
    return out


class GeneRow:
    def __init__(
        self,
        gene: str,
        codons: list[str],
        q_stream: list[tuple[float, ...]],
        s_values: list[float],
        low_high_weights: list[float],
        boundary_weights_cached: list[float],
        aa_by_pos: list[str],
        controls: dict[str, object],
        p: float,
        targets: dict[str, float],
        pack: dict[int | str, list[float]],
    ) -> None:
        self.gene = gene
        self.codons = codons
        self.q_stream = q_stream
        self.s_values = s_values
        self.low_high_weights = low_high_weights
        self.boundary_weights_cached = boundary_weights_cached
        self.aa_by_pos = aa_by_pos
        self.controls = controls
        self.p = p
        self.targets = targets
        self.pack = pack


def build_rows(repo: pathlib.Path) -> dict[str, object]:
    context = q9_context(repo)
    cds, raw_n = load_ordered_cds(repo)
    plddt = load_plddt(repo)
    te = load_te(repo)
    half_life = load_mrna_half_life(repo)
    abundance = load_abundance(repo)
    q_by_codon = context["q_by_codon"]
    code_dna = context["code_dna"]
    sense_codons = context["sense_codons_dna"]
    aa_order = context["aa_order"]
    if not isinstance(q_by_codon, dict) or not isinstance(code_dna, dict) or not isinstance(sense_codons, list) or not isinstance(aa_order, list):
        raise ValueError("q9 context malformed")
    active = sorted(set(cds) & set(plddt) & set(te) & set(half_life) & set(abundance))
    rows: list[GeneRow] = []
    skipped = {"no_aligned_residue": 0, "unsupported_sense_codon": 0}
    for gene in active:
        sequence = cds[gene]
        n_align = min(max(0, len(sequence) - 1), len(plddt[gene]))
        if n_align <= 0:
            skipped["no_aligned_residue"] += 1
            continue
        aligned_codons = sequence[:n_align]
        if any(codon not in q_by_codon for codon in aligned_codons):
            skipped["unsupported_sense_codon"] += 1
            continue
        q_stream = [q_by_codon[codon] for codon in aligned_codons]  # type: ignore[index]
        s_values = [max(0.0, min(1.0, value / 100.0)) for value in plddt[gene][:n_align]]
        low_high_weights = [1.0 - 2.0 * value for value in s_values]
        boundary_cached = boundary_weights(s_values)
        pack = feature_pack_from_q_and_weights(q_stream, low_high_weights, boundary_cached, True)
        counts = codon_counts(sequence, sense_codons)  # type: ignore[arg-type]
        sense_total = max(1, sum(counts.values()))
        aa_counts = {str(aa): 0 for aa in aa_order}
        for codon, count in counts.items():
            aa = code_dna.get(codon)
            if isinstance(aa, str) and aa != "*":
                aa_counts[aa] += count
        aa_total = max(1, sum(aa_counts.values()))
        gc3 = sum(count for codon, count in counts.items() if codon[2] in {"G", "C"}) / sense_total
        plddt_mean = mean(s_values)
        controls = {
            "log_len": math.log(max(1, raw_n.get(gene, len(sequence))) * 3.0),
            "aa": [aa_counts[str(aa)] / aa_total for aa in aa_order],
            "gc3": gc3,
            "abundance": abundance[gene],
            "head_cov": 1.0 if n_align > 0 else 0.0,
            "tail_cov": 1.0 if n_align >= max(0, len(sequence) - 1) else 0.0,
            "mean_plddt": plddt_mean,
            "low_frac": sum(1 for value in s_values if value < LOW_PLDDT_CUTOFF) / n_align,
            "plddt_var": variance(s_values),
            "qglobal": pack["qglobal"],
            "aligned_residues": n_align,
            "cds_codons": len(sequence),
        }
        rows.append(
            GeneRow(
                gene=gene,
                codons=aligned_codons,
                q_stream=q_stream,
                s_values=s_values,
                low_high_weights=low_high_weights,
                boundary_weights_cached=boundary_cached,
                aa_by_pos=[str(code_dna[codon]) for codon in aligned_codons],
                controls=controls,
                p=abundance[gene],
                targets={"logTE": te[gene], "log_mrna_half_life": half_life[gene]},
                pack=pack,
            )
        )
    return {
        "rows": rows,
        "context": context,
        "source_counts": {
            "cds": len(cds),
            "per_residue_plddt": len(plddt),
            "logTE": len(te),
            "log_mrna_half_life": len(half_life),
            "protein_abundance": len(abundance),
        },
        "skipped": skipped,
    }


class FoldDesign:
    def __init__(
        self,
        train: list[int],
        test: list[int],
        base_train: list[list[float]],
        base_test: list[list[float]],
        base_inverse: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.base_train = base_train
        self.base_test = base_test
        self.base_inverse = base_inverse


def regularized_gram(rows: list[list[float]], ridge: float = RIDGE) -> list[list[float]]:
    width = len(rows[0])
    gram = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in rows:
        for i in range(width):
            xi = row[i]
            for j in range(i, width):
                gram[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            gram[i][j] = gram[j][i]
        gram[i][i] += 0.0 if i == 0 else ridge
    return gram


def inverse_from_gram(gram: list[list[float]]) -> list[list[float]]:
    width = len(gram)
    columns: list[list[float]] = []
    for col in range(width):
        rhs = [0.0 for _ in range(width)]
        rhs[col] = 1.0
        columns.append(cholesky_solve(gram, rhs))
    return [[columns[col][row] for col in range(width)] for row in range(width)]


def build_fold_designs(rows: list[GeneRow], include_abundance: bool) -> list[FoldDesign]:
    n = len(rows)
    raw_scalar_names = ["log_len", "gc3", "head_cov", "tail_cov"]
    if include_abundance:
        raw_scalar_names.append("abundance")
    scalar_matrix = [[float(row.controls[name]) for name in raw_scalar_names] for row in rows]
    aa_matrix = [list(row.controls["aa"]) for row in rows]  # type: ignore[arg-type]
    qglobal_matrix = [list(row.controls["qglobal"]) for row in rows]  # type: ignore[arg-type]
    structural_matrix = [[float(row.controls["mean_plddt"]), float(row.controls["low_frac"]), float(row.controls["plddt_var"])] for row in rows]
    extra_matrix = [qglobal_matrix[i] + structural_matrix[i] for i in range(n)]
    folds: list[FoldDesign] = []
    for fold in range(FOLD_COUNT):
        test = [index for index in range(n) if index % FOLD_COUNT == fold]
        test_set = set(test)
        train = [index for index in range(n) if index not in test_set]
        scalar_train, scalar_test = standardize_train_apply(scalar_matrix, train, test)
        aa_train_std, aa_test_std = standardize_train_apply(aa_matrix, train, test)
        pcs = top_pcs(aa_train_std, 5)
        aa_train_pc = [[vector_dot(row, pc) for pc in pcs] for row in aa_train_std]
        aa_test_pc = [[vector_dot(row, pc) for pc in pcs] for row in aa_test_std]
        extra_train, extra_test = standardize_train_apply(extra_matrix, train, test)
        base_train: list[list[float]] = []
        base_test: list[list[float]] = []
        for i in range(len(train)):
            base_train.append([1.0] + scalar_train[i] + aa_train_pc[i] + extra_train[i])
        for i in range(len(test)):
            base_test.append([1.0] + scalar_test[i] + aa_test_pc[i] + extra_test[i])
        base_inverse = inverse_from_gram(regularized_gram(base_train))
        folds.append(FoldDesign(train, test, base_train, base_test, base_inverse))
    return folds


class FoldAddon:
    def __init__(
        self,
        train: list[list[float]],
        test: list[list[float]],
        ztz: list[list[float]],
        xtz: list[list[float]],
        ztx: list[list[float]],
        base_projected_ztz: list[list[float]],
        train_schur: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.ztz = ztz
        self.xtz = xtz
        self.ztx = ztx
        self.base_projected_ztz = base_projected_ztz
        self.train_schur = train_schur


def gram_and_cross(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    if not left or not right:
        return []
    width_left = len(left[0])
    width_right = len(right[0])
    out = [[0.0 for _ in range(width_right)] for _ in range(width_left)]
    for row_left, row_right in zip(left, right):
        for i in range(width_left):
            li = row_left[i]
            for j in range(width_right):
                out[i][j] += li * row_right[j]
    return out


def matmul(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    if not left or not right:
        return []
    m = len(left)
    k = len(left[0])
    n = len(right[0])
    out = [[0.0 for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for t in range(k):
            value = left[i][t]
            if value == 0.0:
                continue
            for j in range(n):
                out[i][j] += value * right[t][j]
    return out


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[col] for row in matrix] for col in range(len(matrix[0]))]


def prepare_fold_addon(
    fold: FoldDesign,
    addons: list[list[float]],
) -> FoldAddon:
    train_add, test_add = standardize_train_apply(addons, fold.train, fold.test)
    ztz = regularized_gram(train_add)
    xtz = gram_and_cross(fold.base_train, train_add)
    ztx = transpose(xtz)
    inv_x_xtz = matmul(fold.base_inverse, xtz)
    base_projected = matmul(ztx, inv_x_xtz)
    width = len(ztz)
    schur = [[ztz[i][j] - base_projected[i][j] for j in range(width)] for i in range(width)]
    for i in range(width):
        schur[i][i] += RIDGE
    return FoldAddon(train_add, test_add, ztz, xtz, ztx, base_projected, schur)


def append_prepared_addon(
    fold: FoldDesign,
    addon: FoldAddon,
) -> tuple[list[list[float]], list[list[float]]]:
    train_x = [fold.base_train[i] + addon.train[i] for i in range(len(fold.train))]
    test_x = [fold.base_test[i] + addon.test[i] for i in range(len(fold.test))]
    return train_x, test_x


def fit_predict_prepared(
    target: list[float],
    fold: FoldDesign,
    addon: FoldAddon,
) -> tuple[float, list[float], list[float]]:
    train_y = [target[index] for index in fold.train]
    width_x = len(fold.base_train[0])
    width_z = len(addon.train[0])
    x_ty = [0.0 for _ in range(width_x)]
    z_ty = [0.0 for _ in range(width_z)]
    yy = 0.0
    for row_x, row_z, y in zip(fold.base_train, addon.train, train_y):
        yy += y * y
        for i in range(width_x):
            x_ty[i] += row_x[i] * y
        for j in range(width_z):
            z_ty[j] += row_z[j] * y
    inv_x_xty = mat_vec(fold.base_inverse, x_ty)
    zt_x_inv_x_xty = mat_vec(addon.ztx, inv_x_xty)
    schur_rhs = [z_ty[j] - zt_x_inv_x_xty[j] for j in range(width_z)]
    beta_z = cholesky_solve(addon.train_schur, schur_rhs)
    xtz_beta_z = mat_vec(addon.xtz, beta_z)
    beta_x = mat_vec(fold.base_inverse, [x_ty[i] - xtz_beta_z[i] for i in range(width_x)])
    beta = beta_x + beta_z
    rhs_dot_beta = vector_dot(x_ty, beta_x) + vector_dot(z_ty, beta_z)
    train_sse = max(0.0, yy - rhs_dot_beta)
    preds = []
    for row_x, row_z in zip(fold.base_test, addon.test):
        preds.append(dot_row(row_x, beta_x) + dot_row(row_z, beta_z))
    return train_sse, beta, preds


def cv_predict_base(target: list[float], folds: list[FoldDesign]) -> list[float]:
    preds = [0.0 for _ in target]
    for fold in folds:
        train_y = [target[index] for index in fold.train]
        beta = ridge_fit(fold.base_train, train_y)
        for local, row in enumerate(fold.base_test):
            preds[fold.test[local]] = dot_row(row, beta)
    return preds


def train_sse_for_design(train_x: list[list[float]], train_y: list[float]) -> tuple[float, list[float]]:
    beta = ridge_fit(train_x, train_y)
    sse = 0.0
    for row, y in zip(train_x, train_y):
        residual = y - dot_row(row, beta)
        sse += residual * residual
    return sse, beta


def cv_predict_m1(
    target: list[float],
    folds: list[FoldDesign],
    matrices: dict[int | str, list[list[float]]],
) -> tuple[list[float], dict[str, object]]:
    prepared_by_lag: dict[int, list[FoldAddon]] = {}
    for lag in LAG_GRID:
        addons = addons_for_lag(matrices, lag)
        prepared_by_lag[lag] = [prepare_fold_addon(fold, addons) for fold in folds]
    return cv_predict_m1_prepared(target, folds, prepared_by_lag)


def cv_predict_m1_prepared(
    target: list[float],
    folds: list[FoldDesign],
    prepared_by_lag: dict[int, list[FoldAddon]],
) -> tuple[list[float], dict[str, object]]:
    preds = [0.0 for _ in target]
    selected_lags: list[int] = []
    for fold_index, fold in enumerate(folds):
        best_lag = LAG_GRID[0]
        best_sse = float("inf")
        best_preds: list[float] | None = None
        for lag in LAG_GRID:
            train_sse, _beta, fold_preds = fit_predict_prepared(target, fold, prepared_by_lag[lag][fold_index])
            if train_sse < best_sse - EPS or (abs(train_sse - best_sse) <= EPS and lag < best_lag):
                best_sse = train_sse
                best_lag = lag
                best_preds = fold_preds
        if best_preds is None:
            raise ValueError("lag selection failed")
        selected_lags.append(best_lag)
        for local, pred in enumerate(best_preds):
            preds[fold.test[local]] = pred
    lag_counts = {str(lag): selected_lags.count(lag) for lag in LAG_GRID}
    return preds, {"fold_selected_lags": selected_lags, "lag_counts": lag_counts}


def prepare_m1_addons(
    folds: list[FoldDesign],
    matrices: dict[int | str, list[list[float]]],
) -> dict[int, list[FoldAddon]]:
    prepared: dict[int, list[FoldAddon]] = {}
    for lag in LAG_GRID:
        addons = addons_for_lag(matrices, lag)
        prepared[lag] = [prepare_fold_addon(fold, addons) for fold in folds]
    return prepared


def sse(target: list[float], preds: list[float]) -> float:
    return sum((y - yhat) * (y - yhat) for y, yhat in zip(target, preds))


def tss(target: list[float]) -> float:
    center = mean(target)
    value = sum((y - center) * (y - center) for y in target)
    return value if value > EPS else EPS


def metric_from_sse(base_sse: float, full_sse: float, target_tss: float, n: int) -> dict[str, float]:
    safe_base = max(base_sse, EPS)
    safe_full = max(full_sse, EPS)
    delta_logpd = 0.5 * n * math.log(safe_base / safe_full)
    added_k = 18
    dl_cost = 0.5 * added_k * math.log(max(2, n)) + math.log(len(LAG_GRID))
    return {
        "delta_r2": (base_sse - full_sse) / target_tss,
        "delta_logpd": delta_logpd,
        "delta_dl": delta_logpd - dl_cost,
        "dl_complexity_cost": dl_cost,
    }


def evaluate_targets(
    target_values: dict[str, list[float]],
    folds: list[FoldDesign],
    matrices: dict[int | str, list[list[float]]],
    base_predictions: dict[str, list[float]] | None = None,
    prepared_by_lag: dict[int, list[FoldAddon]] | None = None,
) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    prepared = prepared_by_lag if prepared_by_lag is not None else prepare_m1_addons(folds, matrices)
    for target_name in TARGETS:
        y = target_values[target_name]
        base_preds = base_predictions[target_name] if base_predictions is not None else cv_predict_base(y, folds)
        base_sse = sse(y, base_preds)
        full_preds, lag_info = cv_predict_m1_prepared(y, folds, prepared)
        full_sse = sse(y, full_preds)
        metrics = metric_from_sse(base_sse, full_sse, tss(y), len(y))
        out[target_name] = {
            **metrics,
            "m0_sse": base_sse,
            "m1_sse": full_sse,
            "selected_lag": lag_info,
            "m0_predictions": base_preds,
            "m1_predictions": full_preds,
        }
    return out


def placement_shuffle_pack(row: GeneRow, trial: int) -> dict[int | str, list[float]]:
    n = len(row.codons)
    out_codons = list(row.codons)
    positions_by_aa: dict[str, list[int]] = {}
    codons_by_aa: dict[str, list[str]] = {}
    for i, aa in enumerate(row.aa_by_pos):
        positions_by_aa.setdefault(aa, []).append(i)
        codons_by_aa.setdefault(aa, []).append(row.codons[i])
    for aa in sorted(positions_by_aa):
        positions = positions_by_aa[aa]
        values = list(codons_by_aa[aa])
        perm = deterministic_permutation(list(range(len(values))), f"{SEED}|placement|trial={trial}|gene={row.gene}|aa={aa}")
        for local_dest, local_src in enumerate(perm):
            out_codons[positions[local_dest]] = values[local_src]
    q_by_observed = {codon: q for codon, q in zip(row.codons, row.q_stream)}
    q_stream = [q_by_observed[codon] for codon in out_codons]
    if len(q_stream) != n:
        raise ValueError("placement shuffle changed length")
    return feature_pack_from_q_and_weights(q_stream, row.low_high_weights, row.boundary_weights_cached, False)


def profile_permutation_indices(rows: list[GeneRow], trial: int) -> list[int]:
    lengths = [float(row.controls["aligned_residues"]) for row in rows]
    means = [float(row.controls["mean_plddt"]) for row in rows]
    lows = [float(row.controls["low_frac"]) for row in rows]
    aa_pc1 = aa_pc1_scores(rows)
    len_cuts = quantile_cuts(lengths, 4)
    mean_cuts = quantile_cuts(means, 3)
    low_cuts = quantile_cuts(lows, 3)
    aa_cuts = quantile_cuts(aa_pc1, 2)
    bins: dict[tuple[int, int, int, int], list[int]] = {}
    for i in range(len(rows)):
        key = (bin_index(lengths[i], len_cuts), bin_index(means[i], mean_cuts), bin_index(lows[i], low_cuts), bin_index(aa_pc1[i], aa_cuts))
        bins.setdefault(key, []).append(i)
    mapping = list(range(len(rows)))
    for key, indices in sorted(bins.items()):
        if len(indices) < 2:
            continue
        perm = deterministic_permutation(indices, f"{SEED}|profile|trial={trial}|bin={key}")
        for dest, src in zip(indices, perm):
            mapping[dest] = src
    return mapping


def plddt_profile_permutation_packs(rows: list[GeneRow], trial: int) -> list[dict[int | str, list[float]]]:
    mapping = profile_permutation_indices(rows, trial)
    packs: list[dict[int | str, list[float]]] = []
    for i, src in enumerate(mapping):
        packs.append(feature_pack_from_q_and_weights(rows[i].q_stream, rows[src].low_high_weights, rows[src].boundary_weights_cached, False))
    return packs


def circular_shift_pack(row: GeneRow, trial: int) -> dict[int | str, list[float]]:
    n = len(row.q_stream)
    offset = stable_offset(n, f"{SEED}|circular-shift|trial={trial}|gene={row.gene}")
    shifted = [row.q_stream[(i - offset) % n] for i in range(n)]
    return feature_pack_from_q_and_weights(shifted, row.low_high_weights, row.boundary_weights_cached, False)


def quantile_cuts(values: list[float], bin_count: int) -> list[float]:
    if not values or bin_count <= 1:
        return []
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


def aa_pc1_scores(rows: list[GeneRow]) -> list[float]:
    aa = [list(row.controls["aa"]) for row in rows]  # type: ignore[arg-type]
    indices = list(range(len(rows)))
    aa_std, _ = standardize_train_apply(aa, indices, [])
    pcs = top_pcs(aa_std, 1)
    if not pcs:
        return [0.0 for _ in rows]
    return [vector_dot(row, pcs[0]) for row in aa_std]


def composition_bin_permute_matrices(
    observed: dict[int | str, list[list[float]]],
    rows: list[GeneRow],
    trial: int,
) -> dict[int | str, list[list[float]]]:
    log_len = [float(row.controls["log_len"]) for row in rows]
    gc3 = [float(row.controls["gc3"]) for row in rows]
    abundance = [float(row.controls["abundance"]) for row in rows]
    aa_pc1 = aa_pc1_scores(rows)
    len_cuts = quantile_cuts(log_len, 3)
    gc_cuts = quantile_cuts(gc3, 3)
    abundance_cuts = quantile_cuts(abundance, 3)
    aa_cuts = quantile_cuts(aa_pc1, 2)
    bins: dict[tuple[int, int, int, int], list[int]] = {}
    for i in range(len(rows)):
        key = (bin_index(log_len[i], len_cuts), bin_index(gc3[i], gc_cuts), bin_index(abundance[i], abundance_cuts), bin_index(aa_pc1[i], aa_cuts))
        bins.setdefault(key, []).append(i)
    mapping = list(range(len(rows)))
    for key, indices in sorted(bins.items()):
        if len(indices) < 2:
            continue
        perm = deterministic_permutation(indices, f"{SEED}|composition-q|trial={trial}|bin={key}")
        for dest, src in zip(indices, perm):
            mapping[dest] = src
    out: dict[int | str, list[list[float]]] = {}
    for key, matrix in observed.items():
        out[key] = [list(matrix[mapping[i]]) for i in range(len(rows))]
    return out


def summarize_null_metric(values: list[float]) -> dict[str, float]:
    return {
        "null95": percentile_nearest_rank(values, 0.95),
        "mean": mean(values),
        "min": min(values) if values else 0.0,
        "max": max(values) if values else 0.0,
    }


def collect_nulls(
    rows: list[GeneRow],
    folds: list[FoldDesign],
    target_values: dict[str, list[float]],
    observed_matrices: dict[int | str, list[list[float]]],
    base_predictions: dict[str, list[float]],
) -> dict[str, object]:
    null_values: dict[str, dict[str, dict[str, list[float]]]] = {
        name: {target: {"delta_r2": [], "delta_logpd": [], "delta_dl": []} for target in TARGETS}
        for name in ("placement_shuffle", "plddt_profile_permutation", "circular_shift", "composition_bin_q_permutation")
    }
    for trial in range(ACTUAL_B):
        placement = raw_feature_matrices([placement_shuffle_pack(row, trial) for row in rows])
        profile = raw_feature_matrices(plddt_profile_permutation_packs(rows, trial))
        shifted = raw_feature_matrices([circular_shift_pack(row, trial) for row in rows])
        comp = composition_bin_permute_matrices(observed_matrices, rows, trial)
        for null_name, matrices in (
            ("placement_shuffle", placement),
            ("plddt_profile_permutation", profile),
            ("circular_shift", shifted),
            ("composition_bin_q_permutation", comp),
        ):
            prepared = prepare_m1_addons(folds, matrices)
            evaluated = evaluate_targets(target_values, folds, matrices, base_predictions, prepared)
            for target in TARGETS:
                for metric in ("delta_r2", "delta_logpd", "delta_dl"):
                    null_values[null_name][target][metric].append(float(evaluated[target][metric]))
    summary: dict[str, dict[str, dict[str, dict[str, float]]]] = {}
    for null_name in null_values:
        summary[null_name] = {}
        for target in TARGETS:
            summary[null_name][target] = {}
            for metric in ("delta_r2", "delta_logpd", "delta_dl"):
                summary[null_name][target][metric] = summarize_null_metric(null_values[null_name][target][metric])
    return {"actual_B": ACTUAL_B, "summary": summary}


def cv_contribution(
    target: list[float],
    folds: list[FoldDesign],
    matrices: dict[int | str, list[list[float]]],
) -> tuple[list[float], list[float], list[float]]:
    base_preds = cv_predict_base(target, folds)
    full_preds, _lag_info = cv_predict_m1(target, folds, matrices)
    struct = [full_preds[i] - base_preds[i] for i in range(len(target))]
    return base_preds, full_preds, struct


def cv_predict_with_extra(target: list[float], folds: list[FoldDesign], extra: list[list[float]]) -> list[float]:
    preds = [0.0 for _ in target]
    for fold in folds:
        addon = prepare_fold_addon(fold, extra)
        _train_sse, _beta, fold_preds = fit_predict_prepared(target, fold, addon)
        for local, pred in enumerate(fold_preds):
            preds[fold.test[local]] = pred
    return preds


def secondary_bridge(
    rows: list[GeneRow],
    matrices: dict[int | str, list[list[float]]],
    execution_folds: list[FoldDesign],
    p_folds: list[FoldDesign],
    target_values: dict[str, list[float]],
) -> dict[str, object]:
    p_target = [row.p for row in rows]
    qglobal = [list(row.controls["qglobal"]) for row in rows]  # type: ignore[arg-type]
    base_exec_contrib: dict[str, list[float]] = {}
    struct_contrib: dict[str, list[float]] = {}
    for target in TARGETS:
        y = target_values[target]
        c_preds = cv_predict_base(y, execution_folds)
        cq_preds = cv_predict_with_extra(y, execution_folds, qglobal)
        _m0, _m1, struct = cv_contribution(y, execution_folds, matrices)
        base_exec_contrib[target] = [cq_preds[i] - c_preds[i] for i in range(len(y))]
        struct_contrib[target] = struct
    base_extra = [
        list(qglobal[i]) + [base_exec_contrib["logTE"][i], base_exec_contrib["log_mrna_half_life"][i]]
        for i in range(len(rows))
    ]
    base_preds_p = cv_predict_with_extra(p_target, p_folds, base_extra)
    base_sse_p = sse(p_target, base_preds_p)
    out: dict[str, object] = {}
    for target in TARGETS:
        full_extra = [base_extra[i] + [struct_contrib[target][i]] for i in range(len(rows))]
        full_preds_p = cv_predict_with_extra(p_target, p_folds, full_extra)
        full_sse_p = sse(p_target, full_preds_p)
        metrics = metric_from_sse(base_sse_p, full_sse_p, tss(p_target), len(p_target))
        out[target] = {
            "increment_delta_r2": metrics["delta_r2"],
            "increment_delta_logpd": metrics["delta_logpd"],
            "increment_delta_dl": metrics["delta_dl"],
            "base_p_sse": base_sse_p,
            "full_p_sse": full_sse_p,
        }
    return {
        "status": "computed",
        "method": "out-of-fold P models exclude abundance from C to avoid target leakage; execution mediators are out-of-fold contributions",
        "by_target_struct_slot": out,
    }


def checks(
    rows: list[GeneRow],
    observed: dict[str, dict[str, object]],
    nulls: dict[str, object],
    bridge: dict[str, object],
    conclusion: str,
) -> list[dict[str, object]]:
    null_summary = nulls.get("summary")
    placement_ok = isinstance(null_summary, dict) and "placement_shuffle" in null_summary and int(nulls.get("actual_B", 0)) >= 100
    return [
        {"name": "q9_and_plddt_aligned", "passed": bool(rows) and min(int(row.controls["aligned_residues"]) for row in rows) > 0, "detail": "codon i aligned to residue i; stop codon excluded by min(len(codons)-1,len(plddt))"},
        {"name": "position_weighted_gated_q", "passed": all(key in rows[0].pack for key in ("low_minus_high", 0, 20, 40, "qglobal")) if rows else False, "detail": "low/high/boundary features computed from per-codon q9 stream and per-residue pLDDT"},
        {"name": "target_certified_slots", "passed": all(target in observed for target in TARGETS), "detail": "targets are log TE and log mRNA half-life, not P"},
        {"name": "m0_m1_heldout", "passed": all("delta_r2" in observed[target] and "delta_logpd" in observed[target] for target in TARGETS), "detail": "gene-level 5-fold held-out ridge"},
        {"name": "dl_with_lag_cost", "passed": all("delta_dl" in observed[target] and "dl_complexity_cost" in observed[target] for target in TARGETS), "detail": "DL subtracts BIC-style 18-feature cost plus log(3) lag choice cost"},
        {"name": "four_class_nulls_placement_key", "passed": placement_ok, "detail": "placement shuffle permutes synonymous codon placement within same gene and amino-acid fiber"},
        {"name": "secondary_p_bridge", "passed": bridge.get("status") == "computed", "detail": "OOF P bridge computed without in-sample execution mediators"},
        {"name": "structure_gating_verdict", "passed": conclusion in {"structure_conditioned_placement_grammar", "execution_gene_level_only"}, "detail": conclusion},
    ]


def verdicts_by_target(observed: dict[str, dict[str, object]], nulls: dict[str, object]) -> dict[str, dict[str, object]]:
    summary = nulls["summary"]
    out: dict[str, dict[str, object]] = {}
    for target in TARGETS:
        obs_r2 = float(observed[target]["delta_r2"])
        obs_logpd = float(observed[target]["delta_logpd"])
        obs_dl = float(observed[target]["delta_dl"])
        null95_r2 = {name: float(summary[name][target]["delta_r2"]["null95"]) for name in summary}
        null95_logpd = {name: float(summary[name][target]["delta_logpd"]["null95"]) for name in summary}
        exceeds_r2 = all(obs_r2 > value for value in null95_r2.values())
        exceeds_logpd = all(obs_logpd > value for value in null95_logpd.values())
        placement_exceeded = obs_r2 > null95_r2["placement_shuffle"] and obs_logpd > null95_logpd["placement_shuffle"]
        positive = exceeds_r2 and exceeds_logpd and obs_dl > 0.0 and placement_exceeded
        out[target] = {
            "positive": positive,
            "verdict": "positive" if positive else "negative",
            "observed_delta_r2": obs_r2,
            "observed_delta_logpd": obs_logpd,
            "observed_delta_dl": obs_dl,
            "null95_delta_r2": null95_r2,
            "null95_delta_logpd": null95_logpd,
            "placement_shuffle_exceeded": placement_exceeded,
        }
    return out


def compact_observed(observed: dict[str, dict[str, object]]) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for target in TARGETS:
        out[target] = {
            "delta_r2": observed[target]["delta_r2"],
            "delta_logpd": observed[target]["delta_logpd"],
            "delta_dl": observed[target]["delta_dl"],
            "dl_complexity_cost": observed[target]["dl_complexity_cost"],
            "selected_lag": observed[target]["selected_lag"],
            "m0_sse": observed[target]["m0_sse"],
            "m1_sse": observed[target]["m1_sse"],
        }
    return out


def main() -> None:
    started = time.time()
    repo = pathlib.Path.cwd()
    if not (repo / "tools/bio_reality/data").exists():
        repo = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath")
    built = build_rows(repo)
    rows = built["rows"]
    if not isinstance(rows, list) or len(rows) < 200:
        emit("needs_data", reason="insufficient joined genes", source_counts=built.get("source_counts"), skipped=built.get("skipped"))
    target_values = {target: [row.targets[target] for row in rows] for target in TARGETS}
    folds_with_abundance = build_fold_designs(rows, include_abundance=True)
    folds_no_abundance = build_fold_designs(rows, include_abundance=False)
    observed_matrices = raw_feature_matrices([row.pack for row in rows])
    base_predictions = {target: cv_predict_base(target_values[target], folds_with_abundance) for target in TARGETS}
    observed_full = evaluate_targets(target_values, folds_with_abundance, observed_matrices, base_predictions)
    nulls = collect_nulls(rows, folds_with_abundance, target_values, observed_matrices, base_predictions)
    bridge = secondary_bridge(rows, observed_matrices, folds_no_abundance, folds_no_abundance, target_values)
    per_target_verdict = verdicts_by_target(observed_full, nulls)
    conclusion = "structure_conditioned_placement_grammar" if any(per_target_verdict[target]["positive"] for target in TARGETS) else "execution_gene_level_only"
    check_rows = checks(rows, observed_full, nulls, bridge, conclusion)
    status = "passed" if all(bool(item["passed"]) for item in check_rows) else "failed"
    plddt_lengths = [int(row.controls["aligned_residues"]) for row in rows]
    payload = {
        "organism": ORGANISM,
        "n_genes": len(rows),
        "source_counts": built["source_counts"],
        "skipped": built["skipped"],
        "q_names": built["context"]["q_names"],
        "feature_definition": {
            "q_event": "9D B*_Q6 synonymous-fiber projected codon event, normalized by coordinate norm; DNA codon i aligned to residue i",
            "position_weighting": "Qglobal=sum(q_i)/n; Qlow=sum((1-s_i)q_i)/n; Qhigh=sum(s_i q_i)/n; Qboundary_lag=sum(b_i q_{i-L})/n",
            "low_minus_high": "M1 uses Qlow-Qhigh plus one train-fold-selected boundary lag in {0,20,40}",
            "boundary_proxy": f"absolute gradient of moving-average pLDDT/100, window={SMOOTH_WINDOW}",
        },
        "cv": {"fold_count": FOLD_COUNT, "ridge_lambda": RIDGE, "lambda_selection": "fixed pre-registered; no held-out leakage", "lag_selection": "outer-train-fold train SSE only"},
        "observed": compact_observed(observed_full),
        "nulls": nulls,
        "per_target_verdict": per_target_verdict,
        "secondary_bridge": bridge,
        "final_conclusion": conclusion,
        "actual_B": ACTUAL_B,
        "alignment_summary": {
            "min_aligned_residues": min(plddt_lengths),
            "median_aligned_residues": percentile_nearest_rank([float(x) for x in plddt_lengths], 0.5),
            "max_aligned_residues": max(plddt_lengths),
        },
        "cannot_claim": [
            "pLDDT is predicted confidence/order proxy, not experimental disorder or structure dynamics",
            "TE and mRNA half-life bridge is mediation-style association, not causal identification",
            "boundary and disorder weights are proxies and may differ across conditions",
            "negative result means this protocol did not certify structure-conditioned placement beyond gene-level execution controls",
        ],
        "checks": check_rows,
        "runtime_sec": round(time.time() - started, 3),
    }
    emit(status, **payload)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        emit("failed", error=type(exc).__name__, message=str(exc))

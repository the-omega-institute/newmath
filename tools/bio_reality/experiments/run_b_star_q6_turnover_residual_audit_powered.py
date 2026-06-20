#!/usr/bin/env python3
"""B*_Q6 measured protein-turnover residual audit for S. cerevisiae.

Pure-stdlib, single-file experiment.  Outcome is measured Christiano/SGD
protein half-life converted to log degradation rate: log(ln(2) / t_half).
"""

from __future__ import annotations

import hashlib
import multiprocessing
import json
import math
import os
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_q6_turnover_residual_audit_powered"
CLAIM_ID = "h3.cross_layer_relation.proteostasis_turnover_residual.b_star_q6_turnover_residual_audit_powered"

FOLD_COUNT = 5
TARGET_NULL_B = 200
RIDGE_C = 1e-6
RIDGE_B = 1e-6
EPS = 1e-12
SEED = "sha256:b_star_q6_turnover_residual_audit_powered:deterministic"
DATA_REL = pathlib.Path("tools/bio_reality/data")

G_B_MATRIX: list[list[float]] = []
G_Y: list[float] = []
G_FOLDS: list["FoldCache"] = []
G_KEYS: list[tuple[int, ...]] = []
G_RECODER: dict[str, object] = {}
G_CONTEXT: dict[str, object] = {}

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


def emit(status: str, **kwargs: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kwargs)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


def load_json(path: pathlib.Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def positive_log(value: object) -> float | None:
    if not finite_number(value):
        return None
    number = float(value)
    if number <= 0.0:
        return None
    return math.log(number)


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
        digest = stable_digest(f"{material}|i={index}|n={len(out)}")
        swap = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [dot(row, vector) for row in matrix]


def cholesky_decompose(matrix: list[list[float]]) -> list[list[float]]:
    n = len(matrix)
    lower = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            value = matrix[i][j] - sum(lower[i][k] * lower[j][k] for k in range(j))
            if i == j:
                if value <= EPS:
                    value = EPS
                lower[i][j] = math.sqrt(value)
            else:
                lower[i][j] = value / lower[j][j]
    return lower


def cholesky_solve(lower: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    y = [0.0 for _ in range(n)]
    for i in range(n):
        y[i] = (rhs[i] - sum(lower[i][k] * y[k] for k in range(i))) / lower[i][i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - sum(lower[k][i] * x[k] for k in range(i + 1, n))) / lower[i][i]
    return x


def ridge_gram_cholesky(rows: list[list[float]], ridge: float) -> list[list[float]]:
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
        if i != 0:
            gram[i][i] += ridge
        else:
            gram[i][i] += ridge * 0.01
    return cholesky_decompose(gram)


def xty(rows: list[list[float]], target: list[float]) -> list[float]:
    width = len(rows[0])
    out = [0.0 for _ in range(width)]
    for row, y in zip(rows, target):
        for i in range(width):
            out[i] += row[i] * y
    return out


def ridge_fit(rows: list[list[float]], target: list[float], ridge: float) -> list[float]:
    return cholesky_solve(ridge_gram_cholesky(rows, ridge), xty(rows, target))


def predict(rows: list[list[float]], beta: list[float]) -> list[float]:
    return [dot(row, beta) for row in rows]


def sse(y: list[float], yhat: list[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(y, yhat))


def tss(y: list[float]) -> float:
    center = mean(y)
    return max(EPS, sum((value - center) ** 2 for value in y))


def delta_dl_bits(sse_base: float, sse_full: float, n: int) -> float:
    return 0.5 * n * math.log(max(sse_base, EPS) / max(sse_full, EPS), 2.0)


def standardize_train_apply(
    raw: list[list[float | None]],
    train: list[int],
    test: list[int],
) -> tuple[list[list[float]], list[list[float]], list[dict[str, float]]]:
    width = len(raw[0])
    stats: list[dict[str, float]] = []
    for col in range(width):
        values = [float(raw[i][col]) for i in train if raw[i][col] is not None and math.isfinite(float(raw[i][col]))]
        center = mean(values) if values else 0.0
        sd = math.sqrt(variance(values)) if values else 1.0
        if sd <= EPS:
            sd = 1.0
        stats.append({"mean": center, "sd": sd})

    def one(index: int) -> list[float]:
        out = []
        for col, stat in enumerate(stats):
            value = raw[index][col]
            number = stat["mean"] if value is None or not math.isfinite(float(value)) else float(value)
            out.append((number - stat["mean"]) / stat["sd"])
        return out

    return [one(i) for i in train], [one(i) for i in test], stats


def add_intercept(rows: list[list[float]]) -> list[list[float]]:
    return [[1.0] + row for row in rows]


def covariance(matrix: list[list[float]]) -> list[list[float]]:
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


def top_pcs(standardized: list[list[float]], k: int) -> list[list[float]]:
    if not standardized:
        return []
    width = len(standardized[0])
    cov = covariance(standardized)
    pcs: list[list[float]] = []
    for pc_index in range(min(k, width)):
        vec = normalize_vector([
            ((int.from_bytes(stable_digest(f"{SEED}|pc|{pc_index}|{i}")[:4], "big") % 2001) - 1000) / 1000.0
            for i in range(width)
        ])
        for _ in range(100):
            nxt = mat_vec(cov, vec)
            for prev in pcs:
                coeff = dot(nxt, prev)
                for i in range(width):
                    nxt[i] -= coeff * prev[i]
            nxt = normalize_vector(nxt)
            if sum(abs(nxt[i] - vec[i]) for i in range(width)) < 1e-11:
                vec = nxt
                break
            vec = nxt
        if math.sqrt(sum(value * value for value in vec)) <= EPS:
            break
        pcs.append(vec)
        eigen = dot(vec, mat_vec(cov, vec))
        for i in range(width):
            for j in range(width):
                cov[i][j] -= eigen * vec[i] * vec[j]
    return pcs


def project_pcs(rows: list[list[float]], pcs: list[list[float]]) -> list[list[float]]:
    return [[dot(row, pc) for pc in pcs] for row in rows]


def standard_code(data_dir: pathlib.Path) -> dict[str, str]:
    raw = load_json(data_dir / "ncbi_genetic_codes.json")
    table = next(item for item in raw["tables"] if item.get("table_id") == 1)
    return {str(codon): aa for codon, aa in zip(raw["codon_order"], table["aa"])}


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for codon in codons:
        out.setdefault(code[codon], []).append(codon)
    return out


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


def q6_context(data_dir: pathlib.Path) -> dict[str, object]:
    code = standard_code(data_dir)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    aa_order = sorted({code[codon] for codon in codons})
    return {"code": code, "codons": codons, "fibers": fibers, "aa_order": aa_order, "q_projected": projected, "q_names": list(projected)}


def codon_counts_from_sequence(sequence: list[str], codons: list[str]) -> dict[str, int]:
    out = {codon: 0 for codon in codons}
    for raw in sequence:
        codon = dna_to_rna(raw)
        if codon in out:
            out[codon] += 1
    return out


def q_row_from_counts(counts: dict[str, int], context: dict[str, object]) -> list[float]:
    codons = context["codons"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    assert isinstance(codons, list) and isinstance(q_projected, dict) and isinstance(q_names, list)
    total = sum(counts[str(codon)] for codon in codons)
    if total <= 0:
        raise ValueError("empty sense codon counts")
    row: list[float] = []
    for name in q_names:
        q = q_projected[str(name)]
        assert isinstance(q, dict)
        denom = math.sqrt(sum(float(q[str(codon)]) ** 2 for codon in codons))
        row.append(sum((counts[str(codon)] / total) * float(q[str(codon)]) for codon in codons) / denom)
    return row


def load_ordered_cds(data_dir: pathlib.Path) -> dict[str, list[str]]:
    payload = load_json(data_dir / "cds_ordered_sequences_saccharomyces_cerevisiae.json")
    out: dict[str, list[str]] = {}
    for item in payload.get("cds", []):
        if isinstance(item, dict) and isinstance(item.get("gene_id"), str) and isinstance(item.get("codons"), list):
            out[str(item["gene_id"])] = [str(c).upper() for c in item["codons"]]
    return out


def load_turnover_y(data_dir: pathlib.Path) -> dict[str, float]:
    payload = load_json(data_dir / "protein_turnover_saccharomyces_cerevisiae.json")
    raw = payload.get("protein_turnover")
    if not isinstance(raw, dict):
        raise ValueError("protein_turnover payload missing protein_turnover object")
    out: dict[str, float] = {}
    for key, value in raw.items():
        if str(key).startswith("4932.") and finite_number(value) and float(value) > 0.0:
            gene = str(key).split(".", 1)[1]
            out[gene] = math.log(math.log(2.0) / float(value))
    return out


def load_abundance(data_dir: pathlib.Path) -> dict[str, float]:
    payload = load_json(data_dir / "proteomics_abundance_saccharomyces_cerevisiae.json")
    raw = payload.get("protein_abundance")
    out: dict[str, float] = {}
    if isinstance(raw, dict):
        for key, value in raw.items():
            logged = positive_log(value)
            if logged is not None and str(key).startswith("4932."):
                out[str(key).split(".", 1)[1]] = logged
    return out


def load_te(data_dir: pathlib.Path) -> dict[str, dict[str, float]]:
    payload = load_json(data_dir / "ribosome_te_saccharomyces_cerevisiae.json")
    out: dict[str, dict[str, float]] = {}
    for item in payload.get("genes", []):
        if not isinstance(item, dict) or not isinstance(item.get("gene_key"), str):
            continue
        log_te = positive_log(item.get("te"))
        log_m = positive_log(item.get("mrna"))
        log_rpf = positive_log(item.get("footprint"))
        if log_te is not None and log_m is not None and log_rpf is not None:
            out[str(item["gene_key"])] = {"logTE_Estat": log_te, "logM": log_m, "logRPF": log_rpf}
    return out


def load_mrna_half_life(data_dir: pathlib.Path) -> tuple[dict[str, float], dict[str, str]]:
    payload = load_json(data_dir / "mrna_half_life_saccharomyces_cerevisiae_neymotin.json")
    out: dict[str, float] = {}
    symbols: dict[str, str] = {}
    for item in payload.get("records", []):
        if not isinstance(item, dict) or not isinstance(item.get("Syst"), str):
            continue
        gene = str(item["Syst"])
        logged = positive_log(item.get("thalf"))
        if logged is not None:
            out[gene] = logged
        if isinstance(item.get("Gene"), str):
            symbols[gene] = str(item["Gene"])
    return out, symbols


def load_plddt(data_dir: pathlib.Path) -> dict[str, dict[str, float]]:
    out: dict[str, dict[str, float]] = {}
    per_path = data_dir / "structural_order_per_residue_saccharomyces_cerevisiae.json"
    if per_path.exists():
        payload = load_json(per_path)
        raw = payload.get("per_residue_plddt") if isinstance(payload, dict) else None
        if isinstance(raw, dict):
            for gene, values in raw.items():
                if isinstance(values, list):
                    vals = [float(v) for v in values if finite_number(v)]
                    if vals:
                        out[str(gene)] = {"plddt_mean": mean(vals), "plddt_low_frac": sum(1 for v in vals if v < 70.0) / len(vals)}
    if out:
        return out
    payload = load_json(data_dir / "structural_order_saccharomyces_cerevisiae.json")
    for item in payload.get("proteins", []):
        if isinstance(item, dict) and isinstance(item.get("protein_id"), str) and finite_number(item.get("structural_order")):
            pid = str(item["protein_id"])
            if pid.startswith("4932."):
                out[pid.split(".", 1)[1]] = {"plddt_mean": float(item["structural_order"]), "plddt_low_frac": 0.0}
    return out


def load_localization(data_dir: pathlib.Path) -> dict[str, dict[str, object]]:
    path = data_dir / "subcellular_localization_saccharomyces_cerevisiae.json"
    if not path.exists():
        return {}
    payload = load_json(path)
    proteins = payload.get("proteins")
    out: dict[str, dict[str, object]] = {}
    if isinstance(proteins, dict):
        for pid, item in proteins.items():
            if str(pid).startswith("4932.") and isinstance(item, dict):
                out[str(pid).split(".", 1)[1]] = item
    return out


def load_essentiality(data_dir: pathlib.Path) -> dict[str, float]:
    path = data_dir / "gene_essentiality_saccharomyces_cerevisiae.json"
    if not path.exists():
        return {}
    payload = load_json(path)
    out: dict[str, float] = {}
    for item in payload.get("genes", []):
        if isinstance(item, dict) and isinstance(item.get("gene_key"), str) and finite_number(item.get("essential")):
            out[str(item["gene_key"])] = float(item["essential"])
    return out


def aa_composition_and_gc3(counts: dict[str, int], context: dict[str, object]) -> tuple[list[float], float]:
    codons = context["codons"]
    code = context["code"]
    aa_order = context["aa_order"]
    assert isinstance(codons, list) and isinstance(code, dict) and isinstance(aa_order, list)
    aa_counts = {str(aa): 0 for aa in aa_order}
    total = 0
    for codon in codons:
        c = counts[str(codon)]
        aa_counts[str(code[str(codon)])] += c
        total += c
    if total <= 0:
        raise ValueError("empty sense counts")
    aa = [aa_counts[str(a)] / total for a in aa_order]
    gc3 = sum(counts[str(codon)] for codon in codons if str(codon)[2] in {"G", "C"}) / total
    return aa, gc3


def nend_onehot(sequence: list[str], context: dict[str, object]) -> list[float]:
    code = context["code"]
    aa_order = context["aa_order"]
    assert isinstance(code, dict) and isinstance(aa_order, list)
    aas = [str(code[dna_to_rna(codon)]) for codon in sequence if dna_to_rna(codon) in code and code[dna_to_rna(codon)] != "*"]
    residue = aas[1] if len(aas) > 1 and aas[0] == "M" else (aas[0] if aas else None)
    return [1.0 if residue == aa else 0.0 for aa in aa_order]


def build_dataset(repo: pathlib.Path) -> dict[str, object]:
    data_dir = repo / DATA_REL
    context = q6_context(data_dir)
    cds = load_ordered_cds(data_dir)
    turnover_y = load_turnover_y(data_dir)
    abundance = load_abundance(data_dir)
    te = load_te(data_dir)
    mrna_hl, symbols = load_mrna_half_life(data_dir)
    plddt = load_plddt(data_dir)
    localization = load_localization(data_dir)
    essentiality = load_essentiality(data_dir)

    loc_categories = ["Cell_membrane", "Cytoplasm", "Cytoskeleton", "Endoplasmic_reticulum", "Golgi", "Membrane", "Mitochondrion", "Nucleus", "Peroxisome", "Secreted", "Vacuole_Lysosome", "Other"]
    control_names = (
        ["logL"]
        + [f"AA_{aa}" for aa in context["aa_order"]]  # type: ignore[index]
        + ["GC3"]
        + [f"Nend_{aa}" for aa in context["aa_order"]]  # type: ignore[index]
        + ["mean_pLDDT", "low_pLDDT_fraction", "pLDDT_missing", "logM", "logRPF", "logP", "E_stat_logTE", "mRNA_HL"]
        + [f"loc_{cat}" for cat in loc_categories]
        + ["loc_missing", "essentiality", "essentiality_missing"]
    )

    active = sorted(set(cds) & set(turnover_y) & set(abundance) & set(te) & set(mrna_hl))
    rows: list[dict[str, object]] = []
    controls: list[list[float | None]] = []
    q_rows: list[list[float]] = []
    y: list[float] = []
    bin_axes: list[list[float | None]] = []
    bin_axis_names = ["E_stat_logTE", "logP", "logM", "logRPF", "mRNA_HL", "logL", "GC3", "AA20_PC1", "mean_pLDDT", "low_pLDDT_fraction"]
    aa_rows: list[list[float]] = []

    for gene in active:
        sequence = cds[gene]
        counts = codon_counts_from_sequence(sequence, context["codons"])  # type: ignore[arg-type]
        if sum(counts.values()) <= 0:
            continue
        aa_comp, gc3 = aa_composition_and_gc3(counts, context)
        aa_rows.append(aa_comp)

    aa_indices = list(range(len(aa_rows)))
    aa_std, _, _ = standardize_train_apply([[v for v in row] for row in aa_rows], aa_indices, [])
    aa_pcs = top_pcs(aa_std, 1)
    aa_pc_values = [dot(row, aa_pcs[0]) if aa_pcs else 0.0 for row in aa_std]
    aa_pc_by_gene: dict[str, float] = {}
    aa_counter = 0

    for gene in active:
        sequence = cds[gene]
        counts = codon_counts_from_sequence(sequence, context["codons"])  # type: ignore[arg-type]
        if sum(counts.values()) <= 0:
            continue
        aa_comp, gc3 = aa_composition_and_gc3(counts, context)
        pld = plddt.get(gene)
        loc = localization.get(gene)
        loc_values = set(str(x) for x in loc.get("categories", [])) if isinstance(loc, dict) and isinstance(loc.get("categories"), list) else set()
        loc_raw = str(loc.get("raw_subcellular_location", "")) if isinstance(loc, dict) else ""
        loc_missing = 0.0 if loc_values else 1.0
        ess = essentiality.get(gene)
        log_l = math.log(max(1, sum(counts.values())))
        control = (
            [log_l]
            + aa_comp
            + [gc3]
            + nend_onehot(sequence, context)
            + [
                None if pld is None else float(pld["plddt_mean"]),
                None if pld is None else float(pld["plddt_low_frac"]),
                1.0 if pld is None else 0.0,
                te[gene]["logM"],
                te[gene]["logRPF"],
                abundance[gene],
                te[gene]["logTE_Estat"],
                mrna_hl[gene],
            ]
            + [1.0 if cat in loc_values else 0.0 for cat in loc_categories]
            + [loc_missing, ess, 1.0 if ess is None else 0.0]
        )
        controls.append(control)
        q_rows.append(q_row_from_counts(counts, context))
        y.append(turnover_y[gene])
        aa_pc = aa_pc_values[aa_counter]
        aa_pc_by_gene[gene] = aa_pc
        aa_counter += 1
        symbol = symbols.get(gene, "")
        upper_symbol = symbol.upper()
        is_ribo = (
            upper_symbol.startswith(("RPL", "RPS", "MRP", "MRPL", "MRPS"))
            or "RIBOSOM" in loc_raw.upper()
        )
        is_mito = "Mitochondrion" in loc_values or "MITOCHONDR" in loc_raw.upper()
        is_membrane = bool({"Membrane", "Cell_membrane"} & loc_values) or "MEMBRANE" in loc_raw.upper()
        rows.append({
            "gene": gene,
            "sequence": sequence,
            "counts": counts,
            "symbol": symbol,
            "ribosomal": is_ribo,
            "mitochondrial": is_mito,
            "membrane": is_membrane,
            "gc3": gc3,
            "logL": log_l,
            "aa_pc1": aa_pc,
        })
        bin_axes.append([
            te[gene]["logTE_Estat"],
            abundance[gene],
            te[gene]["logM"],
            te[gene]["logRPF"],
            mrna_hl[gene],
            log_l,
            gc3,
            aa_pc,
            None if pld is None else float(pld["plddt_mean"]),
            None if pld is None else float(pld["plddt_low_frac"]),
        ])

    source_counts = {
        "cds": len(cds),
        "protein_turnover_half_life": len(turnover_y),
        "ribosome_te": len(te),
        "proteomics_abundance": len(abundance),
        "mrna_half_life": len(mrna_hl),
        "plddt": len(plddt),
        "localization": len(localization),
        "essentiality": len(essentiality),
    }
    controls_available = [
        "logL", "AA20_composition", "GC3", "N_end_residue_after_Met", "mean_pLDDT", "low_pLDDT_fraction",
        "logM", "logRPF", "logP", "E_stat_logTE", "mRNA_HL", "localization_onehot", "membrane_via_localization", "essentiality",
    ]
    controls_missing = ["complex_membership"]
    return {
        "genes": [str(row["gene"]) for row in rows],
        "rows": rows,
        "controls": controls,
        "control_names": control_names,
        "q": q_rows,
        "y": y,
        "context": context,
        "source_counts": source_counts,
        "controls_available": controls_available,
        "controls_missing": controls_missing,
        "bin_axes": bin_axes,
        "bin_axis_names": bin_axis_names,
        "q_names": context["q_names"],
    }


class FoldCache:
    def __init__(self, train: list[int], test: list[int], c_train: list[list[float]], c_test: list[list[float]], y_train: list[float], y_test: list[float]) -> None:
        self.train = train
        self.test = test
        self.c_train = c_train
        self.c_test = c_test
        self.y_train = y_train
        self.y_test = y_test
        width = len(c_train[0])
        self.control_width = width
        self.c_chol = ridge_gram_cholesky(c_train, RIDGE_C)
        self.ctc = [[0.0 for _ in range(width)] for _ in range(width)]
        for row in c_train:
            for i in range(width):
                xi = row[i]
                for j in range(i, width):
                    self.ctc[i][j] += xi * row[j]
        for i in range(width):
            for j in range(i):
                self.ctc[i][j] = self.ctc[j][i]
        self.beta_l2 = cholesky_solve(self.c_chol, xty(c_train, y_train))
        self.c_inv = []
        for col in range(width):
            unit = [0.0 for _ in range(width)]
            unit[col] = 1.0
            self.c_inv.append(cholesky_solve(self.c_chol, unit))
        self.pred_l2_train = predict(c_train, self.beta_l2)
        self.pred_l2_test = predict(c_test, self.beta_l2)
        self.y_resid_train = [a - b for a, b in zip(y_train, self.pred_l2_train)]
        self.ct_y_resid = [0.0 for _ in range(width)]
        for row, value in zip(c_train, self.y_resid_train):
            for i in range(width):
                self.ct_y_resid[i] += row[i] * value


def make_folds(controls: list[list[float | None]], y: list[float], subset: list[int] | None = None) -> list[FoldCache]:
    indices = list(range(len(y))) if subset is None else list(subset)
    folds: list[FoldCache] = []
    for fold in range(FOLD_COUNT):
        test = [idx for pos, idx in enumerate(indices) if pos % FOLD_COUNT == fold]
        test_set = set(test)
        train = [idx for idx in indices if idx not in test_set]
        c_train_raw, c_test_raw, _ = standardize_train_apply(controls, train, test)
        c_train = add_intercept(c_train_raw)
        c_test = add_intercept(c_test_raw)
        folds.append(FoldCache(c_train=c_train, c_test=c_test, train=train, test=test, y_train=[y[i] for i in train], y_test=[y[i] for i in test]))
    return folds


def residualize_b_for_fold(b_matrix: list[list[float]], fold: FoldCache) -> tuple[list[list[float]], list[list[float]]]:
    width_b = len(b_matrix[0])
    raw_train = [[b_matrix[i][j] for j in range(width_b)] for i in fold.train]
    raw_test = [[b_matrix[i][j] for j in range(width_b)] for i in fold.test]
    fitted_train = [[0.0 for _ in range(width_b)] for _ in fold.train]
    fitted_test = [[0.0 for _ in range(width_b)] for _ in fold.test]
    for dim in range(width_b):
        rhs = [0.0 for _ in range(len(fold.c_train[0]))]
        for row, b_row in zip(fold.c_train, raw_train):
            value = b_row[dim]
            for k in range(len(rhs)):
                rhs[k] += row[k] * value
        beta = cholesky_solve(fold.c_chol, rhs)
        for local, row in enumerate(fold.c_train):
            fitted_train[local][dim] = dot(row, beta)
        for local, row in enumerate(fold.c_test):
            fitted_test[local][dim] = dot(row, beta)
    resid_train = [[raw_train[i][j] - fitted_train[i][j] for j in range(width_b)] for i in range(len(raw_train))]
    resid_test = [[raw_test[i][j] - fitted_test[i][j] for j in range(width_b)] for i in range(len(raw_test))]
    stats: list[tuple[float, float]] = []
    for dim in range(width_b):
        values = [row[dim] for row in resid_train]
        center = mean(values)
        sd = math.sqrt(variance(values))
        if sd <= EPS:
            sd = 1.0
        stats.append((center, sd))
    z_train = [[(row[j] - stats[j][0]) / stats[j][1] for j in range(width_b)] for row in resid_train]
    z_test = [[(row[j] - stats[j][0]) / stats[j][1] for j in range(width_b)] for row in resid_test]
    return z_train, z_test


def fold_l3_contribution(b_matrix: list[list[float]], fold: FoldCache) -> tuple[list[float], list[float]]:
    """Return held-out B⊥ contribution and 9D gamma using cached C geometry."""
    width_b = len(b_matrix[0])
    width_c = fold.control_width
    ctb = [[0.0 for _ in range(width_b)] for _ in range(width_c)]
    btb = [[0.0 for _ in range(width_b)] for _ in range(width_b)]
    bty = [0.0 for _ in range(width_b)]
    for row_c, idx, yres in zip(fold.c_train, fold.train, fold.y_resid_train):
        row_b = b_matrix[idx]
        for j in range(width_b):
            bj = row_b[j]
            bty[j] += bj * yres
            for k in range(j, width_b):
                btb[j][k] += bj * row_b[k]
        for i in range(width_c):
            ci = row_c[i]
            for j in range(width_b):
                ctb[i][j] += ci * row_b[j]
    for j in range(width_b):
        for k in range(j):
            btb[j][k] = btb[k][j]

    a_cols: list[list[float]] = []
    for j in range(width_b):
        rhs_col = [ctb[i][j] for i in range(width_c)]
        a_cols.append([sum(fold.c_inv[row][i] * rhs_col[i] for i in range(width_c)) for row in range(width_c)])

    ztz = [[0.0 for _ in range(width_b)] for _ in range(width_b)]
    zty = [0.0 for _ in range(width_b)]
    for j in range(width_b):
        aj = a_cols[j]
        zty[j] = bty[j] - sum(aj[i] * fold.ct_y_resid[i] for i in range(width_c))
        for k in range(j, width_b):
            ak = a_cols[k]
            at_ctb = sum(aj[i] * ctb[i][k] for i in range(width_c))
            # C ridge is diagonal except for a tiny intercept ridge.
            ridge_penalty = aj[0] * ak[0] * RIDGE_C * 0.01 + sum(aj[i] * ak[i] * RIDGE_C for i in range(1, width_c))
            ztz[j][k] = btb[j][k] - at_ctb - ridge_penalty
    for j in range(width_b):
        for k in range(j):
            ztz[j][k] = ztz[k][j]
        ztz[j][j] += RIDGE_B
    gamma = cholesky_solve(cholesky_decompose(ztz), zty)

    a_gamma = [0.0 for _ in range(width_c)]
    for j in range(width_b):
        gj = gamma[j]
        if gj == 0.0:
            continue
        aj = a_cols[j]
        for i in range(width_c):
            a_gamma[i] += aj[i] * gj

    contrib: list[float] = []
    for row_c, idx in zip(fold.c_test, fold.test):
        row_b = b_matrix[idx]
        contrib.append(sum(row_b[j] * gamma[j] for j in range(width_b)) - dot(row_c, a_gamma))
    return contrib, gamma


def evaluate_b_matrix(b_matrix: list[list[float]], folds: list[FoldCache], n_total: int) -> dict[str, object]:
    pred_l2 = [0.0 for _ in range(n_total)]
    pred_l3 = [0.0 for _ in range(n_total)]
    beta_signs: list[str] = []
    beta_vectors: list[list[float]] = []
    for fold in folds:
        contrib_test, gamma = fold_l3_contribution(b_matrix, fold)
        beta_vectors.append(gamma)
        resid_test = [a - b for a, b in zip(fold.y_test, fold.pred_l2_test)]
        score = sum(a * b for a, b in zip(contrib_test, resid_test))
        beta_signs.append("positive" if score > EPS else ("negative" if score < -EPS else "zero"))
        for local, idx in enumerate(fold.test):
            pred_l2[idx] = fold.pred_l2_test[local]
            pred_l3[idx] = fold.pred_l2_test[local] + contrib_test[local]
    return {"pred_l2": pred_l2, "pred_l3": pred_l3, "beta_signs": beta_signs, "beta_vectors": beta_vectors}


def summarize_eval(y: list[float], evaluation: dict[str, object]) -> dict[str, float]:
    pred_l2 = evaluation["pred_l2"]
    pred_l3 = evaluation["pred_l3"]
    assert isinstance(pred_l2, list) and isinstance(pred_l3, list)
    sse_l2 = sse(y, pred_l2)
    sse_l3 = sse(y, pred_l3)
    total = tss(y)
    return {
        "SSE_L2": sse_l2,
        "SSE_L3": sse_l3,
        "R2_L2": 1.0 - sse_l2 / total,
        "R2_L3": 1.0 - sse_l3 / total,
        "delta_r2": (sse_l2 - sse_l3) / total,
        "delta_dl_bits": delta_dl_bits(sse_l2, sse_l3, len(y)),
    }


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    ordered = sorted(values)
    return [ordered[max(0, min(len(ordered) - 1, math.ceil(len(ordered) * i / bins) - 1))] for i in range(1, bins)]


def bin_index(value: float, cuts: list[float]) -> int:
    idx = 0
    while idx < len(cuts) and value > cuts[idx]:
        idx += 1
    return idx


def matched_bin_keys(bin_axes: list[list[float | None]]) -> tuple[list[tuple[int, ...]], dict[str, object]]:
    n = len(bin_axes)
    width = len(bin_axes[0])
    filled = [[0.0 for _ in range(width)] for _ in range(n)]
    for col in range(width):
        vals = [float(row[col]) for row in bin_axes if row[col] is not None and math.isfinite(float(row[col]))]
        center = mean(vals) if vals else 0.0
        for i in range(n):
            value = bin_axes[i][col]
            filled[i][col] = center if value is None or not math.isfinite(float(value)) else float(value)
    cuts = [quantile_cuts([filled[i][col] for i in range(n)], 2) for col in range(width)]
    keys = [tuple(bin_index(filled[i][col], cuts[col]) for col in range(width)) for i in range(n)]
    groups: dict[tuple[int, ...], int] = {}
    for key in keys:
        groups[key] = groups.get(key, 0) + 1
    return keys, {
        "bin_count": len(groups),
        "n_singleton_bins": sum(1 for count in groups.values() if count == 1),
        "median_bin_size": percentile_nearest_rank([float(count) for count in groups.values()], 0.5),
        "max_bin_size": max(groups.values()) if groups else 0,
    }


def shuffle_b_within_keys(b_matrix: list[list[float]], keys: list[tuple[int, ...]], trial: int) -> tuple[list[list[float]], int]:
    groups: dict[tuple[int, ...], list[int]] = {}
    for index, key in enumerate(keys):
        groups.setdefault(key, []).append(index)
    out = [list(row) for row in b_matrix]
    moved = 0
    for key, indices in sorted(groups.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|matched-bin|trial={trial}|key={key}")
        for dest, src in zip(indices, permuted):
            if dest != src:
                moved += 1
            out[dest] = list(b_matrix[src])
    return out, moved


def sample_counts(population: list[str], weights: list[float], total: int, rng: random.Random) -> dict[str, int]:
    if total <= 0:
        return {}
    if len(population) == 1:
        return {population[0]: total}
    positive = [max(0.0, w) for w in weights]
    if sum(positive) <= EPS:
        positive = [1.0 for _ in population]
    total_weight = sum(positive)
    expected = [total * w / total_weight for w in positive]
    base = [int(math.floor(v)) for v in expected]
    remainder = total - sum(base)
    out = {codon: count for codon, count in zip(population, base) if count}
    if remainder:
        frac = [v - math.floor(v) for v in expected]
        if sum(frac) <= EPS:
            frac = positive
        for codon in rng.choices(population, weights=frac, k=remainder):
            out[codon] = out.get(codon, 0) + 1
    return out


def build_recoder(rows: list[dict[str, object]], context: dict[str, object]) -> dict[str, object]:
    code = context["code"]
    codons = context["codons"]
    fibers = context["fibers"]
    assert isinstance(code, dict) and isinstance(codons, list) and isinstance(fibers, dict)
    pooled = {str(codon): 1.0 for codon in codons}
    for row in rows:
        counts = row["counts"]
        assert isinstance(counts, dict)
        for codon in codons:
            pooled[str(codon)] += int(counts[str(codon)])
    optimal: dict[str, int] = {}
    for aa, fiber in fibers.items():
        usages = [pooled[str(codon)] for codon in fiber]
        cut = percentile_nearest_rank(usages, 0.5)
        for codon in fiber:
            optimal[str(codon)] = 1 if pooled[str(codon)] >= cut else 0
    populations: dict[tuple[str, int, int], tuple[list[str], list[float]]] = {}
    for aa, fiber in fibers.items():
        for gc_flag in (0, 1):
            for opt_flag in (0, 1):
                pop = [str(codon) for codon in fiber if (1 if str(codon)[2] in {"G", "C"} else 0) == gc_flag and optimal[str(codon)] == opt_flag]
                populations[(str(aa), gc_flag, opt_flag)] = (pop, [pooled[codon] for codon in pop])
    specs = []
    for row in rows:
        counts = row["counts"]
        assert isinstance(counts, dict)
        tasks: list[tuple[tuple[str, int, int], int]] = []
        for aa, fiber in fibers.items():
            for gc_flag in (0, 1):
                for opt_flag in (0, 1):
                    total = sum(int(counts[str(codon)]) for codon in fiber if (1 if str(codon)[2] in {"G", "C"} else 0) == gc_flag and optimal[str(codon)] == opt_flag)
                    if total:
                        tasks.append(((str(aa), gc_flag, opt_flag), total))
        specs.append(tasks)
    return {"populations": populations, "specs": specs, "codons": codons}


def recoded_b_matrix(recoder: dict[str, object], context: dict[str, object], trial: int) -> tuple[list[list[float]], dict[str, float]]:
    populations = recoder["populations"]
    specs = recoder["specs"]
    codons = recoder["codons"]
    assert isinstance(populations, dict) and isinstance(specs, list) and isinstance(codons, list)
    rng = stable_random(f"{SEED}|recoded|null|{trial}")
    out: list[list[float]] = []
    changed_rows = 0
    for tasks in specs:
        counts = {str(codon): 0 for codon in codons}
        assert isinstance(tasks, list)
        for key, total in tasks:
            pop, weights = populations[key]
            sampled = sample_counts(pop, weights, int(total), rng)
            for codon, count in sampled.items():
                counts[codon] += count
        out.append(q_row_from_counts(counts, context))
        if any(counts[codon] != 0 for codon in codons):
            changed_rows += 1
    return out, {"recoded_rows": float(changed_rows)}


def null_distribution(
    kind: str,
    b_matrix: list[list[float]],
    y: list[float],
    folds: list[FoldCache],
    keys: list[tuple[int, ...]],
    recoder: dict[str, object],
    context: dict[str, object],
    b: int,
) -> dict[str, object]:
    deltas_dl: list[float] = []
    deltas_r2: list[float] = []
    moved: list[float] = []
    for trial in range(b):
        if kind == "matched":
            trial_b, n_moved = shuffle_b_within_keys(b_matrix, keys, trial)
            moved.append(float(n_moved))
        elif kind == "recoded":
            trial_b, diag = recoded_b_matrix(recoder, context, trial)
            moved.append(float(diag["recoded_rows"]))
        else:
            raise ValueError(kind)
        evaluation = evaluate_b_matrix(trial_b, folds, len(y))
        summary = summarize_eval(y, evaluation)
        deltas_dl.append(summary["delta_dl_bits"])
        deltas_r2.append(summary["delta_r2"])
    return {
        "actual_B": b,
        "delta_dl_bits": deltas_dl,
        "delta_r2": deltas_r2,
        "null99_delta_dl_bits": percentile_nearest_rank(deltas_dl, 0.99),
        "null95_delta_dl_bits": percentile_nearest_rank(deltas_dl, 0.95),
        "null_mean_delta_dl_bits": mean(deltas_dl),
        "null_max_delta_dl_bits": max(deltas_dl) if deltas_dl else 0.0,
        "mean_rows_changed_or_moved": mean(moved),
    }


def init_null_worker(
    b_matrix: list[list[float]],
    y: list[float],
    folds: list[FoldCache],
    keys: list[tuple[int, ...]],
    recoder: dict[str, object],
    context: dict[str, object],
) -> None:
    global G_B_MATRIX, G_Y, G_FOLDS, G_KEYS, G_RECODER, G_CONTEXT
    G_B_MATRIX = b_matrix
    G_Y = y
    G_FOLDS = folds
    G_KEYS = keys
    G_RECODER = recoder
    G_CONTEXT = context


def null_trial_worker(args: tuple[str, int]) -> tuple[float, float, float]:
    kind, trial = args
    if kind == "matched":
        trial_b, moved = shuffle_b_within_keys(G_B_MATRIX, G_KEYS, trial)
        changed = float(moved)
    elif kind == "recoded":
        trial_b, diag = recoded_b_matrix(G_RECODER, G_CONTEXT, trial)
        changed = float(diag["recoded_rows"])
    else:
        raise ValueError(kind)
    evaluation = evaluate_b_matrix(trial_b, G_FOLDS, len(G_Y))
    summary = summarize_eval(G_Y, evaluation)
    return summary["delta_dl_bits"], summary["delta_r2"], changed


def null_distribution_parallel(
    kind: str,
    b_matrix: list[list[float]],
    y: list[float],
    folds: list[FoldCache],
    keys: list[tuple[int, ...]],
    recoder: dict[str, object],
    context: dict[str, object],
    b: int,
) -> dict[str, object]:
    workers = min(4, max(1, (os.cpu_count() or 1)))
    args = [(kind, trial) for trial in range(b)]
    if workers <= 1:
        init_null_worker(b_matrix, y, folds, keys, recoder, context)
        results = [null_trial_worker(arg) for arg in args]
    else:
        mp_context = multiprocessing.get_context("fork")
        with mp_context.Pool(
            processes=workers,
            initializer=init_null_worker,
            initargs=(b_matrix, y, folds, keys, recoder, context),
        ) as pool:
            results = pool.map(null_trial_worker, args, chunksize=max(1, b // (workers * 8)))
    deltas_dl = [item[0] for item in results]
    deltas_r2 = [item[1] for item in results]
    changed = [item[2] for item in results]
    return {
        "actual_B": b,
        "delta_dl_bits": deltas_dl,
        "delta_r2": deltas_r2,
        "null99_delta_dl_bits": percentile_nearest_rank(deltas_dl, 0.99),
        "null95_delta_dl_bits": percentile_nearest_rank(deltas_dl, 0.95),
        "null_mean_delta_dl_bits": mean(deltas_dl),
        "null_max_delta_dl_bits": max(deltas_dl) if deltas_dl else 0.0,
        "mean_rows_changed_or_moved": mean(changed),
        "workers": workers,
    }


def one_sided_p(real: float, null_values: list[float]) -> float:
    return (1.0 + sum(1 for value in null_values if value >= real)) / (len(null_values) + 1.0)


def sign_stable(signs: list[str]) -> bool:
    clean = [s for s in signs if s != "zero"]
    return len(clean) == len(signs) and (all(s == "positive" for s in clean) or all(s == "negative" for s in clean))


def run_real_subset(data: dict[str, object], subset: list[int] | None = None) -> dict[str, object]:
    y_all = data["y"]
    controls_all = data["controls"]
    b_all = data["q"]
    assert isinstance(y_all, list) and isinstance(controls_all, list) and isinstance(b_all, list)
    if subset is None:
        y = [float(v) for v in y_all]
        controls = controls_all
        b_matrix = b_all
        folds = make_folds(controls, y)
    else:
        y = [float(y_all[i]) for i in subset]
        old_to_new = {old: new for new, old in enumerate(subset)}
        controls = [controls_all[i] for i in subset]
        b_matrix = [b_all[i] for i in subset]
        folds = make_folds(controls, y)
        _ = old_to_new
    evaluation = evaluate_b_matrix(b_matrix, folds, len(y))
    summary = summarize_eval(y, evaluation)
    return {"n_genes": len(y), "folds": folds, "evaluation": evaluation, "summary": summary}


def main() -> None:
    started = time.time()
    try:
        repo = pathlib.Path.cwd()
        data = build_dataset(repo)
        genes = data["genes"]
        y = data["y"]
        q = data["q"]
        controls = data["controls"]
        rows = data["rows"]
        assert isinstance(genes, list) and isinstance(y, list) and isinstance(q, list) and isinstance(controls, list) and isinstance(rows, list)
        if len(genes) < 200:
            emit(
                "needs_data",
                verdict="needs_data",
                checks={"data_loaded": False, "reason": "joined gene count below 200"},
                result={"n_genes": len(genes), "actual_B": 0, "runtime_sec": round(time.time() - started, 3)},
            )

        folds = make_folds(controls, [float(v) for v in y])
        real_eval = evaluate_b_matrix(q, folds, len(y))
        real = summarize_eval([float(v) for v in y], real_eval)
        beta_signs = real_eval["beta_signs"]
        assert isinstance(beta_signs, list)

        keys, bin_summary = matched_bin_keys(data["bin_axes"])  # type: ignore[arg-type]
        recoder = build_recoder(rows, data["context"])  # type: ignore[arg-type]
        matched = null_distribution_parallel("matched", q, [float(v) for v in y], folds, keys, recoder, data["context"], TARGET_NULL_B)  # type: ignore[arg-type]
        recoded = null_distribution_parallel("recoded", q, [float(v) for v in y], folds, keys, recoder, data["context"], TARGET_NULL_B)  # type: ignore[arg-type]

        p_matched = one_sided_p(real["delta_dl_bits"], matched["delta_dl_bits"])  # type: ignore[arg-type]
        p_recoded = one_sided_p(real["delta_dl_bits"], recoded["delta_dl_bits"])  # type: ignore[arg-type]
        pass_gate = (
            real["delta_dl_bits"] > float(matched["null99_delta_dl_bits"])
            and real["delta_dl_bits"] > float(recoded["null99_delta_dl_bits"])
            and sign_stable([str(s) for s in beta_signs])
        )
        verdict = "proteostasis_escape_candidate" if pass_gate else "turnover_null_current_domain_closed"

        sensitivity_indices = [
            i for i, row in enumerate(rows)
            if not bool(row.get("ribosomal")) and not bool(row.get("mitochondrial")) and not bool(row.get("membrane"))
        ]
        sensitivity = run_real_subset(data, sensitivity_indices)
        sens_summary = sensitivity["summary"]
        assert isinstance(sens_summary, dict)
        sensitivity_no_ribo_mito = {
            "n_genes": sensitivity["n_genes"],
            "removed": len(rows) - len(sensitivity_indices),
            "remove_rule": "ribosomal gene symbol prefix RPL/RPS/MRP/MRPL/MRPS or localization text ribosom; mitochondrial/membrane from localization categories/raw text",
            "R2_L2": sens_summary["R2_L2"],
            "R2_L3": sens_summary["R2_L3"],
            "delta_r2": sens_summary["delta_r2"],
            "delta_dl_bits": sens_summary["delta_dl_bits"],
            "null_verdict_still_holds": sens_summary["delta_dl_bits"] <= 0.0 if verdict == "turnover_null_current_domain_closed" else None,
        }

        checks = {
            "data_loaded": {
                "passed": True,
                "source_counts": data["source_counts"],
                "turnover_outcome": "measured Christiano 2014 SGD protein half-life hours; y=ln(ln2/t_half), not inferred mass-balance lambda",
            },
            "controls_built": {
                "passed": True,
                "available_controls": data["controls_available"],
                "missing_controls": data["controls_missing"],
                "n_control_columns_before_intercept": len(data["control_names"]),  # type: ignore[arg-type]
                "control_policy": "positive quantities natural-log transformed; pLDDT/localization/essentiality missing indicators included where needed",
            },
            "b_perp_residualized_trainfold": {
                "passed": True,
                "q_dim": len(q[0]) if q else 0,
                "q_names": data["q_names"],
                "method": "within each gene-heldout fold, each B*_Q6 dimension is fit on train controls only; train/test residuals then train-standardized before L3 block update",
            },
            "ladder_L2_L3_heldout_by_gene": {
                "passed": True,
                "fold_count": FOLD_COUNT,
                "fold_sizes": [len(f.test) for f in folds],
                "ridge": {"controls": RIDGE_C, "B_perp_block": RIDGE_B},
            },
            "matchedbin_null": {
                "passed": True,
                "actual_B": TARGET_NULL_B,
                "bin_axes": data["bin_axis_names"],
                "bin_summary": bin_summary,
                "null99_delta_dl_bits": matched["null99_delta_dl_bits"],
                "mean_rows_moved": matched["mean_rows_changed_or_moved"],
            },
            "recoded_null": {
                "passed": True,
                "actual_B": TARGET_NULL_B,
                "null99_delta_dl_bits": recoded["null99_delta_dl_bits"],
                "mean_recoded_rows": recoded["mean_rows_changed_or_moved"],
                "recode_policy": "AA sequence preserved by synonymous family; GC3-ending bin and pooled codon-optimality bin preserved per ORF task before recomputing B*_Q6",
            },
            "sensitivity_run": {"passed": True, "sensitivity_no_ribo_mito_membrane": sensitivity_no_ribo_mito},
            "turnover_residual_verdict": {
                "passed": True,
                "gate": "proteostasis_escape_candidate iff real ΔDL exceeds 99% of both nulls and fold contribution signs are stable",
                "sign_stable": sign_stable([str(s) for s in beta_signs]),
                "verdict": verdict,
            },
        }

        cannot_claim = [
            "Christiano 2014 单 turnover 数据集稳态非 pulse-chase per-condition",
            "非 causal folding code",
            "非 physical degradation constant",
            "非 universal law",
            "relative/steady-state",
            "localization/membrane/essentiality controls are available proxies; complex-membership control was not available as a local structured payload",
        ]
        allowed_claim = (
            "B*_Q6 有候选 post-translational proteostasis association, 超 static TE/expression"
            if verdict == "proteostasis_escape_candidate"
            else "无证据 B*_Q6 在 expression+TE+pLDDT+N-end 等之外预测实测 turnover → current-data 域闭合"
        )
        result = {
            "n_genes": len(genes),
            "actual_B": TARGET_NULL_B,
            "runtime_sec": round(time.time() - started, 3),
            "R2_L2": real["R2_L2"],
            "R2_L3": real["R2_L3"],
            "delta_r2": real["delta_r2"],
            "delta_dl_bits": real["delta_dl_bits"],
            "p_matchedbin": p_matched,
            "p_recoded": p_recoded,
            "null99_matchedbin_delta_dl_bits": matched["null99_delta_dl_bits"],
            "null99_recoded_delta_dl_bits": recoded["null99_delta_dl_bits"],
            "sensitivity_no_ribo_mito": sensitivity_no_ribo_mito,
            "beta_B_sign_by_fold": beta_signs,
            "cannot_claim": cannot_claim,
            "allowed_claim": allowed_claim,
        }
        emit("passed", checks=checks, verdict=verdict, result=result)
    except Exception as exc:
        emit(
            "failed",
            checks={"data_loaded": False, "turnover_residual_verdict": {"passed": False}},
            verdict="error",
            result={"runtime_sec": round(time.time() - started, 3), "error": f"{type(exc).__name__}: {exc}"},
        )


if __name__ == "__main__":
    main()

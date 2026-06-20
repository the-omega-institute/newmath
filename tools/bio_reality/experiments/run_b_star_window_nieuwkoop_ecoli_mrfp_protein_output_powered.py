#!/usr/bin/env python3
"""Nieuwkoop E.coli mRFP synonymous whole-CDS B_window protein-output test.

纯 stdlib 离线脚本：解析 xlsx(zip+xml)、生成 compact JSON、构建 9D aa-fiber-centered
B*_Q6 residual 特征、控制 CAI/tAI_proxy/GC/GC3/length，做 5-fold held-out
L2(y~C) vs L3(y~C+b_perp) 与两个 B>=200 null。
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import re
import sys
import time
import zipfile
import xml.etree.ElementTree as ET


EXPERIMENT_ID = "b_star_window_nieuwkoop_ecoli_mrfp_protein_output_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_nieuwkoop_ecoli_mrfp_protein_output_powered"
WORKDIR = pathlib.Path("/tmp/nieu-csc")
XLSX_PATH = pathlib.Path("tools/bio_reality/data/nieuwkoop_mrfp.xlsx")
COMPACT_JSON_PATH = pathlib.Path("/tmp/nieuwkoop_mrfp_compact_real_cai.json")
CAI_WEIGHTS_PATHS = [
    pathlib.Path("tools/bio_reality/data/ecoli_genome_cai_weights.json"),
    WORKDIR / "ecoli_genome_cai_weights.json",
]

FOLD_COUNT = 5
NULL_B = 200
RIDGE = 1e-6
EPS = 1e-12
SEED = "sha256:b_star_window_nieuwkoop_ecoli_mrfp_protein_output_powered:deterministic"

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
Q_NAMES = [
    "K_AAA",
    "Arg_AGR",
    "Ile_AUA",
    "Leu_CUN_vs_UUR",
    "Leu_UUA_vs_UUG",
    "Ser_UCR_vs_AGY",
    "Ser_UCA_vs_UCG",
    "Thr_ACR_vs_ACY",
    "f3_stress",
]

STANDARD_CODE_RNA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}


def emit(status: str, checks: dict[str, object], verdict: str, result: dict[str, object], started: float) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    payload["result"]["runtime_sec"] = round(time.time() - started, 3)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


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


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def pearson(x: list[float], y: list[float]) -> float:
    if len(x) != len(y) or len(x) < 2:
        return 0.0
    mx = mean(x)
    my = mean(y)
    vx = sum((v - mx) ** 2 for v in x)
    vy = sum((v - my) ** 2 for v in y)
    if vx <= EPS or vy <= EPS:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(vx * vy)


def cholesky_decompose(matrix: list[list[float]]) -> list[list[float]]:
    n = len(matrix)
    lower = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            value = matrix[i][j] - sum(lower[i][k] * lower[j][k] for k in range(j))
            if i == j:
                if value <= EPS:
                    raise ValueError("matrix is not positive definite")
                lower[i][j] = math.sqrt(value)
            else:
                lower[i][j] = value / lower[j][j]
    return lower


def cholesky_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    jitter = RIDGE
    for _attempt in range(8):
        adjusted = [list(row) for row in matrix]
        for i in range(n):
            adjusted[i][i] += jitter
        try:
            lower = cholesky_decompose(adjusted)
            y = [0.0 for _ in range(n)]
            for i in range(n):
                y[i] = (rhs[i] - sum(lower[i][k] * y[k] for k in range(i))) / lower[i][i]
            x = [0.0 for _ in range(n)]
            for i in range(n - 1, -1, -1):
                x[i] = (y[i] - sum(lower[k][i] * x[k] for k in range(i + 1, n))) / lower[i][i]
            return x
        except ValueError:
            jitter *= 10.0
    raise ValueError("Cholesky ridge solve failed")


def ridge_fit(x_rows: list[list[float]], y: list[float]) -> list[float]:
    if not x_rows:
        return []
    width = len(x_rows[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, value in zip(x_rows, y):
        for i in range(width):
            rhs[i] += row[i] * value
            for j in range(i, width):
                xtx[i][j] += row[i] * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    return cholesky_solve(xtx, rhs)


def predict_rows(x_rows: list[list[float]], beta: list[float]) -> list[float]:
    return [dot(row, beta) for row in x_rows]


def standardize_train_apply(
    matrix: list[list[float]],
    train: list[int],
    test: list[int],
) -> tuple[list[list[float]], list[list[float]], list[tuple[float, float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test], []
    width = len(matrix[0])
    stats = []
    for col in range(width):
        values = [matrix[i][col] for i in train]
        center = mean(values)
        sd = math.sqrt(variance(values))
        if sd <= EPS:
            sd = 1.0
        stats.append((center, sd))
    train_out = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in train]
    test_out = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in test]
    return train_out, test_out, stats


def sse(y: list[float], pred: list[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(y, pred))


def tss(y: list[float]) -> float:
    center = mean(y)
    return max(EPS, sum((value - center) ** 2 for value in y))


def delta_r2(base_sse: float, full_sse: float, total_tss: float) -> float:
    return (base_sse - full_sse) / total_tss


def delta_dl_bits(base_sse: float, full_sse: float, n: int, added_dim: int) -> float:
    improvement = 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS), 2)
    bic_cost = 0.5 * added_dim * math.log(max(n, 2), 2)
    return improvement - bic_cost


def col_to_index(column: str) -> int:
    out = 0
    for char in column:
        out = out * 26 + ord(char) - ord("A") + 1
    return out - 1


def xlsx_cell_text(cell: ET.Element, shared_strings: list[str], ns: str) -> str:
    cell_type = cell.attrib.get("t")
    value = cell.find(ns + "v")
    if cell_type == "s" and value is not None:
        return shared_strings[int(value.text or "0")]
    if cell_type == "inlineStr":
        inline = cell.find(ns + "is")
        if inline is None:
            return ""
        return "".join(text.text or "" for text in inline.iter(ns + "t"))
    return value.text if value is not None and value.text is not None else ""


def parse_xlsx_rows(path: pathlib.Path) -> list[dict[str, object]]:
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    with zipfile.ZipFile(path) as zf:
        shared_strings: list[str] = []
        shared_xml = ET.fromstring(zf.read("xl/sharedStrings.xml"))
        for item in shared_xml.iter(ns + "si"):
            shared_strings.append("".join(text.text or "" for text in item.iter(ns + "t")))
        sheet_xml = ET.fromstring(zf.read("xl/worksheets/sheet2.xml"))
        raw_rows: list[dict[int, str]] = []
        for row in sheet_xml.iter(ns + "row"):
            values: dict[int, str] = {}
            for cell in row.iter(ns + "c"):
                match = re.match(r"([A-Z]+)", cell.attrib["r"])
                if match:
                    values[col_to_index(match.group(1))] = xlsx_cell_text(cell, shared_strings, ns)
            if values:
                raw_rows.append(values)
    if not raw_rows:
        raise ValueError("xlsx sheet2 is empty")
    header = {value: key for key, value in raw_rows[0].items()}
    required = ["Header", "Plate+location", "mRFP Mean Corrected", "Sequence Data"]
    missing = [name for name in required if name not in header]
    if missing:
        raise ValueError(f"missing required columns: {missing}")
    rows: list[dict[str, object]] = []
    skipped = 0
    for raw_index, raw in enumerate(raw_rows[1:], start=2):
        seq = str(raw.get(header["Sequence Data"], "")).strip().upper()
        corrected_raw = raw.get(header["mRFP Mean Corrected"], "")
        try:
            corrected = float(corrected_raw)
        except ValueError:
            skipped += 1
            continue
        if corrected <= 0.0 or len(seq) % 3 != 0 or seq[:3] != "ATG" or set(seq) - {"A", "T", "G", "C"}:
            skipped += 1
            continue
        codons = [seq[i:i + 3].replace("T", "U") for i in range(0, len(seq), 3)]
        # Validated CDS rows include the terminal stop codon. B/control features below
        # are computed on sense codons only; internal stop codons are rejected.
        if any(STANDARD_CODE_RNA.get(codon) is None for codon in codons):
            skipped += 1
            continue
        if any(STANDARD_CODE_RNA[codon] == "*" for codon in codons[:-1]):
            skipped += 1
            continue
        rows.append(
            {
                "id": len(rows),
                "xlsx_row": raw_index,
                "header": raw.get(header["Header"], ""),
                "plate_location": raw.get(header["Plate+location"], ""),
                "mrfp_mean_corrected": corrected,
                "log_protein_output": math.log(corrected),
                "sequence": seq,
            }
        )
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "source_xlsx": str(path),
        "sheet": "S2 Validated Data",
        "target": "natural_log(mRFP Mean Corrected), positive rows only",
        "n_variants": len(rows),
        "skipped_rows": skipped,
        "rows": rows,
    }
    COMPACT_JSON_PATH.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    return rows


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        aa = code[codon]
        if aa != "*":
            fibers.setdefault(aa, []).append(codon)
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
    for codon in ["AGA", "AGG"]:
        q[codon] = 1.0
    for codon in ["CGU", "CGC", "CGA", "CGG"]:
        q[codon] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for codon in CUN_CODONS:
        q[codon] = 0.25
    for codon in UUR_CODONS:
        q[codon] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for codon in ["UCA", "UCG"]:
        q[codon] = 0.5
    for codon in ["AGU", "AGC"]:
        q[codon] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for codon in ["ACA", "ACG"]:
        q[codon] = 0.5
    for codon in ["ACU", "ACC"]:
        q[codon] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def q_context() -> dict[str, object]:
    codons = sorted(codon for codon, aa in STANDARD_CODE_RNA.items() if aa != "*")
    fibers = fibers_for(STANDARD_CODE_RNA, codons)
    projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    denoms = {
        name: math.sqrt(sum(projected[name][codon] ** 2 for codon in codons))
        for name in Q_NAMES
    }
    return {"codons": codons, "fibers": fibers, "q_projected": projected, "q_denoms": denoms}


def codon_counts(sequence: str, codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in codons}
    for index in range(0, len(sequence), 3):
        codon = sequence[index:index + 3].replace("T", "U")
        if codon in counts:
            counts[codon] += 1
    return counts


def q_row_from_counts(counts: dict[str, int], context: dict[str, object]) -> list[float]:
    codons = context["codons"]
    projected = context["q_projected"]
    denoms = context["q_denoms"]
    if not isinstance(codons, list) or not isinstance(projected, dict) or not isinstance(denoms, dict):
        raise ValueError("B context malformed")
    total = sum(counts[codon] for codon in codons)
    if total <= 0:
        raise ValueError("empty codon counts")
    row = []
    for name in Q_NAMES:
        qvec = projected[name]
        denom = float(denoms[name])
        if not isinstance(qvec, dict):
            raise ValueError("projected B vector malformed")
        row.append(sum((counts[codon] / total) * float(qvec[codon]) for codon in codons) / denom)
    return row


def build_reference_weights(rows: list[dict[str, object]], context: dict[str, object]) -> dict[str, object]:
    codons = context["codons"]
    fibers = context["fibers"]
    if not isinstance(codons, list) or not isinstance(fibers, dict):
        raise ValueError("B context malformed")
    pooled = {codon: 1.0 for codon in codons}
    for row in rows:
        counts = codon_counts(str(row["sequence"]), codons)
        for codon in codons:
            pooled[codon] += counts[codon]
    global_gc3 = sum(pooled[codon] for codon in codons if codon[2] in {"G", "C"}) / sum(pooled.values())
    cai_weight: dict[str, float] = {}
    tai_weight: dict[str, float] = {}
    for _aa, fiber in fibers.items():
        if not isinstance(fiber, list):
            continue
        total = sum(pooled[codon] for codon in fiber)
        conditional = {codon: pooled[codon] / total for codon in fiber}
        max_cond = max(conditional.values())
        raw_tai = {}
        for codon in fiber:
            gc_class = global_gc3 if codon[2] in {"G", "C"} else (1.0 - global_gc3)
            raw_tai[codon] = conditional[codon] * max(gc_class, EPS)
        max_tai = max(raw_tai.values())
        for codon in fiber:
            cai_weight[codon] = max(conditional[codon] / max_cond, EPS)
            tai_weight[codon] = max(raw_tai[codon] / max_tai, EPS)
    return {
        "pooled_counts_with_pseudocount": pooled,
        "global_gc3": global_gc3,
        "cai_weight": cai_weight,
        "tai_proxy_weight": tai_weight,
    }


def load_genome_cai_reference(context: dict[str, object]) -> dict[str, object]:
    codons = context["codons"]
    fibers = context["fibers"]
    if not isinstance(codons, list) or not isinstance(fibers, dict):
        raise ValueError("B context malformed")
    path = None
    payload = None
    for candidate in CAI_WEIGHTS_PATHS:
        if candidate.exists():
            path = candidate
            payload = json.loads(candidate.read_text(encoding="utf-8"))
            break
    if payload is None or path is None:
        raise FileNotFoundError("ecoli_genome_cai_weights.json not found in repo data or /tmp/nieu-csc")
    weights = payload.get("weights_rna")
    rscu_dna = payload.get("rscu_dna", {})
    counts_dna = payload.get("codon_counts_dna", {})
    if not isinstance(weights, dict) or len(weights) < 61:
        raise ValueError("genome CAI weights malformed")
    cai_weight = {codon: max(float(weights[codon]), EPS) for codon in codons}
    rscu = {codon: float(rscu_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons}
    total_counts = sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons)
    if total_counts <= EPS:
        genome_gc3 = 0.5
    else:
        gc3_counts = sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons if codon[2] in {"G", "C"})
        genome_gc3 = gc3_counts / total_counts
    tai_proxy_weight: dict[str, float] = {}
    for _aa, fiber in fibers.items():
        if not isinstance(fiber, list):
            continue
        raw = {}
        for codon in fiber:
            gc_class = genome_gc3 if codon[2] in {"G", "C"} else (1.0 - genome_gc3)
            raw[codon] = max(rscu.get(codon, 0.0), EPS) * max(gc_class, EPS)
        max_raw = max(raw.values()) if raw else 1.0
        for codon in fiber:
            tai_proxy_weight[codon] = max(raw[codon] / max_raw, EPS)
    return {
        "path": str(path),
        "payload": payload,
        "cai_weight": cai_weight,
        "tai_proxy_weight": tai_proxy_weight,
        "genome_gc3": genome_gc3,
    }


def geometric_index(counts: dict[str, int], weights: dict[str, float]) -> float:
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    return math.exp(sum(counts[codon] * math.log(max(weights[codon], EPS)) for codon in counts) / total)


def build_dataset(rows: list[dict[str, object]]) -> dict[str, object]:
    context = q_context()
    codons = context["codons"]
    if not isinstance(codons, list):
        raise ValueError("B context malformed")
    refs = build_reference_weights(rows, context)
    library_cai_weight = refs["cai_weight"]
    genome_refs = load_genome_cai_reference(context)
    cai_weight = genome_refs["cai_weight"]
    tai_weight = genome_refs["tai_proxy_weight"]
    if not isinstance(library_cai_weight, dict) or not isinstance(cai_weight, dict) or not isinstance(tai_weight, dict):
        raise ValueError("reference weights malformed")
    b_matrix: list[list[float]] = []
    controls: list[list[float]] = []
    targets: list[float] = []
    target_raw: list[float] = []
    library_cai_values: list[float] = []
    genome_cai_values: list[float] = []
    control_names = ["CAI_Ecoli_K12_genome_RSCU", "tAI_proxy_Ecoli_K12_genome_RSCU_GC3", "GC", "GC3", "log_CDS_length"]
    for row in rows:
        seq = str(row["sequence"])
        counts = codon_counts(seq, codons)
        total_codons = sum(counts.values())
        gc = (seq.count("G") + seq.count("C")) / len(seq)
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total_codons
        library_cai = geometric_index(counts, library_cai_weight)  # type: ignore[arg-type]
        cai = geometric_index(counts, cai_weight)  # type: ignore[arg-type]
        tai_proxy = geometric_index(counts, tai_weight)  # type: ignore[arg-type]
        library_cai_values.append(library_cai)
        genome_cai_values.append(cai)
        b_matrix.append(q_row_from_counts(counts, context))
        controls.append([cai, tai_proxy, gc, gc3, math.log(total_codons * 3)])
        targets.append(float(row["log_protein_output"]))
        target_raw.append(float(row["mrfp_mean_corrected"]))
    return {
        "context": context,
        "b_matrix": b_matrix,
        "controls": controls,
        "control_names": control_names,
        "targets": targets,
        "target_raw": target_raw,
        "reference": refs,
        "genome_reference": genome_refs,
        "library_cai_values": library_cai_values,
        "genome_cai_values": genome_cai_values,
        "real_cai_vs_proxy_corr": pearson(genome_cai_values, library_cai_values),
    }


class FoldState:
    def __init__(self, fold_id: int, train: list[int], test: list[int], c_train: list[list[float]], c_test: list[list[float]]) -> None:
        self.fold_id = fold_id
        self.train = train
        self.test = test
        self.c_train = c_train
        self.c_test = c_test


def make_folds(controls: list[list[float]], targets: list[float]) -> list[FoldState]:
    n = len(controls)
    indices = list(range(n))
    # variant-level held-out split; target-sorted round-robin keeps fold target ranges comparable.
    sorted_indices = sorted(indices, key=lambda i: (targets[i], i))
    buckets = [[] for _ in range(FOLD_COUNT)]
    for rank, index in enumerate(sorted_indices):
        buckets[rank % FOLD_COUNT].append(index)
    folds: list[FoldState] = []
    for fold_id in range(FOLD_COUNT):
        test = deterministic_permutation(buckets[fold_id], f"{SEED}|fold-test|{fold_id}")
        test_set = set(test)
        train = [index for index in indices if index not in test_set]
        c_train_raw, c_test_raw, _stats = standardize_train_apply(controls, train, test)
        c_train = [[1.0] + row for row in c_train_raw]
        c_test = [[1.0] + row for row in c_test_raw]
        folds.append(FoldState(fold_id, train, test, c_train, c_test))
    return folds


def base_cv_predictions(targets: list[float], folds: list[FoldState]) -> tuple[list[float], list[list[float]]]:
    preds = [0.0 for _ in targets]
    betas: list[list[float]] = []
    for fold in folds:
        train_y = [targets[i] for i in fold.train]
        beta = ridge_fit(fold.c_train, train_y)
        betas.append(beta)
        fold_preds = predict_rows(fold.c_test, beta)
        for local, index in enumerate(fold.test):
            preds[index] = fold_preds[local]
    return preds, betas


def residualize_b_for_fold(
    b_matrix: list[list[float]],
    fold: FoldState,
) -> tuple[list[list[float]], list[list[float]]]:
    width = len(b_matrix[0])
    train_resid_cols: list[list[float]] = []
    test_resid_cols: list[list[float]] = []
    for col in range(width):
        train_target = [b_matrix[i][col] for i in fold.train]
        beta = ridge_fit(fold.c_train, train_target)
        pred_train = predict_rows(fold.c_train, beta)
        pred_test = predict_rows(fold.c_test, beta)
        train_resid_cols.append([b_matrix[index][col] - pred_train[local] for local, index in enumerate(fold.train)])
        test_resid_cols.append([b_matrix[index][col] - pred_test[local] for local, index in enumerate(fold.test)])
    train_resid = [[train_resid_cols[col][row] for col in range(width)] for row in range(len(fold.train))]
    test_resid = [[test_resid_cols[col][row] for col in range(width)] for row in range(len(fold.test))]
    full_resid = [[0.0 for _ in range(width)] for _ in range(len(b_matrix))]
    for local, index in enumerate(fold.train):
        full_resid[index] = train_resid[local]
    for local, index in enumerate(fold.test):
        full_resid[index] = test_resid[local]
    train_std, test_std, _stats = standardize_train_apply(full_resid, fold.train, fold.test)
    return train_std, test_std


def evaluate_b_matrix(
    targets: list[float],
    b_matrix: list[list[float]],
    folds: list[FoldState],
    base_preds: list[float],
) -> dict[str, object]:
    preds = [0.0 for _ in targets]
    beta_b_by_fold: list[list[float]] = []
    contribution_by_fold: list[float] = []
    for fold in folds:
        b_train, b_test = residualize_b_for_fold(b_matrix, fold)
        x_train = [fold.c_train[i] + b_train[i] for i in range(len(fold.train))]
        x_test = [fold.c_test[i] + b_test[i] for i in range(len(fold.test))]
        train_y = [targets[i] for i in fold.train]
        beta = ridge_fit(x_train, train_y)
        beta_b = beta[-len(b_matrix[0]):]
        beta_b_by_fold.append(beta_b)
        fold_preds = predict_rows(x_test, beta)
        fold_contrib = [dot(row, beta_b) for row in b_test]
        fold_y = [targets[i] for i in fold.test]
        contribution_by_fold.append(pearson(fold_contrib, fold_y))
        for local, index in enumerate(fold.test):
            preds[index] = fold_preds[local]
    base = sse(targets, base_preds)
    full = sse(targets, preds)
    return {
        "preds": preds,
        "base_sse": base,
        "full_sse": full,
        "delta_r2": delta_r2(base, full, tss(targets)),
        "delta_dl_bits": delta_dl_bits(base, full, len(targets), len(b_matrix[0])),
        "beta_b_by_fold": beta_b_by_fold,
        "fold_contribution_cor": contribution_by_fold,
    }


def shuffled_b_matrix(b_matrix: list[list[float]], trial: int) -> list[list[float]]:
    indices = deterministic_permutation(list(range(len(b_matrix))), f"{SEED}|within-library-shuffle|trial={trial}")
    return [list(b_matrix[src]) for src in indices]


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    ordered = sorted(values)
    cuts = []
    for i in range(1, bins):
        cuts.append(ordered[max(0, min(len(ordered) - 1, math.ceil(len(ordered) * i / bins) - 1))])
    return cuts


def bin_index(value: float, cuts: list[float]) -> int:
    out = 0
    while out < len(cuts) and value > cuts[out]:
        out += 1
    return out


def matched_bin_shuffled_b_matrix(b_matrix: list[list[float]], controls: list[list[float]], trial: int) -> list[list[float]]:
    cai = [row[0] for row in controls]
    tai = [row[1] for row in controls]
    gc3 = [row[3] for row in controls]
    cai_cuts = quantile_cuts(cai, 3)
    tai_cuts = quantile_cuts(tai, 3)
    gc3_cuts = quantile_cuts(gc3, 3)
    bins: dict[tuple[int, int, int], list[int]] = {}
    for index in range(len(b_matrix)):
        key = (bin_index(cai[index], cai_cuts), bin_index(tai[index], tai_cuts), bin_index(gc3[index], gc3_cuts))
        bins.setdefault(key, []).append(index)
    out = [list(row) for row in b_matrix]
    for key, indices in sorted(bins.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|matched-bin-shuffle|trial={trial}|bin={key}")
        for dest, src in zip(indices, permuted):
            out[dest] = list(b_matrix[src])
    return out


def run_nulls(
    targets: list[float],
    b_matrix: list[list[float]],
    controls: list[list[float]],
    folds: list[FoldState],
    base_preds: list[float],
) -> dict[str, object]:
    within_dl: list[float] = []
    within_r2: list[float] = []
    matched_dl: list[float] = []
    matched_r2: list[float] = []
    for trial in range(NULL_B):
        within_result = evaluate_b_matrix(targets, shuffled_b_matrix(b_matrix, trial), folds, base_preds)
        within_dl.append(float(within_result["delta_dl_bits"]))
        within_r2.append(float(within_result["delta_r2"]))
        matched_result = evaluate_b_matrix(targets, matched_bin_shuffled_b_matrix(b_matrix, controls, trial), folds, base_preds)
        matched_dl.append(float(matched_result["delta_dl_bits"]))
        matched_r2.append(float(matched_result["delta_r2"]))
    return {
        "within": {"delta_dl_bits": within_dl, "delta_r2": within_r2},
        "matched": {"delta_dl_bits": matched_dl, "delta_r2": matched_r2},
    }


def summarize_sign(beta_b_by_fold: list[list[float]], contribution_cor: list[float]) -> dict[str, object]:
    dim_summaries = []
    stable_dims = []
    if beta_b_by_fold:
        width = len(beta_b_by_fold[0])
        for col in range(width):
            values = [row[col] for row in beta_b_by_fold]
            pos = sum(1 for value in values if value > 1e-10)
            neg = sum(1 for value in values if value < -1e-10)
            mean_beta = mean(values)
            sign = "+" if mean_beta > 1e-10 else ("-" if mean_beta < -1e-10 else "0")
            stable = max(pos, neg) >= 4 and sign != "0"
            if stable:
                stable_dims.append(Q_NAMES[col])
            dim_summaries.append({
                "name": Q_NAMES[col],
                "mean_beta": mean_beta,
                "sign": sign,
                "fold_pos": pos,
                "fold_neg": neg,
                "stable_4of5": stable,
            })
    cpos = sum(1 for value in contribution_cor if value > 1e-10)
    cneg = sum(1 for value in contribution_cor if value < -1e-10)
    cmean = mean(contribution_cor)
    return {
        "dimensions": dim_summaries,
        "stable_dimensions": stable_dims,
        "fold_contribution_correlations": contribution_cor,
        "aggregate_direction": "+" if cmean > 1e-10 else ("-" if cmean < -1e-10 else "0"),
        "aggregate_stable_4of5": max(cpos, cneg) >= 4 and abs(cmean) > 1e-10,
        "sign_stable": bool(stable_dims) and max(cpos, cneg) >= 4 and abs(cmean) > 1e-10,
    }


def p_value_greater_equal(null_values: list[float], actual: float) -> float:
    return (1 + sum(1 for value in null_values if value >= actual)) / (len(null_values) + 1)


def verdict_from_stats(
    actual: dict[str, object],
    nulls: dict[str, object],
    base_r2: float,
    beta_sign: dict[str, object],
) -> str:
    actual_dl = float(actual["delta_dl_bits"])
    actual_r2 = float(actual["delta_r2"])
    within = nulls["within"]
    matched = nulls["matched"]
    if not isinstance(within, dict) or not isinstance(matched, dict):
        raise ValueError("null result malformed")
    within95 = percentile_nearest_rank(within["delta_dl_bits"], 0.95)  # type: ignore[arg-type]
    matched95 = percentile_nearest_rank(matched["delta_dl_bits"], 0.95)  # type: ignore[arg-type]
    p_within = p_value_greater_equal(within["delta_dl_bits"], actual_dl)  # type: ignore[arg-type]
    p_matched = p_value_greater_equal(matched["delta_dl_bits"], actual_dl)  # type: ignore[arg-type]
    if actual_dl <= 0.0 or actual_r2 <= 0.0 or not beta_sign["sign_stable"]:
        return "public_perturbation_B_window_null"
    if actual_dl > within95 and actual_dl > matched95 and p_within <= 0.05 and p_matched <= 0.05:
        return "bacterial_synonymous_protein_output_candidate"
    if actual_dl <= matched95 or p_matched > 0.05:
        return "composition_artifact"
    if base_r2 > 0.0 and (actual_dl <= within95 or p_within > 0.05):
        return "causal_execution_only"
    return "public_perturbation_B_window_null"


def main() -> None:
    started = time.time()
    checks: dict[str, object] = {
        "data_parsed": False,
        "b_window_computed": False,
        "controls_built": False,
        "ladder_L2_L3_heldout": False,
        "nulls_run": False,
        "protein_output_verdict": False,
    }
    try:
        rows = parse_xlsx_rows(XLSX_PATH)
        checks["data_parsed"] = {
            "passed": True,
            "xlsx": str(XLSX_PATH),
            "compact_json": str(COMPACT_JSON_PATH),
            "n_rows": len(rows),
        }
        if len(rows) < 200:
            result = {
                "n_variants": len(rows),
                "actual_B": 0,
                "delta_r2": 0.0,
                "delta_dl_bits": 0.0,
                "p_within": 1.0,
                "p_matched": 1.0,
                "null95": {},
                "beta_b_sign": {},
                "cannot_claim": ["数据量不足，无法运行规定的 5-fold + B>=200 null。"],
            }
            emit("needs_data", checks, "public_perturbation_B_window_null", result, started)

        dataset = build_dataset(rows)
        b_matrix = dataset["b_matrix"]
        controls = dataset["controls"]
        targets = dataset["targets"]
        if not isinstance(b_matrix, list) or not isinstance(controls, list) or not isinstance(targets, list):
            raise ValueError("dataset malformed")
        checks["b_window_computed"] = {
            "passed": True,
            "dimension": len(b_matrix[0]) if b_matrix else 0,
            "q_names": Q_NAMES,
            "scope": "whole_CDS_counts_not_12_codon_window",
            "source": "sibling Q6/Q9 aa-fiber-centered synonymous residual construction copied into stdlib script",
        }
        checks["controls_built"] = {
            "passed": True,
            "controls": dataset["control_names"],
            "cai": "Sharp CAI from E.coli K-12 MG1655 genome-derived CDS RSCU weights, CAI=exp(mean log w_c) over sense codons",
            "cai_source": dataset["genome_reference"]["path"] if isinstance(dataset.get("genome_reference"), dict) else "",
            "tai": "proxy only: genome RSCU weight adjusted by genome GC3-ending availability; no E.coli tRNA-copy table used",
            "mfe": "skipped_stdlib_no_thermodynamics",
        }

        folds = make_folds(controls, targets)
        base_preds, base_betas = base_cv_predictions(targets, folds)
        actual = evaluate_b_matrix(targets, b_matrix, folds, base_preds)
        base_sse = float(actual["base_sse"])
        full_sse = float(actual["full_sse"])
        total_tss = tss(targets)
        base_r2 = 1.0 - base_sse / total_tss
        full_r2 = 1.0 - full_sse / total_tss
        beta_sign = summarize_sign(actual["beta_b_by_fold"], actual["fold_contribution_cor"])  # type: ignore[arg-type]
        checks["ladder_L2_L3_heldout"] = {
            "passed": True,
            "fold_count": FOLD_COUNT,
            "fold_sizes": [len(fold.test) for fold in folds],
            "residualization": "b_perp = b - Ehat[b|C] fit on each train fold, then applied to train/test fold",
            "L2_base_r2": base_r2,
            "L3_full_r2": full_r2,
            "delta_r2": actual["delta_r2"],
            "delta_dl_bits": actual["delta_dl_bits"],
            "delta_dl_cost": "0.5*n*log2(SSE_L2/SSE_L3) - 0.5*9*log2(n)",
            "base_control_betas_by_fold": base_betas,
        }

        nulls = run_nulls(targets, b_matrix, controls, folds, base_preds)
        within = nulls["within"]
        matched = nulls["matched"]
        if not isinstance(within, dict) or not isinstance(matched, dict):
            raise ValueError("null result malformed")
        actual_dl = float(actual["delta_dl_bits"])
        actual_r2 = float(actual["delta_r2"])
        p_within = p_value_greater_equal(within["delta_dl_bits"], actual_dl)  # type: ignore[arg-type]
        p_matched = p_value_greater_equal(matched["delta_dl_bits"], actual_dl)  # type: ignore[arg-type]
        null95 = {
            "within_library_shuffle": {
                "delta_dl_bits": percentile_nearest_rank(within["delta_dl_bits"], 0.95),  # type: ignore[arg-type]
                "delta_r2": percentile_nearest_rank(within["delta_r2"], 0.95),  # type: ignore[arg-type]
            },
            "matched_CAI_tAI_GC3_bin_shuffle": {
                "delta_dl_bits": percentile_nearest_rank(matched["delta_dl_bits"], 0.95),  # type: ignore[arg-type]
                "delta_r2": percentile_nearest_rank(matched["delta_r2"], 0.95),  # type: ignore[arg-type]
            },
        }
        checks["nulls_run"] = {
            "passed": True,
            "actual_B": NULL_B,
            "within_library_shuffle_B": NULL_B,
            "matched_CAI_tAI_GC3_bin_shuffle_B": NULL_B,
            "p_within": p_within,
            "p_matched": p_matched,
            "null95": null95,
        }

        candidate_verdict = verdict_from_stats(actual, nulls, base_r2, beta_sign)
        real_cai_robust = candidate_verdict == "bacterial_synonymous_protein_output_candidate"
        verdict = candidate_verdict if real_cai_robust else "causal_execution_only"
        checks["protein_output_verdict"] = {
            "passed": True,
            "rule": "candidate survives real genome CAI iff b_perp improves held-out protein output beyond C including E.coli genome CAI, exceeds both null95 classes, p<=0.05 for both nulls, and beta/contribution signs are stable; otherwise honest downgrade to causal_execution_only",
            "verdict": verdict,
            "pre_downgrade_verdict": candidate_verdict,
            "real_cai_robust": real_cai_robust,
        }
        genome_ref = dataset["genome_reference"]
        if not isinstance(genome_ref, dict):
            raise ValueError("genome reference malformed")
        genome_payload = genome_ref["payload"]
        if not isinstance(genome_payload, dict):
            raise ValueError("genome CAI payload malformed")
        cai_source = {
            "path": genome_ref["path"],
            "source": genome_payload.get("source"),
            "organism": genome_payload.get("organism"),
            "sharp_cai_definition": genome_payload.get("sharp_cai_definition"),
            "reference_set_note": genome_payload.get("reference_set_note"),
            "cds_records_used": genome_payload.get("cds_records_used"),
            "repo_n_cds_records": genome_payload.get("repo_n_cds_records"),
            "repo_n_joined": genome_payload.get("repo_n_joined"),
            "total_sense_codons": genome_payload.get("total_sense_codons"),
            "gzip_prefix_recovery_note": genome_payload.get("gzip_prefix_recovery_note"),
        }
        target_metrics = {
            "log_mRFP_Mean_Corrected": {
                "base_r2_L2_controls": base_r2,
                "full_r2_L3_controls_plus_b_perp": full_r2,
                "delta_r2": actual_r2,
                "delta_dl_bits": actual_dl,
                "p_within": p_within,
                "p_matched": p_matched,
                "null95": null95,
                "real_cai_robust": real_cai_robust,
            }
        }
        cannot_claim = [
            "E.coli 非 yeast；本结果不能直接声称 Shen2022 yeast 机制复现。",
            "无 mRNA 测量，故非 beyond-mRNA escape；这里只能评价 protein output。",
            "细菌翻译上下文与 yeast 不同，不能外推到真核翻译调控。",
            "这里是整 CDS B 特征，不是局部 12-codon window B_window 动态定位。",
            "MFE 未控：纯 stdlib 无 RNA 热力学模型，因此 cannot_claim RNA 结构独立性。",
            "CAI 使用 E.coli K-12 MG1655 genome-derived CDS RSCU weights；参考集为 joined CDS codon counts，不是 HEG-only。",
            "repo JSON 的 cds_payload_raw_prefix_base64 是 gzip raw prefix，不能还原完整 FASTA；本次使用 JSON joined 记录内 3739 条 CDS codon_counts，比 decompressed_prefix_text 覆盖更多 CDS。",
            "tAI 仍是 genome RSCU + GC3 ending availability proxy；没有使用 E.coli tRNA copy 或 wobble 实测表。",
        ]
        result = {
            "n_variants": len(rows),
            "actual_B": NULL_B,
            "cai_source": cai_source,
            "real_cai_robust": real_cai_robust,
            "real_cai_absorbs": not real_cai_robust,
            "real_cai_vs_proxy_corr": dataset["real_cai_vs_proxy_corr"],
            "per_target": target_metrics,
            "delta_r2": actual_r2,
            "delta_dl_bits": actual_dl,
            "p_within": p_within,
            "p_matched": p_matched,
            "null95": null95,
            "beta_b_sign": beta_sign,
            "base_r2_L2_controls": base_r2,
            "full_r2_L3_controls_plus_b_perp": full_r2,
            "sse": {"L2": base_sse, "L3": full_sse},
            "compact_json": str(COMPACT_JSON_PATH),
            "cannot_claim": cannot_claim,
        }
        emit("passed", checks, verdict, result, started)
    except Exception as exc:
        result = {
            "n_variants": 0,
            "actual_B": 0,
            "delta_r2": 0.0,
            "delta_dl_bits": 0.0,
            "p_within": 1.0,
            "p_matched": 1.0,
            "null95": {},
            "beta_b_sign": {},
            "cannot_claim": [f"failed: {type(exc).__name__}: {exc}"],
        }
        emit("failed", checks, "public_perturbation_B_window_null", result, started)


if __name__ == "__main__":
    main()

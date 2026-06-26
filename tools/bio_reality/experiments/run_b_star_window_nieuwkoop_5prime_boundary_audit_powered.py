#!/usr/bin/env python3
"""Nieuwkoop E.coli mRFP 5' initiation/structure boundary audit.

纯 stdlib 单文件脚本。读取 Nieuwkoop S2 Validated Data 与 E.coli genome CAI
weights，复用原实验的 9D aa-fiber-centered B 构造，拆成 codon 2-8 的
B_start 与 codon 9+ 的 B_downstream。用 library-block 5-fold held-out ridge
ladder 评估 5' proxy / first-8 controls 之后 downstream 是否仍有 protein
output 信号，并用 library/GC-bin block permutation null 审计。
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


EXPERIMENT_ID = "b_star_window_nieuwkoop_5prime_boundary_audit_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_nieuwkoop_5prime_boundary_audit_powered"

XLSX_PATH = pathlib.Path("tools/bio_reality/data/nieuwkoop_mrfp.xlsx")
CAI_WEIGHTS_PATH = pathlib.Path("tools/bio_reality/data/ecoli_genome_cai_weights.json")
COMPACT_JSON_PATH = pathlib.Path("/tmp/nieuwkoop_mrfp_5prime_boundary_compact.json")

FOLD_COUNT = 5
NULL_B = 200
RIDGE = 1e-6
EPS = 1e-12
SEED = "sha256:b_star_window_nieuwkoop_5prime_boundary_audit_powered:deterministic"

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


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(indices: list[int], material: str) -> list[int]:
    out = list(indices)
    for index in range(len(out) - 1, 0, -1):
        digest = stable_digest(f"{material}|i={index}|n={len(out)}")
        swap = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def emit(status: str, checks: dict[str, object], verdict: str, result: dict[str, object], started: float) -> None:
    result["runtime_sec"] = round(time.time() - started, 3)
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


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


def sse(y: list[float], pred: list[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(y, pred))


def tss(y: list[float]) -> float:
    center = mean(y)
    return max(EPS, sum((value - center) ** 2 for value in y))


def r2_from_sse(y: list[float], model_sse: float) -> float:
    return 1.0 - model_sse / tss(y)


def delta_ll(base_sse: float, full_sse: float, n: int) -> float:
    return 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS))


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


def cholesky_solve_from_lower(lower: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    y = [0.0 for _ in range(n)]
    for i in range(n):
        y[i] = (rhs[i] - sum(lower[i][k] * y[k] for k in range(i))) / lower[i][i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - sum(lower[k][i] * x[k] for k in range(i + 1, n))) / lower[i][i]
    return x


def ridge_lower_from_xtx(xtx: list[list[float]], ridge: float = RIDGE) -> list[list[float]]:
    n = len(xtx)
    jitter = ridge
    for _attempt in range(8):
        adjusted = [list(row) for row in xtx]
        for i in range(n):
            adjusted[i][i] += jitter
        try:
            return cholesky_decompose(adjusted)
        except ValueError:
            jitter *= 10.0
    raise ValueError("Cholesky ridge factorization failed")


def ridge_fit(x_rows: list[list[float]], y: list[float], ridge: float = RIDGE) -> list[float]:
    if not x_rows:
        return []
    width = len(x_rows[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, value in zip(x_rows, y):
        for i in range(width):
            rhs[i] += row[i] * value
            ri = row[i]
            for j in range(i, width):
                xtx[i][j] += ri * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    lower = ridge_lower_from_xtx(xtx, ridge)
    return cholesky_solve_from_lower(lower, rhs)


def predict_rows(x_rows: list[list[float]], beta: list[float]) -> list[float]:
    return [dot(row, beta) for row in x_rows]


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
        if any(STANDARD_CODE_RNA.get(codon) is None for codon in codons):
            skipped += 1
            continue
        if any(STANDARD_CODE_RNA[codon] == "*" for codon in codons[:-1]):
            skipped += 1
            continue
        rows.append({
            "id": len(rows),
            "xlsx_row": raw_index,
            "library": str(raw.get(header["Header"], "")),
            "plate_location": str(raw.get(header["Plate+location"], "")),
            "mrfp_mean_corrected": corrected,
            "log_protein_output": math.log(corrected),
            "sequence": seq,
        })
    COMPACT_JSON_PATH.write_text(json.dumps({
        "experiment_id": EXPERIMENT_ID,
        "source_xlsx": str(path),
        "sheet": "S2 Validated Data",
        "target": "natural_log(mRFP Mean Corrected), positive validated rows only",
        "n_variants": len(rows),
        "skipped_rows": skipped,
        "rows": rows,
    }, ensure_ascii=False, sort_keys=True, separators=(",", ":")), encoding="utf-8")
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
    denoms = {name: math.sqrt(sum(projected[name][codon] ** 2 for codon in codons)) for name in Q_NAMES}
    return {"codons": codons, "fibers": fibers, "q_projected": projected, "q_denoms": denoms}


def codon_counts_from_rna_codons(rna_codons: list[str], codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in codons}
    for codon in rna_codons:
        if codon in counts:
            counts[codon] += 1
    return counts


def codon_counts(sequence: str, codons: list[str]) -> dict[str, int]:
    rna_codons = [sequence[i:i + 3].replace("T", "U") for i in range(0, len(sequence), 3)]
    return codon_counts_from_rna_codons(rna_codons, codons)


def q_row_from_counts(counts: dict[str, int], context: dict[str, object]) -> list[float]:
    codons = context["codons"]
    projected = context["q_projected"]
    denoms = context["q_denoms"]
    if not isinstance(codons, list) or not isinstance(projected, dict) or not isinstance(denoms, dict):
        raise ValueError("B context malformed")
    total = sum(counts[codon] for codon in codons)
    if total <= 0:
        return [0.0 for _ in Q_NAMES]
    row = []
    for name in Q_NAMES:
        qvec = projected[name]
        denom = float(denoms[name])
        if not isinstance(qvec, dict):
            raise ValueError("projected B vector malformed")
        row.append(sum((counts[codon] / total) * float(qvec[codon]) for codon in codons) / denom)
    return row


def load_genome_cai_reference(context: dict[str, object]) -> dict[str, object]:
    codons = context["codons"]
    fibers = context["fibers"]
    if not isinstance(codons, list) or not isinstance(fibers, dict):
        raise ValueError("B context malformed")
    payload = json.loads(CAI_WEIGHTS_PATH.read_text(encoding="utf-8"))
    weights = payload.get("weights_rna")
    rscu_dna = payload.get("rscu_dna", {})
    counts_dna = payload.get("codon_counts_dna", {})
    if not isinstance(weights, dict) or len(weights) < 61:
        raise ValueError("genome CAI weights malformed")
    cai_weight = {codon: max(float(weights[codon]), EPS) for codon in codons}
    total_counts = sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons)
    if total_counts <= EPS:
        genome_gc3 = 0.5
    else:
        gc3_counts = sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons if codon[2] in {"G", "C"})
        genome_gc3 = gc3_counts / total_counts
    rscu = {codon: float(rscu_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons}
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
        "path": str(CAI_WEIGHTS_PATH),
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


def nt_gc(seq: str) -> float:
    return (seq.count("G") + seq.count("C")) / len(seq) if seq else 0.0


def nt_purine(seq: str) -> float:
    return (seq.count("A") + seq.count("G")) / len(seq) if seq else 0.0


def longest_complement_stem(seq: str, min_loop: int = 3) -> int:
    comp = {"A": "T", "T": "A", "G": "C", "C": "G"}
    best = 0
    n = len(seq)
    for i in range(n):
        for j in range(i + min_loop + 1, n):
            run = 0
            while i + run < j - run and j - run >= 0 and comp.get(seq[i + run]) == seq[j - run]:
                run += 1
            if run > best:
                best = run
    return best


def pairing_potential(seq: str, min_loop: int = 3) -> float:
    comp = {"A": "T", "T": "A", "G": "C", "C": "G"}
    n = len(seq)
    if n < min_loop + 2:
        return 0.0
    possible = 0
    paired = 0
    for i in range(n):
        for j in range(i + min_loop + 1, n):
            possible += 1
            if comp.get(seq[i]) == seq[j]:
                paired += 1
    return paired / possible if possible else 0.0


def plate_number(plate_location: str) -> str:
    match = re.match(r"(\d+)", plate_location)
    return match.group(1) if match else "unknown"


def build_dataset(rows: list[dict[str, object]]) -> dict[str, object]:
    context = q_context()
    codons = context["codons"]
    if not isinstance(codons, list):
        raise ValueError("B context malformed")
    genome_refs = load_genome_cai_reference(context)
    cai_weight = genome_refs["cai_weight"]
    tai_weight = genome_refs["tai_proxy_weight"]
    if not isinstance(cai_weight, dict) or not isinstance(tai_weight, dict):
        raise ValueError("reference weights malformed")

    libraries = sorted({str(row["library"]) for row in rows})
    library_cols = libraries[1:]
    all_feature_names: dict[str, list[str]] = {}
    step1: list[list[float]] = []
    step2_extra: list[list[float]] = []
    b_start: list[list[float]] = []
    b_downstream: list[list[float]] = []
    b_downstream_exclude_2_15: list[list[float]] = []
    targets: list[float] = []
    library_blocks: list[str] = []
    gc3_values: list[float] = []
    first8_comp_names = [f"first8_comp_{codon}" for codon in codons]
    structure_names = [
        "fiveprime_30nt_GC",
        "fiveprime_30nt_purine",
        "fiveprime_30nt_pairing_potential",
        "fiveprime_30nt_longest_stem",
        "fiveprime_codons_1_8_GC",
    ]
    first8_names = [
        "codons_2_8_GC",
        "codons_2_8_purine",
    ] + first8_comp_names
    step1_names = [f"library::{lib}" for lib in library_cols] + [
        "CAI_Ecoli_K12_genome_RSCU",
        "tAI_proxy_Ecoli_K12_genome_RSCU_GC3",
        "GC",
        "GC3",
        "log_CDS_length",
    ]

    for row in rows:
        seq = str(row["sequence"])
        rna_codons = [seq[i:i + 3].replace("T", "U") for i in range(0, len(seq), 3)]
        counts = codon_counts_from_rna_codons(rna_codons, codons)
        total_codons = sum(counts.values())
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total_codons
        gc = nt_gc(seq)
        cai = geometric_index(counts, cai_weight)  # type: ignore[arg-type]
        tai_proxy = geometric_index(counts, tai_weight)  # type: ignore[arg-type]
        lib = str(row["library"])
        lib_dummies = [1.0 if lib == col else 0.0 for col in library_cols]
        step1.append(lib_dummies + [cai, tai_proxy, gc, gc3, math.log(len(seq))])

        # 1-based codon positions: start codon is codon 1, initiation-like audit is codon 2-8.
        codons_2_8 = rna_codons[1:8]
        codons_9_end = rna_codons[8:]
        codons_16_end = rna_codons[15:]
        b_start.append(q_row_from_counts(codon_counts_from_rna_codons(codons_2_8, codons), context))
        b_downstream.append(q_row_from_counts(codon_counts_from_rna_codons(codons_9_end, codons), context))
        b_downstream_exclude_2_15.append(q_row_from_counts(codon_counts_from_rna_codons(codons_16_end, codons), context))

        first8_seq = "".join(c.replace("U", "T") for c in codons_2_8)
        first8_counts = codon_counts_from_rna_codons(codons_2_8, codons)
        first8_total = max(1, sum(first8_counts.values()))
        first8_comp = [first8_counts[codon] / first8_total for codon in codons]
        fiveprime30 = seq[:30]
        codons1_8_seq = seq[:24]
        structure = [
            nt_gc(fiveprime30),
            nt_purine(fiveprime30),
            pairing_potential(fiveprime30),
            float(longest_complement_stem(fiveprime30)),
            nt_gc(codons1_8_seq),
        ]
        step2_extra.append(structure + [nt_gc(first8_seq), nt_purine(first8_seq)] + first8_comp)
        targets.append(float(row["log_protein_output"]))
        library_blocks.append(f"{lib}|plate{plate_number(str(row['plate_location']))}")
        gc3_values.append(gc3)

    all_feature_names["step1"] = step1_names
    all_feature_names["step2_extra"] = structure_names + first8_names
    all_feature_names["b"] = Q_NAMES
    return {
        "context": context,
        "genome_reference": genome_refs,
        "libraries": libraries,
        "step1": step1,
        "step2_extra": step2_extra,
        "step2": [a + b for a, b in zip(step1, step2_extra)],
        "b_start": b_start,
        "b_downstream": b_downstream,
        "b_downstream_exclude_2_15": b_downstream_exclude_2_15,
        "targets": targets,
        "library_blocks": library_blocks,
        "gc3_values": gc3_values,
        "feature_names": all_feature_names,
    }


def standardize_train_test(matrix: list[list[float]], train: list[int], test: list[int]) -> tuple[list[list[float]], list[list[float]], list[tuple[float, float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test], []
    width = len(matrix[0])
    stats: list[tuple[float, float]] = []
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


class Fold:
    def __init__(self, fold_id: int, train: list[int], test: list[int]) -> None:
        self.fold_id = fold_id
        self.train = train
        self.test = test


def make_block_folds(rows: list[dict[str, object]], targets: list[float]) -> list[Fold]:
    block_to_indices: dict[str, list[int]] = {}
    block_library: dict[str, str] = {}
    for index, row in enumerate(rows):
        lib = str(row["library"])
        block = f"{lib}|plate{plate_number(str(row['plate_location']))}"
        block_to_indices.setdefault(block, []).append(index)
        block_library[block] = lib
    fold_blocks: list[list[str]] = [[] for _ in range(FOLD_COUNT)]
    for lib in sorted({str(row["library"]) for row in rows}):
        blocks = [block for block in block_to_indices if block_library[block] == lib]
        blocks.sort(key=lambda b: (mean([targets[i] for i in block_to_indices[b]]), b))
        for rank, block in enumerate(blocks):
            fold_blocks[rank % FOLD_COUNT].append(block)
    folds: list[Fold] = []
    all_indices = list(range(len(rows)))
    for fold_id in range(FOLD_COUNT):
        test_blocks = set(fold_blocks[fold_id])
        test = []
        for block in deterministic_permutation(sorted(test_blocks), f"{SEED}|fold-block-order|{fold_id}"):
            test.extend(block_to_indices[block])
        test = deterministic_permutation(test, f"{SEED}|fold-test-indices|{fold_id}")
        test_set = set(test)
        train = [index for index in all_indices if index not in test_set]
        folds.append(Fold(fold_id, train, test))
    return folds


class PreparedDesign:
    def __init__(self, features: list[list[float]], targets: list[float], folds: list[Fold], name: str) -> None:
        self.features = features
        self.targets = targets
        self.folds = folds
        self.name = name
        self.preds = [0.0 for _ in targets]
        self.train_preds_by_fold: list[list[float]] = []
        self.test_preds_by_fold: list[list[float]] = []
        self.x_train_by_fold: list[list[list[float]]] = []
        self.x_test_by_fold: list[list[list[float]]] = []
        self.lower_by_fold: list[list[list[float]]] = []
        self.betas_by_fold: list[list[float]] = []
        self._prepare()

    def _prepare(self) -> None:
        for fold in self.folds:
            raw_train, raw_test, _stats = standardize_train_test(self.features, fold.train, fold.test)
            x_train = [[1.0] + row for row in raw_train]
            x_test = [[1.0] + row for row in raw_test]
            width = len(x_train[0])
            xtx = [[0.0 for _ in range(width)] for _ in range(width)]
            rhs = [0.0 for _ in range(width)]
            y_train = [self.targets[i] for i in fold.train]
            for row, value in zip(x_train, y_train):
                for i in range(width):
                    rhs[i] += row[i] * value
                    ri = row[i]
                    for j in range(i, width):
                        xtx[i][j] += ri * row[j]
            for i in range(width):
                for j in range(i):
                    xtx[i][j] = xtx[j][i]
            lower = ridge_lower_from_xtx(xtx, RIDGE)
            beta = cholesky_solve_from_lower(lower, rhs)
            train_preds = predict_rows(x_train, beta)
            test_preds = predict_rows(x_test, beta)
            for local, index in enumerate(fold.test):
                self.preds[index] = test_preds[local]
            self.train_preds_by_fold.append(train_preds)
            self.test_preds_by_fold.append(test_preds)
            self.x_train_by_fold.append(x_train)
            self.x_test_by_fold.append(x_test)
            self.lower_by_fold.append(lower)
            self.betas_by_fold.append(beta)

    @property
    def model_sse(self) -> float:
        return sse(self.targets, self.preds)

    @property
    def model_r2(self) -> float:
        return r2_from_sse(self.targets, self.model_sse)


def solve_projection(x_rows: list[list[float]], lower: list[list[float]], values: list[float]) -> list[float]:
    width = len(x_rows[0])
    rhs = [0.0 for _ in range(width)]
    for row, value in zip(x_rows, values):
        for i in range(width):
            rhs[i] += row[i] * value
    return cholesky_solve_from_lower(lower, rhs)


def standardize_residual_columns(train_cols: list[list[float]], test_cols: list[list[float]]) -> tuple[list[list[float]], list[list[float]]]:
    if not train_cols:
        return [], []
    width = len(train_cols)
    train_n = len(train_cols[0])
    test_n = len(test_cols[0])
    stats = []
    for col in range(width):
        center = mean(train_cols[col])
        sd = math.sqrt(variance(train_cols[col]))
        if sd <= EPS:
            sd = 1.0
        stats.append((center, sd))
    train_rows = [[(train_cols[col][row] - stats[col][0]) / stats[col][1] for col in range(width)] for row in range(train_n)]
    test_rows = [[(test_cols[col][row] - stats[col][0]) / stats[col][1] for col in range(width)] for row in range(test_n)]
    return train_rows, test_rows


def evaluate_increment(targets: list[float], baseline: PreparedDesign, increment: list[list[float]], label: str) -> dict[str, object]:
    preds = [0.0 for _ in targets]
    beta_by_fold: list[list[float]] = []
    contribution_cor: list[float] = []
    for fold_index, fold in enumerate(baseline.folds):
        x_train = baseline.x_train_by_fold[fold_index]
        x_test = baseline.x_test_by_fold[fold_index]
        lower = baseline.lower_by_fold[fold_index]
        width = len(increment[0])
        train_resid_cols: list[list[float]] = []
        test_resid_cols: list[list[float]] = []
        for col in range(width):
            z_train = [increment[i][col] for i in fold.train]
            z_test = [increment[i][col] for i in fold.test]
            beta_z = solve_projection(x_train, lower, z_train)
            pred_train = predict_rows(x_train, beta_z)
            pred_test = predict_rows(x_test, beta_z)
            train_resid_cols.append([z_train[i] - pred_train[i] for i in range(len(z_train))])
            test_resid_cols.append([z_test[i] - pred_test[i] for i in range(len(z_test))])
        z_train_rows, z_test_rows = standardize_residual_columns(train_resid_cols, test_resid_cols)
        y_train_resid = [
            targets[index] - baseline.train_preds_by_fold[fold_index][local]
            for local, index in enumerate(fold.train)
        ]
        gamma = ridge_fit(z_train_rows, y_train_resid, RIDGE)
        beta_by_fold.append(gamma)
        z_test_contrib = predict_rows(z_test_rows, gamma)
        y_test = [targets[i] for i in fold.test]
        contribution_cor.append(pearson(z_test_contrib, y_test))
        for local, index in enumerate(fold.test):
            preds[index] = baseline.test_preds_by_fold[fold_index][local] + z_test_contrib[local]
    base_sse = baseline.model_sse
    full_sse = sse(targets, preds)
    return {
        "label": label,
        "preds": preds,
        "base_sse": base_sse,
        "full_sse": full_sse,
        "delta_r2": (base_sse - full_sse) / tss(targets),
        "delta_ll": delta_ll(base_sse, full_sse, len(targets)),
        "full_r2": r2_from_sse(targets, full_sse),
        "beta_by_fold": beta_by_fold,
        "fold_contribution_cor": contribution_cor,
    }


def summarize_sign(beta_by_fold: list[list[float]], contribution_cor: list[float], names: list[str]) -> dict[str, object]:
    dim_summaries = []
    stable_dims = []
    if beta_by_fold:
        width = len(beta_by_fold[0])
        for col in range(width):
            values = [row[col] for row in beta_by_fold]
            pos = sum(1 for value in values if value > 1e-10)
            neg = sum(1 for value in values if value < -1e-10)
            mean_beta = mean(values)
            sign = "+" if mean_beta > 1e-10 else ("-" if mean_beta < -1e-10 else "0")
            stable = max(pos, neg) >= 4 and sign != "0"
            if stable:
                stable_dims.append(names[col] if col < len(names) else f"dim_{col}")
            dim_summaries.append({
                "name": names[col] if col < len(names) else f"dim_{col}",
                "mean_beta": mean_beta,
                "sign": sign,
                "fold_pos": pos,
                "fold_neg": neg,
                "stable_4of5": stable,
            })
    cpos = sum(1 for value in contribution_cor if value > 1e-10)
    cneg = sum(1 for value in contribution_cor if value < -1e-10)
    cmean = mean(contribution_cor)
    aggregate_stable = max(cpos, cneg) >= 4 and abs(cmean) > 1e-10
    return {
        "dimensions": dim_summaries,
        "stable_dimensions": stable_dims,
        "fold_contribution_correlations": contribution_cor,
        "aggregate_direction": "+" if cmean > 1e-10 else ("-" if cmean < -1e-10 else "0"),
        "aggregate_stable_4of5": aggregate_stable,
        "sign_stable": bool(stable_dims) and aggregate_stable,
    }


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


def block_permuted_matrix(matrix: list[list[float]], rows: list[dict[str, object]], gc3_values: list[float], trial: int) -> list[list[float]]:
    cuts = quantile_cuts(gc3_values, 5)
    bins: dict[tuple[str, int], list[int]] = {}
    for index, row in enumerate(rows):
        key = (str(row["library"]), bin_index(gc3_values[index], cuts))
        bins.setdefault(key, []).append(index)
    out = [list(row) for row in matrix]
    for key, indices in sorted(bins.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|library-gc-block-perm|trial={trial}|block={key}")
        for dest, src in zip(indices, permuted):
            out[dest] = list(matrix[src])
    return out


def p_value_greater_equal(null_values: list[float], actual: float) -> float:
    return (1 + sum(1 for value in null_values if value >= actual)) / (len(null_values) + 1)


def concat_matrix(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [a + b for a, b in zip(left, right)]


def main() -> None:
    started = time.time()
    checks: dict[str, object] = {
        "data_parsed": False,
        "b_start_downstream_split": False,
        "fiveprime_proxy_and_first8_controls": False,
        "ladder_step1_2_3_heldout": False,
        "block_null": False,
        "boundary_verdict": False,
    }
    base_cannot_claim = [
        "5' structure 是 GC/pairing proxy 非真 RNA MFE/accessibility(stdlib 限制)，故 initiation 控制不完整。",
        "E.coli reporter；不能外推到 yeast 或其它宿主。",
        "无 mRNA 测量；不能声称 beyond-mRNA escape 或 mRNA abundance/decay 机制。",
        "整 CDS reporter 变体；B_downstream 是 codon 9+ 聚合特征，不是逐窗口定位图。",
    ]
    try:
        if not XLSX_PATH.exists() or not CAI_WEIGHTS_PATH.exists():
            emit("needs_data", checks, "needs_data", {
                "n_variants": 0,
                "actual_B": 0,
                "step1_r2": 0.0,
                "step2_r2": 0.0,
                "step3_r2": 0.0,
                "b_start_delta_ll": 0.0,
                "b_downstream_delta_ll": 0.0,
                "b_downstream_p_block": 1.0,
                "b_downstream_null95": 0.0,
                "sign_stable": False,
                "cannot_claim": base_cannot_claim + ["repo-relative Nieuwkoop xlsx 或 E.coli genome CAI JSON 未找到。"],
            }, started)

        rows = parse_xlsx_rows(XLSX_PATH)
        checks["data_parsed"] = {
            "passed": True,
            "xlsx": str(XLSX_PATH),
            "sheet": "S2 Validated Data",
            "compact_json": str(COMPACT_JSON_PATH),
            "n_rows": len(rows),
        }
        if len(rows) < 200:
            emit("needs_data", checks, "needs_data", {
                "n_variants": len(rows),
                "actual_B": 0,
                "step1_r2": 0.0,
                "step2_r2": 0.0,
                "step3_r2": 0.0,
                "b_start_delta_ll": 0.0,
                "b_downstream_delta_ll": 0.0,
                "b_downstream_p_block": 1.0,
                "b_downstream_null95": 0.0,
                "sign_stable": False,
                "cannot_claim": base_cannot_claim + ["数据量不足，无法运行规定的 5-fold + B>=200 null。"],
            }, started)

        dataset = build_dataset(rows)
        targets = dataset["targets"]
        step1 = dataset["step1"]
        step2 = dataset["step2"]
        b_start = dataset["b_start"]
        b_downstream = dataset["b_downstream"]
        b_downstream_exclude_2_15 = dataset["b_downstream_exclude_2_15"]
        gc3_values = dataset["gc3_values"]
        if not all(isinstance(x, list) for x in [targets, step1, step2, b_start, b_downstream, b_downstream_exclude_2_15, gc3_values]):
            raise ValueError("dataset malformed")
        checks["b_start_downstream_split"] = {
            "passed": True,
            "b_dimension_each": len(b_start[0]) if b_start else 0,
            "q_names": Q_NAMES,
            "B_start": "codon positions 2-8, 1-based; start ATG/codon1 excluded",
            "B_downstream": "codon positions 9-end; terminal stop ignored by sense-codon counts",
            "also_computed": "B_downstream_exclude_2_15 = codon positions 16-end",
        }
        feature_names = dataset["feature_names"]
        checks["fiveprime_proxy_and_first8_controls"] = {
            "passed": True,
            "step1_controls": feature_names["step1"] if isinstance(feature_names, dict) else [],
            "step2_added_controls": feature_names["step2_extra"] if isinstance(feature_names, dict) else [],
            "structure_proxy": "5' 30nt GC, purine, simple complement pairing potential, longest rough stem, codons1-8 GC",
            "first8_controls": "codon2-8 GC, purine, and 61-codon composition frequencies",
            "cannot_claim": base_cannot_claim[0],
        }

        folds = make_block_folds(rows, targets)  # type: ignore[arg-type]
        step1_design = PreparedDesign(step1, targets, folds, "step1_library_cai_tai_gc3_length")  # type: ignore[arg-type]
        step2_design = PreparedDesign(step2, targets, folds, "step2_plus_5prime_proxy_first8")  # type: ignore[arg-type]
        step2_plus_b_start_features = concat_matrix(step2, b_start)  # type: ignore[arg-type]
        step2_plus_b_start_design = PreparedDesign(step2_plus_b_start_features, targets, folds, "step2_plus_B_start")  # type: ignore[arg-type]

        start_increment = evaluate_increment(targets, step2_design, b_start, "B_start_after_step2")  # type: ignore[arg-type]
        downstream_increment = evaluate_increment(targets, step2_plus_b_start_design, b_downstream, "B_downstream_after_step2_and_B_start")  # type: ignore[arg-type]
        combined_increment = evaluate_increment(targets, step2_design, concat_matrix(b_start, b_downstream), "B_start_plus_B_downstream_after_step2")  # type: ignore[arg-type]
        downstream_16_increment = evaluate_increment(targets, step2_plus_b_start_design, b_downstream_exclude_2_15, "B_downstream_16plus_after_step2_and_B_start")  # type: ignore[arg-type]

        step1_sse = step1_design.model_sse
        step2_sse = step2_design.model_sse
        step3_sse = float(combined_increment["full_sse"])
        step1_r2 = step1_design.model_r2
        step2_r2 = step2_design.model_r2
        step3_r2 = r2_from_sse(targets, step3_sse)
        checks["ladder_step1_2_3_heldout"] = {
            "passed": True,
            "fold_count": FOLD_COUNT,
            "folding": "library-block held-out: blocks are Header/library x plate number; all rows in a block stay in the same fold",
            "fold_sizes": [len(fold.test) for fold in folds],
            "fold_block_counts": [len({f'{rows[i]['library']}|plate{plate_number(str(rows[i]['plate_location']))}' for i in fold.test}) for fold in folds],
            "step1": "protein ~ library + E.coli genome CAI + tAI_proxy + whole-CDS GC + GC3 + log_length",
            "step2": "step1 + 5' structure proxy + codon2-8 GC/purine + codon2-8 61-codon composition",
            "step3": "step2 + B_start + B_downstream",
            "step1_r2": step1_r2,
            "step2_r2": step2_r2,
            "step3_r2": step3_r2,
            "step2_delta_r2_vs_step1": (step1_sse - step2_sse) / tss(targets),
            "step2_delta_ll_vs_step1": delta_ll(step1_sse, step2_sse, len(targets)),
            "step3_delta_r2_vs_step2": float(combined_increment["delta_r2"]),
            "step3_delta_ll_vs_step2": float(combined_increment["delta_ll"]),
            "b_start_delta_r2_after_step2": float(start_increment["delta_r2"]),
            "b_start_delta_ll_after_step2": float(start_increment["delta_ll"]),
            "b_downstream_delta_r2_after_step2_and_B_start": float(downstream_increment["delta_r2"]),
            "b_downstream_delta_ll_after_step2_and_B_start": float(downstream_increment["delta_ll"]),
            "b_downstream_16plus_delta_ll_after_step2_and_B_start": float(downstream_16_increment["delta_ll"]),
        }

        null_delta_ll: list[float] = []
        null_delta_r2: list[float] = []
        for trial in range(NULL_B):
            permuted_downstream = block_permuted_matrix(b_downstream, rows, gc3_values, trial)  # type: ignore[arg-type]
            null_result = evaluate_increment(targets, step2_plus_b_start_design, permuted_downstream, f"block_null_{trial}")  # type: ignore[arg-type]
            null_delta_ll.append(float(null_result["delta_ll"]))
            null_delta_r2.append(float(null_result["delta_r2"]))
        b_downstream_delta_ll = float(downstream_increment["delta_ll"])
        b_downstream_null95 = percentile_nearest_rank(null_delta_ll, 0.95)
        b_downstream_p_block = p_value_greater_equal(null_delta_ll, b_downstream_delta_ll)
        downstream_sign = summarize_sign(downstream_increment["beta_by_fold"], downstream_increment["fold_contribution_cor"], Q_NAMES)  # type: ignore[arg-type]
        start_sign = summarize_sign(start_increment["beta_by_fold"], start_increment["fold_contribution_cor"], Q_NAMES)  # type: ignore[arg-type]
        sign_stable = bool(downstream_sign["sign_stable"])
        checks["block_null"] = {
            "passed": True,
            "actual_B": NULL_B,
            "null": "B_downstream rows permuted within Header/library x GC3 quintile blocks; step2+B_start baseline retained",
            "b_downstream_delta_ll": b_downstream_delta_ll,
            "b_downstream_null95": b_downstream_null95,
            "b_downstream_p_block": b_downstream_p_block,
            "b_downstream_null_delta_r2_95": percentile_nearest_rank(null_delta_r2, 0.95),
        }

        downstream_active = b_downstream_delta_ll > 0.0 and b_downstream_delta_ll > b_downstream_null95 and sign_stable
        start_active = float(start_increment["delta_ll"]) > 0.0 and bool(start_sign["sign_stable"])
        if downstream_active:
            verdict = "downstream_beyond_optimality_survives"
            verdict_text = "E.coli B_window positive 不只是 5' initiation; downstream codon 选择独立携带 protein-output 信号(beyond-optimality 更强)"
        elif start_active:
            verdict = "initiation_boundary_only"
            verdict_text = "E.coli positive 收窄为 5' initiation/structure-mediated; 非 downstream beyond-optimality 独立轴"
        else:
            verdict = "absorbed_by_5prime"
            verdict_text = "E.coli positive 主要被 5' structure/first-8 解释"
        checks["boundary_verdict"] = {
            "passed": True,
            "rule": "downstream survives iff B_downstream ΔLL>0, exceeds library/GC-bin block-permutation null95, and downstream sign is stable after step2+B_start baseline",
            "verdict": verdict,
            "verdict_text": verdict_text,
            "downstream_active": downstream_active,
            "start_active": start_active,
        }

        genome_ref = dataset["genome_reference"]
        cai_source = {}
        if isinstance(genome_ref, dict) and isinstance(genome_ref.get("payload"), dict):
            payload = genome_ref["payload"]
            cai_source = {
                "path": genome_ref.get("path"),
                "source": payload.get("source"),
                "organism": payload.get("organism"),
                "sharp_cai_definition": payload.get("sharp_cai_definition"),
                "reference_set_note": payload.get("reference_set_note"),
                "cds_records_used": payload.get("cds_records_used"),
                "total_sense_codons": payload.get("total_sense_codons"),
            }
        result = {
            "n_variants": len(rows),
            "actual_B": NULL_B,
            "runtime_sec": 0.0,
            "step1_r2": step1_r2,
            "step2_r2": step2_r2,
            "step3_r2": step3_r2,
            "step2_delta_ll_vs_step1": delta_ll(step1_sse, step2_sse, len(targets)),
            "step3_delta_ll_vs_step2": float(combined_increment["delta_ll"]),
            "b_start_delta_ll": float(start_increment["delta_ll"]),
            "b_start_delta_r2": float(start_increment["delta_r2"]),
            "b_downstream_delta_ll": b_downstream_delta_ll,
            "b_downstream_delta_r2": float(downstream_increment["delta_r2"]),
            "b_downstream_p_block": b_downstream_p_block,
            "b_downstream_null95": b_downstream_null95,
            "b_downstream_16plus_delta_ll": float(downstream_16_increment["delta_ll"]),
            "sign_stable": sign_stable,
            "b_downstream_sign": downstream_sign,
            "b_start_sign": start_sign,
            "cai_source": cai_source,
            "fold_sizes": [len(fold.test) for fold in folds],
            "cannot_claim": base_cannot_claim,
        }
        emit("passed", checks, verdict, result, started)
    except Exception as exc:
        result = {
            "n_variants": 0,
            "actual_B": 0,
            "step1_r2": 0.0,
            "step2_r2": 0.0,
            "step3_r2": 0.0,
            "b_start_delta_ll": 0.0,
            "b_downstream_delta_ll": 0.0,
            "b_downstream_p_block": 1.0,
            "b_downstream_null95": 0.0,
            "sign_stable": False,
            "cannot_claim": base_cannot_claim + [f"failed: {type(exc).__name__}: {exc}"],
        }
        emit("failed", checks, "needs_data", result, started)


if __name__ == "__main__":
    main()

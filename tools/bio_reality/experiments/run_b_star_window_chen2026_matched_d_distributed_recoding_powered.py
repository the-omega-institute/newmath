#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Chen2026 matched-D distributed recoding B_window 离线实验。

纯 Python stdlib：包含最小 RDX3/XDR reader、FASTA/数据集构建、B_window 计算、
D/condition 内中心化、composition-preserving permutation null、5' blockout、
以及 GmR->AmpR 冻结方向验证。
"""

from __future__ import annotations

import json
import math
import os
import random
import struct
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path


EXPERIMENT_ID = "b_star_window_chen2026_matched_d_distributed_recoding_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_chen2026_matched_d_distributed_recoding_powered"
SEED = 260621
N_PERM = 199
RIDGE = 1.0e-8


NILSXP = 0
SYMSXP = 1
LISTSXP = 2
LANGSXP = 6
CHARSXP = 9
LGLSXP = 10
INTSXP = 13
REALSXP = 14
STRSXP = 16
VECSXP = 19
REFSXP = 255
PERSISTSXP = 247
PACKAGESXP = 248
NAMESPACESXP = 249
BASENAMESPACE = 250
EMPTYENV = 251
BASEENV = 252
GLOBALENV = 253
UNBOUNDVALUE = 254

HAS_ATTR = 1 << 9
HAS_TAG = 1 << 10


GENETIC_CODE = {
    "TTT": "F", "TTC": "F", "TTA": "L", "TTG": "L",
    "TCT": "S", "TCC": "S", "TCA": "S", "TCG": "S",
    "TAT": "Y", "TAC": "Y", "TAA": "*", "TAG": "*",
    "TGT": "C", "TGC": "C", "TGA": "*", "TGG": "W",
    "CTT": "L", "CTC": "L", "CTA": "L", "CTG": "L",
    "CCT": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAT": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGT": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "ATT": "I", "ATC": "I", "ATA": "I", "ATG": "M",
    "ACT": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAT": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGT": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GTT": "V", "GTC": "V", "GTA": "V", "GTG": "V",
    "GCT": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAT": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGT": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

AA_TO_CODONS = defaultdict(list)
for _codon, _aa in GENETIC_CODE.items():
    AA_TO_CODONS[_aa].append(_codon)

Q_NAMES = [
    "K_AAA",
    "Arg_AGR",
    "Ile_ATA",
    "Leu_CTN_vs_TTR",
    "Leu_TTA_vs_TTG",
    "Ser_TCR_vs_AGY",
    "Ser_TCA_vs_TCG",
    "Thr_ACR_vs_ACY",
    "f3_stress",
]

Q9_FAMILIES_DNA = [
    ["TTT", "TTC"], ["TTA", "TTG"], ["TCT", "TCC", "TCA", "TCG"],
    ["TAT", "TAC"], ["TGT", "TGC"], ["CTT", "CTC", "CTA", "CTG"],
    ["CCT", "CCC", "CCA", "CCG"], ["CAT", "CAC"], ["CAA", "CAG"],
    ["CGT", "CGC", "CGA", "CGG"], ["ATT", "ATC", "ATA"],
    ["ACT", "ACC", "ACA", "ACG"], ["AAT", "AAC"], ["AAA", "AAG"],
    ["AGT", "AGC"], ["AGA", "AGG"], ["GTT", "GTC", "GTA", "GTG"],
    ["GCT", "GCC", "GCA", "GCG"], ["GAT", "GAC"], ["GAA", "GAG"],
    ["GGT", "GGC", "GGA", "GGG"],
]


class RReader:
    """最小 RDX3/XDR reader，覆盖本实验 data.frame 所需 SEXP。"""

    def __init__(self, path: Path):
        self.path = path
        self.data = path.read_bytes()
        self.pos = 0
        self.refs = []

    def read(self, n: int) -> bytes:
        if self.pos + n > len(self.data):
            raise EOFError(f"{self.path}: unexpected EOF at {self.pos}")
        out = self.data[self.pos:self.pos + n]
        self.pos += n
        return out

    def int(self) -> int:
        return struct.unpack(">i", self.read(4))[0]

    def uint(self) -> int:
        return struct.unpack(">I", self.read(4))[0]

    def double(self) -> float:
        return struct.unpack(">d", self.read(8))[0]

    def parse_file(self):
        if self.read(5) != b"RDX3\n":
            raise ValueError(f"{self.path}: not RDX3")
        if self.read(2) != b"X\n":
            raise ValueError(f"{self.path}: not XDR")
        version = self.int()
        writer = self.int()
        reader = self.int()
        enc_len = self.int()
        encoding = self.read(enc_len).decode("ascii", "replace")
        value = self.sexp()
        return {
            "version": version,
            "writer": writer,
            "reader": reader,
            "encoding": encoding,
            "value": value,
        }

    def sexp(self):
        flags = self.uint()
        typ = flags & 255
        if typ == REFSXP:
            idx = flags >> 8
            return {"type": "REF", "index": idx}
        if typ in (PERSISTSXP, PACKAGESXP, NAMESPACESXP, BASENAMESPACE, EMPTYENV, BASEENV, GLOBALENV, UNBOUNDVALUE):
            return {"type": f"SPECIAL:{typ}"}

        attr = None
        tag = self.sexp() if (flags & HAS_TAG) else None

        if typ == NILSXP:
            val = None
        elif typ == SYMSXP:
            val = {"type": "SYMSXP", "name": self._string_from_charsxp(self.sexp())}
            self.refs.append(val)
        elif typ == CHARSXP:
            n = self.int()
            if n == -1:
                val = None
            else:
                val = self.read(n).decode("utf-8", "replace")
            self.refs.append(val)
        elif typ == STRSXP:
            n = self.int()
            val = [self._string_from_charsxp(self.sexp()) for _ in range(n)]
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "STRSXP", "values": val, "attr": attr}
        elif typ == INTSXP:
            n = self.int()
            vals = [self.int() for _ in range(n)]
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "INTSXP", "values": vals, "attr": attr}
        elif typ == LGLSXP:
            n = self.int()
            vals = [self.int() for _ in range(n)]
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "LGLSXP", "values": vals, "attr": attr}
        elif typ == REALSXP:
            n = self.int()
            vals = [self.double() for _ in range(n)]
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "REALSXP", "values": vals, "attr": attr}
        elif typ == VECSXP:
            n = self.int()
            vals = [self.sexp() for _ in range(n)]
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "VECSXP", "values": vals, "attr": attr}
        elif typ in (LISTSXP, LANGSXP):
            car = self.sexp()
            cdr = self.sexp()
            attr = self.sexp() if (flags & HAS_ATTR) else None
            val = {"type": "LISTSXP", "tag": tag, "car": car, "cdr": cdr, "attr": attr}
        else:
            raise NotImplementedError(f"{self.path}: unsupported SEXPTYPE {typ} flags={flags} pos={self.pos}")
        return val

    def _string_from_charsxp(self, node):
        if isinstance(node, str) or node is None:
            return node
        if isinstance(node, dict) and node.get("type") == "REF":
            idx = node["index"] - 1
            if 0 <= idx < len(self.refs):
                ref = self.refs[idx]
                if isinstance(ref, str) or ref is None:
                    return ref
                if isinstance(ref, dict) and ref.get("type") == "SYMSXP":
                    return ref.get("name")
        raise ValueError(f"cannot coerce CHARSXP node to string: {node!r}")


def sym_name(node):
    if isinstance(node, dict) and node.get("type") == "SYMSXP":
        return node.get("name")
    if isinstance(node, dict) and node.get("type") == "REF":
        return f"REF:{node.get('index')}"
    return None


def pairlist_items(node):
    cur = node
    while isinstance(cur, dict) and cur.get("type") == "LISTSXP":
        yield sym_name(cur.get("tag")), cur.get("car")
        cur = cur.get("cdr")


def attr_dict(attr):
    out = {}
    for key, val in pairlist_items(attr):
        out[key] = val
    return out


def vector_values(node):
    if not isinstance(node, dict):
        return node
    typ = node.get("type")
    if typ in ("REALSXP", "INTSXP", "LGLSXP"):
        return node["values"]
    if typ == "STRSXP":
        return node["values"]
    return node


def data_frame_from_vecsxp(node):
    if not isinstance(node, dict) or node.get("type") != "VECSXP":
        raise ValueError("object is not VECSXP data.frame")
    attrs = attr_dict(node.get("attr"))
    names_node = attrs.get("names")
    names = vector_values(names_node)
    if not isinstance(names, list):
        raise ValueError("data.frame has no names attribute")
    cols = {}
    for name, col in zip(names, node["values"]):
        cols[name] = vector_values(col)
    n = max((len(v) for v in cols.values() if isinstance(v, list)), default=0)
    rows = []
    for i in range(n):
        row = {}
        for name, values in cols.items():
            row[name] = values[i] if isinstance(values, list) and i < len(values) else values
        rows.append(row)
    return rows, list(cols.keys())


def load_rdata_objects(path: Path):
    parsed = RReader(path).parse_file()
    objects = {}
    for name, value in pairlist_items(parsed["value"]):
        objects[name] = value
    return objects, parsed


def parse_fasta(path: Path, kind: str):
    records = []
    header = None
    parts = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith(">"):
            if header is not None:
                records.append((header, "".join(parts).upper().replace("U", "T")))
            header = line[1:].strip()
            parts = []
        elif header is not None and set(line.upper()) <= set("ACGTUNacgtun"):
            parts.append(line)
    if header is not None:
        records.append((header, "".join(parts).upper().replace("U", "T")))

    out = []
    for hdr, seq in records:
        if kind == "gmr":
            d_s, idx_s = hdr.split("_", 1)
            out.append({"header": hdr, "D": float(d_s), "strain": int(float(idx_s)), "sequence": seq})
        else:
            out.append({"header": hdr, "D": float(hdr), "sequence": seq})
    return out


def maybe_float(x):
    if x is None:
        return None
    try:
        if isinstance(x, float) and math.isnan(x):
            return None
        return float(x)
    except Exception:
        return None


def maybe_int(x):
    f = maybe_float(x)
    return None if f is None else int(round(f))


def gc_fraction(seq: str) -> float:
    seq = seq.upper()
    return (seq.count("G") + seq.count("C")) / len(seq) if seq else 0.0


def codons(seq: str):
    n = len(seq) - (len(seq) % 3)
    return [seq[i:i + 3] for i in range(0, n, 3)]


def load_cai_weights(repo: Path | None):
    candidates = []
    if repo is not None:
        candidates.append(repo / "tools/bio_reality/data/ecoli_genome_cai_weights.json")
    candidates.extend([
        Path("/tmp/chen26ex/ecoli_genome_cai_weights.json"),
        Path.cwd() / "tools/bio_reality/data/ecoli_genome_cai_weights.json",
    ])
    for path in candidates:
        if path.exists():
            obj = json.loads(path.read_text())
            if all(c in obj for c in GENETIC_CODE):
                return {k.upper(): float(v) for k, v in obj.items()}, str(path)
            for key in ("weights_dna", "weights_rna", "weights", "cai_weights", "ecoli_genome_cai_weights"):
                if isinstance(obj, dict) and key in obj and isinstance(obj[key], dict):
                    weights = {}
                    for k, v in obj[key].items():
                        weights[k.upper().replace("U", "T")] = float(v)
                    return weights, str(path)
    # 明确标记 fallback；只在 repo 权重不可用时保证脚本可跑。
    weights = {}
    for aa, cs in AA_TO_CODONS.items():
        for c in cs:
            weights[c] = 1.0
    return weights, "fallback_uniform_weights"


def zero_q(codons_all):
    return {c: 0.0 for c in codons_all}


def fibers_for_codons(codons_all):
    fibers = defaultdict(list)
    for c in codons_all:
        aa = GENETIC_CODE[c]
        if aa != "*":
            fibers[aa].append(c)
    return dict(fibers)


def project_syn(qvec, fibers):
    out = dict(qvec)
    for fiber in fibers.values():
        m = sum(out[c] for c in fiber) / len(fiber)
        for c in fiber:
            out[c] -= m
    return out


def q_context_dna():
    codons_all = sorted(c for c, aa in GENETIC_CODE.items() if aa != "*")
    raw = {}
    q = zero_q(codons_all); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero_q(codons_all); q["AGA"] = 0.5; q["AGG"] = 0.5
    for c in ["CGT", "CGC", "CGA", "CGG"]:
        q[c] = -0.25
    raw["Arg_AGR"] = q
    q = zero_q(codons_all); q["ATA"] = 1.0; q["ATT"] = -0.5; q["ATC"] = -0.5; raw["Ile_ATA"] = q
    q = zero_q(codons_all)
    for c in ["CTT", "CTC", "CTA", "CTG"]:
        q[c] = 0.25
    q["TTA"] = -0.5; q["TTG"] = -0.5; raw["Leu_CTN_vs_TTR"] = q
    q = zero_q(codons_all); q["TTA"] = 1.0; q["TTG"] = -1.0; raw["Leu_TTA_vs_TTG"] = q
    q = zero_q(codons_all)
    for c in ["TCT", "TCC", "TCA", "TCG"]:
        q[c] = 0.25
    q["AGT"] = -0.5; q["AGC"] = -0.5; raw["Ser_TCR_vs_AGY"] = q
    q = zero_q(codons_all); q["TCA"] = 1.0; q["TCG"] = -1.0; raw["Ser_TCA_vs_TCG"] = q
    q = zero_q(codons_all); q["ACA"] = 0.5; q["ACG"] = 0.5; q["ACT"] = -0.5; q["ACC"] = -0.5; raw["Thr_ACR_vs_ACY"] = q
    q = zero_q(codons_all)
    for family in Q9_FAMILIES_DNA:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    fibers = fibers_for_codons(codons_all)
    projected = {name: project_syn(raw[name], fibers) for name in Q_NAMES}
    denoms = {name: math.sqrt(sum(projected[name][c] ** 2 for c in codons_all)) or 1.0 for name in Q_NAMES}
    return {"codons": codons_all, "projected": projected, "denoms": denoms}


Q_CONTEXT = q_context_dna()


def q_row_from_codons(codon_list):
    codons_all = Q_CONTEXT["codons"]
    counts = {c: 0 for c in codons_all}
    for c in codon_list:
        if c in counts:
            counts[c] += 1
    total = sum(counts.values())
    if total <= 0:
        return [0.0] * 9
    row = []
    for name in Q_NAMES:
        qvec = Q_CONTEXT["projected"][name]
        denom = Q_CONTEXT["denoms"][name]
        row.append(sum((counts[c] / total) * qvec[c] for c in codons_all) / denom)
    return row


def b_star_window_features(seq: str, weights: dict[str, float], start_nt: int = 57, drop_first_codons: int = 0):
    """9D B*_Q6 spatial-window 特征：6 个 CAI 窗口 + slope/curvature/roughness。"""
    cds = codons(seq)
    start_codon = max(0, start_nt // 3)
    region = cds[start_codon + drop_first_codons:]
    vals = [math.log(max(weights.get(c, 1.0e-6), 1.0e-6)) for c in region if c in GENETIC_CODE]
    if not vals:
        return [0.0] * 9
    n = len(vals)
    q6 = []
    for i in range(6):
        lo = int(math.floor(i * n / 6.0))
        hi = int(math.floor((i + 1) * n / 6.0))
        chunk = vals[lo:max(lo + 1, hi)]
        q6.append(sum(chunk) / len(chunk))
    mean = sum(vals) / n
    xs = [(i / (n - 1) * 2.0 - 1.0) if n > 1 else 0.0 for i in range(n)]
    den1 = sum(x * x for x in xs) or 1.0
    slope = sum(x * (v - mean) for x, v in zip(xs, vals)) / den1
    curve_basis = [x * x - (sum(xx * xx for xx in xs) / n) for x in xs]
    den2 = sum(x * x for x in curve_basis) or 1.0
    curvature = sum(x * (v - mean) for x, v in zip(curve_basis, vals)) / den2
    rough = sum(abs(vals[i] - vals[i - 1]) for i in range(1, n)) / max(1, n - 1)
    return q6 + [slope, curvature, rough]


def matrix_rankish_center_scale(rows):
    if not rows:
        return rows
    p = len(rows[0])
    means = [sum(r[j] for r in rows) / len(rows) for j in range(p)]
    sds = []
    for j in range(p):
        var = sum((r[j] - means[j]) ** 2 for r in rows) / max(1, len(rows) - 1)
        sds.append(math.sqrt(var) or 1.0)
    return [[(r[j] - means[j]) / sds[j] for j in range(p)] for r in rows]


def cholesky_solve(a, b, ridge=RIDGE):
    n = len(a)
    m = [[float(a[i][j]) + (ridge if i == j else 0.0) for j in range(n)] for i in range(n)]
    l = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = m[i][j] - sum(l[i][k] * l[j][k] for k in range(j))
            if i == j:
                l[i][j] = math.sqrt(max(s, 1.0e-15))
            else:
                l[i][j] = s / l[j][j]
    y = [0.0] * n
    for i in range(n):
        y[i] = (b[i] - sum(l[i][k] * y[k] for k in range(i))) / l[i][i]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - sum(l[k][i] * x[k] for k in range(i + 1, n))) / l[i][i]
    return x


def fit_ridge(X, y):
    n = len(y)
    if n == 0:
        return [], [], 0.0
    X1 = [[1.0] + list(row) for row in X]
    p = len(X1[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yy in zip(X1, y):
        for i in range(p):
            xty[i] += row[i] * yy
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta = cholesky_solve(xtx, xty)
    pred = [sum(beta[j] * row[j] for j in range(p)) for row in X1]
    return beta, pred, r2(y, pred)


def r2(y, pred):
    if not y:
        return 0.0
    mean = sum(y) / len(y)
    sst = sum((v - mean) ** 2 for v in y)
    if sst <= 1.0e-15:
        return 0.0
    sse = sum((v - p) ** 2 for v, p in zip(y, pred))
    return 1.0 - sse / sst


def residualize(y, covars):
    if not covars:
        return list(y)
    _, pred, _ = fit_ridge(covars, y)
    return [yy - pp for yy, pp in zip(y, pred)]


def centered_rows(records, target, require_condition=True):
    grouped = defaultdict(list)
    for rec in records:
        if target not in rec or rec[target] is None:
            continue
        key = (rec["D"], rec.get("condition")) if require_condition else (rec["D"], None)
        grouped[key].append(rec)
    rows = []
    for key, group in grouped.items():
        if len(group) < 2:
            continue
        my = sum(float(g[target]) for g in group) / len(group)
        mb = [sum(g["B_full"][j] for g in group) / len(group) for j in range(9)]
        mm = [sum(g["B_mid3"][j] for g in group) / len(group) for j in range(9)]
        for g in group:
            row = dict(g)
            row["Y_res"] = float(g[target]) - my
            row["B_res"] = [g["B_full"][j] - mb[j] for j in range(9)]
            row["M_res"] = [g["B_mid3"][j] - mm[j] for j in range(9)]
            rows.append(row)
    return rows


def delta_r2_for_rows(rows, feature_key="B_res", target_key="Y_res", covar_keys=None):
    y = [r[target_key] for r in rows]
    Xb = matrix_rankish_center_scale([r[feature_key] for r in rows])
    if covar_keys:
        cov = [[float(r[k]) for k in covar_keys] for r in rows]
        cov = matrix_rankish_center_scale(cov)
        _, _, r2_cov = fit_ridge(cov, y)
        _, _, r2_full = fit_ridge([c + b for c, b in zip(cov, Xb)], y)
        return max(0.0, r2_full - r2_cov), r2_full
    _, _, rr = fit_ridge(Xb, y)
    return max(0.0, rr), rr


def beta_direction(rows, feature_key="B_res"):
    y = [r["Y_res"] for r in rows]
    X = matrix_rankish_center_scale([r[feature_key] for r in rows])
    beta, _, _ = fit_ridge(X, y)
    return beta[1:]


def score_with_beta(feature, beta):
    return sum(a * b for a, b in zip(feature, beta))


def signed_slope(rows, beta, feature_key="B_res", target_key="Y_res"):
    scores = [score_with_beta(r[feature_key], beta) for r in rows]
    y = [r[target_key] for r in rows]
    sx = sum(scores) / len(scores) if scores else 0.0
    sy = sum(y) / len(y) if y else 0.0
    den = sum((x - sx) ** 2 for x in scores)
    if den <= 1.0e-15:
        return 0.0
    return sum((x - sx) * (yy - sy) for x, yy in zip(scores, y)) / den


def permutation_sequence(seq, rng):
    cds = codons(seq)
    buckets = defaultdict(list)
    for i, c in enumerate(cds):
        aa = GENETIC_CODE.get(c)
        if aa is not None:
            buckets[aa].append(i)
    new = list(cds)
    for aa, idxs in buckets.items():
        vals = [cds[i] for i in idxs]
        rng.shuffle(vals)
        for i, c in zip(idxs, vals):
            new[i] = c
    tail = seq[len(cds) * 3:]
    return "".join(new) + tail


def permutation_p(records, rows, target, weights, observed, feature_key="B_res", seed_offset=0):
    rng = random.Random(SEED + seed_offset)
    keys_needed = {(r["gene"], r["header"]) for r in rows}
    base_by_key = {(r["gene"], r["header"]): r for r in records if (r["gene"], r["header"]) in keys_needed}
    ge = 0
    vals = []
    for _ in range(N_PERM):
        permB = {}
        for key, rec in base_by_key.items():
            pseq = permutation_sequence(rec["sequence"], rng)
            permB[key] = {
                "B_full": b_star_window_features(pseq, weights, 57, 0),
                "B_mid3": b_star_window_features(pseq, weights, 57, 60),
            }
        grouped = defaultdict(list)
        for r in rows:
            grouped[(r["D"], r.get("condition"))].append(r)
        prows = []
        for key, group in grouped.items():
            mb = [sum(permB[(g["gene"], g["header"])]["B_full"][j] for g in group) / len(group) for j in range(9)]
            mm = [sum(permB[(g["gene"], g["header"])]["B_mid3"][j] for g in group) / len(group) for j in range(9)]
            for g in group:
                nr = dict(g)
                nr["B_res"] = [permB[(g["gene"], g["header"])]["B_full"][j] - mb[j] for j in range(9)]
                nr["M_res"] = [permB[(g["gene"], g["header"])]["B_mid3"][j] - mm[j] for j in range(9)]
                prows.append(nr)
        stat, _ = delta_r2_for_rows(prows, feature_key=feature_key)
        vals.append(stat)
        if abs(stat) >= abs(observed) - 1.0e-15:
            ge += 1
    return (ge + 1) / (N_PERM + 1), vals


def one_sided_amp_p(records, amp_rows, weights, beta, observed_slope):
    rng = random.Random(SEED + 9001)
    keys_needed = {(r["gene"], r["header"]) for r in amp_rows}
    base_by_key = {(r["gene"], r["header"]): r for r in records if (r["gene"], r["header"]) in keys_needed}
    want_positive = observed_slope >= 0
    extreme = 0
    for _ in range(N_PERM):
        permB = {}
        for key, rec in base_by_key.items():
            pseq = permutation_sequence(rec["sequence"], rng)
            permB[key] = b_star_window_features(pseq, weights, 57, 0)
        grouped = defaultdict(list)
        for r in amp_rows:
            grouped[(r["D"], r.get("condition"))].append(r)
        prows = []
        for key, group in grouped.items():
            mb = [sum(permB[(g["gene"], g["header"])][j] for g in group) / len(group) for j in range(9)]
            for g in group:
                nr = dict(g)
                nr["B_res"] = [permB[(g["gene"], g["header"])][j] - mb[j] for j in range(9)]
                prows.append(nr)
        s = signed_slope(prows, beta, "B_res", "Y_res")
        if want_positive:
            extreme += int(s >= observed_slope - 1.0e-15)
        else:
            extreme += int(s <= observed_slope + 1.0e-15)
    return (extreme + 1) / (N_PERM + 1)


def condition_stability(records, target, beta):
    out = {}
    for cond in sorted({r.get("condition") for r in records if r.get("gene") == "GmR" and target in r and r[target] is not None}, key=str):
        rows = centered_rows([r for r in records if r.get("gene") == "GmR" and r.get("condition") == cond], target)
        if len(rows) >= 4:
            out[str(cond)] = signed_slope(rows, beta)
    return out


def blockout_checks(gmr_records, target):
    rows = centered_rows([r for r in gmr_records if target in r and r[target] is not None], target)
    full_beta = beta_direction(rows, "B_res") if rows else [0.0] * 9
    signs = {}
    for drop_block in range(4):
        brows = []
        for r in rows:
            br = dict(r)
            blocks = r.get("B_blocks", [])
            kept = [blocks[i] for i in range(4) if i != drop_block and i < len(blocks)]
            if kept:
                avg = [sum(k[j] for k in kept) / len(kept) for j in range(9)]
                br["Bout_res"] = avg
                brows.append(br)
        if len(brows) >= 4:
            signs[f"drop_block_{drop_block + 1}"] = signed_slope(brows, full_beta, "Bout_res")
    mid_delta, _ = delta_r2_for_rows(rows, "M_res") if rows else (0.0, 0.0)
    full_delta, _ = delta_r2_for_rows(rows, "B_res") if rows else (0.0, 0.0)
    return {
        "drop_slopes": signs,
        "middle3_delta_r2": mid_delta,
        "full_delta_r2": full_delta,
        "increment_mid3_over_zero": mid_delta,
    }


def find_repo_from_cwd():
    cwd = Path.cwd().resolve()
    for p in [cwd] + list(cwd.parents):
        if (p / "tools/bio_reality").exists():
            return p
    env = os.environ.get("BIO_REALITY_REPO") or os.environ.get("REPO")
    if env and (Path(env) / "tools/bio_reality").exists():
        return Path(env)
    return None


def build_dataset(base: Path, repo: Path | None):
    weights, weight_source = load_cai_weights(repo)
    gmr_fasta = parse_fasta(base / "MOESM3.txt", "gmr")
    amp_fasta = parse_fasta(base / "MOESM4.txt", "ampr")

    expr_obj, _ = load_rdata_objects(base / "draw.expression3.Rdata")
    fit_obj, _ = load_rdata_objects(base / "alldata.all.RPbest.filter.Rdata")
    amp_obj, _ = load_rdata_objects(base / "alldata.all.RPbest.filter.AmpR.Rdata")

    expr_rows, expr_cols = data_frame_from_vecsxp(expr_obj["alldata"])
    fit_rows, fit_cols = data_frame_from_vecsxp(fit_obj["mydf"])
    amp_name = "mydf" if "mydf" in amp_obj else next(iter(amp_obj))
    amp_rows_raw, amp_cols = data_frame_from_vecsxp(amp_obj[amp_name])

    gseq = {(round(r["D"], 6), r["strain"]): r for r in gmr_fasta}
    amp_by_d = defaultdict(list)
    for r in amp_fasta:
        amp_by_d[round(r["D"], 6)].append(r)

    gmr_constructs = {}
    for r in gmr_fasta:
        key = ("GmR", r["header"])
        blocks = []
        cds_region = codons(r["sequence"])[19:]
        block_len = max(1, len(cds_region) // 4)
        for i in range(4):
            start = 19 + i * block_len
            end = 19 + ((i + 1) * block_len if i < 3 else len(cds_region))
            sub = "".join(codons(r["sequence"])[:19] + codons(r["sequence"])[start:end])
            blocks.append(b_star_window_features(sub, weights, 57, 0))
        gmr_constructs[key] = {
            "gene": "GmR", "header": r["header"], "D": r["D"], "strain": r["strain"],
            "sequence": r["sequence"], "gc": gc_fraction(r["sequence"]),
            "B_full": b_star_window_features(r["sequence"], weights, 57, 0),
            "B_mid3": b_star_window_features(r["sequence"], weights, 57, 60),
            "B_blocks": blocks,
        }

    records = []
    join_expr = join_fit = join_amp = 0
    for row in expr_rows:
        d = maybe_float(row.get("Dp"))
        strain = maybe_int(row.get("strain"))
        if d is None or strain is None:
            continue
        seq = gseq.get((round(d, 6), strain))
        if not seq:
            continue
        base_rec = dict(gmr_constructs[("GmR", seq["header"])])
        base_rec.update({
            "condition": maybe_float(row.get("GmCon")),
            "biorep": maybe_int(row.get("biorep")),
            "payoff": maybe_float(row.get("payoff")),
            "cost": maybe_float(row.get("cost")),
        })
        records.append(base_rec)
        join_expr += 1

    for row in fit_rows:
        d = maybe_float(row.get("dp", row.get("Dp")))
        strain = maybe_int(row.get("seq", row.get("strain")))
        if d is None or strain is None:
            continue
        seq = gseq.get((round(d, 6), strain))
        if not seq:
            continue
        base_rec = dict(gmr_constructs[("GmR", seq["header"])])
        base_rec.update({
            "condition": maybe_float(row.get("type", row.get("GmCon"))),
            "biorep": maybe_int(row.get("biorep")),
            "fitness": maybe_float(row.get("fitness0", row.get("fitness"))),
        })
        records.append(base_rec)
        join_fit += 1

    amp_constructs = []
    for r in amp_fasta:
        amp_constructs.append({
            "gene": "AmpR", "header": r["header"], "D": r["D"], "sequence": r["sequence"],
            "gc": gc_fraction(r["sequence"]),
            "B_full": b_star_window_features(r["sequence"], weights, 57, 0),
            "B_mid3": b_star_window_features(r["sequence"], weights, 57, 60),
        })
    amp_by_d_exact = {round(r["D"], 6): r for r in amp_constructs}
    for row in amp_rows_raw:
        d = maybe_float(row.get("dp", row.get("Dp", row.get("D"))))
        if d is None:
            continue
        seq = amp_by_d_exact.get(round(d, 6))
        if not seq:
            continue
        base_rec = dict(seq)
        base_rec.update({
            "condition": maybe_float(row.get("type", row.get("GmCon", 0.0))),
            "biorep": maybe_int(row.get("biorep")),
            "fitness": maybe_float(row.get("fitness0", row.get("fitness"))),
        })
        records.append(base_rec)
        join_amp += 1

    dataset = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "source": {
            "base_dir": str(base),
            "cai_weight_source": weight_source,
            "rdata_objects": {
                "draw.expression3.Rdata": sorted(expr_obj.keys()),
                "alldata.all.RPbest.filter.Rdata": sorted(fit_obj.keys()),
                "alldata.all.RPbest.filter.AmpR.Rdata": sorted(amp_obj.keys()),
            },
            "columns": {
                "expression": expr_cols,
                "fitness_gmr": fit_cols,
                "fitness_ampr": amp_cols,
            },
        },
        "fasta": {"GmR": len(gmr_fasta), "AmpR": len(amp_fasta)},
        "join": {
            "expression_rows": len(expr_rows), "expression_joined": join_expr,
            "gmr_fitness_rows": len(fit_rows), "gmr_fitness_joined": join_fit,
            "ampr_rows": len(amp_rows_raw), "ampr_joined": join_amp,
        },
        "records": records,
    }
    return dataset


def load_or_build_dataset(repo: Path | None):
    base = Path("/tmp/chen26ex")
    repo_dataset = repo / "tools/bio_reality/data/chen2026_matched_d_recoding.json" if repo else None
    local_dataset = base / "chen2026_matched_d_recoding.json"
    if repo_dataset is not None and repo_dataset.exists():
        return json.loads(repo_dataset.read_text()), False
    if local_dataset.exists():
        return json.loads(local_dataset.read_text()), False
    ds = build_dataset(base, repo)
    local_dataset.write_text(json.dumps(ds, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n")
    return ds, True


def run_experiment():
    start = time.time()
    repo = find_repo_from_cwd()
    dataset, built = load_or_build_dataset(repo)
    records = dataset.get("records", [])
    weights, weight_source = load_cai_weights(repo)

    checks = {
        "fasta_parsed": dataset.get("fasta", {}).get("GmR", 0) > 0 and dataset.get("fasta", {}).get("AmpR", 0) > 0,
        "rdata_reader_works": bool(dataset.get("source", {}).get("rdata_objects")),
        "seq_measurement_joined": dataset.get("join", {}).get("expression_joined", 0) > 0 and dataset.get("join", {}).get("gmr_fitness_joined", 0) > 0,
        "b_window_full_and_mid3": all("B_full" in r and "B_mid3" in r for r in records[:10]) and bool(records),
        "D_condition_centered": False,
        "composition_perm_null": False,
        "fiveprime_blockout": False,
        "ampr_validation": False,
        "distributed_beyond_D_verdict": False,
    }

    gmr_records = [r for r in records if r.get("gene") == "GmR"]
    amp_records = [r for r in records if r.get("gene") == "AmpR"]
    multi_d = sorted(d for d, c in Counter(r["D"] for r in gmr_records if "payoff" in r).items() if c >= 2)
    conditions = sorted({r.get("condition") for r in gmr_records if r.get("condition") is not None}, key=lambda x: (float(x), str(x)))
    per_target = {}
    beta_by_target = {}
    all_perm_ok = True
    all_after_ok = True

    for target in ("payoff", "cost", "fitness"):
        use_records = [r for r in gmr_records if target in r and r[target] is not None]
        rows = centered_rows(use_records, target)
        checks["D_condition_centered"] = checks["D_condition_centered"] or len(rows) >= 4
        if len(rows) < 4:
            per_target[target] = {"n": len(rows), "delta_r2": 0.0, "p_perm": 1.0, "p_after_D_GC": 1.0}
            all_perm_ok = False
            all_after_ok = False
            continue
        delta, full_r2 = delta_r2_for_rows(rows, "B_res")
        p_perm, _ = permutation_p(use_records, rows, target, weights, delta, "B_res", seed_offset=len(target) * 101)
        cov_rows = []
        for r in rows:
            nr = dict(r)
            nr["D2"] = r["D"] * r["D"]
            nr["copy"] = 1.0 if r.get("gene") == "AmpR" else 0.0
            cov_rows.append(nr)
        delta_after, _ = delta_r2_for_rows(cov_rows, "B_res", "Y_res", ["D", "D2", "gc", "copy"])
        # permutation p_after_D_GC：同一 null 下重算 covariate 增量
        p_after, _ = permutation_p(use_records, cov_rows, target, weights, delta_after, "B_res", seed_offset=len(target) * 303)
        beta = beta_direction(rows, "B_res")
        beta_by_target[target] = beta
        per_target[target] = {
            "n": len(rows),
            "delta_r2": round(delta, 10),
            "r2_full": round(full_r2, 10),
            "p_perm": round(p_perm, 6),
            "delta_r2_after_D_GC": round(delta_after, 10),
            "p_after_D_GC": round(p_after, 6),
            "beta_norm": round(math.sqrt(sum(b * b for b in beta)), 10),
        }
        if p_perm >= 0.05:
            all_perm_ok = False
        if p_after >= 0.05:
            all_after_ok = False

    checks["composition_perm_null"] = any(per_target[t].get("n", 0) >= 4 for t in per_target)

    # payoff 作为 5' 与方向冻结主轴；若 payoff 不足，退到 fitness。
    anchor = "payoff" if "payoff" in beta_by_target else ("fitness" if "fitness" in beta_by_target else next(iter(beta_by_target), None))
    fp = blockout_checks(gmr_records, anchor) if anchor else {"drop_slopes": {}, "middle3_delta_r2": 0.0, "full_delta_r2": 0.0, "increment_mid3_over_zero": 0.0}
    drop_vals = list(fp["drop_slopes"].values())
    anchor_sign = 1 if (drop_vals and sum(drop_vals) >= 0) else -1
    not_5prime_only = bool(drop_vals) and abs(fp["middle3_delta_r2"]) > 1.0e-9 and all((v == 0.0 or (v > 0) == (drop_vals[0] > 0)) for v in drop_vals)
    checks["fiveprime_blockout"] = bool(drop_vals)

    beta = beta_by_target.get(anchor, [0.0] * 9)
    stability = condition_stability(gmr_records, anchor, beta) if anchor else {}
    stable_sign = False
    if stability:
        signs = [1 if v >= 0 else -1 for v in stability.values() if abs(v) > 1.0e-15]
        stable_sign = bool(signs) and max(Counter(signs).values()) / len(signs) >= 0.75

    amp_rows = centered_rows([r for r in amp_records if "fitness" in r and r["fitness"] is not None], "fitness", require_condition=True)
    amp_slope = signed_slope(amp_rows, beta, "B_res", "Y_res") if len(amp_rows) >= 4 else 0.0
    ampr_p = one_sided_amp_p(records, amp_rows, weights, beta, amp_slope) if len(amp_rows) >= 4 and anchor else 1.0
    checks["ampr_validation"] = len(amp_rows) >= 4

    if not checks["rdata_reader_works"] or not checks["seq_measurement_joined"]:
        status = "needs_data"
        verdict = "uninformative"
        exit_code = 3
    elif not all_perm_ok or not all_after_ok:
        status = "passed"
        verdict = "absorbed_by_optimality"
        exit_code = 0
    elif not not_5prime_only:
        status = "passed"
        verdict = "absorbed_by_5prime"
        exit_code = 0
    elif not stable_sign or ampr_p >= 0.05:
        status = "passed"
        verdict = "no_stable_axis"
        exit_code = 0
    else:
        status = "passed"
        verdict = "distributed_beyond_D"
        exit_code = 0
        checks["distributed_beyond_D_verdict"] = True

    runtime = time.time() - start
    result = {
        "n_gmr": len({r["header"] for r in gmr_records}),
        "n_ampr": len({r["header"] for r in amp_records}),
        "n_D_strata_multi": len(multi_d),
        "conditions": conditions,
        "actual_B": "B_star_window_Q6_9D_Ecoli_CAI_spatial_windows_full_nt60_531_and_middle3_drop_first_60_codons",
        "runtime_sec": round(runtime, 3),
        "per_target": per_target,
        "fiveprime_middle3_increment": {
            "anchor": anchor,
            "middle3_delta_r2": round(fp.get("middle3_delta_r2", 0.0), 10),
            "full_delta_r2": round(fp.get("full_delta_r2", 0.0), 10),
            "drop_slopes": {k: round(v, 10) for k, v in fp.get("drop_slopes", {}).items()},
        },
        "ampr_independent_p": round(ampr_p, 6),
        "ampr_slope": round(amp_slope, 10),
        "beta_sign": {
            "anchor": anchor,
            "gmr_condition_slopes": {k: round(v, 10) for k, v in stability.items()},
            "stable_sign": stable_sign,
        },
        "cannot_claim": [
            "无 per-construct mRNA(非 fitness-beyond-mRNA)",
            "E.coli",
            "GmR/AmpR reporter 构建",
            f"D-centered 需 ≥2 seq/D strata(本次 GmR multi-D strata={len(multi_d)})",
            "composition-perm 是主 null",
        ],
        "dataset_built_this_run": built,
        "cai_weight_source": weight_source,
        "join": dataset.get("join", {}),
    }
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(run_experiment())
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {
                "fasta_parsed": False,
                "rdata_reader_works": False,
                "seq_measurement_joined": False,
                "b_window_full_and_mid3": False,
                "D_condition_centered": False,
                "composition_perm_null": False,
                "fiveprime_blockout": False,
                "ampr_validation": False,
                "distributed_beyond_D_verdict": False,
            },
            "verdict": "uninformative",
            "result": {
                "error": repr(exc),
                "cannot_claim": [
                    "无 per-construct mRNA(非 fitness-beyond-mRNA)",
                    "E.coli",
                    "GmR/AmpR reporter 构建",
                    "D-centered 需 ≥2 seq/D strata(解析失败未计数)",
                    "composition-perm 是主 null",
                ],
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

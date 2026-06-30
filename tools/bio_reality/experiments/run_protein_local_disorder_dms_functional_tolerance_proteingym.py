#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验：WT 序列局部 disorder / low-complexity 是否预测 measured per-position 功能突变耐受性。

纯 stdlib；读 repo-relative:
tools/bio_reality/data/protein_local_disorder_dms_functional_tolerance_proteingym.json
"""

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "protein_local_disorder_dms_functional_tolerance_proteingym"
CLAIM_ID = "h3.cross_layer_relation.functional_mutational_tolerance.local_disorder_dms_tolerance_proteingym"

DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/protein_local_disorder_dms_functional_tolerance_proteingym.json"
SEED = 93187
LAMBDA = 1.0
FOLDS = 5
B = 1000
RHO_FLOOR = 0.10
R2_FLOOR = 0.01
WINDOW = 7

DISORDER_PROMOTING = set("ARGQSEKP")
AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"
HYDROPATHY = {
    "A": 1.8,
    "C": 2.5,
    "D": -3.5,
    "E": -3.5,
    "F": 2.8,
    "G": -0.4,
    "H": -3.2,
    "I": 4.5,
    "K": -3.9,
    "L": 3.8,
    "M": 1.9,
    "N": -3.5,
    "P": -1.6,
    "Q": -3.5,
    "R": -4.5,
    "S": -0.8,
    "T": -0.7,
    "V": 4.2,
    "W": -0.9,
    "Y": -1.3,
}
CHARGE = {
    "D": -1.0,
    "E": -1.0,
    "H": 0.5,
    "K": 1.0,
    "R": 1.0,
}


def mean(xs):
    return sum(xs) / len(xs)


def variance(xs):
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs)


def ranks(xs):
    pairs = sorted((x, i) for i, x in enumerate(xs))
    out = [0.0] * len(xs)
    j = 0
    while j < len(pairs):
        k = j + 1
        while k < len(pairs) and pairs[k][0] == pairs[j][0]:
            k += 1
        r = (j + k - 1) / 2.0 + 1.0
        for t in range(j, k):
            out[pairs[t][1]] = r
        j = k
    return out


def pearson(x, y):
    mx = mean(x)
    my = mean(y)
    sx = sum((v - mx) * (v - mx) for v in x)
    sy = sum((v - my) * (v - my) for v in y)
    if sx <= 0 or sy <= 0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sx * sy)


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def r2_score(y, pred, baseline=None):
    if baseline is None:
        baseline = mean(y)
    sst = sum((v - baseline) * (v - baseline) for v in y)
    if sst <= 0:
        return 0.0
    sse = sum((v - p) * (v - p) for v, p in zip(y, pred))
    return 1.0 - sse / sst


def solve_linear(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            val = abs(aug[r][col])
            if val > best:
                best = val
                pivot = r
        if best < 1e-12:
            aug[col][col] += 1e-8
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pv = aug[col][col]
        for c in range(col, n + 1):
            aug[col][c] /= pv
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= factor * aug[col][c]
    return [aug[i][n] for i in range(n)]


def residualize_against(x, z):
    mx = mean(x)
    mz = mean(z)
    szz = sum((v - mz) * (v - mz) for v in z)
    if szz <= 0:
        return [v - mx for v in x]
    slope = sum((a - mx) * (b - mz) for a, b in zip(x, z)) / szz
    intercept = mx - slope * mz
    return [a - (intercept + slope * b) for a, b in zip(x, z)]


def partial_spearman(x, y, control):
    rx = ranks(x)
    ry = ranks(y)
    rz = ranks(control)
    return pearson(residualize_against(rx, rz), residualize_against(ry, rz))


def fold_indices_by_assay(assay_ids):
    folds = [([], []) for _ in range(FOLDS)]
    by_assay = {}
    for i, assay_id in enumerate(assay_ids):
        by_assay.setdefault(assay_id, []).append(i)
    rnd = random.Random(SEED)
    test_sets = [set() for _ in range(FOLDS)]
    for assay_id in sorted(by_assay):
        idxs = by_assay[assay_id][:]
        rnd.shuffle(idxs)
        for pos, idx in enumerate(idxs):
            test_sets[pos % FOLDS].add(idx)
    all_idxs = set(range(len(assay_ids)))
    out = []
    for fold in range(FOLDS):
        test = sorted(test_sets[fold])
        train = sorted(all_idxs - test_sets[fold])
        out.append((train, test))
    return out


def cv_predictions_from_cols(feature_cols, y, folds):
    n = len(y)
    p = len(feature_cols)
    pred = [0.0] * n
    for train, test in folds:
        means = []
        stds = []
        for col in feature_cols:
            m = sum(col[i] for i in train) / len(train)
            var = sum((col[i] - m) * (col[i] - m) for i in train) / max(1, len(train) - 1)
            means.append(m)
            stds.append(math.sqrt(var) if var > 1e-18 else 1.0)
        ymean = sum(y[i] for i in train) / len(train)
        xtx = [[0.0] * p for _ in range(p)]
        xty = [0.0] * p
        for i in train:
            z = [(feature_cols[j][i] - means[j]) / stds[j] for j in range(p)]
            yc = y[i] - ymean
            for a in range(p):
                za = z[a]
                xty[a] += za * yc
                for c in range(a, p):
                    xtx[a][c] += za * z[c]
        for a in range(p):
            for c in range(a):
                xtx[a][c] = xtx[c][a]
            xtx[a][a] += LAMBDA
        coef = solve_linear(xtx, xty)
        for i in test:
            val = ymean
            for j in range(p):
                val += coef[j] * ((feature_cols[j][i] - means[j]) / stds[j])
            pred[i] = val
    return pred


def heldout_r2_from_cols(feature_cols, y, folds):
    return r2_score(y, cv_predictions_from_cols(feature_cols, y, folds))


def shannon_entropy(seq):
    if not seq:
        return 0.0
    counts = {}
    for aa in seq:
        counts[aa] = counts.get(aa, 0) + 1
    total = len(seq)
    ent = 0.0
    for count in counts.values():
        p = count / total
        ent -= p * (math.log(p) / math.log(2.0))
    return ent


def local_features(seq, pos):
    center = pos - 1
    lo = max(0, center - WINDOW)
    hi = min(len(seq), center + WINDOW + 1)
    flank = seq[lo:center] + seq[center + 1:hi]
    if not flank:
        return 0.0, 0.0
    disorder_frac = sum(1 for aa in flank if aa in DISORDER_PROMOTING) / len(flank)
    return disorder_frac, shannon_entropy(flank)


def center_features(seq, pos):
    aa = seq[pos - 1]
    return (
        HYDROPATHY.get(aa, 0.0),
        CHARGE.get(aa, 0.0),
        1.0 if aa in DISORDER_PROMOTING else 0.0,
    )


def position_term(pos, length):
    if length <= 0:
        return 0.0
    return min(pos - 1, length - pos) / (length / 2.0)


def build_rows(payload):
    assays = payload["assays"]
    rows = []
    mutations_used = 0
    assay_site_counts = {}
    for assay_id in sorted(assays):
        record = assays[assay_id]
        seq = str(record["seq"])
        length = len(seq)
        by_pos = {}
        for mut in record["muts"]:
            pos = int(mut[0])
            score = float(mut[2])
            if 1 <= pos <= length and math.isfinite(score):
                by_pos.setdefault(pos, []).append(score)
        assay_rows = []
        for pos in sorted(by_pos):
            vals = by_pos[pos]
            if len(vals) < 5:
                continue
            dfrac, complexity = local_features(seq, pos)
            hydro, charge, center_disorder = center_features(seq, pos)
            tol = mean(vals)
            assay_rows.append({
                "assay": assay_id,
                "pos": pos,
                "length": length,
                "tolerance_raw": tol,
                "substitutions": len(vals),
                "pos_term": position_term(pos, length),
                "hydropathy": hydro,
                "charge": charge,
                "center_disorder": center_disorder,
                "disorder_frac": dfrac,
                "complexity": complexity,
            })
        if len(assay_rows) < 2:
            continue
        vals = [row["tolerance_raw"] for row in assay_rows]
        sd = math.sqrt(variance(vals) / max(1, len(vals) - 1))
        if sd <= 1e-18:
            continue
        m = mean(vals)
        for row in assay_rows:
            row["tolerance_z"] = (row["tolerance_raw"] - m) / sd
            rows.append(row)
            mutations_used += row["substitutions"]
        assay_site_counts[assay_id] = len(assay_rows)
    return rows, mutations_used, assay_site_counts


def cols_from_rows(rows):
    y = [row["tolerance_z"] for row in rows]
    assay_ids = [row["assay"] for row in rows]
    pos_term = [row["pos_term"] for row in rows]
    hydropathy = [row["hydropathy"] for row in rows]
    charge = [row["charge"] for row in rows]
    center_disorder = [row["center_disorder"] for row in rows]
    disorder_frac = [row["disorder_frac"] for row in rows]
    complexity = [row["complexity"] for row in rows]
    controls = [pos_term, hydropathy, charge, center_disorder]
    full = controls + [disorder_frac, complexity]
    return {
        "y": y,
        "assay_ids": assay_ids,
        "pos_term": pos_term,
        "hydropathy": hydropathy,
        "charge": charge,
        "center_disorder": center_disorder,
        "disorder_frac": disorder_frac,
        "complexity": complexity,
        "controls": controls,
        "full": full,
    }


def assay_index_blocks(assay_ids):
    blocks = {}
    for i, assay_id in enumerate(assay_ids):
        blocks.setdefault(assay_id, []).append(i)
    return [blocks[k] for k in sorted(blocks)]


def permute_local_features(disorder_frac, complexity, blocks, rnd):
    perm_disorder = disorder_frac[:]
    perm_complexity = complexity[:]
    for idxs in blocks:
        src = idxs[:]
        rnd.shuffle(src)
        for dst_i, src_i in zip(idxs, src):
            perm_disorder[dst_i] = disorder_frac[src_i]
            perm_complexity[dst_i] = complexity[src_i]
    return perm_disorder, perm_complexity


def permutation_p_right(null, observed):
    ge = sum(1 for v in null if v >= observed)
    return (ge + 1) / (len(null) + 1)


def permutation_p_abs(null, observed):
    ge = sum(1 for v in null if abs(v) >= abs(observed))
    return (ge + 1) / (len(null) + 1)


def failure_out(note, started=None, checks=None):
    runtime = 0.0 if started is None else time.time() - started
    out = {
        "status": "needs_data",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks if checks is not None else {"proteingym_parsed": False},
        "verdict": "needs_data",
        "note": note,
        "result": {
            "n": 0,
            "distinct": 0,
            "main": {},
            "posctrl": {},
            "runtime_sec": runtime,
            "cannot_claim": ["未能读取 ProteinGym functional DMS compact JSON。"],
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(3)


def main():
    started = time.time()
    if not DATA_PATH.exists():
        failure_out(f"找不到数据文件: {DATA_PATH}", started)

    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    rows, mutations_used, assay_site_counts = build_rows(payload)
    if not rows:
        failure_out("没有可用的 assay 内 per-position tolerance 行。", started, {"proteingym_parsed": True})

    cols = cols_from_rows(rows)
    y = cols["y"]
    distinct = len({round(v, 12) for v in y})
    folds = fold_indices_by_assay(cols["assay_ids"])
    base_r2 = heldout_r2_from_cols(cols["controls"], y, folds)
    full_r2 = heldout_r2_from_cols(cols["full"], y, folds)
    incr_r2 = full_r2 - base_r2

    anchor_rho = spearman(cols["pos_term"], y)
    raw_disorder_rho = spearman(cols["disorder_frac"], y)
    raw_complexity_rho = spearman(cols["complexity"], y)
    center_disorder_rho = spearman(cols["center_disorder"], y)
    hydropathy_rho = spearman(cols["hydropathy"], y)
    partial_disorder = partial_spearman(cols["disorder_frac"], y, cols["pos_term"])
    pos_reproduced = abs(anchor_rho) >= RHO_FLOOR and distinct > 10

    blocks = assay_index_blocks(cols["assay_ids"])
    rnd = random.Random(SEED + 1701)
    null_incr = []
    null_partial = []
    for _b in range(B):
        perm_disorder, perm_complexity = permute_local_features(
            cols["disorder_frac"],
            cols["complexity"],
            blocks,
            rnd,
        )
        perm_full = cols["controls"] + [perm_disorder, perm_complexity]
        perm_full_r2 = heldout_r2_from_cols(perm_full, y, folds)
        null_incr.append(perm_full_r2 - base_r2)
        null_partial.append(partial_spearman(perm_disorder, y, cols["pos_term"]))

    incr_p = permutation_p_right(null_incr, incr_r2)
    partial_p = permutation_p_abs(null_partial, partial_disorder)
    incr_crosses = incr_r2 >= R2_FLOOR and incr_p < 0.01
    partial_crosses = abs(partial_disorder) >= RHO_FLOOR and partial_p < 0.01
    disorder_crosses = incr_crosses or partial_crosses
    raw_has_signal = abs(raw_disorder_rho) >= RHO_FLOOR or abs(raw_complexity_rho) >= RHO_FLOOR

    if not pos_reproduced or distinct <= 10:
        verdict = "needs_data"
    elif disorder_crosses:
        verdict = "crosses_boundary"
    elif raw_has_signal:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "composition_artifact"

    status = "passed" if verdict != "needs_data" else "needs_data"
    checks = {
        "proteingym_parsed": True,
        "tolerance_continuous": distinct > 10,
        "anchor_reproduced": pos_reproduced,
        "flanking_excludes_center": True,
        "within_assay_perm_null": len(null_incr) >= B and len(null_partial) >= B,
        "disorder_beyond_position_crosses": disorder_crosses,
        "assay_internal_zscore": True,
        "center_residue_controls": True,
        "tolerance_verdict": verdict,
    }

    cannot_claim = [
        "观测性关联非因果。",
        "disorder 由 stdlib flanking 组成代理给出，非 IUPred 或真实 disorder 预测器，且没有 MSA 保守性。",
        "功能 DMS 混合生长、活性、抗性、FACS assay；assay 内 z-score 对齐后仍有 readout 异质性。",
        "tolerance 是每个位点 substitution 分数均值，部分位点 substitution 数不均。",
        "少数 GOF 或抗性 assay 的 fitness 方向可能相反。",
        "position 控制后的剩余信号不能排除二级结构、溶剂可及性等未测协变量。",
    ]
    note = (
        "每个 assay 内按位点聚合 measured DMS_score 并 z-score；WT flanking ±7 且排除中心残基，"
        "用 pos_term 与中心残基 hydropathy/charge/disorder 指示作控制；"
        "判定统计为 held-out R² gain 与 disorder_frac 对 tolerance 的 pos_term-partial Spearman，"
        "null 在 assay 内打乱 local sequence descriptors 的位点对应。"
    )
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(rows),
            "distinct": distinct,
            "main": {
                "base_controls_r2_heldout": base_r2,
                "controls_disorder_r2_heldout": full_r2,
                "incr_r2_heldout": incr_r2,
                "incr_perm_p": incr_p,
                "incr_perm_mean": mean(null_incr),
                "incr_perm_min": min(null_incr),
                "incr_perm_max": max(null_incr),
                "partial_spearman_disorder_given_pos": partial_disorder,
                "partial_perm_p": partial_p,
                "partial_perm_mean": mean(null_partial),
                "partial_perm_min": min(null_partial),
                "partial_perm_max": max(null_partial),
                "raw_spearman_disorder": raw_disorder_rho,
                "raw_spearman_complexity": raw_complexity_rho,
                "actual_B": len(null_incr),
                "n_assays": len(assay_site_counts),
                "n_mutations_used": mutations_used,
            },
            "posctrl": {
                "spearman_pos_term_tolerance": anchor_rho,
                "reproduced": pos_reproduced,
                "center_disorder_spearman": center_disorder_rho,
                "hydropathy_spearman": hydropathy_rho,
                "pos_term_definition": "min(p-1,L-p)/(L/2); termini=0, center=1",
            },
            "runtime_sec": time.time() - started,
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if status == "passed" else 3)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        failure_out(str(e), time.time(), {"runtime_exception": True})

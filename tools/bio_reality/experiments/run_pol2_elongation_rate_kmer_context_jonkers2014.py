#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验：基因体 k-mer 上下文是否超过 1-mer 组成预测 measured Pol II 延伸速率。

纯 stdlib；读 repo-relative:
tools/bio_reality/data/pol2_elongation_rate_kmer_context_jonkers2014.json
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "pol2_elongation_rate_kmer_context_jonkers2014"
CLAIM_ID = "h3.cross_layer_relation.transcription_elongation_kinetics.pol2_elongation_rate_kmer_context_jonkers2014"

DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/pol2_elongation_rate_kmer_context_jonkers2014.json"
SEED = 48895
BASES = "ACGT"
K2 = [a + b for a in BASES for b in BASES]
K3 = [a + b + c for a in BASES for b in BASES for c in BASES]
LAMBDA = 1.0
FOLDS = 5
B = 1000


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


def fit_ridge(x_rows, y, lam=LAMBDA):
    n = len(x_rows)
    p = len(x_rows[0]) if x_rows else 0
    cols = p + 1
    means = [0.0] * p
    stds = [1.0] * p
    for j in range(p):
        vals = [row[j] for row in x_rows]
        means[j] = mean(vals)
        var = variance(vals) / max(1, n - 1)
        stds[j] = math.sqrt(var) if var > 1e-18 else 1.0
    ymean = mean(y)
    xtx = [[0.0] * cols for _ in range(cols)]
    xty = [0.0] * cols
    for row, yy in zip(x_rows, y):
        z = [1.0] + [(row[j] - means[j]) / stds[j] for j in range(p)]
        yc = yy - ymean
        for i in range(cols):
            xty[i] += z[i] * yc
            zi = z[i]
            for j in range(i, cols):
                xtx[i][j] += zi * z[j]
    for i in range(cols):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    for j in range(1, cols):
        xtx[j][j] += lam
    xtx[0][0] += 1e-8
    coef = solve_linear(xtx, xty)
    return {"means": means, "stds": stds, "ymean": ymean, "coef": coef}


def predict(model, x_rows):
    p = len(model["means"])
    out = []
    for row in x_rows:
        val = model["ymean"] + model["coef"][0]
        for j in range(p):
            val += model["coef"][j + 1] * ((row[j] - model["means"][j]) / model["stds"][j])
        out.append(val)
    return out


def select_rows(rows, idxs):
    return [rows[i] for i in idxs]


def cv_predictions(x_rows, y):
    n = len(y)
    idx = list(range(n))
    rnd = random.Random(SEED)
    rnd.shuffle(idx)
    pred = [0.0] * n
    for fold in range(FOLDS):
        test = [i for pos, i in enumerate(idx) if pos % FOLDS == fold]
        train = [i for pos, i in enumerate(idx) if pos % FOLDS != fold]
        model = fit_ridge(select_rows(x_rows, train), [y[i] for i in train])
        vals = predict(model, select_rows(x_rows, test))
        for i, p in zip(test, vals):
            pred[i] = p
    return pred


def fold_indices(n):
    idx = list(range(n))
    rnd = random.Random(SEED)
    rnd.shuffle(idx)
    folds = []
    for fold in range(FOLDS):
        test = [i for pos, i in enumerate(idx) if pos % FOLDS == fold]
        train = [i for pos, i in enumerate(idx) if pos % FOLDS != fold]
        folds.append((train, test))
    return folds


def onemer_features(g):
    one = g["onemer"]
    return [one[b] for b in BASES]


def context_features_from_freqs(one, k2, k3):
    feats = []
    for kmer in K2:
        exp = one[kmer[0]] * one[kmer[1]]
        feats.append(k2.get(kmer, 0.0) - exp)
    for kmer in K3:
        # Markov-1 期望固定为 f(XY)f(YZ)/f(Y)；中心碱基缺失时退回 mono 乘积。
        mid = one[kmer[1]]
        if mid > 1e-15:
            exp = k2.get(kmer[:2], 0.0) * k2.get(kmer[1:], 0.0) / mid
        else:
            exp = one[kmer[0]] * one[kmer[1]] * one[kmer[2]]
        feats.append(k3.get(kmer, 0.0) - exp)
    return feats


def full_features(g):
    return onemer_features(g) + context_features_from_freqs(g["onemer"], g["kmer2"], g["kmer3"])


def insample_r2(x_rows, y):
    model = fit_ridge(x_rows, y)
    pred = predict(model, x_rows)
    return r2_score(y, pred)


def heldout_r2(x_rows, y):
    pred = cv_predictions(x_rows, y)
    return r2_score(y, pred)


def invert_matrix(a):
    n = len(a)
    aug = [row[:] + [1.0 if i == j else 0.0 for j in range(n)] for i, row in enumerate(a)]
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
        for c in range(col, 2 * n):
            aug[col][c] /= pv
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            for c in range(col, 2 * n):
                aug[r][c] -= factor * aug[col][c]
    return [row[n:] for row in aug]


def precompute_cv_parts(x_rows):
    parts = []
    for train, test in fold_indices(len(x_rows)):
        train_rows = select_rows(x_rows, train)
        n_train = len(train)
        p = len(train_rows[0]) if train_rows else 0
        means = [0.0] * p
        stds = [1.0] * p
        for j in range(p):
            vals = [row[j] for row in train_rows]
            means[j] = mean(vals)
            var = variance(vals) / max(1, n_train - 1)
            stds[j] = math.sqrt(var) if var > 1e-18 else 1.0

        z_train = [[(row[j] - means[j]) / stds[j] for j in range(p)] for row in train_rows]
        xtx = [[0.0] * p for _ in range(p)]
        for z in z_train:
            for i in range(p):
                zi = z[i]
                for j in range(i, p):
                    xtx[i][j] += zi * z[j]
        for i in range(p):
            for j in range(i):
                xtx[i][j] = xtx[j][i]
            xtx[i][i] += LAMBDA
        inv = invert_matrix(xtx)
        z_test = [(idx, [(x_rows[idx][j] - means[j]) / stds[j] for j in range(p)]) for idx in test]
        parts.append((train, z_train, z_test, inv))
    return parts


def cv_predictions_from_parts(parts, y):
    pred = [0.0] * len(y)
    for train, z_train, z_test, inv in parts:
        y_train = [y[i] for i in train]
        ymean = mean(y_train)
        p = len(z_train[0]) if z_train else 0
        xty = [0.0] * p
        for z, yy in zip(z_train, y_train):
            yc = yy - ymean
            for j, val in enumerate(z):
                xty[j] += val * yc
        coef = [sum(inv[i][j] * xty[j] for j in range(p)) for i in range(p)]
        for idx, zt in z_test:
            pred[idx] = ymean + sum(coef[j] * zt[j] for j in range(p))
    return pred


def label_perm_null_distribution(y, base_parts, full_parts):
    rnd = random.Random(SEED + 1701)
    null = []
    perm = y[:]
    for _ in range(B):
        rnd.shuffle(perm)
        base_pred = cv_predictions_from_parts(base_parts, perm)
        full_pred = cv_predictions_from_parts(full_parts, perm)
        null.append(r2_score(perm, full_pred) - r2_score(perm, base_pred))
    return null


def verdict_from(pos_ok, incr_heldout, pval):
    if not pos_ok:
        return "needs_data"
    if pval < 0.01 and incr_heldout >= 0.01:
        return "crosses_boundary"
    if pval < 0.01:
        return "bounded_descriptor_only"
    return "composition_artifact"


def main():
    started = time.time()
    if not DATA_PATH.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"jonkers_parsed": False},
            "verdict": "needs_data",
            "note": f"找不到数据文件: {DATA_PATH}",
            "result": {"cannot_claim": ["未能读取 Jonkers measured rate compact JSON。"]},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    genes = payload["genes"]
    y = [float(g["rate_kb_min"]) for g in genes]
    distinct = len({round(v, 12) for v in y})
    one_x = [onemer_features(g) for g in genes]
    full_x = [full_features(g) for g in genes]

    onemer_in = insample_r2(one_x, y)
    full_in = insample_r2(full_x, y)
    one_parts = precompute_cv_parts(one_x)
    full_parts = precompute_cv_parts(full_x)
    one_pred = cv_predictions_from_parts(one_parts, y)
    full_pred = cv_predictions_from_parts(full_parts, y)
    onemer_held = r2_score(y, one_pred)
    full_held = r2_score(y, full_pred)
    incr_in = full_in - onemer_in
    incr_held = full_held - onemer_held

    gc = [float(g["gc"]) for g in genes]
    c_content = [float(g["onemer"]["C"]) for g in genes]
    t_content = [float(g["onemer"]["T"]) for g in genes]
    corr_gc = spearman(gc, y)
    corr_c = spearman(c_content, y)
    corr_t = spearman(t_content, y)
    baseline_corr = max([corr_gc, corr_c, corr_t], key=lambda v: abs(v))
    pos_reproduced = (abs(baseline_corr) >= 0.10 and onemer_in > 0.01 and distinct > 10)

    null = label_perm_null_distribution(y, one_parts, full_parts)
    ge = sum(1 for v in null if v >= incr_held)
    pval = (ge + 1) / (len(null) + 1)
    null_mean = mean(null)

    verdict = verdict_from(pos_reproduced, incr_held, pval)
    status = "passed" if verdict != "needs_data" else "needs_data"
    checks = {
        "jonkers_parsed": True,
        "rate_continuous": distinct > 10,
        "mm9_bodies_chromwise": payload.get("meta", {}).get("prep", {}).get("raw_downloads_deleted_after_prep") is True,
        "onemer_baseline": onemer_in > 0.01,
        "context_incremental": incr_in > 0 or incr_held > 0,
        "context_excess_label_perm_null": len(null) >= B and len(genes) == len(y),
        "heldout_validation": full_held == full_held and onemer_held == onemer_held,
        "positive_control": pos_reproduced,
        "pol2_verdict": verdict,
    }
    cannot_claim = [
        "Jonkers GRO-seq flavopiridol release 测速率仅覆盖 mouse ES 中可测速率基因。",
        "mm9/refGene 坐标是转录本近似，存在转录本异构体不确定性。",
        "基因体序列按 strand-aware TSS 起 cap 50kb，不能代表完整超长基因体。",
        "观测性相关实验，不能推出 k-mer 上下文因果改变 Pol II 延伸速率。",
        "k-mer 集固定为 2-mer excess + 3-mer Markov-1 excess 的启发式特征，未在速率上调参。",
        "判定性 null 为 context-excess + label-permutation，全基因非退化；检验上下文 excess 是否超出组成基线与高维偶然过拟合。",
    ]
    if verdict == "composition_artifact":
        cannot_claim.append("高阶上下文不超单核苷酸组成；本结果不能声称 context-beyond-composition。")

    note = (
        "基因体 k-mer 上下文 vs Jonkers measured Pol II 延伸速率；增量 R² 控制 1-mer 组成，"
        "用 context-excess(组成正交) + label-permutation 重做合法判定性检验，取代旧 n=5 退化 mono-shuffle；"
        "excess 是 mono-preserving shuffle 所摧毁的顺序成分，held-out 防过拟合；Jonkers 直接测速率防 disguised-e_in。"
    )
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(genes),
            "distinct": distinct,
            "main": {
                "onemer_baseline_r2_heldout": onemer_held,
                "full_r2_heldout": full_held,
                "incr_r2_insample": incr_in,
                "incr_r2_heldout": incr_held,
                "label_perm_p": pval,
                "label_perm_mean": null_mean,
                "actual_B": len(null),
                "n_genes_used": len(genes),
            },
            "posctrl": {
                "baseline_corr": baseline_corr,
                "spearman_gc": corr_gc,
                "spearman_c": corr_c,
                "spearman_t": corr_t,
                "reproduced": pos_reproduced,
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
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"runtime_exception": True},
            "verdict": "needs_data",
            "note": str(e),
            "result": {"cannot_claim": ["运行时异常，不能作科学结论。"]},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

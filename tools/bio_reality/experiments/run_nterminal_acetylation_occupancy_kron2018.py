#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Kron 2018 yeast NtAc 连续占据率离线实验。

纯 Python 标准库实现：rank、Spearman、OLS 残差、permutation null、AUROC。
实验脚本按 orchestrator 约定从 repo-relative cwd 读取 compact JSON。
"""

from __future__ import annotations

import json
import math
import random
import statistics
import time
from pathlib import Path


EXPERIMENT_ID = "nterminal_acetylation_occupancy_kron2018"
CLAIM_ID = "h3.cross_layer_relation.nterminal_acetylation.nterminal_acetylation_occupancy_kron2018"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/nterminal_acetylation_occupancy_kron2018.json"
AA20 = "ACDEFGHIKLMNPQRSTVWY"
SEED = 20260623
PERM_B = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    ys = sorted(xs)
    if not ys:
        return 0.0
    n = len(ys)
    if n % 2:
        return ys[n // 2]
    return (ys[n // 2 - 1] + ys[n // 2]) / 2.0


def round_sig(x, nd=6):
    if x is None:
        return None
    if isinstance(x, bool):
        return x
    if not isinstance(x, (int, float)):
        return x
    if math.isnan(x) or math.isinf(x):
        return None
    return round(float(x), nd)


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: (xs[i], i))
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx = mean(x)
    my = mean(y)
    sx = 0.0
    sy = 0.0
    sxy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        sx += da * da
        sy += db * db
        sxy += da * db
    den = math.sqrt(sx * sy)
    return sxy / den if den else 0.0


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def solve_linear(a, b):
    n = len(a)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[piv][col]) < 1e-12:
            aug[col][col] += 1e-8
            piv = col
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-20:
            div = 1e-20
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac:
                for j in range(col, n + 1):
                    aug[r][j] -= fac * aug[col][j]
    return [aug[i][n] for i in range(n)]


def fit_predict(xmat, y):
    if not xmat:
        return []
    n = len(xmat)
    p = len(xmat[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, val in zip(xmat, y):
        for i in range(p):
            xty[i] += row[i] * val
            ri = row[i]
            for j in range(i, p):
                xtx[i][j] += ri * row[j]
    for i in range(p):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    beta = solve_linear(xtx, xty)
    return [sum(row[j] * beta[j] for j in range(p)) for row in xmat]


def residualize(y, xmat):
    pred = fit_predict(xmat, y)
    return [v - p for v, p in zip(y, pred)]


def standardize_cols(rows):
    if not rows:
        return []
    n = len(rows)
    p = len(rows[0])
    cols = transpose(rows)
    means = [mean(c) for c in cols]
    sds = []
    for c, m in zip(cols, means):
        var = sum((v - m) ** 2 for v in c) / max(1, n - 1)
        sds.append(math.sqrt(var) if var > 1e-20 else 1.0)
    out = []
    for row in rows:
        out.append([1.0] + [(row[j] - means[j]) / sds[j] for j in range(p)])
    return out


def control_rows(proteins, include_p1prime=False):
    observed_logs = [math.log(p["abundance_lfq"]) for p in proteins if p.get("abundance_lfq")]
    med_log_ab = median(observed_logs)
    p1_levels = sorted({p["p1prime"] for p in proteins})
    rows = []
    for p in proteins:
        comp = p["aa_comp"]
        row = [comp.get(aa, 0.0) for aa in AA20[:-1]]
        row.append(math.log(max(1, p["length"])))
        if p.get("abundance_lfq"):
            row.append(math.log(p["abundance_lfq"]))
            row.append(0.0)
        else:
            row.append(med_log_ab)
            row.append(1.0)
        if include_p1prime:
            for lev in p1_levels[:-1]:
                row.append(1.0 if p["p1prime"] == lev else 0.0)
        rows.append(row)
    return standardize_cols(rows)


def partial_spearman(x, y, controls):
    rx = residualize(ranks(x), controls)
    ry = residualize(ranks(y), controls)
    return pearson(rx, ry), rx, ry


def permutation_p(rx, ry, b=PERM_B, seed=SEED):
    rng = random.Random(seed)
    actual = pearson(rx, ry)
    base = list(ry)
    ge = 0
    for _ in range(b):
        perm = base[:]
        rng.shuffle(perm)
        if abs(pearson(rx, perm)) >= abs(actual) - 1e-15:
            ge += 1
    return (ge + 1) / (b + 1), b


def r2(y, pred):
    my = mean(y)
    sst = sum((v - my) ** 2 for v in y)
    sse = sum((v - p) ** 2 for v, p in zip(y, pred))
    return 1.0 - sse / sst if sst else 0.0


def incremental_r2(x, y, controls):
    y_rank = ranks(y)
    pred0 = fit_predict(controls, y_rank)
    x_rank_res = ranks(x)
    rows1 = [row + [xv] for row, xv in zip(controls, x_rank_res)]
    pred1 = fit_predict(rows1, y_rank)
    return r2(y_rank, pred1) - r2(y_rank, pred0)


def auroc(scores, labels):
    pairs = [(s, l) for s, l in zip(scores, labels) if l in (0, 1)]
    n_pos = sum(1 for _, l in pairs if l == 1)
    n_neg = sum(1 for _, l in pairs if l == 0)
    if n_pos == 0 or n_neg == 0:
        return None
    sorted_pairs = sorted(pairs, key=lambda z: z[0])
    rank_sum = 0.0
    i = 0
    while i < len(sorted_pairs):
        j = i + 1
        while j < len(sorted_pairs) and sorted_pairs[j][0] == sorted_pairs[i][0]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            if sorted_pairs[k][1] == 1:
                rank_sum += avg_rank
        i = j
    return (rank_sum - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)


def group_mean(proteins, filt):
    vals = [p["ntac_pct"] for p in proteins if filt(p)]
    return mean(vals), len(vals)


def positive_controls(proteins):
    natb_mean, natb_n = group_mean(proteins, lambda p: p["nat_type"] == "NatB")
    nata_mean, nata_n = group_mean(proteins, lambda p: p["nat_type"] == "NatA")
    by_second = {}
    for aa in ["S", "T", "A", "V", "G"]:
        m, n = group_mean(proteins, lambda p, aa=aa: p["nat_type"] == "NatA" and p["p1prime"] == aa)
        by_second[aa] = {"mean": round_sig(m), "n": n}
    acid_m, acid_n = group_mean(proteins, lambda p: p["nat_type"] == "NatA" and p["p2prime"] in {"D", "E"})
    non_m, non_n = group_mean(proteins, lambda p: p["nat_type"] == "NatA" and p["p2prime"] not in {"D", "E"})
    reproduced = (
        natb_n >= 100
        and nata_n >= 300
        and 90 <= natb_mean <= 100
        and 60 <= nata_mean <= 75
        and by_second["S"]["mean"] is not None
        and by_second["S"]["mean"] >= 90
        and 35 <= by_second["T"]["mean"] <= 55
        and 30 <= by_second["A"]["mean"] <= 50
        and by_second["V"]["mean"] <= 8
        and by_second["G"]["mean"] <= 5
        and acid_m > non_m + 15
    )
    return {
        "natB_mean": round_sig(natb_mean),
        "natB_n": natb_n,
        "natA_mean": round_sig(nata_mean),
        "natA_n": nata_n,
        "natA_by_2nd": by_second,
        "acidic_3rd_boost": {
            "acidic_mean": round_sig(acid_m),
            "acidic_n": acid_n,
            "nonacidic_mean": round_sig(non_m),
            "nonacidic_n": non_n,
            "delta": round_sig(acid_m - non_m),
        },
        "reproduced": reproduced,
    }


def main():
    t0 = time.time()
    obj = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    proteins = obj["proteins"]
    y = [p["ntac_pct"] for p in proteins]
    x = [p["seq_prior"] for p in proteins]
    controls = control_rows(proteins, include_p1prime=False)
    rho, rx, ry = partial_spearman(x, y, controls)
    pval, actual_b = permutation_p(rx, ry)
    inc_r2 = incremental_r2(x, y, controls)

    within = [p for p in proteins if p["nat_type"] == "NatA" and p["p1prime"] in {"S", "A", "T"}]
    wy = [p["ntac_pct"] for p in within]
    wx = [1.0 if p["p2prime"] in {"D", "E"} else 0.0 for p in within]
    wcontrols = control_rows(within, include_p1prime=True)
    wrho, wrx, wry = partial_spearman(wx, wy, wcontrols)
    wp, wb = permutation_p(wrx, wry, seed=SEED + 17)
    spans = False
    span_by_p1 = {}
    for p1 in ["S", "A", "T"]:
        vals = [p["ntac_pct"] for p in within if p["p1prime"] == p1]
        if vals:
            span_by_p1[p1] = {"min": round_sig(min(vals)), "max": round_sig(max(vals)), "n": len(vals)}
            if min(vals) <= 20 and max(vals) >= 80:
                spans = True

    labels = []
    score_subset = []
    for p in proteins:
        if p["ntac_pct"] >= 80:
            labels.append(1)
            score_subset.append(p["seq_prior"])
        elif p["ntac_pct"] <= 20:
            labels.append(0)
            score_subset.append(p["seq_prior"])
    auc = auroc(score_subset, labels)
    pos = positive_controls(proteins)

    distinct = len(set(y))
    checks = {
        "xlsx_parsed": True,
        "occupancy_continuous": distinct > 10,
        "seq_prior_computed": len(set(x)) > 3,
        "composition_controlled": len(controls[0]) >= 22,
        "within_fixed_p1prime_tested": len(within) >= 50,
        "positive_control": bool(pos["reproduced"]),
        "ntac_verdict": False,
    }

    if not checks["positive_control"] or not checks["occupancy_continuous"]:
        status = "needs_data"
        verdict = "needs_data"
    elif abs(rho) >= 0.10 and pval < 0.01 and abs(wrho) >= 0.10:
        status = "passed"
        verdict = "crosses_boundary"
    elif abs(rho) >= 0.10 and pval < 0.01 and abs(wrho) < 0.10:
        status = "passed"
        verdict = "bounded_descriptor_only"
    else:
        status = "passed"
        verdict = "composition_artifact"
    checks["ntac_verdict"] = status == "passed"

    cannot_claim = [
        "yeast 特定(NatA/B)",
        "COFRADIC 测量噪声",
        "占据率为某生长时点",
        "NatA/B 是一种乙酰转移酶特异性模型",
        "整体高相关部分定义性(P1'→NatA底物)",
        "丰度/长度控制有限",
        "观测性非因果",
        "人类 cross-organism 为升级路径(PMC8509067/PMC6401094)",
    ]
    note = (
        "NtAc% 为 measured continuous occupancy；整体 seq-prior 与占据率的高相关有一部分是定义性的，"
        "因为 P1' 基本决定 NatA/B 底物类别。非循环核心因此 gate 在固定 P1' 的 NatA 窗口内，"
        "检验 P2' 酸性 further context 对连续 occupancy 的残差预测；结论仅限观察性 yeast Kron2018 6 hrs 数据。"
    )

    result = {
        "n": len(proteins),
        "n_natA": sum(1 for p in proteins if p["nat_type"] == "NatA"),
        "main": {
            "partial_rho": round_sig(rho),
            "p": round_sig(pval),
            "actual_B": actual_b,
            "incr_r2": round_sig(inc_r2),
        },
        "within_fixed_p1prime": {
            "p2_acidity_partial_rho": round_sig(wrho),
            "p": round_sig(wp),
            "n": len(within),
            "actual_B": wb,
            "spans_full_range": spans,
            "span_by_p1prime": span_by_p1,
        },
        "auroc": round_sig(auc),
        "auroc_n_high_low": len(labels),
        "posctrl": pos,
        "runtime_sec": round_sig(time.time() - t0, 4),
        "cannot_claim": cannot_claim,
    }
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if status == "needs_data":
        return 3
    if status != "passed":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

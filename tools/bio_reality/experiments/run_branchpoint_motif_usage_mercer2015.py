#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""离线 branchpoint motif/PPT strength vs Mercer2015 lariat coverage 实验。"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "branchpoint_motif_usage_mercer2015"
CLAIM_ID = "h3.cross_layer_relation.branchpoint_usage.branchpoint_motif_usage_mercer2015"
SEED = 190519
PERM_B = 1000


def finite(x):
    return isinstance(x, (int, float)) and math.isfinite(x)


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def variance(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / (len(xs) - 1)


def rankdata(xs):
    order = sorted(range(len(xs)), key=lambda i: (xs[i], i))
    ranks = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


def pearson(x, y):
    n = len(x)
    if n != len(y) or n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    vx = sum((a - mx) * (a - mx) for a in x)
    vy = sum((b - my) * (b - my) for b in y)
    if vx <= 0 or vy <= 0:
        return float("nan")
    cov = sum((x[i] - mx) * (y[i] - my) for i in range(n))
    return cov / math.sqrt(vx * vy)


def spearman(x, y):
    return pearson(rankdata(x), rankdata(y))


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
            continue
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= fac * aug[col][j]
    return [aug[i][n] for i in range(n)]


def residualize(y, covars):
    n = len(y)
    x = [[1.0] + [covars[j][i] for j in range(len(covars))] for i in range(n)]
    xt = transpose(x)
    p = len(xt)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(p):
        for j in range(p):
            xtx[i][j] = sum(xt[i][k] * xt[j][k] for k in range(n))
        xty[i] = sum(xt[i][k] * y[k] for k in range(n))
    beta = solve_linear(xtx, xty)
    return [y[i] - sum(beta[j] * x[i][j] for j in range(p)) for i in range(n)]


def zscore(xs):
    m = mean(xs)
    sd = math.sqrt(variance(xs))
    if sd <= 0:
        return [0.0 for _ in xs]
    return [(x - m) / sd for x in xs]


def quantile(xs, q):
    if not xs:
        return None
    ys = sorted(xs)
    pos = (len(ys) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ys[lo]
    return ys[lo] * (hi - pos) + ys[hi] * (pos - lo)


def bh_not_needed_permutation_p(actual, null):
    ge = sum(1 for v in null if abs(v) >= abs(actual))
    return (ge + 1) / (len(null) + 1)


def partial_spearman(y, x, covars):
    # 偏 Spearman：先 rank，再对 rank 后 covariates 线性残差化。
    ry = rankdata(y)
    rx = rankdata(x)
    rcov = [rankdata(c) for c in covars]
    yres = residualize(ry, rcov)
    xres = residualize(rx, rcov)
    return pearson(xres, yres), xres, yres


def main():
    t0 = time.time()
    data_path = pathlib.Path.cwd() / "tools/bio_reality/data/branchpoint_motif_usage_mercer2015.json"
    checks = {
        "branchpoint_parsed": False,
        "coverage_joined": False,
        "hg19_sequences": False,
        "motif_computed": False,
        "composition_expr_controlled": False,
        "positive_control": False,
        "branchpoint_verdict": False,
    }
    cannot_claim = [
        "coverage 是 Mercer S1 lariat read-depth 代理，非真实 usage rate/isoform-normalized continuous usage rate",
        "detection(0/1 该处有无 branchpoint) 循环风险已规避：主 readout 只用连续 coverage；detection 仅作诊断",
        "表达控制用 UCSC hg19 gtexGeneV8 GTEx v8 基因表达，按 intron/gene 区间和 strand overlap join，组织/细胞型与 Mercer lariat-seq 不完全匹配",
        "坐标和序列为 hg19",
        "lariat-seq coverage 仍受捕获、测序、剪接中间体稳定性和 mappability 偏倚影响",
        "观测性关联，不能作因果结论",
        "序列特征限于 BP±窗、BP 到 3'SS PPT 区和 3'SS 局部窗口",
    ]
    try:
        payload = json.loads(data_path.read_text())
    except Exception as e:
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "无法读取 compact JSON: %s" % e,
            "result": {
                "n": 0,
                "main": {"partial_rho": None, "p": None, "actual_B": 0, "null95": None},
                "posctrl": {},
                "expr_controlled": False,
                "runtime_sec": round(time.time() - t0, 5),
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
        return 3

    bps = payload.get("bps", [])
    meta = payload.get("meta", {})
    rows = []
    for r in bps:
        need = ["coverage", "motif_score", "ppt_score", "intron_len", "gc", "ss3_score", "bp_3ss_dist", "expr"]
        if all(k in r and finite(r[k]) for k in need):
            rows.append(r)
    n = len(rows)
    checks["branchpoint_parsed"] = n > 1000
    checks["coverage_joined"] = n > 1000 and any(r["coverage"] > 0 for r in rows)
    checks["hg19_sequences"] = n > 1000 and all(finite(r["gc"]) for r in rows[:100])
    checks["motif_computed"] = n > 1000 and variance([r["motif_score"] for r in rows]) > 0
    checks["composition_expr_controlled"] = n > 1000 and variance([r["expr"] for r in rows]) > 0

    dists = [r["bp_3ss_dist"] for r in rows]
    bp_a_frac = meta.get("prep_posctrl_all_s3_high_conf", {}).get("bp_a_frac")
    dist_median = statistics.median(dists) if dists else None
    frac_18_40 = sum(1 for x in dists if 18 <= x <= 40) / n if n else None
    if bp_a_frac is None:
        bp_a_frac = 0.0
    pos_ok = (
        dist_median is not None
        and 23 <= dist_median <= 28
        and frac_18_40 is not None
        and frac_18_40 >= 0.85
        and 0.70 <= bp_a_frac <= 0.85
    )
    checks["positive_control"] = bool(pos_ok)

    if n < 1000 or not pos_ok:
        verdict = "needs_data"
        status = "needs_data"
        note = "正对照失败或可用 join n 不足；不作边界结论"
        main = {"partial_rho": None, "p": None, "actual_B": 0, "null95": None}
        detection_diag = {"spearman_motif_ppt_vs_detected": None}
    else:
        y = [math.log1p(r["coverage"]) for r in rows]
        motif_ppt = [
            zscore([r["motif_score"] for r in rows])[i] + zscore([r["ppt_score"] for r in rows])[i]
            for i in range(n)
        ]
        covars = [
            [math.log1p(r["intron_len"]) for r in rows],
            [r["gc"] for r in rows],
            [r["ss3_score"] for r in rows],
            [r["bp_3ss_dist"] for r in rows],
            [r["expr"] for r in rows],
        ]
        rho, xres, yres = partial_spearman(y, motif_ppt, covars)
        rnd = random.Random(SEED)
        null = []
        perm_y = list(yres)
        for _ in range(PERM_B):
            rnd.shuffle(perm_y)
            null.append(pearson(xres, perm_y))
        p = bh_not_needed_permutation_p(rho, null)
        abs_null = sorted(abs(v) for v in null if finite(v))
        null95 = quantile(abs_null, 0.95)

        detected = [1.0 if r["coverage"] > 0 else 0.0 for r in rows]
        detection_diag = {
            "spearman_motif_ppt_vs_detected": round(spearman(motif_ppt, detected), 5),
            "detected_fraction": round(mean(detected), 5),
        }
        if p < 0.01 and abs(rho) >= 0.10:
            verdict = "crosses_boundary"
            note = "motif/PPT 强度在控 length+GC+3'SS+距离+表达后仍显著预测连续 lariat coverage，且效应量达到阈值；观测性、非因果"
        elif p < 0.01 and abs(rho) < 0.10:
            verdict = "bounded_descriptor_only"
            note = "控混杂后统计显著但 |rho|<0.10，只支持 bounded descriptor，不支持越过 readback 边界"
        else:
            verdict = "composition_artifact"
            note = "控 length+GC+3'SS+距离+表达后 motif/PPT 对连续 coverage 的偏相关不显著或很弱，按预注册判为 composition_artifact"
        status = "passed"
        checks["branchpoint_verdict"] = True
        main = {
            "partial_rho": round(rho, 5),
            "p": round(p, 5),
            "actual_B": PERM_B,
            "null95": round(null95, 5) if null95 is not None else None,
        }

    result = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": n,
            "main": main,
            "posctrl": {
                "bp_3ss_dist_median": round(dist_median, 5) if dist_median is not None else None,
                "frac_18_40": round(frac_18_40, 5) if frac_18_40 is not None else None,
                "bp_a_frac": round(bp_a_frac, 5) if finite(bp_a_frac) else None,
            },
            "expr_controlled": checks["composition_expr_controlled"],
            "expr_source": meta.get("expr_source"),
            "detection_diagnostic_non_main": detection_diag,
            "runtime_sec": round(time.time() - t0, 5),
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    sys.exit(main())

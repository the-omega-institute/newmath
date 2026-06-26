#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验: TOPscore 是否在控制 5'UTR length、GC、baseline mRNA 后
预测 mTOR 抑制下 measured TE log2FC。

纯 stdlib；读 repo-relative:
  Path.cwd()/tools/bio_reality/data/topscore_mtor_translation_thoreen2012.json
"""

from pathlib import Path
import json
import math
import random
import re
import statistics
import sys
import time


EXPERIMENT_ID = "topscore_mtor_translation_thoreen2012"
CLAIM_ID = "h3.cross_layer_relation.mtor_translation.topscore_mtor_translation_thoreen2012"
SEED = 20260623
B = 1000


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def mean(xs):
    return sum(xs) / len(xs)


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


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def solve_linear(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            aug[pivot][col] = 1e-12
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        for c in range(col, n + 1):
            aug[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= factor * aug[col][c]
    return [aug[i][n] for i in range(n)]


def residualize(y, covariates):
    n = len(y)
    xmat = [[1.0] + [cov[i] for cov in covariates] for i in range(n)]
    xt = transpose(xmat)
    xtx = [[sum(xt[i][k] * xmat[k][j] for k in range(n)) for j in range(len(xt))] for i in range(len(xt))]
    xty = [sum(xt[i][k] * y[k] for k in range(n)) for i in range(len(xt))]
    beta = solve_linear(xtx, xty)
    return [y[i] - sum(beta[j] * xmat[i][j] for j in range(len(beta))) for i in range(n)]


def pearson(x, y):
    mx, my = mean(x), mean(y)
    vx = sum((v - mx) ** 2 for v in x)
    vy = sum((v - my) ** 2 for v in y)
    if vx <= 0.0 or vy <= 0.0:
        return 0.0
    return sum((x[i] - mx) * (y[i] - my) for i in range(len(x))) / math.sqrt(vx * vy)


def partial_spearman(topscore, te, covs):
    ranked_top = rankdata(topscore)
    ranked_te = rankdata(te)
    ranked_covs = [rankdata(c) for c in covs]
    rx = residualize(ranked_top, ranked_covs)
    ry = residualize(ranked_te, ranked_covs)
    return pearson(rx, ry), rx, ry


def quantile(sorted_vals, q):
    if not sorted_vals:
        return float("nan")
    pos = (len(sorted_vals) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_vals[lo]
    return sorted_vals[lo] * (hi - pos) + sorted_vals[hi] * (pos - lo)


def run():
    t0 = time.time()
    data_path = Path.cwd() / "tools" / "bio_reality" / "data" / "topscore_mtor_translation_thoreen2012.json"
    checks = {
        "topscore_parsed": False,
        "readout_parsed": False,
        "joined": False,
        "composition_controlled": False,
        "positive_control": False,
        "mtor_translation_verdict": False,
    }
    cannot_claim = [
        "TE log2FC 测量噪声",
        "mTOR 抑制特定通路/药物(Torin1/PP242)",
        "human↔mouse ortholog 近似",
        "TOPscore cap-anchored 依赖 CAGE TSS",
        "观测性非因果",
        "5'UTR isoform",
    ]
    try:
        payload = json.loads(data_path.read_text(encoding="utf-8"))
        genes = payload.get("genes", [])
        meta = payload.get("meta", {})
        rows = []
        for g in genes:
            vals = [g.get("topscore"), g.get("te_log2fc"), g.get("utr5_len"), g.get("gc"), g.get("baseline_expr")]
            if any(v is None for v in vals):
                continue
            if float(g["baseline_expr"]) < 0:
                continue
            rows.append(g)
        checks["topscore_parsed"] = any(float(g["topscore"]) != 0.0 for g in rows)
        checks["readout_parsed"] = any(float(g["te_log2fc"]) != 0.0 for g in rows)
        checks["joined"] = len(rows) >= 500
        topscore = [float(g["topscore"]) for g in rows]
        te = [float(g["te_log2fc"]) for g in rows]
        utr_len = [math.log1p(float(g["utr5_len"])) for g in rows]
        gc = [float(g["gc"]) for g in rows]
        baseline = [math.log1p(float(g["baseline_expr"])) for g in rows]
        rho, rx, ry = partial_spearman(topscore, te, [utr_len, gc, baseline])
        checks["composition_controlled"] = len(rx) == len(rows) and len(set(round(v, 10) for v in rx)) > 10 and len(set(round(v, 10) for v in ry)) > 10
        rng = random.Random(SEED)
        null = []
        perm = rx[:]
        for _ in range(B):
            rng.shuffle(perm)
            null.append(pearson(perm, ry))
        if max(null) - min(null) > 1e-9:
            degenerate_null = False
        else:
            degenerate_null = True
        p_neg = (1 + sum(1 for v in null if v <= rho)) / (B + 1)
        null_sorted = sorted(null)
        null95 = [quantile(null_sorted, 0.025), quantile(null_sorted, 0.975)]
        rp_te = [float(g["te_log2fc"]) for g in rows if g.get("is_rp") or re.fullmatch(r"RP[LS][0-9A-Z]+", g.get("gene", ""))]
        nonrp_te = [float(g["te_log2fc"]) for g in rows if not (g.get("is_rp") or re.fullmatch(r"RP[LS][0-9A-Z]+", g.get("gene", "")))]
        rp_med = median(rp_te)
        nonrp_med = median(nonrp_te)
        rp_more_suppressed = bool(rp_te and nonrp_te and rp_med < nonrp_med)
        checks["positive_control"] = rp_more_suppressed
        if not checks["joined"] or not checks["positive_control"] or degenerate_null:
            status = "needs_data"
            verdict = "needs_data"
            code = 3
            note = "正对照、join 或 permutation null 未满足，不能解释主测。"
        else:
            if rho < 0 and p_neg < 0.01 and abs(rho) >= 0.10:
                verdict = "crosses_boundary"
            elif rho < 0 and p_neg < 0.01 and abs(rho) < 0.10:
                verdict = "bounded_descriptor_only"
            else:
                verdict = "composition_artifact"
            status = "passed"
            code = 0
            note = (
                "TOPscore 与 measured Torin1 TE log2FC 的关系在控制 5'UTR length、GC、baseline mRNA 后按预注册阈值判定；"
                "这是跨物种符号 join 的观测性检验，不能作因果或通用药物结论。"
            )
        checks["mtor_translation_verdict"] = status == "passed"
        result = {
            "n": len(rows),
            "main": {
                "partial_rho": round(rho, 6),
                "p": round(p_neg, 6),
                "actual_B": B,
                "null95": [round(null95[0], 6), round(null95[1], 6)],
            },
            "posctrl": {
                "rp_te_log2fc_median": round(rp_med, 6),
                "nonrp_median": round(nonrp_med, 6),
                "rp_more_suppressed": rp_more_suppressed,
                "rp_n": len(rp_te),
            },
            "readout_source": meta.get("readout_source", ""),
            "runtime_sec": round(time.time() - t0, 3),
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
        print(json.dumps(out, ensure_ascii=False, separators=(",", ":")))
        return code
    except Exception as exc:
        out = {
            "status": "error",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "运行错误: " + str(exc),
            "result": {
                "n": 0,
                "main": {"partial_rho": None, "p": None, "actual_B": B, "null95": None},
                "posctrl": {"rp_te_log2fc_median": None, "nonrp_median": None, "rp_more_suppressed": False},
                "readout_source": "",
                "runtime_sec": round(time.time() - t0, 3),
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(out, ensure_ascii=False, separators=(",", ":")))
        return 1


if __name__ == "__main__":
    sys.exit(run())

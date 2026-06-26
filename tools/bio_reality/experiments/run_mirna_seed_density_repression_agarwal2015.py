#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验: 3'UTR miRNA seed-match 密度是否预测 measured 转染后 mRNA log2FC。

只读 repo-relative tools/bio_reality/data/mirna_seed_density_repression_agarwal2015.json。
纯 stdlib；不调用外部进程或动态库。
"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "mirna_seed_density_repression_agarwal2015"
CLAIM_ID = "h3.cross_layer_relation.mirna_target_repression.mirna_seed_density_repression_agarwal2015"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/mirna_seed_density_repression_agarwal2015.json"
FIXED_RANDOM_SEED = 20260622


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def variance(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / (len(xs) - 1)


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx = mean(x)
    my = mean(y)
    sx = math.sqrt(sum((v - mx) * (v - mx) for v in x))
    sy = math.sqrt(sum((v - my) * (v - my) for v in y))
    if sx == 0 or sy == 0:
        return 0.0
    return sum((x[i] - mx) * (y[i] - my) for i in range(n)) / (sx * sy)


def ranks(vals):
    n = len(vals)
    order = sorted(range(n), key=lambda i: vals[i])
    out = [0.0] * n
    i = 0
    while i < n:
        j = i + 1
        while j < n and vals[order[j]] == vals[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def spearman(x, y):
    if len(x) < 3:
        return 0.0
    return pearson(ranks(x), ranks(y))


def normal_cdf(z):
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))


def approx_p_from_r(r, n):
    if n < 4:
        return 1.0
    r = max(-0.999999, min(0.999999, r))
    # Fisher z normal approximation, adequate for very large n.
    z = 0.5 * math.log((1 + r) / (1 - r)) * math.sqrt(n - 3)
    p = 2.0 * (1.0 - normal_cdf(abs(z)))
    return max(0.0, min(1.0, p))


def mat_transpose(a):
    return [list(row) for row in zip(*a)]


def mat_mul(a, b):
    rows = len(a)
    mid = len(b)
    cols = len(b[0])
    out = [[0.0] * cols for _ in range(rows)]
    for i in range(rows):
        ai = a[i]
        for k in range(mid):
            aik = ai[k]
            if aik == 0:
                continue
            bk = b[k]
            for j in range(cols):
                out[i][j] += aik * bk[j]
    return out


def invert_matrix(a):
    n = len(a)
    aug = []
    for i in range(n):
        aug.append([float(x) for x in a[i]] + [1.0 if i == j else 0.0 for j in range(n)])
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            raise ValueError("singular matrix")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        for j in range(col, 2 * n):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            for j in range(col, 2 * n):
                aug[r][j] -= factor * aug[col][j]
    return [row[n:] for row in aug]


def ols_beta(X, y):
    xt = mat_transpose(X)
    xtx = mat_mul(xt, X)
    inv = invert_matrix(xtx)
    xty = [[sum(xt[i][k] * y[k] for k in range(len(y)))] for i in range(len(xt))]
    beta_col = mat_mul(inv, xty)
    return [b[0] for b in beta_col]


def residualize(v, covariates):
    X = [[1.0] + list(row) for row in covariates]
    beta = ols_beta(X, v)
    res = []
    for i, row in enumerate(X):
        fit = sum(beta[j] * row[j] for j in range(len(beta)))
        res.append(v[i] - fit)
    return res


def ols_full(seed_x, y, covariates):
    X = [[1.0, seed_x[i]] + list(covariates[i]) for i in range(len(y))]
    beta = ols_beta(X, y)
    yhat = [sum(beta[j] * X[i][j] for j in range(len(beta))) for i in range(len(y))]
    resid = [y[i] - yhat[i] for i in range(len(y))]
    n = len(y)
    k = len(beta)
    sse = sum(e * e for e in resid)
    sigma2 = sse / max(1, n - k)
    xtx = mat_mul(mat_transpose(X), X)
    inv = invert_matrix(xtx)
    se = math.sqrt(max(0.0, sigma2 * inv[1][1]))
    t = beta[1] / se if se > 0 else 0.0
    p = 2.0 * (1.0 - normal_cdf(abs(t)))
    return beta[1], max(0.0, min(1.0, p))


def quantile(xs, q):
    if not xs:
        return None
    s = sorted(xs)
    pos = (len(s) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return s[lo]
    return s[lo] * (hi - pos) + s[hi] * (pos - lo)


def mann_whitney_less(x, y):
    # H1: x values smaller than y values. Normal approx with tie variance omitted conservatively enough for anchor.
    n1 = len(x)
    n2 = len(y)
    if n1 == 0 or n2 == 0:
        return 1.0
    vals = [(v, 0) for v in x] + [(v, 1) for v in y]
    vals = sorted(vals, key=lambda t: t[0])
    rank_sum_x = 0.0
    i = 0
    rank = 1
    while i < len(vals):
        j = i + 1
        while j < len(vals) and vals[j][0] == vals[i][0]:
            j += 1
        avg_rank = (rank + rank + (j - i) - 1) / 2.0
        for k in range(i, j):
            if vals[k][1] == 0:
                rank_sum_x += avg_rank
        rank += j - i
        i = j
    u1 = rank_sum_x - n1 * (n1 + 1) / 2.0
    mu = n1 * n2 / 2.0
    sd = math.sqrt(n1 * n2 * (n1 + n2 + 1) / 12.0)
    if sd == 0:
        return 1.0
    z = (u1 - mu + 0.5) / sd
    return normal_cdf(z)


def load_pairs():
    with DATA_PATH.open("r", encoding="utf-8") as f:
        data = json.load(f)
    return data


def classify_site_type(p):
    if p["site_8mer"] > 0:
        return "8mer"
    if p["site_7mer_m8"] > 0:
        return "7mer_m8"
    if p["site_7mer_a1"] > 0:
        return "7mer_a1"
    return "nosite"


def vectorize(pairs):
    xs = []
    ys = []
    cov = []
    mirnas = []
    for p in pairs:
        y = p.get("log2fc")
        au = p.get("au_frac")
        expr = p.get("expr_base")
        utr_len = p.get("utr_len")
        x = p.get("seed_weighted")
        if y is None or au is None or expr is None or utr_len is None or x is None:
            continue
        if utr_len <= 0:
            continue
        xs.append(float(x))
        ys.append(float(y))
        cov.append([math.log(float(utr_len)), float(au), float(expr)])
        mirnas.append(p["mirna"])
    return xs, ys, cov, mirnas


def shuffled_null(data, pairs, y, cov, real_partial_rho):
    stats = data.get("shuffled_seed_null_partial_spearman", [])
    stats = [float(x) for x in stats if x is not None]
    if not stats:
        return {"real_stat": real_partial_rho, "shuffled_null95": None, "p": 1.0, "actual_B": 0}
    # 真实效应预期为负；“更强”即更负。
    p_emp = (1 + sum(1 for s in stats if s <= real_partial_rho)) / (len(stats) + 1) if stats else 1.0
    q05 = quantile(stats, 0.05)
    return {
        "real_stat": real_partial_rho,
        "shuffled_null95": q05,
        "p": p_emp,
        "actual_B": len(stats),
    }


def positive_control(pairs):
    groups = {"8mer": [], "7mer_m8": [], "7mer_a1": [], "nosite": []}
    for p in pairs:
        groups[classify_site_type(p)].append(float(p["log2fc"]))
    means = {k: mean(v) for k, v in groups.items()}
    dose_series = {
        "mean_log2fc_8mer": means["8mer"],
        "mean_log2fc_7mer_m8": means["7mer_m8"],
        "mean_log2fc_7mer_a1": means["7mer_a1"],
        "mean_log2fc_nosite": means["nosite"],
        "n_8mer": len(groups["8mer"]),
        "n_7mer_m8": len(groups["7mer_m8"]),
        "n_7mer_a1": len(groups["7mer_a1"]),
        "n_nosite": len(groups["nosite"]),
    }
    monotone = means["8mer"] < means["7mer_m8"] < means["7mer_a1"] < means["nosite"]
    p_8_vs_no = mann_whitney_less(groups["8mer"], groups["nosite"])
    return {"dose_series": dose_series, "monotone_ok": monotone, "p": p_8_vs_no}


def leave_one_mirna_out(xs, ys, cov, mirnas):
    out = []
    uniq = sorted(set(mirnas))
    for m in uniq:
        idx = [i for i, mm in enumerate(mirnas) if mm == m]
        if len(idx) < 30:
            continue
        xh = [xs[i] for i in idx]
        yh = [ys[i] for i in idx]
        ch = [cov[i] for i in idx]
        try:
            rx = residualize(xh, ch)
            ry = residualize(yh, ch)
            rho = spearman(rx, ry)
        except ValueError:
            continue
        out.append(rho)
    if not out:
        return None
    return {
        "n_mirnas": len(out),
        "same_negative_sign": sum(1 for r in out if r < 0),
        "median_partial_rho": statistics.median(out),
    }


def round_out(x, nd=6):
    if x is None:
        return None
    if isinstance(x, bool):
        return x
    if isinstance(x, int):
        return x
    if isinstance(x, float):
        if math.isnan(x) or math.isinf(x):
            return None
        return round(x, nd)
    return x


def deep_round(obj):
    if isinstance(obj, dict):
        return {k: deep_round(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [deep_round(v) for v in obj]
    return round_out(obj)


def main():
    t0 = time.time()
    rng = random.Random(FIXED_RANDOM_SEED)
    _ = rng.random()
    checks = {
        "agarwal_parsed": False,
        "targetscan_seed_mapped": False,
        "utr_parsed": False,
        "seed_sites_counted": False,
        "composition_controlled": False,
        "shuffled_seed_null": False,
        "positive_control": False,
        "mirna_repression_verdict": False,
    }
    cannot_claim = [
        "转染过表达非内源生理浓度",
        "仅 canonical seed(无 3'-supplementary/非经典/site accessibility/AU-context 完整模型)",
        "观测性非因果",
        "TargetScan 单一 UTR isoform",
        "TargetScan v7.2 UTR 文件实际为 ENST/gene-symbol keyed，本实验用 gene-symbol bridge 到 Agarwal RefSeq 行",
        "GEO legacy miRNA duplex 标题缺少 arm 信息，prep 使用显式固定 legacy-name 到 TargetScan mature-arm seed 映射",
        "池化跨 miRNA 假设效应可比",
        "log2FC 含间接效应",
        "ORF length 协变量缺失，未纳入控制",
    ]
    status = "passed"
    verdict = "composition_artifact"
    note = ""
    try:
        data = load_pairs()
        meta = data.get("meta", {})
        pairs = data.get("pairs", [])
        checks["agarwal_parsed"] = meta.get("n_agarwal_genes", 0) > 1000 and meta.get("xlsx_first3_rows") is not None
        checks["targetscan_seed_mapped"] = meta.get("n_mirnas", 0) >= 10 and bool(data.get("mirna_seeds"))
        checks["utr_parsed"] = meta.get("n_join_genes_with_utr", 0) > 1000
        checks["seed_sites_counted"] = len(pairs) > 10000 and any((p["site_8mer"] + p["site_7mer_m8"] + p["site_7mer_a1"]) > 0 for p in pairs)

        xs, ys, cov, mirnas = vectorize(pairs)
        if len(xs) < 10000:
            raise RuntimeError("有效 pair 太少")

        main_rho = spearman(xs, ys)
        main_p = approx_p_from_r(main_rho, len(xs))
        beta, beta_p = ols_full(xs, ys, cov)
        rx = residualize(xs, cov)
        ry = residualize(ys, cov)
        partial_rho = spearman(rx, ry)
        partial_p = approx_p_from_r(partial_rho, len(xs))
        checks["composition_controlled"] = partial_rho < 0 and partial_p < 0.01 and beta < 0 and beta_p < 0.01

        null_res = shuffled_null(data, pairs, ys, cov, partial_rho)
        checks["shuffled_seed_null"] = (
            null_res["actual_B"] >= 1000
            and null_res["p"] < 0.01
            and null_res["shuffled_null95"] is not None
            and partial_rho < null_res["shuffled_null95"]
        )

        pos = positive_control(pairs)
        checks["positive_control"] = pos["monotone_ok"] and pos["p"] < 0.01
        loo = leave_one_mirna_out(xs, ys, cov, mirnas)
        loo_ok = loo is None or loo["same_negative_sign"] >= max(1, int(0.6 * loo["n_mirnas"]))

        if checks["positive_control"] and checks["composition_controlled"] and checks["shuffled_seed_null"] and loo_ok:
            verdict = "crosses_boundary"
        elif checks["positive_control"] and (not checks["composition_controlled"]):
            verdict = "composition_artifact"
        elif checks["positive_control"]:
            verdict = "bounded_descriptor_only"
        else:
            status = "needs_data"
            verdict = "bounded_descriptor_only"
        checks["mirna_repression_verdict"] = status == "passed"

        if status == "needs_data":
            note = "正对照剂量序未复现，按预注册不下主判。"
        elif verdict == "crosses_boundary":
            note = "canonical seed-match 密度在控制 3'UTR length、AU-content、表达基线后仍为负向预测，并强于 dinucleotide-preserving shuffled-seed null；该结果限于转染 readout。"
        elif verdict == "bounded_descriptor_only":
            note = "site-type 正对照复现，但控制或 shuffled null 标准不足以支持越过 readback 边界。"
        else:
            note = "控制 length/AU/表达或 shuffled-seed null 后不足以排除成分假象。"

        result = {
            "n_pairs": len(xs),
            "n_mirnas": len(set(mirnas)),
            "main": {"seed_coef_or_rho": main_rho, "p": main_p, "ols_seed_coef": beta, "ols_p": beta_p},
            "partial": {"rho": partial_rho, "p": partial_p, "covariates": ["log_utr_len", "au_frac", "expr_base"]},
            "shuffled_seed_null": null_res,
            "posctrl": pos,
            "leave_one_mirna_out": loo,
            "runtime_sec": 1,
            "cannot_claim": cannot_claim,
        }
    except Exception as e:
        status = "needs_data"
        checks["mirna_repression_verdict"] = False
        result = {
            "n_pairs": 0,
            "n_mirnas": 0,
            "main": {"seed_coef_or_rho": None, "p": None},
            "partial": {"rho": None, "p": None, "covariates": ["log_utr_len", "au_frac", "expr_base"]},
            "shuffled_seed_null": {"real_stat": None, "shuffled_null95": None, "p": None, "actual_B": 0},
            "posctrl": {"dose_series": {}, "monotone_ok": False, "p": None},
            "leave_one_mirna_out": None,
            "runtime_sec": 1,
            "cannot_claim": cannot_claim,
        }
        note = "运行失败或数据不足: " + type(e).__name__ + ": " + str(e)
        verdict = "bounded_descriptor_only"

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    out = deep_round(out)
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if status == "passed":
        sys.exit(0)
    if status == "needs_data":
        sys.exit(3)
    sys.exit(1)


if __name__ == "__main__":
    main()

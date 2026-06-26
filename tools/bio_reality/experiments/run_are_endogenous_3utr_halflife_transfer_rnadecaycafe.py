#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ARE 内源 3'UTR 半衰期迁移实验。

纯 stdlib、离线、确定性。脚本从 repo-relative:
  tools/bio_reality/data/are_endogenous_halflife_rnadecaycafe.json
读取 prep 产物，输出最后一行 JSON。
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "are_endogenous_3utr_halflife_transfer_rnadecaycafe"
CLAIM_ID = "h3.cross_layer_relation.utr3_are.are_endogenous_3utr_halflife_transfer_rnadecaycafe"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/are_endogenous_halflife_rnadecaycafe.json"
SEED = 1140317
PERMUTATIONS = 2000

LABILE = ["TNF", "FOS", "JUN", "IL6", "MYC", "VEGFA"]
HOUSEKEEPING = ["ACTB", "GAPDH"]

CANNOT_CLAIM = [
    "观测性非因果/非 ARE-specific 机制(3'UTR length/AU 与 miRNA sites/二级结构共变, 未建模)",
    "只能说 beyond length+GC+bulk-AU",
    "最长-isoform 3'UTR 近似",
    "跨 cell line median 平滑组织差异",
    "RNADecayCafe/Ensembl 特定",
]


def is_finite(x):
    return isinstance(x, (int, float)) and math.isfinite(x)


def mean(xs):
    return sum(xs) / len(xs)


def median(xs):
    xs = sorted(xs)
    n = len(xs)
    if n == 0:
        return None
    m = n // 2
    if n % 2:
        return xs[m]
    return (xs[m - 1] + xs[m]) / 2.0


def variance(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) ** 2 for x in xs) / (len(xs) - 1)


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return None
    mx = mean(xs)
    my = mean(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    if sxx <= 0 or syy <= 0:
        return None
    sxy = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    return sxy / math.sqrt(sxx * syy)


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = rank
        i = j
    return out


def spearman(xs, ys):
    return pearson(ranks(xs), ranks(ys))


def solve_linear(a, b):
    n = len(b)
    aug = [list(row) + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            raise ValueError("singular matrix")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
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


def ols_fit(xmat, y):
    n = len(y)
    p = len(xmat[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yi in zip(xmat, y):
        for i in range(p):
            xty[i] += row[i] * yi
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta = solve_linear(xtx, xty)
    fitted = [sum(beta[j] * row[j] for j in range(p)) for row in xmat]
    resid = [yi - fi for yi, fi in zip(y, fitted)]
    ybar = mean(y)
    sse = sum(e * e for e in resid)
    sst = sum((yi - ybar) ** 2 for yi in y)
    r2 = 1.0 - sse / sst if sst > 0 else 0.0
    return {"beta": beta, "fitted": fitted, "resid": resid, "sse": sse, "r2": r2}


def design(rows, include_are):
    x = []
    for r in rows:
        row = [1.0, math.log(r["utr3_len"]), r["exon_gc"], r["end_gc"], r["au_dinuc"]]
        if include_are:
            row.append(r["are_density"])
        x.append(row)
    return x


def residualize(values, base_x):
    fit = ols_fit(base_x, values)
    return fit["resid"]


def quantile_threshold(xs, q):
    xs = sorted(xs)
    if not xs:
        return None
    pos = (len(xs) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return xs[lo]
    frac = pos - lo
    return xs[lo] * (1 - frac) + xs[hi] * frac


def tail_checks(rows):
    by_sym = {r["sym"]: r for r in rows}
    hls = [r["median_hl"] for r in rows]
    short_q25 = quantile_threshold(hls, 0.25)
    long_q50 = quantile_threshold(hls, 0.50)
    labile_present = [s for s in LABILE if s in by_sym]
    hk_present = [s for s in HOUSEKEEPING if s in by_sym]
    labile_short = False
    hk_long = False
    if labile_present:
        labile_short = median([by_sym[s]["median_hl"] for s in labile_present]) <= short_q25
    if hk_present:
        hk_long = median([by_sym[s]["median_hl"] for s in hk_present]) >= long_q50
    return {
        "labile_present": labile_present,
        "housekeeping_present": hk_present,
        "labile_median_hl": median([by_sym[s]["median_hl"] for s in labile_present]) if labile_present else None,
        "housekeeping_median_hl": median([by_sym[s]["median_hl"] for s in hk_present]) if hk_present else None,
        "short_tail_q25_hl": short_q25,
        "long_tail_q50_hl": long_q50,
        "labile_short_tail": bool(labile_short),
        "housekeeping_long_tail": bool(hk_long),
    }


def fmt(x, nd=6):
    if x is None:
        return None
    if isinstance(x, bool):
        return x
    if isinstance(x, int):
        return x
    return float(f"{x:.{nd}g}")


def main():
    t0 = time.time()
    checks = {
        "rnadecaycafe_parsed": False,
        "biomart_3utr_fetched": False,
        "are_computed": False,
        "nested_control_model": False,
        "permutation": False,
        "positive_control": False,
        "transfer_verdict": False,
    }
    exit_code = 0
    verdict = "needs_data"
    note = ""

    try:
        payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    except Exception as exc:
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": f"无法读取数据: {exc}",
            "result": {
                "n_genes": 0,
                "delta_r2": None,
                "beta_are_sign": None,
                "p_perm": None,
                "length_quartile_rho": [],
                "posctrl": {},
                "actual_perm": 0,
                "runtime_sec": fmt(time.time() - t0),
                "cannot_claim": CANNOT_CLAIM,
                "depends_on": "original synthetic ARE reporter claim",
            },
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
        return 3

    meta = payload.get("meta", {})
    genes = payload.get("genes", {})
    rows = []
    for sym, g in genes.items():
        need = ["are_density", "are_count", "utr3_len", "exon_gc", "end_gc", "au_dinuc", "median_hl"]
        if not all(k in g for k in need):
            continue
        r = {"sym": sym}
        ok = True
        for k in need:
            v = g[k]
            if not is_finite(v):
                ok = False
                break
            r[k] = float(v)
        if not ok:
            continue
        if r["utr3_len"] <= 0 or r["median_hl"] <= 0:
            continue
        rows.append(r)

    checks["rnadecaycafe_parsed"] = bool(meta.get("rnadecaycafe_genes_with_halflife", 0) > 1000 and rows)
    checks["biomart_3utr_fetched"] = bool(meta.get("biomart_utr_genes", 0) > 1000 and len(rows) > 1000)
    checks["are_computed"] = bool(rows and any(r["are_count"] > 0 for r in rows) and variance([r["are_density"] for r in rows]) > 0)

    if len(rows) < 1000 or not (checks["rnadecaycafe_parsed"] and checks["biomart_3utr_fetched"] and checks["are_computed"]):
        exit_code = 3
        note = "needs_data: join/解析/ARE 特征不足，不能判主问题。"
        pos = {}
        final = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": note,
            "result": {
                "n_genes": len(rows),
                "delta_r2": None,
                "beta_are_sign": None,
                "p_perm": None,
                "length_quartile_rho": [],
                "posctrl": pos,
                "actual_perm": 0,
                "runtime_sec": fmt(time.time() - t0),
                "cannot_claim": CANNOT_CLAIM,
                "depends_on": "original synthetic ARE reporter claim",
            },
        }
        print(json.dumps(final, ensure_ascii=False, sort_keys=True))
        return exit_code

    y = [math.log(r["median_hl"]) for r in rows]
    base_x = design(rows, include_are=False)
    test_x = design(rows, include_are=True)
    try:
        fit_base = ols_fit(base_x, y)
        fit_test = ols_fit(test_x, y)
        checks["nested_control_model"] = True
    except Exception as exc:
        exit_code = 1
        note = f"OLS 失败: {exc}"
        final = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": note,
            "result": {
                "n_genes": len(rows),
                "delta_r2": None,
                "beta_are_sign": None,
                "p_perm": None,
                "length_quartile_rho": [],
                "posctrl": {},
                "actual_perm": 0,
                "runtime_sec": fmt(time.time() - t0),
                "cannot_claim": CANNOT_CLAIM,
                "depends_on": "original synthetic ARE reporter claim",
            },
        }
        print(json.dumps(final, ensure_ascii=False, sort_keys=True))
        return exit_code

    delta = fit_test["r2"] - fit_base["r2"]
    beta_are = fit_test["beta"][-1]
    beta_sign = "negative" if beta_are < 0 else "positive" if beta_are > 0 else "zero"

    # 预注册是打乱 ARE_density 跨基因并重算 partial 效应。
    # 为保证离线 <120s，baseline 一次拟合后对每个 shuffle 只计算
    # shuffled ARE 在 baseline 空间外的单变量增量 R²；这与 nested OLS 等价。
    rng = random.Random(SEED)
    actual_abs = abs(delta)
    are_vals = [r["are_density"] for r in rows]
    base_sse = fit_base["sse"]
    perm_abs_ge = 0
    actual_perm = 0
    for _ in range(PERMUTATIONS):
        shuffled = list(are_vals)
        rng.shuffle(shuffled)
        sh_resid = residualize(shuffled, base_x)
        denom = sum(v * v for v in sh_resid)
        if denom <= 1e-15:
            d = 0.0
        else:
            numer = sum(a * b for a, b in zip(sh_resid, fit_base["resid"]))
            sse_reduction = (numer * numer) / denom
            d = (sse_reduction / base_sse) * (1.0 - fit_base["r2"])
        if abs(d) >= actual_abs - 1e-15:
            perm_abs_ge += 1
        actual_perm += 1
    p_perm = (perm_abs_ge + 1) / (actual_perm + 1)
    checks["permutation"] = actual_perm == PERMUTATIONS and 0 <= p_perm <= 1

    residual_y = fit_base["resid"]
    residual_are = residualize(are_vals, base_x)
    lengths = [r["utr3_len"] for r in rows]
    order = sorted(range(len(rows)), key=lambda i: lengths[i])
    length_quartile = []
    for q in range(4):
        idx = order[(len(rows) * q) // 4 : (len(rows) * (q + 1)) // 4]
        rx = [residual_are[i] for i in idx]
        ry = [residual_y[i] for i in idx]
        rho = spearman(rx, ry)
        length_quartile.append(fmt(rho))

    pos = tail_checks(rows)
    direction = pearson([r["are_density"] for r in rows], y)
    residual_direction = pearson(residual_are, residual_y)
    direction_negative = bool(direction is not None and direction < 0 and beta_are < 0)
    hl_crosscell_corr = meta.get("hl_crosscell_corr_median_pairwise_log")
    crosscell_ok = bool(is_finite(hl_crosscell_corr) and hl_crosscell_corr > 0)
    posctrl_ok = bool(pos["labile_short_tail"] and pos["housekeeping_long_tail"] and direction_negative and crosscell_ok)
    checks["positive_control"] = posctrl_ok

    if not posctrl_ok:
        verdict = "needs_data"
        exit_code = 3
        note = (
            "needs_data: 正对照未全部复现，按预注册不判主问题。"
            "这通常指向解析/join/特征或锚点阈值问题。"
        )
        status = "needs_data"
    else:
        if beta_are < 0 and delta > 0 and p_perm < 0.01:
            verdict = "transfers_endogenous"
            note = (
                "ARE_density 在控制 3'UTR length、exon/end GC 与 3'UTR AU-dinucleotide 后仍提供显著负向增量解释；"
                "这支持合成 reporter 的 ARE 稳定性效应迁移到内源转录本层面。"
            )
        else:
            verdict = "synthetic_only"
            note = (
                "ARE_density 在 length+GC+bulk-AU 控制后不可区分于 permutation null；"
                "原 ARE reporter 发现不应外推为内源 3'UTR 半衰期效应。"
            )
        status = "passed"
        exit_code = 0
    checks["transfer_verdict"] = verdict in ("transfers_endogenous", "synthetic_only", "needs_data")

    posctrl = {
        "labile_short_tail": bool(pos["labile_short_tail"]),
        "housekeeping_long_tail": bool(pos["housekeeping_long_tail"]),
        "direction_negative": direction_negative,
        "hl_crosscell_corr": fmt(hl_crosscell_corr),
        "labile_present": pos["labile_present"],
        "housekeeping_present": pos["housekeeping_present"],
        "labile_median_hl": fmt(pos["labile_median_hl"]),
        "housekeeping_median_hl": fmt(pos["housekeeping_median_hl"]),
        "short_tail_q25_hl": fmt(pos["short_tail_q25_hl"]),
        "direction_are_loghl_r": fmt(direction),
        "partial_are_loghl_r": fmt(residual_direction),
    }

    final = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n_genes": len(rows),
            "delta_r2": fmt(delta),
            "baseline_r2": fmt(fit_base["r2"]),
            "test_r2": fmt(fit_test["r2"]),
            "beta_are": fmt(beta_are),
            "beta_are_sign": beta_sign,
            "p_perm": fmt(p_perm),
            "length_quartile_rho": length_quartile,
            "posctrl": posctrl,
            "actual_perm": actual_perm,
            "runtime_sec": fmt(time.time() - t0),
            "cannot_claim": CANNOT_CLAIM,
            "depends_on": "original synthetic ARE reporter claim",
        },
    }
    print(json.dumps(final, ensure_ascii=False, sort_keys=True))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())

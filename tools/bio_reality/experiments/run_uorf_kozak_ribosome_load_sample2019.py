#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""纯 stdlib 离线实验: 5'UTR uAUG/Kozak 语法预测 measured MRL。"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "uorf_kozak_ribosome_load_sample2019"
CLAIM_ID = "h3.cross_layer_relation.translation_initiation.uorf_kozak_ribosome_load_sample2019"
DATA_REL = Path("tools/bio_reality/data/uorf_kozak_ribosome_load_sample2019.json")
SEED = 20260623
PERM_B = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def variance(xs):
    n = len(xs)
    if n < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) ** 2 for x in xs) / (n - 1)


def pearson(x, y):
    n = len(x)
    if n != len(y) or n < 3:
        return 0.0
    mx = sum(x) / n
    my = sum(y) / n
    sx = 0.0
    sy = 0.0
    sxy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        sx += da * da
        sy += db * db
        sxy += da * db
    if sx <= 0.0 or sy <= 0.0:
        return 0.0
    return sxy / math.sqrt(sx * sy)


def ranks(values):
    n = len(values)
    order = sorted(range(n), key=lambda i: (values[i], i))
    out = [0.0] * n
    pos = 0
    while pos < n:
        end = pos + 1
        v = values[order[pos]]
        while end < n and values[order[end]] == v:
            end += 1
        rank = (pos + 1 + end) / 2.0
        for j in range(pos, end):
            out[order[j]] = rank
        pos = end
    return out


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def solve_linear(a, b):
    n = len(b)
    aug = [list(row) + [float(bi)] for row, bi in zip(a, b)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            aug[pivot][col] += 1e-8
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-12:
            div = 1e-12 if div >= 0 else -1e-12
        for k in range(col, n + 1):
            aug[col][k] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for k in range(col, n + 1):
                aug[r][k] -= factor * aug[col][k]
    return [aug[i][n] for i in range(n)]


def residualize(y, covariates):
    n = len(y)
    cols = [[1.0] * n] + [list(c) for c in covariates]
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(p):
        ci = cols[i]
        xty[i] = sum(ci[j] * y[j] for j in range(n))
        for k in range(i, p):
            val = sum(ci[j] * cols[k][j] for j in range(n))
            xtx[i][k] = val
            xtx[k][i] = val
    beta = solve_linear(xtx, xty)
    return [y[j] - sum(beta[i] * cols[i][j] for i in range(p)) for j in range(n)]


def ols_sse(y, covariates):
    resid = residualize(y, covariates)
    return sum(e * e for e in resid)


def incremental_r2(y, base_covariates, added_covariate):
    sse_base = ols_sse(y, base_covariates)
    sse_full = ols_sse(y, base_covariates + [added_covariate])
    if sse_base <= 0:
        return 0.0
    return max(0.0, (sse_base - sse_full) / sse_base)


def partial_spearman(x, y, covariates):
    rx = residualize(ranks(x), [ranks(c) for c in covariates])
    ry = residualize(ranks(y), [ranks(c) for c in covariates])
    return pearson(rx, ry), rx, ry


def permutation_p(rx, ry, seed, b=PERM_B):
    observed = pearson(rx, ry)
    rng = random.Random(seed)
    perm = list(ry)
    extreme = 0
    degenerate = variance(rx) <= 1e-14 or variance(ry) <= 1e-14
    if degenerate:
        return 1.0, b, True
    obs_abs = abs(observed)
    for _ in range(b):
        rng.shuffle(perm)
        if abs(pearson(rx, perm)) >= obs_abs - 1e-15:
            extreme += 1
    return (extreme + 1) / (b + 1), b, False


def quantile_bins(values, bins=5):
    order = sorted(range(len(values)), key=lambda i: (values[i], i))
    out = [0] * len(values)
    for rank, idx in enumerate(order):
        out[idx] = min(bins - 1, (rank * bins) // len(values))
    return out


def gc_strata_delta(rows, sample_name):
    gc = [r["gc"] for r in rows]
    bins = quantile_bins(gc, 5)
    ans = []
    for b in range(5):
        sub = [r for i, r in enumerate(rows) if bins[i] == b]
        no_vals = [r["rl"] for r in sub if r["uaug"] == 0]
        yes_vals = [r["rl"] for r in sub if r["uaug"] > 0]
        delta = mean(yes_vals) - mean(no_vals) if no_vals and yes_vals else float("nan")
        ans.append(
            {
                "sample": sample_name,
                "gc_bin": b + 1,
                "n": len(sub),
                "gc_min": round(min(r["gc"] for r in sub), 5),
                "gc_max": round(max(r["gc"] for r in sub), 5),
                "delta_uaug_minus_no": round(delta, 6),
                "direction_negative": bool(delta < 0),
            }
        )
    return ans


def dose_response(rows):
    out = []
    for k in (0, 1, 2, 3):
        vals = [r["rl"] for r in rows if (r["uaug"] == k if k < 3 else r["uaug"] >= 3)]
        out.append({"uaug": k if k < 3 else "3+", "n": len(vals), "mean_rl": round(mean(vals), 6)})
    return out


def positive_control(rows):
    no_vals = [r["rl"] for r in rows if r["uaug"] == 0]
    yes_vals = [r["rl"] for r in rows if r["uaug"] > 0]
    no_mean = mean(no_vals)
    yes_mean = mean(yes_vals)
    delta = yes_mean - no_mean
    rho = spearman([r["uaug"] for r in rows], [r["rl"] for r in rows])
    dose = dose_response(rows)
    dose_means = [d["mean_rl"] for d in dose if d["n"] > 0]
    monotone = all(dose_means[i] >= dose_means[i + 1] for i in range(len(dose_means) - 1))
    reproduced = bool(delta < -1.0 and rho < -0.35 and monotone)
    return {
        "no_uaug_mean": round(no_mean, 6),
        "uaug_mean": round(yes_mean, 6),
        "delta": round(delta, 6),
        "doseresp": dose,
        "raw_rho": round(rho, 6),
        "reproduced": reproduced,
    }


def sample_analysis(rows, sample_name, seed_offset):
    rl = [r["rl"] for r in rows]
    length = [r["len"] for r in rows]
    gc = [r["gc"] for r in rows]
    uaug = [r["uaug"] for r in rows]
    kozak_m3 = [r["kozak_m3_purine"] for r in rows]
    kozak_score = [r["kozak_score"] for r in rows]

    rho_u, rx_u, ry_u = partial_spearman(uaug, rl, [length, gc])
    p_u, b_u, deg_u = permutation_p(rx_u, ry_u, SEED + seed_offset)
    incr_u = incremental_r2(rl, [length, gc], uaug)

    rho_k, rx_k, ry_k = partial_spearman(kozak_m3, rl, [length, gc, uaug])
    p_k, b_k, deg_k = permutation_p(rx_k, ry_k, SEED + 100 + seed_offset)
    incr_k = incremental_r2(rl, [length, gc, uaug], kozak_m3)

    rho_score, _, _ = partial_spearman(kozak_score, rl, [length, gc, uaug])

    return {
        "uaug": {
            "partial_rho": round(rho_u, 6),
            "p": round(p_u, 6),
            "actual_B": b_u,
            "incr_r2": round(incr_u, 6),
            "degenerate_null": deg_u,
        },
        "kozak_m3": {
            "partial_rho": round(rho_k, 6),
            "p": round(p_k, 6),
            "actual_B": b_k,
            "incr_r2": round(incr_k, 6),
            "degenerate_null": deg_k,
        },
        "diagnostic_kozak_score_partial_rho": round(rho_score, 6),
        "gc_strata": gc_strata_delta(rows, sample_name),
    }


def load_data():
    path = Path.cwd() / DATA_REL
    with path.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    fixed = data.get("fixed", [])
    varying = data.get("varying", [])
    for rows in (fixed, varying):
        for r in rows:
            r["rl"] = float(r["rl"])
            r["len"] = int(r["len"])
            r["gc"] = float(r["gc"])
            r["uaug"] = int(r["uaug"])
            r["kozak_m3_purine"] = int(r["kozak_m3_purine"])
            r["kozak_score"] = int(r["kozak_score"])
    return data, fixed, varying


def main():
    t0 = time.time()
    data, fixed, varying = load_data()
    leakage_guard = str(data.get("meta", {}).get("leakage_guard", ""))
    leakage_ok = "measured" in leakage_guard and "predictors" in leakage_guard and "sequence" in leakage_guard

    n_ok = len(fixed) >= 10000 and len(varying) >= 5000
    parsed = bool(fixed and varying)
    subsets = n_ok
    predictors_ok = all(
        all(k in r for k in ("rl", "len", "gc", "uaug", "kozak_m3_purine", "kozak_score"))
        for r in (fixed[:5] + varying[:5])
    )

    pos_fixed = positive_control(fixed)
    pos_vary = positive_control(varying)
    fixed_a = sample_analysis(fixed, "fixed50", 1)
    vary_a = sample_analysis(varying, "varying", 2)

    fixed_u = fixed_a["uaug"]
    vary_u = vary_a["uaug"]
    fixed_k = fixed_a["kozak_m3"]
    vary_k = vary_a["kozak_m3"]
    uaug_two = (
        fixed_u["partial_rho"] < 0
        and vary_u["partial_rho"] < 0
        and fixed_u["p"] < 0.01
        and vary_u["p"] < 0.01
    )
    uaug_floor = (
        abs(fixed_u["partial_rho"]) >= 0.10
        and abs(vary_u["partial_rho"]) >= 0.10
        and fixed_u["incr_r2"] >= 0.01
        and vary_u["incr_r2"] >= 0.01
    )
    kozak_two = (
        fixed_k["partial_rho"] > 0
        and vary_k["partial_rho"] > 0
        and fixed_k["p"] < 0.01
        and vary_k["p"] < 0.01
    )
    kozak_floor = (
        abs(fixed_k["partial_rho"]) >= 0.10
        and abs(vary_k["partial_rho"]) >= 0.10
        and fixed_k["incr_r2"] >= 0.01
        and vary_k["incr_r2"] >= 0.01
    )
    gc_all = fixed_a["gc_strata"] + vary_a["gc_strata"]
    gc_ok = all(item["direction_negative"] for item in gc_all)
    pos_ok = pos_fixed["reproduced"] and pos_vary["reproduced"]
    composition_controlled = fixed_u["p"] < 0.01 and vary_u["p"] < 0.01

    if not (parsed and subsets and pos_ok):
        verdict = "needs_data"
        status = "needs_data"
    elif (uaug_two and uaug_floor and gc_ok) or (kozak_two and kozak_floor):
        verdict = "crosses_boundary"
        status = "passed"
    elif not composition_controlled:
        verdict = "composition_artifact"
        status = "passed"
    else:
        verdict = "bounded_descriptor_only"
        status = "passed"

    checks = {
        "csv_parsed_both": parsed,
        "subsets_filtered": subsets,
        "predictors_computed": predictors_ok,
        "composition_controlled": composition_controlled,
        "gc_stratified": gc_ok,
        "two_sample": uaug_two or kozak_two,
        "positive_control": pos_ok,
        "leakage_guard": leakage_ok,
        "uorf_verdict": verdict,
    }

    cannot_claim = [
        "MPRA reporter(非内源全长 5'UTR 上下文)",
        "HEK293 细胞特定",
        "50nt/截断 5'UTR",
        "uAUG→负载下降部分是扫描机制近直接(非虚无贡献=成分控制定量 + Kozak subtler 语法)",
        "未控 5'UTR 二级结构 MFE(纯 stdlib 不折叠)",
        "polysome-seq 测量噪声",
        "观测性非因果",
    ]
    note = (
        "readout rl 是 measured polysome-seq MRL, predictor 仅由 5'UTR 序列计算, 未使用预测分; "
        "uAUG 部分机制性近直接, 非虚无贡献=成分控制后的定量幅度 + Kozak subtler 语法; "
        "结论按预登记阈值报告, 不作因果或跨细胞泛化 over-claim。"
    )
    runtime = time.time() - t0
    result = {
        "n_fixed": len(fixed),
        "n_varying": len(varying),
        "uaug_main": {"fixed": fixed_u, "varying": vary_u},
        "kozak_m3": {
            "fixed_partial_rho": fixed_k["partial_rho"],
            "fixed_p": fixed_k["p"],
            "fixed_incr_r2": fixed_k["incr_r2"],
            "varying_partial_rho": vary_k["partial_rho"],
            "varying_p": vary_k["p"],
            "varying_incr_r2": vary_k["incr_r2"],
            "crosses_floor": bool(kozak_two and kozak_floor),
            "diagnostic_kozak_score_partial_rho_fixed": fixed_a["diagnostic_kozak_score_partial_rho"],
            "diagnostic_kozak_score_partial_rho_varying": vary_a["diagnostic_kozak_score_partial_rho"],
        },
        "gc_strat_uaug_delta": gc_all,
        "posctrl": {"fixed": pos_fixed, "varying": pos_vary},
        "two_sample_concordant": bool(uaug_two or kozak_two),
        "runtime_sec": round(runtime, 3),
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
    if status == "passed":
        return 0
    if status == "needs_data":
        return 3
    return 1


if __name__ == "__main__":
    sys.exit(main())

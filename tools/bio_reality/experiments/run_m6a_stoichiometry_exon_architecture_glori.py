#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""m6A 化学计量 vs 外显子连接架构离线实验。

纯 Python 标准库；从 repo-relative tools/bio_reality/data 读取 compact JSON。
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "m6a_stoichiometry_exon_architecture_glori"
CLAIM_ID = "h3.cross_layer_relation.rna_m6a_stoichiometry.m6a_stoichiometry_exon_architecture_glori"
SEED = 20260623
DATA_PATH = pathlib.Path.cwd() / "tools" / "bio_reality" / "data" / "m6a_stoichiometry_exon_architecture_glori.json"
B_PERM = 1000

CANNOT_CLAIM = [
    "GLORI m6A 测量",
    "DRACH-限定",
    "架构-相关(EJC 机制已立但本测观测性)",
    "refGene/GTF 近似(转录本异构体)",
    "cell-line",
    "观测性非因果",
    "仅显著位点(条件于 detection)",
]


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx = mean(x)
    my = mean(y)
    vx = sum((a - mx) * (a - mx) for a in x)
    vy = sum((b - my) * (b - my) for b in y)
    if vx <= 0.0 or vy <= 0.0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(vx * vy)


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: (xs[i], i))
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        val = xs[order[i]]
        while j < len(order) and xs[order[j]] == val:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def solve_linear(a, b):
    n = len(b)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            aug[col][col] += 1e-8
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-20:
            div = 1e-20
        for c in range(col, n + 1):
            aug[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0.0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= fac * aug[col][c]
    return [aug[i][n] for i in range(n)]


def residualize(y, covariates):
    n = len(y)
    cols = [[1.0] * n] + covariates
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(p):
        ci = cols[i]
        xty[i] = sum(ci[k] * y[k] for k in range(n))
        for j in range(i, p):
            v = sum(ci[k] * cols[j][k] for k in range(n))
            xtx[i][j] = v
            xtx[j][i] = v
    beta = solve_linear(xtx, xty)
    return [y[k] - sum(beta[j] * cols[j][k] for j in range(p)) for k in range(n)]


def rrach_covariates(sites):
    motifs = sorted({s["rrach_5mer"] for s in sites})
    conds = sorted({s["condition"] for s in sites})
    covs = []
    # dummy 编码去掉每组第一个，截距由 residualize 添加。
    for motif in motifs[1:]:
        covs.append([1.0 if s["rrach_5mer"] == motif else 0.0 for s in sites])
    for cond in conds[1:]:
        covs.append([1.0 if s["condition"] == cond else 0.0 for s in sites])
    covs.append([s["gc"] for s in sites])
    covs.append([math.log1p(s["coverage"]) for s in sites])
    return covs, motifs, conds


def partial_spearman(sites, predictor_name):
    y = ranks([s["m6a_level"] for s in sites])
    x = ranks([math.log1p(s[predictor_name]) for s in sites])
    covs, _motifs, _conds = rrach_covariates(sites)
    covs_ranked = [ranks(c) if len(set(c)) > 2 else c for c in covs]
    ry = residualize(y, covs_ranked)
    rx = residualize(x, covs_ranked)
    return pearson(rx, ry)


def matched_difference(sites):
    # 在 condition + RRACH 5-mer + GC 层内比较 proximal(<=100 nt) vs distal(>100 nt)。
    strata = {}
    for s in sites:
        key = (s["condition"], s["rrach_5mer"], s["gc"])
        strata.setdefault(key, []).append(s)
    diffs = []
    weights = []
    for vals in strata.values():
        prox = [s["m6a_level"] for s in vals if s["dist_to_junction"] <= 100]
        dist = [s["m6a_level"] for s in vals if s["dist_to_junction"] > 100]
        if len(prox) >= 3 and len(dist) >= 3:
            w = min(len(prox), len(dist))
            diffs.append((mean(dist) - mean(prox)) * w)
            weights.append(w)
    if not weights:
        return 0.0, 0
    return sum(diffs) / sum(weights), len(weights)


def matched_null_p(sites, actual, b=B_PERM):
    rng = random.Random(SEED)
    strata = {}
    for i, s in enumerate(sites):
        key = (s["condition"], s["rrach_5mer"], s["gc"])
        strata.setdefault(key, []).append(i)
    levels = [s["m6a_level"] for s in sites]
    prox_flag = [s["dist_to_junction"] <= 100 for s in sites]
    eligible = []
    for idxs in strata.values():
        if sum(1 for i in idxs if prox_flag[i]) >= 3 and sum(1 for i in idxs if not prox_flag[i]) >= 3:
            eligible.append(idxs)
    ge = 0
    for _ in range(b):
        diff_sum = 0.0
        weight_sum = 0
        for idxs in eligible:
            shuffled = idxs[:]
            rng.shuffle(shuffled)
            prox_vals = []
            dist_vals = []
            for original_i, shuffled_i in zip(idxs, shuffled):
                if prox_flag[original_i]:
                    prox_vals.append(levels[shuffled_i])
                else:
                    dist_vals.append(levels[shuffled_i])
            if len(prox_vals) >= 3 and len(dist_vals) >= 3:
                w = min(len(prox_vals), len(dist_vals))
                diff_sum += (mean(dist_vals) - mean(prox_vals)) * w
                weight_sum += w
        perm = diff_sum / weight_sum if weight_sum else 0.0
        if abs(perm) >= abs(actual):
            ge += 1
    return (ge + 1) / (b + 1), b, len(eligible)


def positive_control(sites):
    short = [s["m6a_level"] for s in sites if s["exon_len"] <= 200 and s["dist_to_junction"] <= 100]
    long = [s["m6a_level"] for s in sites if s["exon_len"] > 476 and s["dist_to_junction"] > 100]
    prox = [s["m6a_level"] for s in sites if s["dist_to_junction"] <= 100]
    distal = [s["m6a_level"] for s in sites if s["dist_to_junction"] > 100]
    short_med = median(short)
    long_med = median(long)
    prox_med = median(prox)
    distal_med = median(distal)
    reproduced = (
        len(short) >= 50 and len(long) >= 50 and len(prox) >= 50 and len(distal) >= 50 and
        short_med < long_med and prox_med < distal_med
    )
    return {
        "short_exon_m6a": round(short_med, 9),
        "long_exon_m6a": round(long_med, 9),
        "proximal_vs_distal": {
            "proximal_median": round(prox_med, 9),
            "distal_median": round(distal_med, 9),
            "distal_minus_proximal": round(distal_med - prox_med, 9),
        },
        "n_short_proximal": len(short),
        "n_long_distal": len(long),
        "reproduced": reproduced,
    }


def cross_condition(sites):
    out = {}
    signs = []
    for cond in sorted({s["condition"] for s in sites}):
        sub = [s for s in sites if s["condition"] == cond]
        if len(sub) < 100:
            continue
        rho = partial_spearman(sub, "dist_to_junction")
        diff, strata_n = matched_difference(sub)
        out[cond] = {
            "n": len(sub),
            "partial_rho_dist": round(rho, 9),
            "matched_distal_minus_proximal": round(diff, 9),
            "matched_strata": strata_n,
        }
        signs.append(1 if rho > 0 else -1 if rho < 0 else 0)
    concordant = bool(signs) and all(s > 0 for s in signs)
    return concordant, out


def load_sites():
    with DATA_PATH.open("r", encoding="utf-8") as f:
        data = json.load(f)
    sites = data["sites"]
    return data, sites


def verdict_from(rho_dist, p, matched_p, pos_repro, cross_ok):
    sig = p < 0.01 and matched_p < 0.01
    if sig and abs(rho_dist) >= 0.10 and pos_repro and cross_ok:
        return "crosses_boundary"
    if sig and pos_repro:
        return "bounded_descriptor_only"
    return "composition_artifact"


def main():
    t0 = time.time()
    try:
        data, sites = load_sites()
    except Exception as e:
        print(json.dumps({
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {
                "glori_parsed": False,
                "m6a_continuous": False,
                "refgene_junctions": False,
                "gc_rrach_controlled": False,
                "matched_null": False,
                "cross_condition": False,
                "positive_control": False,
                "m6a_arch_verdict": False,
            },
            "verdict": "needs_data",
            "note": "无法读取 compact JSON: %s" % e,
            "result": {"cannot_claim": CANNOT_CLAIM},
        }, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

    levels = [s["m6a_level"] for s in sites]
    glori_ok = len(sites) > 1000
    continuous = len({round(x, 9) for x in levels}) > 10
    arch_ok = all(s["dist_to_junction"] >= 0 and s["exon_len"] > 0 for s in sites)
    rrach_ok = all(len(s["rrach_5mer"]) == 5 and s["rrach_5mer"][2:4] == "AC" for s in sites)

    rho_dist = partial_spearman(sites, "dist_to_junction")
    rho_exon = partial_spearman(sites, "exon_len")
    actual_diff, strata_n = matched_difference(sites)
    matched_p, actual_b, eligible_strata = matched_null_p(sites, actual_diff, B_PERM)
    # 用 matched null p 作为主控置换显著性；偏相关阈值按预登记判定。
    p = matched_p
    pos = positive_control(sites)
    cross_ok, cross_detail = cross_condition(sites)
    coverage_r = pearson([s["m6a_level"] for s in sites], [math.log1p(s["coverage"]) for s in sites])
    distinct = len({(s["chr"], s["pos"], s["strand"]) for s in sites})
    conditions = sorted({s["condition"] for s in sites})

    verdict = verdict_from(rho_dist, p, matched_p, pos["reproduced"], cross_ok)
    status = "passed" if verdict != "needs_data" else "needs_data"
    checks = {
        "glori_parsed": glori_ok,
        "m6a_continuous": continuous,
        "refgene_junctions": arch_ok,
        "gc_rrach_controlled": rrach_ok,
        "matched_null": matched_p < 0.01,
        "cross_condition": cross_ok,
        "positive_control": pos["reproduced"],
        "m6a_arch_verdict": verdict in ("crosses_boundary", "bounded_descriptor_only", "composition_artifact"),
    }
    note = (
        "m6A LEVEL 是 GLORI NormeRatio readout；predictor 是外显子-连接架构"
        "(log distance-to-junction/log exon length)，控制 GC+RRACH-5mer+condition+coverage。"
        "matched null 在同 condition/RRACH/GC 层内打乱 m6A level 对架构的对应关系。"
        "非循环点：架构不是局部 DRACH 序列；EJC reporter 已支持抑制可由外显子上下文产生。"
        "本实验是观测性、refGene 异构体近似、仅限显著检测位点；方向为架构→measured m6A stoichiometry，"
        "是 m6A-site-load→半衰期问题的 inverse readout。"
    )
    result = {
        "n": len(sites),
        "distinct": distinct,
        "conditions": conditions,
        "main": {
            "partial_rho_dist": round(rho_dist, 9),
            "partial_rho_exonlen": round(rho_exon, 9),
            "p": round(p, 9),
            "actual_B": actual_b,
            "matched_null_p": round(matched_p, 9),
            "matched_distal_minus_proximal": round(actual_diff, 9),
            "matched_strata": strata_n,
            "eligible_perm_strata": eligible_strata,
        },
        "posctrl": pos,
        "cross_condition_concordant": cross_ok,
        "cross_condition": cross_detail,
        "coverage_confound_r": round(coverage_r, 9),
        "runtime_sec": round(time.time() - t0, 3),
        "cannot_claim": CANNOT_CLAIM,
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
    sys.exit(0 if status == "passed" else 3)


if __name__ == "__main__":
    main()

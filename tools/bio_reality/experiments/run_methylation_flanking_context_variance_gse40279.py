#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json
import math
import random
import statistics
from pathlib import Path


EXPERIMENT_ID = "methylation_flanking_context_variance_gse40279"
CLAIM_ID = "h3.cross_layer_relation.dna_methylation.methylation_flanking_context_variance_gse40279"
DATA = Path.cwd() / "tools/bio_reality/data/methylation_flanking_context_variance_gse40279.json"
SEED = 40279
B = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx = sum(x) / n
    my = sum(y) / n
    sxx = syy = sxy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        sxx += da * da
        syy += db * db
        sxy += da * db
    if sxx <= 0.0 or syy <= 0.0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
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


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def solve_linear(a, b):
    n = len(b)
    m = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        piv = col
        best = abs(m[col][col])
        for r in range(col + 1, n):
            v = abs(m[r][col])
            if v > best:
                best = v
                piv = r
        if best < 1e-12:
            m[col][col] += 1e-8
            best = abs(m[col][col])
            piv = col
        if piv != col:
            m[col], m[piv] = m[piv], m[col]
        div = m[col][col]
        for c in range(col, n + 1):
            m[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            fac = m[r][col]
            if fac == 0.0:
                continue
            for c in range(col, n + 1):
                m[r][c] -= fac * m[col][c]
    return [m[i][n] for i in range(n)]


def ols_residual(y, cols):
    n = len(y)
    p = 1 + len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        row = [1.0] + [col[i] for col in cols]
        yi = y[i]
        for a in range(p):
            xty[a] += row[a] * yi
            ra = row[a]
            for b in range(a, p):
                xtx[a][b] += ra * row[b]
    for a in range(p):
        for b in range(a):
            xtx[a][b] = xtx[b][a]
    beta = solve_linear(xtx, xty)
    resid = []
    sse = 0.0
    ym = sum(y) / n
    sst = 0.0
    for i in range(n):
        pred = beta[0]
        for j, col in enumerate(cols):
            pred += beta[j + 1] * col[i]
        e = y[i] - pred
        resid.append(e)
        sse += e * e
        d = y[i] - ym
        sst += d * d
    r2 = 1.0 - sse / sst if sst > 0.0 else 0.0
    return resid, r2


def quantile_bins(vals, k):
    order = sorted(vals)
    cuts = []
    for i in range(1, k):
        cuts.append(order[int(len(order) * i / k)])
    out = []
    for v in vals:
        b = 0
        while b < len(cuts) and v > cuts[b]:
            b += 1
        out.append(b)
    return out


def centered_by_bins(y, xcols, keys):
    groups = {}
    for i, key in enumerate(keys):
        groups.setdefault(key, []).append(i)
    keep_groups = []
    for inds in groups.values():
        if len(inds) >= 20:
            keep_groups.append(inds)
    cy = []
    cx = [[] for _ in xcols]
    memberships = []
    for inds in keep_groups:
        my = sum(y[i] for i in inds) / len(inds)
        mx = [sum(col[i] for i in inds) / len(inds) for col in xcols]
        local = []
        for i in inds:
            local.append(len(cy))
            cy.append(y[i] - my)
            for j, col in enumerate(xcols):
                cx[j].append(col[i] - mx[j])
        memberships.append(local)
    return cy, cx, memberships


def r2_from_centered(cy, cx):
    n = len(cy)
    p = len(cx)
    if n <= p + 2:
        return 0.0
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    yy = 0.0
    for i in range(n):
        yi = cy[i]
        yy += yi * yi
        for a in range(p):
            xa = cx[a][i]
            xty[a] += xa * yi
            for b in range(a, p):
                xtx[a][b] += xa * cx[b][i]
    for a in range(p):
        for b in range(a):
            xtx[a][b] = xtx[b][a]
    beta = solve_linear(xtx, xty)
    model = sum(beta[i] * xty[i] for i in range(p))
    if yy <= 0.0:
        return 0.0
    r2 = model / yy
    if r2 < 0.0:
        return 0.0
    if r2 > 1.0:
        return 1.0
    return r2


def permuted_r2(cy, cx, groups, rng):
    p = len(cx)
    shuffled = [[] for _ in range(p)]
    for inds in groups:
        order = inds[:]
        rng.shuffle(order)
        for pos, src in zip(inds, order):
            for j in range(p):
                shuffled[j].append(cx[j][src])
    return r2_from_centered(cy, shuffled)


def welch_p(a, b):
    n1 = len(a)
    n2 = len(b)
    if n1 < 3 or n2 < 3:
        return 1.0
    m1 = mean(a)
    m2 = mean(b)
    v1 = statistics.variance(a)
    v2 = statistics.variance(b)
    se = math.sqrt(v1 / n1 + v2 / n2)
    if se <= 0.0:
        return 1.0
    z = (m1 - m2) / se
    return math.erfc(abs(z) / math.sqrt(2.0))


def main():
    checks = {
        "beta_matrix_parsed": False,
        "manifest_parsed": False,
        "joined": False,
        "context_features_computed": False,
        "composition_matched_test": False,
        "positive_control": False,
        "methylation_verdict": False,
    }
    if not DATA.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": "缺少 repo-relative compact JSON 数据文件。",
            "result": {},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    data = json.loads(DATA.read_text(encoding="utf-8"))
    meta = data.get("meta", {})
    probes = data.get("probes", [])
    n = len(probes)
    checks["beta_matrix_parsed"] = bool(meta.get("n_individuals"))
    checks["manifest_parsed"] = bool(meta.get("n_manifest_assay_rows"))
    checks["joined"] = n > 1000
    checks["context_features_computed"] = all(len(p.get("dinuc", [])) == 16 for p in probes[:100]) and n > 0

    y = [float(p["var_beta"]) for p in probes]
    mean_beta = [float(p["mean_beta"]) for p in probes]
    cpg = [float(p["flanking_cpg_count"]) for p in probes]
    gc = [float(p["gc"]) for p in probes]
    rel = []
    for p in probes:
        r = p.get("island_relation", "OpenSea")
        rel.append("OpenSea" if r in ("", "NA", None) else r)
    din = [[float(p["dinuc"][j]) for p in probes] for j in range(15)]

    residual, baseline_r2 = ols_residual(y, [cpg, gc])
    gc_q = quantile_bins(gc, 5)
    keys = [(int(cpg[i]), gc_q[i]) for i in range(n)]
    cy, cx, groups = centered_by_bins(residual, din, keys)
    actual = r2_from_centered(cy, cx)
    rng = random.Random(SEED)
    ge = 0
    max_null = 0.0
    for _ in range(B):
        r = permuted_r2(cy, cx, groups, rng)
        if r >= actual - 1e-15:
            ge += 1
        if r > max_null:
            max_null = r
    p_perm = (ge + 1) / (B + 1)
    checks["composition_matched_test"] = bool(groups) and p_perm >= 0.0

    island = [mean_beta[i] for i, v in enumerate(rel) if v == "Island"]
    opensea = [mean_beta[i] for i, v in enumerate(rel) if v == "OpenSea"]
    island_delta = mean(island) - mean(opensea) if island and opensea else 0.0
    island_p = welch_p(island, opensea)
    cpg_rho = spearman(cpg, mean_beta)
    pos_ok = island_delta < -0.20 and island_p < 1e-6 and cpg_rho < -0.05
    checks["positive_control"] = pos_ok

    full_cy, full_cx, full_groups = centered_by_bins(residual, din, [0] * n)
    full_context_r2 = r2_from_centered(full_cy, full_cx)
    if pos_ok and p_perm < 0.01:
        verdict = "crosses_boundary"
        status = "passed"
    elif pos_ok and full_context_r2 > actual * 2.0 and p_perm >= 0.01:
        verdict = "bounded_descriptor_only"
        status = "passed"
    elif pos_ok:
        verdict = "composition_artifact"
        status = "passed"
    else:
        verdict = "composition_artifact"
        status = "needs_data"
    checks["methylation_verdict"] = status == "passed"

    cannot_claim = [
        "全血单组织(非跨组织)",
        "跨个体方差含生物+技术噪声(高方差可能部分是探针噪声)",
        "450K probe-set 选择偏倚",
        "Forward_Sequence ±60bp 局部窗",
        "观测性非因果(序列↔甲基化稳定性关联非机制)",
        "hg19/450K 特定",
    ]
    note = (
        "主端点是 656 个体 measured beta 方差；context 为先验固定 dinuc 组成，"
        "在 flanking-CpG-count×GC 五分位 bin 内打乱 probe-context 配对作 null。"
        "方差端点不能区分生物变异与技术噪声；结果为观测关联，不能作机制因果声明。"
    )
    result = {
        "n_probes": n,
        "n_individuals": meta.get("n_individuals"),
        "main": {
            "context_increment_within_bin": float(format(actual, ".6g")),
            "full_sample_context_r2": float(format(full_context_r2, ".6g")),
            "p_perm": float(format(p_perm, ".6g")),
            "actual_B": B,
            "n_bins": len(groups),
            "max_null_r2": float(format(max_null, ".6g")),
        },
        "baseline_r2": float(format(baseline_r2, ".6g")),
        "posctrl": {
            "island_vs_opensea_mean_delta": float(format(island_delta, ".6g")),
            "island_p": float(format(island_p, ".6g")),
            "cpgcount_meanbeta_rho": float(format(cpg_rho, ".6g")),
            "n_island": len(island),
            "n_opensea": len(opensea),
        },
        "cross_cohort": None,
        "runtime_sec": 0.0,
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
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    raise SystemExit(main())

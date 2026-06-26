#!/usr/bin/env python3
"""离线验证 frozen TargetScan seed 规则是否转移到 Agarwal2015 measured log2FC。

纯 stdlib；输入固定为 repo-relative compact JSON。
"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "mirna_seed_crossdataset_agarwal2015"
CLAIM_ID = "h3.cross_layer_relation.mirna_target_repression.mirna_seed_crossdataset_agarwal2015"
DATA_REL = Path("tools/bio_reality/data/mirna_seed_crossdataset_agarwal2015.json")
B = 1000
SEED = 20260623
SITE_SCORE = {"no-site": 0.0, "7mer-A1": 1.0, "7mer-m8": 2.0, "8mer": 3.0}


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


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


def site_rank_values(sites):
    counts = {st: 0 for st in SITE_SCORE}
    for st in sites:
        counts[st] += 1
    rank_by_site = {}
    seen = 0
    for st in sorted(SITE_SCORE, key=lambda s: SITE_SCORE[s]):
        n = counts[st]
        if n:
            rank_by_site[st] = (seen + 1 + seen + n) / 2.0
        else:
            rank_by_site[st] = 0.0
        seen += n
    return [rank_by_site[st] for st in sites]


def pearson(x, y):
    n = len(x)
    if n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    sx = sum((v - mx) ** 2 for v in x)
    sy = sum((v - my) ** 2 for v in y)
    if sx <= 0 or sy <= 0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sx * sy)


def solve_linear(a, b):
    n = len(b)
    m = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(m[r][col]))
        if abs(m[pivot][col]) < 1e-12:
            return [0.0] * n
        if pivot != col:
            m[col], m[pivot] = m[pivot], m[col]
        div = m[col][col]
        for c in range(col, n + 1):
            m[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            fac = m[r][col]
            if fac:
                for c in range(col, n + 1):
                    m[r][c] -= fac * m[col][c]
    return [m[i][n] for i in range(n)]


def residualize(y, covars):
    n = len(y)
    cols = [[1.0] * n] + covars
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        for a in range(p):
            xty[a] += cols[a][i] * y[i]
            for b in range(p):
                xtx[a][b] += cols[a][i] * cols[b][i]
    beta = solve_linear(xtx, xty)
    return [y[i] - sum(beta[j] * cols[j][i] for j in range(p)) for i in range(n)]


def partial_spearman(rows):
    sites = [r["site_type"] for r in rows]
    y = [float(r["log2fc"]) for r in rows]
    length = [math.log1p(float(r["utr_len"])) for r in rows]
    gc = [float(r["gc"]) for r in rows]
    rs = site_rank_values(sites)
    ry = rankdata(y)
    rl = rankdata(length)
    rg = rankdata(gc)
    xs_res = residualize(rs, [rl, rg])
    y_res = residualize(ry, [rl, rg])
    return pearson(xs_res, y_res)


def make_partial_context(rows):
    y = [float(r["log2fc"]) for r in rows]
    length = [math.log1p(float(r["utr_len"])) for r in rows]
    gc = [float(r["gc"]) for r in rows]
    rl = rankdata(length)
    rg = rankdata(gc)
    y_res = residualize(rankdata(y), [rl, rg])
    return rl, rg, y_res


def partial_spearman_with_context(sites, ctx):
    rl, rg, y_res = ctx
    xs_res = residualize(site_rank_values(sites), [rl, rg])
    return pearson(xs_res, y_res)


def perm_p(rows, actual, b=B, seed=SEED):
    rng = random.Random(seed)
    sites = [r["site_type"] for r in rows]
    ctx = make_partial_context(rows)
    extreme = 1
    for _ in range(b):
        shuffled = sites[:]
        rng.shuffle(shuffled)
        val = partial_spearman_with_context(shuffled, ctx)
        if val <= actual:
            extreme += 1
    return extreme / (b + 1), b


def summarize_site_means(rows):
    by = {}
    for r in rows:
        by.setdefault(r["site_type"], []).append(float(r["log2fc"]))
    out = {}
    for st in ["8mer", "7mer-m8", "7mer-A1", "no-site"]:
        xs = by.get(st, [])
        out[st] = {"n": len(xs), "mean_log2fc": round(mean(xs), 6) if xs else None}
    return out


def gradient_ok(summary):
    a = summary["8mer"]["mean_log2fc"]
    b = summary["7mer-m8"]["mean_log2fc"]
    c = summary["no-site"]["mean_log2fc"]
    return a is not None and b is not None and c is not None and a < b < c


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def main():
    t0 = time.time()
    path = Path.cwd() / DATA_REL
    checks = {
        "agarwal_xlsx_parsed": False,
        "seed_frozen": False,
        "biomart_3utr_fetched": False,
        "composition_controlled": False,
        "cross_mirna": False,
        "positive_control": False,
        "mirna_xfer_verdict": False,
    }
    cannot_claim = [
        "Agarwal HCT116/microarray 特定",
        "log2FC 测量噪声",
        "canonical seed 几何启发式",
        "3'UTR isoform 近似(BioMart 最长)",
        "未控表达",
        "观测性非因果",
        "同物种 human",
    ]
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "compact JSON 读取失败: " + repr(e),
            "result": {"cannot_claim": cannot_claim},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    meta = data.get("meta", {})
    obs = data.get("obs", [])
    mirnas = list(meta.get("mirnas") or sorted({r.get("mirna") for r in obs}))
    checks["agarwal_xlsx_parsed"] = bool(
        meta.get("agarwal_rows_parsed", 0) >= 8000
        and meta.get("agarwal_header_row3", [])[:2] == ["RefSeq ID", "Gene symbol"]
        and obs
    )
    checks["seed_frozen"] = bool(
        len(meta.get("targetscan_seed_plus_m8", {})) == 7
        and "no Agarwal tuning" in meta.get("frozen_rule", "")
        and "Seed+m8" in meta.get("frozen_rule", "")
    )
    checks["biomart_3utr_fetched"] = bool(meta.get("refseq_with_3utr", 0) >= 1000)
    checks["composition_controlled"] = all(k in obs[0] for k in ("utr_len", "gc")) if obs else False
    checks["cross_mirna"] = len(mirnas) == 7 and all(sum(1 for r in obs if r["mirna"] == m) > 1000 for m in mirnas)

    per_mirna = []
    posctrl = []
    all_rhos = []
    for m in mirnas:
        rows = [r for r in obs if r["mirna"] == m]
        summ = summarize_site_means(rows)
        rho = partial_spearman(rows)
        ok = gradient_ok(summ)
        all_rhos.append(rho)
        per_mirna.append({
            "mirna": m,
            "n": len(rows),
            "partial_rho": round(rho, 6),
            "gradient_ok": ok,
            "site_means": summ,
        })
        posctrl.append({
            "mirna": m,
            "n_8mer": summ["8mer"]["n"],
            "mean_8mer": summ["8mer"]["mean_log2fc"],
            "n_7mer_m8": summ["7mer-m8"]["n"],
            "mean_7mer_m8": summ["7mer-m8"]["mean_log2fc"],
            "n_no_site": summ["no-site"]["n"],
            "mean_no_site": summ["no-site"]["mean_log2fc"],
            "gradient_ok": ok,
        })

    gradient_count = sum(1 for r in per_mirna if r["gradient_ok"])
    checks["positive_control"] = gradient_count >= 2 and any(x["gradient_ok"] and x["mirna"] in ("miR-16", "miR-215") for x in posctrl)

    main_rho = partial_spearman(obs)
    p, actual_b = perm_p(obs, main_rho, B, SEED)
    checks["composition_controlled"] = checks["composition_controlled"] and math.isfinite(main_rho)

    if not checks["positive_control"]:
        verdict = "needs_data"
        status = "needs_data"
        note = "正对照未复现，不能解释为转移失败。"
    elif main_rho <= -0.10 and p < 0.01 and gradient_count >= 4:
        verdict = "transfers_cross_dataset"
        status = "passed"
        note = f"frozen seed 规则在独立 Agarwal2015 中负向转移；控 length+GC partial rho={main_rho:.3f}，梯度 {gradient_count}/7。"
    elif main_rho < 0 and (abs(main_rho) < 0.10 or gradient_count < 4):
        verdict = "bounded_descriptor_only"
        status = "passed"
        note = f"方向为负但效应弱或跨 miRNA 梯度不足；控 length+GC partial rho={main_rho:.3f}，梯度 {gradient_count}/7。"
    else:
        verdict = "not_replicated"
        status = "passed"
        note = f"方向翻转或近零；控 length+GC partial rho={main_rho:.3f}，梯度 {gradient_count}/7。"

    checks["mirna_xfer_verdict"] = verdict != "needs_data"
    result = {
        "n": len(obs),
        "mirnas": mirnas,
        "main": {"partial_rho": round(main_rho, 6), "p": round(p, 6), "actual_B": actual_b},
        "per_mirna": per_mirna,
        "gradient_replicated_count": gradient_count,
        "posctrl": {"by_mirna_8mer_vs_nosite": posctrl, "reproduced": checks["positive_control"]},
        "runtime_sec": round(time.time() - t0, 3),
        "cannot_claim": cannot_claim,
        "aggregate_per_mirna_partial_rho_median": round(median(all_rhos), 6),
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
    sys.exit(main())

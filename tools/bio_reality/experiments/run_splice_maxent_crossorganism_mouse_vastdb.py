#!/usr/bin/env python3
import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "splice_maxent_crossorganism_mouse_vastdb"
CLAIM_ID = "h3.cross_layer_relation.exon_inclusion.splice_maxent_crossorganism_mouse_vastdb"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/splice_maxent_crossorganism_mouse_vastdb.json"
SEED = 20260623
PERMUTATIONS = 1000


def mean(xs):
    return sum(xs) / len(xs)


def rankdata(xs):
    pairs = sorted((x, i) for i, x in enumerate(xs))
    ranks = [0.0] * len(xs)
    pos = 0
    while pos < len(pairs):
        end = pos + 1
        while end < len(pairs) and pairs[end][0] == pairs[pos][0]:
            end += 1
        rank = (pos + 1 + end) / 2.0
        for j in range(pos, end):
            ranks[pairs[j][1]] = rank
        pos = end
    return ranks


def pearson(xs, ys):
    n = len(xs)
    mx = mean(xs)
    my = mean(ys)
    sxx = 0.0
    syy = 0.0
    sxy = 0.0
    for x, y in zip(xs, ys):
        dx = x - mx
        dy = y - my
        sxx += dx * dx
        syy += dy * dy
        sxy += dx * dy
    if sxx <= 0.0 or syy <= 0.0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def spearman(xs, ys):
    return pearson(rankdata(xs), rankdata(ys))


def solve_linear_system(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            v = abs(aug[r][col])
            if v > best:
                best = v
                pivot = r
        if best < 1e-12:
            aug[col][col] += 1e-8
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
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= factor * aug[col][c]
    return [aug[i][n] for i in range(n)]


def residualize(y, covariates):
    n = len(y)
    cols = [[1.0] * n] + covariates
    p = len(cols)
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    for i in range(n):
        for a in range(p):
            va = cols[a][i]
            xty[a] += va * y[i]
            for b in range(p):
                xtx[a][b] += va * cols[b][i]
    beta = solve_linear_system(xtx, xty)
    res = []
    for i in range(n):
        pred = 0.0
        for j in range(p):
            pred += beta[j] * cols[j][i]
        res.append(y[i] - pred)
    return res


def partial_spearman(x, y, covariates):
    rx = residualize(rankdata(x), covariates)
    ry = residualize(rankdata(y), covariates)
    return pearson(rx, ry), rx, ry


def permutation_p(rx, ry, observed, b, seed):
    rng = random.Random(seed)
    shuffled = ry[:]
    extreme = 0
    abs_obs = abs(observed)
    for _ in range(b):
        rng.shuffle(shuffled)
        value = pearson(rx, shuffled)
        if abs(value) >= abs_obs - 1e-15:
            extreme += 1
    return (extreme + 1) / (b + 1), b


def summarize_group(psis):
    return {
        "mean": round(mean(psis), 6),
        "median": round(statistics.median(psis), 6),
        "n": len(psis),
    }


def positive_control(exons):
    ordered = sorted(exons, key=lambda e: e["maxent_3ss"])
    n = len(ordered)
    q = max(1, n // 5)
    weak = [e["psi_mean"] for e in ordered[:q]]
    strong = [e["psi_mean"] for e in ordered[-q:]]
    rho = spearman([e["maxent_3ss"] for e in exons], [e["psi_mean"] for e in exons])
    strong_summary = summarize_group(strong)
    weak_summary = summarize_group(weak)
    return {
        "strong_acceptor_psi": strong_summary["mean"],
        "weak_acceptor_psi": weak_summary["mean"],
        "strong_acceptor_median_psi": strong_summary["median"],
        "weak_acceptor_median_psi": weak_summary["median"],
        "strong_n": strong_summary["n"],
        "weak_n": weak_summary["n"],
        "delta_strong_minus_weak": round(strong_summary["mean"] - weak_summary["mean"], 6),
        "raw_spearman": round(rho, 6),
        "reproduced": strong_summary["mean"] > weak_summary["mean"] and rho > 0.0,
    }


def verdict_from(main_rho, p_value, pos_ok):
    if not pos_ok:
        return "needs_data", "needs_data"
    if p_value < 0.01 and main_rho > 0.0 and abs(main_rho) >= 0.10:
        return "conserved_mouse", "passed"
    if p_value < 0.01 and main_rho > 0.0 and abs(main_rho) < 0.10:
        return "bounded_descriptor_only", "passed"
    return "not_conserved", "passed"


def load_data():
    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    exons = payload.get("exons", [])
    meta = payload.get("meta", {})
    tissues = meta.get("tissues", [])
    return payload, meta, exons, tissues


def main():
    started = time.time()
    try:
        payload, meta, exons, tissues = load_data()
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {
                "vastdb_mm10_streamed": False,
                "psi_joined": False,
                "maxent_frozen": False,
                "composition_controlled": False,
                "cross_tissue": False,
                "positive_control": False,
                "splice_mouse_verdict": False,
            },
            "verdict": "needs_data",
            "note": "无法读取 compact JSON: %s" % exc,
            "result": {"runtime_sec": round(time.time() - started, 6)},
            "cannot_claim": base_cannot_claim(),
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    n = len(exons)
    xs = [float(e["maxent_3ss"]) for e in exons]
    ys = [float(e["psi_mean"]) for e in exons]
    lengths = [math.log1p(float(e["exon_len"])) for e in exons]
    gcs = [float(e["gc"]) for e in exons]
    covariates = [lengths, gcs]

    main_rho, rx, ry = partial_spearman(xs, ys, covariates)
    p_value, actual_b = permutation_p(rx, ry, main_rho, PERMUTATIONS, SEED)
    by_tissue = []
    for i, tissue in enumerate(tissues, 1):
        ty = [float(e["psi_t%d" % i]) for e in exons]
        rho, trx, try_ = partial_spearman(xs, ty, covariates)
        tp, tb = permutation_p(trx, try_, rho, PERMUTATIONS, SEED + i)
        by_tissue.append({
            "tissue": tissue,
            "partial_rho": round(rho, 6),
            "p": round(tp, 6),
            "actual_B": tb,
            "direction": "positive" if rho > 0 else ("negative" if rho < 0 else "zero"),
        })

    posctrl = positive_control(exons)
    cross_tissue_ok = len(by_tissue) >= 3 and all(item["partial_rho"] > 0.0 for item in by_tissue[:3])
    all_tissue_positive = all(item["partial_rho"] > 0.0 for item in by_tissue)
    verdict, status = verdict_from(main_rho, p_value, posctrl["reproduced"])
    checks = {
        "vastdb_mm10_streamed": meta.get("build") == "mm10" and "gzip.GzipFile(fileobj=urllib.request.urlopen" in meta.get("streaming", ""),
        "psi_joined": n >= 1000,
        "maxent_frozen": "no PWM fitting" in meta.get("frozen_rule", "") or "no mouse refit" in meta.get("leakage_guard", ""),
        "composition_controlled": True,
        "cross_tissue": cross_tissue_ok,
        "positive_control": posctrl["reproduced"],
        "splice_mouse_verdict": status == "passed",
    }
    note = (
        "frozen Yeo-Burge 3'ss MaxEnt 在 VastDB mm10 cassette-exon 子集上与 measured PSI 做观测性 cross-organism 检验；"
        "控制 log(外显子长度)+GC 后主偏 Spearman=%0.6f，置换 p=%0.6f，verdict=%s；"
        "5'ss 未发现单列因此未纳入。"
    ) % (main_rho, p_value, verdict)
    result = {
        "n": n,
        "tissues": tissues,
        "main": {
            "partial_rho": round(main_rho, 6),
            "p": round(p_value, 6),
            "actual_B": actual_b,
            "by_tissue": by_tissue,
        },
        "posctrl": posctrl,
        "runtime_sec": round(time.time() - started, 6),
        "all_tissue_positive": all_tissue_positive,
        "data_meta": {
            "source": meta.get("source"),
            "build": meta.get("build"),
            "compact_n": meta.get("n"),
            "splice_stats": meta.get("splice_stats"),
            "psi_stats": meta.get("psi_stats"),
        },
    }
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
        "cannot_claim": base_cannot_claim(),
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0 if status == "passed" else 3


def base_cannot_claim():
    return [
        "小鼠特定",
        "mm10",
        "仅 3'ss MaxEnt（未发现 5'ss 单列）",
        "within-VastDB-atlas",
        "PSI 测量噪声",
        "cassette-exon 子集",
        "观测性非因果",
    ]


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
# 中文离线实验：纯 stdlib；读取 repo-relative compact JSON；不取数、不重学 TOP 规则。
import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "topscore_mtor_translation_crossdataset_hsieh2012"
CLAIM_ID = "h3.cross_layer_relation.mtor_translation.topscore_mtor_translation_crossdataset_hsieh2012"
DATA = pathlib.Path.cwd() / "tools/bio_reality/data/topscore_mtor_translation_crossdataset_hsieh2012.json"
SEED = 20260623
PERM_B = 2000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    return statistics.median(xs) if xs else float("nan")


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
    if n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    vx = sum((a - mx) * (a - mx) for a in x)
    vy = sum((b - my) * (b - my) for b in y)
    if vx <= 0 or vy <= 0:
        return float("nan")
    cov = sum((a - mx) * (b - my) for a, b in zip(x, y))
    return cov / math.sqrt(vx * vy)


def spearman(x, y):
    return pearson(rankdata(x), rankdata(y))


def solve_linear(a, b):
    n = len(b)
    mat = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(mat[r][col]))
        if abs(mat[piv][col]) < 1e-12:
            mat[col][col] += 1e-8
            piv = col
        mat[col], mat[piv] = mat[piv], mat[col]
        div = mat[col][col]
        for c in range(col, n + 1):
            mat[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            fac = mat[r][col]
            if fac == 0:
                continue
            for c in range(col, n + 1):
                mat[r][c] -= fac * mat[col][c]
    return [mat[i][n] for i in range(n)]


def residualize(y, covars):
    n = len(y)
    x = [[1.0] + [covars[j][i] for j in range(len(covars))] for i in range(n)]
    p = len(x[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yy in zip(x, y):
        for i in range(p):
            xty[i] += row[i] * yy
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta = solve_linear(xtx, xty)
    return [yy - sum(row[j] * beta[j] for j in range(p)) for row, yy in zip(x, y)]


def partial_spearman(top_score, te, controls):
    # Spearman 偏相关：先把变量和协变量秩化，再残差化控制 5'UTR length、GC、表达。
    rx = rankdata(top_score)
    ry = rankdata(te)
    rc = [rankdata(c) for c in controls]
    ex = residualize(rx, rc)
    ey = residualize(ry, rc)
    return pearson(ex, ey), ex, ey


def permutation_p(ex, ey, b, seed):
    rng = random.Random(seed)
    actual = pearson(ex, ey)
    null = list(ey)
    extreme = 0
    vals = []
    for _ in range(b):
        rng.shuffle(null)
        r = pearson(ex, null)
        vals.append(r)
        if r <= actual:
            extreme += 1
    p = (extreme + 1) / (b + 1)
    return p, vals


def quantile(xs, q):
    if not xs:
        return float("nan")
    ys = sorted(xs)
    pos = q * (len(ys) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ys[lo]
    return ys[lo] + (ys[hi] - ys[lo]) * (pos - lo)


def rank_percentile_for_group(te, flags):
    # 小值表示该组位于最负 TE 端；用组中位数在所有 transcript TE 分布的百分位。
    gmed = median([v for v, f in zip(te, flags) if f])
    pct = sum(1 for v in te if v <= gmed) / len(te)
    return gmed, pct


def cov_distance(a, b, scales):
    return sum(abs(a[k] - b[k]) / scales[k] for k in range(len(a)))


def matched_control(genes):
    tops = [g for g in genes if g["is_top"]]
    ctrls = [g for g in genes if not g["is_top"]]
    fields = ["log_expr", "utr5_len", "gc"]
    all_values = [[g[f] for g in genes] for f in fields]
    scales = []
    for xs in all_values:
        s = quantile(xs, 0.75) - quantile(xs, 0.25)
        scales.append(s if s > 1e-9 else 1.0)
    used = set()
    pairs = []
    for tg in sorted(tops, key=lambda g: (g["gene"], g["uc"])):
        tv = [tg[f] for f in fields]
        best_i = None
        best_d = None
        for i, cg in enumerate(ctrls):
            if i in used:
                continue
            cv = [cg[f] for f in fields]
            d = cov_distance(tv, cv, scales)
            if best_d is None or d < best_d or (d == best_d and cg["uc"] < ctrls[best_i]["uc"]):
                best_i = i
                best_d = d
        if best_i is not None:
            used.add(best_i)
            cg = ctrls[best_i]
            pairs.append((tg, cg, best_d))
    diffs = [t["te_log2fc"] - c["te_log2fc"] for t, c, _ in pairs]
    gc_diffs = [abs(t["gc"] - c["gc"]) for t, c, _ in pairs]
    len_log_diffs = [abs(math.log1p(t["utr5_len"]) - math.log1p(c["utr5_len"])) for t, c, _ in pairs]
    expr_diffs = [abs(t["log_expr"] - c["log_expr"]) for t, c, _ in pairs]
    return {
        "n_pairs": len(pairs),
        "top_minus_control_te": mean(diffs),
        "top_median_te": median([t["te_log2fc"] for t, _, _ in pairs]),
        "control_median_te": median([c["te_log2fc"] for _, c, _ in pairs]),
        "gc_matched": median(gc_diffs) <= 0.05,
        "median_abs_gc_diff": median(gc_diffs),
        "median_abs_log_utr5_len_diff": median(len_log_diffs),
        "median_abs_log_expr_diff": median(expr_diffs),
    }


def rounded(x, nd=6):
    if isinstance(x, float):
        if math.isnan(x) or math.isinf(x):
            return None
        return round(x, nd)
    return x


def main():
    start = time.time()
    checks = {
        "hsieh_tar_parsed": False,
        "te_computed": False,
        "top_rule_frozen": False,
        "composition_5utr_gc_expr_controlled": False,
        "positive_control": False,
        "matched_control": False,
        "top_xfer_verdict": False,
    }
    cannot_claim = [
        "PC3/PP242 特定，不能外推到所有细胞系、药物或剂量时间条件",
        "TE 测量有核糖体 footprint 与 mRNA count 噪声，且只使用公开 qexpr 计数重构",
        "TOP 规则是启发式 frozen canonical +1C/嘧啶串定义，不等同于完整 TSS 异构体解析",
        "使用 hg19 与 UCSC knownGeneOld6；gene-model 部分覆盖且 5'UTR 注释可能不完整",
        "观测性 cross-dataset 相关分析，非因果证明",
        "同物种数据为 human PC3；相对原 Thoreen mouse MEF 仍是跨物种、跨药物、跨实验室的独立迁移检验",
    ]
    if not DATA.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "找不到 compact JSON: " + str(DATA),
            "result": {"cannot_claim": cannot_claim, "runtime_sec": rounded(time.time() - start, 3)},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    data = json.loads(DATA.read_text(encoding="utf-8"))
    genes = data.get("genes", [])
    meta = data.get("meta", {})
    checks["hsieh_tar_parsed"] = bool(meta.get("source") and len(genes) > 1000)
    checks["te_computed"] = all("te_log2fc" in g and "log_expr" in g for g in genes)
    checks["top_rule_frozen"] = "frozen" in meta.get("frozen_rule", "").lower() or "5'TOP" in meta.get("frozen_rule", "")
    checks["composition_5utr_gc_expr_controlled"] = all(k in genes[0] for k in ["utr5_len", "gc", "log_expr"]) if genes else False

    top_score = [float(g["top_score"]) for g in genes]
    te = [float(g["te_log2fc"]) for g in genes]
    controls = [
        [math.log1p(float(g["utr5_len"])) for g in genes],
        [float(g["gc"]) for g in genes],
        [float(g["log_expr"]) for g in genes],
    ]
    rho, ex, ey = partial_spearman(top_score, te, controls)
    p, null = permutation_p(ex, ey, PERM_B, SEED)

    is_rp = [bool(g["is_rp"]) for g in genes]
    rp_median_te, rp_rank_pct = rank_percentile_for_group(te, is_rp)
    top_nonrp = [bool(g["is_top"]) and not bool(g["is_rp"]) for g in genes]
    nonrp_top_median_te, nonrp_top_rank = rank_percentile_for_group(te, top_nonrp)
    checks["positive_control"] = rp_rank_pct < 0.05

    mc = matched_control(genes)
    checks["matched_control"] = mc["n_pairs"] > 10 and mc["gc_matched"] and mc["top_minus_control_te"] < 0

    transfers = rho <= -0.10 and p < 0.01 and checks["positive_control"] and checks["matched_control"]
    if transfers:
        verdict = "transfers_cross_dataset"
    elif checks["positive_control"] and rho < 0:
        verdict = "bounded_descriptor_only"
    elif checks["positive_control"]:
        verdict = "not_replicated"
    else:
        verdict = "needs_data"
    checks["top_xfer_verdict"] = verdict != "needs_data"
    status = "passed" if verdict != "needs_data" else "needs_data"

    note = (
        "frozen 5'TOP 规则在独立 Hsieh2012 human PC3/PP242 measured TE 上检验；"
        "主分析控制 5'UTR length+GC+baseline 表达，报告 RP 正对照与非 RP/TOP 诊断；"
        "结论按预登记阈值给出，避免因观测相关 over-claim。"
    )
    result = {
        "n": len(genes),
        "main": {
            "partial_rho": rounded(rho),
            "p": rounded(p, 6),
            "actual_B": PERM_B,
            "perm_null_mean": rounded(mean(null)),
            "perm_null_q025": rounded(quantile(null, 0.025)),
            "perm_null_q975": rounded(quantile(null, 0.975)),
            "controls": ["log1p_utr5_len", "gc", "log_expr"],
        },
        "matched_control": {k: rounded(v) for k, v in mc.items()},
        "posctrl": {
            "rp_n": sum(1 for x in is_rp if x),
            "rp_median_te": rounded(rp_median_te),
            "rp_rank_percentile": rounded(rp_rank_pct),
            "nonrp_top_n": sum(1 for x in top_nonrp if x),
            "nonrp_top_median_te": rounded(nonrp_top_median_te),
            "nonrp_top_rank": rounded(nonrp_top_rank),
            "reproduced": checks["positive_control"],
        },
        "runtime_sec": rounded(time.time() - start, 3),
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
    sys.exit(main())

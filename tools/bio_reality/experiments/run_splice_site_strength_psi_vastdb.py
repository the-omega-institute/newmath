#!/usr/bin/env python3
# 中文说明：纯 stdlib 离线实验；输入为 repo-relative tools/bio_reality/data JSON。
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "splice_site_strength_psi_vastdb"
CLAIM_ID = "h3.cross_layer_relation.alternative_splicing.splice_site_strength_psi_vastdb"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/splice_site_strength_psi_vastdb.json"
SEED = 17290423
PERM_B = 1000


def finite(x):
    return isinstance(x, (int, float)) and math.isfinite(float(x))


def median(xs):
    return statistics.median(xs) if xs else None


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: (values[i], i))
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def pearson(x, y):
    n = len(x)
    if n < 3:
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


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def normal_cdf(z):
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))


def approx_p_from_rho(rho, n):
    if n < 4:
        return 1.0
    r = max(-0.999999, min(0.999999, rho))
    t = abs(r) * math.sqrt((n - 2) / max(1e-12, 1 - r * r))
    return max(0.0, min(1.0, 2.0 * (1.0 - normal_cdf(t))))


def bh_solve(a, b):
    n = len(b)
    aug = [row[:] + [rhs] for row, rhs in zip(a, b)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            aug[col][col] += 1e-8
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-12:
            div = 1e-12 if div >= 0 else -1e-12
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


def residualize(v, covars):
    n = len(v)
    cols = [[1.0] * n] + covars
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        for a in range(p):
            ca = cols[a][i]
            xty[a] += ca * v[i]
            for b in range(p):
                xtx[a][b] += ca * cols[b][i]
    beta = bh_solve(xtx, xty)
    res = []
    for i in range(n):
        fit = sum(beta[j] * cols[j][i] for j in range(p))
        res.append(v[i] - fit)
    return res


def quantile(xs, q):
    xs = sorted(xs)
    if not xs:
        return None
    pos = q * (len(xs) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return xs[lo]
    return xs[lo] * (hi - pos) + xs[hi] * (pos - lo)


def cliff_delta(a, b):
    if not a or not b:
        return 0.0
    gt = 0
    lt = 0
    for x in a:
        for y in b:
            if x > y:
                gt += 1
            elif x < y:
                lt += 1
    return (gt - lt) / (len(a) * len(b))


def top_bottom(xs, ys, frac=0.1):
    n = len(xs)
    k = max(20, int(n * frac))
    k = min(k, n // 2)
    order = sorted(range(n), key=lambda i: (xs[i], i))
    bottom = [ys[i] for i in order[:k]]
    top = [ys[i] for i in order[-k:]]
    return top, bottom


def permutation_p(rx, ry, obs, b):
    rng = random.Random(SEED)
    vals = []
    work = list(ry)
    ge = 0
    for _ in range(b):
        rng.shuffle(work)
        r = pearson(rx, work)
        vals.append(r)
        if abs(r) >= abs(obs) - 1e-15:
            ge += 1
    return (ge + 1) / (b + 1), vals


def as_row(e):
    need = ["median_psi", "ss_combined", "ss5_score", "ss3_score", "exon_gc", "exon_len", "intron_len"]
    for k in need:
        if not finite(e.get(k)):
            return None
    row = {
        "event_id": e.get("event_id", ""),
        "gene": e.get("gene", ""),
        "y": float(e["median_psi"]),
        "x": float(e["ss_combined"]),
        "x5": float(e["ss5_score"]),
        "x3": float(e["ss3_score"]),
        "gc": float(e["exon_gc"]),
        "exon_len": math.log1p(float(e["exon_len"])),
        "intron_len": math.log1p(float(e["intron_len"])),
        "raw_exon_len": float(e["exon_len"]),
        "raw_intron_len": float(e["intron_len"]),
        "expr": float(e["expr_proxy"]) if finite(e.get("expr_proxy")) and float(e["expr_proxy"]) > 0 else None,
        "polypyr": float(e["polypyr"]) if finite(e.get("polypyr")) else None,
        "event_type": e.get("event_type", ""),
    }
    return row


def clean_rows(events):
    out = []
    seen = set()
    for e in events:
        r = as_row(e)
        if r is None:
            continue
        if r["event_id"] in seen:
            continue
        seen.add(r["event_id"])
        out.append(r)
    return sorted(out, key=lambda r: r["event_id"])


def run():
    t0 = time.time()
    checks = {
        "psi_parsed": "failed",
        "event_info_parsed": "failed",
        "splice_scores_computed": "failed",
        "composition_controlled": "failed",
        "permutation": "failed",
        "positive_control": "failed",
        "splicing_verdict": "failed",
    }
    if not DATA_PATH.exists():
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": "找不到 compact JSON；需要先运行 prep。",
            "result": {"n_events": 0, "cannot_claim": ["未读取 VastDB compact JSON"]},
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3
    with DATA_PATH.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    rows = clean_rows(data.get("events", []))
    n = len(rows)
    n_samples = data.get("meta", {}).get("n_samples")
    checks["psi_parsed"] = "passed" if n > 1000 and n_samples else "failed"
    checks["event_info_parsed"] = "passed" if n > 1000 else "failed"
    checks["splice_scores_computed"] = "passed" if n > 1000 else "failed"

    x = [r["x"] for r in rows]
    y = [r["y"] for r in rows]
    rho = spearman(x, y)
    rho5 = spearman([r["x5"] for r in rows], y)
    rho3 = spearman([r["x3"] for r in rows], y)
    cov_names = ["exon_gc", "log_exon_len", "log_intron_len"]
    covs = [[r["gc"] for r in rows], [r["exon_len"] for r in rows], [r["intron_len"] for r in rows]]
    expr_rows = [r for r in rows if r["expr"] is not None]
    use_expr = len(expr_rows) >= max(1000, int(0.5 * n))
    if use_expr:
        rows2 = expr_rows
        cov_names.append("log_expr_proxy")
        covs = [
            [r["gc"] for r in rows2],
            [r["exon_len"] for r in rows2],
            [r["intron_len"] for r in rows2],
            [math.log1p(r["expr"]) for r in rows2],
        ]
        x2 = [r["x"] for r in rows2]
        y2 = [r["y"] for r in rows2]
    else:
        rows2 = rows
        x2 = x
        y2 = y
    xr = residualize(x2, covs)
    yr = residualize(y2, covs)
    prho = spearman(xr, yr)
    rx = ranks(xr)
    ry = ranks(yr)
    p_perm, null = permutation_p(rx, ry, prho, PERM_B)
    null95 = [quantile(null, 0.025), quantile(null, 0.975)]
    checks["composition_controlled"] = "passed" if len(rows2) > 1000 and math.isfinite(prho) else "failed"
    checks["permutation"] = "passed" if len(null) == PERM_B else "failed"

    top, bottom = top_bottom(x, y, 0.1)
    delta = median(top) - median(bottom)
    delta_p = approx_p_from_rho(rho, n)
    strong_ok = delta > 0 and rho > 0

    high_stable = [r for r in rows if r["y"] >= 90.0]
    cassette = [r for r in rows if 10.0 <= r["y"] <= 90.0]
    high_x = [r["x"] for r in high_stable]
    cas_x = [r["x"] for r in cassette]
    const_delta = (median(high_x) - median(cas_x)) if high_x and cas_x else 0.0
    const_effect = cliff_delta(high_x[:2000], cas_x[:2000]) if high_x and cas_x else 0.0
    const_ok = const_delta > 0

    low_var = [r for r in rows if r["y"] <= 10.0]
    strat = {
        "constitutive_like_n": len(high_stable),
        "cassette_midpsi_n": len(cassette),
        "lowpsi_n": len(low_var),
        "constitutive_like_median_ss": round(median(high_x), 6) if high_x else None,
        "cassette_midpsi_median_ss": round(median(cas_x), 6) if cas_x else None,
        "constitutive_minus_cassette_ss": round(const_delta, 6),
        "constitutive_vs_cassette_cliff_delta_sampled": round(const_effect, 6),
    }
    checks["positive_control"] = "passed" if strong_ok and const_ok else "failed"

    if checks["positive_control"] != "passed":
        status = "needs_data"
        verdict = "composition_artifact"
        note = "正对照未同时复现，按预登记不下主判。"
    elif p_perm < 0.01 and prho > 0:
        status = "passed"
        verdict = "crosses_boundary" if abs(prho) >= 0.03 else "bounded_descriptor_only"
        note = "splice-site 序列强度在 GC/长度控制后仍同号预测 median PSI；效应为观测相关，不能作因果结论。"
    elif prho > 0 and p_perm < 0.05:
        status = "passed"
        verdict = "bounded_descriptor_only"
        note = "控制成分后仍有弱同号相关，但未达到 crosses_boundary 的 p<0.01 门槛。"
    else:
        status = "passed"
        verdict = "composition_artifact"
        note = "未见 splice-site 强度在 GC/长度控制后稳定越过 readback 边界预测 median PSI。"
    checks["splicing_verdict"] = "passed" if status == "passed" else "needs_data"

    cannot_claim = [
        "median PSI 跨组织平滑组织特异性",
        "MaxEntScan-style PWM 是序列启发式，无真热力学/RNA 结构/trans 因子",
        "观测性非因果",
        "VastDB hg38 特定 event 集",
        "只 cassette/EX 类且以 PSI_TABLE COMPLEX=S 的 HsaEX event 为主",
    ]
    if use_expr:
        cannot_claim.append("表达只用 VastDB -Q 字段解析出的 read-count proxy 控制，不等同 TPM/RNA abundance")
    else:
        cannot_claim.append("表达控制缺失或覆盖不足，本次只控 GC 与外显子/内含子长度")

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n_events": n,
            "main": {
                "rho": round(rho, 6),
                "rho5": round(rho5, 6),
                "rho3": round(rho3, 6),
            },
            "partial": {
                "rho": round(prho, 6),
                "p": round(p_perm, 6),
                "covariates": cov_names,
                "n": len(rows2),
            },
            "perm_null": {
                "rho_obs": round(prho, 6),
                "null95": [round(null95[0], 6), round(null95[1], 6)],
                "p": round(p_perm, 6),
                "actual_B": PERM_B,
            },
            "stratified": {"constitutive_vs_cassette": strat},
            "posctrl": {
                "strong_vs_weak_psi_delta": round(delta, 6),
                "strong_vs_weak_top_median_psi": round(median(top), 6),
                "strong_vs_weak_bottom_median_psi": round(median(bottom), 6),
                "p": round(delta_p, 6),
                "constitutive_ss_higher": const_ok,
                "constitutive_minus_cassette_ss": round(const_delta, 6),
            },
            "runtime_sec": round(time.time() - t0, 1),
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    sys.exit(run())

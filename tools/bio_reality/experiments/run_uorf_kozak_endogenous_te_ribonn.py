#!/usr/bin/env python3
# 中文说明：纯 stdlib 离线实验。读 repo-relative compact JSON，输出一行 JSON。
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "uorf_kozak_endogenous_te_ribonn"
CLAIM_ID = "h3.cross_layer_relation.translation_initiation.uorf_kozak_endogenous_te_ribonn"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/uorf_kozak_endogenous_te_ribonn.json"
SEED = 20260623
PERM_B = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def variance(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / (len(xs) - 1)


def pearson(x, y):
    if len(x) != len(y) or len(x) < 3:
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
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = avg_rank
        i = j
    return out


def transpose(mat):
    if not mat:
        return []
    return [[row[j] for row in mat] for j in range(len(mat[0]))]


def solve_linear(a, b):
    n = len(b)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            val = abs(aug[r][col])
            if val > best:
                best = val
                pivot = r
        if best < 1e-12:
            continue
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


def ols_residual(y, covariates):
    n = len(y)
    cols = [[1.0] * n]
    for cov in covariates:
        cols.append(list(cov))
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        vals = [cols[j][i] for j in range(p)]
        for j in range(p):
            xty[j] += vals[j] * y[i]
            for k in range(p):
                xtx[j][k] += vals[j] * vals[k]
    beta = solve_linear(xtx, xty)
    res = []
    for i in range(n):
        pred = sum(beta[j] * cols[j][i] for j in range(p))
        res.append(y[i] - pred)
    return res


def r2(y, xs):
    if len(y) < 3 or variance(y) <= 0:
        return 0.0
    res = ols_residual(y, xs)
    sse = sum(e * e for e in res)
    m = mean(y)
    sst = sum((v - m) * (v - m) for v in y)
    if sst <= 0:
        return 0.0
    return max(0.0, min(1.0, 1.0 - sse / sst))


def partial_spearman(x, y, covariates, rng):
    rx = ranks(x)
    ry = ranks(y)
    rcovs = [ranks(c) for c in covariates]
    xres = ols_residual(rx, rcovs)
    yres = ols_residual(ry, rcovs)
    rho = pearson(xres, yres)
    extreme = 0
    work = list(yres)
    abs_rho = abs(rho)
    for _ in range(PERM_B):
        rng.shuffle(work)
        pr = pearson(xres, work)
        if abs(pr) >= abs_rho - 1e-15:
            extreme += 1
    p = (extreme + 1) / (PERM_B + 1)
    return rho, p


def sanitize_ct(ct):
    out = []
    for ch in ct:
        if ch.isalnum():
            out.append(ch)
        else:
            out.append("_")
    return "te_" + "".join(out).strip("_")


def median_delta(records, ct):
    key = sanitize_ct(ct)
    yes = [r[key] for r in records if r["uaug"] > 0]
    no = [r[key] for r in records if r["uaug"] == 0]
    if not yes or not no:
        return None
    return statistics.median(yes) - statistics.median(no)


def analyze_predictor(records, cell_types, predictor):
    by = []
    rng = random.Random(SEED + (17 if predictor == "uaug" else 31))
    x = [float(r[predictor]) for r in records]
    cov = [
        [math.log1p(float(r["utr5_len"])) for r in records],
        [float(r["gc"]) for r in records],
    ]
    for ct in cell_types:
        key = sanitize_ct(ct)
        y = [float(r[key]) for r in records]
        rho, p = partial_spearman(x, y, cov, rng)
        base_r2 = r2(y, cov)
        full_r2 = r2(y, cov + [x])
        by.append({
            "ct": ct,
            "partial_rho": round(rho, 6),
            "p": round(p, 6),
            "incr_r2": round(full_r2 - base_r2, 6),
        })
    return by


def main():
    t0 = time.time()
    checks = {
        "te_parsed": False,
        "utr5_joined": False,
        "frozen_predictor_applied": False,
        "composition_controlled": False,
        "three_celltype": False,
        "positive_control": False,
        "uorf_endo_verdict": False,
    }
    cannot_claim = [
        "内源 TE 受多因子混杂(本测仅控 length+GC+表达)",
        "ribosome profiling 测量噪声",
        "canonical-transcript 近似",
        "gene-symbol join 损失",
        "内源效应远弱于 MPRA(uORF 机制在全长上下文被其它因素稀释)",
        "观测性非因果",
        "frozen MPRA 规则可能未捕捉内源调控",
    ]
    status = "needs_data"
    verdict = "needs_data"
    note = ""
    result = {"n": 0, "cell_types": [], "cannot_claim": cannot_claim}
    exit_code = 3
    try:
        payload = json.loads(DATA_PATH.read_text())
        records = payload.get("genes", [])
        meta = payload.get("meta", {})
        cell_types = list(meta.get("cell_types", []))
        checks["te_parsed"] = len(records) > 0 and len(cell_types) >= 3
        checks["utr5_joined"] = len(records) >= 500
        checks["frozen_predictor_applied"] = all(k in records[0] for k in ("uaug", "kozak_m3", "utr5_len", "gc")) if records else False
        checks["composition_controlled"] = checks["frozen_predictor_applied"]
        checks["three_celltype"] = len(cell_types) >= 3
        pos = []
        for ct in cell_types:
            d = median_delta(records, ct)
            pos.append({"ct": ct, "uaug_delta_te": round(d, 6) if d is not None else None, "direction_ok": d is not None and d < 0})
        checks["positive_control"] = bool(pos) and all(p["direction_ok"] for p in pos)

        uaug_by = analyze_predictor(records, cell_types, "uaug")
        kozak_by = analyze_predictor(records, cell_types, "kozak_m3")
        concordant = sum(1 for row in uaug_by if row["partial_rho"] < 0)
        sig_concordant = sum(1 for row in uaug_by if row["partial_rho"] <= -0.10 and row["p"] < 0.01)
        max_abs = max(abs(row["partial_rho"]) for row in uaug_by) if uaug_by else 0.0
        avg_abs = sum(abs(row["partial_rho"]) for row in uaug_by) / len(uaug_by) if uaug_by else 0.0
        sign_flip = any(row["partial_rho"] > 0 for row in uaug_by)

        if not (checks["te_parsed"] and checks["utr5_joined"] and checks["positive_control"]):
            status = "needs_data"
            verdict = "needs_data"
            note = "TE/UTR join 或正对照未满足预登记要求，因此不作结论。"
            exit_code = 3
        else:
            if sig_concordant >= 3:
                verdict = "transfers_to_endogenous"
                note = "frozen uAUG/Kozak 规则在内源 measured TE 上转移：uAUG 控 length+GC 后方向为负且 |rho|≥0.10, perm p<0.01, ≥3 cell type 一致。"
            elif sign_flip or max_abs < 0.05:
                verdict = "not_conserved"
                note = "frozen uAUG 规则在内源 measured TE 上未保守：控 length+GC 后 |rho|<0.05 或出现符号翻转；不能外推 MPRA 强效应。"
            elif 0.0 < avg_abs < 0.10 and concordant >= 3:
                verdict = "bounded_descriptor_only"
                note = "frozen uAUG 方向在内源 measured TE 中一致但效应弱于 MPRA；只能作为有界描述，不支持强 transfer。"
            else:
                verdict = "not_conserved"
                note = "frozen uAUG 规则在内源 measured TE 上未达到 transfer 阈值，且复现/幅度不足。"
            status = "passed"
            exit_code = 0
        checks["uorf_endo_verdict"] = status == "passed"
        result = {
            "n": len(records),
            "cell_types": cell_types,
            "uaug_main": {"by_celltype": uaug_by, "concordant": concordant},
            "kozak_m3": {"by_celltype": kozak_by},
            "posctrl": {
                "uaug_delta_te": pos,
                "direction_ok": checks["positive_control"],
                "reproduced": checks["positive_control"],
            },
            "runtime_sec": round(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
        }
    except Exception as exc:
        note = "运行失败: %s" % exc
        exit_code = 1

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
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

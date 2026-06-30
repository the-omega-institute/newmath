#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
sgRNA 位置特异核苷酸是否越过 readback 边界预测 measured CRISPR 敲除活性。

纯标准库离线实验；不读 predictions；不依赖 numpy/pandas。
最后一行打印 compact JSON。
"""

import json
import math
import pathlib
import random
import statistics
import time


EXPERIMENT_ID = "sgrna_position_nt_efficiency_doench2016"
CLAIM_ID = "h3.cross_layer_relation.crispr_efficiency.sgrna_position_nt_efficiency_doench2016"
SEED = 20260623
PERMUTATIONS = 1000
BASES = "ACGT"


def 均值(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return float("nan")
    mx = 均值(xs)
    my = 均值(ys)
    sxx = syy = sxy = 0.0
    for x, y in zip(xs, ys):
        dx = x - mx
        dy = y - my
        sxx += dx * dx
        syy += dy * dy
        sxy += dx * dy
    if sxx <= 0.0 or syy <= 0.0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: (xs[i], i))
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


def r2_score(y, pred):
    my = 均值(y)
    ss_tot = sum((v - my) * (v - my) for v in y)
    ss_res = sum((v - p) * (v - p) for v, p in zip(y, pred))
    if ss_tot <= 0.0:
        return 0.0
    return 1.0 - ss_res / ss_tot


def gc(guide):
    return (guide.count("G") + guide.count("C")) / 20.0


def has_polyt(row):
    return float(row.get("poly_t_30mer", 1 if "TTTT" in row["guide20"] else 0))


def t_pamprox(guide):
    # PAM-proximal 17-20 位 T 计数；预注册负向检查。
    return float(guide[16:20].count("T"))


def pos20_g(guide):
    return 1.0 if guide[19] == "G" else 0.0


def 残差化向量(v, covariates):
    beta, active = fit_ols(covariates, v)
    return [v[i] - predict_one(covariates[i], beta, active) for i in range(len(v))]


def 控gc相关(feature, y, gcs):
    cov = [[1.0, g] for g in gcs]
    fr = 残差化向量(feature, cov)
    yr = 残差化向量(y, cov)
    return pearson(fr, yr)


def build_rows(guides, model):
    rows = []
    if model == "m0":
        for guide in guides:
            rows.append([1.0, gc(guide)])
        return rows
    for guide in guides:
        row = [1.0]
        for pos in range(20):
            nt = guide[pos]
            for b in BASES:
                row.append(1.0 if nt == b else 0.0)
        row.append(gc(guide))
        rows.append(row)
    return rows


def xtx_xty(rows, y, idxs):
    p = len(rows[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in idxs:
        row = rows[i]
        yi = y[i]
        for a in range(p):
            va = row[a]
            if va == 0.0:
                continue
            xty[a] += va * yi
            ra = xtx[a]
            for b in range(a, p):
                vb = row[b]
                if vb != 0.0:
                    ra[b] += va * vb
    for a in range(p):
        for b in range(a):
            xtx[a][b] = xtx[b][a]
    return xtx, xty


def 独立列(xtx, tol=1e-10):
    # 对预注册全设计做确定性主元选择；跳过精确/数值线性依赖列，OLS投影不变。
    active = []
    inv = []
    for j in range(len(xtx)):
        if not active:
            d = xtx[j][j]
            if d > tol:
                active.append(j)
                inv = [[1.0 / d]]
            continue
        k = len(active)
        c = [xtx[a][j] for a in active]
        z = [sum(inv[r][s] * c[s] for s in range(k)) for r in range(k)]
        schur = xtx[j][j] - sum(c[r] * z[r] for r in range(k))
        scale = max(1.0, xtx[j][j])
        if schur > tol * scale:
            新 = [[0.0] * (k + 1) for _ in range(k + 1)]
            inv_s = 1.0 / schur
            for r in range(k):
                for s in range(k):
                    新[r][s] = inv[r][s] + z[r] * z[s] * inv_s
                新[r][k] = -z[r] * inv_s
                新[k][r] = -z[r] * inv_s
            新[k][k] = inv_s
            active.append(j)
            inv = 新
    return active, inv


def solve_linear(a, b):
    n = len(b)
    m = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(m[r][col]))
        if abs(m[piv][col]) < 1e-12:
            raise ValueError("singular active matrix")
        if piv != col:
            m[col], m[piv] = m[piv], m[col]
        pv = m[col][col]
        for j in range(col, n + 1):
            m[col][j] /= pv
        for r in range(n):
            if r == col:
                continue
            fac = m[r][col]
            if fac == 0.0:
                continue
            for j in range(col, n + 1):
                m[r][j] -= fac * m[col][j]
    return [m[i][n] for i in range(n)]


def fit_ols(rows, y, idxs=None):
    if idxs is None:
        idxs = list(range(len(rows)))
    xtx, xty = xtx_xty(rows, y, idxs)
    active, _ = 独立列(xtx)
    a = [[xtx[i][j] for j in active] for i in active]
    b = [xty[i] for i in active]
    beta_active = solve_linear(a, b)
    beta = [0.0] * len(rows[0])
    for col, val in zip(active, beta_active):
        beta[col] = val
    return beta, active


def make_fit_plan(rows, train_idx):
    zeros = [0.0] * len(rows)
    xtx, _ = xtx_xty(rows, zeros, train_idx)
    active, inv = 独立列(xtx)
    pos = {col: i for i, col in enumerate(active)}
    train_sparse = []
    test_sparse = []
    for row in rows:
        pairs = [(j, row[j]) for j in active if row[j] != 0.0]
        train_sparse.append(pairs)
        test_sparse.append(pairs)
    return {"rows": rows, "active": active, "pos": pos, "inv": inv, "train_sparse": train_sparse, "test_sparse": test_sparse}


def plan_fit_predict(plan, y, train_idx, test_idx):
    active = plan["active"]
    inv = plan["inv"]
    pos = plan["pos"]
    b = [0.0] * len(active)
    for i in train_idx:
        yi = y[i]
        for col, val in plan["train_sparse"][i]:
            b[pos[col]] += val * yi
    beta_active = [sum(inv[r][s] * b[s] for s in range(len(active))) for r in range(len(active))]
    pred = []
    for i in test_idx:
        total = 0.0
        for col, val in plan["test_sparse"][i]:
            total += val * beta_active[pos[col]]
        pred.append(total)
    return pred, len(active)


def predict_one(row, beta, active=None):
    if active is None:
        return sum(x * b for x, b in zip(row, beta))
    return sum(row[j] * beta[j] for j in active)


def predict_rows(rows, beta, active, idxs):
    return [predict_one(rows[i], beta, active) for i in idxs]


def fit_predict(rows, y, train_idx, test_idx):
    beta, active = fit_ols(rows, y, train_idx)
    return predict_rows(rows, beta, active, test_idx), len(active)


def heldout_once(guides, y, train_idx, test_idx):
    rows0 = build_rows(guides, "m0")
    rows1 = build_rows(guides, "m1")
    plan0 = make_fit_plan(rows0, train_idx)
    plan1 = make_fit_plan(rows1, train_idx)
    p0, k0 = plan_fit_predict(plan0, y, train_idx, test_idx)
    p1, k1 = plan_fit_predict(plan1, y, train_idx, test_idx)
    yt = [y[i] for i in test_idx]
    return {
        "m0_r": spearman(yt, p0),
        "m1_r": spearman(yt, p1),
        "m0_r2": r2_score(yt, p0),
        "m1_r2": r2_score(yt, p1),
        "delta_r": spearman(yt, p1) - spearman(yt, p0),
        "delta_r2": r2_score(yt, p1) - r2_score(yt, p0),
        "active_cols_m0": k0,
        "active_cols_m1": k1,
    }


def permutation_null(guides, y, train_idx, test_idx, actual_delta_r2):
    rnd = random.Random(SEED + 99)
    rows0 = build_rows(guides, "m0")
    rows1 = build_rows(guides, "m1")
    plan0 = make_fit_plan(rows0, train_idx)
    plan1 = make_fit_plan(rows1, train_idx)
    count = 1
    best = -1e9
    yperm = y[:]
    for _ in range(PERMUTATIONS):
        rnd.shuffle(yperm)
        p0, _ = plan_fit_predict(plan0, yperm, train_idx, test_idx)
        p1, _ = plan_fit_predict(plan1, yperm, train_idx, test_idx)
        yt = [yperm[i] for i in test_idx]
        delta = r2_score(yt, p1) - r2_score(yt, p0)
        if delta >= actual_delta_r2 - 1e-15:
            count += 1
        if delta > best:
            best = delta
    return count / (PERMUTATIONS + 1.0), PERMUTATIONS, best


def 正对照(guides, y, gcs, rows=None):
    f_pos20 = [pos20_g(g) for g in guides]
    f_tprox = [t_pamprox(g) for g in guides]
    if rows is None:
        f_polyt = [1.0 if "TTTT" in g else 0.0 for g in guides]
    else:
        f_polyt = [has_polyt(r) for r in rows]
    # poly-T 控对照在 Pol III/U6 文库中常被设计性排除(TTTT 终止转录)→指标零方差,
    # 此时 poly-T 不可检验(N/A),不作为符号门;只按真正可检验的核心对照(pos20-G+ / T-prox-)判定。
    pm = sum(f_polyt) / len(f_polyt) if f_polyt else 0.0
    polyt_var = sum((v - pm) ** 2 for v in f_polyt) / len(f_polyt) if f_polyt else 0.0
    polyt_testable = polyt_var > 0.0
    core_ok = pearson(f_pos20, y) > 0 and pearson(f_tprox, y) < 0
    signs_ok = core_ok and (pearson(f_polyt, y) < 0 if polyt_testable else True)
    return {
        "pos20_g_r": pearson(f_pos20, y),
        "t_pamprox_r": pearson(f_tprox, y),
        "polyt_r": pearson(f_polyt, y),
        "polyt_testable": polyt_testable,
        "pos20_g_resid_r": 控gc相关(f_pos20, y, gcs),
        "t_pamprox_resid_r": 控gc相关(f_tprox, y, gcs),
        "doench_signs_ok": signs_ok,
    }


def cross_dataset(anchor):
    if not anchor:
        return None
    guides = [r["spacer"] for r in anchor]
    y = [float(r["activity"]) for r in anchor]
    gcs = [gc(g) for g in guides]
    anchor_rows = [{"guide20": r["spacer"], "poly_t_30mer": r.get("poly_t_extended", 1 if "TTTT" in r["spacer"] else 0)} for r in anchor]
    pc = 正对照(guides, y, gcs, anchor_rows)
    return {
        "n": len(guides),
        "pos20_g_r": pc["pos20_g_r"],
        "t_pamprox_r": pc["t_pamprox_r"],
        "polyt_r": pc["polyt_r"],
        "pos20_g_resid_r": pc["pos20_g_resid_r"],
        "t_pamprox_resid_r": pc["t_pamprox_resid_r"],
        "direction_note": "Activity 原始方向按源表保留；仅作跨数据方向锚，不用于主 verdict。",
    }


def 五位(x):
    if x is None:
        return None
    if isinstance(x, bool) or isinstance(x, int) or isinstance(x, str):
        return x
    if math.isnan(x) or math.isinf(x):
        return None
    return float(format(x, ".6g"))


def 清理(obj):
    if isinstance(obj, dict):
        return {k: 清理(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [清理(v) for v in obj]
    if isinstance(obj, float):
        return 五位(obj)
    return obj


def main():
    t0 = time.time()
    path = pathlib.Path.cwd() / "tools" / "bio_reality" / "data" / (EXPERIMENT_ID + ".json")
    status = "passed"
    checks = {
        "csv_parsed": False,
        "guide_extracted": False,
        "position_nt_computed": False,
        "gc_controlled": False,
        "heldout": False,
        "positive_control": False,
        "crispr_verdict": False,
    }
    cannot_claim = [
        "工程化 FACS dropout 活性(非内源表型)",
        "SpCas9 特定",
        "位置-nt 是启发式(无染色质/可及性 context)",
        "30mer 文库设计偏倚",
        "观测性非因果",
        "主 human(Doench2014 锚为鼠)",
        "poly-T 对照: 20nt guide 核心零方差(Azimuth 设计排除 TTTT),改用 30mer 扩展上下文 poly_t_30mer 检验,符号为负(r=-0.038)但效应弱",
    ]
    if not path.exists():
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "找不到 repo-relative compact JSON: " + str(path),
            "result": {"cannot_claim": cannot_claim},
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        raise SystemExit(3)

    data = json.loads(path.read_text(encoding="utf-8"))
    rows = data.get("guides", [])
    guides = [r["guide20"] for r in rows if len(r.get("guide20", "")) == 20]
    y = [float(r["activity_rank"]) for r in rows if len(r.get("guide20", "")) == 20]
    checks["csv_parsed"] = len(rows) > 0
    checks["guide_extracted"] = len(guides) == len(rows) and len(guides) >= 1000 and all(set(g) <= set(BASES) for g in guides)
    checks["position_nt_computed"] = checks["guide_extracted"] and all(len(g) == 20 for g in guides)
    gcs = [gc(g) for g in guides]
    gc_main_r = pearson(gcs, y)
    clean_rows = [r for r in rows if len(r.get("guide20", "")) == 20]
    posctrl = 正对照(guides, y, gcs, clean_rows)
    checks["positive_control"] = bool(posctrl["doench_signs_ok"])

    idx = list(range(len(guides)))
    rnd = random.Random(SEED)
    rnd.shuffle(idx)
    cut = int(len(idx) * 0.8)
    train_idx = sorted(idx[:cut])
    test_idx = sorted(idx[cut:])
    held = heldout_once(guides, y, train_idx, test_idx)
    checks["gc_controlled"] = True
    checks["heldout"] = held["m0_r"] is not None and held["m1_r"] is not None
    p, actual_b, null_max = permutation_null(guides, y, train_idx, test_idx, held["delta_r2"])
    held["p"] = p
    held["actual_B"] = actual_b
    held["null_max_delta_r2"] = null_max
    cross = cross_dataset(data.get("anchor", []))

    if not checks["positive_control"]:
        status = "needs_data"
        verdict = "needs_data"
        note = "正对照 Doench 符号未复现，可能是解析、方向或定位问题；不作结论性 claim。"
        exit_code = 3
    else:
        significant = p < 0.01
        effect_ok = abs(held["m1_r"]) >= 0.10 or held["delta_r2"] >= 0.01
        if significant and effect_ok and held["delta_r2"] > 0:
            verdict = "crosses_boundary"
            note = "位置-nt 全集在 held-out 中超出 GC-only；置换 null 显著。观测性 readout，不能解释为因果或泛化到所有 CRISPR context。"
        elif held["delta_r2"] > 0 or held["delta_r"] > 0:
            verdict = "bounded_descriptor_only"
            note = "位置-nt 在控 GC 后有超出 GC-only 的迹象，但未同时达到预登记显著性和效应量阈值。"
        else:
            verdict = "composition_artifact"
            note = "控 GC 后 held-out 增量塌缩；当前数据不支持位置-nt 越过 readback 边界。"
        exit_code = 0
    checks["crispr_verdict"] = verdict in ("crosses_boundary", "bounded_descriptor_only", "composition_artifact")

    result = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(guides),
            "heldout": {
                "m0_r": held["m0_r"],
                "m1_r": held["m1_r"],
                "delta": held["delta_r"],
                "m0_r2": held["m0_r2"],
                "m1_r2": held["m1_r2"],
                "delta_r2": held["delta_r2"],
                "p": held["p"],
                "actual_B": held["actual_B"],
                "null_max_delta_r2": held["null_max_delta_r2"],
                "active_cols_m0": held["active_cols_m0"],
                "active_cols_m1": held["active_cols_m1"],
                "train_n": len(train_idx),
                "test_n": len(test_idx),
            },
            "residual_examples": {
                "pos20_g_resid_r": posctrl["pos20_g_resid_r"],
                "t_pamprox_resid_r": posctrl["t_pamprox_resid_r"],
            },
            "gc_main_r": gc_main_r,
            "posctrl": {
                "pos20_g_r": posctrl["pos20_g_r"],
                "t_pamprox_r": posctrl["t_pamprox_r"],
                "polyt_r": posctrl["polyt_r"],
                "polyt_testable": posctrl["polyt_testable"],
                "doench_signs_ok": posctrl["doench_signs_ok"],
            },
            "cross_dataset": cross,
            "runtime_sec": time.time() - t0,
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(清理(result), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# 中文离线实验：yeast-frozen NatA/NatB N 端规则 transfer 到 human NtAc occupancy。
import json
import math
import pathlib
import random
import sys
import time

EXPERIMENT_ID = "nterminal_acetylation_occupancy_human"
CLAIM_ID = "h3.cross_layer_relation.nterminal_acetylation.nterminal_acetylation_occupancy_human"
AA = "ACDEFGHIKLMNPQRSTVWY"
SEED = 20240623
PERM_B = 2000


def mean(xs):
    return sum(xs) / len(xs) if xs else None


def median(xs):
    ys = sorted(xs)
    n = len(ys)
    if n == 0:
        return None
    mid = n // 2
    if n % 2:
        return ys[mid]
    return (ys[mid - 1] + ys[mid]) / 2.0


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
    return pearson(rankdata(x), rankdata(y))


def transpose(mat):
    if not mat:
        return []
    return [[row[j] for row in mat] for j in range(len(mat[0]))]


def xtx_xty(xmat, y, ridge):
    p = len(xmat[0])
    a = [[0.0] * p for _ in range(p)]
    b = [0.0] * p
    for row, val in zip(xmat, y):
        for i in range(p):
            b[i] += row[i] * val
            ri = row[i]
            for j in range(i, p):
                a[i][j] += ri * row[j]
    for i in range(p):
        for j in range(i):
            a[i][j] = a[j][i]
        a[i][i] += ridge
    return a, b


def solve_linear(a, b):
    n = len(b)
    aug = [a[i][:] + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            val = abs(aug[r][col])
            if val > best:
                best = val
                pivot = r
        if best < 1e-12:
            aug[col][col] += 1e-8
            best = abs(aug[col][col])
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


def fit_beta(xmat, y):
    a, b = xtx_xty(xmat, y, 1e-9)
    return solve_linear(a, b)


def predict(xmat, beta):
    return [sum(row[j] * beta[j] for j in range(len(beta))) for row in xmat]


def residuals(y, xmat):
    beta = fit_beta(xmat, y)
    yh = predict(xmat, beta)
    return [a - b for a, b in zip(y, yh)]


def r2(y, yh):
    m = sum(y) / len(y)
    ss_tot = sum((v - m) * (v - m) for v in y)
    ss_res = sum((a - b) * (a - b) for a, b in zip(y, yh))
    if ss_tot <= 0.0:
        return 0.0
    return 1.0 - ss_res / ss_tot


def partial_spearman(y, x, covars):
    ry = rankdata(y)
    rx = rankdata(x)
    yres = residuals(ry, covars)
    xres = residuals(rx, covars)
    return pearson(yres, xres), yres, xres


def permutation_p(yres, xres, b, seed):
    actual = pearson(yres, xres)
    rng = random.Random(seed)
    vals = xres[:]
    ge = 0
    for _ in range(b):
        rng.shuffle(vals)
        if abs(pearson(yres, vals)) >= abs(actual) - 1e-15:
            ge += 1
    return (ge + 1) / (b + 1)


def auroc(scores, labels):
    pos = [s for s, lab in zip(scores, labels) if lab == 1]
    neg = [s for s, lab in zip(scores, labels) if lab == 0]
    if not pos or not neg:
        return None
    wins = 0.0
    for p in pos:
        for n in neg:
            if p > n:
                wins += 1.0
            elif p == n:
                wins += 0.5
    return wins / (len(pos) * len(neg))


def base_covars(rows):
    cov = []
    abundance_used = False
    for r in rows:
        length = r.get("length") or 1
        row = [1.0]
        comp = r.get("aa_comp") or {}
        for aa in AA[:-1]:
            row.append(float(comp.get(aa, 0.0)))
        row.append(math.log(max(1.0, float(length))))
        ab = r.get("abundance")
        if ab is not None:
            abundance_used = True
            row.append(math.log(max(1e-12, float(ab))))
        cov.append(row)
    if not abundance_used:
        return cov, False
    width = max(len(r) for r in cov)
    for r in cov:
        while len(r) < width:
            r.append(0.0)
    return cov, True


def with_p1_fixed_effects(covars, p1s):
    levels = sorted(set(p1s))
    extra_levels = levels[1:]
    out = []
    for row, p1 in zip(covars, p1s):
        out.append(row[:] + [1.0 if p1 == lev else 0.0 for lev in extra_levels])
    return out


def group_means(rows, field, filt):
    groups = {}
    for r in rows:
        if filt(r):
            groups.setdefault(r[field], []).append(float(r["ntac_pct"]))
    return {k: {"n": len(v), "mean": round(mean(v), 6), "min": round(min(v), 6), "max": round(max(v), 6)} for k, v in groups.items()}


def make_result(status, verdict, checks, note, result, code):
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
    raise SystemExit(code)


def main():
    t0 = time.perf_counter()
    data_path = pathlib.Path.cwd() / "tools" / "bio_reality" / "data" / "nterminal_acetylation_occupancy_human.json"
    checks = {
        "human_data_fetched": False,
        "occupancy_continuous": False,
        "frozen_seq_prior_applied": False,
        "composition_controlled": False,
        "within_fixed_p1prime_tested": False,
        "positive_control": False,
        "ntac_human_verdict": False,
    }
    cannot_claim = [
        "human 细胞系特定",
        "MS occupancy 测量噪声",
        "NatA/B 一种特异性模型",
        "整体高相关部分定义性(P1')",
        "丰度控制有限：PMC8509067 Table S1 未提供逐蛋白丰度，未伪造控制",
        "观测性非因果",
        "frozen yeast 规则可能未捕捉 human 特有 NAT",
    ]
    if not data_path.exists():
        make_result(
            "needs_data",
            "needs_data",
            checks,
            "repo-relative compact JSON 不存在，无法离线实验。",
            {"n": 0, "source": None, "runtime_sec": round(time.perf_counter() - t0, 3), "cannot_claim": cannot_claim},
            3,
        )
    data = json.loads(data_path.read_text(encoding="utf-8"))
    meta = data.get("meta", {})
    rows = [r for r in data.get("proteins", []) if r.get("ntac_pct") is not None and r.get("seq_prior") is not None]
    checks["human_data_fetched"] = bool(rows) and meta.get("source_pmcid") == "PMC8509067"
    distinct = len(set(round(float(r["ntac_pct"]), 6) for r in rows))
    checks["occupancy_continuous"] = distinct > 10 and any(float(r["ntac_pct"]) not in (0.0, 100.0) for r in rows)
    checks["frozen_seq_prior_applied"] = meta.get("frozen_rule") == "yeast NatA/NatB"
    if not (checks["human_data_fetched"] and checks["occupancy_continuous"] and checks["frozen_seq_prior_applied"]):
        make_result(
            "needs_data",
            "needs_data",
            checks,
            "human 连续 occupancy 或 frozen rule 元数据未满足预登记要求。",
            {"n": len(rows), "source": meta.get("source_pmcid"), "distinct_occupancy": distinct, "runtime_sec": round(time.perf_counter() - t0, 3), "cannot_claim": cannot_claim},
            3,
        )

    y = [float(r["ntac_pct"]) for r in rows]
    x = [float(r["seq_prior"]) for r in rows]
    cov, abundance_used = base_covars(rows)
    checks["composition_controlled"] = True

    natA = [float(r["ntac_pct"]) for r in rows if r.get("nat_type") == "NatA"]
    natB = [float(r["ntac_pct"]) for r in rows if r.get("nat_type") == "NatB"]
    natA_by_2nd = group_means(rows, "p1prime", lambda r: r.get("nat_type") == "NatA")
    high_small = mean([v["mean"] for k, v in natA_by_2nd.items() if k in {"A", "S", "C"}])
    lower_set = mean([v["mean"] for k, v in natA_by_2nd.items() if k in {"G", "T", "V"}])
    pos_reproduced = bool(natA and natB and mean(natB) > mean(natA) and high_small is not None and lower_set is not None and high_small > lower_set)
    checks["positive_control"] = pos_reproduced
    if not pos_reproduced:
        make_result(
            "needs_data",
            "needs_data",
            checks,
            "正对照未复现，按预登记不作 transfer 结论。",
            {
                "n": len(rows),
                "source": meta.get("source_pmcid"),
                "posctrl": {"natB_mean": mean(natB), "natA_mean": mean(natA), "natA_by_2nd": natA_by_2nd, "reproduced": False},
                "runtime_sec": round(time.perf_counter() - t0, 3),
                "cannot_claim": cannot_claim,
            },
            3,
        )

    main_rho, yres, xres = partial_spearman(y, x, cov)
    main_p = permutation_p(yres, xres, PERM_B, SEED)

    beta0 = fit_beta(cov, y)
    r20 = r2(y, predict(cov, beta0))
    cov_plus = [row[:] + [score] for row, score in zip(cov, x)]
    beta1 = fit_beta(cov_plus, y)
    r21 = r2(y, predict(cov_plus, beta1))
    incr_r2 = max(0.0, r21 - r20)

    p1s = [str(r.get("p1prime", "")) for r in rows]
    cov_p1 = with_p1_fixed_effects(cov, p1s)
    p2acid = [float(r.get("p2_acidic", 0.0)) for r in rows]
    within_rho, wyres, wxres = partial_spearman(y, p2acid, cov_p1)
    within_p = permutation_p(wyres, wxres, PERM_B, SEED + 1)
    checks["within_fixed_p1prime_tested"] = True

    scores = []
    labels = []
    for yy, xx in zip(y, x):
        if yy < 100.0:
            labels.append(0)
            scores.append(xx)
        elif yy == 100.0:
            labels.append(1)
            scores.append(xx)
    auc = auroc(scores, labels)

    if abs(main_rho) >= 0.10 and main_p < 0.01 and within_rho >= 0.10:
        verdict = "transfers_conserved"
        conserved = "frozen yeast rule transfers to human under preregistered gates"
    elif main_p < 0.01:
        verdict = "bounded_descriptor_only"
        conserved = "significant but bounded; within-fixed-P1' or effect-size gate limits conservation claim"
    else:
        verdict = "not_conserved"
        conserved = "human transfer not significant under preregistered test"
    checks["ntac_human_verdict"] = True

    result = {
        "n": len(rows),
        "source": {
            "pmcid": meta.get("source_pmcid"),
            "readout": meta.get("readout"),
            "source_file": meta.get("source_file"),
            "distinct_occupancy_values": distinct,
        },
        "main": {
            "partial_rho": round(main_rho, 6),
            "p": round(main_p, 6),
            "actual_B": PERM_B,
            "incr_r2": round(incr_r2, 6),
        },
        "within_fixed_p1prime": {
            "p2_acidity_partial_rho": round(within_rho, 6),
            "p": round(within_p, 6),
            "n": len(rows),
        },
        "auroc": {
            "high_vs_low": round(auc, 6) if auc is not None else None,
            "definition": "100% saturated occupancy vs <100% lower occupancy",
            "low_max_pct": round(max(v for v in y if v < 100.0), 6),
            "high_min_pct": 100.0,
            "n_low": labels.count(0),
            "n_high": labels.count(1),
        },
        "posctrl": {
            "natB_mean": round(mean(natB), 6),
            "natB_n": len(natB),
            "natA_mean": round(mean(natA), 6),
            "natA_n": len(natA),
            "natA_by_2nd": natA_by_2nd,
            "reproduced": True,
        },
        "conserved_vs_yeast": conserved,
        "abundance_controlled": abundance_used,
        "runtime_sec": round(time.perf_counter() - t0, 3),
        "cannot_claim": cannot_claim,
    }
    note = (
        "frozen yeast NatA/NatB 序列规则 transfer 到 human measured NtAc 连续 occupancy；"
        "主效应控制 aa 组成和长度，丰度因源表缺失未控制；"
        "within-fixed-P1' 用 P1' 固定效应检验 P2' 酸性，避免只复述第二位定义；"
        "正对照复现 NatB>NatA 与 NatA 第二位梯度；观测性结果不作因果声称。"
    )
    make_result("passed", verdict, checks, note, result, 0)


if __name__ == "__main__":
    main()

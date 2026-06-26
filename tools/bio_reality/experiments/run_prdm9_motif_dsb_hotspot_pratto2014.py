#!/usr/bin/env python3
# 中文说明：纯 stdlib 离线实验。读 repo-relative compact JSON，检验 PRDM9-A motif 是否越过 readback 边界预测 DSB 强度。

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "prdm9_motif_dsb_hotspot_pratto2014"
CLAIM_ID = "h3.cross_layer_relation.meiotic_recombination.prdm9_motif_dsb_hotspot_pratto2014"
DATA_PATH = pathlib.Path.cwd() / "tools" / "bio_reality" / "data" / "prdm9_motif_dsb_hotspot_pratto2014.json"
SEED = 20260623
PERM_B = 1000


def finite(x):
    return isinstance(x, (int, float)) and math.isfinite(x)


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        r = (i + j - 1) / 2.0 + 1.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def pearson(x, y):
    n = len(x)
    if n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    sx = 0.0
    sy = 0.0
    sxy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        sx += da * da
        sy += db * db
        sxy += da * db
    den = math.sqrt(sx * sy)
    return sxy / den if den > 0 else float("nan")


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def solve_linear(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            return [0.0] * n
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pv = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= pv
        for r in range(n):
            if r == col:
                continue
            f = aug[r][col]
            if f == 0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= f * aug[col][j]
    return [aug[i][n] for i in range(n)]


def ols_residuals(y, covars):
    xmat = [[1.0] + list(row) for row in covars]
    p = len(xmat[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yy in zip(xmat, y):
        for i in range(p):
            xty[i] += row[i] * yy
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    # 很小 ridge 只为数值稳定，不改变检验定义。
    for i in range(1, p):
        xtx[i][i] += 1e-10
    beta = solve_linear(xtx, xty)
    return [yy - sum(beta[j] * row[j] for j in range(p)) for yy, row in zip(y, xmat)]


def partial_spearman(x, y, covars):
    rx = ranks(x)
    ry = ranks(y)
    rc = [ranks(col) for col in transpose(covars)] if covars else []
    rc_rows = [list(row) for row in zip(*rc)] if rc else [[] for _ in x]
    ex = ols_residuals(rx, rc_rows)
    ey = ols_residuals(ry, rc_rows)
    return pearson(ex, ey), ex, ey


def permutation_p_from_residuals(ex, ey, b, seed):
    actual = pearson(ex, ey)
    rng = random.Random(seed)
    vals = ey[:]
    ge = 0
    null_abs = []
    target = abs(actual)
    for _ in range(b):
        rng.shuffle(vals)
        r = pearson(ex, vals)
        ar = abs(r)
        null_abs.append(ar)
        if ar >= target - 1e-15:
            ge += 1
    null_abs = sorted(null_abs)
    idx = max(0, min(len(null_abs) - 1, int(math.ceil(0.95 * len(null_abs))) - 1))
    return (ge + 1) / (b + 1), null_abs[idx], actual


def permutation_p_one_sided_positive(x, y, b, seed):
    rx = ranks(x)
    ry = ranks(y)
    actual = pearson(rx, ry)
    rng = random.Random(seed)
    vals = ry[:]
    ge = 0
    null_abs = []
    for _ in range(b):
        rng.shuffle(vals)
        r = pearson(rx, vals)
        null_abs.append(abs(r))
        if r >= actual - 1e-15:
            ge += 1
    null_abs = sorted(null_abs)
    idx = max(0, min(len(null_abs) - 1, int(math.ceil(0.95 * len(null_abs))) - 1))
    return (ge + 1) / (b + 1), null_abs[idx], actual


def clean_rows(hotspots):
    rows = []
    for h in hotspots:
        vals = [h.get(k) for k in ("aa_strength", "ac_strength", "a_pwm", "c_pwm", "gc", "cpg_oe")]
        if all(finite(v) for v in vals):
            aa = float(h["aa_strength"])
            ac = float(h["ac_strength"])
            if aa > 0 and ac > 0:
                rows.append(
                    {
                        "chrom": h.get("chrom", ""),
                        "center": int(h.get("center", 0)),
                        "aa": math.log1p(aa),
                        "ac": math.log1p(ac),
                        "aa_raw": aa,
                        "ac_raw": ac,
                        "a": float(h["a_pwm"]),
                        "c": float(h["c_pwm"]),
                        "a_flank": float(h["a_flank_pwm"]) if finite(h.get("a_flank_pwm")) else None,
                        "gc": float(h["gc"]),
                        "cpg": float(h["cpg_oe"]),
                    }
                )
    return rows


def flank_proxy_score(rows):
    pairs = [(r["a"], r["a_flank"]) for r in rows if finite(r.get("a_flank"))]
    if not pairs:
        return float("nan")
    return mean([a - f for a, f in pairs])


def gc_strata(rows):
    ordered = sorted(rows, key=lambda r: r["gc"])
    if len(ordered) < 30:
        return []
    out = []
    for label, chunk in (
        ("low_gc", ordered[: len(ordered) // 3]),
        ("mid_gc", ordered[len(ordered) // 3 : 2 * len(ordered) // 3]),
        ("high_gc", ordered[2 * len(ordered) // 3 :]),
    ):
        rho = spearman([r["a"] for r in chunk], [r["aa"] for r in chunk])
        out.append({"stratum": label, "n": len(chunk), "a_pwm_aa_rho": round(rho, 6)})
    return out


def rnd(x, nd=6):
    if not finite(x):
        return None
    return round(x, nd)


def main():
    t0 = time.time()
    checks = {
        "peaks_parsed": False,
        "pwm_loaded": False,
        "hg19_sequences": False,
        "pwm_scored": False,
        "composition_controlled": False,
        "allele_specific_test": False,
        "positive_control": False,
        "recombination_verdict": False,
    }
    cannot_claim = [
        "hg19 特定",
        "DMC1 SSDS 测量噪声/PRDM9 基因型样本特定",
        "PWM 是序列模型近似(无 chromatin/PRDM9 表达 context)",
        "±250bp 窗",
        "观测性非因果(PRDM9 结合机制已知但本测是序列-DSB 关联)",
        "A/C PWM 质量限",
    ]
    if not DATA_PATH.exists():
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "bounded_descriptor_only",
            "note": "找不到 compact JSON: " + str(DATA_PATH),
            "result": {"n_hotspots": 0, "cannot_claim": cannot_claim},
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3
    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    meta = payload.get("meta", {})
    rows = clean_rows(payload.get("hotspots", []))
    n = len(rows)
    checks["peaks_parsed"] = n > 1000
    checks["pwm_loaded"] = bool(meta.get("pwm_source"))
    checks["hg19_sequences"] = n > 1000 and meta.get("build") == "hg19"
    checks["pwm_scored"] = n > 1000 and len({r["a"] for r in rows[: min(n, 1000)]}) > 1
    if n < 1000:
        status = "needs_data"
        verdict = "bounded_descriptor_only"
        note = "有效热点不足，不能做结论性检验。"
        out = {
            "status": status,
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": verdict,
            "note": note,
            "result": {"n_hotspots": n, "cannot_claim": cannot_claim, "runtime_sec": rnd(time.time() - t0, 3)},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    a = [r["a"] for r in rows]
    c = [r["c"] for r in rows]
    aa = [r["aa"] for r in rows]
    ac = [r["ac"] for r in rows]
    gc = [r["gc"] for r in rows]
    cpg = [r["cpg"] for r in rows]
    win_len = [500.0 for _ in rows]
    cov = list(zip(gc, cpg, win_len))

    a_aa_corr = spearman(a, aa)
    center_vs_proxy = flank_proxy_score(rows)
    checks["positive_control"] = a_aa_corr > 0 and center_vs_proxy > 0

    main_rho, ex_a, ey_aa = partial_spearman(a, aa, cov)
    main_p, null95, _ = permutation_p_from_residuals(ex_a, ey_aa, PERM_B, SEED + 1)
    checks["composition_controlled"] = finite(main_rho)

    delta_pwm = [r["a"] - r["c"] for r in rows]
    delta_strength = [r["aa"] - r["ac"] for r in rows]
    delta_p, delta_null95, delta_rho = permutation_p_one_sided_positive(delta_pwm, delta_strength, PERM_B, SEED + 2)
    checks["allele_specific_test"] = finite(delta_rho)

    c_rho, ex_c, ey_aa_c = partial_spearman(c, aa, cov)
    c_p, c_null95, _ = permutation_p_from_residuals(ex_c, ey_aa_c, PERM_B, SEED + 3)
    # C 不冒充：按预登记，若 C_pwm 也以强效应预测 AA 残差，则标记为非特异/成分嫌疑。
    c_predicts_aa_specific = bool(c_rho > 0 and abs(c_rho) >= 0.10 and c_p < 0.01)
    a_c_gap = main_rho - c_rho
    a_c_ratio = main_rho / c_rho if c_rho > 0 else None
    a_more_than_c = bool(main_rho > 0 and a_c_gap >= 0.05 and (c_rho < 0.10 or main_rho >= 1.5 * max(c_rho, 1e-12)))

    crosses = (
        checks["positive_control"]
        and main_p < 0.01
        and abs(main_rho) >= 0.10
        and delta_rho > 0
        and delta_p < 0.01
        and not c_predicts_aa_specific
        and a_more_than_c
    )
    if crosses:
        verdict = "crosses_boundary"
    elif main_p >= 0.01 or c_predicts_aa_specific or not a_more_than_c:
        verdict = "composition_artifact"
    else:
        verdict = "bounded_descriptor_only"
    status = "passed" if checks["positive_control"] and checks["composition_controlled"] and checks["allele_specific_test"] else "needs_data"
    checks["recombination_verdict"] = status == "passed"
    note = (
        "PRDM9-A PWM 是外部/冻结序列先验，AA/AC_strength 是 DMC1 SSDS readout；"
        f"控 GC/CpG 后 A_pwm-AA partial rho={main_rho:.4f}, p={main_p:.4g}; "
        f"等位基因特异 delta(A-C→AA-AC) rho={delta_rho:.4f}, p={delta_p:.4g}; "
        f"C_pwm-AA partial rho={c_rho:.4f}, p={c_p:.4g}; verdict={verdict}。"
    )
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n_hotspots": n,
            "main": {"a_pwm_aa_partial_rho": rnd(main_rho), "p": rnd(main_p, 6)},
            "allele_specific": {"delta_rho": rnd(delta_rho), "p": rnd(delta_p, 6)},
            "falsification": {
                "c_pwm_aa_partial_rho": rnd(c_rho),
                "p": rnd(c_p, 6),
                "c_predicts_aa_specific": c_predicts_aa_specific,
                "a_minus_c_partial_rho_gap": rnd(a_c_gap),
                "a_over_c_partial_rho_ratio": rnd(a_c_ratio),
                "a_more_predictive_than_c": a_more_than_c,
            },
            "perm_null": {"null95": rnd(null95), "actual_B": PERM_B, "delta_null95": rnd(delta_null95), "c_null95": rnd(c_null95)},
            "posctrl": {"a_pwm_center_vs_flank": rnd(center_vs_proxy), "a_pwm_aa_corr": rnd(a_aa_corr)},
            "gc_strata": gc_strata(rows),
            "runtime_sec": rnd(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
            "meta": {
                "build": meta.get("build"),
                "pwm_source": meta.get("pwm_source"),
                "leakage_guard": meta.get("leakage_guard"),
            },
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    sys.exit(main())

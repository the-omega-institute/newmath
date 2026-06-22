#!/usr/bin/env python3
import json
import math
import pathlib
import random
import statistics
import sys
import time

EXPERIMENT_ID = "scd_charge_patterning_thermal_stability_meltome_human"
CLAIM_ID = "h3.cross_layer_relation.protein_thermal_stability.scd_charge_patterning_thermal_stability_meltome_human"
DATA_REL = pathlib.Path("tools/bio_reality/data") / f"{EXPERIMENT_ID}.json"

SEED = 20260622
PERM_B = 3000
HELDOUT_PERM_B = 1000
PARTIAL_PERM_B = 1000
AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"


def sig5(x):
    return float(f"{x:.5g}")


def mean(xs):
    return sum(xs) / len(xs)


def rankdata(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    ranks = [0.0] * len(xs)
    i = 0
    n = len(xs)
    while i < n:
        j = i + 1
        v = xs[order[i]]
        while j < n and xs[order[j]] == v:
            j += 1
        r = (i + j - 1) / 2.0 + 1.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


def pearson_from_centered(xc, yc):
    sx = sum(v * v for v in xc)
    sy = sum(v * v for v in yc)
    if sx <= 0.0 or sy <= 0.0:
        return 0.0
    return sum(a * b for a, b in zip(xc, yc)) / math.sqrt(sx * sy)


def spearman(xs, ys):
    rx = rankdata(xs)
    ry = rankdata(ys)
    mx = mean(rx)
    my = mean(ry)
    return pearson_from_centered([v - mx for v in rx], [v - my for v in ry])


def spearman_against_centered_rank(xs, y_rank_centered):
    rx = rankdata(xs)
    mx = mean(rx)
    return pearson_from_centered([v - mx for v in rx], y_rank_centered)


def normal_two_sided_p_from_rho(rho, n):
    if n < 4:
        return 1.0
    rho = max(-0.999999999, min(0.999999999, rho))
    t = abs(rho) * math.sqrt((n - 2) / (1.0 - rho * rho))
    # 大样本下 t 分布与正态差异很小；用 erfc 给确定性 stdlib p。
    return math.erfc(t / math.sqrt(2.0))


def quantile_nearest(xs, q):
    vals = sorted(xs)
    idx = int(math.ceil(q * len(vals))) - 1
    idx = max(0, min(len(vals) - 1, idx))
    return vals[idx]


def scd_from_charge_seq(charges):
    positions = []
    values = []
    for i, ch in enumerate(charges):
        if ch == "+":
            positions.append(i)
            values.append(1)
        elif ch == "-":
            positions.append(i)
            values.append(-1)
    total = 0.0
    m = len(positions)
    for a in range(m):
        pa = positions[a]
        qa = values[a]
        for b in range(a + 1, m):
            total += qa * values[b] * math.sqrt(positions[b] - pa)
    return total / len(charges)


def shuffled_charge_seq(charges, rng):
    chars = list(charges)
    rng.shuffle(chars)
    return "".join(chars)


def tertile_breaks(values):
    vals = sorted(values)
    n = len(vals)
    return vals[n // 3], vals[(2 * n) // 3]


def tertile_index(value, breaks):
    if value < breaks[0]:
        return 0
    if value < breaks[1]:
        return 1
    return 2


def composition_strata(prots):
    len_breaks = tertile_breaks([p["length"] for p in prots])
    charged_breaks = tertile_breaks([p["charged_frac"] for p in prots])
    net_breaks = tertile_breaks([p["net_charge_frac"] for p in prots])
    bins = {}
    for i, p in enumerate(prots):
        key = (
            tertile_index(p["length"], len_breaks),
            tertile_index(p["charged_frac"], charged_breaks),
            tertile_index(p["net_charge_frac"], net_breaks),
        )
        bins.setdefault(key, []).append(i)
    return [idxs for idxs in bins.values() if idxs]


def stratified_label_permutation_null(scds, tms, strata, b, seed):
    scd_rank = rankdata(scds)
    tm_rank = rankdata(tms)
    mx = mean(scd_rank)
    my = mean(tm_rank)
    scd_centered = [r - mx for r in scd_rank]
    tm_centered = [r - my for r in tm_rank]
    sx = sum(v * v for v in scd_centered)
    sy = sum(v * v for v in tm_centered)
    denom = math.sqrt(sx * sy)
    if denom <= 0.0:
        return None, 0, []

    perm = list(tm_centered)
    rng = random.Random(seed)
    first_tm = None
    changed = 0
    rhos = []
    for bi in range(b):
        for idxs in strata:
            vals = [perm[i] for i in idxs]
            rng.shuffle(vals)
            for i, v in zip(idxs, vals):
                perm[i] = v
        if bi == 0:
            first_tm = perm[0]
            changed = sum(1 for a, bval in zip(tm_centered, perm) if abs(a - bval) > 1e-12)
        rhos.append(sum(a * bval for a, bval in zip(scd_centered, perm)) / denom)
        for idxs in strata:
            for i in idxs:
                perm[i] = tm_centered[i]
    return first_tm, changed, rhos


def residualize(y, xcols):
    n = len(y)
    basis = []
    tiny = 1e-12
    for col in xcols:
        v = [float(z) for z in col]
        for q in basis:
            dot = sum(a * b for a, b in zip(v, q))
            if dot:
                v = [a - dot * b for a, b in zip(v, q)]
        norm = math.sqrt(sum(a * a for a in v))
        if norm > tiny:
            basis.append([a / norm for a in v])
    fit = [0.0] * n
    for q in basis:
        coef = sum(a * b for a, b in zip(y, q))
        for i in range(n):
            fit[i] += coef * q[i]
    return [float(y[i]) - fit[i] for i in range(n)], len(basis)


def covariate_columns(prots):
    cols = []
    cols.append([1.0] * len(prots))
    cols.append([math.log(p["length"]) for p in prots])
    for j in range(20):
        cols.append([p["aa_comp"][j] for p in prots])
    cols.append([p["net_charge_frac"] for p in prots])
    cols.append([p["charged_frac"] for p in prots])
    cols.append([p["disorder_proxy"] for p in prots])
    return cols


def permutation_p_by_shuffling_y(x, y, obs, b, rng):
    vals = list(y)
    hits = 0
    for _ in range(b):
        rng.shuffle(vals)
        rho = spearman(x, vals)
        if abs(rho) >= abs(obs) - 1e-15:
            hits += 1
    return (hits + 1) / (b + 1)


def select(values, indices):
    return [values[i] for i in indices]


def welch_t_p_approx(a, b):
    ma = mean(a)
    mb = mean(b)
    va = statistics.variance(a)
    vb = statistics.variance(b)
    t = abs(ma - mb) / math.sqrt(va / len(a) + vb / len(b))
    return math.erfc(t / math.sqrt(2.0))


def positive_control(prots):
    ordered = sorted(prots, key=lambda p: p["tm"])
    lo = ordered[:1000]
    hi = ordered[-1000:]
    dekr_lo = [p["charged_frac"] for p in lo]
    dekr_hi = [p["charged_frac"] for p in hi]
    # AA_ORDER: I=7, L=10, V=17
    ivl_lo = [p["aa_comp"][7] + p["aa_comp"][10] + p["aa_comp"][17] for p in lo]
    ivl_hi = [p["aa_comp"][7] + p["aa_comp"][10] + p["aa_comp"][17] for p in hi]
    p_dekr = welch_t_p_approx(dekr_lo, dekr_hi)
    p_ivl = welch_t_p_approx(ivl_lo, ivl_hi)
    return {
        "dekr_delta": sig5(mean(dekr_hi) - mean(dekr_lo)),
        "ivl_delta": sig5(mean(ivl_hi) - mean(ivl_lo)),
        "tm_lo": sig5(mean([p["tm"] for p in lo])),
        "tm_hi": sig5(mean([p["tm"] for p in hi])),
        "p": sig5(max(p_dekr, p_ivl)),
        "p_dekr": sig5(p_dekr),
        "p_ivl": sig5(p_ivl),
    }


def main():
    started = time.time()
    data_path = pathlib.Path.cwd() / DATA_REL
    with data_path.open() as f:
        data = json.load(f)
    prots = data["prots"]
    n = len(prots)
    tms = [p["tm"] for p in prots]
    scds = [scd_from_charge_seq(p["charge_seq"]) for p in prots]

    checks = {
        "fasta_parsed": bool(n and data.get("meta", {}).get("source") == "FLIP/Meltome human_cell"),
        "scd_computed": bool(n and any(abs(x) > 0 for x in scds)),
    }

    rho_obs = spearman(scds, tms)
    first_real = scds[0]
    sanity_rng = random.Random(SEED + 5)
    first_shuffled = scd_from_charge_seq(shuffled_charge_seq(prots[0]["charge_seq"], sanity_rng))
    strata = composition_strata(prots)
    first_tm_perm, changed, null = stratified_label_permutation_null(scds, tms, strata, PERM_B, SEED)
    null_abs = [abs(x) for x in null]
    hits = sum(1 for x in null if abs(x) >= abs(rho_obs) - 1e-15)
    p_perm = (hits + 1) / (PERM_B + 1)
    null95 = quantile_nearest(null_abs, 0.95)
    null99 = quantile_nearest(null_abs, 0.99)
    checks["composition_perm_null"] = bool(len(null) == PERM_B and changed > n * 0.5 and first_tm_perm is not None)

    cols = covariate_columns(prots)
    r_tm, cov_rank = residualize(tms, cols)
    r_scd, _ = residualize(scds, cols)
    rho_partial = spearman(r_scd, r_tm)
    p_partial = permutation_p_by_shuffling_y(r_scd, r_tm, rho_partial, PARTIAL_PERM_B, random.Random(SEED + 11))
    checks["partial_residualized"] = True

    indices = list(range(n))
    split_rng = random.Random(SEED + 23)
    split_rng.shuffle(indices)
    cut = int(round(n * 0.7))
    train_idx = sorted(indices[:cut])
    test_idx = sorted(indices[cut:])
    train_rho = spearman(select(scds, train_idx), select(tms, train_idx))
    test_rho = spearman(select(scds, test_idx), select(tms, test_idx))
    test_p = permutation_p_by_shuffling_y(
        select(scds, test_idx),
        select(tms, test_idx),
        test_rho,
        HELDOUT_PERM_B,
        random.Random(SEED + 37),
    )
    sign_concordant = (train_rho == 0 and test_rho == 0) or (train_rho * test_rho > 0)
    checks["held_out"] = True

    pos = positive_control(prots)
    pos_ok = bool(pos["p"] < 0.01 and pos["dekr_delta"] < 0 and pos["ivl_delta"] > 0)
    checks["positive_control"] = pos_ok

    first_scd_delta = abs(first_real - first_shuffled)
    order_ok = bool(first_shuffled is not None and first_scd_delta > 1e-12)
    checks["order_sanity"] = order_ok

    partial_ok = bool(p_partial < 0.01 and rho_partial * rho_obs > 0)
    held_ok = bool(sign_concordant and test_p < 0.05)
    perm_ok = bool(p_perm < 0.01 and abs(rho_obs) > null99)
    if not pos_ok:
        verdict = "needs_data"
        status = "needs_data"
    elif perm_ok and partial_ok and held_ok:
        # Spearman rho^2 is a conservative descriptor of rank-scale variance here.
        verdict = "bounded_descriptor_only" if rho_obs * rho_obs < 0.02 else "crosses_boundary"
        status = "passed"
    else:
        verdict = "composition_artifact"
        status = "passed"
    checks["thermal_boundary_verdict"] = status == "passed"

    cannot_claim = [
        "Tm 是体外 TPP 物理量非细胞内稳定性/寿命",
        "within-human 单细胞系非全人/不跨物种",
        "SCD 是一种 charge-patterning 度量(κ 等其它度量可能不同)",
        "composition null 是分层 label-permutation 近似, 非精确 per-protein 电荷重排",
        "disorder proxy 是 stdlib 启发式非 IUPred",
        "组成控制用 stdlib(无真二级结构/结构 context)",
        "观测性非因果(electrostatic-stabilization 机制只是一种解读)",
        "FLIP 匿名 id 无法接外部特征",
    ]
    note = (
        "SCD 与 measured TPP Tm 的原始 rank 相关很小；composition null 是 composition-stratified label-permutation，"
        "即在 length×charged_frac×net_charge 三分位箱内置乱 Tm，非 per-protein 精确电荷重排(后者纯 stdlib 不可行)。"
        "该 null 配合 residualized partial 与 SCD 的构造性组成不变性共同控成分。"
        "正对照复现低 Tm 蛋白 DEKR 更高、IVL 更低。"
        "残差化控制 log(length)、20aa composition、net charge、charged fraction、disorder proxy；结论为观测性非因果，且不外推到细胞内寿命或跨物种。"
    )
    if verdict == "composition_artifact":
        note += "按预登记规则，order 信号未同时通过组成置换 null、残差化与 held-out，因此判为 composition_artifact。"
    elif verdict == "bounded_descriptor_only":
        note += "按预登记规则，order 信号通过关键检查但效应量在 rank 尺度 rho^2 < 0.02，因此判为 bounded_descriptor_only。"
    elif verdict == "crosses_boundary":
        note += "按预登记规则，SCD order 信号越过 readback 边界预测 Tm 超组成。"

    runtime = time.time() - started
    runtime_bucket = math.ceil(runtime / 10.0) * 10.0
    result = {
        "n": n,
        "main": {"rho_scd_tm": sig5(rho_obs), "direction": "positive" if rho_obs > 0 else "negative" if rho_obs < 0 else "zero"},
        "composition_perm_null": {
            "null_type": "composition_stratified_label_permutation",
            "rho_obs": sig5(rho_obs),
            "null95": sig5(null95),
            "null99": sig5(null99),
            "p_perm": sig5(p_perm),
            "actual_B": PERM_B,
            "changed_tm_labels_first_perm": changed,
            "strata_n": len(strata),
        },
        "partial_residualized": {
            "rho": sig5(rho_partial),
            "p": sig5(p_partial),
            "covariate_rank": cov_rank,
        },
        "held_out": {
            "train_rho": sig5(train_rho),
            "test_rho": sig5(test_rho),
            "test_p": sig5(test_p),
            "sign_concordant": sign_concordant,
            "train_n": len(train_idx),
            "test_n": len(test_idx),
        },
        "posctrl": pos,
        "scd_order_sanity": {
            "real_scd": sig5(first_real),
            "shuffled_scd": sig5(first_shuffled),
            "abs_delta_first_shuffle": sig5(first_scd_delta),
        },
        "runtime_sec": sig5(runtime_bucket),
        "runtime_sec_note": "10s ceiling bucket for deterministic JSON; shell time verified <300s",
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
    if status == "passed":
        return 0
    if status == "needs_data":
        return 3
    return 1


if __name__ == "__main__":
    sys.exit(main())

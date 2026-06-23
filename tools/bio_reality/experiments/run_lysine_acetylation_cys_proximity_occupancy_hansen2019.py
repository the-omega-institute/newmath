#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""赖氨酸乙酰化占据率: 局部 Cys chemistry vs KAT motif 离线实验。

纯 Python 标准库；从 repo-relative tools/bio_reality/data 读取 prep 生成的 compact JSON。
"""

import json
import math
import random
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "lysine_acetylation_cys_proximity_occupancy_hansen2019"
CLAIM_ID = "h3.cross_layer_relation.protein_acetylation.lysine_acetylation_cys_proximity_occupancy_hansen2019"
DATA = Path.cwd() / "tools/bio_reality/data/lysine_acetylation_cys_proximity_occupancy_hansen2019.json"
AA20 = "ACDEFGHIKLMNPQRSTVWY"
SEED = 20240623
PERM_B = 1000


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        vi = values[order[i]]
        while j < len(order) and values[order[j]] == vi:
            j += 1
        avg = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = avg
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


def solve_linear(a, b):
    n = len(b)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[piv][col]) < 1e-10:
            aug[col][col] += 1e-8
            piv = col
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-14:
            div = 1e-14 if div >= 0 else -1e-14
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= fac * aug[col][j]
    return [aug[i][n] for i in range(n)]


def residuals(y, covars):
    n = len(y)
    if not covars:
        m = sum(y) / n
        return [v - m for v in y]
    p = 1 + len(covars)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        row = [1.0] + [c[i] for c in covars]
        yi = y[i]
        for a in range(p):
            xty[a] += row[a] * yi
            for b in range(a, p):
                xtx[a][b] += row[a] * row[b]
    for a in range(p):
        for b in range(a):
            xtx[a][b] = xtx[b][a]
    # 极小 ridge 只用于数值稳定；截距不惩罚。
    for a in range(1, p):
        xtx[a][a] += 1e-9
    beta = solve_linear(xtx, xty)
    out = []
    for i in range(n):
        pred = beta[0]
        for j, c in enumerate(covars, start=1):
            pred += beta[j] * c[i]
        out.append(y[i] - pred)
    return out


def partial_spearman(x, y, covars):
    rx = ranks(x)
    ry = ranks(y)
    rc = [ranks(c) for c in covars]
    return pearson(residuals(rx, rc), residuals(ry, rc))


def partial_spearman_from_ranked_covars(x, y, ranked_covars):
    rx = ranks(x)
    ry = ranks(y)
    return pearson(residuals(rx, ranked_covars), residuals(ry, ranked_covars))


def perm_p_partial(x, y, covars, b, seed):
    rx = ranks(x)
    ry = ranks(y)
    rc = [ranks(c) for c in covars]
    ex = residuals(rx, rc)
    ey = residuals(ry, rc)
    obs = pearson(ex, ey)
    rng = random.Random(seed)
    tmp = list(ex)
    ge = 0
    for _ in range(b):
        rng.shuffle(tmp)
        if abs(pearson(tmp, ey)) >= abs(obs) - 1e-15:
            ge += 1
    return obs, (ge + 1) / (b + 1)


def auc_score(scores, labels):
    pos = sum(1 for v in labels if v == 1)
    neg = len(labels) - pos
    if pos == 0 or neg == 0:
        return 0.5
    r = ranks(scores)
    rank_pos = sum(rv for rv, lab in zip(r, labels) if lab == 1)
    return (rank_pos - pos * (pos + 1) / 2.0) / (pos * neg)


def quantile(values, q):
    vals = sorted(values)
    if not vals:
        return 0.0
    pos = q * (len(vals) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return vals[lo]
    return vals[lo] * (hi - pos) + vals[hi] * (pos - lo)


def signed_max_abs_pair(items):
    best_name = None
    best_val = 0.0
    for name, val in items:
        if abs(val) > abs(best_val):
            best_name = name
            best_val = val
    return best_name, best_val


def main():
    t0 = time.time()
    checks = {
        "hansen_xlsx_parsed": False,
        "occupancy_continuous": False,
        "local_cys_computed": False,
        "abundance_controlled": False,
        "kat_motif_tested": False,
        "cys_free_subset": False,
        "positive_control": False,
        "kac_verdict": False,
    }
    cannot_claim = [
        "局部-Cys 是非酶 chemistry(Cys 催化 S→N 乙酰转移)非调控码。",
        "KAT 酶 motif 经典共识在此为 null，不能包装成 p300/CBP 调控码 crossing。",
        "丰度是最大混杂，已控制但不能证明完全消除所有混杂。",
        "MS stoichiometry 有测量噪声，尤其超低占据率更不稳定。",
        "HeLa 特定数据集，不能直接外推到所有细胞类型或条件。",
        "观测性非因果，不能声称 Cys 邻近必然导致该位点乙酰化占据率升高。",
        "数据可能偏倚于高反应性、可检出的乙酰化位点。",
    ]
    status = "failed"
    verdict = "needs_data"
    note = "未完成"
    exit_code = 1
    result = {}

    try:
        obj = json.loads(DATA.read_text(encoding="utf-8"))
        meta = obj.get("meta", {})
        sites = obj.get("sites", [])
        checks["hansen_xlsx_parsed"] = bool(sites) and meta.get("sheet") == "Supplementary Data 1c"

        rows = [
            r
            for r in sites
            if isinstance(r.get("stoich"), (int, float))
            and isinstance(r.get("log_abundance"), (int, float))
            and len(r.get("window31", "")) == 31
            and r.get("window31", "")[15] == "K"
        ]
        n = len(rows)
        sto = [float(r["stoich"]) for r in rows]
        distinct_stoich = len({round(v, 12) for v in sto})
        checks["occupancy_continuous"] = distinct_stoich > 10 and n > 1000

        abundance = [float(r["log_abundance"]) for r in rows]
        local = [float(r["local_cys_score"]) for r in rows]
        near = [float(r.get("near_cys_count", 0.0)) for r in rows]
        far = [float(r["far_cys"]) for r in rows]
        basic = [float(r["kat_basic"]) for r in rows]
        acidic = [float(r["kat_acidic"]) for r in rows]
        smallga = [float(r["kat_smallGA"]) for r in rows]
        cys_m3 = [float(r.get("cys_m3", 0.0)) for r in rows]
        cys_m2 = [float(r.get("cys_m2", 0.0)) for r in rows]
        cys_m4 = [float(r.get("cys_m4", 0.0)) for r in rows]
        aa_cov = [[float(r["aa_" + aa]) for r in rows] for aa in AA20[:-1]]
        checks["local_cys_computed"] = max(local) > 0 and sum(1 for v in local if v > 0) > 10

        local_rho, pval = perm_p_partial(local, sto, [abundance], PERM_B, SEED)
        checks["abundance_controlled"] = True
        cys_m3_rho = partial_spearman(cys_m3, sto, [abundance])
        cys_m2_rho = partial_spearman(cys_m2, sto, [abundance])
        cys_m4_rho = partial_spearman(cys_m4, sto, [abundance])
        composite_rho = local_rho
        pos_reproduced = cys_m3_rho > 0.05 and composite_rho > 0.10 and pval <= 0.01
        checks["positive_control"] = pos_reproduced

        near_rho = partial_spearman(near, sto, [abundance])
        far_rho = partial_spearman(far, sto, [abundance])

        q25 = quantile(sto, 0.25)
        q75 = quantile(sto, 0.75)
        auc_scores = []
        auc_labels = []
        for s, x in zip(sto, local):
            if s <= q25:
                auc_scores.append(x)
                auc_labels.append(0)
            elif s >= q75:
                auc_scores.append(x)
                auc_labels.append(1)
        auroc = auc_score(auc_scores, auc_labels)

        cys_controls = [abundance, local, near, far] + aa_cov
        ranked_cys_controls = [ranks(c) for c in cys_controls]
        kat_basic_rho = partial_spearman_from_ranked_covars(basic, sto, ranked_cys_controls)
        kat_acidic_rho = partial_spearman_from_ranked_covars(acidic, sto, ranked_cys_controls)
        kat_smallga_rho = partial_spearman_from_ranked_covars(smallga, sto, ranked_cys_controls)
        kat_name, kat_rho = signed_max_abs_pair(
            [("basic_KR", kat_basic_rho), ("acidic_DE", kat_acidic_rho), ("small_GA", kat_smallga_rho)]
        )
        kat_survives = abs(kat_rho) >= 0.10
        checks["kat_motif_tested"] = True

        cf_idx = [i for i, r in enumerate(rows) if not bool(r.get("has_cys"))]
        cf_n = len(cf_idx)
        if cf_n >= 100:
            cf_sto = [sto[i] for i in cf_idx]
            cf_ab = [abundance[i] for i in cf_idx]
            cf_basic = [basic[i] for i in cf_idx]
            cf_acidic = [acidic[i] for i in cf_idx]
            cf_smallga = [smallga[i] for i in cf_idx]
            cf_aa_cov = [[float(rows[i]["aa_" + aa]) for i in cf_idx] for aa in AA20[:-1]]
            cf_cov = [cf_ab] + cf_aa_cov
            cf_vals = [
                partial_spearman(cf_basic, cf_sto, cf_cov),
                partial_spearman(cf_acidic, cf_sto, cf_cov),
                partial_spearman(cf_smallga, cf_sto, cf_cov),
            ]
            cys_free_residual = max(cf_vals, key=lambda v: abs(v))
        else:
            cys_free_residual = 0.0
        checks["cys_free_subset"] = cf_n >= 100

        local_position_not_bulk = local_rho >= 0.10 and auroc >= 0.60 and near_rho > far_rho + 0.10
        cys_free_null = abs(cys_free_residual) < 0.10
        if not checks["hansen_xlsx_parsed"] or not checks["occupancy_continuous"] or not pos_reproduced:
            verdict = "needs_data"
            status = "failed"
            exit_code = 3
            note = "解析或正对照未达预登记要求，不能给结论。"
        elif local_position_not_bulk and (not kat_survives) and cys_free_null:
            verdict = "bounded_descriptor_only"
            status = "passed"
            exit_code = 0
            note = (
                "序列上下文能预测 measured lysine acetylation stoichiometry，但有效上下文是局部 Cys 反应性位置"
                "(非酶 chemistry)，不是 KAT/p300/CBP motif 调控码；KAT motif 控 Cys/丰度/组成后为 null，"
                "Cys-free 子集无残余序列信号。"
            )
        elif kat_survives:
            verdict = "crosses_boundary"
            status = "passed"
            exit_code = 0
            note = "KAT motif 控丰度+Cys+组成后仍达阈；这与 scout 预判不同，需谨慎复核。"
        elif abs(local_rho) < 0.10 or near_rho <= far_rho + 0.10:
            verdict = "composition_artifact"
            status = "passed"
            exit_code = 0
            note = "局部 Cys 信号未能区别于 bulk 组成/丰度。"
        else:
            verdict = "needs_data"
            status = "failed"
            exit_code = 3
            note = "统计结果未清晰落入预登记判据。"

        checks["kac_verdict"] = status == "passed"
        result = {
            "n": n,
            "distinct_stoich": distinct_stoich,
            "local_cys": {
                "partial_rho_abundance": round(local_rho, 6),
                "p": round(pval, 6),
                "actual_B": PERM_B,
                "auroc": round(auroc, 6),
            },
            "near_vs_far_cys": {
                "near_rho": round(near_rho, 6),
                "far_rho": round(far_rho, 6),
            },
            "kat_motif": {
                "partial_rho": round(kat_rho, 6),
                "best_component": kat_name,
                "components": {
                    "basic_KR": round(kat_basic_rho, 6),
                    "acidic_DE": round(kat_acidic_rho, 6),
                    "small_GA": round(kat_smallga_rho, 6),
                },
                "survives": kat_survives,
            },
            "cys_free_subset": {
                "n": cf_n,
                "residual_rho": round(cys_free_residual, 6),
            },
            "posctrl": {
                "cys_m3_rho": round(cys_m3_rho, 6),
                "cys_m2_rho": round(cys_m2_rho, 6),
                "cys_m4_rho": round(cys_m4_rho, 6),
                "composite_rho": round(composite_rho, 6),
                "reproduced": pos_reproduced,
            },
            "runtime_sec": round(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
        }
    except Exception as exc:
        status = "failed"
        verdict = "needs_data"
        exit_code = 1
        note = f"运行异常: {exc}"
        result = {"runtime_sec": round(time.time() - t0, 3), "cannot_claim": cannot_claim}

    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    print(json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

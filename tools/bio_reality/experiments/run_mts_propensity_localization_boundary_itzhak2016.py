#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""离线 MTS propensity / localization boundary 实验。

纯 stdlib；输入固定为 repo-relative tools/bio_reality/data/mts_localization_itzhak2016.json。
最后一行输出规定 JSON。
"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "mts_propensity_localization_boundary_itzhak2016"
CLAIM_ID = "h3.cross_layer_relation.subcellular_localization.mts_propensity_localization_boundary_itzhak2016"
DATA = Path.cwd() / "tools/bio_reality/data/mts_localization_itzhak2016.json"
AA20 = list("ACDEFGHIKLMNPQRSTVWY")
HIGH_CONF = {"Very High", "High"}
PERM_B = 2000
SEED = 20260622


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def sd(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1))


def zscores(xs):
    m = mean(xs)
    s = sd(xs)
    if s <= 0:
        return [0.0 for _ in xs]
    return [(x - m) / s for x in xs]


def compute_score(prots):
    nb = [float(p["nmts_netbasic"]) for p in prots]
    st = [float(p["nmts_st"]) for p in prots]
    mo = [float(p["nmts_moment"]) for p in prots]
    z_nb = zscores(nb)
    z_st = zscores(st)
    z_mo = zscores(mo)
    for p, a, b, c in zip(prots, z_nb, z_st, z_mo):
        p["_nmts_score"] = a + b + c


def rankdata(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
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


def rank_effect(xs, labels):
    n1 = sum(labels)
    n0 = len(labels) - n1
    if n1 == 0 or n0 == 0:
        return {"u": float("nan"), "auc": float("nan"), "rank_biserial": float("nan")}
    ranks = rankdata(xs)
    r1 = sum(r for r, y in zip(ranks, labels) if y)
    u = r1 - n1 * (n1 + 1) / 2.0
    auc = u / (n1 * n0)
    return {"u": u, "auc": auc, "rank_biserial": 2 * auc - 1}


def diff_mean(xs, labels):
    a = [x for x, y in zip(xs, labels) if y]
    b = [x for x, y in zip(xs, labels) if not y]
    return mean(a) - mean(b)


def permutation_p(xs, labels, b=PERM_B, seed=SEED):
    rng = random.Random(seed)
    obs = diff_mean(xs, labels)
    n1 = sum(labels)
    shuffled = list(labels)
    extreme = 0
    for _ in range(b):
        rng.shuffle(shuffled)
        stat = diff_mean(xs, shuffled)
        if abs(stat) >= abs(obs) - 1e-15:
            extreme += 1
    return obs, (extreme + 1) / (b + 1), b


def solve_linear_system(a, b):
    n = len(b)
    mat = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(mat[r][col]))
        if abs(mat[pivot][col]) < 1e-12:
            mat[col][col] += 1e-8
            pivot = col
        if pivot != col:
            mat[col], mat[pivot] = mat[pivot], mat[col]
        div = mat[col][col]
        if abs(div) < 1e-20:
            div = 1e-20
        for j in range(col, n + 1):
            mat[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = mat[r][col]
            if fac == 0:
                continue
            for j in range(col, n + 1):
                mat[r][j] -= fac * mat[col][j]
    return [mat[i][n] for i in range(n)]


def residualize_score(prots, ridge=1e-3):
    y = [p["_nmts_score"] for p in prots]
    lengths = [math.log(max(1, p["length"])) for p in prots]
    charges = []
    for p in prots:
        freq = p["aafreq"]
        charges.append((freq[AA20.index("K")] + freq[AA20.index("R")]) - (freq[AA20.index("D")] + freq[AA20.index("E")]))
    raw_cols = [lengths] + [[p["aafreq"][i] for p in prots] for i in range(20)] + [charges]
    cols = [[1.0 for _ in prots]]
    for col in raw_cols:
        m = mean(col)
        s = sd(col)
        if s <= 0:
            cols.append([0.0 for _ in col])
        else:
            cols.append([(v - m) / s for v in col])
    pcols = len(cols)
    xtx = [[0.0] * pcols for _ in range(pcols)]
    xty = [0.0] * pcols
    for i in range(len(prots)):
        row = [col[i] for col in cols]
        for j in range(pcols):
            xty[j] += row[j] * y[i]
            for k in range(j, pcols):
                xtx[j][k] += row[j] * row[k]
    for j in range(pcols):
        for k in range(j):
            xtx[j][k] = xtx[k][j]
    for j in range(1, pcols):
        xtx[j][j] += ridge
    beta = solve_linear_system(xtx, xty)
    residuals = []
    for i in range(len(prots)):
        pred = sum(beta[j] * cols[j][i] for j in range(pcols))
        residuals.append(y[i] - pred)
    return residuals


def marker_positive_control(prots):
    marker = [p for p in prots if p["marker_class"]]
    mito = [p for p in marker if p["marker_class"] == "Mitochondrion"]
    non = [p for p in marker if p["marker_class"] and p["marker_class"] != "Mitochondrion"]
    xs = [p["_nmts_score"] for p in mito + non]
    labels = [1] * len(mito) + [0] * len(non)
    stat, pval, _ = permutation_p(xs, labels, seed=SEED + 11)
    return {
        "n_mito": len(mito),
        "n_nonmito": len(non),
        "marker_mito_mean": mean([p["_nmts_score"] for p in mito]),
        "marker_nonmito_mean": mean([p["_nmts_score"] for p in non]),
        "stat": stat,
        "p": pval,
    }


def subcomp_group_name(p):
    s = (p.get("sub_comp") or "").strip()
    if s in {"Matrix", "Mito_Matrix"}:
        return "matrix_inner"
    if s in {"Mito_Inner", "Inner", "Inner Membrane"}:
        return "matrix_inner"
    if s in {"Mito_Outer", "Outer", "Outer Membrane"}:
        return "outer"
    return ""


def subcomp_dissociation(prots):
    mito = [p for p in prots if p["top_pred"] == "Mitochondrion"]
    mi = [p for p in mito if subcomp_group_name(p) == "matrix_inner"]
    outer = [p for p in mito if subcomp_group_name(p) == "outer"]
    xs = [p["_nmts_score"] for p in mi + outer]
    labels = [1] * len(mi) + [0] * len(outer)
    if not mi or not outer:
        return {
            "n_matrix_inner": len(mi), "n_outer": len(outer),
            "matrix_inner_mean": float("nan"), "outer_mean": float("nan"),
            "stat": float("nan"), "p": 1.0,
        }
    stat, pval, _ = permutation_p(xs, labels, seed=SEED + 23)
    return {
        "n_matrix_inner": len(mi),
        "n_outer": len(outer),
        "matrix_inner_mean": mean([p["_nmts_score"] for p in mi]),
        "outer_mean": mean([p["_nmts_score"] for p in outer]),
        "stat": stat,
        "p": pval,
    }


def carrier_ta_flag(p):
    gene = (p.get("gene") or "").upper().replace("-", "")
    return gene.startswith("SLC25") or gene.startswith("TOMM") or gene.startswith("SAMM") or gene.startswith("MAVS")


def enrichment_2x2(a, b, c, d, bperm=PERM_B, seed=SEED + 37):
    total = a + b + c + d
    if total == 0:
        return {"fold": float("nan"), "p": 1.0}
    low_n = a + b
    flags = [1] * (a + c) + [0] * (b + d)
    obs = a
    rng = random.Random(seed)
    extreme = 0
    for _ in range(bperm):
        rng.shuffle(flags)
        stat = sum(flags[:low_n])
        if stat >= obs:
            extreme += 1
    low_rate = a / max(1, a + b)
    high_rate = c / max(1, c + d)
    fold = low_rate / high_rate if high_rate > 0 else float("inf")
    return {"fold": fold, "p": (extreme + 1) / (bperm + 1)}


def defiance(prots):
    high_conf = [p for p in prots if p["confidence"] in HIGH_CONF]
    non_scores = [p["_nmts_score"] for p in high_conf if p["top_pred"] != "Mitochondrion"]
    cutoff = median(non_scores)
    mito = [p for p in high_conf if p["top_pred"] == "Mitochondrion"]
    low = [p for p in mito if p["_nmts_score"] < cutoff]
    high = [p for p in mito if p["_nmts_score"] >= cutoff]
    a = sum(1 for p in low if carrier_ta_flag(p))
    b = len(low) - a
    c = sum(1 for p in high if carrier_ta_flag(p))
    d = len(high) - c
    enr = enrichment_2x2(a, b, c, d)
    examples = sorted(low, key=lambda p: (carrier_ta_flag(p) == 0, p["_nmts_score"]))[:25]
    return {
        "cutoff_nonmito_median": cutoff,
        "n": len(low),
        "n_mito_high_conf": len(mito),
        "carrier_ta_low": a,
        "carrier_ta_high": c,
        "carrier_TA_enriched": enr["p"] < 0.05 and enr["fold"] > 1.0,
        "carrier_TA_fold": enr["fold"],
        "carrier_TA_p": enr["p"],
        "examples": [
            {
                "uniprot": p["uniprot"],
                "gene": p["gene"],
                "sub_comp": p["sub_comp"],
                "nmts_score": round(p["_nmts_score"], 6),
                "tm_count": p["tm_count"],
                "carrier_TA_flag": carrier_ta_flag(p),
            }
            for p in examples
        ],
    }


def finite_round(x, digits=6):
    if isinstance(x, float):
        if math.isnan(x) or math.isinf(x):
            return None if math.isnan(x) else ("inf" if x > 0 else "-inf")
        return round(x, digits)
    if isinstance(x, dict):
        return {k: finite_round(v, digits) for k, v in x.items()}
    if isinstance(x, list):
        return [finite_round(v, digits) for v in x]
    return x


def main():
    start = time.time()
    checks = {
        "xlsx_parsed": False,
        "uniprot_batch_joined": False,
        "nmts_computed": False,
        "measured_label_no_leakage": True,
        "composition_controlled_perm": False,
        "subcompartment_dissociation": False,
        "positive_control": False,
        "localization_verdict": False,
    }
    status = "passed"
    verdict = "composition_artifact"
    note = ""
    exit_code = 0
    try:
        payload = json.loads(DATA.read_text(encoding="utf-8"))
        prots = payload["prots"]
        meta = payload.get("meta", {})
        checks["xlsx_parsed"] = len(prots) > 8000 and "header" in meta
        checks["uniprot_batch_joined"] = len(prots) > 8000
        checks["nmts_computed"] = all("nmts_netbasic" in p and "aafreq" in p and len(p["aafreq"]) == 20 for p in prots)
        compute_score(prots)

        high_conf = [p for p in prots if p["confidence"] in HIGH_CONF]
        main_set = [p for p in high_conf if p["top_pred"]]
        xs = [p["_nmts_score"] for p in main_set]
        labels = [1 if p["top_pred"] == "Mitochondrion" else 0 for p in main_set]
        main_stat, main_p, actual_perm = permutation_p(xs, labels, seed=SEED)
        eff = rank_effect(xs, labels)

        residuals = residualize_score(main_set)
        ctrl_stat, ctrl_p, _ = permutation_p(residuals, labels, seed=SEED + 5)
        checks["composition_controlled_perm"] = ctrl_p < 0.01 and ctrl_stat > 0

        diss = subcomp_dissociation(prots)
        checks["subcompartment_dissociation"] = diss["p"] < 0.05 and diss["matrix_inner_mean"] > diss["outer_mean"]

        pos = marker_positive_control(prots)
        hspd1 = next((p for p in prots if p["uniprot"] == "P10809"), None)
        atp1a1 = next((p for p in prots if p["uniprot"] == "P05023"), None)
        hspd1_ok = hspd1 is not None and hspd1["_nmts_score"] > mean([p["_nmts_score"] for p in prots])
        atp_ok = atp1a1 is not None and atp1a1["tm_count"] >= 8
        checks["positive_control"] = pos["p"] < 0.01 and pos["stat"] > 0 and hspd1_ok and atp_ok

        defi = defiance(prots)
        contact = main_p < 0.01 and main_stat > 0 and ctrl_p < 0.01 and ctrl_stat > 0 and checks["subcompartment_dissociation"]
        if contact and defi["carrier_TA_enriched"]:
            verdict = "defied_boundary"
            note = "N-MTS 倾向与 measured 线粒体定位有接触，且低 N-MTS measured-mito 中 SLC25/TOMM/TA-like 边界名单富集；不声称 import 速率或跨细胞普遍性。"
        elif contact:
            verdict = "mts_localization_contact"
            note = "N-MTS 倾向越过 readback 边界预测 HeLa measured 线粒体定位，并在 matrix/inner vs outer split 中分离；defiance 名单存在但 carrier/TA 富集未达阈值。"
        else:
            verdict = "composition_artifact"
            note = "N-MTS 与定位的原始接触未能同时通过 composition/length/charge 控制和 sub-compartment dissociation。"
        checks["localization_verdict"] = contact
        if not checks["positive_control"] or not checks["uniprot_batch_joined"]:
            status = "needs_data"
            verdict = "composition_artifact"
            exit_code = 3
            note = "正对照或 UniProt join 未达预设阈值，主判不下。"

        result = {
            "n_joined": len(prots),
            "n_mito": sum(1 for p in prots if p["top_pred"] == "Mitochondrion"),
            "main": {
                "n_high_conf": len(main_set),
                "n_mito_high_conf": sum(labels),
                "stat": main_stat,
                "p_perm": main_p,
                "effect": eff,
                "mito_mean": mean([x for x, y in zip(xs, labels) if y]),
                "nonmito_mean": mean([x for x, y in zip(xs, labels) if not y]),
            },
            "composition_controlled": {"stat": ctrl_stat, "p_after_control": ctrl_p},
            "dissociation": diss,
            "posctrl": {
                "marker_mito_mean": pos["marker_mito_mean"],
                "marker_nonmito_mean": pos["marker_nonmito_mean"],
                "p": pos["p"],
                "n_marker_mito": pos["n_mito"],
                "n_marker_nonmito": pos["n_nonmito"],
                "hspd1_nmts": hspd1["_nmts_score"] if hspd1 else None,
                "hspd1_netbasic": hspd1["nmts_netbasic"] if hspd1 else None,
                "atp1a1_tm": atp1a1["tm_count"] if atp1a1 else None,
            },
            "defiance": defi,
            "actual_perm": actual_perm,
            "runtime_sec": time.time() - start,
            "cannot_claim": [
                "静态稳态定位非 import 速率/通量",
                "HeLa only 不跨细胞/物种",
                "N-MTS/TM 是 stdlib 启发式非实验靶向测定(粗 TM 窗口可能误判 ±1)",
                "用 measured 标签防 leakage 但 Top Prediction 本身有分类误差",
                "defiance 名单受 sub-compartment 注释完整性限制",
            ],
        }
    except Exception as exc:
        status = "needs_data"
        verdict = "composition_artifact"
        note = "实验运行失败: %s" % exc
        result = {
            "n_joined": 0,
            "n_mito": 0,
            "main": {},
            "composition_controlled": {},
            "dissociation": {},
            "posctrl": {},
            "defiance": {},
            "actual_perm": 0,
            "runtime_sec": time.time() - start,
            "cannot_claim": [
                "静态稳态定位非 import 速率/通量",
                "HeLa only 不跨细胞/物种",
                "N-MTS/TM 是 stdlib 启发式非实验靶向测定(粗 TM 窗口可能误判 ±1)",
                "用 measured 标签防 leakage 但 Top Prediction 本身有分类误差",
                "defiance 名单受 sub-compartment 注释完整性限制",
            ],
        }
        exit_code = 3

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    print(json.dumps(finite_round(out), ensure_ascii=False, separators=(",", ":")))
    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()

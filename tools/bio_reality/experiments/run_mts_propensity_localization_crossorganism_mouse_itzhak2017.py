#!/usr/bin/env python3
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path

EXPERIMENT_ID = "mts_propensity_localization_crossorganism_mouse_itzhak2017"
CLAIM_ID = "h3.cross_layer_relation.subcellular_localization.mts_propensity_localization_crossorganism_mouse_itzhak2017"

数据路径 = Path.cwd() / "tools/bio_reality/data/mts_localization_mouse_itzhak2017.json"
氨基酸顺序 = list("ACDEFGHIKLMNPQRSTVWY")
SEED = 11520270622


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def sd(xs):
    if len(xs) < 2:
        return 0.0
    return statistics.pstdev(xs)


def z准备(vals):
    m = mean(vals)
    s = sd(vals)
    if s == 0:
        s = 1.0
    return m, s


def mann_whitney_u(x, y):
    合 = [(v, 1) for v in x] + [(v, 0) for v in y]
    合.sort(key=lambda t: t[0])
    rank_sum_x = 0.0
    i = 0
    while i < len(合):
        j = i + 1
        while j < len(合) and 合[j][0] == 合[i][0]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            if 合[k][1] == 1:
                rank_sum_x += avg_rank
        i = j
    nx = len(x)
    ny = len(y)
    u = rank_sum_x - nx * (nx + 1) / 2.0
    auc = u / (nx * ny) if nx and ny else float("nan")
    return u, auc


def point_biserial(vals, labels):
    x1 = [v for v, y in zip(vals, labels) if y]
    x0 = [v for v, y in zip(vals, labels) if not y]
    allm = mean(vals)
    s = sd(vals)
    if not x1 or not x0 or s == 0:
        return 0.0
    p = len(x1) / len(vals)
    q = len(x0) / len(vals)
    return (mean(x1) - mean(x0)) / s * math.sqrt(p * q)


def label_perm_p(vals, labels, nperm=5000):
    rng = random.Random(SEED)
    n1 = sum(labels)
    obs = mean([v for v, y in zip(vals, labels) if y]) - mean([v for v, y in zip(vals, labels) if not y])
    count = 1
    idx = list(range(len(vals)))
    for _ in range(nperm):
        rng.shuffle(idx)
        s1 = sum(vals[i] for i in idx[:n1])
        s0 = sum(vals[i] for i in idx[n1:])
        d = s1 / n1 - s0 / (len(vals) - n1)
        if d >= obs:
            count += 1
    return count / (nperm + 1), obs


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def 全长净电荷(p):
    freqs = p["aafreq"]
    d = {aa: freqs[i] for i, aa in enumerate(氨基酸顺序)}
    return (d.get("K", 0.0) + d.get("R", 0.0) - d.get("D", 0.0) - d.get("E", 0.0))


def 组成距离(a, b):
    da = math.log1p(a["length"]) - math.log1p(b["length"])
    dc = 全长净电荷(a) - 全长净电荷(b)
    s = 2.0 * da * da + 10.0 * dc * dc
    af = a["aafreq"]
    bf = b["aafreq"]
    for x, y in zip(af, bf):
        d = x - y
        s += d * d
    return s


def 组成控制_p(mito, non, score_key="nmts_score", nperm=5000):
    # 每个 mito 找一个全长 aa 组成/长度/净电荷最近的非 mito；随后做配对符号置换。
    diffs = []
    used = set()
    non_sorted = list(non)
    for m in sorted(mito, key=lambda p: p["uniprot"]):
        best = None
        bestd = None
        for n in non_sorted:
            d = 组成距离(m, n)
            if n["uniprot"] in used:
                d += 0.02
            if best is None or d < bestd:
                best = n
                bestd = d
        if best is not None:
            used.add(best["uniprot"])
            diffs.append(m[score_key] - best[score_key])
    if not diffs:
        return None
    obs = mean(diffs)
    rng = random.Random(SEED + 1)
    count = 1
    for _ in range(nperm):
        d = 0.0
        for x in diffs:
            d += x if rng.random() < 0.5 else -x
        d /= len(diffs)
        if d >= obs:
            count += 1
    return {
        "p_after_control": count / (nperm + 1),
        "effect_matched_mean_diff": obs,
        "n_pairs": len(diffs),
    }


def fisher_one_sided(a, b, c, d):
    # 表: defiant flagged=a, defiant unflagged=b, other flagged=c, other unflagged=d; 右尾富集。
    from math import comb
    n = a + b + c + d
    row1 = a + b
    col1 = a + c
    denom = comb(n, row1)
    max_a = min(row1, col1)
    p = 0.0
    for x in range(a, max_a + 1):
        if row1 - x <= n - col1:
            p += comb(col1, x) * comb(n - col1, row1 - x) / denom
    return p


def 是否_defiance_gene(gene):
    g = (gene or "").lower()
    return g.startswith("slc25") or g.startswith("tomm") or g == "samm50"


def main():
    t0 = time.time()
    checks = {
        "xlsx_parsed": False,
        "uniprot_batch_joined": False,
        "nmts_computed": False,
        "measured_label_no_leakage": False,
        "composition_controlled_perm": False,
        "defiance_set": False,
        "positive_control": False,
        "crossorganism_verdict": False,
    }
    cannot_claim = [
        "静态稳态定位非 import 速率",
        "mouse neuron(单组织/系统)非全 mouse",
        "N-MTS/TM stdlib 启发式",
        "measured Prediction 有分类误差",
        "用 measured 防 leakage",
        "defiance 受 sub-comp 注释完整性限制",
        "深化 human MTS 的跨物种臂(observational 保守非机制)",
    ]

    try:
        data = json.loads(数据路径.read_text(encoding="utf-8"))
    except Exception as e:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "hela_specific",
            "note": "无法读取输入 JSON: %s" % e,
            "result": {"cannot_claim": cannot_claim},
        }
        print(json.dumps(out, ensure_ascii=False, separators=(",", ":")))
        sys.exit(3)

    meta = data.get("meta", {})
    prots = data.get("prots", [])
    checks["xlsx_parsed"] = bool(meta.get("headers")) and meta.get("sheet") == "Mouse Neuron Spatial Proteome"
    checks["uniprot_batch_joined"] = len(prots) >= 8000
    checks["measured_label_no_leakage"] = "UniProt used only for sequence" in meta.get("leakage_guard", "")

    vals_nb = [p["nmts_netbasic"] for p in prots]
    vals_st = [p["nmts_st"] for p in prots]
    vals_mo = [p["nmts_moment"] for p in prots]
    m_nb, s_nb = z准备(vals_nb)
    m_st, s_st = z准备(vals_st)
    m_mo, s_mo = z准备(vals_mo)
    for p in prots:
        p["nmts_score"] = (
            (p["nmts_netbasic"] - m_nb) / s_nb
            + (p["nmts_st"] - m_st) / s_st
            + (p["nmts_moment"] - m_mo) / s_mo
        )
    checks["nmts_computed"] = all("nmts_score" in p for p in prots)

    高置信 = [p for p in prots if p.get("confidence") in ("High", "Medium") and p.get("prediction")]
    mito = [p for p in 高置信 if p.get("prediction") == "Mitochondrion"]
    non = [p for p in 高置信 if p.get("prediction") != "Mitochondrion"]
    scores = [p["nmts_score"] for p in mito + non]
    labels = [1] * len(mito) + [0] * len(non)
    mito_scores = [p["nmts_score"] for p in mito]
    non_scores = [p["nmts_score"] for p in non]
    u, auc = mann_whitney_u(mito_scores, non_scores)
    p_perm, delta = label_perm_p(scores, labels)
    r_pb = point_biserial(scores, labels)
    main_res = {
        "stat": {
            "mann_whitney_u": round(u, 6),
            "auc": round(auc, 6),
            "point_biserial": round(r_pb, 6),
            "mean_mito": round(mean(mito_scores), 6),
            "mean_nonmito": round(mean(non_scores), 6),
            "median_mito": round(median(mito_scores), 6),
            "median_nonmito": round(median(non_scores), 6),
            "n_high_conf_mito": len(mito),
            "n_high_conf_nonmito": len(non),
        },
        "p_perm": p_perm,
        "effect": delta,
    }

    comp = 组成控制_p(mito, non)
    if comp:
        checks["composition_controlled_perm"] = True

    sub = None
    if meta.get("has_subcompartment"):
        sub = {"skipped": False, "note": "prep meta says sub-compartment exists but no matrix/inner/outer contrast was implemented"}
    else:
        sub = {"skipped": True, "reason": "Itzhak mouse sheet has Subcellular distribution but no matrix/inner/outer mitochondrial sub-compartment column"}

    non_median = median(non_scores)
    measured_mito_all = [p for p in prots if p.get("prediction") == "Mitochondrion"]
    defiant = [p for p in measured_mito_all if p["nmts_score"] < non_median]
    other_mito = [p for p in measured_mito_all if p["nmts_score"] >= non_median]
    a = sum(1 for p in defiant if 是否_defiance_gene(p.get("gene")))
    b = len(defiant) - a
    c = sum(1 for p in other_mito if 是否_defiance_gene(p.get("gene")))
    d = len(other_mito) - c
    prop_def = a / len(defiant) if defiant else 0.0
    prop_other = c / len(other_mito) if other_mito else 0.0
    fold = (prop_def / prop_other) if prop_other > 0 else (float("inf") if prop_def > 0 else 0.0)
    fisher_p = fisher_one_sided(a, b, c, d) if len(defiant) and len(other_mito) else 1.0
    examples = sorted(
        [
            {
                "gene": p["gene"],
                "uniprot": p["uniprot"],
                "prediction": p["prediction"],
                "confidence": p.get("confidence", ""),
                "nmts_score": round(p["nmts_score"], 5),
                "netbasic": p["nmts_netbasic"],
                "tm_count": p["tm_count"],
            }
            for p in defiant
            if 是否_defiance_gene(p.get("gene"))
        ],
        key=lambda x: (x["gene"].lower(), x["uniprot"]),
    )[:25]
    carrier_ta_enriched = fold > 1.5 and fisher_p < 0.05 and a >= 3
    checks["defiance_set"] = len(defiant) > 0
    defiance = {
        "n": len(defiant),
        "threshold_nonmito_median": round(non_median, 6),
        "flagged_defiant": a,
        "flagged_nondefiant_mito": c,
        "carrier_ta_enriched": carrier_ta_enriched,
        "fold": round(fold, 6) if math.isfinite(fold) else "inf",
        "fisher_p": fisher_p,
        "examples": examples,
    }

    marker_mito = [p for p in prots if p.get("marker") == "Mitochondrion"]
    marker_non = [p for p in prots if p.get("marker") and p.get("marker") != "Mitochondrion"]
    marker_scores = [p["nmts_score"] for p in marker_mito + marker_non]
    marker_labels = [1] * len(marker_mito) + [0] * len(marker_non)
    marker_p, marker_delta = label_perm_p(marker_scores, marker_labels, nperm=5000)
    by_gene = {}
    for p in prots:
        by_gene.setdefault(p.get("gene", "").lower(), p)
    hspd1 = by_gene.get("hspd1")
    atp1a1 = by_gene.get("atp1a1")
    hspd1_nmts = hspd1["nmts_score"] if hspd1 else None
    atp1a1_tm = atp1a1["tm_count"] if atp1a1 else None
    pos_ok = (
        marker_mito and marker_non
        and mean([p["nmts_score"] for p in marker_mito]) > mean([p["nmts_score"] for p in marker_non])
        and marker_p < 0.01
        and hspd1_nmts is not None and hspd1_nmts > mean(non_scores)
        and atp1a1_tm is not None and atp1a1_tm >= 2
    )
    checks["positive_control"] = bool(pos_ok)
    posctrl = {
        "marker_mito_mean": round(mean([p["nmts_score"] for p in marker_mito]), 6),
        "marker_nonmito_mean": round(mean([p["nmts_score"] for p in marker_non]), 6),
        "p": marker_p,
        "effect": marker_delta,
        "hspd1_nmts": round(hspd1_nmts, 6) if hspd1_nmts is not None else None,
        "hspd1_netbasic": hspd1["nmts_netbasic"] if hspd1 else None,
        "atp1a1_tm": atp1a1_tm,
    }

    contact_ok = p_perm < 0.01 and comp and comp["p_after_control"] < 0.01 and delta > 0
    defiance_ok = carrier_ta_enriched
    if not pos_ok or not checks["uniprot_batch_joined"]:
        status = "needs_data"
        verdict = "hela_specific"
        note = "正对照或 join 不足，主判不下；需检查解析、UniProt join 或启发式特征。"
        exit_code = 3
    else:
        status = "passed"
        if contact_ok and defiance_ok:
            verdict = "conserved_mouse"
            note = "mouse neuron measured Prediction 中 N-MTS propensity 对线粒体定位显著升高，组成/长度/全长净电荷匹配后仍成立；Slc25/Tomm/Samm50 低 N-MTS defiance 在 measured-mito 低端富集。因无 matrix/inner/outer 列，亚线粒体 dissociation 未判。"
        elif contact_ok or defiance_ok:
            verdict = "partial_conserved"
            note = "mouse neuron 中 contact 或 defiance 只有一臂复现；无 matrix/inner/outer 列，不能判亚线粒体 dissociation。"
        else:
            verdict = "hela_specific"
            note = "mouse neuron 中 N-MTS contact 在组成控制后未达到阈值，或 defiance 未复现；不支持跨物种保守。"
        exit_code = 0
    checks["crossorganism_verdict"] = status == "passed"

    result = {
        "n_joined": len(prots),
        "n_mito": sum(1 for p in prots if p.get("prediction") == "Mitochondrion"),
        "main": main_res,
        "composition_controlled": {
            "p_after_control": comp["p_after_control"] if comp else None,
            "effect": comp["effect_matched_mean_diff"] if comp else None,
            "n_pairs": comp["n_pairs"] if comp else 0,
        },
        "dissociation": sub,
        "defiance": defiance,
        "posctrl": posctrl,
        "actual_perm": {"main": 5000, "composition_controlled": 5000, "positive_control": 5000, "seed": SEED},
        "runtime_sec": round(time.time() - t0, 3),
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
    print(json.dumps(out, ensure_ascii=False, separators=(",", ":")))
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

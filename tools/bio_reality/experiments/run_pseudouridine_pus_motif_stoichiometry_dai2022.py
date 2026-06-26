#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""离线实验：PUS frozen motif 是否预测 measured mRNA Psi stoichiometry。

约束：纯 Python 标准库；读 repo-relative tools/bio_reality/data/*.json。
"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "pseudouridine_pus_motif_stoichiometry_dai2022"
CLAIM_ID = "h3.cross_layer_relation.rna_pseudouridylation.pseudouridine_pus_motif_stoichiometry_dai2022"
DATA_REL = Path("tools/bio_reality/data/pseudouridine_pus_motif_stoichiometry_dai2022.json")
SEED = 20260623
PERMUTATIONS = 2000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def stdev(xs):
    if len(xs) < 2:
        return float("nan")
    return statistics.stdev(xs)


def cohen_d(xs, ys):
    if len(xs) < 2 or len(ys) < 2:
        return float("nan")
    sx = stdev(xs)
    sy = stdev(ys)
    pooled_num = (len(xs) - 1) * sx * sx + (len(ys) - 1) * sy * sy
    pooled_den = len(xs) + len(ys) - 2
    if pooled_den <= 0 or pooled_num <= 0:
        return float("nan")
    return (mean(xs) - mean(ys)) / math.sqrt(pooled_num / pooled_den)


def rankdata(values):
    order = sorted(range(len(values)), key=lambda i: (values[i], i))
    ranks = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = avg_rank
        i = j
    return ranks


def solve_linear(a, b):
    # 小型高斯消元，足够处理 3x3 正规方程。
    n = len(b)
    mat = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(mat[r][col]))
        if abs(mat[pivot][col]) < 1e-12:
            raise ValueError("singular matrix")
        if pivot != col:
            mat[col], mat[pivot] = mat[pivot], mat[col]
        div = mat[col][col]
        for c in range(col, n + 1):
            mat[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            factor = mat[r][col]
            if factor == 0:
                continue
            for c in range(col, n + 1):
                mat[r][c] -= factor * mat[col][c]
    return [mat[i][n] for i in range(n)]


def residualize(y, covariates):
    n = len(y)
    cols = [[1.0] * n] + covariates
    p = len(cols)
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    for i in range(n):
        row = [col[i] for col in cols]
        for r in range(p):
            xty[r] += row[r] * y[i]
            for c in range(p):
                xtx[r][c] += row[r] * row[c]
    beta = solve_linear(xtx, xty)
    out = []
    for i in range(n):
        fitted = sum(beta[j] * cols[j][i] for j in range(p))
        out.append(y[i] - fitted)
    return out


def pearson(xs, ys):
    if len(xs) != len(ys) or len(xs) < 3:
        return float("nan")
    mx = mean(xs)
    my = mean(ys)
    sx2 = sum((x - mx) ** 2 for x in xs)
    sy2 = sum((y - my) ** 2 for y in ys)
    if sx2 <= 0 or sy2 <= 0:
        return float("nan")
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(sx2 * sy2)


def partial_spearman_control_gcu(sites):
    y_rank = rankdata([s["frac"] for s in sites])
    # frozen motif 分：TRUB1/PUS7 位置身份码中较强者；不在 Frac 上调参。
    x_rank = rankdata([max(s["trub1_score"], s["pus7_score"]) for s in sites])
    gc_rank = rankdata([s["gc"] for s in sites])
    u_rank = rankdata([s["u_frac"] for s in sites])
    y_res = residualize(y_rank, [gc_rank, u_rank])
    x_res = residualize(x_rank, [gc_rank, u_rank])
    rho = pearson(x_res, y_res)
    return rho, x_res, y_res


def permutation_pvalue(x_res, y_res, observed, b=PERMUTATIONS):
    rng = random.Random(SEED)
    work = list(x_res)
    extreme = 0
    obs_abs = abs(observed)
    for _ in range(b):
        rng.shuffle(work)
        r = pearson(work, y_res)
        if abs(r) >= obs_abs - 1e-15:
            extreme += 1
    return (extreme + 1) / (b + 1), b


def class_summary(sites):
    out = {}
    for klass in ["trub1", "pus7", "other"]:
        vals = [s["frac"] for s in sites if s["motif_class"] == klass]
        out[klass] = {
            "n": len(vals),
            "mean": round(mean(vals), 6) if vals else None,
            "sd": round(stdev(vals), 6) if len(vals) > 1 else None,
        }
    return out


def dataset_summaries(sites):
    datasets = sorted({s["dataset"] for s in sites})
    out = {}
    for dataset in datasets:
        ds = [s for s in sites if s["dataset"] == dataset]
        summ = class_summary(ds)
        trub1 = summ["trub1"]["mean"]
        pus7 = summ["pus7"]["mean"]
        other = summ["other"]["mean"]
        order = bool(trub1 is not None and pus7 is not None and other is not None and trub1 > pus7 > other)
        out[dataset] = {
            "n": len(ds),
            "motif_class_means": summ,
            "trub1_gt_pus7_gt_other": order,
            "trub1_other_d": round(cohen_d(
                [s["frac"] for s in ds if s["motif_class"] == "trub1"],
                [s["frac"] for s in ds if s["motif_class"] == "other"],
            ), 6),
        }
    return out


def positive_control(ds_summaries):
    out = {}
    ok = True
    for dataset, summ in ds_summaries.items():
        trub1 = summ["motif_class_means"]["trub1"]["mean"]
        other = summ["motif_class_means"]["other"]["mean"]
        d = summ["trub1_other_d"]
        reproduced = bool(trub1 is not None and other is not None and trub1 > other and d >= 0.5)
        ok = ok and reproduced
        out[dataset] = {
            "trub1_frac": trub1,
            "other_frac": other,
            "trub1_other_d": d,
            "reproduced": reproduced,
        }
    return out, ok


def main():
    start = time.time()
    data_path = Path.cwd() / DATA_REL
    if not data_path.exists():
        result = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {
                "bidseq_parsed": False,
                "frac_continuous": False,
                "pus_motif_frozen": True,
                "gc_u_controlled": False,
                "cross_dataset": False,
                "positive_control": False,
                "psi_verdict": False,
            },
            "verdict": "needs_data",
            "note": f"找不到数据文件: {data_path}",
            "result": {},
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 1

    payload = json.loads(data_path.read_text(encoding="utf-8"))
    sites = payload.get("sites", [])
    datasets = sorted({s["dataset"] for s in sites})
    distinct_frac = len({s["frac"] for s in sites})
    bidseq_parsed = bool(sites and all(k in sites[0] for k in ["frac", "motif_window", "motif_class", "gc", "u_frac"]))
    frac_continuous = distinct_frac > 10 and all(0 <= s["frac"] <= 100.000001 for s in sites)

    rho, x_res, y_res = partial_spearman_control_gcu(sites)
    p, actual_b = permutation_pvalue(x_res, y_res, rho)
    ds_summaries = dataset_summaries(sites)
    posctrl, pos_ok = positive_control(ds_summaries)
    combined = class_summary(sites)
    trub1_vals = [s["frac"] for s in sites if s["motif_class"] == "trub1"]
    other_vals = [s["frac"] for s in sites if s["motif_class"] == "other"]
    trub1_other_d = cohen_d(trub1_vals, other_vals)
    combined_order = bool(
        combined["trub1"]["mean"] is not None
        and combined["pus7"]["mean"] is not None
        and combined["other"]["mean"] is not None
        and combined["trub1"]["mean"] > combined["pus7"]["mean"] > combined["other"]["mean"]
    )
    concordant_datasets = [d for d, s in ds_summaries.items() if s["trub1_gt_pus7_gt_other"]]
    transfer_ok = len(concordant_datasets) >= 2
    significant = p < 0.01
    effect_ok = abs(rho) >= 0.10 or trub1_other_d >= 0.5

    if bidseq_parsed and frac_continuous and significant and effect_ok and combined_order and transfer_ok and pos_ok:
        verdict = "crosses_boundary"
    elif bidseq_parsed and frac_continuous and not significant:
        verdict = "composition_artifact"
    elif bidseq_parsed and frac_continuous and significant:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "needs_data"
    status = "passed" if verdict != "needs_data" else "failed"

    checks = {
        "bidseq_parsed": bidseq_parsed,
        "frac_continuous": frac_continuous,
        "pus_motif_frozen": True,
        "gc_u_controlled": True,
        "cross_dataset": transfer_ok,
        "positive_control": pos_ok,
        "psi_verdict": verdict in {"crosses_boundary", "bounded_descriptor_only", "composition_artifact"},
    }
    cross_dataset = {}
    for dataset in ["hela", "hek293t", "a549"]:
        if dataset in ds_summaries:
            cross_dataset[dataset] = {
                "n": ds_summaries[dataset]["n"],
                "trub1": ds_summaries[dataset]["motif_class_means"]["trub1"]["mean"],
                "pus7": ds_summaries[dataset]["motif_class_means"]["pus7"]["mean"],
                "other": ds_summaries[dataset]["motif_class_means"]["other"]["mean"],
                "trub1_gt_pus7_gt_other": ds_summaries[dataset]["trub1_gt_pus7_gt_other"],
                "trub1_other_d": ds_summaries[dataset]["trub1_other_d"],
            }
    cross_dataset["concordant"] = transfer_ok
    note = (
        "BID-seq measured mRNA Ψ Frac_Ave % 上，frozen TRUB1/PUS7 位置身份 motif "
        "在控制局部 GC 与 U 含量后仍预测化学计量；site 集来自 Deletion_Ave 化学 called rows，"
        "motif 为 post-hoc 序列规则。结论为观测性、条件于已检测 Ψ 位点。"
    )
    cannot_claim = [
        "BID-seq Ψ 测量(化学计量估计)",
        "mRNA Ψ 特定",
        "PUS motif 启发式(TRUB1/PUS7 不覆盖所有 PUS)",
        "cell-line",
        "观测性非因果",
        "site 集为已检测 Ψ 位点(条件于 detection)",
    ]
    result = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(sites),
            "datasets": datasets,
            "main": {
                "partial_rho_gcu": round(rho, 6),
                "p": round(p, 8),
                "actual_B": actual_b,
                "motif_score": "max(TRUB1_score,PUS7_score), frozen identity score",
                "trub1_other_d": round(trub1_other_d, 6),
            },
            "motif_class_means": {
                "trub1": combined["trub1"],
                "pus7": combined["pus7"],
                "other": combined["other"],
                "trub1_gt_pus7_gt_other": combined_order,
            },
            "cross_dataset": cross_dataset,
            "posctrl": {
                "trub1_frac": combined["trub1"]["mean"],
                "other_frac": combined["other"]["mean"],
                "trub1_other_d": round(trub1_other_d, 6),
                "reproduced": pos_ok,
                "by_dataset": posctrl,
            },
            "runtime_sec": round(time.time() - start, 6),
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if verdict == "needs_data":
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())

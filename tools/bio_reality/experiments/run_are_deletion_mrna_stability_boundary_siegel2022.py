#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ARE 删除 -> measured reporter mRNA stability 边界实验。

纯 Python 标准库；读 repo-relative:
tools/bio_reality/data/are_deletion_stability_siegel2022.json
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "are_deletion_mrna_stability_boundary_siegel2022"
CLAIM_ID = "h3.cross_layer_relation.utr3_are.are_deletion_mrna_stability_boundary_siegel2022"
DATA_REL = pathlib.Path("tools/bio_reality/data/are_deletion_stability_siegel2022.json")
SEED = 20220622
ACTUAL_PERM = 1000
GRADING_PERM = 2000

CANNOT_CLAIM = [
    "合成 160nt reporter 非内源全长 3'UTR/原生染色质上下文",
    "仅 2 免疫永生细胞系",
    "只测 ARE→decay 子轴(非 APA/PAS 选择/miRNA-seed/translation)",
    "effect_size 是 reporter T4/T0 ratio 非内源半衰期",
    "within-backbone 删除小碱基改变本身是因果变量",
    "grading 用 pooled label-permutation null(within-region 对 per-parent ARE-length 退化)",
]


def 有限数(v):
    try:
        x = float(v)
    except (TypeError, ValueError):
        return None
    if math.isfinite(x):
        return x
    return None


def 平均秩(values):
    indexed = sorted((v, i) for i, v in enumerate(values))
    ranks = [0.0] * len(values)
    j = 0
    while j < len(indexed):
        k = j + 1
        while k < len(indexed) and indexed[k][0] == indexed[j][0]:
            k += 1
        rank = (j + 1 + k) / 2.0
        for p in range(j, k):
            ranks[indexed[p][1]] = rank
        j = k
    return ranks


def pearson(x, y):
    n = len(x)
    if n < 3:
        return float("nan")
    mx = sum(x) / n
    my = sum(y) / n
    num = 0.0
    sx = 0.0
    sy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        num += da * db
        sx += da * da
        sy += db * db
    den = math.sqrt(sx * sy)
    if den == 0.0:
        return float("nan")
    return num / den


def spearman(x, y):
    if len(x) != len(y) or len(x) < 3:
        return float("nan")
    return pearson(平均秩(x), 平均秩(y))


def pearson_已秩(rank_x, rank_y):
    n = len(rank_x)
    if n < 3:
        return float("nan")
    mx = sum(rank_x) / n
    my = sum(rank_y) / n
    num = 0.0
    sx = 0.0
    sy = 0.0
    for a, b in zip(rank_x, rank_y):
        da = a - mx
        db = b - my
        num += da * db
        sx += da * da
        sy += db * db
    den = math.sqrt(sx * sy)
    if den == 0.0:
        return float("nan")
    return num / den


def 均值中位数阳性(effects):
    if not effects:
        return {"mean_effect": None, "median_effect": None, "pct_positive": None}
    return {
        "mean_effect": round(sum(effects) / len(effects), 6),
        "median_effect": round(statistics.median(effects), 6),
        "pct_positive": round(100.0 * sum(1 for v in effects if v > 0.0) / len(effects), 3),
    }


def 单侧均值符号置换_p(rows, rng, b):
    effects = [r["effect_size"] for r in rows]
    obs = sum(effects) / len(effects)
    ge = 0
    for _ in range(b):
        stat = sum(v if rng.random() < 0.5 else -v for v in effects) / len(effects)
        if stat >= obs - 1e-15:
            ge += 1
    return (ge + 1) / (b + 1)


def pooled_label_spearman_perm(rows, feature, rng, b):
    effects = [r["effect_size"] for r in rows]
    xs = [r[feature] for r in rows]
    effect_ranks = 平均秩(effects)
    feature_ranks = 平均秩(xs)
    obs = pearson_已秩(effect_ranks, feature_ranks)
    if not math.isfinite(obs):
        return obs, None

    ge_abs = 0
    for _ in range(b):
        shuffled_feature_ranks = list(feature_ranks)
        rng.shuffle(shuffled_feature_ranks)
        stat = pearson_已秩(effect_ranks, shuffled_feature_ranks)
        if math.isfinite(stat) and abs(stat) >= abs(obs) - 1e-15:
            ge_abs += 1
    return obs, (ge_abs + 1) / (b + 1)


def 规范行(raw_rows):
    out = []
    for row in raw_rows:
        effect = 有限数(row.get("effect_size"))
        are_len = 有限数(row.get("are_len"))
        are_cluster = 有限数(row.get("are_cluster"))
        region = str(row.get("region", "")).strip()
        if effect is None or are_len is None or are_cluster is None or not region:
            continue
        out.append(
            {
                "effect_size": effect,
                "are_len": are_len,
                "are_cluster": are_cluster,
                "region": region,
                "is_top_are": bool(row.get("is_top_are")),
            }
        )
    return out


def 分析_cell(rows, seed_offset):
    rng = random.Random(SEED + seed_offset)
    top_rows = [r for r in rows if r.get("is_top_are")]
    pos_rows = top_rows if top_rows else rows
    effects = [r["effect_size"] for r in pos_rows]
    pos = 均值中位数阳性(effects)
    # 正对照是 paired mutant-reference effect 是否偏正；用符号翻转 null。
    mean_p = 单侧均值符号置换_p(pos_rows, random.Random(SEED + seed_offset + 100), ACTUAL_PERM)
    rho_len, p_len = pooled_label_spearman_perm(
        rows, "are_len", random.Random(SEED + seed_offset + 200), GRADING_PERM
    )
    rho_cluster, p_cluster = pooled_label_spearman_perm(
        rows, "are_cluster", random.Random(SEED + seed_offset + 300), GRADING_PERM
    )
    _ = rng.random()
    return {
        "posctrl": pos,
        "mean_perm_p": round(mean_p, 6),
        "n_top_are": len(pos_rows),
        "grading": {
            "rho_len": round(rho_len, 6) if math.isfinite(rho_len) else None,
            "p_len_pooled": round(p_len, 6) if p_len is not None else None,
            "rho_cluster": round(rho_cluster, 6) if math.isfinite(rho_cluster) else None,
            "p_cluster_pooled": round(p_cluster, 6) if p_cluster is not None else None,
        },
    }


def 分级符号一致(a, b):
    pairs = [
        (a["rho_len"], b["rho_len"]),
        (a["rho_cluster"], b["rho_cluster"]),
    ]
    for x, y in pairs:
        if x is None or y is None:
            return False
        if x <= 0.0 or y <= 0.0:
            return False
    return True


def 分级置换支持(a, b):
    len_ok = (
        a["p_len_pooled"] is not None
        and b["p_len_pooled"] is not None
        and a["p_len_pooled"] < 0.01
        and b["p_len_pooled"] < 0.01
    )
    cluster_ok = (
        a["p_cluster_pooled"] is not None
        and b["p_cluster_pooled"] is not None
        and a["p_cluster_pooled"] < 0.01
        and b["p_cluster_pooled"] < 0.01
    )
    return len_ok or cluster_ok


def main():
    t0 = time.time()
    data_path = pathlib.Path.cwd() / DATA_REL
    checks = {
        "data_parsed": False,
        "joined_parent": False,
        "posctrl": False,
        "grading_spearman": False,
        "within_region_perm": False,
        "corrected_pooled_null": False,
        "grading_permutation_supported": False,
        "cross_cellline_replication": False,
        "stability_verdict": False,
    }

    try:
        with data_path.open("r", encoding="utf-8") as f:
            payload = json.load(f)
        checks["data_parsed"] = True
    except Exception as e:
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "does_not_cross",
            "note": "无法读取/解析 compact JSON: " + str(e),
            "result": {
                "n_jurkat": 0,
                "n_beas2b": 0,
                "posctrl": {},
                "grading": {},
                "sign_concordant": False,
                "actual_perm": ACTUAL_PERM,
                "grading_perm": GRADING_PERM,
                "null_method": "pooled_label_permutation_over_deletions(corrected; within-region was degenerate for per-parent predictor)",
                "runtime_sec": round(time.time() - t0, 3),
                "cannot_claim": CANNOT_CLAIM,
            },
        }
        print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))
        return 3

    jurkat = 规范行(payload.get("jurkat", []))
    beas2b = 规范行(payload.get("beas2b", []))
    n_j = len(jurkat)
    n_b = len(beas2b)
    meta = payload.get("meta", {})
    checks["joined_parent"] = (
        n_j > 20
        and n_b > 20
        and int(meta.get("n_jurkat", -1)) == n_j
        and int(meta.get("n_beas2b", -1)) == n_b
    )

    if not checks["joined_parent"]:
        status = "needs_data"
        verdict = "does_not_cross"
        note = "取数不足或 meta n 与有效行不一致，不能评估 ARE 删除稳定性边界。"
        result = {
            "n_jurkat": n_j,
            "n_beas2b": n_b,
            "posctrl": {},
            "grading": {},
            "sign_concordant": False,
            "actual_perm": ACTUAL_PERM,
            "grading_perm": GRADING_PERM,
            "null_method": "pooled_label_permutation_over_deletions(corrected; within-region was degenerate for per-parent predictor)",
            "runtime_sec": round(time.time() - t0, 3),
            "cannot_claim": CANNOT_CLAIM,
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
        return 3

    j = 分析_cell(jurkat, 1000)
    b = 分析_cell(beas2b, 2000)

    posctrl_ok = (
        j["posctrl"]["mean_effect"] is not None
        and b["posctrl"]["mean_effect"] is not None
        and j["posctrl"]["mean_effect"] > 0.0
        and b["posctrl"]["mean_effect"] > 0.0
        and j["mean_perm_p"] < 0.01
        and b["mean_perm_p"] < 0.01
    )
    checks["posctrl"] = bool(posctrl_ok)

    sign_concordant = 分级符号一致(j["grading"], b["grading"])
    perm_complete = all(
        x is not None
        for x in [
            j["grading"]["p_len_pooled"],
            j["grading"]["p_cluster_pooled"],
            b["grading"]["p_len_pooled"],
            b["grading"]["p_cluster_pooled"],
        ]
    )
    perm_supported = 分级置换支持(j["grading"], b["grading"])
    grading_ok = sign_concordant and perm_supported
    checks["grading_spearman"] = bool(sign_concordant)
    checks["within_region_perm"] = False
    checks["corrected_pooled_null"] = bool(perm_complete)
    checks["grading_permutation_supported"] = bool(perm_supported)
    checks["cross_cellline_replication"] = bool(sign_concordant)

    if posctrl_ok and grading_ok:
        verdict = "crosses_boundary"
        status = "passed"
        note = (
            "ARE 删除在两个 reporter backbone 数据集中均显示稳定化正对照，"
            "且 ARE 长度/cluster 的 Spearman 分级方向在 Jurkat 与 Beas2B 一致为正，"
            "corrected pooled label-permutation p<0.01；旧 within-region null 对 per-parent predictor 退化，已不用。"
        )
    elif posctrl_ok:
        verdict = "partial_presence_only"
        status = "passed"
        note = (
            "ARE 删除稳定化正对照在两个细胞系复现；旧 within-region grading null 对 per-parent ARE_length/cluster 退化，"
            "已改用 pooled label-permutation 打破 length↔effect 关联。corrected pooled-null grading 未达 p<0.01，"
            "只能支持有无层面，不支持剂量式跨边界预测。"
        )
    else:
        verdict = "does_not_cross"
        status = "needs_data"
        note = (
            "ARE 删除稳定化正对照未在两个细胞系以 mean>0 且 permutation p<0.01 复现；"
            "旧 within-region grading null 对 per-parent predictor 退化，已换 pooled label-permutation，但按预登记不能推进定量分级结论。"
        )
    checks["stability_verdict"] = status == "passed"

    result = {
        "n_jurkat": n_j,
        "n_beas2b": n_b,
        "posctrl": {
            "jurkat": j["posctrl"],
            "beas2b": b["posctrl"],
            "mean_perm_p": {"jurkat": j["mean_perm_p"], "beas2b": b["mean_perm_p"]},
            "n_top_are": {"jurkat": j["n_top_are"], "beas2b": b["n_top_are"]},
        },
        "grading": {"jurkat": j["grading"], "beas2b": b["grading"]},
        "grading_corrected": {"jurkat": j["grading"], "beas2b": b["grading"]},
        "sign_concordant": bool(sign_concordant),
        "grading_permutation_supported": bool(perm_supported),
        "actual_perm": ACTUAL_PERM,
        "grading_perm": GRADING_PERM,
        "null_method": "pooled_label_permutation_over_deletions(corrected; within-region was degenerate for per-parent predictor)",
        "runtime_sec": round(time.time() - t0, 3),
        "cannot_claim": CANNOT_CLAIM,
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
    if status == "passed":
        return 0
    if status == "needs_data":
        return 3
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

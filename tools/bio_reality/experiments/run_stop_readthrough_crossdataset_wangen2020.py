#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Wangen2020 stop-context cross-dataset transfer experiment.

纯 stdlib离线实验。读取 repo-relative compact JSON，不重学规则；只检验冻结
stop identity + +1 nt ordinal 是否预测 measured RRTS。
"""

import json
import math
import random
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "stop_readthrough_crossdataset_wangen2020"
CLAIM_ID = "h3.cross_layer_relation.stop_readthrough.stop_readthrough_crossdataset_wangen2020"
DATA_REL = Path("tools/bio_reality/data/stop_readthrough_crossdataset_wangen2020.json")
SEED = 20260623
PERMUTATIONS = 1000
STIMULATED_CORE = ["G418_0.5", "Gentamicin", "Paromomycin"]
UNTREATED = "untr"


def average_ranks(values):
    ordered = sorted((value, idx) for idx, value in enumerate(values))
    ranks = [0.0] * len(values)
    i = 0
    while i < len(ordered):
        j = i + 1
        while j < len(ordered) and ordered[j][0] == ordered[i][0]:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[ordered[k][1]] = rank
        i = j
    return ranks


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return 0.0
    mx = sum(xs) / n
    my = sum(ys) / n
    sx = 0.0
    sy = 0.0
    cov = 0.0
    for x, y in zip(xs, ys):
        dx = x - mx
        dy = y - my
        cov += dx * dy
        sx += dx * dx
        sy += dy * dy
    if sx <= 0.0 or sy <= 0.0:
        return 0.0
    return cov / math.sqrt(sx * sy)


def spearman(xs, ys):
    return pearson(average_ranks(xs), average_ranks(ys))


def perm_pvalue(xs, ys, observed, seed):
    rng = random.Random(seed)
    xr = average_ranks(xs)
    yr = average_ranks(ys)
    extreme = 1
    abs_obs = abs(observed)
    for _ in range(PERMUTATIONS):
        shuffled = list(yr)
        rng.shuffle(shuffled)
        rho = pearson(xr, shuffled)
        if abs(rho) >= abs_obs - 1e-15:
            extreme += 1
    return extreme / (PERMUTATIONS + 1)


def mean(values):
    return sum(values) / len(values) if values else None


def rounded(value, digits=6):
    if value is None:
        return None
    return round(float(value), digits)


def group_by_condition(obs):
    out = {}
    for row in obs:
        out.setdefault(row["condition"], []).append(row)
    return out


def stop_means(rows):
    buckets = {"UGA": [], "UAG": [], "UAA": []}
    for row in rows:
        stop = row["stopcodon"]
        if stop in buckets:
            buckets[stop].append(row["rrts"])
    return {key: mean(vals) for key, vals in buckets.items()}


def stop4_means(rows):
    buckets = {}
    for row in rows:
        buckets.setdefault(row["stop4nt"], []).append(row["rrts"])
    return {key: mean(vals) for key, vals in buckets.items() if vals}


def residualize_y_by_log_cds(rows):
    # 控表达的补充检查：RRTS ~ intercept + log(cds_density)，返回 residual。
    xs = [math.log(row["cds_density"]) for row in rows]
    ys = [row["rrts"] for row in rows]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    den = sum((x - mx) ** 2 for x in xs)
    if den <= 0:
        return ys
    beta = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / den
    alpha = my - beta * mx
    return [y - (alpha + beta * x) for x, y in zip(xs, ys)]


def condition_result(condition, rows, cond_index):
    xs = [row["stop_ordinal"] for row in rows]
    ys = [row["rrts"] for row in rows]
    rho = spearman(xs, ys)
    p = perm_pvalue(xs, ys, rho, SEED + cond_index * 1009 + len(rows))
    residual_ys = residualize_y_by_log_cds(rows)
    residual_rho = spearman(xs, residual_ys)
    return {
        "cond": condition,
        "rho": rounded(rho),
        "p": rounded(p),
        "n": len(rows),
        "rho_expression_residual": rounded(residual_rho),
    }


def choose_verdict(by_condition, posctrl):
    by_name = {row["cond"]: row for row in by_condition}
    core = [by_name.get(name) for name in STIMULATED_CORE]
    core_ok = [
        row for row in core
        if row and row["rho"] is not None and row["rho"] >= 0.10 and row["p"] < 0.01
    ]
    any_negative = any(row and row["rho"] < -0.02 for row in core)
    if len(core_ok) >= 3 and posctrl["reproduced"]:
        return "transfers_cross_dataset"
    if any_negative:
        return "not_replicated"
    return "bounded_descriptor_only"


def main():
    start = time.time()
    data_path = Path.cwd() / DATA_REL
    checks = {
        "wangen_xlsx_parsed": False,
        "rrts_extracted": False,
        "frozen_rule_applied": False,
        "expression_controlled": False,
        "cross_condition": False,
        "positive_control": False,
        "stop_xfer_verdict": False,
    }
    if not data_path.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "compact JSON 不存在，无法离线实验。",
            "result": {"data_path": str(data_path)},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    with data_path.open("r", encoding="utf-8") as fh:
        data = json.load(fh)
    obs = data.get("obs", [])
    meta = data.get("meta", {})
    by_cond = group_by_condition(obs)
    conditions = list(meta.get("conditions") or sorted(by_cond))

    checks["wangen_xlsx_parsed"] = bool(meta.get("headers")) and bool(conditions)
    checks["rrts_extracted"] = bool(obs) and all("rrts" in row for row in obs[:100])
    checks["frozen_rule_applied"] = bool(obs) and all("stop_ordinal" in row for row in obs[:100])
    checks["expression_controlled"] = bool(obs) and min(row["cds_density"] for row in obs) >= 5.0
    checks["cross_condition"] = all(name in by_cond for name in STIMULATED_CORE)

    by_condition = []
    for idx, condition in enumerate(conditions):
        rows = by_cond.get(condition, [])
        if len(rows) >= 3:
            by_condition.append(condition_result(condition, rows, idx))

    g418_rows = by_cond.get("G418_0.5", [])
    g418_stop = stop_means(g418_rows)
    g418_stop_r = {key: rounded(value, 6) for key, value in g418_stop.items()}
    four_means = stop4_means(g418_rows)
    ugac_mean = four_means.get("UGAC")
    highest_stop4 = None
    if four_means:
        highest_stop4 = sorted(four_means.items(), key=lambda item: (-item[1], item[0]))[0][0]
    stop_order_ok = (
        g418_stop.get("UGA") is not None
        and g418_stop.get("UAG") is not None
        and g418_stop.get("UAA") is not None
        and g418_stop["UGA"] > g418_stop["UAG"] > g418_stop["UAA"]
    )
    ugac_highest = highest_stop4 == "UGAC"
    posctrl = {
        "g418_stop_means": g418_stop_r,
        "ugac_mean": rounded(ugac_mean, 6),
        "highest_stop4": highest_stop4,
        "ugac_highest": ugac_highest,
        "reproduced": bool(stop_order_ok and ugac_highest),
    }
    checks["positive_control"] = posctrl["reproduced"]

    verdict = choose_verdict(by_condition, posctrl)
    status = "passed" if verdict != "needs_data" else "needs_data"
    checks["stop_xfer_verdict"] = verdict in {
        "transfers_cross_dataset",
        "bounded_descriptor_only",
        "not_replicated",
    }
    if not all(checks.values()):
        status = "needs_data"
        verdict = "needs_data"
        checks["stop_xfer_verdict"] = False

    by_name = {row["cond"]: row for row in by_condition}
    untreated_rho = by_name.get(UNTREATED, {}).get("rho")
    stimulated_rows = [by_name.get(name) for name in STIMULATED_CORE]
    stimulated_concordant = all(
        row is not None and row["rho"] >= 0.10 and row["p"] < 0.01
        for row in stimulated_rows
    )

    cannot_claim = [
        "HEK293T/氨基糖苷诱导特定",
        "RRTS 测量噪声",
        "basal 通读噪声底(transfer 限 stimulated)",
        "stop 规则启发式",
        "观测性非因果",
        "同物种 human",
    ]
    note = (
        "冻结 stop-context 规则在独立 Wangen2020 measured RRTS 上做 cross-dataset transfer；"
        "不在 Wangen 重学或调参。scope: signal 主要在 aminoglycoside-stimulated/readthrough-quantifiable 条件，"
        "untreated/basal 接近噪声底。结果是观测性相关，非因果。"
    )

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(obs),
            "conditions": conditions,
            "main": {
                "by_condition": by_condition,
                "stimulated_core": STIMULATED_CORE,
                "stimulated_concordant": stimulated_concordant,
                "permutations": PERMUTATIONS,
                "seed": SEED,
            },
            "posctrl": posctrl,
            "untreated_rho": untreated_rho,
            "runtime_sec": rounded(time.time() - start, 6),
            "cannot_claim": cannot_claim,
            "data_meta": {
                "source": meta.get("source"),
                "leakage_guard": meta.get("leakage_guard"),
                "frozen_rule": meta.get("frozen_rule"),
                "expression_filter": meta.get("expression_filter"),
                "n_per_cond": meta.get("n_per_cond"),
            },
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    raise SystemExit(main())

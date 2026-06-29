#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验：蛋白-蛋白界面结构位置是否预测 measured binding ddG。

纯 stdlib；读 repo-relative:
tools/bio_reality/data/protein_interface_burial_binding_ddg_skempi.json
"""

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "protein_interface_burial_binding_ddg_skempi"
CLAIM_ID = "h3.cross_layer_relation.protein_binding_energetics.interface_burial_binding_ddg_skempi"

DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/protein_interface_burial_binding_ddg_skempi.json"
SEED = 91723
B = 1000
RHO_FLOOR = 0.10
MIN_BLOCK_N = 10
ILOC_ORDINAL = {"SUR": 0, "INT": 0, "RIM": 1, "SUP": 2, "COR": 3}


def mean(xs):
    return sum(xs) / len(xs)


def variance(xs):
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs)


def ranks(xs):
    pairs = sorted((x, i) for i, x in enumerate(xs))
    out = [0.0] * len(xs)
    j = 0
    while j < len(pairs):
        k = j + 1
        while k < len(pairs) and pairs[k][0] == pairs[j][0]:
            k += 1
        r = (j + k - 1) / 2.0 + 1.0
        for t in range(j, k):
            out[pairs[t][1]] = r
        j = k
    return out


def pearson(x, y):
    mx = mean(x)
    my = mean(y)
    sx = sum((v - mx) * (v - mx) for v in x)
    sy = sum((v - my) * (v - my) for v in y)
    if sx <= 0 or sy <= 0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sx * sy)


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def permutation_p_right(null, observed):
    ge = sum(1 for v in null if v >= observed)
    return (ge + 1) / (len(null) + 1)


def sd(xs):
    if not xs:
        return 0.0
    return math.sqrt(variance(xs) / len(xs))


def validate_record(row):
    pdb = row["pdb"]
    wt = row["wt"]
    mut = row["mut"]
    iloc = row["iloc"]
    if iloc not in ILOC_ORDINAL:
        raise ValueError(f"未知 iloc: {iloc}")
    ddg = float(row["ddg"])
    return {
        "pdb": str(pdb),
        "wt": str(wt),
        "mut": str(mut),
        "iloc": iloc,
        "burial": float(ILOC_ORDINAL[iloc]),
        "ddg": ddg,
    }


def prepare_blocks(records):
    by_sub = {}
    for i, row in enumerate(records):
        by_sub.setdefault((row["wt"], row["mut"]), []).append(i)
    blocks = {}
    for key in sorted(by_sub):
        idxs = by_sub[key]
        if len(idxs) < MIN_BLOCK_N:
            continue
        y = [records[i]["ddg"] for i in idxs]
        yr = ranks(y)
        my = (len(y) + 1) / 2.0
        y_ss = sum((v - my) * (v - my) for v in yr)
        blocks[key] = {
            "idxs": idxs,
            "y_rank": yr,
            "y_ss": y_ss,
            "n": len(idxs),
        }
    return blocks


def block_spearman_from_ranked_x(x, block):
    idxs = block["idxs"]
    n = block["n"]
    if n <= 1 or block["y_ss"] <= 0:
        return 0.0
    x_vals = [x[i] for i in idxs]
    xr = ranks(x_vals)
    mx = (n + 1) / 2.0
    my = mx
    x_ss = 0.0
    cov = 0.0
    for a, b in zip(xr, block["y_rank"]):
        dx = a - mx
        x_ss += dx * dx
        cov += dx * (b - my)
    if x_ss <= 0:
        return 0.0
    return cov / math.sqrt(x_ss * block["y_ss"])


def within_substitution_rho(burial, blocks):
    total = 0
    acc = 0.0
    block_rhos = []
    for key in sorted(blocks):
        block = blocks[key]
        rho = block_spearman_from_ranked_x(burial, block)
        n = block["n"]
        total += n
        acc += rho * n
        block_rhos.append({"substitution": key[0] + ">" + key[1], "n": n, "rho": rho})
    return (acc / total if total else 0.0), total, block_rhos


def pdb_groups(records):
    groups = {}
    for i, row in enumerate(records):
        groups.setdefault(row["pdb"], []).append(i)
    return groups


def permutable_pdb_groups(records):
    out = {}
    all_groups = pdb_groups(records)
    iloc_variable = 0
    for pdb, idxs in all_groups.items():
        if len({records[i]["iloc"] for i in idxs}) >= 2:
            iloc_variable += 1
        vals = {records[i]["burial"] for i in idxs}
        if len(idxs) >= 2 and len(vals) >= 2:
            out[pdb] = idxs
    return all_groups, out, iloc_variable


def permuted_within_pdb_burial(base, perm_groups, rnd):
    out = base[:]
    for idxs in perm_groups.values():
        vals = [base[i] for i in idxs]
        rnd.shuffle(vals)
        for i, val in zip(idxs, vals):
            out[i] = val
    return out


def iloc_counts(records):
    counts = {}
    for row in records:
        counts[row["iloc"]] = counts.get(row["iloc"], 0) + 1
    return {key: counts.get(key, 0) for key in ["SUR", "INT", "RIM", "SUP", "COR"]}


def failure_out(note, started=None, checks=None):
    runtime = 0.0 if started is None else time.time() - started
    out = {
        "status": "needs_data",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks if checks is not None else {"skempi_parsed": False},
        "verdict": "needs_data",
        "note": note,
        "result": {
            "n": 0,
            "distinct": 0,
            "main": {},
            "posctrl": {},
            "runtime_sec": runtime,
            "cannot_claim": ["未能读取 SKEMPI measured binding ddG compact JSON。"],
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(3)


def main():
    started = time.time()
    if not DATA_PATH.exists():
        failure_out(f"找不到数据文件: {DATA_PATH}", started)

    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    raw_records = payload["records"]
    records = [validate_record(row) for row in raw_records]
    if not records:
        failure_out("数据文件 records 为空。", started, {"skempi_parsed": False})

    burial = [row["burial"] for row in records]
    ddg = [row["ddg"] for row in records]
    distinct = len({round(v, 12) for v in ddg})
    blocks = prepare_blocks(records)
    rho_anchor = spearman(burial, ddg)
    pos_reproduced = (abs(rho_anchor) >= RHO_FLOOR and distinct > 10)
    rho_within, rows_in_blocks, block_rhos = within_substitution_rho(burial, blocks)

    all_pdb_groups, perm_groups, iloc_variable_pdbs = permutable_pdb_groups(records)
    permutable_rows = sum(len(v) for v in perm_groups.values())
    rnd = random.Random(SEED + 1701)
    null = []
    for _b in range(B):
        perm_burial = permuted_within_pdb_burial(burial, perm_groups, rnd)
        rho_perm, _rows, _block_rhos = within_substitution_rho(perm_burial, blocks)
        null.append(rho_perm)

    within_p = permutation_p_right(null, rho_within)
    null_var = variance(null) if null else 0.0
    null_degenerate = null_var <= 1e-18
    primary_crosses = abs(rho_within) >= RHO_FLOOR and within_p < 0.01

    if not pos_reproduced or distinct <= 10 or not blocks:
        verdict = "needs_data"
    elif primary_crosses:
        verdict = "crosses_boundary"
    elif within_p < 0.01:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "composition_artifact"

    status = "passed" if verdict != "needs_data" else "needs_data"
    n_pdb = len(all_pdb_groups)
    n_pdb_permutable = len(perm_groups)
    permutable_fraction = n_pdb_permutable / n_pdb if n_pdb else 0.0
    checks = {
        "skempi_parsed": True,
        "ddg_continuous": distinct > 10,
        "anchor_reproduced": pos_reproduced,
        "within_substitution_design": True,
        "within_pdb_perm_null": len(null) >= B and n_pdb_permutable > 0,
        "n_complexes_permutable": n_pdb_permutable,
        "primary_crosses": primary_crosses,
        "binding_verdict": verdict,
    }

    cannot_claim = [
        "观测性关联非因果。",
        "ddg 跨异质实验方法和温度，RT 使用行级温度近似或数据源近似。",
        "iloc 是粗 5 类界面结构标注，非连续 SASA 或真实接触数。",
        "within-pdb 置换控复合物混杂但不控位点级协变量，如二级结构。",
        "少数复合物 iloc 无变异使 within-pdb null 在那些复合物退化；已报告参与置换的复合物数。",
        "binding ddG 是 affinity 比值对数，假设 Kd 测量可比。",
    ]
    if null_degenerate:
        cannot_claim.append("within-pdb null 方差近零，置换检验不可作强判定。")

    note = (
        "SKEMPI single mutations: iloc ordinal burial(SUR/INT=0,RIM=1,SUP=2,COR=3) "
        "对 measured binding ddG；headline 在 fixed wt>mut substitution blocks 内计算，"
        "within-pdb permutation 保留复合物内 ddG 边际和 iloc 多重集并打乱 location↔ddG 映射。"
    )
    if permutable_fraction < 0.5:
        note += " 可置换复合物不足半数，null 的复合物覆盖度有限。"

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(records),
            "distinct": distinct,
            "main": {
                "rho_within": rho_within,
                "within_perm_p": within_p,
                "within_perm_mean": mean(null),
                "within_perm_min": min(null),
                "within_perm_max": max(null),
                "within_perm_sd": sd(null),
                "actual_B": len(null),
                "substitution_blocks_total": len({(r["wt"], r["mut"]) for r in records}),
                "substitution_blocks_used": len(blocks),
                "rows_in_blocks": rows_in_blocks,
                "min_block_n": MIN_BLOCK_N,
                "n_complexes": n_pdb,
                "n_complexes_iloc_variable": iloc_variable_pdbs,
                "n_complexes_permutable": n_pdb_permutable,
                "n_records_permutable": permutable_rows,
                "null_degenerate": null_degenerate,
                "block_rho_min": min((b["rho"] for b in block_rhos), default=0.0),
                "block_rho_max": max((b["rho"] for b in block_rhos), default=0.0),
                "block_rho_mean_unweighted": mean([b["rho"] for b in block_rhos]) if block_rhos else 0.0,
            },
            "posctrl": {
                "rho_anchor_burial_ddg": rho_anchor,
                "reproduced": pos_reproduced,
                "iloc_counts": iloc_counts(records),
                "mean_ddg": mean(ddg),
                "min_ddg": min(ddg),
                "max_ddg": max(ddg),
            },
            "runtime_sec": time.time() - started,
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if status == "passed" else 3)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        failure_out(str(e), time.time(), {"runtime_exception": True})

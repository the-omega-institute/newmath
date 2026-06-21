#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""纯 stdlib 离线实验：人类 m6A_load 是否预测更短 mRNA 半衰期。"""

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "m6a_load_halflife_crossorganism_human_m6aconquer"
CLAIM_ID = "h3.cross_layer_relation.rna_modification.m6a_load_halflife_crossorganism_human_m6aconquer"
DATA_REL = pathlib.Path("tools/bio_reality/data/m6a_load_halflife_human_m6aconquer.json")
CELL_LINES = ("HEK293", "K562", "HeLa")
PERM_N = 1000
SEED = 11320260622


def 有限数(v):
    return isinstance(v, (int, float)) and math.isfinite(float(v))


def 精简(v, sig=6):
    if v is None:
        return None
    if isinstance(v, bool):
        return v
    if isinstance(v, int):
        return v
    if isinstance(v, float):
        if not math.isfinite(v):
            return None
        return float(format(v, "." + str(sig) + "g"))
    return v


def rankdata(values):
    n = len(values)
    order = sorted(range(n), key=lambda i: values[i])
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i + 1
        vi = values[order[i]]
        while j < n and values[order[j]] == vi:
            j += 1
        avg = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = avg
        i = j
    return ranks


def pearson(x, y):
    n = len(x)
    if n < 3 or n != len(y):
        return None
    mx = sum(x) / n
    my = sum(y) / n
    sxx = 0.0
    syy = 0.0
    sxy = 0.0
    for a, b in zip(x, y):
        da = a - mx
        db = b - my
        sxx += da * da
        syy += db * db
        sxy += da * db
    if sxx <= 0.0 or syy <= 0.0:
        return None
    return sxy / math.sqrt(sxx * syy)


def spearman(x, y):
    if len(x) < 3:
        return None
    return pearson(rankdata(x), rankdata(y))


def solve_linear(a, b):
    n = len(b)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            return None
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def residualize(v, controls):
    n = len(v)
    cols = [[1.0] * n] + controls
    p = len(cols)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        row = [cols[j][i] for j in range(p)]
        yi = v[i]
        for a in range(p):
            xty[a] += row[a] * yi
            for b in range(a, p):
                xtx[a][b] += row[a] * row[b]
    for a in range(p):
        for b in range(a):
            xtx[a][b] = xtx[b][a]
    beta = solve_linear(xtx, xty)
    if beta is None:
        return None
    out = []
    for i in range(n):
        pred = beta[0]
        for j, c in enumerate(controls, start=1):
            pred += beta[j] * c[i]
        out.append(v[i] - pred)
    return out


def partial_corr_from_ranks(rx, ry, control_ranks):
    ex = residualize(rx, control_ranks)
    ey = residualize(ry, control_ranks)
    if ex is None or ey is None:
        return None
    return pearson(ex, ey)


def rows_for_cell(genes, cell):
    rows = []
    for sym, g in genes.items():
        hl = g.get("hl", {}).get(cell)
        load = g.get("m6a_load")
        length = g.get("exon_length")
        gc = g.get("gc")
        if 有限数(hl) and hl > 0 and 有限数(load) and 有限数(length) and length > 0 and 有限数(gc):
            rows.append((sym, float(load), math.log(float(hl)), float(length), float(gc)))
    rows.sort(key=lambda r: r[0])
    return rows


def cell_stats(genes, cell, seed):
    rows = rows_for_cell(genes, cell)
    x = [r[1] for r in rows]
    y = [r[2] for r in rows]
    length = [r[3] for r in rows]
    gc = [r[4] for r in rows]
    rx = rankdata(x)
    ry = rankdata(y)
    rlen = rankdata(length)
    rgc = rankdata(gc)

    rho = pearson(rx, ry)
    rho_len = partial_corr_from_ranks(rx, ry, [rlen])
    rho_lengc = partial_corr_from_ranks(rx, ry, [rlen, rgc])

    rng = random.Random(seed)
    extreme = 0
    perm_values = []
    obs_abs = abs(rho_lengc) if rho_lengc is not None else None
    if obs_abs is not None:
        shuffled = list(rx)
        for _ in range(PERM_N):
            rng.shuffle(shuffled)
            val = partial_corr_from_ranks(shuffled, ry, [rlen, rgc])
            if val is None:
                continue
            perm_values.append(val)
            if abs(val) >= obs_abs - 1e-15:
                extreme += 1
    p_perm = None
    if obs_abs is not None and len(perm_values) > 0:
        p_perm = (extreme + 1.0) / (len(perm_values) + 1.0)
    perm_mean = sum(perm_values) / len(perm_values) if perm_values else None
    perm_sd = None
    if perm_values and len(perm_values) > 1:
        m = perm_mean
        perm_sd = math.sqrt(sum((v - m) * (v - m) for v in perm_values) / (len(perm_values) - 1))

    return {
        "n": len(rows),
        "rho": 精简(rho),
        "rho_partial_len": 精简(rho_len),
        "rho_partial_lengc": 精简(rho_lengc),
        "p_perm": 精简(p_perm),
        "perm_extreme": extreme,
        "perm_done": len(perm_values),
        "perm_mean": 精简(perm_mean),
        "perm_sd": 精简(perm_sd),
    }


def crosscell_halflife_corr(genes):
    out = {}
    for i, a in enumerate(CELL_LINES):
        for b in CELL_LINES[i + 1 :]:
            xs = []
            ys = []
            for g in genes.values():
                ha = g.get("hl", {}).get(a)
                hb = g.get("hl", {}).get(b)
                if 有限数(ha) and ha > 0 and 有限数(hb) and hb > 0:
                    xs.append(math.log(float(ha)))
                    ys.append(math.log(float(hb)))
            out[a + "_" + b] = {"n": len(xs), "rho": 精简(spearman(xs, ys))}
    return out


def m6a_len_corr(genes):
    xs = []
    ys = []
    for g in genes.values():
        load = g.get("m6a_load")
        length = g.get("exon_length")
        if 有限数(load) and 有限数(length) and length > 0:
            xs.append(float(load))
            ys.append(float(length))
    return {"n": len(xs), "rho": 精简(spearman(xs, ys))}


def main():
    t0 = time.time()
    data_path = pathlib.Path.cwd() / DATA_REL
    checks = {
        "m6aconquer_parsed": False,
        "rnadecaycafe_parsed": False,
        "coord_overlap_join": False,
        "length_partial": False,
        "permutation": False,
        "positive_control_direction": False,
        "crossorganism_verdict": False,
    }
    cannot_claim = [
        "观测性 frozen-direction transfer(无人类 STM2457 因果臂, 是 mouse 静态臂的跨物种复制非因果)",
        "count 非 stoichiometry",
        "位点按 whole-gene-body overlap 分配(含 intron)非 exon-resolved",
        "m6A 去稳定方向是已知生物学(transfer 测的是定量保守性非新机制)",
        "m6AConquer/RNAdecayCafe 特定数据集",
        "人类 cell line 非组织",
    ]
    try:
        with data_path.open("r", encoding="utf-8") as f:
            payload = json.load(f)
    except Exception as e:
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "mouse_specific",
            "note": "无法读取 compact JSON: " + str(e),
            "result": {"cannot_claim": cannot_claim},
        }
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    meta = payload.get("meta", {})
    genes = payload.get("genes", {})
    checks["m6aconquer_parsed"] = bool(meta.get("n_sites", 0) > 0 and meta.get("headers", {}).get("m6aconquer_sites"))
    checks["rnadecaycafe_parsed"] = bool(meta.get("n_genes_model", 0) > 0 and meta.get("headers", {}).get("rnadecaycafe_halflife"))
    checks["coord_overlap_join"] = bool(len(genes) >= 1000 and meta.get("join", {}).get("n_genes_nonzero_m6a_load", 0) > 0)

    per_cell = {}
    for idx, cell in enumerate(CELL_LINES):
        per_cell[cell] = cell_stats(genes, cell, SEED + idx * 1009)
    checks["length_partial"] = all(per_cell[c]["rho_partial_len"] is not None and per_cell[c]["rho_partial_lengc"] is not None for c in CELL_LINES)
    checks["permutation"] = all(per_cell[c]["perm_done"] >= PERM_N for c in CELL_LINES)
    checks["positive_control_direction"] = bool(per_cell["HEK293"]["rho"] is not None and per_cell["HEK293"]["rho"] < 0)

    sign_concordant_n = sum(1 for c in CELL_LINES if per_cell[c]["rho_partial_lengc"] is not None and per_cell[c]["rho_partial_lengc"] < 0)
    hek = per_cell["HEK293"]
    parse_ok = all(checks[k] for k in ("m6aconquer_parsed", "rnadecaycafe_parsed", "coord_overlap_join", "length_partial", "permutation"))

    if not parse_ok:
        status = "needs_data"
        verdict = "mouse_specific"
        note = "解析或 join 不足，不能做结论性 transfer 判定。"
    else:
        status = "passed"
        if hek["rho_partial_lengc"] is not None and hek["rho_partial_lengc"] < 0 and hek["p_perm"] is not None and hek["p_perm"] < 0.01 and checks["positive_control_direction"] and sign_concordant_n >= 2:
            verdict = "transfers_conserved"
            note = "人类观测性 frozen-direction transfer 支持保守：HEK293 length+GC partial 为负且 permutation 显著，三条人类 cell line 中至少两条同为负。该臂不是人类因果扰动。"
        elif hek["rho"] is not None and hek["rho"] < 0 and (hek["rho_partial_lengc"] is None or hek["rho_partial_lengc"] >= 0 or hek["p_perm"] is None or hek["p_perm"] >= 0.01):
            verdict = "confounded"
            note = "HEK293 raw 方向为负，但 length+GC partial 后不满足显著 frozen-direction transfer，按预登记判为 confounded。该臂是观测性复制，不能声称人类因果。"
        else:
            verdict = "mouse_specific"
            note = "人类 HEK293 没有复现预登记负向 anchor 或 partial 结果近 null/不显著，按预登记判为 mouse_specific。该臂是观测性复制，不能声称人类因果。"
    checks["crossorganism_verdict"] = bool(status == "passed")

    sanity = {
        "hl_crosscell_corr": crosscell_halflife_corr(genes),
        "m6a_len_corr": m6a_len_corr(genes),
        "assigned_sites_any_gene_body": meta.get("n_sites_assigned_any_gene_body"),
        "site_gene_body_overlaps": meta.get("n_site_gene_body_overlaps"),
    }

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n_sites": meta.get("n_sites"),
            "n_genes": len(genes),
            "per_celltype": per_cell,
            "sign_concordant_n": sign_concordant_n,
            "sanity": sanity,
            "actual_perm": PERM_N,
            "runtime_sec": 精简(time.time() - t0),
            "cannot_claim": cannot_claim,
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if status == "passed":
        return 0
    if status == "needs_data":
        return 3
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

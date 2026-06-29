#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
离线实验：3D Cα 结构埋藏与长程接触次序是否预测 measured per-site folding ddG。

纯 stdlib；读 repo-relative:
tools/bio_reality/data/protein_structure_burial_folding_ddg_tsuboyama2023.json
"""

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "protein_structure_burial_folding_ddg_tsuboyama2023"
CLAIM_ID = "h3.cross_layer_relation.protein_folding_stability.structure_burial_contact_order_folding_ddg_tsuboyama2023"

DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/protein_structure_burial_folding_ddg_tsuboyama2023.json"
SEED = 82463
LAMBDA = 1.0
FOLDS = 5
B = 1000
RHO_FLOOR = 0.10
R2_FLOOR = 0.01


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


def r2_score(y, pred, baseline=None):
    if baseline is None:
        baseline = mean(y)
    sst = sum((v - baseline) * (v - baseline) for v in y)
    if sst <= 0:
        return 0.0
    sse = sum((v - p) * (v - p) for v, p in zip(y, pred))
    return 1.0 - sse / sst


def solve_linear(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            val = abs(aug[r][col])
            if val > best:
                best = val
                pivot = r
        if best < 1e-12:
            aug[col][col] += 1e-8
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pv = aug[col][col]
        for c in range(col, n + 1):
            aug[col][c] /= pv
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= factor * aug[col][c]
    return [aug[i][n] for i in range(n)]


def fit_ridge(x_rows, y, lam=LAMBDA):
    n = len(x_rows)
    p = len(x_rows[0]) if x_rows else 0
    cols = p + 1
    means = [0.0] * p
    stds = [1.0] * p
    for j in range(p):
        vals = [row[j] for row in x_rows]
        means[j] = mean(vals)
        var = variance(vals) / max(1, n - 1)
        stds[j] = math.sqrt(var) if var > 1e-18 else 1.0
    ymean = mean(y)
    xtx = [[0.0] * cols for _ in range(cols)]
    xty = [0.0] * cols
    for row, yy in zip(x_rows, y):
        z = [1.0] + [(row[j] - means[j]) / stds[j] for j in range(p)]
        yc = yy - ymean
        for i in range(cols):
            xty[i] += z[i] * yc
            zi = z[i]
            for j in range(i, cols):
                xtx[i][j] += zi * z[j]
    for i in range(cols):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    for j in range(1, cols):
        xtx[j][j] += lam
    xtx[0][0] += 1e-8
    coef = solve_linear(xtx, xty)
    return {"means": means, "stds": stds, "ymean": ymean, "coef": coef}


def predict(model, x_rows):
    p = len(model["means"])
    out = []
    for row in x_rows:
        val = model["ymean"] + model["coef"][0]
        for j in range(p):
            val += model["coef"][j + 1] * ((row[j] - model["means"][j]) / model["stds"][j])
        out.append(val)
    return out


def select_rows(rows, idxs):
    return [rows[i] for i in idxs]


def fold_indices(n):
    idx = list(range(n))
    rnd = random.Random(SEED)
    rnd.shuffle(idx)
    folds = []
    for fold in range(FOLDS):
        test = [i for pos, i in enumerate(idx) if pos % FOLDS == fold]
        train = [i for pos, i in enumerate(idx) if pos % FOLDS != fold]
        folds.append((train, test))
    return folds


def cv_predictions(x_rows, y):
    pred = [0.0] * len(y)
    for train, test in fold_indices(len(y)):
        model = fit_ridge(select_rows(x_rows, train), [y[i] for i in train])
        vals = predict(model, select_rows(x_rows, test))
        for i, p in zip(test, vals):
            pred[i] = p
    return pred


def squared_distance(a, b):
    dx = a[1] - b[1]
    dy = a[2] - b[2]
    dz = a[3] - b[3]
    return dx * dx + dy * dy + dz * dz


def ca_structure_features(ca_coords):
    out = {}
    for pdb, rows in ca_coords.items():
        coords = [(int(r[0]), float(r[1]), float(r[2]), float(r[3])) for r in rows]
        n = len(coords)
        for i, row in enumerate(coords):
            resseq = row[0]
            burial = 0
            co_sum = 0.0
            co_n = 0
            for j, other in enumerate(coords):
                if i == j:
                    continue
                d2 = squared_distance(row, other)
                gap = abs(resseq - other[0])
                if d2 <= 100.0:
                    burial += 1
                if d2 <= 64.0 and gap >= 3:
                    co_sum += gap
                    co_n += 1
            contact_order = (co_sum / co_n / n) if co_n else 0.0
            out[(pdb, resseq)] = (float(burial), float(contact_order), n)
    return out


def fast_ranked_spearman_int_x(x_by_site, site_idxs, y_rank, y_ss, max_x):
    n = len(site_idxs)
    if n <= 1 or y_ss <= 0:
        return 0.0
    counts = [0] * (max_x + 1)
    for site_i in site_idxs:
        counts[int(x_by_site[site_i])] += 1
    mids = [0.0] * (max_x + 1)
    seen = 0
    for val, count in enumerate(counts):
        if count:
            mids[val] = seen + (count + 1) / 2.0
            seen += count
    mx = (n + 1) / 2.0
    my = (n + 1) / 2.0
    sxx = 0.0
    cov = 0.0
    for k, site_i in enumerate(site_idxs):
        dx = mids[int(x_by_site[site_i])] - mx
        sxx += dx * dx
        cov += dx * (y_rank[k] - my)
    if sxx <= 0:
        return 0.0
    return cov / math.sqrt(sxx * y_ss)


def prepare_target_blocks(sites, site_pos):
    vals = {}
    idxs = {}
    for site_i, site in enumerate(sites):
        for target, ddg in site["ddg"].items():
            vals.setdefault(target, []).append(float(ddg))
            idxs.setdefault(target, []).append(site_pos[site_i])
    blocks = {}
    for target in sorted(vals):
        y = vals[target]
        yr = ranks(y)
        my = (len(y) + 1) / 2.0
        y_ss = sum((v - my) * (v - my) for v in yr)
        blocks[target] = {
            "idxs": idxs[target],
            "y": y,
            "y_rank": yr,
            "y_ss": y_ss,
            "n": len(y),
        }
    return blocks


def within_substitution_rho(x_by_site, blocks, max_x):
    total = 0
    acc = 0.0
    per_target = {}
    for target in sorted(blocks):
        block = blocks[target]
        rho = fast_ranked_spearman_int_x(
            x_by_site,
            block["idxs"],
            block["y_rank"],
            block["y_ss"],
            max_x,
        )
        n = block["n"]
        total += n
        acc += rho * n
        per_target[target] = {"n": n, "rho": rho}
    return (acc / total if total else 0.0), per_target


def residualize_against(x, z):
    mx = mean(x)
    mz = mean(z)
    szz = sum((v - mz) * (v - mz) for v in z)
    if szz <= 0:
        return [v - mx for v in x]
    slope = sum((a - mx) * (b - mz) for a, b in zip(x, z)) / szz
    intercept = mx - slope * mz
    return [a - (intercept + slope * b) for a, b in zip(x, z)]


def partial_spearman(x, y, control):
    rx = ranks(x)
    ry = ranks(y)
    rz = ranks(control)
    return pearson(residualize_against(rx, rz), residualize_against(ry, rz))


def weighted_site_cv_r2(feature_cols, y_site, weights, folds, sst_rows, within_const):
    n = len(y_site)
    p = len(feature_cols)
    pred = [0.0] * n
    for train, test in folds:
        total_w = sum(weights[i] for i in train)
        means = []
        stds = []
        for col in feature_cols:
            m = sum(weights[i] * col[i] for i in train) / total_w
            var = sum(weights[i] * (col[i] - m) * (col[i] - m) for i in train) / max(1.0, total_w - 1.0)
            means.append(m)
            stds.append(math.sqrt(var) if var > 1e-18 else 1.0)
        ymean = sum(weights[i] * y_site[i] for i in train) / total_w
        xtx = [[0.0] * p for _ in range(p)]
        xty = [0.0] * p
        for i in train:
            z = [(feature_cols[j][i] - means[j]) / stds[j] for j in range(p)]
            yc = y_site[i] - ymean
            w = weights[i]
            for a in range(p):
                za = z[a]
                xty[a] += w * za * yc
                for c in range(a, p):
                    xtx[a][c] += w * za * z[c]
        for a in range(p):
            for c in range(a):
                xtx[a][c] = xtx[c][a]
            xtx[a][a] += LAMBDA
        coef = solve_linear(xtx, xty)
        for i in test:
            val = ymean
            for j in range(p):
                val += coef[j] * ((feature_cols[j][i] - means[j]) / stds[j])
            pred[i] = val
    sse = within_const
    for i in range(n):
        err = y_site[i] - pred[i]
        sse += weights[i] * err * err
    if sst_rows <= 0:
        return 0.0
    return 1.0 - sse / sst_rows


def frontier_incr_r2(burial, contact_order, y_site, weights, folds, sst_rows, within_const):
    base = weighted_site_cv_r2([burial], y_site, weights, folds, sst_rows, within_const)
    full = weighted_site_cv_r2([burial, contact_order], y_site, weights, folds, sst_rows, within_const)
    return full - base, base, full


def permuted_features_by_domain(burial, contact_order, domain_to_idxs, rnd):
    perm_burial = burial[:]
    perm_contact_order = contact_order[:]
    for idxs in domain_to_idxs.values():
        src = idxs[:]
        rnd.shuffle(src)
        for dst_i, src_i in zip(idxs, src):
            perm_burial[dst_i] = burial[src_i]
            perm_contact_order[dst_i] = contact_order[src_i]
    return perm_burial, perm_contact_order


def permutation_p_abs(null, observed):
    ge = sum(1 for v in null if abs(v) >= abs(observed))
    return (ge + 1) / (len(null) + 1)


def permutation_p_right(null, observed):
    ge = sum(1 for v in null if v >= observed)
    return (ge + 1) / (len(null) + 1)


def frontier_verdict(incr_r2, partial_rho, pval):
    if pval < 0.01 and incr_r2 >= R2_FLOOR:
        return "crosses_boundary"
    if pval < 0.01 or abs(partial_rho) >= RHO_FLOOR:
        return "bounded_descriptor_only"
    return "null"


def failure_out(note, started=None, checks=None):
    runtime = 0.0 if started is None else time.time() - started
    out = {
        "status": "needs_data",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks if checks is not None else {"tsuboyama_parsed": False},
        "verdict": "needs_data",
        "note": note,
        "result": {
            "n": 0,
            "distinct": 0,
            "main": {},
            "posctrl": {},
            "runtime_sec": runtime,
            "cannot_claim": ["未能读取 Tsuboyama measured folding ddG compact JSON。"],
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(3)


def main():
    started = time.time()
    if not DATA_PATH.exists():
        failure_out(f"找不到数据文件: {DATA_PATH}", started)

    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    sites = payload["sites"]
    features = ca_structure_features(payload["ca_coords"])

    site_burial = []
    site_contact_order = []
    site_mean_ddg = []
    site_weights = []
    site_pos = []
    domain_to_idxs = {}
    target_sums = {}
    target_counts = {}
    all_ddg = []
    observed_sites = []

    for site in sites:
        key = (site["pdb"], int(site["pos"]))
        burial, contact_order, _domain_len = features[key]
        site_i = len(observed_sites)
        observed_sites.append(site)
        site_pos.append(site_i)
        site_burial.append(burial)
        site_contact_order.append(contact_order)
        vals = []
        for target, ddg_raw in site["ddg"].items():
            ddg = float(ddg_raw)
            vals.append(ddg)
            all_ddg.append(ddg)
            target_sums[target] = target_sums.get(target, 0.0) + ddg
            target_counts[target] = target_counts.get(target, 0) + 1
        site_mean_ddg.append(mean(vals))
        site_weights.append(len(vals))
        domain_to_idxs.setdefault(site["pdb"], []).append(site_i)

    distinct = len({round(v, 12) for v in all_ddg})
    blocks = prepare_target_blocks(observed_sites, site_pos)
    max_burial = max(int(v) for v in site_burial) if site_burial else 0

    anchor_rho = spearman(site_burial, site_mean_ddg)
    pos_reproduced = (abs(anchor_rho) >= RHO_FLOOR and distinct > 10)
    rho_within, per_target = within_substitution_rho(site_burial, blocks, max_burial)

    target_means = {target: target_sums[target] / target_counts[target] for target in target_sums}
    row_site_idx = []
    row_y_resid = []
    y_site = []
    within_const = 0.0
    y_total = 0.0
    for site_i, site in enumerate(observed_sites):
        vals = []
        for target, ddg_raw in site["ddg"].items():
            yr = float(ddg_raw) - target_means[target]
            vals.append(yr)
            row_site_idx.append(site_i)
            row_y_resid.append(yr)
            y_total += yr
        site_y = mean(vals)
        y_site.append(site_y)
        within_const += sum((v - site_y) * (v - site_y) for v in vals)
    y_global = y_total / len(row_y_resid)
    sst_rows = sum((v - y_global) * (v - y_global) for v in row_y_resid)

    folds = fold_indices(len(y_site))
    incr_r2, base_r2, full_r2 = frontier_incr_r2(
        site_burial,
        site_contact_order,
        y_site,
        site_weights,
        folds,
        sst_rows,
        within_const,
    )
    row_burial = [site_burial[i] for i in row_site_idx]
    row_contact_order = [site_contact_order[i] for i in row_site_idx]
    partial_co = partial_spearman(row_contact_order, row_y_resid, row_burial)

    rnd = random.Random(SEED + 1701)
    null_rho = []
    null_incr = []
    for _b in range(B):
        perm_burial, perm_contact_order = permuted_features_by_domain(
            site_burial,
            site_contact_order,
            domain_to_idxs,
            rnd,
        )
        perm_rho, _per_target = within_substitution_rho(perm_burial, blocks, max_burial)
        perm_incr, _perm_base, _perm_full = frontier_incr_r2(
            perm_burial,
            perm_contact_order,
            y_site,
            site_weights,
            folds,
            sst_rows,
            within_const,
        )
        null_rho.append(perm_rho)
        null_incr.append(perm_incr)

    within_p = permutation_p_abs(null_rho, rho_within)
    frontier_p = permutation_p_right(null_incr, incr_r2)
    primary_crosses = abs(rho_within) >= RHO_FLOOR and within_p < 0.01

    if not pos_reproduced or distinct <= 10:
        verdict = "needs_data"
    elif primary_crosses:
        verdict = "crosses_boundary"
    elif within_p < 0.01:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "composition_artifact"

    frontier_call = frontier_verdict(incr_r2, partial_co, frontier_p)
    contact_order_crosses = frontier_call == "crosses_boundary"
    status = "passed" if verdict != "needs_data" else "needs_data"
    checks = {
        "tsuboyama_parsed": True,
        "ddg_continuous": distinct > 10,
        "anchor_reproduced": pos_reproduced,
        "within_substitution_design": True,
        "within_domain_perm_null": len(null_rho) >= B and len(null_incr) >= B,
        "primary_crosses": primary_crosses,
        "contact_order_beyond_burial_crosses": contact_order_crosses,
        "structure_verdict": verdict,
    }

    cannot_claim = [
        "观测性关联非因果。",
        "AlphaFold 预测结构非实验晶体/NMR。",
        "burial/contact-order 为 Cα-only 粗粒度代理，非全原子 SASA/真 contact-order。",
        "ddg 来自 cDNA-display proteolysis 高通量代理，非量热。",
        "混合 designed+natural domains。",
        "within-domain 置换控 domain 混杂但不能排除位点级共变量，如二级结构类型。",
        "frontier 若 null 则不可声称拓扑超越局部埋藏。",
    ]
    note = (
        "Cα burial 在 fixed target substitution blocks 内预测 measured folding ddG；"
        "contact-order 分支用 target-demeaned site-held-out ridge 检查 CO over burial，"
        "within-domain feature permutation 保留 domain 边际并打乱 structure↔position 映射。"
    )
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(all_ddg),
            "distinct": distinct,
            "main": {
                "rho_within": rho_within,
                "within_perm_p": within_p,
                "within_perm_mean": mean(null_rho),
                "within_perm_min": min(null_rho),
                "within_perm_max": max(null_rho),
                "actual_B": len(null_rho),
                "target_blocks": len(blocks),
                "per_target": per_target,
            },
            "posctrl": {
                "rho_anchor_burial_mean_ddg": anchor_rho,
                "reproduced": pos_reproduced,
                "n_sites": len(observed_sites),
                "mean_ddg_all": mean(all_ddg),
            },
            "frontier": {
                "burial_r2_heldout": base_r2,
                "burial_contact_order_r2_heldout": full_r2,
                "incr_r2_heldout": incr_r2,
                "partial_spearman_co": partial_co,
                "perm_p": frontier_p,
                "perm_mean": mean(null_incr),
                "perm_min": min(null_incr),
                "perm_max": max(null_incr),
                "verdict": frontier_call,
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

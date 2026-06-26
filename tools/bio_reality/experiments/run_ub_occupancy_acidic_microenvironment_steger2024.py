#!/usr/bin/env python3
# 中文说明：纯 stdlib 离线实验。读 repo-relative data JSON，不做网络、不调用外部程序。

import json
import math
import random
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "ub_occupancy_acidic_microenvironment_steger2024"
CLAIM_ID = "h3.cross_layer_relation.ubiquitylation_occupancy.ub_occupancy_acidic_microenvironment_steger2024"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/ub_occupancy_acidic_microenvironment_steger2024.json"
AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"
HIGH_OCC = 0.005
PERM_B = 2000
SEED = 20240622


def finite(x):
    return x is not None and isinstance(x, (int, float)) and math.isfinite(x)


def rankdata(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    ranks = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        vi = values[order[i]]
        while j < len(order) and values[order[j]] == vi:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


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
    return pearson(rankdata(x), rankdata(y))


def gaussian_solve(a, b):
    n = len(b)
    m = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = col
        best = abs(m[col][col])
        for r in range(col + 1, n):
            v = abs(m[r][col])
            if v > best:
                best = v
                pivot = r
        if pivot != col:
            m[col], m[pivot] = m[pivot], m[col]
        if abs(m[col][col]) < 1e-12:
            m[col][col] = 1e-12 if m[col][col] >= 0 else -1e-12
        pv = m[col][col]
        for c in range(col, n + 1):
            m[col][c] /= pv
        for r in range(n):
            if r == col:
                continue
            f = m[r][col]
            if f == 0.0:
                continue
            for c in range(col, n + 1):
                m[r][c] -= f * m[col][c]
    return [m[i][n] for i in range(n)]


def residualize(y, xrows):
    n = len(y)
    p = len(xrows[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yy in zip(xrows, y):
        for i in range(p):
            xi = row[i]
            xty[i] += xi * yy
            for j in range(i, p):
                xtx[i][j] += xi * row[j]
    for i in range(p):
        xtx[i][i] += 1e-10
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    beta = gaussian_solve(xtx, xty)
    out = []
    for row, yy in zip(xrows, y):
        pred = sum(beta[i] * row[i] for i in range(p))
        out.append(yy - pred)
    return out


def log_cov(v):
    if not finite(v) or v <= 0:
        return None
    return math.log(v)


def covariate_row(site):
    lc = log_cov(site.get("copy_number"))
    li = log_cov(site.get("ibaq"))
    length = site.get("length")
    comp = site.get("aa_comp_win")
    if lc is None or li is None or not finite(length) or not isinstance(comp, list) or len(comp) != 20:
        return None
    # 19 个独立 AA 组成比例；T 作为 baseline，否则 20 比例 + 截距完全共线。
    comp19 = [float(comp[i]) for i, aa in enumerate(AA_ORDER) if aa != "T"]
    return [1.0, lc, li, math.log(float(length))] + comp19


def perm_p_from_centered(rx, ry, obs, b, seed):
    rng = random.Random(seed)
    n = len(rx)
    base = ry[:]
    sx = sum(v * v for v in rx)
    sy = sum(v * v for v in ry)
    denom = math.sqrt(sx * sy) if sx > 0 and sy > 0 else 1.0
    extreme = 1
    for _ in range(b):
        rng.shuffle(base)
        dot = 0.0
        for a, c in zip(rx, base):
            dot += a * c
        stat = dot / denom
        if abs(stat) >= abs(obs) - 1e-15:
            extreme += 1
    return extreme / (b + 1)


def partial_spearman_with_perm(rows):
    y = [float(s["occupancy"]) for s, _ in rows]
    x = [float(s["acidic_pm7"]) for s, _ in rows]
    cov = [r for _, r in rows]
    ry_raw = residualize(y, cov)
    rx_raw = residualize(x, cov)
    ry = rankdata(ry_raw)
    rx = rankdata(rx_raw)
    mx = sum(rx) / len(rx)
    my = sum(ry) / len(ry)
    rxc = [v - mx for v in rx]
    ryc = [v - my for v in ry]
    obs = pearson(rx, ry)
    p = perm_p_from_centered(rxc, ryc, obs, PERM_B, SEED + 1)
    return obs, p, len(rows)


def abundance_corr(sites):
    occ_copy = []
    occ_ibaq = []
    for s in sites:
        yval = s.get("occupancy")
        lc = log_cov(s.get("copy_number"))
        li = log_cov(s.get("ibaq"))
        if finite(yval) and lc is not None:
            occ_copy.append((float(yval), lc))
        if finite(yval) and li is not None:
            occ_ibaq.append((float(yval), li))
    return {
        "spearman_occ_log_copy_number": spearman([a for a, _ in occ_copy], [b for _, b in occ_copy]) if len(occ_copy) >= 3 else None,
        "n_copy": len(occ_copy),
        "spearman_occ_log_iBAQ": spearman([a for a, _ in occ_ibaq], [b for _, b in occ_ibaq]) if len(occ_ibaq) >= 3 else None,
        "n_iBAQ": len(occ_ibaq),
    }


def positive_control(sites):
    usable = [s for s in sites if finite(s.get("occupancy")) and s.get("gene")]
    high = [s for s in usable if float(s["occupancy"]) > HIGH_OCC]
    low = [s for s in usable if float(s["occupancy"]) <= HIGH_OCC]
    labels = [1] * len(high) + [0] * len(low)
    slc = [1 if str(s.get("gene", "")).upper().startswith("SLC") else 0 for s in high + low]
    if not high or not low:
        return {"ok": False, "reason": "高/低占据组为空"}
    obs = sum(slc[:len(high)]) / len(high) - sum(slc[len(high):]) / len(low)
    rng = random.Random(SEED + 2)
    n_high = len(high)
    total_slc = sum(slc)
    extreme = 1
    for _ in range(PERM_B):
        rng.shuffle(labels)
        high_slc = 0
        for lab, val in zip(labels, slc):
            if lab:
                high_slc += val
        low_slc = total_slc - high_slc
        stat = high_slc / n_high - low_slc / (len(slc) - n_high)
        if stat >= obs - 1e-15:
            extreme += 1
    p = extreme / (PERM_B + 1)
    return {
        "ok": p < 0.01 and obs > 0,
        "threshold_high_occupancy": HIGH_OCC,
        "n_high": len(high),
        "n_low": len(low),
        "slc_prop_high": sum(slc[:len(high)]) / len(high),
        "slc_prop_low": sum(slc[len(high):]) / len(low),
        "diff": obs,
        "p": p,
    }


def comp_distance(a, b):
    return sum((float(x) - float(y)) ** 2 for x, y in zip(a, b))


def within_protein_null(sites):
    by_prot = {}
    for s in sites:
        if finite(s.get("occupancy")) and isinstance(s.get("aa_comp_win"), list):
            by_prot.setdefault(s["uniprot"], []).append(s)
    diffs = []
    for plist in by_prot.values():
        if len(plist) < 2:
            continue
        highs = [s for s in plist if float(s["occupancy"]) > HIGH_OCC]
        controls = [s for s in plist if float(s["occupancy"]) <= HIGH_OCC]
        if not highs or not controls:
            continue
        used = set()
        for h in sorted(highs, key=lambda z: (-float(z["occupancy"]), z["pos"])):
            best = None
            best_key = None
            for c in controls:
                key_id = id(c)
                if key_id in used and len(controls) >= len(highs):
                    continue
                d = comp_distance(h["aa_comp_win"], c["aa_comp_win"])
                key = (d, abs(int(h["pos"]) - int(c["pos"])), int(c["pos"]))
                if best_key is None or key < best_key:
                    best_key = key
                    best = c
            if best is not None:
                used.add(id(best))
                diffs.append(float(h["acidic_pm7"]) - float(best["acidic_pm7"]))
    if not diffs:
        return {"ok": False, "reason": "无同蛋白高/低占据匹配对", "n_pairs": 0}
    obs = sum(diffs) / len(diffs)
    rng = random.Random(SEED + 3)
    extreme = 1
    for _ in range(PERM_B):
        stat = 0.0
        for d in diffs:
            stat += d if rng.random() < 0.5 else -d
        stat /= len(diffs)
        if abs(stat) >= abs(obs) - 1e-15:
            extreme += 1
    p = extreme / (PERM_B + 1)
    return {
        "ok": p < 0.01 and obs > 0,
        "method": "same-protein measured Ub-site nearest 20AA-composition low-occupancy control; paired sign-flip null",
        "n_pairs": len(diffs),
        "mean_acidic_high_minus_matched_low": obs,
        "p": p,
    }


def held_out_by_protein(sites):
    left_x = []
    left_y = []
    right_x = []
    right_y = []
    for s in sites:
        if not finite(s.get("occupancy")) or not finite(s.get("acidic_pm7")):
            continue
        # 稳定、无需 hash 随机盐的蛋白分割。
        bucket = sum(ord(ch) for ch in s["uniprot"]) % 2
        if bucket == 0:
            left_x.append(float(s["acidic_pm7"]))
            left_y.append(float(s["occupancy"]))
        else:
            right_x.append(float(s["acidic_pm7"]))
            right_y.append(float(s["occupancy"]))
    return {
        "split": "sum(ord(uniprot)) parity",
        "rho_even": spearman(left_x, left_y) if len(left_x) >= 3 else None,
        "n_even": len(left_x),
        "rho_odd": spearman(right_x, right_y) if len(right_x) >= 3 else None,
        "n_odd": len(right_x),
    }


def fmt(x):
    if x is None:
        return None
    if isinstance(x, float):
        return float(f"{x:.6g}")
    return x


def main():
    t0 = time.time()
    checks = {
        "xlsx_parsed": False,
        "uniprot_joined": False,
        "acidic_env_computed": False,
        "abundance_composition_controlled": False,
        "within_protein_null": False,
        "positive_control": False,
        "ub_occupancy_verdict": False,
    }
    cannot_claim = [
        "occupancy≠泛素化速率/通量(稳态占据)",
        "acceptor-site motif 本就弱→先验 predictor 站不住就 composition_artifact 别救",
        "观测性非因果",
        "丰度控用 copy_number/iBAQ 仍可能残留",
        "±7 窗局部近似",
        "单一 HeLa 数据集",
        "predictor 先验固定防事后分隔",
    ]
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        meta = data.get("meta", {})
        sites = data.get("sites", [])
        checks["xlsx_parsed"] = len(sites) > 10000 and meta.get("raw_measured_sites", 0) > 10000
        checks["uniprot_joined"] = meta.get("n_prots", 0) > 2500 and meta.get("bad_position_or_not_K", 999999) < 200
        checks["acidic_env_computed"] = all("acidic_pm7" in s and "aa_comp_win" in s for s in sites[:100]) and len(sites) > 10000

        x = [float(s["acidic_pm7"]) for s in sites if finite(s.get("acidic_pm7")) and finite(s.get("occupancy"))]
        y = [float(s["occupancy"]) for s in sites if finite(s.get("acidic_pm7")) and finite(s.get("occupancy"))]
        main_rho = spearman(x, y)

        rows = []
        for s in sites:
            r = covariate_row(s)
            if r is not None and finite(s.get("occupancy")) and finite(s.get("acidic_pm7")):
                rows.append((s, r))
        prho, pp, pn = partial_spearman_with_perm(rows)
        checks["abundance_composition_controlled"] = pn > 5000 and pp is not None

        wnull = within_protein_null(sites)
        checks["within_protein_null"] = bool(wnull.get("n_pairs", 0) > 100)

        pos = positive_control(sites)
        checks["positive_control"] = bool(pos.get("ok"))
        abund = abundance_corr(sites)
        held = held_out_by_protein(sites)

        if not checks["positive_control"] or not checks["xlsx_parsed"] or not checks["uniprot_joined"]:
            status = "needs_data"
            verdict = "composition_artifact"
            note = "正对照或数据 join 自检未通过，按预注册规则不下主判。"
            exit_code = 3
        else:
            status = "passed"
            if pp < 0.01 and wnull.get("ok"):
                # 酸性组成是低维 descriptor；Spearman^2 仅作保守效应量尺度。
                if prho * prho < 0.02:
                    verdict = "bounded_descriptor_only"
                    note = "酸性微环境在丰度+组成控制及蛋白内匹配后仍有统计信号，但效应量很小；只能作为有界描述符。"
                else:
                    verdict = "crosses_boundary"
                    note = "酸性微环境在丰度+组成控制及蛋白内匹配后仍预测 measured occupancy，且 SLC 正对照复现；观测性、非速率结论。"
            elif pp < 0.01 and not wnull.get("ok"):
                verdict = "composition_artifact"
                note = "主 partial 信号存在，但蛋白内组成匹配后未存活，按预注册规则归为 composition_artifact。"
            else:
                verdict = "composition_artifact"
                note = "酸性微环境未在丰度+局部组成控制后形成稳健预测，按预注册规则归为 composition_artifact。"
            checks["ub_occupancy_verdict"] = True
            exit_code = 0

        # 为满足连跑 stdout bit-identical，runtime_sec 不使用墙钟；实际墙钟由外部 time 自验记录。
        runtime_sec = 0.0
        result = {
            "n_sites": len(sites),
            "n_prots": len({s["uniprot"] for s in sites}),
            "main": {"rho": fmt(main_rho), "predictor": "acidic_pm7"},
            "partial": {
                "rho": fmt(prho),
                "p": fmt(pp),
                "n": pn,
                "covariates": "log(copy_number)+log(iBAQ)+log(protein_length)+19 independent +/-7 AA composition fractions (T baseline)",
            },
            "within_protein_null": {k: fmt(v) for k, v in wnull.items()},
            "posctrl": {
                "pm_slc_high_vs_low": {k: fmt(v) for k, v in pos.items()},
                "occ_abundance_corr": {k: fmt(v) for k, v in abund.items()},
            },
            "held_out": {k: fmt(v) for k, v in held.items()},
            "actual_perm": PERM_B,
            "runtime_sec": runtime_sec,
            "runtime_note": "stdout deterministic; wall time measured by harness",
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
        return exit_code
    except Exception as e:
        out = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": "实验脚本异常: " + repr(e),
            "result": {
                "n_sites": 0,
                "n_prots": 0,
                "main": {"rho": None},
                "partial": {"rho": None, "p": None, "covariates": None},
                "within_protein_null": {},
                "posctrl": {},
                "held_out": None,
                "actual_perm": 0,
                "runtime_sec": float(f"{time.time() - t0:.6g}"),
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 1


if __name__ == "__main__":
    sys.exit(main())

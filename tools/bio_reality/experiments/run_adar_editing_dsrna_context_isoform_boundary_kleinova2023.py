#!/usr/bin/env python3
# 中文；纯 stdlib 离线实验。读 repo-relative data JSON。
import collections
import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "adar_editing_dsrna_context_isoform_boundary_kleinova2023"
CLAIM_ID = "h3.cross_layer_relation.rna_editing.adar_editing_dsrna_context_isoform_boundary_kleinova2023"
DATA = pathlib.Path.cwd() / "tools/bio_reality/data/adar_editing_dsrna_context_kleinova2023.json"
SEED = 20260622
B = 1200


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and xs[order[j]] == xs[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = r
        i = j
    return out


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx = mean(x)
    my = mean(y)
    vx = sum((a - mx) ** 2 for a in x)
    vy = sum((b - my) ** 2 for b in y)
    if vx <= 0 or vy <= 0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(vx * vy)


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def gc_bin(gc):
    if gc < 0.35:
        return "gc0"
    if gc < 0.45:
        return "gc1"
    if gc < 0.55:
        return "gc2"
    return "gc3"


def permute_within_strata(values, strata, rng):
    by = collections.defaultdict(list)
    for i, s in enumerate(strata):
        by[s].append(i)
    out = list(values)
    for idxs in by.values():
        vals = [out[i] for i in idxs]
        rng.shuffle(vals)
        for i, v in zip(idxs, vals):
            out[i] = v
    return out


def strat_spearman_perm(rows, repetition, ykey, rng):
    sub = [r for r in rows if r["repetition"] == repetition and r.get(ykey) is not None]
    x = [r["dsrna_score"] for r in sub]
    y = [r[ykey] for r in sub]
    strata = [(r["repetition"], gc_bin(r["local_gc"])) for r in sub]
    obs = spearman(x, y)
    ge = 1
    for _ in range(B):
        yp = permute_within_strata(y, strata, rng)
        if spearman(x, yp) >= obs:
            ge += 1
    p = ge / (B + 1)
    return {"rho": obs, "p_perm": p, "n": len(sub)}


def fraction_five_g(rows):
    return sum(1 for r in rows if r["five_prime_nt"] == "G") / len(rows)


def five_g_perm(rows, rng):
    # 正对照：REP 层 5'-G 比例低于 25% 基因组 A 上游基线。用二项式/置换等价模拟基线标签。
    rep = [r for r in rows if r["repetition"] == "REP"]
    obs = sum(1 for r in rep if r["five_prime_nt"] == "G")
    n = len(rep)
    ge_low = 1
    for _ in range(B):
        sim = sum(1 for _ in range(n) if rng.random() < 0.25)
        if sim <= obs:
            ge_low += 1
    return obs / n, 0.25, ge_low / (B + 1), n


def rep_vs_nonrep_edit(rows, rng):
    # sanity：REP/SINE 等重复来源的 editing rate 高于 NONREP；响应取 p150/p110 两 isoform 平均。
    vals = []
    labels = []
    for r in rows:
        if r["repetition"] in ("REP", "NONREP"):
            vals.append((r["ratio_p150"] + r["ratio_p110"]) / 2.0)
            labels.append(r["repetition"])
    rep_vals = [v for v, lab in zip(vals, labels) if lab == "REP"]
    non_vals = [v for v, lab in zip(vals, labels) if lab == "NONREP"]
    obs = mean(rep_vals) - mean(non_vals)
    n_rep = len(rep_vals)
    ge = 1
    idxs = list(range(len(vals)))
    for _ in range(B):
        rng.shuffle(idxs)
        rep_idx = set(idxs[:n_rep])
        a = [vals[i] for i in range(len(vals)) if i in rep_idx]
        b = [vals[i] for i in range(len(vals)) if i not in rep_idx]
        if mean(a) - mean(b) >= obs:
            ge += 1
    return {"rep_mean": mean(rep_vals), "nonrep_mean": mean(non_vals), "delta": obs, "p": ge / (B + 1)}


def isoform_did(rows, rng):
    p150 = [r for r in rows if r["editedby"] == "p150"]
    p110 = [r for r in rows if r["editedby"] == "p110"]
    both = [r for r in rows if r["editedby"] == "both"]
    m150 = mean([r["dsrna_score"] for r in p150])
    m110 = mean([r["dsrna_score"] for r in p110])
    mboth = mean([r["dsrna_score"] for r in both])
    obs = m150 - m110
    vals = [r["dsrna_score"] for r in p150 + p110]
    labels = ["p150"] * len(p150) + ["p110"] * len(p110)
    n150 = len(p150)
    ge = 1
    idxs = list(range(len(vals)))
    for _ in range(B):
        rng.shuffle(idxs)
        a_idx = set(idxs[:n150])
        a = [vals[i] for i in range(len(vals)) if i in a_idx]
        b = [vals[i] for i in range(len(vals)) if i not in a_idx]
        if mean(a) - mean(b) >= obs:
            ge += 1
    return {
        "p150_dsrna_mean": m150,
        "p110_dsrna_mean": m110,
        "both_dsrna_mean": mboth,
        "delta": obs,
        "p": ge / (B + 1),
        "n_p150": len(p150),
        "n_p110": len(p110),
        "n_both": len(both),
    }


def round_obj(x):
    if isinstance(x, float):
        if math.isnan(x) or math.isinf(x):
            return None
        return float("%.6g" % x)
    if isinstance(x, dict):
        return {k: round_obj(v) for k, v in x.items()}
    if isinstance(x, list):
        return [round_obj(v) for v in x]
    return x


def main():
    t0 = time.time()
    checks = {
        "editome_parsed": False,
        "mm10_fetched": False,
        "features_computed": False,
        "dsrna_stratified": False,
        "isoform_did": False,
        "positive_control": False,
        "editing_verdict": False,
    }
    rng = random.Random(SEED)
    if not DATA.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "REFUTED",
            "note": "找不到 compact JSON: %s" % DATA,
            "result": {"cannot_claim": cannot_claim()},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True))
        return 3
    data = json.loads(DATA.read_text())
    rows = data.get("sites", [])
    for r in rows:
        r["edit_mean"] = (r["ratio_p150"] + r["ratio_p110"]) / 2.0
    checks["editome_parsed"] = len(rows) >= 3000
    center = data.get("meta", {}).get("center_base_after_strand_correction", {})
    checks["mm10_fetched"] = len(rows) >= 3000 and (center.get("A", 0) + center.get("a", 0) >= int(0.95 * len(rows)))
    checks["features_computed"] = all(
        ("five_prime_nt" in r and "dsrna_score" in r and "local_gc" in r) for r in rows
    )
    ds = {
        "REP": strat_spearman_perm(rows, "REP", "edit_mean", rng),
        "NONREP": strat_spearman_perm(rows, "NONREP", "edit_mean", rng),
    }
    checks["dsrna_stratified"] = True
    did = isoform_did(rows, rng)
    checks["isoform_did"] = True
    five_frac, base_frac, five_p, five_n = five_g_perm(rows, rng)
    rep_non = rep_vs_nonrep_edit(rows, rng)
    pos_ok = five_p < 0.01 and rep_non["delta"] > 0
    checks["positive_control"] = pos_ok

    ds_ok = (
        ds["REP"]["rho"] > 0
        and ds["REP"]["p_perm"] < 0.01
        and ds["NONREP"]["rho"] > 0
        and ds["NONREP"]["p_perm"] < 0.01
    )
    did_ok = did["delta"] > 0 and did["p"] < 0.05
    if not pos_ok:
        status = "needs_data"
        verdict = "REFUTED"
        note = "正对照未通过，不能解释主检验；优先怀疑坐标/strand/解析或该表子集不支持锚点。"
    elif ds_ok and did_ok:
        status = "passed"
        verdict = "CROSSES"
        note = "5'-G 耗竭锚点通过，dsRNA proxy 在 REP/NONREP 且 GC 分层置换下仍正相关，p150-specific 的 dsRNA-score 高于 p110-specific；支持序列 context 越过 readback 边界并出现 isoform 遗传 DiD。"
    elif ds_ok:
        status = "passed"
        verdict = "BOUNDARY-LOCAL"
        note = "5'-G 耗竭锚点通过，dsRNA proxy 在分层内预测 editing level，但 isoform DiD 未达预登记阈值；支持局部序列 context 预测，不支持 isoform 差异。"
    else:
        status = "passed"
        verdict = "REFUTED"
        note = "5'-G 正对照通过，但 dsRNA-score 与 editing level 的正相关在 repeat-class + GC 分层置换后未达到预登记阈值；不能声称跨过该 reality boundary。"
    checks["editing_verdict"] = status == "passed"

    result = {
        "n_sites": len(rows),
        "dsrna_strat": ds,
        "isoform_did": did,
        "posctrl": {
            "five_g_frac": five_frac,
            "baseline_g_frac": base_frac,
            "p": five_p,
            "n_rep": five_n,
            "rep_vs_nonrep_edit": rep_non,
        },
        "actual_perm": B,
        "runtime_sec": time.time() - t0,
        "cannot_claim": cannot_claim(),
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
    print(json.dumps(round_obj(out), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 0 if status == "passed" else 3


def cannot_claim():
    return [
        "predictor 从 mm10 基因组算非 read counts(防 leakage)",
        "单一 mouse-MEF transfection 系统(ADAR-null 重构, 过表达, 非生理), n=3 reps",
        "dsRNA-score 是 local-window proxy(无真热力学 fold/trans-pairing), 故 null 不否定 dsRNA 依赖一般性",
        "editing level 饱和/bounded heteroscedastic(用 rank)",
        "不跨人类/物种泛化",
        "~3137 sites",
    ]


if __name__ == "__main__":
    sys.exit(main())

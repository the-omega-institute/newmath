#!/usr/bin/env python3
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "utr5_features_ribosome_load_sample2019"
CLAIM_ID = "h3.cross_layer_relation.translation_initiation.utr5_features_ribosome_load_sample2019"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/utr5_features_ribosome_load_sample2019.json"
SEED = 20260622
PERM_B = 1000


def round_sig(x, sig=6):
    if x is None:
        return None
    if isinstance(x, int):
        return x
    if x == 0 or not math.isfinite(x):
        return x
    return float(("{:." + str(sig) + "g}").format(x))


def mean(xs):
    return statistics.fmean(xs) if xs else float("nan")


def rankdata(xs):
    n = len(xs)
    order = sorted(range(n), key=xs.__getitem__)
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i + 1
        val = xs[order[i]]
        while j < n and xs[order[j]] == val:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = rank
        i = j
    return ranks


def centered(xs):
    m = mean(xs)
    return [x - m for x in xs]


def corr_from_centered(xc, yc):
    sxy = 0.0
    sx = 0.0
    sy = 0.0
    for x, y in zip(xc, yc):
        sxy += x * y
        sx += x * x
        sy += y * y
    if sx <= 0.0 or sy <= 0.0:
        return float("nan")
    return sxy / math.sqrt(sx * sy)


def spearman(x, y):
    return corr_from_centered(centered(rankdata(x)), centered(rankdata(y)))


def residualize_on_one(v, z):
    mv = mean(v)
    mz = mean(z)
    cov = 0.0
    varz = 0.0
    for vi, zi in zip(v, z):
        dz = zi - mz
        cov += (vi - mv) * dz
        varz += dz * dz
    if varz <= 0.0:
        return [vi - mv for vi in v]
    beta = cov / varz
    alpha = mv - beta * mz
    return [vi - alpha - beta * zi for vi, zi in zip(v, z)]


def partial_spearman_gc(x, y, gc):
    rx = rankdata(x)
    ry = rankdata(y)
    rg = rankdata(gc)
    ex = residualize_on_one(rx, rg)
    ey = residualize_on_one(ry, rg)
    return corr_from_centered(ex, ey), ex, ey


def permutation_p_from_residuals(ex, ey, obs, b, rng):
    denom_x = 0.0
    denom_y = 0.0
    for x in ex:
        denom_x += x * x
    for y in ey:
        denom_y += y * y
    denom = math.sqrt(denom_x * denom_y)
    if denom <= 0.0 or not math.isfinite(obs):
        return {"p": 1.0, "null95": [None, None], "actual_B": 0}
    work = list(ey)
    hits = 0
    vals = []
    abs_obs = abs(obs)
    for _ in range(b):
        rng.shuffle(work)
        dot = 0.0
        for x, y in zip(ex, work):
            dot += x * y
        val = dot / denom
        vals.append(val)
        if abs(val) >= abs_obs:
            hits += 1
    vals = sorted(vals)
    lo = vals[int(0.025 * b)]
    hi = vals[int(0.975 * b)]
    return {"p": (hits + 1) / (b + 1), "null95": [lo, hi], "actual_B": b}


def permutation_p_delta(y, group, obs, b, rng):
    n0 = sum(1 for g in group if not g)
    if n0 == 0 or n0 == len(group):
        return 1.0
    work = list(y)
    hits = 0
    abs_obs = abs(obs)
    for _ in range(b):
        rng.shuffle(work)
        m0 = mean(work[:n0])
        m1 = mean(work[n0:])
        if abs(m0 - m1) >= abs_obs:
            hits += 1
    return (hits + 1) / (b + 1)


def select(records, mask):
    return [rec for rec, keep in zip(records, mask) if keep]


def vectors(records):
    y = [float(rec["r"]) for rec in records]
    gc = [float(rec["g"]) for rec in records]
    main_score = [
        0.25 * float(rec["k"])
        - 1.25 * float(rec["a"])
        - 0.75 * float(rec["uk"])
        - 0.10 * float(rec["s"])
        + 0.05 * float(rec.get("mo", 0))
        for rec in records
    ]
    kozak_struct = [
        0.25 * float(rec["k"]) - 0.10 * float(rec["s"]) + 0.05 * float(rec.get("mo", 0))
        for rec in records
    ]
    uaug = [int(rec["a"]) > 0 for rec in records]
    return y, gc, main_score, kozak_struct, uaug


def main():
    started = time.time()
    checks = {
        "csv_parsed": "fail",
        "features_computed": "fail",
        "composition_controlled": "fail",
        "uaug_free_subset_test": "fail",
        "permutation": "fail",
        "positive_control": "fail",
        "translation_verdict": "fail",
    }

    try:
        payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        records = payload["seqs"]
        meta = payload.get("meta", {})
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": "无法读取离线 JSON: " + str(exc),
            "result": {"n": 0, "cannot_claim": []},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(3)

    n = len(records)
    checks["csv_parsed"] = "pass" if n > 0 and meta.get("n_total_reads_ge_100", 0) >= n else "fail"
    needed = {"r", "a", "k", "uk", "s", "g"}
    feature_ok = n > 0 and all(needed.issubset(rec.keys()) for rec in records[: min(100, n)])
    checks["features_computed"] = "pass" if feature_ok else "fail"

    y, gc, main_score, kozak_struct, uaug = vectors(records)
    rng = random.Random(SEED)

    no_uaug_y = [v for v, has in zip(y, uaug) if not has]
    yes_uaug_y = [v for v, has in zip(y, uaug) if has]
    delta = mean(no_uaug_y) - mean(yes_uaug_y)
    pos_p = permutation_p_delta(y, uaug, delta, PERM_B, rng)
    pos_ok = len(no_uaug_y) > 20 and len(yes_uaug_y) > 20 and delta > 1.0 and pos_p < 0.01
    checks["positive_control"] = "pass" if pos_ok else "fail"

    rho = spearman(main_score, y)
    partial, ex, ey = partial_spearman_gc(main_score, y, gc)
    main_perm = permutation_p_from_residuals(ex, ey, partial, PERM_B, rng)
    checks["composition_controlled"] = "pass" if main_perm["p"] < 0.01 else "fail"
    checks["permutation"] = "pass" if main_perm["actual_B"] >= 1000 else "fail"

    ufree_records = select(records, [not z for z in uaug])
    uy, ugc, _umain, ukozak_struct, _uuaug = vectors(ufree_records)
    if len(ufree_records) >= 100:
        ufree_partial, uex, uey = partial_spearman_gc(ukozak_struct, uy, ugc)
        ufree_perm = permutation_p_from_residuals(uex, uey, ufree_partial, PERM_B, rng)
    else:
        ufree_partial = float("nan")
        ufree_perm = {"p": 1.0, "null95": [None, None], "actual_B": 0}
    checks["uaug_free_subset_test"] = "pass" if ufree_perm["p"] < 0.01 else "fail"

    even_records = records[::2]
    odd_records = records[1::2]
    ey0, eg0, em0, _eks0, _eu0 = vectors(even_records)
    oy0, og0, om0, _oks0, _ou0 = vectors(odd_records)
    even_partial = partial_spearman_gc(em0, ey0, eg0)[0] if even_records else float("nan")
    odd_partial = partial_spearman_gc(om0, oy0, og0)[0] if odd_records else float("nan")
    heldout_same_sign = (
        math.isfinite(even_partial)
        and math.isfinite(odd_partial)
        and even_partial * odd_partial > 0
    )

    if not pos_ok:
        status = "needs_data"
        verdict = "composition_artifact"
        note = "uAUG 正对照未复现，按预登记视为解析或数据问题。"
    elif main_perm["p"] >= 0.01:
        status = "passed"
        verdict = "composition_artifact"
        note = "主特征在 GC 残差化后未越过 permutation 阈值，不能声称超成分预测。"
    elif ufree_perm["p"] >= 0.01:
        status = "passed"
        verdict = "bounded_descriptor_only"
        note = "全体样本存在 GC 控后信号，但 uAUG-free 子集中 Kozak/结构增量未通过阈值，主要边界信号受 uAUG 描述限制。"
    elif abs(ufree_partial) < 0.02:
        status = "passed"
        verdict = "bounded_descriptor_only"
        note = "uAUG-free 子集增量达到 permutation 阈值，但效应极小，按有界描述处理。"
    else:
        status = "passed"
        verdict = "crosses_boundary"
        note = "5UTR 先验特征在 GC 控后预测 measured MRL，且 uAUG-free 子集中 Kozak/结构 proxy 仍有增量；这是合成 reporter MPRA 的观测性结果。"

    checks["translation_verdict"] = "pass" if status == "passed" else "fail"

    result = {
        "n": n,
        "main": {
            "rho": round_sig(rho),
            "partial_rho_gc_controlled": round_sig(partial),
            "p": round_sig(main_perm["p"]),
        },
        "uaug_free_subset": {
            "n": len(ufree_records),
            "kozak_struct_increment": round_sig(ufree_partial),
            "p": round_sig(ufree_perm["p"]),
        },
        "perm_null": {
            "rho_obs": round_sig(partial),
            "null95": [round_sig(x) for x in main_perm["null95"]],
            "p": round_sig(main_perm["p"]),
            "actual_B": main_perm["actual_B"],
        },
        "posctrl": {
            "uaug_vs_no_mrl_delta": round_sig(delta),
            "mean_no_uaug": round_sig(mean(no_uaug_y)),
            "mean_has_uaug": round_sig(mean(yes_uaug_y)),
            "n_no_uaug": len(no_uaug_y),
            "n_has_uaug": len(yes_uaug_y),
            "p": round_sig(pos_p),
        },
        "cross_sample": None,
        "heldout_split": {
            "even_partial": round_sig(even_partial),
            "odd_partial": round_sig(odd_partial),
            "same_sign": heldout_same_sign,
        },
        "runtime_sec": round_sig(time.time() - started),
        "cannot_claim": [
            "合成随机 5'UTR 非内源，可能不覆盖内源 context",
            "eGFP 报告基因上下文",
            "MRL 是 polysome-fraction 估计",
            "结构 proxy 是 stdlib 启发式非真 MFE",
            "观测性非因果",
            "单细胞系/单实验",
            "Kozak/uORF 先验定义",
        ],
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
    sys.exit(0 if status == "passed" else 3)


if __name__ == "__main__":
    main()

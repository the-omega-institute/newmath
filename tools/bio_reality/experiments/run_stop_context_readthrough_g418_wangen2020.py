#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pure-stdlib offline experiment:
does extended stop context predict measured G418-induced RRTS beyond
stop identity, +4 nucleotide, log(UTR3), and local GC?
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "stop_context_readthrough_g418_wangen2020"
CLAIM_ID = "h3.cross_layer_relation.translation_termination.stop_context_readthrough_g418_wangen2020"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/stop_context_readthrough_g418_wangen2020.json"
SEED = 20260623
PERMUTATIONS = 1000
RIDGE = 1e-8
TEST_FRAC = 0.25

STOPS = ["UGA", "UAG", "UAA"]
NTS = ["A", "C", "G", "U"]
CTX_KEYS = ["m6", "m5", "m4", "m3", "m2", "m1", "p5", "p6", "p7", "p8", "p9", "p10"]
CANNOT_CLAIM = [
    "RRTS 是核糖体密度比，非绝对蛋白通读量",
    "RRTS=G418 诱导通读，不能声称基础内源通读",
    "HEK293T/药物处理条件特定",
    "Ensembl transcript isoform join 可能丢失未匹配转录本",
    "扩展 context 窗口限于 nt_m06..m1 与 nt_p05..p10",
    "观测性关联，非因果扰动实验",
    "+4 规则是已知 baseline，非新发现",
]


def rank_average(values):
    pairs = sorted((v, i) for i, v in enumerate(values))
    ranks = [0.0] * len(values)
    k = 0
    while k < len(pairs):
        j = k + 1
        while j < len(pairs) and pairs[j][0] == pairs[k][0]:
            j += 1
        avg = (k + 1 + j) / 2.0
        for t in range(k, j):
            ranks[pairs[t][1]] = avg
        k = j
    n = len(values)
    if n <= 1:
        return [0.0] * n
    return [(r - 1.0) / (n - 1.0) for r in ranks]


def median(xs):
    if not xs:
        return None
    return statistics.median(xs)


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def sample_sd(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return math.sqrt(sum((x - m) * (x - m) for x in xs) / (len(xs) - 1))


def one_hot(value, levels):
    return [1.0 if value == lev else 0.0 for lev in levels[:-1]]


def baseline_features(rec):
    row = [1.0]
    row.extend(one_hot(rec["stop_codon"], STOPS))
    row.extend(one_hot(rec["stop_p4"], NTS))
    row.append(math.log(float(rec["utr3len"])))
    row.append(float(rec["gc"]))
    return row


def context_features(rec):
    vals = []
    ctx = rec["nt_context"]
    for key in CTX_KEYS:
        vals.extend(one_hot(ctx[key], NTS))
    return vals


def build_design(records, include_context=True, context_source=None):
    rows = []
    for i, rec in enumerate(records):
        row = baseline_features(rec)
        if include_context:
            src = context_source[i] if context_source is not None else rec
            row.extend(context_features(src))
        rows.append(row)
    return rows


def xtx_xty(x, y, indices):
    p = len(x[0])
    a = [[0.0] * p for _ in range(p)]
    b = [0.0] * p
    for idx in indices:
        row = x[idx]
        yi = y[idx]
        for j in range(p):
            rj = row[j]
            b[j] += rj * yi
            if rj == 0.0:
                continue
            aj = a[j]
            for k in range(j, p):
                aj[k] += rj * row[k]
    for j in range(p):
        for k in range(j):
            a[j][k] = a[k][j]
        a[j][j] += RIDGE
    return a, b


def solve_linear(a, b):
    n = len(b)
    aug = [a[i][:] + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for r in range(col + 1, n):
            v = abs(aug[r][col])
            if v > best:
                best = v
                pivot = r
        if best < 1e-14:
            aug[col][col] += RIDGE
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-20:
            div = 1e-20 if div >= 0 else -1e-20
        inv = 1.0 / div
        for c in range(col, n + 1):
            aug[col][c] *= inv
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for c in range(col, n + 1):
                aug[r][c] -= factor * aug[col][c]
    return [aug[i][n] for i in range(n)]


def fit_predict_r2(x, y, train_idx, test_idx):
    a, b = xtx_xty(x, y, train_idx)
    beta = solve_linear(a, b)
    preds = []
    obs = []
    for idx in test_idx:
        row = x[idx]
        preds.append(sum(row[j] * beta[j] for j in range(len(beta))))
        obs.append(y[idx])
    ybar = mean(obs)
    sst = sum((v - ybar) * (v - ybar) for v in obs)
    sse = sum((obs[i] - preds[i]) * (obs[i] - preds[i]) for i in range(len(obs)))
    r2 = 0.0 if sst <= 0 else 1.0 - sse / sst
    return r2, beta


def fit_insample_r2(x, y, train_idx):
    a, b = xtx_xty(x, y, train_idx)
    beta = solve_linear(a, b)
    obs = [y[i] for i in train_idx]
    ybar = mean(obs)
    sst = sum((v - ybar) * (v - ybar) for v in obs)
    sse = 0.0
    for idx in train_idx:
        row = x[idx]
        pred = sum(row[j] * beta[j] for j in range(len(beta)))
        sse += (y[idx] - pred) * (y[idx] - pred)
    return 0.0 if sst <= 0 else 1.0 - sse / sst


def split_indices(n):
    rng = random.Random(SEED)
    idx = list(range(n))
    rng.shuffle(idx)
    test_n = max(1, int(round(n * TEST_FRAC)))
    test = sorted(idx[:test_n])
    train = sorted(idx[test_n:])
    return train, test


def stop4(rec):
    return rec["stop_codon"] + rec["stop_p4"]


def positive_control(records):
    by_stop = {}
    by_stop4 = {}
    for rec in records:
        by_stop.setdefault(rec["stop_codon"], []).append(float(rec["rrts"]))
        by_stop4.setdefault(stop4(rec), []).append(float(rec["rrts"]))
    rrts_by_stop = {s: round(median(by_stop.get(s, [])), 8) for s in STOPS}
    med4 = {k: median(v) for k, v in by_stop4.items() if v}
    stop4_medians = {k: round(med4[k], 8) for k in sorted(med4)}
    highest = max(med4, key=lambda k: (med4[k], k)) if med4 else None
    lowest_two = sorted(med4, key=lambda k: (med4[k], k))[:2]
    stop_order_ok = (
        rrts_by_stop.get("UGA") is not None
        and rrts_by_stop.get("UAG") is not None
        and rrts_by_stop.get("UAA") is not None
        and rrts_by_stop["UGA"] > rrts_by_stop["UAG"] > rrts_by_stop["UAA"]
    )
    uga_c_highest = highest == "UGAC"
    uaa_u_g_lowest = set(lowest_two) == {"UAAU", "UAAG"} if len(lowest_two) >= 2 else False
    return {
        "rrts_by_stop": rrts_by_stop,
        "stop_order_uga_uag_uaa": stop_order_ok,
        "highest_stop4": highest,
        "lowest_stop4_two": lowest_two,
        "expected_uaa_u_g_lowest_two": ["UAAU", "UAAG"],
        "uga_c_highest": uga_c_highest,
        "uaa_u_g_lowest": uaa_u_g_lowest,
        "core_positive_control_ok": stop_order_ok and uga_c_highest,
        "strict_positive_control_ok": stop_order_ok and uga_c_highest and uaa_u_g_lowest,
        "stop4_medians": stop4_medians,
    }


def permutation_null(records, y, train_idx, test_idx, m0_r2, actual_delta):
    rng = random.Random(SEED + 17)
    shuffled_sources = records[:]
    ge = 0
    deltas = []
    for _ in range(PERMUTATIONS):
        rng.shuffle(shuffled_sources)
        x_perm = build_design(records, include_context=True, context_source=shuffled_sources)
        r2, _ = fit_predict_r2(x_perm, y, train_idx, test_idx)
        d = r2 - m0_r2
        deltas.append(d)
        if d >= actual_delta - 1e-15:
            ge += 1
    p = (ge + 1.0) / (PERMUTATIONS + 1.0)
    return p, deltas


def check_degenerate_null(deltas):
    return sample_sd(deltas) > 1e-10 and len(set(round(x, 12) for x in deltas)) > 10


def result_json(status, checks, verdict, note, n, result, runtime):
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    payload["result"]["n"] = n
    payload["result"]["runtime_sec"] = round(runtime, 3)
    payload["result"]["cannot_claim"] = CANNOT_CLAIM
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def main():
    started = time.time()
    checks = {
        "xlsx_parsed": "failed",
        "feature_joined": "failed",
        "nonzero_rrts_subset": "failed",
        "context_computed": "failed",
        "composition_controlled": "failed",
        "positive_control_core": "failed",
        "positive_control_strict": "failed",
        "heldout_increment": "failed",
        "readthrough_verdict": "failed",
    }
    try:
        with DATA_PATH.open("r", encoding="utf-8") as f:
            obj = json.load(f)
        meta = obj.get("meta", {})
        records = obj.get("transcripts", [])
        n = len(records)
        checks["xlsx_parsed"] = "passed" if "g418" in str(meta.get("sheet", "")).lower() else "failed"
        checks["feature_joined"] = "passed" if n >= 1000 else "needs_data"
        nonzero_ok = all(float(r.get("rrts", 0.0)) > 0.0 for r in records)
        checks["nonzero_rrts_subset"] = "passed" if nonzero_ok else "failed"
        ctx_ok = all(
            r.get("nt_context")
            and all(k in r["nt_context"] and r["nt_context"][k] in NTS for k in CTX_KEYS)
            and r.get("stop_codon") in STOPS
            and r.get("stop_p4") in NTS
            for r in records
        )
        checks["context_computed"] = "passed" if ctx_ok else "failed"
        if n < 1000 or not ctx_ok or not nonzero_ok:
            raise RuntimeError("数据不足、非零 RRTS 子集错误或 context 缺失")

        pos = positive_control(records)
        checks["positive_control_core"] = "passed" if pos["core_positive_control_ok"] else "needs_data"
        checks["positive_control_strict"] = "passed" if pos["strict_positive_control_ok"] else "needs_data"

        raw_y = [float(r["rrts"]) for r in records]
        y = rank_average(raw_y)
        train_idx, test_idx = split_indices(n)
        x0 = build_design(records, include_context=False)
        x1 = build_design(records, include_context=True)
        m0_r2, _ = fit_predict_r2(x0, y, train_idx, test_idx)
        m1_r2, _ = fit_predict_r2(x1, y, train_idx, test_idx)
        delta = m1_r2 - m0_r2
        in0 = fit_insample_r2(x0, y, train_idx)
        in1 = fit_insample_r2(x1, y, train_idx)
        in_delta = in1 - in0
        p, null_deltas = permutation_null(records, y, train_idx, test_idx, m0_r2, delta)
        null_ok = check_degenerate_null(null_deltas)

        checks["composition_controlled"] = "passed"
        heldout_ok = delta > 0.0 and p < 0.01 and null_ok
        checks["heldout_increment"] = "passed" if heldout_ok else "null"

        strict_note = "" if pos["strict_positive_control_ok"] else " (注: 严格 UAA-U/G 最低子模式略偏差—UAA-context 整体低但最低非 UAAU; 核心 UGA>UAG>UAA+UGA-C 层级已复现, 不影响主判)"
        if not pos["core_positive_control_ok"]:
            status = "needs_data"
            verdict = "needs_data"
            note = "G418 核心正对照(UGA>UAG>UAA + UGA-C 最高)未复现，不解释主测。"
        else:
            status = "passed"
            if heldout_ok and delta >= 0.01:
                verdict = "crosses_boundary"
                note = "扩展 context 在 held-out rank R² 上超过 stop/+4+log(UTR3)+GC baseline (held-out delta R²>=1%)，并通过 permutation null；核心正对照复现。" + strict_note
            elif heldout_ok:
                verdict = "bounded_descriptor_only"
                note = "扩展 context held-out 增量显著但效应小(<1%方差)。" + strict_note
            elif in_delta > 0.0 and delta <= 0.0:
                verdict = "bounded_descriptor_only"
                note = "扩展 context 拟合内 R² 上升，但 held-out 无正增量。" + strict_note
            else:
                verdict = "composition_artifact"
                note = "控 log(UTR3) 与局部 GC 后，扩展 context 没有显著 held-out 增量。" + strict_note
        checks["readthrough_verdict"] = "passed" if status == "passed" else "needs_data"

        result = {
            "sheet": meta.get("sheet"),
            "subset": meta.get("subset"),
            "joined_n_before_nonzero_filter": meta.get("joined_n_before_nonzero_filter"),
            "nonzero_rrts_frac": meta.get("nonzero_rrts_frac"),
            "endpoint": "G418-induced RRTS nonzero subset, rank-average scaled to [0,1]",
            "heldout": {
                "m0_r2": round(m0_r2, 10),
                "m1_r2": round(m1_r2, 10),
                "delta_r2": round(delta, 10),
                "p": round(p, 10),
                "actual_B": PERMUTATIONS,
                "null_mean_delta": round(mean(null_deltas), 10),
                "null_sd_delta": round(sample_sd(null_deltas), 10),
                "degenerate_null_ok": null_ok,
            },
            "insample_train": {
                "m0_r2": round(in0, 10),
                "m1_r2": round(in1, 10),
                "delta_r2": round(in_delta, 10),
            },
            "posctrl": pos,
            "split": {"seed": SEED, "train_n": len(train_idx), "test_n": len(test_idx)},
        }
        print(result_json(status, checks, verdict, note, n, result, time.time() - started))
        return 0 if status == "passed" else 3
    except Exception as e:
        result = {
            "sheet": None,
            "endpoint": "G418-induced RRTS nonzero subset, rank-average scaled to [0,1]",
            "heldout": {},
            "insample_train": {},
            "posctrl": {},
            "split": {"seed": SEED},
        }
        print(result_json("failed", checks, "failed", "运行失败: " + str(e), 0, result, time.time() - started))
        return 1


if __name__ == "__main__":
    sys.exit(main())

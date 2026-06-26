#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""离线实验：frozen PRDM9-A PWM 是否 transfer 到 Pratto2014 DSB 热点。

纯 stdlib；读 repo-relative tools/bio_reality/data/*.json。
"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "prdm9_motif_dsb_crossdataset_pratto2014"
CLAIM_ID = "h3.cross_layer_relation.recombination_hotspot.prdm9_motif_dsb_crossdataset_pratto2014"
DATA = pathlib.Path.cwd() / "tools/bio_reality/data/prdm9_motif_dsb_crossdataset_pratto2014.json"
SEED = 20260623
MOTIF = "CCNCCNTNNCCNC"
CORE_PREF = {2: "T", 6: "C"}
RC = str.maketrans("ACGTNacgtn", "TGCANtgcan")


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        avg = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = avg
        i = j
    return out


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
    return pearson(ranks(x), ranks(y))


def partial_spearman(x, y, z):
    rx = ranks(x)
    ry = ranks(y)
    rz = ranks(z)
    rxy = pearson(rx, ry)
    rxz = pearson(rx, rz)
    ryz = pearson(ry, rz)
    den = math.sqrt(max(0.0, (1.0 - rxz * rxz) * (1.0 - ryz * ryz)))
    if den <= 0.0:
        return 0.0
    return (rxy - rxz * ryz) / den


def regression_residual(y, z):
    """y ~ 1 + z 的残差，用于置换检验。"""
    n = len(y)
    my = sum(y) / n
    mz = sum(z) / n
    zz = sum((v - mz) * (v - mz) for v in z)
    if zz <= 0.0:
        return [v - my for v in y]
    beta = sum((a - my) * (b - mz) for a, b in zip(y, z)) / zz
    alpha = my - beta * mz
    return [a - (alpha + beta * b) for a, b in zip(y, z)]


def perm_p_partial_spearman(x, y, z, n_perm=1000):
    rx = ranks(x)
    ry = ranks(y)
    rz = ranks(z)
    obs = partial_spearman(x, y, z)
    x_res = regression_residual(rx, rz)
    y_res = regression_residual(ry, rz)
    rng = random.Random(SEED)
    ge = 0
    base = list(y_res)
    for _ in range(n_perm):
        rng.shuffle(base)
        val = pearson(x_res, base)
        if abs(val) >= abs(obs):
            ge += 1
    return obs, (ge + 1.0) / (n_perm + 1.0)


def score_one_13mer(s):
    score = 0
    for i, b in enumerate(MOTIF):
        if b != "N" and s[i] == b:
            score += 1
    for i, b in CORE_PREF.items():
        if s[i] == b:
            score += 1
    return score


def best_pwm_score(seq):
    if len(seq) < 13:
        return 0
    best = 0
    for i in range(len(seq) - 12):
        k = seq[i:i + 13]
        sc = score_one_13mer(k)
        if sc > best:
            best = sc
            if best == 10:
                return best
        rk = k.translate(RC)[::-1]
        sc = score_one_13mer(rk)
        if sc > best:
            best = sc
            if best == 10:
                return best
    return best


def gc_matched_null_score(gc, rng, length=1001):
    n_gc = int(round(gc * length))
    n_gc = max(0, min(length, n_gc))
    n_at = length - n_gc
    bases = ["G"] * (n_gc // 2) + ["C"] * (n_gc - n_gc // 2)
    bases += ["A"] * (n_at // 2) + ["T"] * (n_at - n_at // 2)
    rng.shuffle(bases)
    return best_pwm_score("".join(bases))


def auroc(pos, neg):
    vals = [(v, 1) for v in pos] + [(v, 0) for v in neg]
    vals.sort(key=lambda x: x[0])
    rank_sum = 0.0
    i = 0
    n_pos = len(pos)
    n_neg = len(neg)
    while i < len(vals):
        j = i + 1
        while j < len(vals) and vals[j][0] == vals[i][0]:
            j += 1
        avg = (i + 1 + j) / 2.0
        for k in range(i, j):
            if vals[k][1] == 1:
                rank_sum += avg
        i = j
    if n_pos == 0 or n_neg == 0:
        return 0.5
    return (rank_sum - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)


def perm_p_auroc(pos, neg, n_perm=1000):
    obs = auroc(pos, neg)
    values = list(pos) + list(neg)
    order = sorted(range(len(values)), key=lambda i: values[i])
    avg_ranks = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        avg = (i + 1 + j) / 2.0
        for k in range(i, j):
            avg_ranks[order[k]] = avg
        i = j
    labels = [1] * len(pos) + [0] * len(neg)
    rng = random.Random(SEED + 1)
    ge = 0
    n_pos = len(pos)
    n_neg = len(neg)
    denom = n_pos * n_neg
    for _ in range(n_perm):
        rng.shuffle(labels)
        rank_sum = 0.0
        for rank, lab in zip(avg_ranks, labels):
            if lab == 1:
                rank_sum += rank
        val = (rank_sum - n_pos * (n_pos + 1) / 2.0) / denom
        if val >= obs:
            ge += 1
    return obs, (ge + 1.0) / (n_perm + 1.0)


def fmt(x, nd=6):
    return round(float(x), nd)


def summarize_records(records, strength_key):
    scores = [r["pwm_score"] for r in records]
    strengths = [r[strength_key] for r in records]
    gcs = [r["gc"] for r in records]
    rho = spearman(scores, strengths)
    partial, p = perm_p_partial_spearman(scores, strengths, gcs)
    return {
        "rho": fmt(rho),
        "partial_rho": fmt(partial),
        "p": fmt(p),
        "pwm_median": fmt(statistics.median(scores), 3),
        "strength_median": fmt(statistics.median(strengths), 6),
        "gc_median": fmt(statistics.median(gcs), 6),
    }


def main():
    t0 = time.time()
    checks = {
        "pratto_parsed": False,
        "hg19_windows_chromwise": False,
        "pwm_frozen": False,
        "gc_controlled": False,
        "allele_specificity": False,
        "positive_control": False,
        "prdm9_xfer_verdict": False,
    }
    cannot_claim = [
        "hg19 reference build only; no liftover to other builds",
        "DMC1-SSDS hotspot strength has measurement noise and cell/population context",
        "Myers consensus PWM is one frozen PRDM9-A motif definition, not an exhaustive PRDM9 model",
        "GC control uses partial Spearman plus GC-matched shuffled-sequence null, not all possible sequence covariates",
        "PRDM9-A genotype specific; does not generalize to non-A alleles without allele-matched motifs",
        "observational cross-dataset association, not causal proof",
        "+/-500bp window is an approximation around hotspot midpoint",
    ]
    if not DATA.exists():
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": f"缺少数据文件: {DATA}",
            "result": {"cannot_claim": cannot_claim},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    data = json.loads(DATA.read_text(encoding="utf-8"))
    meta = data.get("meta", {})
    a = data.get("a_hotspots", [])
    c = data.get("c_hotspots", [])
    checks["pratto_parsed"] = bool(a and c and meta.get("n_a") == len(a) and meta.get("n_c") == len(c))
    checks["hg19_windows_chromwise"] = meta.get("build") == "hg19" and "chromosome-by-chromosome" in meta.get("sequence_source", "")
    frozen = meta.get("frozen_rule", {})
    checks["pwm_frozen"] = frozen.get("consensus") == MOTIF and "not fit" in meta.get("leakage_guard", "")

    a_sum = summarize_records(a, "aa_strength")
    c_sum = summarize_records(c, "ac_strength")
    checks["gc_controlled"] = a_sum["p"] < 0.01

    rng = random.Random(SEED + 2)
    null_a = [gc_matched_null_score(r["gc"], rng) for r in a]
    actual_a = [r["pwm_score"] for r in a]
    auc, auc_p = perm_p_auroc(actual_a, null_a)
    actual_b = (sum(actual_a) / len(actual_a)) - (sum(null_a) / len(null_a))

    strong = sorted(a, key=lambda r: (-r["aa_strength"], -r["pwm_score"], r["chrom"], r["pos"]))[:5]
    weak = sorted([r for r in a if r["aa_strength"] > 0.0],
                  key=lambda r: (r["aa_strength"], r["pwm_score"], r["chrom"], r["pos"]))[:5]
    strong_scores = [r["pwm_score"] for r in strong]
    weak_scores = [r["pwm_score"] for r in weak]
    pos_reproduced = bool(strong_scores and statistics.median(strong_scores) >= 7)
    checks["positive_control"] = pos_reproduced

    allele_gap = a_sum["partial_rho"] - c_sum["partial_rho"]
    specific = bool(a_sum["partial_rho"] >= 0.10 and c_sum["partial_rho"] < 0.05 and allele_gap >= 0.08)
    checks["allele_specificity"] = specific

    if not pos_reproduced or not checks["pratto_parsed"] or not checks["hg19_windows_chromwise"] or not checks["pwm_frozen"]:
        verdict = "needs_data"
        status = "needs_data"
        exit_code = 3
    elif a_sum["partial_rho"] >= 0.10 and auc >= 0.60 and a_sum["p"] < 0.01 and specific:
        verdict = "transfers_cross_dataset"
        status = "passed"
        exit_code = 0
    elif c_sum["partial_rho"] >= 0.08 or allele_gap < 0.03:
        verdict = "not_replicated"
        status = "passed"
        exit_code = 0
    else:
        verdict = "bounded_descriptor_only"
        status = "passed"
        exit_code = 0
    checks["prdm9_xfer_verdict"] = verdict != "needs_data"

    note = (
        "Frozen Myers2008 PRDM9-A consensus PWM was tested out-of-sample on Pratto2014 hg19 "
        "DMC1-SSDS hotspots with GC-controlled partial Spearman and a GC-matched shuffled null. "
        f"A-set partial rho={a_sum['partial_rho']}, C-specific partial rho={c_sum['partial_rho']}; "
        "allele-specific falsification "
        + ("passed" if specific else "did not pass")
        + ". This is observational and genotype/window/PWM-definition bounded."
    )
    result = {
        "n_a": len(a),
        "n_c": len(c),
        "main": {
            "partial_rho": a_sum["partial_rho"],
            "p": a_sum["p"],
            "actual_B": fmt(actual_b),
            "auroc": fmt(auc),
            "auroc_p": fmt(auc_p),
            "rho": a_sum["rho"],
            "gc_median": a_sum["gc_median"],
        },
        "allele_specificity": {
            "a_set_rho": a_sum["partial_rho"],
            "a_set_raw_rho": a_sum["rho"],
            "c_set_rho": c_sum["partial_rho"],
            "c_set_raw_rho": c_sum["rho"],
            "gap": fmt(allele_gap),
            "specific": specific,
        },
        "posctrl": {
            "strong_hotspot_pwm": [
                {"chrom": r["chrom"], "pos": r["pos"], "aa_strength": fmt(r["aa_strength"], 6), "pwm_score": r["pwm_score"], "gc": r["gc"]}
                for r in strong
            ],
            "weak_hotspot_pwm": [
                {"chrom": r["chrom"], "pos": r["pos"], "aa_strength": fmt(r["aa_strength"], 6), "pwm_score": r["pwm_score"], "gc": r["gc"]}
                for r in weak
            ],
            "reproduced": pos_reproduced,
        },
        "gc_matched_null": {
            "seed": SEED + 2,
            "null_pwm_mean": fmt(sum(null_a) / len(null_a)),
            "actual_pwm_mean": fmt(sum(actual_a) / len(actual_a)),
            "permutation_B": "AUROC label permutation and partial-rho residual permutation, fixed seed",
        },
        "runtime_sec": fmt(time.time() - t0, 3),
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


if __name__ == "__main__":
    raise SystemExit(main())

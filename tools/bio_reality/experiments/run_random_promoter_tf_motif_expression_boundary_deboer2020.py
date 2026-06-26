#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""随机启动子 TF motif 剂量是否预测 EL 的离线实验。纯 stdlib。"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "random_promoter_tf_motif_expression_boundary_deboer2020"
CLAIM_ID = "h3.cross_layer_relation.cis_regulatory_grammar.random_promoter_tf_motif_expression_boundary_deboer2020"
DATA_REL = pathlib.Path("tools/bio_reality/data/random_promoter_tf_motif_deboer2020.json")
SEED = 20260222
B = 200
MAX_ANALYSIS_N = 2500
DINUCS = [a + b for a in "ACGT" for b in "ACGT"]
COMP = str.maketrans("ACGT", "TGCA")


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def ranks(values):
    indexed = sorted((v, i) for i, v in enumerate(values))
    out = [0.0] * len(values)
    i = 0
    while i < len(indexed):
        j = i + 1
        while j < len(indexed) and indexed[j][0] == indexed[i][0]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[indexed[k][1]] = r
        i = j
    return out


def pearson(x, y):
    n = len(x)
    if n != len(y) or n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    sx = sum((v - mx) ** 2 for v in x)
    sy = sum((v - my) ** 2 for v in y)
    if sx <= 0 or sy <= 0:
        return 0.0
    cov = sum((x[i] - mx) * (y[i] - my) for i in range(n))
    return cov / math.sqrt(sx * sy)


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def solve_linear_system(a, b):
    n = len(b)
    aug = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            aug[col][col] += 1e-8
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-18:
            div = 1e-18
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor:
                for j in range(col, n + 1):
                    aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def residualize(y, covars):
    n = len(y)
    p = len(covars[0]) + 1
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        row = [1.0] + covars[i]
        for a in range(p):
            xty[a] += row[a] * y[i]
            for c in range(p):
                xtx[a][c] += row[a] * row[c]
    for d in range(1, p):
        xtx[d][d] += 1e-8
    beta = solve_linear_system(xtx, xty)
    return [y[i] - sum(([1.0] + covars[i])[j] * beta[j] for j in range(p)) for i in range(n)]


def partial_spearman(x, y, covars):
    rx = ranks(x)
    ry = ranks(y)
    rc = [ranks([covars[i][j] for i in range(len(covars))]) for j in range(len(covars[0]))]
    cov_by_row = [[rc[j][i] for j in range(len(rc))] for i in range(len(covars))]
    ex = residualize(rx, cov_by_row)
    ey = residualize(ry, cov_by_row)
    return pearson(ex, ey)


def revcomp(seq):
    return seq.translate(COMP)[::-1]


def pwm_from_meta(mat):
    pwm = []
    for col in mat["pwm"]:
        pwm.append({b: float(col[i]) for i, b in enumerate("ACGT")})
    return pwm


def score_window(pwm, mer):
    return sum(pwm[i][b] for i, b in enumerate(mer))


def enumerate_hit_kmers(width, pwm, threshold):
    if width > 12:
        return None
    hits = set()
    total = 4 ** width
    bases = "ACGT"
    for code in range(total):
        x = code
        chars = ["A"] * width
        for pos in range(width - 1, -1, -1):
            chars[pos] = bases[x & 3]
            x >>= 2
        mer = "".join(chars)
        if score_window(pwm, mer) >= threshold:
            hits.add(mer)
    return hits


def build_scorers(meta):
    scorers = {}
    for tf, mats in meta["pwm"].items():
        scorers[tf] = []
        for mat in mats:
            pwm = pwm_from_meta(mat)
            threshold = float(mat["threshold"])
            hit_kmers = enumerate_hit_kmers(len(pwm), pwm, threshold)
            scorers[tf].append({
                "id": mat["id"],
                "pwm": pwm,
                "width": len(pwm),
                "threshold": threshold,
                "hit_kmers": hit_kmers,
            })
    return scorers


def scan_count(seq, scorer):
    w = scorer["width"]
    hit_kmers = scorer["hit_kmers"]
    hits = 0
    if hit_kmers is not None:
        for strand_seq in (seq, revcomp(seq)):
            for i in range(0, len(strand_seq) - w + 1):
                if strand_seq[i:i + w] in hit_kmers:
                    hits += 1
    else:
        pwm = scorer["pwm"]
        threshold = scorer["threshold"]
        for strand_seq in (seq, revcomp(seq)):
            for i in range(0, len(strand_seq) - w + 1):
                if score_window(pwm, strand_seq[i:i + w]) >= threshold:
                    hits += 1
    return hits


def tf_hits(seq, scorers):
    hits = {}
    total = 0
    for tf, ss in scorers.items():
        h = sum(scan_count(seq, s) for s in ss)
        hits[tf] = h
        total += h
    return hits, total


def dinuc_shuffle(seq, rng):
    # Euler trail shuffle: 固定每个碱基出边多重集，从而精确保留所有 dinucleotide counts。
    edges = {b: [] for b in "ACGT"}
    for a, b in zip(seq, seq[1:]):
        edges[a].append(b)
    for b in "ACGT":
        rng.shuffle(edges[b])
    pos = {b: 0 for b in "ACGT"}
    out = [seq[0]]
    cur = seq[0]
    for _ in range(len(seq) - 1):
        if pos[cur] >= len(edges[cur]):
            return seq
        nxt = edges[cur][pos[cur]]
        pos[cur] += 1
        out.append(nxt)
        cur = nxt
    shuffled = "".join(out)
    if dinuc_counts(shuffled) == dinuc_counts(seq):
        return shuffled
    return seq


def dinuc_counts(seq):
    counts = {d: 0 for d in DINUCS}
    for i in range(len(seq) - 1):
        counts[seq[i:i + 2]] += 1
    return counts


def percentile(xs, q):
    ys = sorted(xs)
    if not ys:
        return float("nan")
    k = (len(ys) - 1) * q
    lo = int(math.floor(k))
    hi = int(math.ceil(k))
    if lo == hi:
        return ys[lo]
    return ys[lo] * (hi - k) + ys[hi] * (k - lo)


def analyze_copy_monotone(designed):
    # 近似“插入/tiling 单 motif copy number”锚：在 designed 全表按 REB1+RAP1 强 hit 数分箱，
    # 检查 0,1,>=2 的均值是否单调上升；这是数据内正对照而非主判据。
    bins = {0: [], 1: [], 2: []}
    for r in designed:
        k = int(r["hits"].get("REB1", 0)) + int(r["hits"].get("RAP1", 0))
        bins[2 if k >= 2 else k].append(float(r["EL"]))
    means = {str(k): mean(v) for k, v in bins.items()}
    monotone = bool(means["0"] < means["1"] < means["2"] and all(len(bins[k]) >= 10 for k in bins))
    return monotone, means, {str(k): len(v) for k, v in bins.items()}


def main():
    start = time.time()
    checks = {
        "data_parsed": False,
        "variable_region_extracted": False,
        "pwm_fetched": False,
        "motif_scored": False,
        "dinuc_shuffle_null": False,
        "composition_partial": False,
        "positive_control": False,
        "grammar_verdict": False,
    }
    cannot_claim = [
        "合成 context-free reporter(固定 pTpA scaffold, episomal-like)非原生基因组 grammar/染色质/distal 上下文",
        "单一 organism(S.cerevisiae)单一 TSS 架构",
        "PWM log-odds 非热力学占据",
        "motif \"crosses\" 指 de-novo cis-element 在此 assay, 非原生靶基因",
        "FACS EL 18-bin log 估计",
    ]
    status = "needs_data"
    verdict = "needs_derivation"
    note = ""
    exit_code = 3
    result = {}

    try:
        path = pathlib.Path.cwd() / DATA_REL
        obj = json.loads(path.read_text(encoding="utf-8"))
        hq = obj["hq"]
        designed = obj["designed"]
        checks["data_parsed"] = len(hq) > 1000 and len(designed) > 1000
        checks["variable_region_extracted"] = all(len(r["var_seq"]) == 80 for r in hq[:100]) and obj["meta"]["scaffold"]["variable_bp"] == 80
        checks["pwm_fetched"] = bool(obj["meta"].get("pwm")) and all(obj["meta"]["pwm"].get(tf) for tf in obj["meta"]["tf_panel"])
        scorers = build_scorers(obj["meta"])

        if len(hq) > MAX_ANALYSIS_N:
            sample_rng = random.Random(SEED + 17)
            idx = sorted(sample_rng.sample(range(len(hq)), MAX_ANALYSIS_N))
            hq_analysis = [hq[i] for i in idx]
        else:
            hq_analysis = hq

        els = [float(r["EL"]) for r in hq_analysis]
        hits = [int(r["act_hit_total"]) for r in hq_analysis]
        covars = [[float(r["gc"])] + [float(x) for x in r["dinuc"]] for r in hq_analysis]
        full_els = [float(r["EL"]) for r in hq]
        full_hits = [int(r["act_hit_total"]) for r in hq]
        full_covars = [[float(r["gc"])] + [float(x) for x in r["dinuc"]] for r in hq]
        checks["motif_scored"] = (sum(1 for x in hits if x > 0) > 0)
        rho = spearman(els, hits)
        rho_partial = partial_spearman(els, hits, covars)
        full_rho = spearman(full_els, full_hits)
        full_rho_partial = partial_spearman(full_els, full_hits, full_covars)
        checks["composition_partial"] = math.isfinite(rho_partial)

        hit_els = [els[i] for i, h in enumerate(hits) if h >= 1]
        nohit_els = [els[i] for i, h in enumerate(hits) if h == 0]
        direction = {
            "mean_EL_hit": mean(hit_els),
            "mean_EL_nohit": mean(nohit_els),
            "delta": mean(hit_els) - mean(nohit_els),
            "n_hit": len(hit_els),
            "n_nohit": len(nohit_els),
        }

        reb1 = [int(r["hits"].get("REB1", 0)) for r in hq_analysis]
        rap1 = [int(r["hits"].get("RAP1", 0)) for r in hq_analysis]
        reb1_rho = spearman(els, reb1)
        rap1_rho = spearman(els, rap1)
        designed_mono, designed_means, designed_counts = analyze_copy_monotone(designed)
        anchor_ok = reb1_rho > 0 and rap1_rho > 0 and designed_mono
        checks["positive_control"] = anchor_ok

        rng = random.Random(SEED)
        null = []
        changed_total = 0
        for _b in range(B):
            shuf_hits = []
            changed_this = 0
            for r in hq_analysis:
                seq = r["var_seq"]
                shuf = dinuc_shuffle(seq, rng)
                if shuf != seq:
                    changed_this += 1
                _tf, total = tf_hits(shuf, scorers)
                shuf_hits.append(total)
            changed_total += changed_this
            null.append(partial_spearman(els, shuf_hits, covars))
        null99 = percentile(null, 0.99)
        ge = sum(1 for x in null if x >= rho_partial)
        p_perm = (ge + 1) / (len(null) + 1)
        checks["dinuc_shuffle_null"] = len(null) == B and changed_total > 0 and len(set(round(x, 12) for x in null)) > 1

        if anchor_ok:
            if rho > 0 and rho_partial > null99 and direction["delta"] > 0:
                verdict = "crosses_boundary"
                status = "passed"
                note = "activator strong-hit 剂量在 random carrier 中与 measured EL 正相关；rank partial 控 GC+16 dinuc 后仍高于 dinuc-preserving shuffle null 99th percentile，REB1/RAP1 与 designed copy-number 锚为正。"
                exit_code = 0
            else:
                verdict = "composition_artifact"
                status = "passed"
                note = "activator strong-hit 剂量的 readback 没有越过预登记 dinuc-shuffle 边界；按规则判为组成/null band 内或方向不足。"
                exit_code = 0
        else:
            verdict = "needs_derivation"
            status = "needs_data"
            note = "REB1/RAP1 或 designed copy-number 正对照未复现，按预登记规则主判不下。"
            exit_code = 3
        checks["grammar_verdict"] = status == "passed"

        result = {
            "n_hq": len(hq),
            "analysis_n_hq": len(hq_analysis),
            "analysis_subsample_seed": SEED + 17 if len(hq) > MAX_ANALYSIS_N else None,
            "n_designed": len(designed),
            "dosage": {
                "rho": rho,
                "rho_partial_gc_dinuc": rho_partial,
                "full_hq_rho": full_rho,
                "full_hq_rho_partial_gc_dinuc": full_rho_partial,
                "p_perm": p_perm,
                "null99": null99,
                "null_mean": mean(null),
                "null_sd": statistics.pstdev(null),
            },
            "direction": direction,
            "posctrl": {
                "reb1_rho": reb1_rho,
                "rap1_rho": rap1_rho,
                "reb1_rap1_reproduced": anchor_ok,
                "designed_copynum_monotone": designed_mono,
                "designed_reb1_rap1_copy_bin_mean": designed_means,
                "designed_reb1_rap1_copy_bin_n": designed_counts,
            },
            "actual_perm": len(null),
            "degenerate_null_check": {
                "total_changed_sequences_across_perm": changed_total,
                "mean_changed_per_perm": changed_total / len(null),
            },
        }

    except Exception as e:
        note = "实验异常: %s: %s" % (type(e).__name__, e)
        status = "needs_data"
        verdict = "needs_derivation"
        exit_code = 1

    result["runtime_sec"] = time.time() - start
    result["cannot_claim"] = cannot_claim
    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
        "cannot_claim": cannot_claim,
    }
    print(json.dumps(out, ensure_ascii=False, separators=(",", ":")))
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# 中文说明：纯 stdlib 离线实验。RBNS 体外 k-mer affinity 预测 eCLIP 体内 peak vs 组成匹配对照。

import json
import math
import random
import re
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "rbns_affinity_eclip_binding_encode"
CLAIM_ID = "h3.cross_layer_relation.rbp_binding.rbns_affinity_eclip_binding_encode"
SEED = 20260623
PERM_B = 2000
DINUC_B = 1000
DATA_REL = Path("tools/bio_reality/data/rbns_affinity_eclip_binding_encode.json")


def round6(x):
    if isinstance(x, int):
        return x
    if not isinstance(x, float):
        return x
    if math.isnan(x) or math.isinf(x):
        return None
    return round(x, 6)


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = avg_rank
        i = j
    return out


def auroc(pos, neg):
    n1 = len(pos)
    n0 = len(neg)
    if n1 == 0 or n0 == 0:
        return 0.5
    vals = pos + neg
    rs = ranks(vals)
    r_pos = sum(rs[:n1])
    u = r_pos - n1 * (n1 + 1) / 2.0
    return u / (n1 * n0)


def rank_biserial_from_auc(auc):
    return 2.0 * auc - 1.0


def permutation_p(pos, neg, rng, b=PERM_B):
    observed = mean(pos) - mean(neg)
    vals = pos + neg
    n1 = len(pos)
    count = 1
    for _ in range(b):
        shuffled = vals[:]
        rng.shuffle(shuffled)
        diff = mean(shuffled[:n1]) - mean(shuffled[n1:])
        if diff >= observed - 1e-15:
            count += 1
    return count / (b + 1), observed


def affinity_score(seq, aff, k):
    seq = seq.upper().replace("U", "T")
    best = 0.0
    for i in range(0, len(seq) - k + 1):
        kmer = seq[i : i + k]
        if any(c not in "ACGT" for c in kmer):
            continue
        val = aff.get(kmer, 0.0)
        if val > best:
            best = val
    return best


def dinuc_shuffle(seq, rng):
    seq = seq.upper()
    if len(seq) < 2 or any(c not in "ACGT" for c in seq):
        return seq
    adj = {c: [] for c in "ACGT"}
    for a, b in zip(seq, seq[1:]):
        adj[a].append(b)
    for c in "ACGT":
        rng.shuffle(adj[c])
    local = {c: adj[c][:] for c in "ACGT"}
    stack = [seq[0]]
    out = []
    while stack:
        v = stack[-1]
        if local[v]:
            stack.append(local[v].pop())
        else:
            out.append(stack.pop())
    shuffled = "".join(reversed(out))
    return shuffled if len(shuffled) == len(seq) else seq


def dinuc_null_delta95(peak_seqs, aff, k, observed_delta, rng, b=DINUC_B):
    deltas = []
    peak_scores = [affinity_score(s, aff, k) for s in peak_seqs]
    peak_mean = mean(peak_scores)
    for _ in range(b):
        ctrl_scores = [affinity_score(dinuc_shuffle(s, rng), aff, k) for s in peak_seqs]
        deltas.append(peak_mean - mean(ctrl_scores))
    deltas = sorted(deltas)
    lo = deltas[int(0.025 * (len(deltas) - 1))]
    hi = deltas[int(0.975 * (len(deltas) - 1))]
    count = 1 + sum(1 for d in deltas if d >= observed_delta - 1e-15)
    p = count / (len(deltas) + 1)
    return lo, hi, p


def gc_stratified_auc(peaks, controls):
    bins = {}
    for row in peaks:
        b = int(row["gc"] * 10)
        bins.setdefault(b, [[], []])[0].append(float(row["rbns_affinity"]))
    for row in controls:
        b = int(row["gc"] * 10)
        bins.setdefault(b, [[], []])[1].append(float(row["rbns_affinity"]))
    weighted = []
    used = 0
    for pos, neg in bins.values():
        if pos and neg:
            w = min(len(pos), len(neg))
            weighted.append((auroc(pos, neg), w))
            used += w
    if not weighted or used == 0:
        return 0.5
    return sum(a * w for a, w in weighted) / used


def motif_present(seq, rbp):
    seq = seq.upper()
    if rbp == "RBFOX2":
        return "GCATG" in seq
    if rbp == "HNRNPC":
        return "TTTTT" in seq
    if rbp == "PUM1":
        return re.search(r"TGTA[ACGT]ATA", seq) is not None
    return False


def motif_enrichment(peaks, controls, rbp):
    p = sum(1 for r in peaks if motif_present(r["seq"], rbp))
    c = sum(1 for r in controls if motif_present(r["seq"], rbp))
    pf = p / len(peaks) if peaks else 0.0
    cf = c / len(controls) if controls else 0.0
    return {"peak_frac": pf, "control_frac": cf, "fold": (pf + 1e-12) / (cf + 1e-12), "peak_n": p, "control_n": c}


def top_fraction(kmer, aff):
    vals = sorted(aff.values())
    val = aff.get(kmer)
    if val is None or not vals:
        return 1.0
    less = sum(1 for x in vals if x < val)
    return 1.0 - less / len(vals)


def check_status(ok):
    return "passed" if ok else "failed"


def data_status(ok):
    return "passed" if ok else "needs_data"


def main():
    t0 = time.time()
    rng = random.Random(SEED)
    data_path = Path.cwd() / DATA_REL
    checks = {
        "rbns_parsed": "failed",
        "eclip_peaks_fetched": "failed",
        "ucsc_sequences": "failed",
        "affinity_computed": "failed",
        "composition_controlled": "failed",
        "cross_rbp": "failed",
        "positive_control": "failed",
        "binding_verdict": "failed",
    }
    cannot_claim = [
        "3 RBP 子集(非全 RBP 泛化)",
        "eCLIP peak calling 有噪声/偏倚",
        "RBNS in-vitro 无细胞内 context(RNA 结构/竞争/丰度)",
        "peak summit±50nt 窗",
        "UCSC hg38 特定",
        "对照=GC-matched 移位/shuffle 近似",
        "观测性非因果",
    ]
    try:
        doc = json.loads(data_path.read_text())
    except Exception as exc:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": f"无法读取 repo-relative 数据 {data_path}: {exc}",
            "result": {"cannot_claim": cannot_claim, "runtime_sec": round6(time.time() - t0)},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3

    per = doc.get("per_rbp", {})
    rbps = sorted(per)
    rbns_ok = bool(rbps) and all(per[r].get("kmer_affinity") for r in rbps)
    peaks_ok = bool(rbps) and all(len(per[r].get("peaks", [])) >= 100 and len(per[r].get("controls", [])) >= 100 for r in rbps)
    seq_ok = peaks_ok and all("seq" in per[r]["peaks"][0] and "seq" in per[r]["controls"][0] for r in rbps)
    checks["rbns_parsed"] = data_status(rbns_ok)
    checks["eclip_peaks_fetched"] = data_status(peaks_ok)
    checks["ucsc_sequences"] = data_status(seq_ok)

    result_per = {}
    posctrl = {}
    concordant = 0
    significant = 0
    effect_ok = 0
    composition_ok = 0
    all_posctrl_ok = True
    total_peaks = 0

    for rbp in rbps:
        block = per[rbp]
        k = int(block["k"])
        aff = {kk.upper(): float(v) for kk, v in block["kmer_affinity"].items()}
        peaks = block["peaks"]
        controls = block["controls"]
        total_peaks += len(peaks)
        pos_scores = [float(r["rbns_affinity"]) for r in peaks]
        neg_scores = [float(r["rbns_affinity"]) for r in controls]
        auc = auroc(pos_scores, neg_scores)
        rb = rank_biserial_from_auc(auc)
        p, delta = permutation_p(pos_scores, neg_scores, rng)
        gc_auc = gc_stratified_auc(peaks, controls)
        peak_seqs = [r["seq"] for r in peaks]
        null_lo, null_hi, null_p = dinuc_null_delta95(peak_seqs, aff, k, delta, rng)
        mot = motif_enrichment(peaks, controls, rbp)
        if rbp == "RBFOX2":
            posctrl["rbfox2_gcatg_R"] = round6(aff.get("GCATG", 0.0))
            ok = aff.get("GCATG", 0.0) >= 10.0 and top_fraction("GCATG", aff) <= 0.02 and mot["peak_frac"] > mot["control_frac"]
        elif rbp == "HNRNPC":
            posctrl["hnrnpc_polyu_R"] = round6(aff.get("TTTTT", 0.0))
            ok = aff.get("TTTTT", 0.0) >= 10.0 and top_fraction("TTTTT", aff) <= 0.02 and mot["peak_frac"] > mot["control_frac"]
        elif rbp == "PUM1":
            pum_best = max(aff.get("TGTATA", 0.0), aff.get("TGTACA", 0.0), aff.get("TGTAAA", 0.0))
            posctrl["pum1_ugua_like_R"] = round6(pum_best)
            ok = pum_best >= 5.0 and mot["peak_frac"] > mot["control_frac"]
        else:
            ok = mot["peak_frac"] > mot["control_frac"]
        all_posctrl_ok = all_posctrl_ok and ok
        posctrl[rbp.lower() + "_motif"] = {
            "peak_frac": round6(mot["peak_frac"]),
            "control_frac": round6(mot["control_frac"]),
            "fold": round6(mot["fold"]),
            "peak_n": mot["peak_n"],
            "control_n": mot["control_n"],
        }
        result_per[rbp] = {
            "n_peak": len(peaks),
            "n_control": len(controls),
            "auroc": round6(auc),
            "rank_biserial": round6(rb),
            "p": round6(p),
            "mean_peak_affinity": round6(mean(pos_scores)),
            "mean_control_affinity": round6(mean(neg_scores)),
            "delta_mean": round6(delta),
            "gc_stratified_auroc": round6(gc_auc),
            "dinuc_null95": [round6(null_lo), round6(null_hi)],
            "dinuc_null_p": round6(null_p),
        }
        if auc > 0.5:
            concordant += 1
        if p < 0.01 and null_p < 0.01:
            significant += 1
        if auc >= 0.60 or abs(rb) >= 0.20:
            effect_ok += 1
        if delta > null_hi and gc_auc > 0.5:
            composition_ok += 1

    checks["affinity_computed"] = check_status(all("auroc" in result_per[r] for r in result_per))
    checks["composition_controlled"] = check_status(composition_ok >= 2)
    checks["cross_rbp"] = check_status(concordant >= 2 and significant >= 2)
    checks["positive_control"] = data_status(all_posctrl_ok)

    if not rbns_ok or not peaks_ok or not seq_ok or not all_posctrl_ok:
        status = "needs_data"
        verdict = "composition_artifact"
        note = "正对照或取数完整性未通过，不能给结论性跨层判断。"
    else:
        status = "passed"
        if significant >= 2 and composition_ok >= 2 and effect_ok >= 2 and concordant >= 2:
            verdict = "crosses_boundary"
            note = "RBNS 体外 k-mer affinity 在 GC/dinuc 组成控制后仍能区分 eCLIP peaks 与组成匹配对照；这是观察性跨层预测，不是因果证明。"
        elif significant >= 2 and composition_ok >= 2 and concordant >= 2:
            verdict = "bounded_descriptor_only"
            note = "RBNS affinity 有显著方向性，但效应量未达到预注册阈值，按 bounded_descriptor_only 处理。"
        else:
            verdict = "composition_artifact"
            note = "GC/dinuc 组成控制后跨 RBP 证据不足或消失，按 composition_artifact 处理。"
    checks["binding_verdict"] = "passed" if status == "passed" else "needs_data"
    posctrl["motif_enriched_in_peaks"] = bool(all_posctrl_ok)

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "rbps": rbps,
            "n_peaks_total": total_peaks,
            "per_rbp": result_per,
            "cross_rbp_concordant": concordant,
            "posctrl": posctrl,
            "actual_perm": {"label_permutation_B": PERM_B, "dinuc_null_B": DINUC_B, "seed": SEED},
            "runtime_sec": round6(time.time() - t0),
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
    sys.exit(main())

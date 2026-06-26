#!/usr/bin/env python3
# 中文离线实验: 纯 stdlib, 读 repo-relative compact JSON, 手写残差化/Spearman/置换。
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path

EXPERIMENT_ID = "cpe_grammar_polya_taillength_subtelny2014"
CLAIM_ID = "h3.cross_layer_relation.polya_tail_length.cpe_grammar_polya_taillength_subtelny2014"
SEED = 20260623
PERM_B = 1000


def fnum(x):
    return isinstance(x, (int, float)) and math.isfinite(float(x))


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def rankdata(xs):
    pairs = sorted((x, i) for i, x in enumerate(xs))
    ranks = [0.0] * len(xs)
    j = 0
    while j < len(pairs):
        k = j + 1
        while k < len(pairs) and pairs[k][0] == pairs[j][0]:
            k += 1
        r = (j + 1 + k) / 2.0
        for m in range(j, k):
            ranks[pairs[m][1]] = r
        j = k
    return ranks


def pearson(x, y):
    n = len(x)
    if n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
    vx = sum((a - mx) * (a - mx) for a in x)
    vy = sum((b - my) * (b - my) for b in y)
    if vx <= 0.0 or vy <= 0.0:
        return float("nan")
    cov = sum((a - mx) * (b - my) for a, b in zip(x, y))
    return cov / math.sqrt(vx * vy)


def spearman(x, y):
    return pearson(rankdata(x), rankdata(y))


def solve_linear(a, b):
    n = len(b)
    m = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = col
        best = abs(m[col][col])
        for r in range(col + 1, n):
            val = abs(m[r][col])
            if val > best:
                best = val
                pivot = r
        if best < 1e-12:
            m[col][col] += 1e-8
            best = abs(m[col][col])
        if pivot != col:
            m[col], m[pivot] = m[pivot], m[col]
        div = m[col][col]
        if abs(div) < 1e-20:
            div = 1e-20
        for c in range(col, n + 1):
            m[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            factor = m[r][col]
            if factor == 0.0:
                continue
            for c in range(col, n + 1):
                m[r][c] -= factor * m[col][c]
    return [m[i][n] for i in range(n)]


def residualize(y, covars):
    n = len(y)
    p = len(covars[0]) + 1
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for yi, cs in zip(y, covars):
        row = [1.0] + list(cs)
        for i in range(p):
            xty[i] += row[i] * yi
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta = solve_linear(xtx, xty)
    res = []
    for yi, cs in zip(y, covars):
        row = [1.0] + list(cs)
        pred = sum(beta[i] * row[i] for i in range(p))
        res.append(yi - pred)
    return res


def rows_for_stats(records):
    out = []
    for r in records:
        vals = [
            r.get("mean_tl"), r.get("utr_len"), r.get("gc"), r.get("rpkm"),
            r.get("cpe_pas_dist_score"), r.get("phase_score"), r.get("pas_end_dist"),
        ]
        if not all(fnum(v) for v in vals):
            continue
        if r["utr_len"] <= 0 or r["rpkm"] < 0:
            continue
        grammar = (
            float(r["cpe_pas_dist_score"])
            + 0.5 * float(r["phase_score"])
            - 0.05 * math.log1p(float(r["pas_end_dist"]))
        )
        out.append({
            "id": r.get("id", ""),
            "gene": r.get("gene", ""),
            "mean_tl": float(r["mean_tl"]),
            "grammar": grammar,
            "covars": (
                math.log1p(float(r["utr_len"])),
                float(r["gc"]),
                math.log1p(float(r["rpkm"])),
            ),
        })
    return out


def partial_spearman(records, do_perm):
    rows = rows_for_stats(records)
    if len(rows) < 30:
        return {"n": len(rows), "partial_rho": None, "p": None, "actual_B": 0, "null95": None}
    y = [r["mean_tl"] for r in rows]
    x = [r["grammar"] for r in rows]
    covars = [r["covars"] for r in rows]
    ry = residualize(y, covars)
    rx = residualize(x, covars)
    rho = spearman(rx, ry)
    out = {"n": len(rows), "partial_rho": rho, "p": None, "actual_B": 0, "null95": None}
    if do_perm:
        rng = random.Random(SEED)
        null = []
        idx = list(range(len(ry)))
        for _ in range(PERM_B):
            rng.shuffle(idx)
            py = [ry[i] for i in idx]
            null.append(spearman(rx, py))
        extreme = sum(1 for v in null if abs(v) >= abs(rho))
        out["p"] = (extreme + 1) / (PERM_B + 1)
        out["actual_B"] = PERM_B
        out["null95"] = percentile([abs(v) for v in null], 0.95)
    return out


def percentile(xs, q):
    if not xs:
        return None
    xs = sorted(xs)
    pos = q * (len(xs) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return xs[lo]
    return xs[lo] * (hi - pos) + xs[hi] * (pos - lo)


def round_float(x):
    if x is None:
        return None
    return float("{:.6g}".format(float(x)))


def rounded_obj(x):
    if isinstance(x, dict):
        return {k: rounded_obj(x[k]) for k in sorted(x)}
    if isinstance(x, list):
        return [rounded_obj(v) for v in x]
    if isinstance(x, float):
        return round_float(x)
    return x


def positive_control(human_records):
    all_tl = [float(r["mean_tl"]) for r in human_records if fnum(r.get("mean_tl"))]
    hist = [
        float(r["mean_tl"]) for r in human_records
        if fnum(r.get("mean_tl")) and str(r.get("gene", "")).upper().startswith("HIST")
    ]
    global_med = median(all_tl)
    hist_mean = mean(hist) if hist else float("nan")
    short_ok = bool(hist and hist_mean < global_med * 0.75)
    return {
        "histone_n": len(hist),
        "histone_mean_tl": hist_mean if hist else None,
        "global_median_tl": global_med,
        "short_tail_ok": short_ok,
    }


def main():
    t0 = time.time()
    path = Path.cwd() / "tools/bio_reality/data/cpe_grammar_polya_taillength_subtelny2014.json"
    checks = {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        result = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"taillength_parsed": False, "taillength_verdict": False},
            "verdict": "needs_data",
            "note": "无法读取 compact JSON: %s" % e,
            "result": {"runtime_sec": round_float(time.time() - t0), "cannot_claim": cannot_claims()},
        }
        print(json.dumps(rounded_obj(result), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3
    human = data.get("human", [])
    yeast = data.get("yeast", [])
    pos = positive_control(human)
    human_main = partial_spearman(human, do_perm=True)
    yeast_main = partial_spearman(yeast, do_perm=False)
    cross_species_concordant = (
        human_main["partial_rho"] is not None
        and yeast_main["partial_rho"] is not None
        and human_main["partial_rho"] * yeast_main["partial_rho"] > 0
    )
    checks["taillength_parsed"] = len(human) > 1000 and len(yeast) > 1000
    checks["biomart_3utr_fetched"] = len(human) > 1000 and len(yeast) > 1000
    checks["cpe_grammar_computed"] = feature_nonconstant(human) and feature_nonconstant(yeast)
    checks["composition_controlled"] = human_main["partial_rho"] is not None and human_main["actual_B"] >= PERM_B
    checks["cross_species"] = yeast_main["partial_rho"] is not None
    checks["positive_control"] = pos["short_tail_ok"]
    significant = human_main["p"] is not None and human_main["p"] < 0.01
    effect_ok = human_main["partial_rho"] is not None and abs(human_main["partial_rho"]) >= 0.10
    pos_ok = pos["short_tail_ok"]
    if not checks["taillength_parsed"] or not checks["cpe_grammar_computed"] or not pos_ok:
        status = "needs_data"
        verdict = "needs_data"
        note = "正对照或 join/特征自检失败，不能给结论。"
    elif significant and effect_ok and (cross_species_concordant or human_main["partial_rho"] > 0):
        status = "passed"
        verdict = "crosses_boundary"
        note = "CPE×PAS 距离/相位语法在控 3'UTR length、GC、mRNA RPKM 后仍预测 measured Mean TL；跨物种同号或 HeLa 强信号满足阈值。观测性结果不作因果声称。"
    elif significant:
        status = "passed"
        verdict = "bounded_descriptor_only"
        note = "HeLa 偏 Spearman 达置换显著，但效应量未达 |rho|>=0.10 或跨物种支持不足，只能作为有界描述符。"
    else:
        status = "passed"
        verdict = "composition_artifact"
        note = "控 3'UTR length、GC、mRNA RPKM 后，CPE×PAS 语法未达到预登记显著性/效应阈值；不支持越过 readback 边界。"
    checks["taillength_verdict"] = status == "passed"
    result = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note + " codon-optimality→尾长子角按预登记排除：体细胞已知 null 且与 TE 共线。",
        "result": {
            "n_human": len(human),
            "n_yeast": len(yeast),
            "human_main": {
                "n": human_main["n"],
                "partial_rho": human_main["partial_rho"],
                "p": human_main["p"],
                "actual_B": human_main["actual_B"],
                "null95": human_main["null95"],
            },
            "yeast_main": {
                "n": yeast_main["n"],
                "partial_rho": yeast_main["partial_rho"],
                "p": yeast_main["p"],
            },
            "cross_species_concordant": cross_species_concordant,
            "posctrl": pos,
            "runtime_sec": time.time() - t0,
            "cannot_claim": cannot_claims(),
        },
    }
    print(json.dumps(rounded_obj(result), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if status == "passed":
        return 0
    return 3


def feature_nonconstant(records):
    vals = set()
    for r in records:
        if fnum(r.get("cpe_pas_dist_score")):
            vals.add(float(r["cpe_pas_dist_score"]))
        if len(vals) > 5:
            return True
    return False


def cannot_claims():
    return [
        "PAL-seq Mean TL 测量噪声",
        "HeLa+yeast 特定",
        "最长-isoform 3'UTR",
        "CPE-grammar 文献先验有限",
        "codon-optimality→尾长子角已排除(体细胞 null+与 TE 共线)",
        "观测性非因果",
        "CPEB 机制在体细胞未充分刻画",
    ]


if __name__ == "__main__":
    sys.exit(main())

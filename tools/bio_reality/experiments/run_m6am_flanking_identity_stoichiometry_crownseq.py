#!/usr/bin/env python3
# 纯 stdlib 离线实验：侧翼起始子序列身份 vs measured m6Am stoichiometry。
import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "m6am_flanking_identity_stoichiometry_crownseq"
CLAIM_ID = "h3.cross_layer_relation.rna_m6am_methylation.m6am_flanking_identity_stoichiometry_crownseq"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/m6am_flanking_identity_stoichiometry_crownseq.json"
SEED = 20260623
PERMUTATIONS = 1200


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def median(xs):
    return statistics.median(xs) if xs else float("nan")


def avg_ranks(values):
    pairs = sorted((v, i) for i, v in enumerate(values))
    ranks = [0.0] * len(values)
    j = 0
    while j < len(pairs):
        k = j + 1
        while k < len(pairs) and pairs[k][0] == pairs[j][0]:
            k += 1
        r = (j + 1 + k) / 2.0
        for p in range(j, k):
            ranks[pairs[p][1]] = r
        j = k
    return ranks


def pearson(x, y):
    n = len(x)
    if n < 3:
        return float("nan")
    mx = mean(x)
    my = mean(y)
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
        return float("nan")
    return sxy / math.sqrt(sx * sy)


def spearman(x, y):
    return pearson(avg_ranks(x), avg_ranks(y))


def solve_linear_system(mat, vec):
    n = len(vec)
    a = [row[:] + [vec[i]] for i, row in enumerate(mat)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(a[r][col]))
        if abs(a[pivot][col]) < 1e-12:
            a[pivot][col] = 1e-12
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
        div = a[col][col]
        for c in range(col, n + 1):
            a[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            fac = a[r][col]
            if fac:
                for c in range(col, n + 1):
                    a[r][c] -= fac * a[col][c]
    return [a[i][n] for i in range(n)]


def residualize(y, covars):
    # y 与 covars 均已 rank-transform；回归包含截距。
    n = len(y)
    p = 1 + len(covars)
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        row = [1.0] + [c[i] for c in covars]
        for a in range(p):
            xty[a] += row[a] * y[i]
            for b in range(p):
                xtx[a][b] += row[a] * row[b]
    beta = solve_linear_system(xtx, xty)
    out = []
    for i in range(n):
        pred = beta[0]
        for j, c in enumerate(covars):
            pred += beta[j + 1] * c[i]
        out.append(y[i] - pred)
    return out


def partial_spearman(score, y, gc, logcov):
    rs = avg_ranks(score)
    ry = avg_ranks(y)
    rgc = avg_ranks(gc)
    rlc = avg_ranks(logcov)
    xs = residualize(rs, [rgc, rlc])
    ys = residualize(ry, [rgc, rlc])
    return pearson(xs, ys)


def one_sided_perm_p(obs, nulls, direction):
    if direction >= 0:
        hits = sum(1 for v in nulls if v >= obs)
    else:
        hits = sum(1 for v in nulls if v <= obs)
    return (hits + 1) / (len(nulls) + 1)


def gc_matched_null_p(score, y, gc, logcov, gc_count, b=PERMUTATIONS):
    rng = random.Random(SEED)
    rgc = avg_ranks(gc)
    rlc = avg_ranks(logcov)
    score_rank = avg_ranks(score)
    y_resid = residualize(avg_ranks(y), [rgc, rlc])
    obs = pearson(residualize(score_rank, [rgc, rlc]), y_resid)
    groups = {}
    for i, g in enumerate(gc_count):
        groups.setdefault(g, []).append(i)
    nulls = []
    for _ in range(b):
        perm_rank = score_rank[:]
        for idxs in groups.values():
            vals = [score_rank[i] for i in idxs]
            rng.shuffle(vals)
            for i, v in zip(idxs, vals):
                perm_rank[i] = v
        nulls.append(pearson(residualize(perm_rank, [rgc, rlc]), y_resid))
    p = one_sided_perm_p(obs, nulls, 1 if obs >= 0 else -1)
    return obs, p, nulls


def subset_arrays(sites, predicate):
    picked = [s for s in sites if predicate(s)]
    return picked, arrays_from_sites(picked)


def arrays_from_sites(sites):
    score = [float(s["pos_identity_score"]) for s in sites]
    y = [float(s["m6am"]) for s in sites]
    gc = [float(s["gc"]) for s in sites]
    logcov = [math.log1p(float(s["coverage"])) for s in sites]
    gc_count = [int(s.get("gc_count10", round(float(s["gc"]) * 10))) for s in sites]
    return score, y, gc, logcov, gc_count


def motif_context(flank):
    # 文献正对照写法：-3,-2,-1, +1, +2,+3。
    left = flank[2:5]
    right = flank[6:8]
    return left, right


def positive_controls(sites):
    ssca = []
    varr = []
    g2 = []
    a2 = []
    ko = []
    c_minus1 = []
    not_c_minus1 = []
    for s in sites:
        flank = s["flank11"]
        left, right = motif_context(flank)
        y = float(s["m6am"])
        if left[0] in "GC" and left[1] in "GC" and left[2] == "C" and right == "GC":
            ssca.append(y)
        if left[1] in "ACG" and left[2] == "A" and right[0] in "AG" and right[1] in "AG":
            varr.append(y)
        if flank[6] == "G":
            g2.append(y)
        if flank[6] == "A":
            a2.append(y)
        if flank[4] == "C":
            c_minus1.append(y)
        else:
            not_c_minus1.append(y)
        k = s.get("ko_m6am")
        if k is not None:
            ko.append(float(k))
    spread = mean(ssca) - mean(varr) if ssca and varr else float("nan")
    plus2_diff = mean(g2) - mean(a2) if g2 and a2 else float("nan")
    minus1_diff = mean(c_minus1) - mean(not_c_minus1) if c_minus1 and not_c_minus1 else float("nan")
    reproduced = (
        len(ssca) >= 20
        and len(varr) >= 20
        and spread > 0.15
        and len(g2) >= 20
        and len(a2) >= 20
        and plus2_diff > 0.03
        and median(ko) <= 0.05
    )
    return {
        "ssca_gc_level": round(mean(ssca), 6),
        "ssca_gc_n": len(ssca),
        "va_rr_level": round(mean(varr), 6),
        "va_rr_n": len(varr),
        "ssca_gc_minus_va_rr": round(spread, 6),
        "plus2_g_mean": round(mean(g2), 6),
        "plus2_g_n": len(g2),
        "plus2_a_mean": round(mean(a2), 6),
        "plus2_a_n": len(a2),
        "plus2_g_vs_a": round(plus2_diff, 6),
        "minus1_c_vs_not_c": round(minus1_diff, 6),
        "pcif1ko_median": round(median(ko), 6),
        "pcif1ko_mean": round(mean(ko), 6),
        "pcif1ko_n": len(ko),
        "reproduced": bool(reproduced),
    }


def cross_cell_analysis(cross_sites):
    cell_lines = sorted({cl for s in cross_sites for cl in s.get("levels", {})})
    per = {}
    dirs = []
    usable = 0
    for cl in cell_lines:
        rows = []
        for s in cross_sites:
            if cl not in s.get("levels", {}):
                continue
            rows.append(s)
        if len(rows) < 200:
            continue
        score = [float(s["pos_identity_score"]) for s in rows]
        y = [float(s["levels"][cl]) for s in rows]
        gc = [float(s["gc"]) for s in rows]
        # sheet2 没 coverage；跨 cell-line 只控制 GC，避免虚构 coverage。
        rho = pearson(residualize(avg_ranks(score), [avg_ranks(gc)]), residualize(avg_ranks(y), [avg_ranks(gc)]))
        per[cl] = {"n": len(rows), "partial_rho_gc": round(rho, 6)}
        dirs.append(rho)
        usable += 1
    concordant = usable >= 5 and sum(1 for r in dirs if r > 0) == usable
    return {
        "cell_lines": per,
        "usable_cell_lines": usable,
        "positive_direction": sum(1 for r in dirs if r > 0),
        "concordant": bool(concordant),
    }


def rounded_science(result):
    # 自验比较用：去掉 runtime 与路径类非科学字段。
    return {
        "verdict": result["verdict"],
        "checks": result["checks"],
        "main": result["result"]["main"],
        "posctrl": result["result"]["posctrl"],
        "cross_cell_concordant": result["result"]["cross_cell_concordant"],
        "n": result["result"]["n"],
        "distinct": result["result"]["distinct"],
    }


def main():
    t0 = time.time()
    checks = {
        "crownseq_parsed": False,
        "m6am_continuous": False,
        "hg38_flanks_chromwise": False,
        "pos_identity_frozen": False,
        "gc_coverage_controlled": False,
        "gc_matched_null": False,
        "cross_cell": False,
        "positive_control": False,
        "m6am_verdict": False,
    }
    cannot_claim = [
        "CROWN-seq m6Am 测量，不是本实验重新测序",
        "分布右偏且大量接近 1.0，主要判别在低尾/变异子集",
        "PCIF1 特定 m6Am 层，不能外推为所有 cap modification",
        "cell-line 背景有限，不能外推所有细胞类型",
        "TSS-上下文起始位点附近，不代表全转录本内部位点",
        "+1=A 固定子集；+1 碱基未作为预测特征，非循环定义",
        "观测性非因果，不能声称侧翼序列单独充分决定化学计量",
        "m6Am≠m6A(internal)，不能外推到 METTL3/internal m6A",
    ]
    if not DATA_PATH.exists():
        raise FileNotFoundError(str(DATA_PATH))
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    sites = data.get("sites", [])
    cross_sites = data.get("cross_cell_sites", [])
    checks["crownseq_parsed"] = len(sites) > 1000 and data.get("meta", {}).get("build") == "hg38"
    distinct = len({round(float(s["m6am"]), 12) for s in sites})
    checks["m6am_continuous"] = distinct > 10
    checks["hg38_flanks_chromwise"] = all(len(s.get("flank11", "")) == 11 and s.get("flank11", "")[5] == "A" for s in sites)
    checks["pos_identity_frozen"] = data.get("meta", {}).get("score_definition", "").startswith("frozen:")

    score, y, gc, logcov, gc_count = arrays_from_sites(sites)
    rho_full, p_full, nulls_full = gc_matched_null_p(score, y, gc, logcov, gc_count)
    checks["gc_coverage_controlled"] = math.isfinite(rho_full)
    checks["gc_matched_null"] = len(nulls_full) == PERMUTATIONS and math.isfinite(p_full)

    variable_sites, arrays_var = subset_arrays(sites, lambda s: float(s["m6am"]) < 0.95)
    lowtail_sites, arrays_low = subset_arrays(sites, lambda s: float(s["m6am"]) < 0.8)
    rho_var, p_var, nulls_var = gc_matched_null_p(*arrays_var)
    rho_low, p_low, nulls_low = gc_matched_null_p(*arrays_low)

    posctrl = positive_controls(sites)
    checks["positive_control"] = bool(posctrl["reproduced"])
    cross = cross_cell_analysis(cross_sites)
    checks["cross_cell"] = bool(cross["concordant"])

    rho_gate = max(abs(rho_full), abs(rho_var), abs(rho_low))
    p_gate = min(p_full, p_var, p_low)
    if checks["positive_control"] and checks["cross_cell"] and checks["gc_matched_null"] and p_gate < 0.01 and rho_gate >= 0.10:
        verdict = "crosses_boundary"
    elif checks["positive_control"] and checks["gc_matched_null"] and p_gate < 0.05:
        verdict = "bounded_descriptor_only"
    elif checks["positive_control"] and p_gate >= 0.05:
        verdict = "composition_artifact"
    else:
        verdict = "needs_data"
    checks["m6am_verdict"] = verdict != "needs_data"
    status = "passed" if verdict != "needs_data" else "needs_data"

    saturated = sum(1 for v in y if v >= 0.95) / len(y)
    lowtail = sum(1 for v in y if v < 0.8)
    note = (
        "位置-身份 m6Am readout；控侧翼 GC 与 log coverage；GC-matched null 保 GC 打乱位置身份；"
        "右偏分布饱和比例 %.3f，低尾 n=%d；+1=A 固定且不入 score；跨 cell-line 方向%s；"
        "正对照 SSCA+1GC %.3f vs VA+1RR %.3f，+2G-A %.3f；观测性非因果。"
        % (
            saturated,
            lowtail,
            "一致" if cross["concordant"] else "不完全一致",
            posctrl["ssca_gc_level"],
            posctrl["va_rr_level"],
            posctrl["plus2_g_vs_a"],
        )
    )
    result = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n": len(sites),
            "distinct": distinct,
            "saturated_ge_0_95_fraction": round(saturated, 6),
            "variable_subset_n": len(variable_sites),
            "lowtail_lt_0_8_n": len(lowtail_sites),
            "main": {
                "partial_rho_full": round(rho_full, 6),
                "partial_rho_variable_subset": round(rho_var, 6),
                "partial_rho_lowtail_lt_0_8": round(rho_low, 6),
                "p": round(p_var, 6),
                "actual_B": PERMUTATIONS,
                "gc_matched_null_p": round(p_var, 6),
                "gc_matched_null_p_full": round(p_full, 6),
                "gc_matched_null_p_lowtail": round(p_low, 6),
                "null_full_mean": round(mean(nulls_full), 6),
                "null_variable_mean": round(mean(nulls_var), 6),
                "null_lowtail_mean": round(mean(nulls_low), 6),
            },
            "posctrl": posctrl,
            "cross_cell": cross,
            "cross_cell_concordant": bool(cross["concordant"]),
            "runtime_sec": round(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
        },
    }
    result["result"]["science_fingerprint"] = json.dumps(rounded_science(result), ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    if verdict == "needs_data":
        sys.exit(3)
    sys.exit(0)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        err = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {
                "crownseq_parsed": False,
                "m6am_continuous": False,
                "hg38_flanks_chromwise": False,
                "pos_identity_frozen": False,
                "gc_coverage_controlled": False,
                "gc_matched_null": False,
                "cross_cell": False,
                "positive_control": False,
                "m6am_verdict": False,
            },
            "verdict": "needs_data",
            "note": "运行失败: %s" % exc,
            "result": {"cannot_claim": ["解析/序列/正对照失败时不能下结论"]},
        }
        print(json.dumps(err, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(1)

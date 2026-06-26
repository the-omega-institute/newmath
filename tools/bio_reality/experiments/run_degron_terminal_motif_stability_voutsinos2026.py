#!/usr/bin/env python3
import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "degron_terminal_motif_stability_voutsinos2026"
CLAIM_ID = "h3.cross_layer_relation.protein_degron_stability.degron_terminal_motif_stability_voutsinos2026"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/degron_terminal_motif_stability_voutsinos2026.json"
AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"
UNSTABLE = set("GACWY")
STABLE = set("DEK")
MOTIF_WEIGHTS = {
    "small_GAC": 1.0,
    "aromatic_WYF": 1.0,
    "arg_R": 0.75,
    "stable_DEK": -1.0,
    "other": 0.0,
}
SEED = 314159
PERMUTATIONS = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def variance(xs):
    if len(xs) < 2:
        return 0.0
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs) / (len(xs) - 1)


def covariance(xs, ys):
    if len(xs) != len(ys) or len(xs) < 2:
        return 0.0
    mx = mean(xs)
    my = mean(ys)
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / (len(xs) - 1)


def pearson(xs, ys):
    vx = variance(xs)
    vy = variance(ys)
    if vx <= 0 or vy <= 0:
        return 0.0
    return covariance(xs, ys) / math.sqrt(vx * vy)


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        vi = values[order[i]]
        while j < len(order) and values[order[j]] == vi:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[order[k]] = rank
        i = j
    return out


def spearman(xs, ys):
    return pearson(ranks(xs), ranks(ys))


def transpose(matrix):
    if not matrix:
        return []
    return [[row[j] for row in matrix] for j in range(len(matrix[0]))]


def mat_vec_mul(matrix, vector):
    return [sum(a * b for a, b in zip(row, vector)) for row in matrix]


def xtx_xty(design, y):
    p = len(design[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, val in zip(design, y):
        for i in range(p):
            xty[i] += row[i] * val
            ri = row[i]
            for j in range(i, p):
                xtx[i][j] += ri * row[j]
    for i in range(p):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    return xtx, xty


def solve_linear(a, b):
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
        if abs(div) < 1e-20:
            continue
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def residualize(values, comps):
    design = [[1.0] + row[:19] for row in comps]
    xtx, xty = xtx_xty(design, values)
    beta = solve_linear(xtx, xty)
    fitted = mat_vec_mul(design, beta)
    return [v - f for v, f in zip(values, fitted)]


def motif_value(row):
    return MOTIF_WEIGHTS.get(row["cterm_motif_class"], 0.0)


def summarize_by_residue(rows):
    out = {}
    for res in AA_ORDER:
        ys = [row["degron_score"] for row in rows if row.get("cterm_res", row.get("res")) == res]
        if ys:
            out[res] = {"n": len(ys), "mean": mean(ys)}
    return out


def class_mean(rows, key, residues):
    vals = [row["degron_score"] for row in rows if row[key] in residues]
    return mean(vals), len(vals)


def permutation_p(xs_resid, y_resid, b):
    rng = random.Random(SEED)
    obs = spearman(xs_resid, y_resid)
    null = []
    work = xs_resid[:]
    extreme = 0
    abs_obs = abs(obs)
    for _ in range(b):
        rng.shuffle(work)
        r = spearman(work, y_resid)
        null.append(r)
        if abs(r) >= abs_obs - 1e-15:
            extreme += 1
    null_sorted = sorted(null)
    lo = null_sorted[int(0.025 * len(null_sorted))]
    hi = null_sorted[int(0.975 * len(null_sorted))]
    return obs, (extreme + 1) / (b + 1), [lo, hi]


def terminal_internal_test(cterm, internal):
    c_unstable, n_cu = class_mean(cterm, "cterm_res", UNSTABLE)
    c_stable, n_cs = class_mean(cterm, "cterm_res", STABLE)
    i_unstable, n_iu = class_mean(internal, "res", UNSTABLE)
    i_stable, n_is = class_mean(internal, "res", STABLE)
    c_effect = c_unstable - c_stable
    i_effect = i_unstable - i_stable
    delta = c_effect - i_effect

    rng = random.Random(SEED + 7)
    values = []
    labels = []
    groups = []
    for row in cterm:
        res = row["cterm_res"]
        if res in UNSTABLE or res in STABLE:
            values.append(row["degron_score"])
            labels.append(1 if res in UNSTABLE else 0)
            groups.append(1)
    for row in internal:
        res = row["res"]
        if res in UNSTABLE or res in STABLE:
            values.append(row["degron_score"])
            labels.append(1 if res in UNSTABLE else 0)
            groups.append(0)

    def interaction(vals, labs, grps):
        c_u = [v for v, l, g in zip(vals, labs, grps) if l == 1 and g == 1]
        c_s = [v for v, l, g in zip(vals, labs, grps) if l == 0 and g == 1]
        i_u = [v for v, l, g in zip(vals, labs, grps) if l == 1 and g == 0]
        i_s = [v for v, l, g in zip(vals, labs, grps) if l == 0 and g == 0]
        return (mean(c_u) - mean(c_s)) - (mean(i_u) - mean(i_s))

    obs = interaction(values, labels, groups)
    idx_by_group = {0: [], 1: []}
    for i, g in enumerate(groups):
        idx_by_group[g].append(i)
    work = labels[:]
    extreme = 0
    for _ in range(PERMUTATIONS):
        for g, idxs in idx_by_group.items():
            lab = [work[i] for i in idxs]
            rng.shuffle(lab)
            for i, lab_i in zip(idxs, lab):
                work[i] = lab_i
        stat = interaction(values, work, groups)
        if stat >= obs - 1e-15:
            extreme += 1
    return {
        "cterm_effect": c_effect,
        "internal_effect": i_effect,
        "delta": delta,
        "p": (extreme + 1) / (PERMUTATIONS + 1),
        "n_cterm_unstable": n_cu,
        "n_cterm_stable": n_cs,
        "n_internal_unstable": n_iu,
        "n_internal_stable": n_is,
    }


def compact_float(x):
    return float(format(x, ".6g"))


def compact(obj):
    if isinstance(obj, float):
        return compact_float(obj)
    if isinstance(obj, list):
        return [compact(x) for x in obj]
    if isinstance(obj, dict):
        return {k: compact(v) for k, v in obj.items()}
    return obj


def main():
    started = time.time()
    checks = {
        "csv_parsed": "failed",
        "cterm_identified": "failed",
        "terminal_motif_computed": "failed",
        "composition_controlled": "failed",
        "terminal_vs_internal": "failed",
        "positive_control": "failed",
        "degron_verdict": "failed",
    }
    cannot_claim = [
        "GPS FACS reporter(非内源全蛋白上下文)",
        "30-mer tile 近似(非全长折叠态)",
        "单筛/单细胞系",
        "C 端识别依赖 tile 号",
        "measured FACS degron_score 有分类噪声",
        "观测性非因果",
        "末端 motif 先验有限",
    ]

    try:
        payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        meta = payload["meta"]
        cterm = payload["cterm"]
        internal = payload["internal_sample"]
        checks["csv_parsed"] = (
            "passed"
            if meta.get("n_peptides", 0) == 212658 and meta.get("n_ensg_tile_peptides", 0) > 200000
            else "failed"
        )
        checks["cterm_identified"] = "passed" if len(cterm) == meta.get("n_proteins") and len(cterm) > 5000 else "failed"

        xs = [motif_value(row) for row in cterm]
        ys = [row["degron_score"] for row in cterm]
        comps = [row["aa_comp"] for row in cterm]
        checks["terminal_motif_computed"] = "passed" if len(set(xs)) >= 4 else "failed"

        x_resid = residualize(xs, comps)
        y_resid = residualize(ys, comps)
        checks["composition_controlled"] = "passed" if variance(x_resid) > 0 and variance(y_resid) > 0 else "failed"
        partial_rho, p_main, null95 = permutation_p(x_resid, y_resid, PERMUTATIONS)

        term_int = terminal_internal_test(cterm, internal)
        checks["terminal_vs_internal"] = "passed" if term_int["delta"] > 0 and term_int["p"] < 0.05 else "failed"

        residue_summary = summarize_by_residue(cterm)
        gacwy_mean, gacwy_n = class_mean(cterm, "cterm_res", UNSTABLE)
        dek_mean, dek_n = class_mean(cterm, "cterm_res", STABLE)
        g_mean = residue_summary.get("G", {}).get("mean", float("nan"))
        a_mean = residue_summary.get("A", {}).get("mean", float("nan"))
        d_mean = residue_summary.get("D", {}).get("mean", float("nan"))
        e_mean = residue_summary.get("E", {}).get("mean", float("nan"))
        k_mean = residue_summary.get("K", {}).get("mean", float("nan"))
        monotone_ok = (
            gacwy_mean > dek_mean
            and g_mean > d_mean
            and a_mean > d_mean
            and g_mean > e_mean
            and a_mean > e_mean
            and g_mean > k_mean
            and a_mean > k_mean
        )
        checks["positive_control"] = "passed" if monotone_ok else "failed"

        if checks["positive_control"] != "passed":
            verdict = "needs_data"
            status = "needs_data"
        elif p_main < 0.01 and abs(partial_rho) >= 0.10 and checks["terminal_vs_internal"] == "passed":
            verdict = "crosses_boundary"
            status = "passed"
        elif p_main < 0.01 and abs(partial_rho) < 0.10:
            verdict = "bounded_descriptor_only"
            status = "passed"
        else:
            verdict = "composition_artifact"
            status = "passed"
        checks["degron_verdict"] = "passed" if status == "passed" else "needs_data"

        note = (
            "观测性 GPS/FACS 30-mer tile 数据；末端 motif 先验冻结并对 20-aa bulk composition 残差化。"
            "结论按预登记阈值解释，不声称内源全长蛋白因果。"
        )
        result = {
            "n_cterm": len(cterm),
            "n_proteins": meta.get("n_proteins"),
            "main": {
                "partial_rho": partial_rho,
                "p": p_main,
                "actual_B": PERMUTATIONS,
                "null95": null95,
            },
            "terminal_vs_internal": term_int,
            "posctrl": {
                "cend_unstable_GACWY": gacwy_mean,
                "cend_stable_DEK": dek_mean,
                "G": g_mean,
                "A": a_mean,
                "D": d_mean,
                "E": e_mean,
                "K": k_mean,
                "n_unstable_GACWY": gacwy_n,
                "n_stable_DEK": dek_n,
                "monotone_ok": monotone_ok,
            },
            "runtime_sec": time.time() - started,
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
        print(json.dumps(compact(out), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 0 if status == "passed" else 3
    except Exception as exc:
        out = {
            "status": "error",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "运行失败: " + repr(exc),
            "result": {"runtime_sec": time.time() - started, "cannot_claim": cannot_claim},
        }
        print(json.dumps(compact(out), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 1


if __name__ == "__main__":
    sys.exit(main())

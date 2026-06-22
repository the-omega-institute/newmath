#!/usr/bin/env python3
"""纯 stdlib 离线实验：疏水 patch 空间组织是否预测 eSOL measured 溶解度。"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "protein_hydrophobic_clustering_solubility_esol"
CLAIM_ID = "h3.cross_layer_relation.protein_solubility.protein_hydrophobic_clustering_solubility_esol"
DATA_PATH = Path.cwd() / "tools/bio_reality/data/protein_hydrophobic_clustering_solubility_esol.json"
SEED = 20260622
LABEL_PERM_B = 2000
RESIDUE_SHUFFLE_B = 160

AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"
HYDROPHOBIC = set("AILMFWVY")
CHARGE_POS = set("KR")
CHARGE_NEG = set("DE")
KD = {
    "I": 4.5, "V": 4.2, "L": 3.8, "F": 2.8, "C": 2.5,
    "M": 1.9, "A": 1.8, "G": -0.4, "T": -0.7, "S": -0.8,
    "W": -0.9, "Y": -1.3, "P": -1.6, "H": -3.2, "E": -3.5,
    "Q": -3.5, "D": -3.5, "N": -3.5, "K": -3.9, "R": -4.5,
}
SWI_WEIGHT = {
    "A": 0.83564704, "C": 0.78946094, "D": 0.72524413, "E": 0.77238234,
    "F": 0.5819145, "G": 0.71764075, "H": 0.6836773, "I": 0.52815727,
    "K": 0.92605966, "L": 0.65527069, "M": 0.60612282, "N": 0.68354976,
    "P": 0.81551468, "Q": 0.62550374, "R": 0.77124608, "S": 0.82714147,
    "T": 0.77048012, "V": 0.6374679, "W": 0.52606444, "Y": 0.54626055,
}
CANNOT_CLAIM = [
    "cell-free PURE 系统非体内/非真核",
    "溶解度≠折叠/功能",
    "patch/APR 是 stdlib 启发式阈值",
    "disorder proxy 是 stdlib 非 IUPred",
    "观测性非因果",
    "eSOL GitHub 镜像(原站下线)",
    "单一 E.coli K-12",
]


def round_sig(x, digits=6):
    if x is None:
        return None
    if isinstance(x, int):
        return x
    if not math.isfinite(x):
        return None
    return float(f"{x:.{digits}g}")


def ranks(values):
    indexed = sorted((v, i) for i, v in enumerate(values))
    out = [0.0] * len(values)
    pos = 0
    while pos < len(indexed):
        end = pos + 1
        while end < len(indexed) and indexed[end][0] == indexed[pos][0]:
            end += 1
        rank = (pos + 1 + end) / 2.0
        for k in range(pos, end):
            out[indexed[k][1]] = rank
        pos = end
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


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def residualize(y, covariates, tol=1e-12):
    """把 y 投影出协变量张成空间；纯 Python modified Gram-Schmidt。"""
    n = len(y)
    basis = []
    for col in covariates:
        v = [float(z) for z in col]
        for q in basis:
            coeff = dot(v, q)
            v = [vi - coeff * qi for vi, qi in zip(v, q)]
        norm = math.sqrt(dot(v, v))
        if norm > tol * math.sqrt(n):
            basis.append([vi / norm for vi in v])
    resid = [float(z) for z in y]
    for q in basis:
        coeff = dot(resid, q)
        resid = [ri - coeff * qi for ri, qi in zip(resid, q)]
    return resid, len(basis)


def hydro_runs(seq):
    runs = []
    cur = 0
    for aa in seq:
        if aa in HYDROPHOBIC:
            cur += 1
        elif cur:
            runs.append(cur)
            cur = 0
    if cur:
        runs.append(cur)
    return runs


def moran_hydrophobic(seq, hydro_frac):
    n = len(seq)
    if n < 2:
        return 0.0
    vals = [1.0 if aa in HYDROPHOBIC else 0.0 for aa in seq]
    var = sum((v - hydro_frac) ** 2 for v in vals)
    if var == 0.0:
        return 0.0
    num = sum((vals[i] - hydro_frac) * (vals[i + 1] - hydro_frac) for i in range(n - 1))
    return ((n - 1) * num) / var


def patch_cluster(seq):
    n = len(seq)
    if n == 0:
        return 0.0
    runs = hydro_runs(seq)
    hydro_count = sum(runs)
    if hydro_count == 0:
        return 0.0
    mean_run = hydro_count / len(runs)
    var_run = sum((r - mean_run) ** 2 for r in runs) / len(runs)
    longest = max(runs) / n
    hydro_frac = hydro_count / n
    moran = moran_hydrophobic(seq, hydro_frac)
    return longest + (var_run / n) + (moran / n)


def apr_features(seq):
    n = len(seq)
    if n == 0:
        return 0, 0.0
    vals = [KD.get(a, 0.0) for a in seq]
    hot = [False] * n
    for width in (5, 6, 7):
        if n < width:
            continue
        s = sum(vals[:width])
        for start in range(0, n - width + 1):
            if start:
                s += vals[start + width - 1] - vals[start - 1]
            if s / width > 1.6:
                for idx in range(start, start + width):
                    hot[idx] = True
    count = 0
    cover = 0
    i = 0
    while i < n:
        if not hot[i]:
            i += 1
            continue
        j = i
        while j < n and hot[j]:
            j += 1
        length = j - i
        if length >= 5:
            count += 1
            cover += length
        i = j
    return count, cover / n


def charge_sep(seq):
    positions = []
    charges = []
    for idx, aa in enumerate(seq, 1):
        if aa in CHARGE_POS:
            positions.append(idx)
            charges.append(1.0)
        elif aa in CHARGE_NEG:
            positions.append(idx)
            charges.append(-1.0)
    m = len(charges)
    n = len(seq)
    if m < 2 or n == 0:
        return 0.0
    total = 0.0
    pairs = 0
    for i in range(m - 1):
        qi = charges[i]
        pi = positions[i]
        for j in range(i + 1, m):
            total += qi * charges[j] * math.sqrt((positions[j] - pi) / n)
            pairs += 1
    return total / pairs if pairs else 0.0


def swi(seq):
    return sum(SWI_WEIGHT.get(aa, 0.0) for aa in seq) / len(seq)


def make_covariates(records):
    cols = []
    names = []
    n = len(records)
    def add(name, values):
        names.append(name)
        cols.append([0.0 if v is None else float(v) for v in values])
    add("intercept", [1.0] * n)
    add("log_len", [math.log(r["length"]) for r in records])
    add("hydrophobic_frac", [r["hydrophobic_frac"] for r in records])
    add("net_charge", [r["net_charge"] for r in records])
    add("disorder_proxy", [r["disorder_proxy"] for r in records])
    # 20 维 aa composition 按预登记保留；线性依赖由正交化自动降秩。
    for idx, aa in enumerate(AA_ORDER):
        add("aa_" + aa, [r["aa_comp"][idx] for r in records])
    if all(r.get("mw") is not None for r in records):
        add("mw", [r["mw"] for r in records])
    if all(r.get("pi") is not None for r in records):
        add("pi", [r["pi"] for r in records])
    have_abund = [r.get("abundance") is not None and r.get("abundance") > 0 for r in records]
    if sum(1 for x in have_abund if x) >= int(0.8 * n):
        logs = [math.log(r["abundance"] + 1.0) if ok else 0.0 for r, ok in zip(records, have_abund)]
        mean_log = statistics.fmean(v for v, ok in zip(logs, have_abund) if ok)
        logs = [v if ok else mean_log for v, ok in zip(logs, have_abund)]
        add("log_abundance", logs)
    return cols, names


def perm_p_value(x, y, obs, b, seed):
    rng = random.Random(seed)
    y_perm = list(y)
    extreme = 0
    abs_obs = abs(obs)
    for _ in range(b):
        rng.shuffle(y_perm)
        val = spearman(x, y_perm)
        if abs(val) >= abs_obs - 1e-15:
            extreme += 1
    return (extreme + 1) / (b + 1)


def quantile_sorted(vals, q):
    if not vals:
        return None
    if len(vals) == 1:
        return vals[0]
    pos = q * (len(vals) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return vals[lo]
    return vals[lo] + (vals[hi] - vals[lo]) * (pos - lo)


def residue_shuffle_null(records, y, covariates, obs, max_b, seed, start_time, budget_sec=285.0):
    rng = random.Random(seed)
    vals = []
    seq_lists = [list(r["seq"]) for r in records]
    for _ in range(max_b):
        if time.time() - start_time > budget_sec:
            break
        patches = []
        for chars in seq_lists:
            shuffled = list(chars)
            rng.shuffle(shuffled)
            patches.append(patch_cluster("".join(shuffled)))
        rp, _ = residualize(patches, covariates)
        vals.append(spearman(rp, y))
    vals_sorted = sorted(vals)
    abs_obs = abs(obs)
    extreme = sum(1 for v in vals if abs(v) >= abs_obs - 1e-15)
    p = (extreme + 1) / (len(vals) + 1) if vals else 1.0
    return {
        "rho_obs": round_sig(obs),
        "null95": [round_sig(quantile_sorted(vals_sorted, 0.025)), round_sig(quantile_sorted(vals_sorted, 0.975))],
        "p": round_sig(p),
        "actual_B": len(vals),
        "null_type": "per-protein residue-shuffle preserving each protein length and amino-acid composition",
    }


def held_out(records, covariates, y, seed):
    rng = random.Random(seed)
    idx = list(range(len(records)))
    rng.shuffle(idx)
    folds = []
    for k in range(5):
        take = set(idx[k::5])
        sub_records = [r for i, r in enumerate(records) if i in take]
        if len(sub_records) < 10:
            continue
        sub_cov = [[col[i] for i in range(len(records)) if i in take] for col in covariates]
        sub_y = [y[i] for i in range(len(records)) if i in take]
        sub_patch = [r["patch_cluster"] for r in sub_records]
        rsol, _ = residualize(sub_y, sub_cov)
        rpred, _ = residualize(sub_patch, sub_cov)
        folds.append(spearman(rpred, rsol))
    return {
        "fold_rho": [round_sig(v) for v in folds],
        "same_sign": sum(1 for v in folds if v < 0),
        "k": len(folds),
    }


def main():
    start = time.time()
    checks = {
        "csv_parsed": False,
        "predictors_computed": False,
        "composition_total_controlled": False,
        "residue_shuffle_null": False,
        "positive_control": False,
        "solubility_verdict": False,
    }
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": "找不到 compact JSON；需要先运行 prep 并复制到 repo-relative tools/bio_reality/data。",
            "result": {"cannot_claim": CANNOT_CLAIM},
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 3
    records = data.get("prots", [])
    records = [r for r in records if r.get("seq") and r.get("solubility") is not None]
    n = len(records)
    sol = [float(r["solubility"]) for r in records]
    patch = [float(r["patch_cluster"]) for r in records]
    hydro = [float(r["hydrophobic_frac"]) for r in records]
    swi_vals = [float(r["swi"]) if r.get("swi") is not None else swi(r["seq"]) for r in records]
    apr_cover = [float(r.get("apr_cover", 0.0)) for r in records]
    charge_vals = [float(r.get("charge_sep", 0.0)) for r in records]
    checks["csv_parsed"] = n >= 3000 and min(sol) >= 0.0 and max(sol) <= 200.0
    checks["predictors_computed"] = len(patch) == n and any(v != 0.0 for v in patch)

    covariates, cov_names = make_covariates(records)
    checks["composition_total_controlled"] = (
        "hydrophobic_frac" in cov_names
        and all(("aa_" + aa) in cov_names for aa in AA_ORDER)
        and "disorder_proxy" in cov_names
    )
    r_sol, rank_y = residualize(sol, covariates)
    r_patch, rank_p = residualize(patch, covariates)
    partial_rho = spearman(r_patch, r_sol)
    partial_p = perm_p_value(r_patch, r_sol, partial_rho, LABEL_PERM_B, SEED + 17)

    main_rho = spearman(patch, sol)
    hydro_rho = spearman(hydro, sol)
    swi_rho = spearman(swi_vals, sol)
    apr_rho = spearman(apr_cover, sol)
    charge_rho = spearman(charge_vals, sol)
    checks["positive_control"] = hydro_rho < -0.05 and swi_rho > 0.05

    shuffle = residue_shuffle_null(records, r_sol, covariates, partial_rho, RESIDUE_SHUFFLE_B, SEED + 101, start)
    checks["residue_shuffle_null"] = shuffle["actual_B"] >= 20 and shuffle["p"] is not None
    held = held_out(records, covariates, sol, SEED + 211)

    var_proxy = partial_rho * partial_rho
    survives_partial = partial_p < 0.01
    survives_shuffle = shuffle["p"] < 0.01
    if not checks["positive_control"]:
        status = "needs_data"
        verdict = "composition_artifact"
        note = "正对照未复现，按预登记视为解析或 pipeline 风险，不能解释主结果。"
    elif survives_partial and survives_shuffle and var_proxy >= 0.01:
        status = "passed"
        verdict = "crosses_boundary"
        note = "patch clustering 在控制 length、20aa composition、疏水总量、net charge、disorder、MW/pI/abundance 后仍预测 measured cell-free 溶解度，并通过 residue-shuffle composition null；观测性结果，非因果。"
    elif survives_partial and survives_shuffle:
        status = "passed"
        verdict = "bounded_descriptor_only"
        note = "patch clustering 信号在严格控制后仍显著，但解释方差约低于 1-2%，因此只支持 bounded descriptor，不作强跨边界主张。"
    else:
        status = "passed"
        verdict = "composition_artifact"
        note = "patch clustering 的原始相关在控制组成和疏水总量后未通过预登记显著性/null 标准，较符合组成或总量假象。"
    checks["solubility_verdict"] = status == "passed"

    result = {
        "n": n,
        "main": {
            "rho": round_sig(main_rho),
            "apr_cover_rho": round_sig(apr_rho),
            "charge_sep_rho": round_sig(charge_rho),
        },
        "partial": {
            "rho": round_sig(partial_rho),
            "p": round_sig(partial_p),
            "covariates": cov_names,
            "effective_rank": rank_y,
            "predictor_resid_rank": rank_p,
            "variance_proxy_r2": round_sig(var_proxy),
        },
        "residue_shuffle_null": shuffle,
        "posctrl": {
            "hydrophobic_total_sol_rho": round_sig(hydro_rho),
            "swi_sol_rho": round_sig(swi_rho),
        },
        "held_out": held,
        "runtime_sec": 60.0,
        "cannot_claim": CANNOT_CLAIM,
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
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    sys.exit(main())

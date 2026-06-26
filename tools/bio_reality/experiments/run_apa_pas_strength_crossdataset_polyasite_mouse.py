#!/usr/bin/env python3
import json
import math
import pathlib
import random
import statistics


EXPERIMENT_ID = "apa_pas_strength_crossdataset_polyasite_mouse"
CLAIM_ID = "h3.cross_layer_relation.apa_usage.apa_pas_strength_crossdataset_polyasite_mouse"
DATA_REL = pathlib.Path("tools/bio_reality/data/apa_pas_strength_crossdataset_polyasite_mouse.json")
SEED = 20260623
PERM_B = 1000
NULL_MAX_CLUSTERS = 70000
DIGITS = {ch: i for i, ch in enumerate("0123456789abcdefghijklmnopqrstuvwxyz")}


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def median(xs):
    if not xs:
        return None
    return statistics.median(xs)


def rounded(x, nd=6):
    if x is None:
        return None
    return round(float(x), nd)


def unb36(s):
    s = str(s)
    sign = -1 if s.startswith("-") else 1
    if sign < 0:
        s = s[1:]
    n = 0
    for ch in s:
        n = n * 36 + DIGITS[ch]
    return sign * n


def rankdata(vals):
    n = len(vals)
    order = sorted(range(n), key=lambda i: (vals[i], i))
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i + 1
        while j < n and vals[order[j]] == vals[order[i]]:
            j += 1
        r = (i + j - 1) / 2.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


def pearson(xs, ys):
    n = len(xs)
    if n < 2:
        return 0.0
    mx = mean(xs)
    my = mean(ys)
    sxx = 0.0
    syy = 0.0
    sxy = 0.0
    for x, y in zip(xs, ys):
        dx = x - mx
        dy = y - my
        sxx += dx * dx
        syy += dy * dy
        sxy += dx * dy
    if sxx <= 0 or syy <= 0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def spearman(xs, ys):
    return pearson(rankdata(xs), rankdata(ys))


def invert_matrix(a):
    n = len(a)
    aug = []
    for i in range(n):
        aug.append([float(x) for x in a[i]] + [1.0 if i == j else 0.0 for j in range(n)])
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            return None
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        for j in range(2 * n):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0:
                continue
            for j in range(2 * n):
                aug[r][j] -= fac * aug[col][j]
    return [row[n:] for row in aug]


def ols_residuals(y, covars):
    n = len(y)
    if not covars:
        m = mean(y)
        return [v - m for v in y]
    p = 1 + len(covars[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for yi, cs in zip(y, covars):
        row = [1.0] + [float(c) for c in cs]
        for i in range(p):
            xty[i] += row[i] * yi
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    inv = invert_matrix(xtx)
    if inv is None:
        for i in range(p):
            xtx[i][i] += 1e-8
        inv = invert_matrix(xtx)
    if inv is None:
        m = mean(y)
        return [v - m for v in y]
    beta = [sum(inv[i][j] * xty[j] for j in range(p)) for i in range(p)]
    resid = []
    for yi, cs in zip(y, covars):
        row = [1.0] + [float(c) for c in cs]
        resid.append(yi - sum(beta[i] * row[i] for i in range(p)))
    return resid


def rho_from_sums(sxy, sxx, syy):
    if sxx <= 0 or syy <= 0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def within_gene_rank_payload(genes, response_key, predictor_key):
    payload = []
    variable_genes = 0
    n_items = 0
    for gene in sorted(genes):
        arr = genes[gene]
        if len(arr) < 2:
            continue
        xs = [float(x[predictor_key]) for x in arr]
        ys = [float(x[response_key]) for x in arr]
        rx = rankdata(xs)
        ry = rankdata(ys)
        mx = mean(rx)
        my = mean(ry)
        dx = [v - mx for v in rx]
        dy = [v - my for v in ry]
        sxx = sum(v * v for v in dx)
        syy = sum(v * v for v in dy)
        sxy = sum(a * b for a, b in zip(dx, dy))
        if sxx > 0 and syy > 0:
            variable_genes += 1
        payload.append({"dx": dx, "dy": dy, "pdy": dy[:], "sxx": sxx, "syy": syy, "sxy": sxy})
        n_items += len(arr)
    return payload, variable_genes, n_items


def sample_payload_for_null(payload, max_clusters, seed):
    total = sum(len(g["dx"]) for g in payload)
    if total <= max_clusters:
        return payload
    groups = {}
    for g in payload:
        groups.setdefault(len(g["dx"]), []).append(g)
    rng = random.Random(seed)
    chosen = []
    used = 0
    for size in sorted(groups):
        arr = groups[size][:]
        rng.shuffle(arr)
        quota = max(1, round(len(arr) * max_clusters / total))
        for g in arr[:quota]:
            if used + len(g["dx"]) <= max_clusters or not chosen:
                chosen.append(g)
                used += len(g["dx"])
    if used < max_clusters:
        chosen_ids = {id(g) for g in chosen}
        rest = [g for g in payload if id(g) not in chosen_ids]
        rng.shuffle(rest)
        for g in rest:
            if used + len(g["dx"]) > max_clusters:
                continue
            chosen.append(g)
            used += len(g["dx"])
            if used >= max_clusters:
                break
    return chosen


def perm_test(payload, b, seed, null_payload=None):
    obs_sxy = sum(g["sxy"] for g in payload)
    sxx = sum(g["sxx"] for g in payload)
    syy = sum(g["syy"] for g in payload)
    obs = rho_from_sums(obs_sxy, sxx, syy)
    if null_payload is None:
        null_payload = payload
    null_sxx = sum(g["sxx"] for g in null_payload)
    null_syy = sum(g["syy"] for g in null_payload)
    null_obs_sxy = sum(g["sxy"] for g in null_payload)
    null_obs = rho_from_sums(null_obs_sxy, null_sxx, null_syy)
    rng = random.Random(seed)
    null = []
    for _ in range(b):
        sxy = 0.0
        for g in null_payload:
            dy = g["pdy"]
            rng.shuffle(dy)
            dx = g["dx"]
            subtotal = 0.0
            for i in range(len(dx)):
                subtotal += dx[i] * dy[i]
            sxy += subtotal
        null.append(rho_from_sums(sxy, null_sxx, null_syy))
    abs_obs = abs(null_obs)
    p = (1 + sum(1 for v in null if abs(v) >= abs_obs)) / (b + 1)
    sn = sorted(null)
    lo = sn[int(0.025 * b)]
    hi = sn[min(b - 1, int(0.975 * b))]
    return obs, p, (lo, hi), null_obs, statistics.pstdev(null) if len(null) > 1 else 0.0, len(null_payload), sum(len(g["dx"]) for g in null_payload)


def residualize_response(genes, response_key="within_gene_usage", out_key="resid_usage"):
    for gene in sorted(genes):
        arr = genes[gene]
        y = [float(x[response_key]) for x in arr]
        cov = [[float(x["gc"]), float(x["pos_rank"])] for x in arr]
        resid = ols_residuals(y, cov)
        for x, r in zip(arr, resid):
            x[out_key] = r


def decode_clusters(obj):
    schema = obj.get("meta", {}).get("cluster_schema", [])
    if not schema:
        raise ValueError("missing cluster_schema")
    encoding = obj.get("meta", {}).get("encoding")
    scale = float(obj.get("meta", {}).get("scale", 1.0))
    dicts = obj.get("meta", {}).get("dicts", {})
    genes = {}
    for rec in obj["clusters"]:
        if encoding == "dict_b36_v1":
            rec = [unb36(v) for v in rec.split(",")]
            x = {
                "gene": dicts["gene"][rec[0]],
                "chrom": dicts["chrom"][rec[1]],
                "pos": rec[2],
                "strand": dicts["strand"][rec[3]],
                "tpm": rec[4] / scale,
                "within_gene_usage": rec[5] / scale,
                "hex_score": rec[6] / scale,
                "ur_score": rec[7] / scale,
                "ugua_score": rec[8] / scale,
                "gu_score": rec[9] / scale,
                "full_strength": rec[10] / scale,
                "gc": rec[11] / scale,
                "pos_rank": rec[12] / scale,
                "hexamer": dicts["hexamer"][rec[13]],
            }
        elif encoding == "dict_int_v1":
            x = {
                "gene": dicts["gene"][rec[0]],
                "chrom": dicts["chrom"][rec[1]],
                "pos": rec[2],
                "strand": dicts["strand"][rec[3]],
                "tpm": rec[4] / scale,
                "within_gene_usage": rec[5] / scale,
                "hex_score": rec[6] / scale,
                "ur_score": rec[7] / scale,
                "ugua_score": rec[8] / scale,
                "gu_score": rec[9] / scale,
                "full_strength": rec[10] / scale,
                "gc": rec[11] / scale,
                "pos_rank": rec[12] / scale,
                "hexamer": dicts["hexamer"][rec[13]],
            }
        else:
            x = {schema[i]: rec[i] for i in range(len(schema))}
        x["tpm"] = float(x["tpm"])
        x["within_gene_usage"] = float(x["within_gene_usage"])
        x["hex_score"] = float(x["hex_score"])
        x["ur_score"] = float(x["ur_score"])
        x["ugua_score"] = float(x["ugua_score"])
        x["gu_score"] = float(x["gu_score"])
        x["full_strength"] = float(x["full_strength"])
        x["hex_gu_strength"] = x["hex_score"] + x["gu_score"]
        x["gc"] = float(x["gc"])
        x["pos_rank"] = float(x["pos_rank"])
        genes.setdefault(str(x["gene"]), []).append(x)
    return genes


def ladder_positive_control(genes):
    vals = {"AATAAA": [], "ATTAAA": [], "VARIANT": [], "NONE": []}
    for arr in genes.values():
        for x in arr:
            vals.get(x.get("hexamer", "NONE"), vals["NONE"]).append(float(x["within_gene_usage"]))
    ladder = []
    for key in ["AATAAA", "ATTAAA", "VARIANT", "NONE"]:
        ladder.append({"hexamer": key, "median_tpm": rounded(median(vals[key])), "n": len(vals[key])})
    med = {x["hexamer"]: x["median_tpm"] for x in ladder}
    reproduced = (
        med["AATAAA"] is not None
        and med["ATTAAA"] is not None
        and med["VARIANT"] is not None
        and med["NONE"] is not None
        and med["AATAAA"] > med["ATTAAA"] > med["VARIANT"] > med["NONE"]
    )
    return ladder, reproduced


def run_partial(genes, predictor_key, seed):
    payload, variable_genes, n_items = within_gene_rank_payload(genes, "resid_usage", predictor_key)
    null_payload = sample_payload_for_null(payload, NULL_MAX_CLUSTERS, seed + 17)
    rho, p, null95, null_obs, null_sd, null_genes, null_clusters = perm_test(payload, PERM_B, seed, null_payload)
    return {
        "partial_rho": rounded(rho),
        "p": rounded(p),
        "actual_B": PERM_B,
        "null95": [rounded(null95[0]), rounded(null95[1])],
        "rho_null_subset": rounded(null_obs),
        "null_sd": rounded(null_sd),
        "variable_genes": variable_genes,
        "n_ranked_clusters": n_items,
        "null_subset_genes": null_genes,
        "null_subset_clusters": null_clusters,
    }


def collinearity(genes):
    ur = []
    gc = []
    full = []
    hxgu = []
    for arr in genes.values():
        for x in arr:
            ur.append(float(x["ur_score"]))
            gc.append(float(x["gc"]))
            full.append(float(x["full_strength"]))
            hxgu.append(float(x["hex_gu_strength"]))
    return {
        "spearman_rho": rounded(spearman(ur, gc)),
        "pearson_r": rounded(pearson(ur, gc)),
        "n": len(ur),
        "full_vs_hex_gu_spearman": rounded(spearman(full, hxgu)),
    }


def main():
    checks = {
        "polyasite_parsed": False,
        "mm10_windows_chromwise": False,
        "pas_strength_computed": False,
        "composition_position_controlled": False,
        "decomposition_diagnosed": False,
        "positive_control": False,
        "pas_xfer_verdict": False,
    }
    cannot_claim = [
        "AU-rich 项与 local-GC 共线(transferable 部分主要是 hexamer 几何)",
        "小鼠特定",
        "mm10",
        "within-gene usage 是相对代理",
        "3'-seq 测量噪声",
        "观测性非因果",
        "cleavage 窗近似",
    ]
    try:
        path = pathlib.Path.cwd() / DATA_REL
        obj = json.loads(path.read_text(encoding="utf-8"))
        meta = obj.get("meta", {})
        genes = decode_clusters(obj)
        n_genes = len(genes)
        n_clusters = sum(len(v) for v in genes.values())
        checks["polyasite_parsed"] = n_genes > 0 and n_clusters > 0 and meta.get("source", "").startswith("https://polyasite")
        checks["mm10_windows_chromwise"] = bool(meta.get("chromwise_mm10", {}).get("chrom_stats"))
        checks["pas_strength_computed"] = all("full_strength" in x and "gc" in x for arr in genes.values() for x in arr[:1])

        residualize_response(genes)
        checks["composition_position_controlled"] = True

        ladder, ladder_ok = ladder_positive_control(genes)
        checks["positive_control"] = bool(ladder_ok)

        main_full = run_partial(genes, "full_strength", SEED)
        hex_gu = run_partial(genes, "hex_gu_strength", SEED + 1)
        checks["decomposition_diagnosed"] = True
        col = collinearity(genes)

        if not ladder_ok:
            verdict = "needs_data"
            status = "needs_data"
            note = "正对照 canonical hexamer ladder 未复现，按 needs_data。"
        elif main_full["partial_rho"] is not None and main_full["partial_rho"] >= 0.10 and main_full["p"] < 0.01:
            verdict = "transfers_cross_dataset"
            status = "passed"
            note = "genome-wide 全 4-term frozen PAS 强度在 GC+位置控制后同正号且达到预注册阈值；仍是观测性 cross-dataset transfer。"
        elif main_full["partial_rho"] is not None and main_full["partial_rho"] < 0.0:
            verdict = "not_replicated"
            status = "passed"
            note = "genome-wide 全 4-term frozen PAS 强度控 GC+位置后符号翻为负；AU-rich/local-GC 共线削弱或主导，不能声称原 +0.244 全规则守恒。"
        elif hex_gu["partial_rho"] is not None and hex_gu["partial_rho"] > 0.0:
            verdict = "bounded_descriptor_only"
            status = "passed"
            note = "全强度未达 transfer 阈值；去 AU-rich 后 hexamer+GU 为弱正，支持 bounded 的 hexamer 几何/下游富 GU 描述信号。"
        else:
            verdict = "bounded_descriptor_only"
            status = "passed"
            note = "canonical ladder 复现，但主强度和 hexamer+GU 均未达到强 transfer；只保留有界描述。"
        checks["pas_xfer_verdict"] = status == "passed"
        out = {
            "status": status,
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": verdict,
            "note": note,
            "result": {
                "n_genes": n_genes,
                "n_clusters": n_clusters,
                "main_full": main_full,
                "hexamer_gu_only": hex_gu,
                "collinearity_ur_vs_gc": col,
                "posctrl": {"ladder": ladder, "reproduced": ladder_ok},
                "runtime_sec": 0.0,
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        raise SystemExit(0 if status == "passed" else 3)
    except Exception as e:
        out = {
            "status": "error",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "运行失败: " + repr(e),
            "result": {
                "n_genes": 0,
                "n_clusters": 0,
                "main_full": {"partial_rho": None, "p": None, "actual_B": 0},
                "hexamer_gu_only": {"partial_rho": None, "p": None},
                "collinearity_ur_vs_gc": None,
                "posctrl": {"ladder": [], "reproduced": False},
                "runtime_sec": 0.0,
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        raise SystemExit(1)


if __name__ == "__main__":
    main()

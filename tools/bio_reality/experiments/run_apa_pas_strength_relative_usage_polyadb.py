#!/usr/bin/env python3
import json
import math
import pathlib
import random
import statistics
import time


EXPERIMENT_ID = "apa_pas_strength_relative_usage_polyadb"
CLAIM_ID = "h3.cross_layer_relation.alternative_polyadenylation.apa_pas_strength_relative_usage_polyadb"
SEED = 20260622
PERM_B = 2000
DATA_REL = pathlib.Path("tools/bio_reality/data/apa_pas_strength_relative_usage_polyadb.json")
HEX_DECODE = {3: "AAUAAA", 2: "AUUAAA", 1: "Arich", 0: "None"}
CHROM_DECODE = {str(i): str(i) for i in range(1, 23)}
CHROM_DECODE.update({"x": "X", "y": "Y", "m": "M"})
NULL_MAX_PAS = 60000


def unb36(s):
    return int(str(s), 36)


def unpack_pas_id(s):
    s = str(s)
    for i, ch in enumerate(s):
        if ch in "+-" and i > 0:
            chrom_code = s[:i]
            if chrom_code in CHROM_DECODE:
                return "chr" + CHROM_DECODE[chrom_code] + ":" + ch + ":" + str(unb36(s[i + 1:]))
    return s


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


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
    mx = sum(xs) / n
    my = sum(ys) / n
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


def normal_two_sided_from_r(r, n):
    if n < 4:
        return 1.0
    z = abs(r) * math.sqrt(max(0.0, n - 3.0))
    return math.erfc(z / math.sqrt(2.0))


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
        # Tiny ridge fallback for collinearity in hand-written OLS.
        for i in range(p):
            xtx[i][i] += 1e-8
        inv = invert_matrix(xtx)
    beta = [sum(inv[i][j] * xty[j] for j in range(p)) for i in range(p)]
    resid = []
    for yi, cs in zip(y, covars):
        row = [1.0] + [float(c) for c in cs]
        resid.append(yi - sum(beta[i] * row[i] for i in range(p)))
    return resid


def within_gene_rank_payload(genes, response_key="rel_usage", predictor_key="pas_strength"):
    payload = []
    flat_x = []
    flat_y = []
    variable_genes = 0
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
        if sxx > 0:
            variable_genes += 1
        payload.append({
            "dx": dx,
            "dy": dy,
            "pdy": dy[:],
            "sxx": sxx,
            "syy": syy,
            "sxy": sxy,
        })
        flat_x.extend(dx)
        flat_y.extend(dy)
    return payload, flat_x, flat_y, variable_genes


def rho_from_sums(sxy, sxx, syy):
    if sxx <= 0 or syy <= 0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def sample_payload_for_null(payload, max_pas, seed):
    total = sum(len(g["dx"]) for g in payload)
    if total <= max_pas:
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
        quota = max(1, round(len(arr) * max_pas / total))
        for g in arr[:quota]:
            if used + len(g["dx"]) <= max_pas or not chosen:
                chosen.append(g)
                used += len(g["dx"])
    if used < max_pas:
        chosen_ids = {id(g) for g in chosen}
        rest = [g for g in payload if id(g) not in chosen_ids]
        rng.shuffle(rest)
        for g in rest:
            if used + len(g["dx"]) > max_pas:
                continue
            chosen.append(g)
            used += len(g["dx"])
            if used >= max_pas:
                break
    return chosen


def perm_test(payload, b, seed, null_payload=None):
    obs_sxy = sum(g["sxy"] for g in payload)
    sxx = sum(g["sxx"] for g in payload)
    syy = sum(g["syy"] for g in payload)
    obs = rho_from_sums(obs_sxy, sxx, syy)
    if null_payload is None:
        null_payload = payload
    null_obs_sxy = sum(g["sxy"] for g in null_payload)
    null_sxx = sum(g["sxx"] for g in null_payload)
    null_syy = sum(g["syy"] for g in null_payload)
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
    return obs, (lo, hi), p, null, null_obs, len(null_payload), sum(len(g["dx"]) for g in null_payload)


def add_residual_response(genes, out_key="resid_usage"):
    used_dist = 0
    total_genes = 0
    for gene in sorted(genes):
        arr = genes[gene]
        y = [float(x["rel_usage"]) for x in arr]
        has_dist = all(x.get("stop_dist") is not None for x in arr)
        cov = []
        for x in arr:
            row = [float(x["local_gc"]), float(x["pos_rank"])]
            if has_dist:
                row.append(math.log1p(abs(float(x["stop_dist"]))))
            cov.append(row)
        if has_dist:
            used_dist += 1
        total_genes += 1
        resid = ols_residuals(y, cov)
        for x, r in zip(arr, resid):
            x[out_key] = r
    return used_dist, total_genes


def hexamer_gradient(genes):
    vals = {"AAUAAA": [], "AUUAAA": [], "Arich": [], "None": []}
    for arr in genes.values():
        for x in arr:
            h = x.get("hexamer")
            if h in vals:
                vals[h].append(float(x["rel_usage"]))
            elif h == "Other":
                vals["None"].append(float(x["rel_usage"]))
    return {k: mean(v) if v else None for k, v in vals.items()}, {k: len(v) for k, v in vals.items()}


def hexamer_score(h):
    if h == "AAUAAA":
        return 3.0
    if h == "AUUAAA":
        return 2.0
    if h == "Arich":
        return 1.0
    return 0.0


def hexamer_perm(genes, b, seed):
    for arr in genes.values():
        for x in arr:
            x["hex_score"] = hexamer_score(x.get("hexamer"))
    payload, _, _, _ = within_gene_rank_payload(genes, "rel_usage", "hex_score")
    null_payload = sample_payload_for_null(payload, NULL_MAX_PAS, seed + 100)
    obs, _, p, _, null_obs, null_genes, null_pas = perm_test(payload, b, seed, null_payload)
    return obs, p, null_obs, null_genes, null_pas


def polyastrength_corr(genes):
    xs = []
    ys = []
    for arr in genes.values():
        for x in arr:
            p = x.get("polyastrength")
            if p is not None:
                xs.append(float(x["pas_strength"]))
                ys.append(float(p))
    return spearman(xs, ys) if len(xs) > 2 else None, len(xs)


def heldout(genes):
    names = sorted(genes)
    rng = random.Random(SEED + 3)
    rng.shuffle(names)
    mid = len(names) // 2
    out = {}
    for label, subset in (("split_a", names[:mid]), ("split_b", names[mid:])):
        sub = {g: genes[g] for g in subset}
        payload, _, _, _ = within_gene_rank_payload(sub)
        sxx = sum(g["sxx"] for g in payload)
        syy = sum(g["syy"] for g in payload)
        sxy = sum(g["sxy"] for g in payload)
        out[label] = rho_from_sums(sxy, sxx, syy)
    return out


def decode_genes(raw_genes):
    decoded = {}
    for gene, arr in raw_genes.items():
        out = []
        for x in arr:
            if isinstance(x, dict):
                out.append(x)
            else:
                if isinstance(x, str):
                    parts = x.split(",")
                    x = [None if p == "" else p for p in parts]
                    for i in range(1, len(x)):
                        if x[i] is not None:
                            x[i] = unb36(x[i])
                if len(x) == 12:
                    hexamer = x[7]
                    stop_dist = x[10]
                    poly = x[11]
                else:
                    hexamer = HEX_DECODE.get(x[7], "None")
                    stop_dist = None
                    poly = x[10]
                out.append({
                    "pas_id": unpack_pas_id(x[0]),
                    "rel_usage": x[1] / 1_000_000.0,
                    "pas_strength": x[2] / 1000.0,
                    "strength_parts": {
                        "hex": x[3] / 1000.0,
                        "ur": x[4] / 1000.0,
                        "ugua": x[5] / 1000.0,
                        "gu": x[6] / 1000.0,
                    },
                    "hexamer": hexamer,
                    "local_gc": x[8] / 1000.0,
                    "pos_rank": x[9] / 1000.0,
                    "stop_dist": stop_dist,
                    "polyastrength": None if poly is None else poly / 1000.0,
                })
        decoded[gene] = out
    return decoded


def rounded(x, nd=6):
    if x is None:
        return None
    return round(float(x), nd)


def main():
    t0 = time.time()
    path = pathlib.Path.cwd() / DATA_REL
    checks = {
        "tsv_parsed": False,
        "pas_strength_computed": False,
        "within_gene_perm_null": False,
        "composition_controlled": False,
        "positive_control": False,
        "apa_boundary_verdict": False,
    }
    cannot_claim = [
        "3'READS-seq 特定测量",
        "观测性非因果",
        "pas_strength 是 stdlib motif proxy(无真热力学/结构)",
        "within-gene 相对用量(非绝对切割效率)",
        "人类",
        "PolyaStrength 仅 sanity 未入主分析",
        "序列窗 ±75nt 限定",
    ]
    try:
        obj = json.loads(path.read_text())
        genes = decode_genes(obj["genes"])
        meta = obj.get("meta", {})
        checks["tsv_parsed"] = bool(genes) and meta.get("n_pas", 0) > 0
        checks["pas_strength_computed"] = all("pas_strength" in x for arr in genes.values() for x in arr[:1])

        payload, flat_x, flat_y, variable_genes = within_gene_rank_payload(genes)
        null_payload = sample_payload_for_null(payload, NULL_MAX_PAS, SEED + 10)
        rho_obs, null95, p_perm, null, null_obs, null_genes, null_pas = perm_test(payload, PERM_B, SEED, null_payload)
        null_sd = statistics.pstdev(null) if len(null) > 1 else 0.0
        checks["within_gene_perm_null"] = variable_genes > 0 and null_sd > 0

        used_dist, total_genes = add_residual_response(genes)
        ppayload, _, _, pvariable_genes = within_gene_rank_payload(genes, "resid_usage")
        pnull_payload = sample_payload_for_null(ppayload, NULL_MAX_PAS, SEED + 11)
        prho, pnull95, ppartial, pnull, pnull_obs, pnull_genes, pnull_pas = perm_test(ppayload, PERM_B, SEED + 1, pnull_payload)
        checks["composition_controlled"] = pvariable_genes > 0 and (statistics.pstdev(pnull) if len(pnull) > 1 else 0.0) > 0

        gradient, gradient_n = hexamer_gradient(genes)
        hex_rho, hex_p, hex_null_obs, hex_null_genes, hex_null_pas = hexamer_perm(genes, PERM_B, SEED + 2)
        aa = gradient.get("AAUAAA")
        au = gradient.get("AUUAAA")
        ar = gradient.get("Arich")
        nn = gradient.get("None")
        checks["positive_control"] = (
            aa is not None and au is not None and ar is not None and nn is not None
            and aa > au > ar > nn
            and hex_p < 0.01
        )

        poly_corr, poly_n = polyastrength_corr(genes)
        h_out = heldout(genes)
        n_pas = sum(len(v) for v in genes.values())
        n_genes = len(genes)

        if not checks["positive_control"]:
            verdict = "needs_data"
            status = "needs_data"
            note = "PAS_hexamer 正对照梯度未复现，主判不下。"
        elif p_perm < 0.01 and ppartial < 0.01 and rho_obs * prho > 0 and prho > 0:
            # Rank correlation squared is only a rough bounded effect proxy here.
            if prho * prho < 0.02:
                verdict = "bounded_descriptor_only"
                note = "自算 PAS motif proxy 在 GC+位置控制后仍同号显著，但 rank 相关平方低于约 1-2%，只支持有界描述信号。"
            else:
                verdict = "crosses_boundary"
                note = "自算 PAS motif proxy 在同基因内预测相对 APA 用量，且 GC+位置控制后仍显著；观测性结果不作因果声称。"
            status = "passed"
        elif p_perm < 0.01 and (ppartial >= 0.01 or rho_obs * prho <= 0):
            verdict = "composition_artifact"
            status = "passed"
            note = "未控制时存在信号，但 GC/位置残差化后不满足同号显著，按成分/位置 artifact 处理。"
        else:
            verdict = "composition_artifact"
            status = "passed"
            note = "主 within-gene permutation 未达到预注册阈值，未支持序列强度越过 readback 边界。"
        checks["apa_boundary_verdict"] = status == "passed"

        result = {
            "n_pas": n_pas,
            "n_genes": n_genes,
            "main": {"within_gene_rho": rounded(rho_obs)},
            "perm_null": {
                "rho_obs": rounded(rho_obs),
                "rho_obs_null_subset": rounded(null_obs),
                "null95": [rounded(null95[0]), rounded(null95[1])],
                "p_perm": rounded(p_perm),
                "actual_B": PERM_B,
                "null_subset_genes": null_genes,
                "null_subset_pas": null_pas,
                "null_sd": rounded(null_sd),
                "variable_genes": variable_genes,
            },
            "partial": {
                "rho": rounded(prho),
                "rho_null_subset": rounded(pnull_obs),
                "p": rounded(ppartial),
                "null95": [rounded(pnull95[0]), rounded(pnull95[1])],
                "null_subset_genes": pnull_genes,
                "null_subset_pas": pnull_pas,
                "covariates": "local_gc + within_gene_pos_rank + log1p(abs(stop_dist)) where complete, otherwise local_gc + pos_rank",
                "genes_with_stop_dist": used_dist,
                "genes_total": total_genes,
            },
            "posctrl": {
                "hexamer_usage_gradient": {k: rounded(v) for k, v in gradient.items()},
                "hexamer_counts_used": gradient_n,
                "gradient_rho": rounded(hex_rho),
                "gradient_rho_null_subset": rounded(hex_null_obs),
                "gradient_p": rounded(hex_p),
                "gradient_null_subset_genes": hex_null_genes,
                "gradient_null_subset_pas": hex_null_pas,
                "pas_strength_vs_polyastrength_corr": rounded(poly_corr),
                "pas_strength_vs_polyastrength_n": poly_n,
            },
            "held_out": {k: rounded(v) for k, v in h_out.items()},
            "runtime_sec": 0.0,
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
        raise SystemExit(0 if status == "passed" else 3)
    except Exception as e:
        checks["apa_boundary_verdict"] = False
        out = {
            "status": "error",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "needs_data",
            "note": "运行失败: " + repr(e),
            "result": {
                "n_pas": 0,
                "n_genes": 0,
                "main": {"within_gene_rho": None},
                "perm_null": {"rho_obs": None, "null95": None, "p_perm": None, "actual_B": 0},
                "partial": {"rho": None, "p": None},
                "posctrl": {"hexamer_usage_gradient": {}, "gradient_p": None, "pas_strength_vs_polyastrength_corr": None},
                "held_out": None,
                "runtime_sec": 0.0,
                "cannot_claim": cannot_claim,
            },
        }
        print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        raise SystemExit(1)


if __name__ == "__main__":
    main()

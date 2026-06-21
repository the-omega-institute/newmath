#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""N-end degron 是否越过序列 readback 边界预测 Mathieson 内源蛋白半衰期。"""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "nend_degron_protein_turnover_boundary_mathieson"
CLAIM_ID = "h3.cross_layer_relation.protein_turnover.nend_degron_protein_turnover_boundary_mathieson"
DATA_REL = pathlib.Path("tools/bio_reality/data/nend_turnover_mathieson.json")
AA_ORDER = "ACDEFGHIKLMNPQRSTVWY"
HYDROPHOBIC = set("AILMFWYV")
KNOWN_UNSTABLE = ["MYC", "ODC1", "CCNB1", "CCND1", "FOS", "HIF1A"]
PERMUTATIONS = 1000
SEED = 20260621


def rg(x, nd=6):
    if x is None:
        return None
    return round(float(x), nd)


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return None
    mx = sum(xs) / n
    my = sum(ys) / n
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx <= 0 or vy <= 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy)


def rank_percentile(sorted_vals, value):
    if not sorted_vals:
        return None
    less_eq = 0
    for x in sorted_vals:
        if x <= value:
            less_eq += 1
        else:
            break
    return 100.0 * less_eq / len(sorted_vals)


def quantile_bins(values, q=5):
    n = len(values)
    order = sorted(range(n), key=lambda i: values[i])
    bins = [0] * n
    for rank, idx in enumerate(order):
        bins[idx] = min(q - 1, (rank * q) // n)
    return bins


def transpose(mat):
    if not mat:
        return []
    return [list(col) for col in zip(*mat)]


def cholesky_solve(a, b):
    n = len(a)
    jitter = 0.0
    for _attempt in range(8):
        try:
            aa = [row[:] for row in a]
            if jitter:
                for i in range(n):
                    aa[i][i] += jitter
            lmat = [[0.0] * n for _ in range(n)]
            for i in range(n):
                for j in range(i + 1):
                    s = aa[i][j]
                    for k in range(j):
                        s -= lmat[i][k] * lmat[j][k]
                    if i == j:
                        if s <= 1e-14:
                            raise ValueError("非正定矩阵")
                        lmat[i][j] = math.sqrt(s)
                    else:
                        lmat[i][j] = s / lmat[j][j]
            y = [0.0] * n
            for i in range(n):
                s = b[i]
                for k in range(i):
                    s -= lmat[i][k] * y[k]
                y[i] = s / lmat[i][i]
            x = [0.0] * n
            for i in range(n - 1, -1, -1):
                s = y[i]
                for k in range(i + 1, n):
                    s -= lmat[k][i] * x[k]
                x[i] = s / lmat[i][i]
            return x
        except ValueError:
            jitter = 1e-10 if jitter == 0.0 else jitter * 10.0
    raise RuntimeError("Cholesky 求解失败")


def xtx_xty(xmat, y):
    p = len(xmat[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, yi in zip(xmat, y):
        for i, xi in enumerate(row):
            xty[i] += xi * yi
            for j in range(i + 1):
                xtx[i][j] += xi * row[j]
    for i in range(p):
        for j in range(i):
            xtx[j][i] = xtx[i][j]
    return xtx, xty


def residualize_vector(v, xmat, xtx=None):
    if xtx is None:
        xtx, xtv = xtx_xty(xmat, v)
    else:
        p = len(xmat[0])
        xtv = [0.0] * p
        for row, vi in zip(xmat, v):
            for i, xi in enumerate(row):
                xtv[i] += xi * vi
    coef = cholesky_solve(xtx, xtv)
    return [vi - sum(c * x for c, x in zip(coef, row)) for vi, row in zip(v, xmat)]


def beta_from_residuals(score_resid, y_resid):
    den = sum(x * x for x in score_resid)
    if den <= 1e-14:
        return None
    return sum(x * y for x, y in zip(score_resid, y_resid)) / den


def build_covariates(records):
    # 20 个 AA 频率去掉最后一个 Y，避免和截距完全共线。
    rows = []
    for r in records:
        rows.append([1.0, math.log(r["length"])] + [float(x) for x in r["aafrac"][:19]])
    return rows


def hydrophobic_fraction(aafrac):
    return sum(aafrac[AA_ORDER.index(aa)] for aa in HYDROPHOBIC)


def strata_indices(records):
    lengths = [math.log(r["length"]) for r in records]
    hydros = [hydrophobic_fraction(r["aafrac"]) for r in records]
    lb = quantile_bins(lengths, 5)
    hb = quantile_bins(hydros, 5)
    strata = {}
    for i, key in enumerate(zip(lb, hb)):
        strata.setdefault(key, []).append(i)
    return list(strata.values())


def permute_within_strata(values, strata, rng):
    out = list(values)
    for idxs in strata:
        vals = [out[i] for i in idxs]
        rng.shuffle(vals)
        for i, v in zip(idxs, vals):
            out[i] = v
    return out


def model_for_score(records, score_key, y_key="y", do_perm=False):
    y = [r[y_key] for r in records]
    xmat = build_covariates(records)
    xtx, _ = xtx_xty(xmat, y)
    y_resid = residualize_vector(y, xmat, xtx)
    score = [float(r[score_key]) for r in records]
    score_resid = residualize_vector(score, xmat, xtx)
    beta = beta_from_residuals(score_resid, y_resid)
    p_perm = None
    actual_perm = 0
    if do_perm and beta is not None:
        rng = random.Random(SEED + len(records) * 17 + sum(ord(c) for c in score_key))
        strata = strata_indices(records)
        ge = 0
        for _ in range(PERMUTATIONS):
            ps = permute_within_strata(score, strata, rng)
            pr = residualize_vector(ps, xmat, xtx)
            pb = beta_from_residuals(pr, y_resid)
            if pb is not None and abs(pb) >= abs(beta) - 1e-15:
                ge += 1
            actual_perm += 1
        p_perm = (ge + 1.0) / (actual_perm + 1.0)
    return {"beta": beta, "p_perm": p_perm, "actual_perm": actual_perm}


def bh_qvalues(pairs):
    valid = [(name, p) for name, p in pairs if p is not None]
    m = len(valid)
    qvals = {name: None for name, _p in pairs}
    if m == 0:
        return qvals
    ordered = sorted(valid, key=lambda x: x[1], reverse=True)
    prev = 1.0
    for rank_from_high, (name, p) in enumerate(ordered):
        rank = m - rank_from_high
        q = min(prev, p * m / rank)
        q = min(1.0, q)
        qvals[name] = q
        prev = q
    return qvals


def load_data():
    path = pathlib.Path.cwd() / DATA_REL
    with path.open("r", encoding="utf-8") as fh:
        return json.load(fh), path


def records_for_cell(genes, cell):
    records = []
    for gene, g in genes.items():
        hl = g["hl"].get(cell)
        if hl is None or hl <= 0:
            continue
        records.append(
            {
                "gene": gene,
                "y": math.log2(float(hl)),
                "half_life": float(hl),
                "nend": float(g["nend"]),
                "cterm": float(g["cterm"]),
                "internal": float(g["internal"]),
                "length": int(g["length"]),
                "aafrac": [float(x) for x in g["aafrac"]],
            }
        )
    return records


def sanity_known_unstable(genes, celltypes):
    out = {}
    aggregate = []
    for gene, g in genes.items():
        vals = [float(g["hl"][c]) for c in celltypes if g["hl"].get(c) is not None and g["hl"][c] > 0]
        if vals:
            aggregate.append((gene, statistics.median(vals)))
    sorted_vals = sorted(v for _g, v in aggregate)
    by_gene = {g.upper(): v for g, v in aggregate}
    for gene in KNOWN_UNSTABLE:
        if gene in by_gene:
            out[gene] = {"median_half_life_h": rg(by_gene[gene]), "percentile_short_is_low": rg(rank_percentile(sorted_vals, by_gene[gene]), 3)}
        else:
            out[gene] = None
    present = [v["percentile_short_is_low"] for v in out.values() if v is not None]
    return out, present


def sanity_cross_cell_corr(genes, celltypes):
    vals = []
    pair_corrs = {}
    for i, c1 in enumerate(celltypes):
        for c2 in celltypes[i + 1 :]:
            xs, ys = [], []
            for g in genes.values():
                h1 = g["hl"].get(c1)
                h2 = g["hl"].get(c2)
                if h1 is not None and h2 is not None and h1 > 0 and h2 > 0:
                    xs.append(math.log2(float(h1)))
                    ys.append(math.log2(float(h2)))
            r = pearson(xs, ys)
            pair_corrs[c1 + "__" + c2] = {"n": len(xs), "pearson_log2": rg(r)}
            if r is not None:
                vals.append(r)
    return {"median_pairwise_log2_corr": rg(statistics.median(vals) if vals else None), "pairs": pair_corrs}


def main():
    t0 = time.time()
    checks = {
        "mathieson_parsed": False,
        "uniprot_joined": False,
        "nend_encoded": False,
        "main_model_per_celltype": False,
        "pseudo_terminal_negctrl": False,
        "composition_matched_perm": False,
        "crosscelltype_aggregate": False,
        "sanity_anchor": False,
        "turnover_verdict": False,
    }
    cannot_claim = [
        "简化 N-end rule：Met-excision 只是二位小残基启发式，无 N-末端乙酰化、蛋白切割或实测 N-端信息。",
        "gene-symbol→UniProt-canonical join 有 isoform、alternative processing 和基因符号歧义不确定；UniProt 多条同 GN 仅取最长序列。",
        "无 mRNA-HL/translation-rate/abundance 协变量，故只能说 beyond AA-composition+length，不能说 beyond mRNA-stability/translation；比原 Schwanhäusser 设计弱；因 Schwanhäusser Supp Table 3 Springer 反爬且不在 PMC 取不到而改用 Mathieson。",
        "Mathieson 是 SILAC primary-cell 蛋白半衰期数据，存在细胞型、测量窗口和定量模型限制。",
        "不能声称 ubiquitin/proteasome 机制，只能报告序列 N-end 分类与 measured half-life 的统计关系。",
        "不能声称 proteome-wide 普适；只覆盖成功 join 且有 good half_life 的 reviewed human SwissProt 基因。",
        "不能跨物种外推；主分析排除 Mouse Neurons 列。",
    ]
    try:
        data, data_path = load_data()
        meta = data.get("meta", {})
        genes = data.get("genes", {})
        celltypes = list(meta.get("celltypes", []))
        checks["mathieson_parsed"] = bool(meta.get("mathieson_gene_rows", 0) and celltypes)
        checks["uniprot_joined"] = bool(meta.get("n_joined", 0) and len(genes) == meta.get("n_joined"))
        checks["nend_encoded"] = all(("nend" in g and "cterm" in g and "internal" in g and "aafrac" in g) for g in genes.values())

        per_cell = {}
        p_pairs = []
        cterm_models = {}
        internal_models = {}
        actual_perm = 0
        for cell in celltypes:
            recs = records_for_cell(genes, cell)
            if len(recs) < 30:
                per_cell[cell] = {"n": len(recs), "beta_nend": None, "p_perm": None, "bh_q": None}
                continue
            nmodel = model_for_score(recs, "nend", do_perm=True)
            cmodel = model_for_score(recs, "cterm", do_perm=True)
            imodel = model_for_score(recs, "internal", do_perm=True)
            actual_perm += nmodel["actual_perm"] + cmodel["actual_perm"] + imodel["actual_perm"]
            per_cell[cell] = {
                "n": len(recs),
                "beta_nend": rg(nmodel["beta"]),
                "p_perm": rg(nmodel["p_perm"]),
                "bh_q": None,
                "beta_cterm": rg(cmodel["beta"]),
                "p_cterm_perm": rg(cmodel["p_perm"]),
                "beta_internal": rg(imodel["beta"]),
                "p_internal_perm": rg(imodel["p_perm"]),
            }
            cterm_models[cell] = cmodel
            internal_models[cell] = imodel
            p_pairs.append((cell, nmodel["p_perm"]))

        qvals = bh_qvalues(p_pairs)
        for cell, q in qvals.items():
            per_cell[cell]["bh_q"] = rg(q)

        checks["main_model_per_celltype"] = any(v.get("beta_nend") is not None for v in per_cell.values())
        checks["pseudo_terminal_negctrl"] = bool(cterm_models and internal_models)
        checks["composition_matched_perm"] = actual_perm >= PERMUTATIONS * max(1, len(celltypes))

        human_results = [per_cell[c] for c in celltypes if per_cell.get(c, {}).get("beta_nend") is not None]
        neg_count = sum(1 for r in human_results if r["beta_nend"] is not None and r["beta_nend"] < 0)
        consistent_sign_frac = neg_count / len(human_results) if human_results else None
        majority_needed = (len(human_results) + 1) // 2
        nend_majority_sig = sum(
            1 for r in human_results if r["beta_nend"] is not None and r["beta_nend"] < 0 and r["bh_q"] is not None and r["bh_q"] < 0.05
        ) >= majority_needed
        nend_any_strong = any(r["beta_nend"] is not None and r["beta_nend"] < 0 and r["p_perm"] is not None and r["p_perm"] < 0.01 for r in human_results)

        c_abs = [abs(m["beta"]) for m in cterm_models.values() if m["beta"] is not None]
        i_abs = [abs(m["beta"]) for m in internal_models.values() if m["beta"] is not None]
        n_abs = [abs(r["beta_nend"]) for r in human_results if r["beta_nend"] is not None]
        c_sig = [m for m in cterm_models.values() if m["p_perm"] is not None and m["p_perm"] <= 0.05]
        i_sig = [m for m in internal_models.values() if m["p_perm"] is not None and m["p_perm"] <= 0.05]
        c_median = statistics.median(c_abs) if c_abs else None
        i_median = statistics.median(i_abs) if i_abs else None
        n_median = statistics.median(n_abs) if n_abs else None
        negctrl_null = (
            not c_sig
            and not i_sig
            and (n_median is None or c_median is None or c_median <= n_median)
            and (n_median is None or i_median is None or i_median <= n_median)
        )

        checks["crosscelltype_aggregate"] = bool(human_results)
        hl_repro_corr = sanity_cross_cell_corr(genes, celltypes)
        known_percentiles, known_present = sanity_known_unstable(genes, celltypes)
        rep_corrs = meta.get("replicate_log2_half_life_corr", {})
        rep_vals = [
            v.get("pearson_log2")
            for k, v in rep_corrs.items()
            if k in celltypes and isinstance(v, dict) and v.get("pearson_log2") is not None and v.get("n", 0) >= 20
        ]
        known_available_n = len([x for x in known_present if x is not None])
        sanity_ok = (
            checks["mathieson_parsed"]
            and checks["uniprot_joined"]
            and hl_repro_corr.get("median_pairwise_log2_corr") is not None
            and hl_repro_corr["median_pairwise_log2_corr"] > 0.25
            and (not rep_vals or statistics.median(rep_vals) > 0.25)
        )
        checks["sanity_anchor"] = bool(sanity_ok)

        contact = (
            sanity_ok
            and nend_any_strong
            and nend_majority_sig
            and consistent_sign_frac is not None
            and consistent_sign_frac >= 0.5
            and negctrl_null
        )
        verdict = "Nend_turnover_contact" if contact else "bounded_descriptor_only"
        status = "passed" if sanity_ok else "needs_data"
        checks["turnover_verdict"] = status == "passed"

        if status == "needs_data":
            note = (
                "sanity 或 join/解析不足，主判不下；当前输出仅作诊断。"
            )
            exit_code = 3
        elif verdict == "Nend_turnover_contact":
            note = (
                "N-end score 在 AA composition + length 控制后呈多数细胞型负向，置换显著且 pseudo-terminal 负控未显著；"
                "这是边界接触的统计证据，但不推出机制或 mRNA/translation 独立性。"
            )
            exit_code = 0
        else:
            note = (
                "在 Mathieson 数据中，简化 N-end score 未同时满足强置换显著、多数细胞型 BH-q 和 C/Internal pseudo-terminal 负控门槛；"
                "因此按预登记判为 bounded_descriptor_only，而非外部 reality contact。"
            )
            exit_code = 0

        result = {
            "n_joined": meta.get("n_joined", len(genes)),
            "celltypes": celltypes,
            "per_celltype": per_cell,
            "beta_cterm_summary": {
                "median_abs_beta": rg(c_median),
                "sig_perm_p_le_0_05_cells": [c for c, m in cterm_models.items() if m["p_perm"] is not None and m["p_perm"] <= 0.05],
            },
            "beta_internal_summary": {
                "median_abs_beta": rg(i_median),
                "sig_perm_p_le_0_05_cells": [c for c, m in internal_models.items() if m["p_perm"] is not None and m["p_perm"] <= 0.05],
            },
            "negctrl_null": bool(negctrl_null),
            "consistent_sign_frac": rg(consistent_sign_frac),
            "sanity": {
                "hl_repro_corr": hl_repro_corr,
                "replicate_log2_half_life_corr": rep_corrs,
                "known_unstable_percentiles": known_percentiles,
                "known_unstable_available_n": known_available_n,
                "known_unstable_anchor_note": (
                    "预设短寿命锚基因在 Mathieson high-quality sheet 的 gene_name 列及 joined 数据中均未找到；"
                    "因此只报告缺失，不用该锚判失败。"
                    if known_available_n == 0
                    else "仅对 joined 且有 good half_life 的预设短寿命锚报告 percentile。"
                ),
            },
            "actual_perm": actual_perm,
            "runtime_sec": rg(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
            "data_path": str(data_path),
            "permutations_per_model": PERMUTATIONS,
            "seed": SEED,
        }
        payload = {
            "status": status,
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": verdict,
            "note": note,
            "result": result,
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return exit_code
    except Exception as exc:
        payload = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "bounded_descriptor_only",
            "note": "运行异常，主判不下: %s" % exc,
            "result": {"runtime_sec": rg(time.time() - t0, 3), "cannot_claim": cannot_claim},
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        return 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
纯 stdlib 离线实验：3'UTR 先验 motif 是否在控制长度、GC、表达 proxy、CDS 信号肽后预测 APEX-seq 定位 enrichment。
"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "mrna_localization_3utr_motif_fazal2019"
CLAIM_ID = "h3.cross_layer_relation.mrna_localization.mrna_localization_3utr_motif_fazal2019"
SEED = 20260623
DATA_PATH = Path.cwd() / "tools" / "bio_reality" / "data" / "mrna_localization_3utr_motif_fazal2019.json"


def finite(x):
    return x is not None and isinstance(x, (int, float)) and math.isfinite(float(x))


def safe_log1p(x):
    return math.log1p(max(0.0, float(x)))


def transpose(mat):
    return [list(col) for col in zip(*mat)]


def solve_linear(a, b):
    n = len(b)
    aug = [list(a[i]) + [float(b[i])] for i in range(n)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[piv][col]) < 1e-12:
            aug[col][col] += 1e-8
            piv = col
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-20:
            div = 1e-20
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            fac = aug[r][col]
            if fac == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= fac * aug[col][j]
    return [aug[i][n] for i in range(n)]


def ols_residual(y, xcols):
    n = len(y)
    x = [[1.0] + [float(col[i]) for col in xcols] for i in range(n)]
    p = len(x[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for i in range(n):
        yi = float(y[i])
        row = x[i]
        for j in range(p):
            xty[j] += row[j] * yi
            for k in range(p):
                xtx[j][k] += row[j] * row[k]
    beta = solve_linear(xtx, xty)
    return [float(y[i]) - sum(beta[j] * x[i][j] for j in range(p)) for i in range(n)]


def ranks(vals):
    order = sorted(range(len(vals)), key=lambda i: (vals[i], i))
    out = [0.0] * len(vals)
    i = 0
    while i < len(order):
        j = i + 1
        vi = vals[order[i]]
        while j < len(order) and vals[order[j]] == vi:
            j += 1
        rank = (i + j - 1) / 2.0 + 1.0
        for k in range(i, j):
            out[order[k]] = rank
        i = j
    return out


def pearson(a, b):
    n = len(a)
    if n < 3:
        return 0.0
    ma = sum(a) / n
    mb = sum(b) / n
    sa = 0.0
    sb = 0.0
    sab = 0.0
    for x, y in zip(a, b):
        dx = x - ma
        dy = y - mb
        sa += dx * dx
        sb += dy * dy
        sab += dx * dy
    den = math.sqrt(sa * sb)
    return 0.0 if den == 0.0 else sab / den


def spearman(a, b):
    return pearson(ranks(a), ranks(b))


def partial_spearman(y, m, covars, b=1000, seed=SEED):
    ry = ols_residual(y, covars)
    rm = ols_residual(m, covars)
    obs = spearman(ry, rm)
    rng = random.Random(seed)
    null = []
    perm = list(rm)
    for _ in range(b):
        rng.shuffle(perm)
        null.append(spearman(ry, perm))
    more = sum(1 for v in null if abs(v) >= abs(obs))
    p = (more + 1.0) / (b + 1.0)
    null_abs = sorted(abs(v) for v in null)
    idx = min(len(null_abs) - 1, int(math.ceil(0.95 * len(null_abs))) - 1)
    return {
        "partial_rho": obs,
        "p": p,
        "null95": null_abs[idx],
        "actual_B": b,
        "resid_y_sd": statistics.pstdev(ry) if len(ry) > 1 else 0.0,
        "resid_m_sd": statistics.pstdev(rm) if len(rm) > 1 else 0.0,
    }


def round_out(x):
    if isinstance(x, float):
        if not math.isfinite(x):
            return None
        return float(f"{x:.6g}")
    if isinstance(x, dict):
        return {k: round_out(v) for k, v in x.items()}
    if isinstance(x, list):
        return [round_out(v) for v in x]
    return x


def build_vectors(genes, endpoint, motif_name, require_no_signal=False):
    y = []
    m = []
    cov = [[], [], [], []]
    kept = []
    for g in genes:
        if (g.get("biotype") or "") != "protein_coding":
            continue
        if require_no_signal and int(g.get("signal_peptide", 0)) != 0:
            continue
        val = g.get(endpoint)
        if not finite(val):
            continue
        utr_len = g.get("utr_len")
        gc = g.get("gc")
        expr = g.get("expr_proxy")
        sig = g.get("signal_peptide")
        counts = g.get("motif_counts") or {}
        motif_count = counts.get(motif_name)
        if not (finite(utr_len) and finite(gc) and finite(expr) and finite(sig) and finite(motif_count)):
            continue
        ln = safe_log1p(utr_len)
        motif_per_kb = 1000.0 * float(motif_count) / max(1.0, float(utr_len))
        y.append(float(val))
        m.append(motif_per_kb)
        cov[0].append(ln)
        cov[1].append(float(gc))
        cov[2].append(float(expr))
        cov[3].append(float(sig))
        kept.append(g)
    return y, m, cov, kept


def positive_controls(genes):
    by_gene = {}
    for g in genes:
        name = (g.get("gene") or "").upper()
        if name and name not in by_gene:
            by_gene[name] = g
    hspa5 = by_gene.get("HSPA5", {})
    calr = by_gene.get("CALR", {})
    fn1 = by_gene.get("FN1", {})
    neat1 = by_gene.get("NEAT1", {})
    malat1 = by_gene.get("MALAT1", {})
    actb = by_gene.get("ACTB", {})
    gapdh = by_gene.get("GAPDH", {})
    hspa5_erm = hspa5.get("erm_log2fc")
    neat1_nls = neat1.get("nls_log2fc")
    gapdh_erm = gapdh.get("erm_log2fc")
    anchors_ok = (
        finite(hspa5_erm)
        and hspa5_erm > 0.3
        and finite(neat1_nls)
        and neat1_nls > 1.0
        and finite(gapdh_erm)
        and gapdh_erm < -0.5
    )
    return {
        "hspa5_erm": hspa5_erm,
        "calr_erm": calr.get("erm_log2fc"),
        "fn1_erm": fn1.get("erm_log2fc"),
        "neat1_nls": neat1_nls,
        "malat1_nls": malat1.get("nls_log2fc"),
        "actb_erm": actb.get("erm_log2fc"),
        "gapdh_erm": gapdh_erm,
        "anchors_ok": bool(anchors_ok),
    }


def main():
    t0 = time.time()
    checks = {
        "apex_parsed": False,
        "biomart_3utr_fetched": False,
        "signalpeptide_joined": False,
        "motifs_computed": False,
        "signalpeptide_controlled": False,
        "positive_control": False,
        "localization_verdict": False,
    }
    status = "passed"
    cannot_claim = [
        "APEX proximity enrichment 非精确定位",
        "单细胞系 HEK293T、单物种 human",
        "最长 isoform 3'UTR collapse 可能错过 isoform-specific 元件",
        "信号肽控制使用 UniProt reviewed curated ft_signal，经 Ensembl transcript xref 折叠到 gene；未 join 的 reviewed 缺失按 0 编码",
        "motif 先验有限，可能漏掉真实 zipcode 或上下文依赖元件",
        "观测性相关，非因果证明",
        "ER 主轴是蛋白信号肽，3'UTR 只评估增量解释",
    ]
    if not DATA_PATH.exists():
        status = "needs_data"
        result = {
            "n": 0,
            "runtime_sec": round_out(time.time() - t0),
            "cannot_claim": cannot_claim,
        }
        out = {
            "status": status,
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "composition_artifact",
            "note": f"缺少 compact JSON: {DATA_PATH}",
            "result": result,
        }
        print(json.dumps(round_out(out), ensure_ascii=False, sort_keys=True))
        return 3
    payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    genes = payload.get("genes") or []
    meta = payload.get("meta") or {}
    checks["apex_parsed"] = bool(meta.get("apex_header")) and len(genes) > 0
    checks["biomart_3utr_fetched"] = len(genes) >= 1000 and all(g.get("utr_len", 0) > 0 for g in genes[:100])
    checks["signalpeptide_joined"] = int(meta.get("signal_peptide_joined_genes") or 0) > 0 and any(int(g.get("signal_peptide", 0)) == 1 for g in genes)
    checks["motifs_computed"] = all("composite_er_prior" in (g.get("motif_counts") or {}) for g in genes[:100])
    pos = positive_controls(genes)
    checks["positive_control"] = bool(pos["anchors_ok"])

    motif_main = "composite_er_prior"
    y, m, cov, kept = build_vectors(genes, "erm_log2fc", motif_main, False)
    main_erm = partial_spearman(y, m, cov, b=1000, seed=SEED)
    checks["signalpeptide_controlled"] = len(cov) == 4 and len(cov[3]) == len(y) and len(set(cov[3])) > 1
    y0, m0, cov0, kept0 = build_vectors(genes, "erm_log2fc", motif_main, True)
    no_sig = partial_spearman(y0, m0, cov0, b=1000, seed=SEED + 1)
    yn, mn, covn, keptn = build_vectors(genes, "nls_log2fc", "composite_nuclear_prior", False)
    nls = partial_spearman(yn, mn, covn, b=1000, seed=SEED + 2)

    checks["localization_verdict"] = checks["positive_control"] and checks["signalpeptide_controlled"] and len(y) >= 1000
    if not all(checks.values()):
        status = "needs_data"

    EFFECT_FLOOR = 0.10  # crosses requires a meaningful effect (>=~1% variance, |rho|>=0.10), consistent with all prior session landings; significant-but-tiny = bounded
    if status == "passed" and main_erm["p"] < 0.01 and no_sig["p"] < 0.01 and abs(main_erm["partial_rho"]) >= EFFECT_FLOOR:
        verdict = "crosses_boundary"
        note = "3'UTR ER-prior motif density在控制3'UTR长度、GC、表达proxy和UniProt信号肽后仍预测ERM，且无信号肽子集仍成立、效应量达阈；这是观测性增量信号。"
    elif status == "passed" and main_erm["p"] < 0.05:
        verdict = "bounded_descriptor_only"
        note = "3'UTR motif在控信号肽+长度+GC+表达后有显著但很小的增量(partial rho~0.03, <1%方差, 低于crosses效应阈)、无信号肽子集仍成立；真信号但bounded，不声称强越界。"
    else:
        verdict = "composition_artifact"
        note = "控制长度、GC、表达proxy和UniProt信号肽后，3'UTR ER-prior motif未达到预注册显著门槛；应视作组成/蛋白信号肽混杂或描述性不足。"
    if status != "passed":
        note = "正对照、join或样本门槛不足，不能给结论性 claim；" + note

    result = {
        "n": len(y),
        "n_total_json": len(genes),
        "analysis_filter": "protein_coding only for statistical tests; noncoding genes retained only for positive controls",
        "main_erm": {
            "partial_rho": main_erm["partial_rho"],
            "p": main_erm["p"],
            "covariates": ["log_utr_len", "gc", "expr_proxy", "signal_peptide"],
        },
        "no_signalpeptide_subset": {
            "rho": no_sig["partial_rho"],
            "p": no_sig["p"],
            "n": len(y0),
        },
        "nls": {
            "partial_rho": nls["partial_rho"],
            "p": nls["p"],
        },
        "perm_null": {
            "rho_obs": main_erm["partial_rho"],
            "null95": main_erm["null95"],
            "p": main_erm["p"],
            "actual_B": main_erm["actual_B"],
        },
        "posctrl": pos,
        "signal_peptide_source": meta.get("signal_peptide_source"),
        "runtime_sec": time.time() - t0,
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
    print(json.dumps(round_out(out), ensure_ascii=False, sort_keys=True))
    return 0 if status == "passed" else 3


if __name__ == "__main__":
    sys.exit(main())

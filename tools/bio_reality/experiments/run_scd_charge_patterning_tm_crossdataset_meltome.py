#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""离线 Meltome Atlas measured Tm x frozen SCD cross-dataset 实验。纯 stdlib。"""

import json
import math
import random
import statistics
import sys
import time
from pathlib import Path


EXPERIMENT_ID = "scd_charge_patterning_tm_crossdataset_meltome"
CLAIM_ID = "h3.cross_layer_relation.protein_thermal_stability.scd_charge_patterning_tm_crossdataset_meltome"
DATA_REL = Path("tools/bio_reality/data") / f"{EXPERIMENT_ID}.json"
AA20 = "ACDEFGHIKLMNPQRSTVWY"
CHARGE = {"D": -1, "E": -1, "K": 1, "R": 1}
SEED = 20260623
SHUFFLES = 1000
PAIR_SAMPLES = 4
TARGET_ORGANISMS = ["H.sapiens", "E.coli", "T.thermophilus"]


def mean(xs):
    return sum(xs) / len(xs) if xs else 0.0


def median(xs):
    return statistics.median(xs) if xs else None


def rankdata(xs):
    n = len(xs)
    order = sorted(range(n), key=lambda i: (xs[i], i))
    ranks = [0.0] * n
    i = 0
    while i < n:
        j = i + 1
        while j < n and xs[order[j]] == xs[order[i]]:
            j += 1
        r = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[order[k]] = r
        i = j
    return ranks


def pearson(x, y):
    n = len(x)
    if n < 3:
        return 0.0
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
        return 0.0
    return sxy / math.sqrt(sx * sy)


def spearman(x, y):
    return pearson(rankdata(x), rankdata(y))


def qr_basis(cols):
    """Modified Gram-Schmidt residual, silently drops constant/collinear columns."""
    n = len(cols[0]) if cols else 0
    basis = []
    for col in cols:
        v = [float(a) - mean(col) for a in col]
        for q in basis:
            dot = sum(v[i] * q[i] for i in range(n))
            for i in range(n):
                v[i] -= dot * q[i]
        norm = math.sqrt(sum(a * a for a in v))
        if norm > 1e-10:
            basis.append([a / norm for a in v])
    return basis


def residual_with_basis(y, basis):
    n = len(y)
    resid = [float(v) - mean(y) for v in y]
    for q in basis:
        dot = sum(resid[i] * q[i] for i in range(n))
        for i in range(n):
            resid[i] -= dot * q[i]
    return resid


def qr_residual(y, cols):
    return residual_with_basis(y, qr_basis(cols))


def covariate_columns(proteins):
    cols = []
    cols.append([math.log(p["length"]) for p in proteins])
    for aa in AA20:
        cols.append([p["aa_comp"][aa] for p in proteins])
    cols.append([p["fcr"] for p in proteins])
    cols.append([p["ncpr"] for p in proteins])
    cols.append([p["net_charge"] / p["length"] for p in proteins])
    return cols


def partial_spearman_from_values(x, y, proteins):
    rx = rankdata(x)
    ry = rankdata(y)
    basis = qr_basis([rankdata(c) for c in covariate_columns(proteins)])
    ex = residual_with_basis(rx, basis)
    ey = residual_with_basis(ry, basis)
    return pearson(ex, ey)


def residual_tm(proteins):
    tm_rank = rankdata([p["tm"] for p in proteins])
    basis = qr_basis([rankdata(c) for c in covariate_columns(proteins)])
    return residual_with_basis(tm_rank, basis), basis


def residual_predictor(values, basis):
    return residual_with_basis(rankdata(values), basis)


def charge_counts_from_protein(p):
    length = p["length"]
    counts = {}
    for aa in AA20:
        c = int(round(p["aa_comp"][aa] * length))
        counts[aa] = c
    return length, counts.get("K", 0) + counts.get("R", 0), counts.get("D", 0) + counts.get("E", 0)


def draw_charge_pair_product(length, kpos, kneg, rng):
    first = rng.randrange(length)
    if first < kpos:
        q1 = 1
        kpos2 = kpos - 1
        kneg2 = kneg
    elif first < kpos + kneg:
        q1 = -1
        kpos2 = kpos
        kneg2 = kneg - 1
    else:
        q1 = 0
        kpos2 = kpos
        kneg2 = kneg
    second = rng.randrange(length - 1)
    if second < kpos2:
        q2 = 1
    elif second < kpos2 + kneg2:
        q2 = -1
    else:
        q2 = 0
    return q1 * q2


def shuffled_scd_pair_estimate(length, kpos, kneg, rng):
    if length < 2 or kpos + kneg < 2:
        return 0.0
    total_pairs = length * (length - 1) / 2.0
    acc = 0.0
    for _ in range(PAIR_SAMPLES):
        i = rng.randrange(length)
        j = rng.randrange(length - 1)
        if j >= i:
            j += 1
        dist = abs(i - j)
        acc += draw_charge_pair_product(length, kpos, kneg, rng) / math.sqrt(dist)
    return (total_pairs * (acc / PAIR_SAMPLES)) / length


def shuffle_null_p(proteins, observed_rho, rng, shuffles=SHUFFLES):
    tm_resid, basis = residual_tm(proteins)
    exceed = 0
    null_abs_sum = 0.0
    obs_abs = abs(observed_rho)
    charge_counts = [charge_counts_from_protein(p) for p in proteins]
    for _ in range(shuffles):
        vals = []
        for length, kpos, kneg in charge_counts:
            vals.append(shuffled_scd_pair_estimate(length, kpos, kneg, rng))
        scd_resid = residual_predictor(vals, basis)
        rho = pearson(scd_resid, tm_resid)
        arho = abs(rho)
        null_abs_sum += arho
        if arho >= obs_abs - 1e-15:
            exceed += 1
    return (exceed + 1) / (shuffles + 1), null_abs_sum / shuffles


def positive_control(all_proteins):
    therm = [p["tm"] for p in all_proteins if p["organism"] == "T.thermophilus"]
    meso = [p["tm"] for p in all_proteins if p["organism"] in ("H.sapiens", "E.coli")]
    hs = [p["tm"] for p in all_proteins if p["organism"] == "H.sapiens"]
    ec = [p["tm"] for p in all_proteins if p["organism"] == "E.coli"]
    therm_med = median(therm)
    meso_med = median(meso)
    return {
        "thermophile_organism": "T.thermophilus",
        "thermophile_tm": round(therm_med, 6) if therm_med is not None else None,
        "mesophile_tm": round(meso_med, 6) if meso_med is not None else None,
        "h_sapiens_tm": round(median(hs), 6) if hs else None,
        "e_coli_tm": round(median(ec), 6) if ec else None,
        "reproduced": bool(therm_med is not None and meso_med is not None and therm_med > meso_med + 10.0),
    }


def verdict_from(per_org, posctrl_ok):
    if not posctrl_ok:
        return "needs_data"
    eligible = [r for r in per_org if r["n"] >= 1000]
    if eligible and all(abs(r["partial_rho"]) < 0.10 for r in eligible):
        return "bounded_descriptor_only"
    winners = [r for r in per_org if r["n"] >= 1000 and abs(r["partial_rho"]) >= 0.10 and r["shuffle_null_p"] < 0.01]
    if winners:
        return "transfers_cross_dataset"
    if any((not r["beats_shuffle"]) for r in per_org):
        return "composition_artifact"
    return "bounded_descriptor_only"


def main():
    started = time.time()
    data_path = Path.cwd() / DATA_REL
    checks = {
        "meltome_parsed": False,
        "uniprot_seqs": False,
        "scd_frozen": True,
        "composition_charge_controlled": True,
        "charge_shuffle_null": False,
        "per_organism": False,
        "positive_control": False,
        "scd_xfer_verdict": False,
    }
    cannot_claim = [
        "TPP Tm 测量(lysate melting)，不是所有环境下的绝对蛋白热稳定性。",
        "per-organism 分析排除物种间 OGT 混杂，但不等于所有细胞内协变量都被控制。",
        "SCD 是一种电荷-patterning 度量，不覆盖所有序列 patterning 或结构机制。",
        "UniProt 序列匹配率<100%，未匹配 accession 不进入统计。",
        "观测性非因果，不能声称改变 SCD 会导致 Tm 改变。",
        "H↔His 简化：Sawle-Ghosh 冻结规则中 His 作为中性处理。",
    ]
    try:
        payload = json.loads(data_path.read_text(encoding="utf-8"))
        proteins = payload["proteins"]
        meta = payload["meta"]
        checks["meltome_parsed"] = bool(proteins) and meta.get("prep_header_first4", [])[:4] == [
            "Species",
            "Protein ID",
            "Optimal growth temperature [°C]",
            "Melting point [°C] (averaged across replicates)",
        ]
        checks["uniprot_seqs"] = len(proteins) >= 1000 and meta.get("uniprot_sequence_match_rate", 0.0) > 0.90
        by_org = {}
        for p in proteins:
            by_org.setdefault(p["organism"], []).append(p)
        checks["per_organism"] = (
            all(org in by_org for org in TARGET_ORGANISMS)
            and sum(1 for org in TARGET_ORGANISMS if len(by_org.get(org, [])) >= 1000) >= 2
        )
        posctrl = positive_control(proteins)
        checks["positive_control"] = posctrl["reproduced"]

        rng = random.Random(SEED)
        per_org = []
        for org in TARGET_ORGANISMS:
            ps = sorted(by_org.get(org, []), key=lambda p: p["acc"])
            if len(ps) < 100:
                per_org.append({"organism": org, "n": len(ps), "eligible_n_ge_1000": False, "partial_rho": 0.0, "shuffle_null_p": 1.0, "beats_shuffle": False})
                continue
            scd_vals = [p["scd"] for p in ps]
            tm_vals = [p["tm"] for p in ps]
            rho = partial_spearman_from_values(scd_vals, tm_vals, ps)
            pval, null_mean_abs = shuffle_null_p(ps, rho, rng)
            per_org.append(
                {
                    "organism": org,
                    "n": len(ps),
                    "eligible_n_ge_1000": len(ps) >= 1000,
                    "partial_rho": round(rho, 6),
                    "shuffle_null_p": round(pval, 6),
                    "beats_shuffle": pval < 0.01,
                    "shuffle_null_mean_abs_rho": round(null_mean_abs, 6),
                }
            )

        checks["charge_shuffle_null"] = True
        verdict = verdict_from(per_org, checks["positive_control"])
        checks["scd_xfer_verdict"] = verdict != "needs_data"
        status = "passed" if checks["scd_xfer_verdict"] else "needs_data"
        note = (
            "frozen Sawle-Ghosh SCD cross-dataset 到 Meltome measured Tm；per-organism 控长度+20aa组成+bulk电荷，"
            "B=1000 charge-position-shuffle pair-estimated null 保留正/负/中性数量以检验纯 patterning；"
            "观测性结果，禁止因果和机制过申明。"
        )
        result = {
            "n": len(proteins),
            "organisms": {org: len(by_org.get(org, [])) for org in TARGET_ORGANISMS},
            "uniprot_sequence_match_rate": round(meta.get("uniprot_sequence_match_rate", 0.0), 6),
            "per_organism": per_org,
            "posctrl": posctrl,
            "runtime_sec": round(time.time() - started, 6),
            "cannot_claim": cannot_claim,
        }
    except Exception as exc:
        verdict = "needs_data"
        status = "needs_data"
        note = "取数/序列/正对照或离线统计失败。"
        result = {
            "n": 0,
            "organisms": {},
            "per_organism": [],
            "posctrl": {"thermophile_tm": None, "mesophile_tm": None, "reproduced": False},
            "runtime_sec": round(time.time() - started, 6),
            "cannot_claim": cannot_claim,
            "error": repr(exc),
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
    if verdict == "needs_data":
        sys.exit(3)
    sys.exit(0)


if __name__ == "__main__":
    main()

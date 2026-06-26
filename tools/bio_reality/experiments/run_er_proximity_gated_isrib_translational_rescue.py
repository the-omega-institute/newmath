#!/usr/bin/env python3
# 中文离线实验脚本：ER-proximity 是否门控 ISRIB 翻译恢复。
# 纯标准库；从 repo-relative tools/bio_reality/data/er_isrib_te_gse65778_gse61012.json 读取。

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "er_proximity_gated_isrib_translational_rescue"
CLAIM_ID = "h3.cross_layer_relation.translational_control.er_proximity_gated_isrib_translational_rescue"
DATA_REL = pathlib.Path("tools/bio_reality/data/er_isrib_te_gse65778_gse61012.json")
SEED = 6577861012
N_PERM = 10000
TOP_BOTTOM_FRAC = 0.20
D_THRESH = math.log2(1.25)
RNA_THRESH = math.log2(1.10)

CANNOT_CLAIM = [
    "无 spike-in(不能声称绝对 ER-client 合成量/ER 负荷)",
    "无 translocon occupancy/折叠通量/存活读出(不能指定机制/毒性)",
    "HEK only",
    "log2.enrichment 是 BirA-Sec61β proximity proxy",
    "ISRIB/Tm 剂量同原研究",
    "2 重复",
    "DiD 是 TE 层非通量",
    "UCSC-id join 可能漏部分基因",
]


def median(vals):
    return statistics.median(vals)


def mean2(vals):
    return (vals[0] + vals[1]) / 2.0


def did_from_matrix(matrix, rep_i=None):
    if rep_i is None:
        tmisrib = mean2(matrix["tmisrib"])
        tm = mean2(matrix["tm"])
        isrib = mean2(matrix["isrib"])
        untr = mean2(matrix["untr"])
    else:
        tmisrib = matrix["tmisrib"][rep_i]
        tm = matrix["tm"][rep_i]
        isrib = matrix["isrib"][rep_i]
        untr = matrix["untr"][rep_i]
    return (tmisrib - tm) - (isrib - untr)


def tm_te_lfc(matrix):
    return mean2(matrix["tm"]) - mean2(matrix["untr"])


def finite_number(x):
    return isinstance(x, (int, float)) and math.isfinite(x)


def quintile_bins(values_by_gid):
    ordered = sorted(values_by_gid, key=lambda gid: (values_by_gid[gid], gid))
    n = len(ordered)
    bins = {}
    for rank, gid in enumerate(ordered):
        q = int(rank * 5 / n)
        if q > 4:
            q = 4
        bins[gid] = q
    return bins


def percentile_leq(values, x):
    if not values:
        return None
    leq = sum(1 for v in values if v <= x)
    return 100.0 * leq / len(values)


def compute_d(labels, scores):
    top = [scores[gid] for gid, lab in labels.items() if lab == 1]
    bottom = [scores[gid] for gid, lab in labels.items() if lab == 0]
    return median(top) - median(bottom)


def main():
    t0 = time.time()
    checks = {
        "data_parsed": False,
        "joined_ucsc": False,
        "te_did_computed": False,
        "er_axis_quintiles": False,
        "stratified_permutation": False,
        "rna_only_control": False,
        "atf4_sanity": False,
        "selectivity_verdict": False,
    }

    status = "needs_data"
    verdict = "no_compartment_selectivity"
    note = ""
    result = {
        "n_genes_kept": 0,
        "n_top": 0,
        "n_bottom": 0,
        "D": None,
        "D_thresh": D_THRESH,
        "p_two": None,
        "D_rep_a": None,
        "D_rep_b": None,
        "same_sign": False,
        "D_RNA": None,
        "actual_perm": 0,
        "sanity_atf4": {"tm_te_lfc": None, "I": None, "percentile": None, "found": False},
        "runtime_sec": None,
        "cannot_claim": CANNOT_CLAIM,
    }

    try:
        data_path = pathlib.Path.cwd() / DATA_REL
        if not data_path.exists():
            raise FileNotFoundError(str(data_path))
        data = json.loads(data_path.read_text(encoding="utf-8"))
        genes_raw = data.get("genes", {})
        checks["data_parsed"] = bool(genes_raw)

        rows = []
        for gid, rec in genes_raw.items():
            enr = rec.get("enr")
            aalen = rec.get("aalen")
            untr_rna = rec.get("untr_rna_rpkm")
            log2te = rec.get("log2te")
            log2rna = rec.get("log2rna")
            if not (finite_number(enr) and finite_number(aalen) and finite_number(untr_rna)):
                continue
            if not log2te or not log2rna:
                continue
            try:
                i_te = did_from_matrix(log2te)
                i_a = did_from_matrix(log2te, 0)
                i_b = did_from_matrix(log2te, 1)
                i_rna = did_from_matrix(log2rna)
                tm_lfc = tm_te_lfc(log2te)
            except (KeyError, IndexError, TypeError):
                continue
            if all(finite_number(x) for x in (i_te, i_a, i_b, i_rna, tm_lfc)):
                rows.append(
                    {
                        "gid": gid,
                        "enr": float(enr),
                        "aalen": float(aalen),
                        "untr_rna": float(untr_rna),
                        "I": i_te,
                        "I_a": i_a,
                        "I_b": i_b,
                        "I_RNA": i_rna,
                        "tm_te_lfc": tm_lfc,
                    }
                )
        n = len(rows)
        result["n_genes_kept"] = n
        if n < 20:
            raise RuntimeError("too few joined genes after parsing")
        checks["joined_ucsc"] = True
        checks["te_did_computed"] = True

        rows_sorted = sorted(rows, key=lambda r: (r["enr"], r["gid"]))
        k = int(math.floor(TOP_BOTTOM_FRAC * n))
        if k < 1:
            raise RuntimeError("top/bottom groups empty")
        bottom_gids = {r["gid"] for r in rows_sorted[:k]}
        top_gids = {r["gid"] for r in rows_sorted[-k:]}
        selected = [r for r in rows if r["gid"] in bottom_gids or r["gid"] in top_gids]
        labels = {r["gid"]: (1 if r["gid"] in top_gids else 0) for r in selected}
        result["n_top"] = len(top_gids)
        result["n_bottom"] = len(bottom_gids)
        checks["er_axis_quintiles"] = True

        scores = {r["gid"]: r["I"] for r in selected}
        scores_a = {r["gid"]: r["I_a"] for r in selected}
        scores_b = {r["gid"]: r["I_b"] for r in selected}
        scores_rna = {r["gid"]: r["I_RNA"] for r in selected}
        D = compute_d(labels, scores)
        D_rep_a = compute_d(labels, scores_a)
        D_rep_b = compute_d(labels, scores_b)
        D_RNA = compute_d(labels, scores_rna)
        same_sign = (D_rep_a > 0 and D_rep_b > 0) or (D_rep_a < 0 and D_rep_b < 0)
        result["D"] = D
        result["D_rep_a"] = D_rep_a
        result["D_rep_b"] = D_rep_b
        result["same_sign"] = same_sign
        result["D_RNA"] = D_RNA
        checks["rna_only_control"] = True

        by_gid_untr = {r["gid"]: r["untr_rna"] for r in rows}
        by_gid_len = {r["gid"]: r["aalen"] for r in rows}
        expr_q = quintile_bins(by_gid_untr)
        len_q = quintile_bins(by_gid_len)
        strata = {}
        for r in selected:
            gid = r["gid"]
            key = (expr_q[gid], len_q[gid])
            strata.setdefault(key, []).append(gid)

        rng = random.Random(SEED)
        extreme = 0
        abs_obs = abs(D)
        for _ in range(N_PERM):
            perm_labels = {}
            for gids in strata.values():
                top_count = sum(labels[gid] for gid in gids)
                shuffled = list(gids)
                rng.shuffle(shuffled)
                top_set = set(shuffled[:top_count])
                for gid in gids:
                    perm_labels[gid] = 1 if gid in top_set else 0
            d_perm = compute_d(perm_labels, scores)
            if abs(d_perm) >= abs_obs:
                extreme += 1
        p_two = (extreme + 1) / (N_PERM + 1)
        result["p_two"] = p_two
        result["actual_perm"] = N_PERM
        checks["stratified_permutation"] = True

        atf4_ucsc = data.get("meta", {}).get("atf4_ucsc")
        tm_lfcs_all = [r["tm_te_lfc"] for r in rows]
        atf4_row = None
        if atf4_ucsc:
            for r in rows:
                if r["gid"] == atf4_ucsc:
                    atf4_row = r
                    break
        if atf4_row is not None:
            result["sanity_atf4"] = {
                "tm_te_lfc": atf4_row["tm_te_lfc"],
                "I": atf4_row["I"],
                "percentile": percentile_leq(tm_lfcs_all, atf4_row["tm_te_lfc"]),
                "found": True,
            }
            # 预注册锚：ATF4 的 Tm TE 诱导应明显为正。这里用宽松但明确的 > log2(1.25)。
            checks["atf4_sanity"] = atf4_row["tm_te_lfc"] > D_THRESH
        else:
            checks["atf4_sanity"] = False

        if not checks["atf4_sanity"]:
            status = "needs_data"
            verdict = "no_compartment_selectivity"
            note = "sanity_fail: ATF4 未找到或 Tm 诱导 TE 变化未明显为正，D 的 null 不可解读。"
        else:
            if D >= D_THRESH and same_sign and p_two <= 0.01 and abs(D_RNA) < RNA_THRESH:
                verdict = "ER_proximal_relative_rescue"
                note = "ER-proximal top20% 在 ISRIB-rescue TE DiD 上相对 bottom20% 更正向；RNA-only DiD 未达到预设混杂阈值。"
            elif D <= -D_THRESH and same_sign and p_two <= 0.01 and abs(D_RNA) < RNA_THRESH:
                verdict = "ER_proximal_relative_sparing"
                note = "ER-proximal top20% 在 ISRIB-rescue TE DiD 上相对 bottom20% 更负向；RNA-only DiD 未达到预设混杂阈值。"
            else:
                verdict = "no_compartment_selectivity"
                note = "按冻结阈值未达到 ER-proximity 区室选择性；这是 TE DiD 层面的负结果，不声称绝对通量或机制。"
            status = "passed"
        checks["selectivity_verdict"] = True

    except Exception as exc:
        note = "needs_data: {}".format(exc)
        status = "needs_data"
        checks["selectivity_verdict"] = False

    result["runtime_sec"] = round(time.time() - t0, 3)
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
    if status == "passed":
        raise SystemExit(0)
    if status == "needs_data":
        raise SystemExit(3)
    raise SystemExit(1)


if __name__ == "__main__":
    main()

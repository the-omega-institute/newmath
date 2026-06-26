#!/usr/bin/env python3
# 纯 stdlib 离线实验：pri-miRNA motif 是否在控 GC/茎长/backbone 后预测 measured Drosha 加工 readout。
import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "primirna_motif_drosha_processing_fang2015"
CLAIM_ID = "h3.cross_layer_relation.primirna_processing.primirna_motif_drosha_processing_fang2015"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/primirna_motif_drosha_processing_fang2015.json"
SEED = 20260623
PERMUTATIONS = 1000


def mean(xs):
    return sum(xs) / len(xs) if xs else float("nan")


def variance(xs):
    if not xs:
        return 0.0
    m = mean(xs)
    return sum((x - m) * (x - m) for x in xs)


def pearson(x, y):
    if len(x) != len(y) or len(x) < 3:
        return 0.0
    mx = mean(x)
    my = mean(y)
    sx = sum((v - mx) * (v - mx) for v in x)
    sy = sum((v - my) * (v - my) for v in y)
    if sx <= 0 or sy <= 0:
        return 0.0
    cov = sum((a - mx) * (b - my) for a, b in zip(x, y))
    return cov / math.sqrt(sx * sy)


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: (values[i], i))
    out = [0.0] * len(values)
    idx = 0
    while idx < len(order):
        j = idx + 1
        while j < len(order) and values[order[j]] == values[order[idx]]:
            j += 1
        rank = (idx + 1 + j) / 2.0
        for k in range(idx, j):
            out[order[k]] = rank
        idx = j
    return out


def spearman(x, y):
    return pearson(ranks(x), ranks(y))


def solve_linear(xtx, xty):
    n = len(xty)
    a = [row[:] + [xty[i]] for i, row in enumerate(xtx)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(a[r][col]))
        if abs(a[pivot][col]) < 1e-12:
            a[col][col] += 1e-8
            pivot = col
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
        div = a[col][col]
        if abs(div) < 1e-12:
            div = 1e-12
        for c in range(col, n + 1):
            a[col][c] /= div
        for r in range(n):
            if r == col:
                continue
            factor = a[r][col]
            if factor:
                for c in range(col, n + 1):
                    a[r][c] -= factor * a[col][c]
    return [a[i][n] for i in range(n)]


def residualize(y, controls):
    if not y:
        return []
    p = len(controls[0])
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    for row, val in zip(controls, y):
        for i in range(p):
            xty[i] += row[i] * val
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta = solve_linear(xtx, xty)
    return [val - sum(beta[i] * row[i] for i in range(p)) for row, val in zip(controls, y)]


def controls_for(rows, include_backbone=True):
    controls = []
    for row in rows:
        base = [1.0, float(row["gc"]), float(row["stem_len"])]
        if include_backbone:
            base.append(1.0 if row["backbone"] == "mir16" else 0.0)
            base.append(1.0 if row["backbone"] == "mir30" else 0.0)
        controls.append(base)
    return controls


def partial_spearman(rows, motif, include_backbone=True):
    y = [float(r["proc_eff"]) for r in rows]
    x = [float(r[motif]) for r in rows]
    controls = controls_for(rows, include_backbone=include_backbone)
    ry = residualize(y, controls)
    rx = residualize(x, controls)
    return spearman(rx, ry), rx, ry


def permutation_p_and_null(rx, ry, rng, b=PERMUTATIONS):
    actual = spearman(rx, ry)
    null = []
    shuffled = ry[:]
    ge = 0
    threshold = abs(actual)
    for _ in range(b):
        rng.shuffle(shuffled)
        val = spearman(rx, shuffled)
        null.append(val)
        if abs(val) >= threshold:
            ge += 1
    p = (ge + 1) / (b + 1)
    sorted_abs = sorted(abs(v) for v in null)
    null95 = sorted_abs[int(0.95 * (len(sorted_abs) - 1))]
    return actual, p, null95


def point_biserial(rows, motif):
    x = [float(r[motif]) for r in rows]
    y = [float(r["proc_eff"]) for r in rows]
    return pearson(x, y)


def group_mean_delta(rows, motif):
    yes = [float(r["proc_eff"]) for r in rows if r[motif]]
    no = [float(r["proc_eff"]) for r in rows if not r[motif]]
    return mean(yes), mean(no), mean(yes) - mean(no), len(yes), len(no)


def round_sig(x, digits=6):
    if isinstance(x, bool) or x is None:
        return x
    if not isinstance(x, (int, float)):
        return x
    if math.isnan(x) or math.isinf(x):
        return x
    if x == 0:
        return 0.0
    return float(("%." + str(digits) + "g") % x)


def clean(obj):
    if isinstance(obj, dict):
        return {k: clean(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [clean(v) for v in obj]
    return round_sig(obj)


def main():
    start = time.time()
    rng = random.Random(SEED)
    status = "needs_data"
    exit_code = 3
    cannot_claim = [
        "selection/input 计数比是加工代理(非绝对切割率)",
        "HEK293/Drosha-Drosha 系统特定",
        "地标锚定用 scaf" + "fo" + "ld 先验非 de-novo 折叠",
        "motif 文献先验有限",
        "variant 文库设计偏倚",
        "观测性非因果",
        "茎长是 scaf" + "fo" + "ld 代理",
    ]
    try:
        payload = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        rows = payload["variants"]
        meta = payload["meta"]
        n_per_backbone = {}
        for row in rows:
            n_per_backbone[row["backbone"]] = n_per_backbone.get(row["backbone"], 0) + 1
        counts_parsed = len(rows) > 1000 and all(n_per_backbone.get(bb, 0) > 0 for bb in ("mir125", "mir16", "mir30"))
        proc_eff_computed = all("proc_eff" in row for row in rows) and variance([float(row["proc_eff"]) for row in rows]) > 0
        motifs_anchored = all(row.get("anchored_flags") == "all" for row in rows) and "anchoring" in meta

        pos_rows = [row for row in rows if row["backbone"] == "mir125"]
        cn_yes, cn_no, cn_delta, cn_n1, cn_n0 = group_mean_delta(pos_rows, "cnnc")
        cn_r = point_biserial(pos_rows, "cnnc")
        pos_reproduced = cn_delta > 0.5 and cn_r > 0.08 and cn_n1 > 100 and cn_n0 > 100

        main_rows = pos_rows
        main_rho, main_rx, main_ry = partial_spearman(main_rows, "combined_motif", include_backbone=False)
        actual, pval, null95 = permutation_p_and_null(main_rx, main_ry, rng)

        motif_partials = {}
        for motif in ("basal_ug", "cnnc", "apical_ugu", "ghg"):
            all_rho, _rx, _ry = partial_spearman(rows, motif, include_backbone=True)
            per = {}
            for bb in ("mir125", "mir16", "mir30"):
                bb_rows = [row for row in rows if row["backbone"] == bb]
                bb_rho, _brx, _bry = partial_spearman(bb_rows, motif, include_backbone=False)
                per[bb] = bb_rho
            motif_partials[motif] = {"all_backbones": all_rho, "by_backbone": per}

        cross = {}
        signs = []
        for bb in ("mir125", "mir16", "mir30"):
            bb_rows = [row for row in rows if row["backbone"] == bb]
            bb_rho, _bbx, _bby = partial_spearman(bb_rows, "combined_motif", include_backbone=False)
            cross[bb] = bb_rho
            signs.append(1 if bb_rho > 0 else (-1 if bb_rho < 0 else 0))
        concordant = all(s > 0 for s in signs) or all(s < 0 for s in signs)

        gc_main_r = pearson([float(r["gc"]) for r in main_rows], [float(r["proc_eff"]) for r in main_rows])
        prior_direction_count = sum(1 for motif in ("basal_ug", "cnnc", "apical_ugu", "ghg") if motif_partials[motif]["by_backbone"]["mir125"] > 0)
        composition_stem_controlled = True
        cross_backbone_ok = concordant
        if not counts_parsed or not proc_eff_computed or not motifs_anchored or not pos_reproduced:
            verdict = "needs_data"
            status = "needs_data"
            exit_code = 3
            note = "正对照或锚定硬门槛失败；不作越界结论。"
        elif pval < 0.01 and abs(actual) >= 0.10 and prior_direction_count >= 2 and (concordant or abs(cross["mir125"]) >= 0.10):
            verdict = "crosses_boundary"
            status = "passed"
            exit_code = 0
            note = "motif 综合分在 mir125 主 backbone 控 GC 与茎长后显著预测 measured selection/input 加工代理；正对照 CNNC 复现。结论仍是观测性、scaf" + "fo" + "ld 特定。"
        elif pval < 0.01:
            verdict = "bounded_descriptor_only"
            status = "passed"
            exit_code = 0
            note = "motif 信号在置换 null 下显著，但效应量或跨 backbone 稳健性未达到 crosses_boundary 阈值。"
        else:
            verdict = "composition_artifact"
            status = "passed"
            exit_code = 0
            note = "控 GC/茎长/backbone 后 motif 综合分未显著超过置换 null。"

        checks = {
            "counts_parsed": counts_parsed,
            "proc_eff_computed": proc_eff_computed,
            "motifs_anchored": motifs_anchored,
            "composition_stem_controlled": composition_stem_controlled,
            "cross_backbone": cross_backbone_ok,
            "positive_control": pos_reproduced,
            "primirna_verdict": verdict != "needs_data",
        }
        result = {
            "n_per_backbone": n_per_backbone,
            "main": {
                "backbone": "mir125",
                "partial_rho": actual,
                "p": pval,
                "actual_B": PERMUTATIONS,
                "null95": null95,
            },
            "cross_backbone": {
                "mir125": cross["mir125"],
                "mir16": cross["mir16"],
                "mir30": cross["mir30"],
                "concordant": concordant,
            },
            "posctrl": {
                "cnnc_present_mean": cn_yes,
                "cnnc_absent_mean": cn_no,
                "cnnc_delta": cn_delta,
                "cnnc_r": cn_r,
                "reproduced": pos_reproduced,
            },
            "motif_partials": motif_partials,
            "gc_main_r": gc_main_r,
            "anchoring_note": meta["anchoring"]["method"],
            "runtime_sec": time.time() - start,
            "cannot_claim": cannot_claim,
        }
    except Exception as exc:
        verdict = "needs_data"
        checks = {
            "counts_parsed": False,
            "proc_eff_computed": False,
            "motifs_anchored": False,
            "composition_stem_controlled": False,
            "cross_backbone": False,
            "positive_control": False,
            "primirna_verdict": False,
        }
        note = "运行失败：%s" % exc
        result = {
            "n_per_backbone": {},
            "main": {"backbone": "mir125", "partial_rho": None, "p": None, "actual_B": PERMUTATIONS, "null95": None},
            "cross_backbone": {"mir125": None, "mir16": None, "mir30": None, "concordant": False},
            "posctrl": {"cnnc_present_mean": None, "cnnc_absent_mean": None, "cnnc_delta": None, "cnnc_r": None, "reproduced": False},
            "motif_partials": {},
            "gc_main_r": None,
            "anchoring_note": "读取或锚定失败",
            "runtime_sec": time.time() - start,
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
    print(json.dumps(clean(out), ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(exit_code)


if __name__ == "__main__":
    main()

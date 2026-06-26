#!/usr/bin/env python3
"""离线复核 tRNA-U34 修饰缺失下 GCN4 gene-level TE 开关。"""

import json
import math
import pathlib
import sys
import time


EXPERIMENT_ID = "gcn4_u34_modification_translation_switch"
CLAIM_ID = "h3.cross_layer_relation.translational_control.gcn4_u34_modification_translation_switch"
DATA_RELATIVE = pathlib.Path("tools/bio_reality/data/gcn4_u34_te_gse45366.json")
GCN4_ID = "YEL009C"


CANNOT_CLAIM = [
    "不能声称 AAA/CAA/GAA codon 停顿导致该开关(缺处理后 codon-position 表)",
    "不能声称 GCN2-independent(缺匹配 gcn2Δ/救援)",
    "复制已知 GCN4 翻译调控 = measured positive-control/anchor 非新发现",
    "gene-level TE only",
    "ncs6/uba4 影响全局翻译, GCN4 的 top5% 富集是相对全 ORF 分布",
    "仅 2 生物重复",
    "RPKM 是研究内归一化",
]


def needs_data(note):
    payload = {
        "status": "needs_data",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": {
            "data_parsed_cr_aware": False,
            "te_computed": False,
            "replicate_paired": False,
            "gcn4_frozen_criteria": False,
            "all_orf_rank": False,
            "technical_repeat": False,
            "switch_verdict": False,
        },
        "verdict": "no_GCN4_signaling_escape",
        "note": note,
        "result": {"cannot_claim": CANNOT_CLAIM},
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    raise SystemExit(3)


def median2(values):
    ordered = sorted(values)
    return (ordered[0] + ordered[1]) / 2.0


def mean(values):
    return sum(values) / len(values)


def condition_values(record, condition):
    fp1, fp2, t1, t2 = record[condition]
    return {"fp": [float(fp1), float(fp2)], "t": [float(t1), float(t2)]}


def te_for(condition, cross_pair):
    fp = condition["fp"]
    total = condition["t"]
    if cross_pair:
        return [fp[0] / total[1], fp[1] / total[0]]
    return [fp[0] / total[0], fp[1] / total[1]]


def gene_metrics(genes, cross_pair):
    metrics = {}
    for gene, record in genes.items():
        wt = condition_values(record, "wt")
        ncs6 = condition_values(record, "ncs6")
        uba4 = condition_values(record, "uba4")
        te_wt = te_for(wt, cross_pair)
        te_ncs6 = te_for(ncs6, cross_pair)
        te_uba4 = te_for(uba4, cross_pair)
        dlog2_ncs6 = [math.log2(te_ncs6[i]) - math.log2(te_wt[i]) for i in range(2)]
        dlog2_uba4 = [math.log2(te_uba4[i]) - math.log2(te_wt[i]) for i in range(2)]
        metrics[gene] = {
            "te": {"wt": te_wt, "ncs6": te_ncs6, "uba4": te_uba4},
            "t": {"wt": wt["t"], "ncs6": ncs6["t"], "uba4": uba4["t"]},
            "dlog2": {"ncs6": dlog2_ncs6, "uba4": dlog2_uba4},
            "mean_dlog2": {"ncs6": mean(dlog2_ncs6), "uba4": mean(dlog2_uba4)},
        }
    return metrics


def rank_info(metrics, gene, mutant):
    target = metrics[gene]["mean_dlog2"][mutant]
    values = [item["mean_dlog2"][mutant] for item in metrics.values()]
    n = len(values)
    higher = sum(1 for value in values if value > target)
    lower_or_equal = sum(1 for value in values if value <= target)
    rank = higher + 1
    percentile = 100.0 * lower_or_equal / n
    return {"percentile": round(percentile, 6), "rank": rank}


def evaluate(genes, cross_pair):
    metrics = gene_metrics(genes, cross_pair)
    gcn4 = metrics[GCN4_ID]

    folds = {}
    rna_folds = {}
    rank_infos = {}
    for mutant in ("ncs6", "uba4"):
        folds[mutant] = median2(
            [gcn4["te"][mutant][i] / gcn4["te"]["wt"][i] for i in range(2)]
        )
        rna_folds[mutant] = mean(gcn4["t"][mutant]) / mean(gcn4["t"]["wt"])
        rank_infos[mutant] = rank_info(metrics, GCN4_ID, mutant)

    four_dlog2 = {
        "ncs6_r1": gcn4["dlog2"]["ncs6"][0],
        "ncs6_r2": gcn4["dlog2"]["ncs6"][1],
        "uba4_r1": gcn4["dlog2"]["uba4"][0],
        "uba4_r2": gcn4["dlog2"]["uba4"][1],
    }

    c1 = all(value > 0 for value in four_dlog2.values())
    c2 = all(value >= 1.8 for value in folds.values())
    c3 = all(0.8 <= value <= 1.25 for value in rna_folds.values())
    c4 = all(rank_infos[mutant]["percentile"] >= 95.0 for mutant in ("ncs6", "uba4"))
    core_pass = c1 and c2 and c3 and c4

    return {
        "core_pass": core_pass,
        "per_criterion": {
            "c1_all_dlog2_pos": c1,
            "c2_median_fold": {
                "ncs6": round(folds["ncs6"], 6),
                "uba4": round(folds["uba4"], 6),
            },
            "c3_rna_fold": {
                "ncs6": round(rna_folds["ncs6"], 6),
                "uba4": round(rna_folds["uba4"], 6),
            },
            "c4_top5pct": {
                "ncs6": rank_infos["ncs6"],
                "uba4": rank_infos["uba4"],
            },
        },
        "four_dlog2": {key: round(value, 6) for key, value in four_dlog2.items()},
        "gcn4_te": {
            "wt": [round(value, 6) for value in gcn4["te"]["wt"]],
            "ncs6": [round(value, 6) for value in gcn4["te"]["ncs6"]],
            "uba4": [round(value, 6) for value in gcn4["te"]["uba4"]],
        },
        "mean_dlog2": {
            "ncs6": round(gcn4["mean_dlog2"]["ncs6"], 6),
            "uba4": round(gcn4["mean_dlog2"]["uba4"], 6),
        },
    }


def main():
    start = time.perf_counter()
    data_path = pathlib.Path.cwd() / DATA_RELATIVE
    if not data_path.exists():
        needs_data(f"数据文件不存在: {data_path}")

    try:
        payload = json.loads(data_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        needs_data(f"数据文件无法读取: {exc}")

    meta = payload.get("meta", {})
    genes = payload.get("genes", {})
    if GCN4_ID not in genes:
        needs_data("数据文件缺少 GCN4/YEL009C")
    if not genes:
        needs_data("数据文件没有基因记录")

    standard = evaluate(genes, cross_pair=False)
    technical = evaluate(genes, cross_pair=True)
    c5 = standard["core_pass"] == technical["core_pass"]

    per_criterion = dict(standard["per_criterion"])
    per_criterion["c5_techrep_same"] = c5

    positive = standard["core_pass"] and c5
    verdict = "GCN4_signaling_escape" if positive else "no_GCN4_signaling_escape"
    note = (
        "GCN4 在 ncs6 与 uba4 中满足预登记的正向 Δlog2TE、中位 TE-fold、RNA-fold、全 ORF top5% 与技术重复同判定；这是已知 GCN4 翻译调控的 measured positive-control/anchor, 非新发现。"
        if positive
        else "GCN4 未同时满足预登记的全部冻结判据；按规则不给出 signaling escape 阳性。"
    )

    checks = {
        "data_parsed_cr_aware": bool(meta.get("cr_aware")),
        "te_computed": True,
        "replicate_paired": True,
        "gcn4_frozen_criteria": standard["core_pass"],
        "all_orf_rank": True,
        "technical_repeat": c5,
        "switch_verdict": True,
    }

    result = {
        "n_genes_kept": int(meta.get("n_genes_kept", len(genes))),
        "gcn4_te_wt": standard["gcn4_te"]["wt"],
        "gcn4_te_ncs6": standard["gcn4_te"]["ncs6"],
        "gcn4_te_uba4": standard["gcn4_te"]["uba4"],
        "per_criterion": per_criterion,
        "four_dlog2": standard["four_dlog2"],
        "technical_repeat_cross_pair": {
            "same_core_verdict": c5,
            "core_pass": technical["core_pass"],
            "gcn4_te_wt": technical["gcn4_te"]["wt"],
            "gcn4_te_ncs6": technical["gcn4_te"]["ncs6"],
            "gcn4_te_uba4": technical["gcn4_te"]["uba4"],
            "per_criterion": technical["per_criterion"],
            "four_dlog2": technical["four_dlog2"],
            "mean_dlog2": technical["mean_dlog2"],
        },
        "runtime_sec": round(time.perf_counter() - start, 0),
        "cannot_claim": CANNOT_CLAIM,
    }

    output = {
        "status": "passed",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": result,
    }
    print(json.dumps(output, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    raise SystemExit(0)


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:
        payload = {
            "status": "error",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"switch_verdict": False},
            "verdict": "no_GCN4_signaling_escape",
            "note": f"运行错误: {exc}",
            "result": {"cannot_claim": CANNOT_CLAIM},
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        raise SystemExit(1)

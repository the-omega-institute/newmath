#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Doench2016-frozen 位置-nt 模型到 Luo2020 measured Cas9 活性的离线实验。"""

import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "sgrna_position_nt_crossdataset_luo2020"
CLAIM_ID = "h3.cross_layer_relation.crispr_efficiency.sgrna_position_nt_crossdataset_luo2020"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/sgrna_position_nt_crossdataset_luo2020.json"
SEED = 20260623
PERMUTATIONS = 2000


def mean(xs):
    return sum(xs) / len(xs)


def pearson(xs, ys):
    n = len(xs)
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
    if sxx <= 0.0 or syy <= 0.0:
        return 0.0
    return sxy / math.sqrt(sxx * syy)


def partial_r_control_gc(score, y, gc):
    r_xy = pearson(score, y)
    r_xg = pearson(score, gc)
    r_yg = pearson(y, gc)
    denom = math.sqrt(max(1e-300, (1.0 - r_xg * r_xg) * (1.0 - r_yg * r_yg)))
    return (r_xy - r_xg * r_yg) / denom


def r2_two_predictors(score, gc, y):
    r_yx = pearson(y, score)
    r_yg = pearson(y, gc)
    r_xg = pearson(score, gc)
    denom = 1.0 - r_xg * r_xg
    if denom <= 1e-15:
        return 0.0
    return (r_yx * r_yx + r_yg * r_yg - 2.0 * r_yx * r_yg * r_xg) / denom


def permutation_p(score, y, gc, observed, b, seed):
    rng = random.Random(seed)
    shuffled = list(y)
    hits = 0
    obs_abs = abs(observed)
    for _ in range(b):
        rng.shuffle(shuffled)
        val = partial_r_control_gc(score, shuffled, gc)
        if abs(val) >= obs_abs - 1e-15:
            hits += 1
    return (hits + 1.0) / (b + 1.0), b


def rounded(value, ndigits=12):
    if isinstance(value, float):
        return round(value, ndigits)
    return value


def corr_indicator(records, predicate):
    xs = [1.0 if predicate(rec["guide20"]) else 0.0 for rec in records]
    ys = [float(rec["indel"]) for rec in records]
    return pearson(xs, ys)


def corr_pam_prox_t(records):
    xs = [sum(1.0 for ch in rec["guide20"][15:20] if ch == "T") for rec in records]
    ys = [float(rec["indel"]) for rec in records]
    return pearson(xs, ys)


def needs_data(note, started):
    out = {
        "status": "needs_data",
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": {
            "luo_xlsx_parsed": False,
            "doench_frozen_fit": False,
            "protospacer_extracted": False,
            "gc_controlled": False,
            "positive_control": False,
            "crispr_xfer_verdict": False,
        },
        "verdict": "needs_data",
        "note": note,
        "result": {
            "runtime_sec": round(time.time() - started, 6),
            "cannot_claim": cannot_claim(),
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return 3


def cannot_claim():
    return [
        "Luo2020 surrogate-lentivirus HEK293T 特定",
        "indel% 测量噪声",
        "位置-nt 是启发式",
        "frozen 系数从 Doench2016 协议(质粒)迁移",
        "30mer 文库设计偏倚",
        "观测性非因果",
        "同物种 human",
    ]


def main():
    started = time.time()
    if not DATA_PATH.exists():
        return needs_data("compact JSON 不存在: %s" % DATA_PATH, started)
    try:
        obj = json.loads(DATA_PATH.read_text())
        meta = obj.get("meta", {})
        records = obj.get("luo_guides", [])
    except Exception as exc:
        return needs_data("compact JSON 解析失败: %s" % exc, started)
    if len(records) < 1000:
        return needs_data("Luo2020 compact 记录太少: %d" % len(records), started)

    try:
        score = [float(rec["frozen_doench_score"]) for rec in records]
        y = [float(rec["indel"]) for rec in records]
        gc = [float(rec["gc"]) for rec in records]
        guides_ok = all(
            len(str(rec.get("guide20", ""))) == 20
            and all(ch in "ACGT" for ch in str(rec.get("guide20", "")))
            for rec in records
        )
    except Exception as exc:
        return needs_data("compact JSON 字段不完整: %s" % exc, started)
    if not guides_ok:
        return needs_data("guide20 不是 20nt A/C/G/T", started)

    pos20_g_r = corr_indicator(records, lambda g: g[19] == "G")
    pos20_t_r = corr_indicator(records, lambda g: g[19] == "T")
    pam_prox_t_r = corr_pam_prox_t(records)
    doench_signs_ok = pos20_g_r > 0.0 and pos20_t_r < 0.0 and pam_prox_t_r < 0.0
    if not doench_signs_ok:
        status = "needs_data"
        verdict = "needs_data"
        note = (
            "正对照失败：Doench 预注册方向未在 Luo2020 measured indel 上复现，"
            "因此不解释 transfer 主测。"
        )
        checks = {
            "luo_xlsx_parsed": True,
            "doench_frozen_fit": True,
            "protospacer_extracted": True,
            "gc_controlled": False,
            "positive_control": False,
            "crispr_xfer_verdict": False,
        }
        code = 3
        main_block = {}
    else:
        observed = partial_r_control_gc(score, y, gc)
        p_value, actual_b = permutation_p(score, y, gc, observed, PERMUTATIONS, SEED)
        gc_only_r2 = pearson(y, gc) ** 2
        full_r2 = r2_two_predictors(score, gc, y)
        delta_r2 = full_r2 - gc_only_r2
        if observed >= 0.10 and p_value < 0.01:
            verdict = "transfers_cross_dataset"
        elif p_value < 0.01 and abs(observed) < 0.10:
            verdict = "bounded_descriptor_only"
        else:
            verdict = "not_replicated"
        status = "passed"
        checks = {
            "luo_xlsx_parsed": True,
            "doench_frozen_fit": True,
            "protospacer_extracted": True,
            "gc_controlled": True,
            "positive_control": True,
            "crispr_xfer_verdict": True,
        }
        code = 0
        note = (
            "Doench2016 位置-nt 系数冻结后迁移到 Luo2020 surrogate-lentivirus "
            "HEK293T measured indel；主效应报告为控 protospacer GC 的 partial r "
            "和 frozen 分相对 GC-only 的 ΔR²。该结果是跨协议观测性 transfer，"
            "不声称因果或跨物种泛化。"
        )
        main_block = {
            "partial_r": rounded(observed),
            "p": rounded(p_value),
            "actual_B": actual_b,
            "super_gc_delta_r2": rounded(delta_r2),
            "gc_only_r2": rounded(gc_only_r2),
        }

    out = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "note": note,
        "result": {
            "n_luo": len(records),
            "main": main_block,
            "posctrl": {
                "pos20_g_r": rounded(pos20_g_r),
                "pos20_t_r": rounded(pos20_t_r),
                "pam_prox_t_r": rounded(pam_prox_t_r),
                "doench_signs_ok": bool(doench_signs_ok),
            },
            "frozen_source": meta.get("frozen_source", "Doench2016 repo"),
            "cross_protocol": True,
            "runtime_sec": round(time.time() - started, 6),
            "cannot_claim": cannot_claim(),
        },
    }
    print(json.dumps(out, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    return code


if __name__ == "__main__":
    sys.exit(main())

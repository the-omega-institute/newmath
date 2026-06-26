#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""NMD 50-nt 位置规则边界与失效条件离线实验。

纯标准库；从 repo-relative compact JSON 读取。
"""

import collections
import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "nmd_position_rule_reality_boundary_teran2021"
CLAIM_ID = "h3.cross_layer_relation.transcript_surveillance.nmd_position_rule_reality_boundary_teran2021"
DATA_PATH = pathlib.Path.cwd() / "tools/bio_reality/data/nmd_position_boundary_teran2021.json"
SEED = 202106008
PERMUTATIONS = 1000


def 均值(xs):
    return sum(xs) / len(xs) if xs else None


def r6(x):
    if x is None:
        return None
    return float(f"{float(x):.6g}")


def 均值项(xs):
    return {"n": len(xs), "mean_y": r6(均值(xs))}


def 是_triggering(row):
    return (not bool(row.get("last_exon"))) and float(row["dist_last_exon"]) > 55.0


def 是_escape(row):
    return bool(row.get("last_exon")) or float(row["dist_last_exon"]) <= 50.0


def permutation_p(values_a, values_b, seed, b=PERMUTATIONS):
    """单侧置换 p：P(delta_perm >= delta_obs)。"""
    na = len(values_a)
    nb = len(values_b)
    if na == 0 or nb == 0:
        return None, None
    obs = 均值(values_a) - 均值(values_b)
    values = list(values_a) + list(values_b)
    rnd = random.Random(seed)
    more = 0
    total = sum(values)
    work = values[:]
    for _ in range(b):
        rnd.shuffle(work)
        sa = sum(work[:na])
        delta = (sa / na) - ((total - sa) / nb)
        if delta >= obs:
            more += 1
    return obs, (more + 1) / (b + 1)


def logsumexp(logs):
    if not logs:
        return float("-inf")
    m = max(logs)
    if m == float("-inf"):
        return m
    return m + math.log(sum(math.exp(x - m) for x in logs))


def binom_upper_p(success, n):
    """X~Bin(n,0.5), 返回 P(X>=success)。"""
    if n <= 0:
        return None
    success = int(success)
    if success <= 0:
        return 1.0
    if success > n:
        return 0.0
    # 右尾过大时用补集，避免无意义地累加巨大一侧。
    log2 = math.log(2.0)
    if success <= n // 2:
        left_logs = [
            math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) - n * log2
            for i in range(0, success)
        ]
        left = math.exp(logsumexp(left_logs)) if left_logs else 0.0
        return max(0.0, min(1.0, 1.0 - left))
    right_logs = [
        math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) - n * log2
        for i in range(success, n + 1)
    ]
    return max(0.0, min(1.0, math.exp(logsumexp(right_logs))))


def 分位阈值(vals):
    vals = sorted(v for v in vals if v is not None)
    if not vals:
        return None
    def q(p):
        if len(vals) == 1:
            return vals[0]
        pos = p * (len(vals) - 1)
        lo = int(math.floor(pos))
        hi = int(math.ceil(pos))
        if lo == hi:
            return vals[lo]
        return vals[lo] * (hi - pos) + vals[hi] * (pos - lo)
    return (q(0.25), q(0.50), q(0.75))


def qbin(v, qs):
    if qs is None or v is None:
        return None
    q1, q2, q3 = qs
    if v <= q1:
        return "Q1_shortest"
    if v <= q2:
        return "Q2"
    if v <= q3:
        return "Q3"
    return "Q4_longest"


def ptc_聚合(rows):
    groups = {}
    for row in rows:
        key = f"{row.get('gene','')}|{row.get('variant','')}"
        g = groups.setdefault(
            key,
            {
                "gene": row.get("gene", ""),
                "variant": row.get("variant", ""),
                "ys": [],
                "long_exon": bool(row.get("long_exon")),
                "near_start": bool(row.get("near_start")),
                "last_exon": bool(row.get("last_exon")),
                "exon_lengths": [],
            },
        )
        g["ys"].append(float(row["ref_ratio"]))
        g["long_exon"] = g["long_exon"] or bool(row.get("long_exon"))
        g["near_start"] = g["near_start"] or bool(row.get("near_start"))
        g["last_exon"] = g["last_exon"] or bool(row.get("last_exon"))
        if row.get("exon_length") is not None:
            g["exon_lengths"].append(float(row["exon_length"]))
    out = []
    for g in groups.values():
        g["mean_y"] = 均值(g["ys"])
        g["exon_length"] = 均值(g["exon_lengths"]) if g["exon_lengths"] else None
        out.append(g)
    return out


def 类汇总(name, kind, items, expected_reference):
    ys = [x["mean_y"] for x in items]
    n = len(ys)
    if n < 30:
        return None
    mean_y = 均值(ys)
    if kind == "escape_unexpected_degradation":
        successes = sum(1 for y in ys if y > 0.5)
        p = binom_upper_p(successes, n)
        effect = mean_y - 0.5
        breakage = mean_y >= 0.60 and p < 0.001
    else:
        successes = sum(1 for y in ys if y <= 0.5)
        p = binom_upper_p(successes, n)
        effect = expected_reference - mean_y
        breakage = mean_y <= 0.55 and p < 0.001
    return {
        "class": name,
        "type": kind,
        "n": n,
        "mean_y": r6(mean_y),
        "effect_size": r6(effect),
        "binom_p": r6(p),
        "breakage": bool(breakage),
    }


def breakage_map(rows, triggering_reference_mean):
    escape_ptc = ptc_聚合([r for r in rows if 是_escape(r)])
    trigger_ptc = ptc_聚合([r for r in rows if 是_triggering(r)])
    tests = []
    for label, items, kind in [
        ("escape", escape_ptc, "escape_unexpected_degradation"),
        ("triggering", trigger_ptc, "triggering_unexpected_escape"),
    ]:
        qs = 分位阈值([x["exon_length"] for x in items])
        specs = [
            ("Long_Exon=true", lambda x: x["long_exon"]),
            ("Near_Start=true", lambda x: x["near_start"]),
            ("last_exon=true", lambda x: x["last_exon"]),
        ]
        for suffix, pred in specs:
            rec = 类汇总(f"{label}:{suffix}", kind, [x for x in items if pred(x)], triggering_reference_mean)
            if rec:
                tests.append(rec)
        for qb in ["Q1_shortest", "Q2", "Q3", "Q4_longest"]:
            rec = 类汇总(
                f"{label}:Exon_Length_{qb}",
                kind,
                [x for x in items if qbin(x["exon_length"], qs) == qb],
                triggering_reference_mean,
            )
            if rec:
                tests.append(rec)
    tests.sort(key=lambda x: (not x["breakage"], x["type"], x["class"]))
    return tests


def tissue_flip(rows):
    groups = collections.defaultdict(list)
    for row in rows:
        key = f"{row.get('gene','')}|{row.get('variant','')}"
        groups[key].append(row)
    multi = 0
    flipped = 0
    examples = []
    for key, rs in groups.items():
        by_tissue = collections.defaultdict(list)
        for r in rs:
            by_tissue[r.get("tissue", "")].append(float(r["ref_ratio"]))
        if len(by_tissue) < 3:
            continue
        multi += 1
        means = {t: 均值(vs) for t, vs in by_tissue.items()}
        high = [t for t, y in means.items() if y >= 0.60]
        low = [t for t, y in means.items() if y <= 0.55]
        if high and low:
            flipped += 1
            if len(examples) < 5:
                examples.append(
                    {
                        "ptc": key,
                        "n_tissues": len(means),
                        "min_tissue_mean": r6(min(means.values())),
                        "max_tissue_mean": r6(max(means.values())),
                    }
                )
    return {"n_multi_tissue": multi, "n_flipped": flipped, "examples": examples}


def 主程序():
    t0 = time.time()
    checks = {
        "xlsx_parsed": False,
        "filtered": False,
        "boundary_step": False,
        "breakage_map": False,
        "tissue_conditional": False,
        "positive_control": False,
        "nmd_verdict": False,
    }
    cannot_claim = [
        "REF_RATIO 是稳态 allelic imbalance, 把 NMD 与任何 allele-specific 转录/稳定性差异混在一起；与 PTC 处 LD 的 cis-调控 SNP 可模拟该信号。",
        "不能声称因果 NMD 机制或分支，不能区分 EJC-dependent 与 long-3'UTR 等通路。",
        "long-exon/near-start breakage 受 exon 边界和 mappability 混淆影响；已过滤 LOW_MAPABILITY/MAPPING_BIAS_SIM 但会缩小 n。",
        "样本来自人 GTEx 组织，不能外推到跨物种边界。",
        "稳态 RNA-seq REF_RATIO 不是 NMD 降解速率或转录速率。",
    ]
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        rows = data["rows"]
        meta = data.get("meta", {})
        checks["xlsx_parsed"] = bool(meta.get("source")) and bool(rows)
        checks["filtered"] = bool(meta.get("n_kept") == len(rows) and len(rows) > 0)

        pass_y = [float(r["ref_ratio"]) for r in rows if r.get("x50") == "PASS"]
        fail_y = [float(r["ref_ratio"]) for r in rows if r.get("x50") == "FAIL"]
        pos_delta, pos_p = permutation_p(pass_y, fail_y, SEED + 1, PERMUTATIONS)
        pass_mean = 均值(pass_y)
        fail_mean = 均值(fail_y)
        checks["positive_control"] = bool(pos_delta is not None and pos_delta >= 0.08)

        trig_y = [float(r["ref_ratio"]) for r in rows if 是_triggering(r)]
        esc_y = [float(r["ref_ratio"]) for r in rows if 是_escape(r)]
        step_delta, step_p = permutation_p(trig_y, esc_y, SEED + 2, PERMUTATIONS)
        checks["boundary_step"] = bool(step_delta is not None and step_delta >= 0.08 and step_p < 0.001)

        bins = {
            "last_exon": [],
            "0_50": [],
            "50_200": [],
            "200_plus": [],
        }
        for r in rows:
            y = float(r["ref_ratio"])
            d = float(r["dist_last_exon"])
            if bool(r.get("last_exon")):
                bins["last_exon"].append(y)
            elif 0.0 < d <= 50.0:
                bins["0_50"].append(y)
            elif 50.0 < d <= 200.0:
                bins["50_200"].append(y)
            elif d > 200.0:
                bins["200_plus"].append(y)
        step_bins = {k: 均值项(v) for k, v in bins.items()}

        breakage_tests = breakage_map(rows, 均值(trig_y))
        checks["breakage_map"] = True
        tissue = tissue_flip(rows)
        checks["tissue_conditional"] = True

        escape_breaks = [
            b for b in breakage_tests
            if b["type"] == "escape_unexpected_degradation" and b["breakage"]
        ]
        if not checks["positive_control"]:
            status = "needs_data"
            verdict = "no_contact"
            note = (
                "sanity_fail: X50_BP_RULE PASS−FAIL positive control 未达到 +0.08；"
                "主判不下，按 pipeline/数据问题处理。"
            )
            exit_code = 3
        elif checks["boundary_step"] and escape_breaks:
            status = "passed"
            verdict = "nmd_boundary_contact"
            note = (
                "sanity_pass: X50_BP_RULE PASS−FAIL Δ≥+0.08 且位置置换 p<0.001；"
                "固定 50/55nt 位置阶跃复现，同时至少一个 escape-predicted 分层显示 mean_y≥0.60、binomial p<0.001 的意外降解。"
            )
            exit_code = 0
        elif checks["boundary_step"]:
            status = "passed"
            verdict = "bounded_descriptor_only"
            note = (
                "sanity_pass: X50_BP_RULE PASS−FAIL Δ≥+0.08 且位置置换 p<0.001；"
                "固定 50/55nt 位置阶跃复现，但没有 escape-predicted 分层达到预登记 breakage 阈值。"
            )
            exit_code = 0
        else:
            status = "needs_data"
            verdict = "no_contact"
            note = (
                "sanity 与主阶跃矛盾或主阶跃未达阈值；按 pipeline/数据失败处理，不能作 no-contact 科学结论。"
            )
            exit_code = 3
        checks["nmd_verdict"] = status == "passed"

        result = {
            "n_kept": len(rows),
            "posctrl": {
                "pass_mean": r6(pass_mean),
                "fail_mean": r6(fail_mean),
                "delta": r6(pos_delta),
                "p_perm": r6(pos_p),
                "n_pass": len(pass_y),
                "n_fail": len(fail_y),
            },
            "boundary_step": {
                "triggering_mean": r6(均值(trig_y)),
                "escape_mean": r6(均值(esc_y)),
                "delta": r6(step_delta),
                "p_perm": r6(step_p),
                "n_triggering": len(trig_y),
                "n_escape": len(esc_y),
            },
            "step_bins": step_bins,
            "breakage_classes": breakage_tests,
            "tissue_flip": tissue,
            "actual_perm": PERMUTATIONS,
            "runtime_sec": r6(time.time() - t0),
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
    except Exception as e:
        checks["nmd_verdict"] = False
        out = {
            "status": "needs_data",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": checks,
            "verdict": "no_contact",
            "note": f"解析或运行失败: {type(e).__name__}: {e}",
            "result": {
                "n_kept": 0,
                "posctrl": {},
                "step_bins": {},
                "breakage_classes": [],
                "tissue_flip": {"n_multi_tissue": 0, "n_flipped": 0},
                "actual_perm": PERMUTATIONS,
                "runtime_sec": r6(time.time() - t0),
                "cannot_claim": cannot_claim,
            },
        }
        exit_code = 1
    print(json.dumps(out, ensure_ascii=False, separators=(",", ":"), sort_keys=True))
    return exit_code


if __name__ == "__main__":
    sys.exit(主程序())

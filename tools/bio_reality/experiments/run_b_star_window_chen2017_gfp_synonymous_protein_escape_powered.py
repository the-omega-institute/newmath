#!/usr/bin/env python3
"""Chen2017 GFP synonymous B_window protein|mRNA escape replication.

纯 stdlib 离线实验脚本。运行目录应为 repo 根目录:
  python3 /tmp/chen2017-exp/run_b_star_window_chen2017_gfp_synonymous_protein_escape_powered.py
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_window_chen2017_gfp_synonymous_protein_escape_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_chen2017_gfp_synonymous_protein_escape_powered"

DATA_REL = pathlib.Path("tools/bio_reality/data/chen2017_gfp_synonymous.json")
FOLD_COUNT = 5
RIDGE = 1e-6
EPS = 1e-12
TARGET_NULL_B = 200
SEED = "sha256:b_star_window_chen2017_gfp_synonymous_protein_escape_powered:deterministic"
B_COST_DIMS = 9

CANNOT_CLAIM = [
    "GFP reporter 区域非全基因/内源表达位点的全局基因组结论",
    "B_window 只覆盖 12-codon window",
    "protein 是 log2 FACS-bin 估计而非绝对蛋白拷贝数",
    "mRNA/protein 来自同一研究，非跨研究复现",
    "replicate-averaged target 会隐藏 replicate-level measurement variance",
    "只 2 个 region，leave-region-out 泛化有限",
]


def emit(status: str, checks: dict[str, bool], verdict: str, result: dict[str, Any], exit_code: int | None = None) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    if exit_code is None:
        exit_code = 0 if status == "passed" else (3 if status == "needs_data" else 1)
    sys.exit(exit_code)


def finite(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    c = mean(values)
    return sum((x - c) ** 2 for x in values) / len(values)


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def stable_random(material: str) -> random.Random:
    return random.Random(int.from_bytes(stable_digest(material)[:8], "big"))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[idx]


def dot(row: list[float], beta: list[float]) -> float:
    return sum(row[i] * beta[i] for i in range(len(beta)))


def cholesky_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    a = [list(row) for row in matrix]
    jitter = RIDGE
    for attempt in range(8):
        try:
            l = [[0.0 for _ in range(n)] for _ in range(n)]
            for i in range(n):
                for j in range(i + 1):
                    s = a[i][j] - sum(l[i][k] * l[j][k] for k in range(j))
                    if i == j:
                        if s <= EPS:
                            raise ValueError("not spd")
                        l[i][j] = math.sqrt(s)
                    else:
                        l[i][j] = s / l[j][j]
            y = [0.0 for _ in range(n)]
            for i in range(n):
                y[i] = (rhs[i] - sum(l[i][k] * y[k] for k in range(i))) / l[i][i]
            x = [0.0 for _ in range(n)]
            for i in range(n - 1, -1, -1):
                x[i] = (y[i] - sum(l[k][i] * x[k] for k in range(i + 1, n))) / l[i][i]
            return x
        except ValueError:
            for i in range(n):
                a[i][i] += jitter
            jitter *= 10.0
    return gaussian_solve(a, rhs)


def cholesky_factor(matrix: list[list[float]]) -> list[list[float]]:
    n = len(matrix)
    a = [list(row) for row in matrix]
    jitter = RIDGE
    for _attempt in range(8):
        try:
            l = [[0.0 for _ in range(n)] for _ in range(n)]
            for i in range(n):
                for j in range(i + 1):
                    s = a[i][j] - sum(l[i][k] * l[j][k] for k in range(j))
                    if i == j:
                        if s <= EPS:
                            raise ValueError("not spd")
                        l[i][j] = math.sqrt(s)
                    else:
                        l[i][j] = s / l[j][j]
            return l
        except ValueError:
            for i in range(n):
                a[i][i] += jitter
            jitter *= 10.0
    raise ValueError("failed cholesky_factor")


def cholesky_solve_factored(l: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    y = [0.0 for _ in range(n)]
    for i in range(n):
        y[i] = (rhs[i] - sum(l[i][k] * y[k] for k in range(i))) / l[i][i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        x[i] = (y[i] - sum(l[k][i] * x[k] for k in range(i + 1, n))) / l[i][i]
    return x


def gram_factor(x: list[list[float]]) -> list[list[float]]:
    width = len(x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in x:
        for i in range(width):
            xi = row[i]
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        if i != 0:
            xtx[i][i] += RIDGE
    return cholesky_factor(xtx)


def gaussian_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += RIDGE
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pv = aug[col][col] if abs(aug[col][col]) > EPS else EPS
        for j in range(col, n + 1):
            aug[col][j] /= pv
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def ridge_fit(x: list[list[float]], y: list[float]) -> list[float]:
    width = len(x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, yi in zip(x, y):
        for i in range(width):
            rhs[i] += row[i] * yi
            xi = row[i]
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        if i != 0:
            xtx[i][i] += RIDGE
    return cholesky_solve(xtx, rhs)


def ridge_fit_many(x: list[list[float]], ys: dict[str, list[float]]) -> dict[str, list[float]]:
    width = len(x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs_by_name = {name: [0.0 for _ in range(width)] for name in ys}
    for row_index, row in enumerate(x):
        for i in range(width):
            xi = row[i]
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
            for name, y in ys.items():
                rhs_by_name[name][i] += xi * y[row_index]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        if i != 0:
            xtx[i][i] += RIDGE
    factor = cholesky_factor(xtx)
    return {name: cholesky_solve_factored(factor, rhs) for name, rhs in rhs_by_name.items()}


def standardize_columns(
    matrix: list[list[float]],
    train: list[int],
    test: list[int],
) -> tuple[list[list[float]], list[list[float]], list[tuple[float, float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test], []
    width = len(matrix[0])
    stats: list[tuple[float, float]] = []
    for col in range(width):
        vals = [matrix[i][col] for i in train]
        c = mean(vals)
        sd = math.sqrt(variance(vals))
        if sd <= EPS:
            sd = 1.0
        stats.append((c, sd))
    tr = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in train]
    te = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in test]
    return tr, te, stats


def apply_standardize(row: list[float], stats: list[tuple[float, float]]) -> list[float]:
    return [(row[col] - stats[col][0]) / stats[col][1] for col in range(len(stats))]


def make_control_matrix(rows: list[dict[str, Any]]) -> list[list[float]]:
    out: list[list[float]] = []
    for row in rows:
        c = row["controls"]
        region = int(row["region"])
        out.append([
            1.0 if region == 2 else 0.0,
            float(c["CAI"]),
            float(c["tAI"]),
            float(c["MFE"]),
            float(c["GC3"]),
        ])
    return out


def make_folds(rows: list[dict[str, Any]]) -> list[list[int]]:
    by_region: dict[int, list[int]] = {1: [], 2: []}
    for i, row in enumerate(rows):
        by_region[int(row["region"])].append(i)
    folds = [[] for _ in range(FOLD_COUNT)]
    for region in sorted(by_region):
        perm = list(by_region[region])
        rng = stable_random(f"{SEED}|folds|region={region}")
        rng.shuffle(perm)
        for pos, idx in enumerate(perm):
            folds[pos % FOLD_COUNT].append(idx)
    return [sorted(fold) for fold in folds]


class FoldDesign:
    def __init__(
        self,
        train: list[int],
        test: list[int],
        x2_train: list[list[float]],
        x2_test: list[list[float]],
        b_stats: list[tuple[float, float]],
        x2_factor: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.x2_train = x2_train
        self.x2_test = x2_test
        self.b_stats = b_stats
        self.x2_factor = x2_factor


def build_fold_designs(c_matrix: list[list[float]], b_matrix: list[list[float]], folds: list[list[int]]) -> list[FoldDesign]:
    n = len(c_matrix)
    out: list[FoldDesign] = []
    for test in folds:
        test_set = set(test)
        train = [i for i in range(n) if i not in test_set]
        c_train, c_test, _ = standardize_columns(c_matrix, train, test)
        _b_train, _b_test, b_stats = standardize_columns(b_matrix, train, test)
        x2_train = [[1.0] + row for row in c_train]
        out.append(FoldDesign(
            train=train,
            test=test,
            x2_train=x2_train,
            x2_test=[[1.0] + row for row in c_test],
            b_stats=b_stats,
            x2_factor=gram_factor(x2_train),
        ))
    return out


def residualize_b_for_design(
    b_matrix: list[list[float]],
    design: FoldDesign,
) -> tuple[list[list[float]], list[list[float]]]:
    b_train_std = [[(b_matrix[i][col] - design.b_stats[col][0]) / design.b_stats[col][1] for col in range(B_COST_DIMS)] for i in design.train]
    b_test_std = [[(b_matrix[i][col] - design.b_stats[col][0]) / design.b_stats[col][1] for col in range(B_COST_DIMS)] for i in design.test]
    train_out = [[0.0 for _ in range(B_COST_DIMS)] for _ in design.train]
    test_out = [[0.0 for _ in range(B_COST_DIMS)] for _ in design.test]
    for col in range(B_COST_DIMS):
        rhs = [0.0 for _ in range(len(design.x2_train[0]))]
        for row, b_row in zip(design.x2_train, b_train_std):
            y = b_row[col]
            for i, x in enumerate(row):
                rhs[i] += x * y
        beta = cholesky_solve_factored(design.x2_factor, rhs)
        for i, row in enumerate(design.x2_train):
            train_out[i][col] = b_train_std[i][col] - dot(row, beta)
        for i, row in enumerate(design.x2_test):
            test_out[i][col] = b_test_std[i][col] - dot(row, beta)
    return train_out, test_out


def fit_predict_target(
    target: list[float],
    c_matrix: list[list[float]],
    b_matrix: list[list[float]] | None,
    folds: list[list[int]],
) -> tuple[list[float], list[float], list[float]]:
    n = len(target)
    preds = [0.0 for _ in range(n)]
    beta_b_sum = [0.0 for _ in range(B_COST_DIMS)]
    beta_b_count = 0
    for test in folds:
        test_set = set(test)
        train = [i for i in range(n) if i not in test_set]
        c_train, c_test, _ = standardize_columns(c_matrix, train, test)
        x_train = [[1.0] + row for row in c_train]
        x_test = [[1.0] + row for row in c_test]
        if b_matrix is not None:
            b_res_train, b_res_test = residualize_b_train_apply(b_matrix, c_matrix, train, test)
            x_train = [x_train[i] + b_res_train[i] for i in range(len(train))]
            x_test = [x_test[i] + b_res_test[i] for i in range(len(test))]
        beta = ridge_fit(x_train, [target[i] for i in train])
        for local, idx in enumerate(test):
            preds[idx] = dot(x_test[local], beta)
        if b_matrix is not None:
            for j, value in enumerate(beta[-B_COST_DIMS:]):
                beta_b_sum[j] += value
            beta_b_count += 1
    beta_b_mean = [v / beta_b_count for v in beta_b_sum] if beta_b_count else [0.0 for _ in range(B_COST_DIMS)]
    return preds, beta_b_mean, []


def fit_predict_target_cached(
    target: list[float],
    b_matrix: list[list[float]] | None,
    designs: list[FoldDesign],
) -> tuple[list[float], list[float]]:
    n = len(target)
    preds = [0.0 for _ in range(n)]
    beta_b_sum = [0.0 for _ in range(B_COST_DIMS)]
    beta_b_count = 0
    for design in designs:
        x_train = design.x2_train
        x_test = design.x2_test
        if b_matrix is not None:
            b_train, b_test = residualize_b_for_design(b_matrix, design)
            x_train = [design.x2_train[i] + b_train[i] for i in range(len(design.train))]
            x_test = [design.x2_test[i] + b_test[i] for i in range(len(design.test))]
        beta = ridge_fit(x_train, [target[i] for i in design.train])
        for local, idx in enumerate(design.test):
            preds[idx] = dot(x_test[local], beta)
        if b_matrix is not None:
            for j, value in enumerate(beta[-B_COST_DIMS:]):
                beta_b_sum[j] += value
            beta_b_count += 1
    beta_b = [v / beta_b_count for v in beta_b_sum] if beta_b_count else [0.0 for _ in range(B_COST_DIMS)]
    return preds, beta_b


def residualize_b_train_apply(
    b_matrix: list[list[float]],
    c_matrix: list[list[float]],
    train: list[int],
    test: list[int],
) -> tuple[list[list[float]], list[list[float]]]:
    c_train, c_test, _ = standardize_columns(c_matrix, train, test)
    b_train_std, b_test_std, _ = standardize_columns(b_matrix, train, test)
    x_train = [[1.0] + row for row in c_train]
    x_test = [[1.0] + row for row in c_test]
    train_out = [[0.0 for _ in range(B_COST_DIMS)] for _ in train]
    test_out = [[0.0 for _ in range(B_COST_DIMS)] for _ in test]
    for col in range(B_COST_DIMS):
        y = [row[col] for row in b_train_std]
        beta = ridge_fit(x_train, y)
        for i, row in enumerate(x_train):
            train_out[i][col] = b_train_std[i][col] - dot(row, beta)
        for i, row in enumerate(x_test):
            test_out[i][col] = b_test_std[i][col] - dot(row, beta)
    return train_out, test_out


def oof_residual_y_on_x(
    y: list[float],
    x: list[float],
    folds: list[list[int]],
) -> tuple[list[float], float]:
    n = len(y)
    preds = [0.0 for _ in range(n)]
    beta_slopes = []
    for test in folds:
        test_set = set(test)
        train = [i for i in range(n) if i not in test_set]
        vals = [x[i] for i in train]
        c = mean(vals)
        sd = math.sqrt(variance(vals))
        if sd <= EPS:
            sd = 1.0
        x_train = [[1.0, (x[i] - c) / sd] for i in train]
        beta = ridge_fit(x_train, [y[i] for i in train])
        beta_slopes.append(beta[1])
        for idx in test:
            preds[idx] = beta[0] + beta[1] * ((x[idx] - c) / sd)
    return [y[i] - preds[i] for i in range(n)], mean(beta_slopes)


def sse(y: list[float], pred: list[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(y, pred))


def tss(y: list[float]) -> float:
    c = mean(y)
    value = sum((v - c) ** 2 for v in y)
    return value if value > EPS else EPS


def delta_dl_bits(base_sse: float, full_sse: float, n: int) -> float:
    # BIC-style gain with 9 extra B coefficients charged, in bits.
    safe_base = max(base_sse, EPS)
    safe_full = max(full_sse, EPS)
    return (0.5 * n * math.log(safe_base / safe_full) - 0.5 * B_COST_DIMS * math.log(n)) / math.log(2.0)


def score_target(
    target: list[float],
    c_matrix: list[list[float]],
    b_matrix: list[list[float]],
    folds: list[list[int]],
) -> dict[str, Any]:
    pred_l2, _unused, _ = fit_predict_target(target, c_matrix, None, folds)
    pred_l3, beta_b, _ = fit_predict_target(target, c_matrix, b_matrix, folds)
    s2 = sse(target, pred_l2)
    s3 = sse(target, pred_l3)
    total = tss(target)
    return {
        "R2_L2": 1.0 - s2 / total,
        "R2_L3": 1.0 - s3 / total,
        "delta_r2": (s2 - s3) / total,
        "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
        "sse_L2": s2,
        "sse_L3": s3,
        "beta_b": beta_b,
    }


def score_target_cached(
    target: list[float],
    b_matrix: list[list[float]],
    designs: list[FoldDesign],
    pred_l2: list[float] | None = None,
) -> dict[str, Any]:
    if pred_l2 is None:
        pred_l2, _ = fit_predict_target_cached(target, None, designs)
    pred_l3, beta_b = fit_predict_target_cached(target, b_matrix, designs)
    s2 = sse(target, pred_l2)
    s3 = sse(target, pred_l3)
    total = tss(target)
    return {
        "R2_L2": 1.0 - s2 / total,
        "R2_L3": 1.0 - s3 / total,
        "delta_r2": (s2 - s3) / total,
        "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
        "sse_L2": s2,
        "sse_L3": s3,
        "beta_b": beta_b,
    }


def score_targets_for_b_cached(
    targets: dict[str, list[float]],
    b_matrix: list[list[float]],
    designs: list[FoldDesign],
    l2_preds: dict[str, list[float]],
) -> dict[str, dict[str, Any]]:
    preds = {name: [0.0 for _ in target] for name, target in targets.items()}
    beta_sums = {name: [0.0 for _ in range(B_COST_DIMS)] for name in targets}
    beta_counts = {name: 0 for name in targets}
    for design in designs:
        b_train, b_test = residualize_b_for_design(b_matrix, design)
        x3_train = [design.x2_train[i] + b_train[i] for i in range(len(design.train))]
        x3_test = [design.x2_test[i] + b_test[i] for i in range(len(design.test))]
        y_train_by_name = {name: [target[i] for i in design.train] for name, target in targets.items()}
        betas = ridge_fit_many(x3_train, y_train_by_name)
        for name, beta in betas.items():
            for local, idx in enumerate(design.test):
                preds[name][idx] = dot(x3_test[local], beta)
            for j, value in enumerate(beta[-B_COST_DIMS:]):
                beta_sums[name][j] += value
            beta_counts[name] += 1
    out: dict[str, dict[str, Any]] = {}
    for name, target in targets.items():
        s2 = sse(target, l2_preds[name])
        s3 = sse(target, preds[name])
        total = tss(target)
        out[name] = {
            "R2_L2": 1.0 - s2 / total,
            "R2_L3": 1.0 - s3 / total,
            "delta_r2": (s2 - s3) / total,
            "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
            "sse_L2": s2,
            "sse_L3": s3,
            "beta_b": [v / beta_counts[name] for v in beta_sums[name]],
        }
    return out


def compact_metric(metric: dict[str, Any]) -> dict[str, Any]:
    return {
        "R2_L2": metric["R2_L2"],
        "R2_L3": metric["R2_L3"],
        "delta_r2": metric["delta_r2"],
        "delta_dl_bits": metric["delta_dl_bits"],
        "p_within": metric.get("p_within"),
        "p_matched": metric.get("p_matched"),
        "null95": metric.get("null95"),
    }


def shuffle_within_region(b_matrix: list[list[float]], rows: list[dict[str, Any]], trial: int) -> list[list[float]]:
    out = [list(row) for row in b_matrix]
    for region in (1, 2):
        idxs = [i for i, row in enumerate(rows) if int(row["region"]) == region]
        src = list(idxs)
        rng = stable_random(f"{SEED}|within|trial={trial}|region={region}")
        rng.shuffle(src)
        for dst, source in zip(idxs, src):
            out[dst] = list(b_matrix[source])
    return out


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    if not values:
        return []
    ordered = sorted(values)
    cuts = []
    for b in range(1, bins):
        idx = int(round((len(ordered) - 1) * b / bins))
        cuts.append(ordered[idx])
    return cuts


def bin_index(value: float, cuts: list[float]) -> int:
    idx = 0
    while idx < len(cuts) and value > cuts[idx]:
        idx += 1
    return idx


def matched_bins(rows: list[dict[str, Any]]) -> list[tuple[int, int, int, int, int]]:
    axes = ["CAI", "tAI", "GC3", "MFE"]
    cuts_by_region_axis: dict[tuple[int, str], list[float]] = {}
    for region in (1, 2):
        subset = [row for row in rows if int(row["region"]) == region]
        for axis in axes:
            vals = [float(row["controls"][axis]) for row in subset]
            cuts_by_region_axis[(region, axis)] = quantile_cuts(vals, 3)
    keys = []
    for row in rows:
        region = int(row["region"])
        c = row["controls"]
        keys.append((
            region,
            bin_index(float(c["CAI"]), cuts_by_region_axis[(region, "CAI")]),
            bin_index(float(c["tAI"]), cuts_by_region_axis[(region, "tAI")]),
            bin_index(float(c["GC3"]), cuts_by_region_axis[(region, "GC3")]),
            bin_index(float(c["MFE"]), cuts_by_region_axis[(region, "MFE")]),
        ))
    return keys


def shuffle_matched(b_matrix: list[list[float]], keys: list[tuple[int, int, int, int, int]], trial: int) -> list[list[float]]:
    out = [list(row) for row in b_matrix]
    groups: dict[tuple[int, int, int, int, int], list[int]] = {}
    for i, key in enumerate(keys):
        groups.setdefault(key, []).append(i)
    for key in sorted(groups):
        idxs = groups[key]
        if len(idxs) < 2:
            continue
        src = list(idxs)
        rng = stable_random(f"{SEED}|matched|trial={trial}|key={key}")
        rng.shuffle(src)
        for dst, source in zip(idxs, src):
            out[dst] = list(b_matrix[source])
    return out


def null_summary(
    target: list[float],
    b_matrix: list[list[float]],
    designs: list[FoldDesign],
    rows: list[dict[str, Any]],
    kind: str,
    b: int,
    pred_l2: list[float],
) -> dict[str, Any]:
    values: list[float] = []
    keys = matched_bins(rows) if kind == "matched" else []
    for trial in range(b):
        shuffled = shuffle_within_region(b_matrix, rows, trial) if kind == "within" else shuffle_matched(b_matrix, keys, trial)
        metric = score_target_cached(target, shuffled, designs, pred_l2)
        values.append(float(metric["delta_dl_bits"]))
    return {
        "values": values,
        "null95": percentile_nearest_rank(values, 0.95),
    }


def null_summaries_all_targets(
    targets: dict[str, list[float]],
    b_matrix: list[list[float]],
    designs: list[FoldDesign],
    rows: list[dict[str, Any]],
    kind: str,
    b: int,
    l2_preds: dict[str, list[float]],
) -> dict[str, dict[str, Any]]:
    values: dict[str, list[float]] = {name: [] for name in targets}
    keys = matched_bins(rows) if kind == "matched" else []
    for trial in range(b):
        shuffled = shuffle_within_region(b_matrix, rows, trial) if kind == "within" else shuffle_matched(b_matrix, keys, trial)
        metrics = score_targets_for_b_cached(targets, shuffled, designs, l2_preds)
        for name, metric in metrics.items():
            values[name].append(float(metric["delta_dl_bits"]))
    return {
        name: {
            "values": vals,
            "null95": percentile_nearest_rank(vals, 0.95),
        }
        for name, vals in values.items()
    }


def p_upper(observed: float, null_values: list[float]) -> float:
    return (1.0 + sum(1 for value in null_values if value >= observed)) / (len(null_values) + 1.0)


def leave_region_out(
    target: list[float],
    c_matrix: list[list[float]],
    b_matrix: list[list[float]],
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    out: dict[str, Any] = {}
    n = len(target)
    for train_region, test_region in ((1, 2), (2, 1)):
        train = [i for i, row in enumerate(rows) if int(row["region"]) == train_region]
        test = [i for i, row in enumerate(rows) if int(row["region"]) == test_region]
        c_train, c_test, _ = standardize_columns(c_matrix, train, test)
        x2_train = [[1.0] + row for row in c_train]
        x2_test = [[1.0] + row for row in c_test]
        beta2 = ridge_fit(x2_train, [target[i] for i in train])
        p2 = [dot(row, beta2) for row in x2_test]
        b_train, b_test = residualize_b_train_apply(b_matrix, c_matrix, train, test)
        x3_train = [x2_train[i] + b_train[i] for i in range(len(train))]
        x3_test = [x2_test[i] + b_test[i] for i in range(len(test))]
        beta3 = ridge_fit(x3_train, [target[i] for i in train])
        p3 = [dot(row, beta3) for row in x3_test]
        y_test = [target[i] for i in test]
        s2 = sse(y_test, p2)
        s3 = sse(y_test, p3)
        total = tss(y_test)
        key = f"train_region{train_region}_predict_region{test_region}"
        out[key] = {
            "n_train": len(train),
            "n_test": len(test),
            "R2_L2": 1.0 - s2 / total,
            "R2_L3": 1.0 - s3 / total,
            "delta_r2": (s2 - s3) / total,
            "delta_dl_bits": delta_dl_bits(s2, s3, len(test)),
        }
    if n <= 0:
        raise ValueError("empty target")
    return out


def sign_stable(beta: list[float], threshold: float = 1e-10) -> bool:
    nonzero = [x for x in beta if abs(x) > threshold]
    if not nonzero:
        return False
    pos = sum(1 for x in nonzero if x > 0)
    neg = sum(1 for x in nonzero if x < 0)
    return max(pos, neg) >= 6


def beta_signs(beta: list[float], q_names: list[str]) -> dict[str, int]:
    out = {}
    for name, value in zip(q_names, beta):
        out[name] = 1 if value > 1e-10 else (-1 if value < -1e-10 else 0)
    return out


def validate_dataset(data: Any) -> tuple[list[dict[str, Any]], list[str]]:
    if not isinstance(data, dict) or not isinstance(data.get("rows"), list):
        raise ValueError("dataset malformed")
    q_names = data.get("q_names")
    if not isinstance(q_names, list) or len(q_names) != B_COST_DIMS:
        raise ValueError("q_names malformed")
    rows: list[dict[str, Any]] = []
    for item in data["rows"]:
        if not isinstance(item, dict):
            continue
        b = item.get("b_window")
        c = item.get("controls")
        t = item.get("targets")
        seq = item.get("sequence")
        if (
            isinstance(b, list) and len(b) == B_COST_DIMS
            and isinstance(c, dict) and isinstance(t, dict)
            and isinstance(seq, str) and len(seq) == 36
            and all(finite(x) for x in b)
            and all(finite(c.get(k)) for k in ("CAI", "tAI", "MFE", "GC3"))
            and finite(t.get("mrna")) and finite(t.get("protein"))
            and int(item.get("region")) in (1, 2)
        ):
            rows.append(item)
    return rows, [str(x) for x in q_names]


def decide_verdict(metrics: dict[str, dict[str, Any]]) -> str:
    mrna = metrics["mrna"]
    resid = metrics["protein_resid"]
    protein = metrics["protein"]
    resid_pass = (
        resid["delta_dl_bits"] > 0.0
        and resid["delta_dl_bits"] > resid["null95"]["within"]
        and resid["delta_dl_bits"] > resid["null95"]["matched"]
        and sign_stable(resid["beta_b"])
    )
    mrna_pass = (
        mrna["delta_dl_bits"] > 0.0
        and mrna["delta_dl_bits"] > mrna["null95"]["within"]
        and mrna["delta_dl_bits"] > mrna["null95"]["matched"]
    )
    matched_catches = (
        protein["delta_dl_bits"] <= protein["null95"]["matched"]
        or mrna["delta_dl_bits"] <= mrna["null95"]["matched"]
        or resid["delta_dl_bits"] <= resid["null95"]["matched"]
    )
    if resid_pass:
        return "post_mRNA_protein_escape_candidate"
    if mrna_pass and not resid_pass:
        return "causal_execution_only"
    if matched_catches:
        return "composition_artifact"
    if resid["delta_dl_bits"] <= 0.0 or not sign_stable(resid["beta_b"]):
        return "public_perturbation_B_window_null"
    return "public_perturbation_B_window_null"


def main() -> None:
    started = time.time()
    checks = {
        "data_parsed": False,
        "b_window_computed": False,
        "controls_built": False,
        "ladder_L2_L3_heldout": False,
        "leave_region_out": False,
        "nulls_run": False,
        "protein_escape_verdict": False,
    }
    try:
        repo = pathlib.Path.cwd()
        data_path = repo / DATA_REL
        data = json.loads(data_path.read_text(encoding="utf-8"))
        rows, q_names = validate_dataset(data)
        checks["data_parsed"] = len(rows) > 0
        if len(rows) < 200:
            result = {"n_variants": len(rows), "cannot_claim": CANNOT_CLAIM, "runtime_sec": time.time() - started}
            emit("needs_data", checks, "needs_data", result)

        c_matrix = make_control_matrix(rows)
        b_matrix = [[float(x) for x in row["b_window"]] for row in rows]
        mrna = [float(row["targets"]["mrna"]) for row in rows]
        protein = [float(row["targets"]["protein"]) for row in rows]
        folds = make_folds(rows)
        designs = build_fold_designs(c_matrix, b_matrix, folds)
        checks["b_window_computed"] = all(len(row) == B_COST_DIMS for row in b_matrix)
        checks["controls_built"] = all(len(row) == 5 for row in c_matrix)

        protein_resid, protein_on_mrna_slope = oof_residual_y_on_x(protein, mrna, folds)
        targets = {
            "mrna": mrna,
            "protein": protein,
            "protein_resid": protein_resid,
        }
        raw_metrics: dict[str, dict[str, Any]] = {}
        l2_preds: dict[str, list[float]] = {}
        for name, target in targets.items():
            pred_l2, _ = fit_predict_target_cached(target, None, designs)
            l2_preds[name] = pred_l2
            raw_metrics[name] = score_target_cached(target, b_matrix, designs, pred_l2)
        checks["ladder_L2_L3_heldout"] = True

        actual_b = TARGET_NULL_B
        within_all = null_summaries_all_targets(targets, b_matrix, designs, rows, "within", actual_b, l2_preds)
        matched_all = null_summaries_all_targets(targets, b_matrix, designs, rows, "matched", actual_b, l2_preds)
        for name, target in targets.items():
            within = within_all[name]
            matched = matched_all[name]
            observed = raw_metrics[name]["delta_dl_bits"]
            raw_metrics[name]["p_within"] = p_upper(observed, within["values"])
            raw_metrics[name]["p_matched"] = p_upper(observed, matched["values"])
            raw_metrics[name]["null95"] = {
                "within": within["null95"],
                "matched": matched["null95"],
            }
        checks["nulls_run"] = True

        lro = {
            name: leave_region_out(target, c_matrix, b_matrix, rows)
            for name, target in targets.items()
        }
        checks["leave_region_out"] = True

        verdict = decide_verdict(raw_metrics)
        checks["protein_escape_verdict"] = True
        status = "passed"
        per_target = {name: compact_metric(metric) for name, metric in raw_metrics.items()}
        n_region1 = sum(1 for row in rows if int(row["region"]) == 1)
        n_region2 = sum(1 for row in rows if int(row["region"]) == 2)
        result = {
            "n_variants": len(rows),
            "n_region1": n_region1,
            "n_region2": n_region2,
            "actual_B": actual_b,
            "runtime_sec": time.time() - started,
            "per_target": per_target,
            "leave_region_out": lro,
            "beta_b_sign": {
                name: beta_signs(raw_metrics[name]["beta_b"], q_names)
                for name in ("mrna", "protein", "protein_resid")
            },
            "protein_on_oof_mrna_slope": protein_on_mrna_slope,
            "cannot_claim": CANNOT_CLAIM,
        }
        emit(status, checks, verdict, result)
    except Exception as exc:
        result = {"error": repr(exc), "runtime_sec": time.time() - started, "cannot_claim": CANNOT_CLAIM}
        emit("failed", checks, "failed_exception", result, exit_code=1)


if __name__ == "__main__":
    main()

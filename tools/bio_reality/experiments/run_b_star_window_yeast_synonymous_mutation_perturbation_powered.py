#!/usr/bin/env python3
"""Shen 2022 yeast endogenous synonymous perturbation test for B*_Q6 window axes.

纯 stdlib 离线脚本。cwd 应为 repo 根目录；数据读自
tools/bio_reality/data/shen2022_yeast_synonymous_perturbation.json。
"""

from __future__ import annotations

import hashlib
import json
import math
import multiprocessing as mp
import os
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_window_yeast_synonymous_mutation_perturbation_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_yeast_synonymous_mutation_perturbation_powered"
DATA_REL = pathlib.Path("tools/bio_reality/data/shen2022_yeast_synonymous_perturbation.json")
RIDGE = 1e-6
EPS = 1e-12
NULL_B = 200
SEED = "sha256:b_star_window_yeast_synonymous_mutation_perturbation_powered:deterministic"
WORKER_STATE: dict[str, Any] = {}


class FoldCache:
    def __init__(
        self,
        train: list[int],
        test: list[int],
        gene: str,
        c_train: list[list[float]],
        c_test: list[list[float]],
        chol: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.gene = gene
        self.c_train = c_train
        self.c_test = c_test
        self.chol = chol
        width = len(c_train[0])
        self.c_train_sums = [sum(row[j] for row in c_train) for j in range(width)]


def emit(status: str, checks: dict[str, bool], verdict: str, result: dict[str, Any], cannot_claim: list[str]) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
        "cannot_claim": cannot_claim,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    m = mean(values)
    return sum((x - m) ** 2 for x in values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[idx]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def stable_random(material: str) -> random.Random:
    return random.Random(int.from_bytes(stable_digest(material)[:8], "big"))


def deterministic_shuffle(items: list[Any], material: str) -> list[Any]:
    out = list(items)
    for i in range(len(out) - 1, 0, -1):
        j = int.from_bytes(stable_digest(f"{material}|{i}")[:8], "big") % (i + 1)
        out[i], out[j] = out[j], out[i]
    return out


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += RIDGE
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pv = aug[col][col]
        if abs(pv) <= EPS:
            pv = EPS
            aug[col][col] = pv
        inv = 1.0 / pv
        for j in range(col, n + 1):
            aug[col][j] *= inv
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def ridge_fit(x: list[list[float]], y: list[float]) -> list[float]:
    width = len(x[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, yy in zip(x, y):
        for i in range(width):
            rhs[i] += row[i] * yy
            xi = row[i]
            for j in range(i, width):
                xtx[i][j] += xi * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        if i != 0:
            xtx[i][i] += RIDGE
    return solve_linear_system(xtx, rhs)


def ridge_xtx_cholesky(x: list[list[float]]) -> list[list[float]]:
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
    chol = [[0.0 for _ in range(width)] for _ in range(width)]
    for i in range(width):
        for j in range(i + 1):
            value = xtx[i][j]
            for k in range(j):
                value -= chol[i][k] * chol[j][k]
            if i == j:
                if value <= EPS:
                    value = EPS
                chol[i][j] = math.sqrt(value)
            else:
                chol[i][j] = value / chol[j][j]
    return chol


def cholesky_solve(chol: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    y = [0.0 for _ in range(n)]
    for i in range(n):
        value = rhs[i]
        row = chol[i]
        for k in range(i):
            value -= row[k] * y[k]
        y[i] = value / row[i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        value = y[i]
        for k in range(i + 1, n):
            value -= chol[k][i] * x[k]
        x[i] = value / chol[i][i]
    return x


def control_beta_vector(fold: FoldCache, values: list[float]) -> list[float]:
    width = len(fold.c_train[0])
    rhs = [0.0 for _ in range(width)]
    for local, idx in enumerate(fold.train):
        row = fold.c_train[local]
        value = values[idx]
        for j in range(width):
            rhs[j] += row[j] * value
    return cholesky_solve(fold.chol, rhs)


def control_beta_matrix(fold: FoldCache, matrix: list[list[float]]) -> list[list[float]]:
    width = len(fold.c_train[0])
    q = len(matrix[0])
    rhs = [[0.0 for _ in range(q)] for _ in range(width)]
    for local, idx in enumerate(fold.train):
        row = fold.c_train[local]
        vals = matrix[idx]
        for j in range(width):
            cj = row[j]
            for col in range(q):
                rhs[j][col] += cj * vals[col]
    beta = [[0.0 for _ in range(q)] for _ in range(width)]
    for col in range(q):
        sol = cholesky_solve(fold.chol, [rhs[row][col] for row in range(width)])
        for row in range(width):
            beta[row][col] = sol[row]
    return beta


def dot_matrix_row(row: list[float], beta: list[list[float]], col: int) -> float:
    return sum(row[i] * beta[i][col] for i in range(len(row)))


def dot(row: list[float], beta: list[float]) -> float:
    return sum(row[i] * beta[i] for i in range(len(beta)))


def standardize_train_apply(matrix: list[list[float]], train: list[int], test: list[int]) -> tuple[list[list[float]], list[list[float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test]
    width = len(matrix[0])
    centers = []
    scales = []
    for col in range(width):
        vals = [matrix[i][col] for i in train]
        m = mean(vals)
        sd = math.sqrt(variance(vals))
        centers.append(m)
        scales.append(sd if sd > EPS else 1.0)
    tr = [[(matrix[i][col] - centers[col]) / scales[col] for col in range(width)] for i in train]
    te = [[(matrix[i][col] - centers[col]) / scales[col] for col in range(width)] for i in test]
    return tr, te


def one_hot(values: list[str]) -> list[list[float]]:
    cats = sorted(set(values))
    if len(cats) <= 1:
        return [[] for _ in values]
    cats = cats[1:]
    return [[1.0 if v == cat else 0.0 for cat in cats] for v in values]


def build_controls(rows: list[dict[str, Any]]) -> list[list[float]]:
    genes = one_hot([r["gene"] for r in rows])
    families = one_hot([r["codon_family"] for r in rows])
    wt_codons = one_hot([r["wt_codon"] for r in rows])
    numeric = [[
        float(r["codon_pos_norm"]),
        float(r["delta_cai"]),
        float(r["delta_tai"]),
        float(r["delta_csc"]),
        float(r["delta_gc3"]),
    ] for r in rows]
    out = []
    for i in range(len(rows)):
        out.append([1.0] + numeric[i] + genes[i] + families[i] + wt_codons[i])
    return out


def folds_by_gene(rows: list[dict[str, Any]]) -> list[tuple[list[int], list[int], str]]:
    genes = sorted(set(r["gene"] for r in rows))
    folds = []
    for gene in genes:
        test = [i for i, r in enumerate(rows) if r["gene"] == gene]
        test_set = set(test)
        train = [i for i in range(len(rows)) if i not in test_set]
        folds.append((train, test, gene))
    return folds


def make_fold_cache(controls: list[list[float]], folds: list[tuple[list[int], list[int], str]]) -> list[FoldCache]:
    raw_numeric = [row[1:] for row in controls]
    caches = []
    for train, test, gene in folds:
        c_train, c_test = standardize_train_apply(raw_numeric, train, test)
        x_train = [[1.0] + row for row in c_train]
        x_test = [[1.0] + row for row in c_test]
        caches.append(FoldCache(train, test, gene, x_train, x_test, ridge_xtx_cholesky(x_train)))
    return caches


def control_predictions(target: list[float], fold_cache: list[FoldCache]) -> tuple[list[float], list[list[float]]]:
    pred = [0.0 for _ in target]
    betas = []
    for fold in fold_cache:
        beta = control_beta_vector(fold, target)
        betas.append(beta)
        for local, idx in enumerate(fold.test):
            pred[idx] = dot(fold.c_test[local], beta)
    return pred, betas


def residualize_matrix_for_fold(matrix: list[list[float]], fold: FoldCache) -> tuple[list[list[float]], list[list[float]]]:
    q = len(matrix[0])
    beta = control_beta_matrix(fold, matrix)
    train_res = []
    for local, idx in enumerate(fold.train):
        row = fold.c_train[local]
        train_res.append([matrix[idx][col] - dot_matrix_row(row, beta, col) for col in range(q)])
    test_res = []
    for local, idx in enumerate(fold.test):
        row = fold.c_test[local]
        test_res.append([matrix[idx][col] - dot_matrix_row(row, beta, col) for col in range(q)])
    return train_res, test_res


def standardize_pair(train_matrix: list[list[float]], test_matrix: list[list[float]]) -> tuple[list[list[float]], list[list[float]]]:
    if not train_matrix or not train_matrix[0]:
        return train_matrix, test_matrix
    width = len(train_matrix[0])
    centers = []
    scales = []
    for col in range(width):
        vals = [row[col] for row in train_matrix]
        m = mean(vals)
        sd = math.sqrt(variance(vals))
        centers.append(m)
        scales.append(sd if sd > EPS else 1.0)
    train = [[(row[col] - centers[col]) / scales[col] for col in range(width)] for row in train_matrix]
    test = [[(row[col] - centers[col]) / scales[col] for col in range(width)] for row in test_matrix]
    return train, test


def evaluate_b_for_targets(
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    base_betas: dict[str, list[list[float]]],
) -> dict[str, dict[str, Any]]:
    full_preds = {name: list(pred) for name, pred in base_preds.items()}
    fold_betas = {name: [] for name in targets}
    for fold_index, fold in enumerate(fold_cache):
        b_train_res, b_test_res = residualize_matrix_for_fold(b, fold)
        b_train_std, b_test_std = standardize_pair(b_train_res, b_test_res)
        for name, target in targets.items():
            beta_c = base_betas[name][fold_index]
            y_res = [target[idx] - dot(fold.c_train[local], beta_c) for local, idx in enumerate(fold.train)]
            gamma = ridge_fit(b_train_std, y_res)
            fold_betas[name].append(gamma)
            for local, idx in enumerate(fold.test):
                full_preds[name][idx] = base_preds[name][idx] + dot(b_test_std[local], gamma)
    out: dict[str, dict[str, Any]] = {}
    for name, target in targets.items():
        s2 = sse(target, base_preds[name])
        s3 = sse(target, full_preds[name])
        total = tss(target)
        out[name] = {
            "R2_L2": 1.0 - s2 / total,
            "R2_L3": 1.0 - s3 / total,
            "delta_r2": (s2 - s3) / total,
            "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
            "sse_L2": s2,
            "sse_L3": s3,
            "beta_b_by_fold": fold_betas[name],
        }
    return out


def sparse_rows(matrix: list[list[float]]) -> list[list[tuple[int, float]]]:
    return [[(j, value) for j, value in enumerate(row) if abs(value) > EPS] for row in matrix]


def solve_small(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    return solve_linear_system(matrix, rhs)


def evaluate_b_for_targets_fast(
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    base_betas: dict[str, list[list[float]]],
    target_cache: dict[str, list[dict[str, Any]]],
) -> dict[str, dict[str, Any]]:
    q = len(b[0])
    sparse = sparse_rows(b)
    full_preds = {name: list(pred) for name, pred in base_preds.items()}
    fold_betas = {name: [] for name in targets}
    for fold_index, fold in enumerate(fold_cache):
        p = len(fold.c_train[0])
        n_train = len(fold.train)
        s = [[0.0 for _ in range(q)] for _ in range(p)]
        bt_b = [[0.0 for _ in range(q)] for _ in range(q)]
        b_sum = [0.0 for _ in range(q)]
        bty = {name: [0.0 for _ in range(q)] for name in targets}
        for local, idx in enumerate(fold.train):
            brow = sparse[idx]
            if not brow:
                continue
            row_c = fold.c_train[local]
            for col, value in brow:
                b_sum[col] += value
                for jj in range(p):
                    s[jj][col] += row_c[jj] * value
            for a, va in brow:
                row_bt = bt_b[a]
                for c, vc in brow:
                    row_bt[c] += va * vc
            for name in targets:
                yres = target_cache[name][fold_index]["yres"][local]
                for col, value in brow:
                    bty[name][col] += value * yres
        beta_s = [[0.0 for _ in range(q)] for _ in range(p)]
        for col in range(q):
            sol = cholesky_solve(fold.chol, [s[row][col] for row in range(p)])
            for row in range(p):
                beta_s[row][col] = sol[row]
        rb_sum = [b_sum[col] - sum(fold.c_train_sums[row] * beta_s[row][col] for row in range(p)) for col in range(q)]
        g = [[0.0 for _ in range(q)] for _ in range(q)]
        for a in range(q):
            for c in range(q):
                correction = sum(s[row][a] * beta_s[row][c] for row in range(p))
                g[a][c] = bt_b[a][c] - correction
        means = [rb_sum[col] / max(1, n_train) for col in range(q)]
        sds = []
        for col in range(q):
            centered_ss = g[col][col] - 2.0 * means[col] * rb_sum[col] + n_train * means[col] * means[col]
            sds.append(math.sqrt(centered_ss / max(1, n_train)) if centered_ss > EPS else 1.0)
        gz = [[0.0 for _ in range(q)] for _ in range(q)]
        for a in range(q):
            for c in range(q):
                centered = g[a][c] - means[c] * rb_sum[a] - means[a] * rb_sum[c] + n_train * means[a] * means[c]
                gz[a][c] = centered / (sds[a] * sds[c])
            gz[a][a] += RIDGE
        test_bres = []
        for local, idx in enumerate(fold.test):
            raw = [0.0 for _ in range(q)]
            for col, value in sparse[idx]:
                raw[col] = value
            row_c = fold.c_test[local]
            cres = [raw[col] - sum(row_c[jj] * beta_s[jj][col] for jj in range(p)) for col in range(q)]
            test_bres.append([(cres[col] - means[col]) / sds[col] for col in range(q)])
        for name in targets:
            h = [0.0 for _ in range(q)]
            yres_sum = target_cache[name][fold_index]["yres_sum"]
            ctyres_solve = target_cache[name][fold_index]["ctyres_solve"]
            for col in range(q):
                raw_h = bty[name][col] - sum(s[row][col] * ctyres_solve[row] for row in range(p))
                h[col] = (raw_h - means[col] * yres_sum) / sds[col]
            gamma = solve_small(gz, h)
            fold_betas[name].append(gamma)
            for local, idx in enumerate(fold.test):
                full_preds[name][idx] = base_preds[name][idx] + dot(test_bres[local], gamma)
    out: dict[str, dict[str, Any]] = {}
    for name, target in targets.items():
        s2 = sse(target, base_preds[name])
        s3 = sse(target, full_preds[name])
        total = tss(target)
        out[name] = {
            "R2_L2": 1.0 - s2 / total,
            "R2_L3": 1.0 - s3 / total,
            "delta_r2": (s2 - s3) / total,
            "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
            "sse_L2": s2,
            "sse_L3": s3,
            "beta_b_by_fold": fold_betas[name],
        }
    return out


def build_target_cache(
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_betas: dict[str, list[list[float]]],
) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = {name: [] for name in targets}
    for fold_index, fold in enumerate(fold_cache):
        p = len(fold.c_train[0])
        for name, target in targets.items():
            beta_c = base_betas[name][fold_index]
            yres = []
            cty = [0.0 for _ in range(p)]
            for local, idx in enumerate(fold.train):
                value = target[idx] - dot(fold.c_train[local], beta_c)
                yres.append(value)
                row_c = fold.c_train[local]
                for jj in range(p):
                    cty[jj] += row_c[jj] * value
            out[name].append({
                "yres": yres,
                "yres_sum": sum(yres),
                "ctyres_solve": cholesky_solve(fold.chol, cty),
            })
    return out


def residualize_b_cached(b: list[list[float]], fold_cache: list[FoldCache]) -> list[list[float]]:
    width = len(b[0])
    out = [[0.0 for _ in range(width)] for _ in b]
    for fold in fold_cache:
        for col in range(width):
            y = [b[i][col] for i in fold.train]
            beta = ridge_fit(fold.c_train, y)
            for local, idx in enumerate(fold.test):
                out[idx][col] = b[idx][col] - dot(fold.c_test[local], beta)
    return out


def cv_predict_cached(target: list[float], b_resid: list[list[float]] | None, fold_cache: list[FoldCache]) -> tuple[list[float], list[list[float]]]:
    pred = [0.0 for _ in target]
    fold_betas: list[list[float]] = []
    for fold in fold_cache:
        if b_resid is not None:
            b_train, b_test = standardize_train_apply(b_resid, fold.train, fold.test)
        else:
            b_train = [[] for _ in fold.train]
            b_test = [[] for _ in fold.test]
        x_train = [fold.c_train[i] + b_train[i] for i in range(len(fold.train))]
        x_test = [fold.c_test[i] + b_test[i] for i in range(len(fold.test))]
        beta = ridge_fit(x_train, [target[i] for i in fold.train])
        if b_resid is not None:
            fold_betas.append(beta[-len(b_resid[0]):])
        for local, idx in enumerate(fold.test):
            pred[idx] = dot(x_test[local], beta)
    return pred, fold_betas


def cv_predict(target: list[float], controls: list[list[float]], b_resid: list[list[float]] | None, folds: list[tuple[list[int], list[int], str]]) -> tuple[list[float], list[list[float]]]:
    return cv_predict_cached(target, b_resid, make_fold_cache(controls, folds))


def sse(y: list[float], pred: list[float]) -> float:
    return sum((yy - pp) ** 2 for yy, pp in zip(y, pred))


def tss(y: list[float]) -> float:
    m = mean(y)
    v = sum((yy - m) ** 2 for yy in y)
    return v if v > EPS else EPS


def delta_dl_bits(base_sse: float, full_sse: float, n: int) -> float:
    return 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS), 2.0)


def target_stats_cached(target: list[float], b_resid: list[list[float]], fold_cache: list[FoldCache], base_pred: list[float] | None = None) -> dict[str, Any]:
    p2 = base_pred if base_pred is not None else cv_predict_cached(target, None, fold_cache)[0]
    p3, betas = cv_predict_cached(target, b_resid, fold_cache)
    s2 = sse(target, p2)
    s3 = sse(target, p3)
    total = tss(target)
    return {
        "R2_L2": 1.0 - s2 / total,
        "R2_L3": 1.0 - s3 / total,
        "delta_r2": (s2 - s3) / total,
        "delta_dl_bits": delta_dl_bits(s2, s3, len(target)),
        "sse_L2": s2,
        "sse_L3": s3,
        "beta_b_by_fold": betas,
    }


def target_stats(target: list[float], controls: list[list[float]], b_resid: list[list[float]], folds: list[tuple[list[int], list[int], str]]) -> dict[str, Any]:
    return target_stats_cached(target, b_resid, make_fold_cache(controls, folds))


def shuffle_within_gene_b(rows: list[dict[str, Any]], b: list[list[float]], iteration: int) -> list[list[float]]:
    out = [list(row) for row in b]
    for gene in sorted(set(r["gene"] for r in rows)):
        idx = [i for i, r in enumerate(rows) if r["gene"] == gene]
        vals = [b[i] for i in idx]
        vals = deterministic_shuffle(vals, f"{SEED}|within_gene|{iteration}|{gene}")
        for i, val in zip(idx, vals):
            out[i] = list(val)
    return out


def matched_bin_key(row: dict[str, Any]) -> tuple[str, int, int, int]:
    return (
        row["gene"],
        int(math.floor((float(row["delta_cai"]) + 1.5) / 0.5)),
        int(math.floor((float(row["delta_csc"]) + 5.0) / 1.0)),
        int(float(row["delta_gc3"]) + 1.0),
    )


def shuffle_matched_b(rows: list[dict[str, Any]], b: list[list[float]], iteration: int) -> list[list[float]]:
    out = [list(row) for row in b]
    groups: dict[tuple[str, int, int, int], list[int]] = {}
    for i, row in enumerate(rows):
        groups.setdefault(matched_bin_key(row), []).append(i)
    for key in sorted(groups):
        idx = groups[key]
        vals = [b[i] for i in idx]
        vals = deterministic_shuffle(vals, f"{SEED}|matched|{iteration}|{key}")
        for i, val in zip(idx, vals):
            out[i] = list(val)
    return out


def recoding_null_b(rows: list[dict[str, Any]], iteration: int) -> list[list[float]]:
    out = []
    for i, row in enumerate(rows):
        alts = row.get("synonymous_recoding_alternatives", [])
        choices = [row] + [alt for alt in alts if isinstance(alt, dict) and "delta_b" in alt]
        rng = stable_random(f"{SEED}|recoding|{iteration}|{i}|{row['genotype']}")
        pick = choices[rng.randrange(len(choices))]
        out.append(list(pick["delta_b"]))
    return out


def run_nulls(
    rows: list[dict[str, Any]],
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    base_betas: dict[str, list[list[float]]],
    target_cache: dict[str, list[dict[str, Any]]],
) -> dict[str, dict[str, list[float]]]:
    out = {
        name: {"within_gene": [], "matched": [], "recoding": []}
        for name in targets
    }
    jobs = [("within_gene", it) for it in range(NULL_B)] + [("matched", it) for it in range(NULL_B)] + [("recoding", it) for it in range(NULL_B)]
    workers = max(1, min(10, os.cpu_count() or 2, len(jobs)))
    if workers == 1:
        results = [_null_worker_direct(rows, b, targets, fold_cache, base_preds, base_betas, target_cache, job) for job in jobs]
    else:
        ctx = mp.get_context("fork")
        with ctx.Pool(
            processes=workers,
            initializer=_init_null_worker,
            initargs=(rows, b, targets, fold_cache, base_preds, base_betas, target_cache),
        ) as pool:
            results = pool.map(_null_worker, jobs, chunksize=4)
    for null_name, iteration, values in sorted(results, key=lambda item: (item[0], item[1])):
        for target_name, value in values.items():
            out[target_name][null_name].append(value)
    return out


def _init_null_worker(
    rows: list[dict[str, Any]],
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    base_betas: dict[str, list[list[float]]],
    target_cache: dict[str, list[dict[str, Any]]],
) -> None:
    WORKER_STATE["rows"] = rows
    WORKER_STATE["b"] = b
    WORKER_STATE["targets"] = targets
    WORKER_STATE["fold_cache"] = fold_cache
    WORKER_STATE["base_preds"] = base_preds
    WORKER_STATE["base_betas"] = base_betas
    WORKER_STATE["target_cache"] = target_cache


def _null_worker(job: tuple[str, int]) -> tuple[str, int, dict[str, float]]:
    return _null_worker_direct(
        WORKER_STATE["rows"],
        WORKER_STATE["b"],
        WORKER_STATE["targets"],
        WORKER_STATE["fold_cache"],
        WORKER_STATE["base_preds"],
        WORKER_STATE["base_betas"],
        WORKER_STATE["target_cache"],
        job,
    )


def _null_worker_direct(
    rows: list[dict[str, Any]],
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    base_betas: dict[str, list[list[float]]],
    target_cache: dict[str, list[dict[str, Any]]],
    job: tuple[str, int],
) -> tuple[str, int, dict[str, float]]:
    null_name, iteration = job
    if null_name == "within_gene":
        b_null = shuffle_within_gene_b(rows, b, iteration)
    elif null_name == "matched":
        b_null = shuffle_matched_b(rows, b, iteration)
    elif null_name == "recoding":
        b_null = recoding_null_b(rows, iteration)
    else:
        raise ValueError(null_name)
    all_stats = evaluate_b_for_targets_fast(b_null, targets, fold_cache, base_preds, base_betas, target_cache)
    return null_name, iteration, {target_name: all_stats[target_name]["delta_dl_bits"] for target_name in targets}


def sign_summary(betas_by_target: dict[str, list[list[float]]], q_names: list[str]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for target, folds in betas_by_target.items():
        rows = []
        if not folds:
            out[target] = []
            continue
        for col, q in enumerate(q_names):
            vals = [fold[col] for fold in folds]
            pos = sum(1 for v in vals if v > 0.0)
            neg = sum(1 for v in vals if v < 0.0)
            rows.append({"axis": q, "mean_beta": mean(vals), "positive_folds": pos, "negative_folds": neg})
        out[target] = rows
    return out


def p_ge(null_values: list[float], actual: float) -> float:
    return (1.0 + sum(1 for v in null_values if v >= actual)) / (len(null_values) + 1.0)


def main() -> None:
    t0 = time.time()
    repo = pathlib.Path.cwd()
    data_path = repo / DATA_REL
    cannot_claim = [
        "单核苷酸突变导致 Δb_window 稀疏，不能代表全基因 recoding 扰动。",
        "内源上下文固定但 composition/optimality 仍可能部分混淆；已用 gene、position、codon family、ΔCAI、ΔtAI、ΔCSC proxy、ΔGC3、WT codon 控制。",
        "非 RQC-specific；本实验不观测核糖体质量控制 readout。",
        "21 基因有限，leave-gene-out 外推范围有限。",
        "ΔCSC 使用 yeast codon usage within-fiber log-frequency proxy；未使用真实 Presnyak CSC。RNA MFE 未纳入，因为离线纯 stdlib 无可靠热力学引擎。",
        "fitness 是多因素 readout；fitness_resid 只是在 mRNA 线性残差之外，不等于机制分离。"
    ]
    base_checks = {
        "data_fetched": False,
        "cds_mapped": False,
        "delta_b_window_computed": False,
        "controls_built": False,
        "ladder_L2_L3_leavegeneout": False,
        "nulls_run": False,
        "perturbation_verdict": False,
    }
    if not data_path.exists():
        emit("needs_data", base_checks, "needs_data", {"missing": str(DATA_REL)}, cannot_claim)
    payload = load_json(data_path)
    checks = dict(base_checks)
    checks["data_fetched"] = bool(payload.get("checks", {}).get("data_fetched"))
    checks["cds_mapped"] = bool(payload.get("checks", {}).get("cds_mapped"))
    checks["delta_b_window_computed"] = bool(payload.get("checks", {}).get("delta_b_window_computed"))
    rows_all = payload.get("rows", [])
    rows = [r for r in rows_all if r.get("mutation_type") == "Synonymous_mutation"]
    if len(rows) < 100 or len(set(r["gene"] for r in rows)) < 10:
        result = {
            "n_genes": len(set(r.get("gene") for r in rows)),
            "n_synonymous_mutants": len(rows),
            "cds_map_hit": sum(1 for v in payload.get("cds_map", {}).values() if v.get("hit")),
            "actual_B": NULL_B,
            "runtime_sec": round(time.time() - t0, 3),
            "per_target": {},
            "beta_b_sign_by_fold": {},
        }
        emit("needs_data", checks, "needs_data", result, cannot_claim)

    controls = build_controls(rows)
    checks["controls_built"] = True
    folds = folds_by_gene(rows)
    fold_cache = make_fold_cache(controls, folds)
    b = [list(map(float, r["delta_b"])) for r in rows]
    mrna = [float(r["mrna_rel_mean"]) for r in rows]
    fitness = [float(r["fitness_ypd_mean"]) for r in rows]
    # fitness_resid = fitness - E[fitness | mRNA]，同样按 leave-gene-out 训练折估计，避免目标泄漏。
    mrna_control = [[1.0, v] for v in mrna]
    pred_fit_from_mrna, _ = cv_predict(fitness, mrna_control, None, folds)
    fitness_resid = [fitness[i] - pred_fit_from_mrna[i] for i in range(len(rows))]
    targets = {"mrna": mrna, "fitness": fitness, "fitness_resid": fitness_resid}

    stats: dict[str, dict[str, Any]] = {}
    betas_by_target = {}
    base_info = {name: control_predictions(target, fold_cache) for name, target in targets.items()}
    base_preds = {name: item[0] for name, item in base_info.items()}
    base_betas = {name: item[1] for name, item in base_info.items()}
    target_cache = build_target_cache(targets, fold_cache, base_betas)
    all_actual = evaluate_b_for_targets_fast(b, targets, fold_cache, base_preds, base_betas, target_cache)
    for name, target in targets.items():
        stat = all_actual[name]
        betas_by_target[name] = stat.pop("beta_b_by_fold")
        stats[name] = stat
    checks["ladder_L2_L3_leavegeneout"] = True

    nulls = run_nulls(rows, b, targets, fold_cache, base_preds, base_betas, target_cache)
    checks["nulls_run"] = True
    per_target: dict[str, Any] = {}
    for name in ["mrna", "fitness", "fitness_resid"]:
        actual = stats[name]["delta_dl_bits"]
        null_within = nulls[name]["within_gene"]
        null_matched = nulls[name]["matched"]
        null_recoding = nulls[name]["recoding"]
        per_target[name] = {
            "R2_L2": stats[name]["R2_L2"],
            "R2_L3": stats[name]["R2_L3"],
            "delta_r2": stats[name]["delta_r2"],
            "delta_dl_bits": actual,
            "p_within_gene": p_ge(null_within, actual),
            "p_matched": p_ge(null_matched, actual),
            "p_recoding": p_ge(null_recoding, actual),
            "null95_within_gene": percentile_nearest_rank(null_within, 0.95),
            "null95_matched": percentile_nearest_rank(null_matched, 0.95),
            "null95_recoding": percentile_nearest_rank(null_recoding, 0.95),
        }

    beta_sign = sign_summary(betas_by_target, list(payload.get("q_names", [])))
    def beats_all_nulls(name: str) -> bool:
        row = per_target[name]
        return (
            row["delta_dl_bits"] > row["null95_within_gene"]
            and row["delta_dl_bits"] > row["null95_matched"]
            and row["delta_dl_bits"] > row["null95_recoding"]
            and row["delta_r2"] > 0.0
        )

    def sign_stable(name: str) -> bool:
        rows_sign = beta_sign.get(name, [])
        if not rows_sign:
            return False
        best = max(rows_sign, key=lambda x: abs(x["mean_beta"]))
        return max(best["positive_folds"], best["negative_folds"]) >= max(12, int(0.75 * len(folds)))

    if beats_all_nulls("fitness_resid") and sign_stable("fitness_resid"):
        verdict = "fitness_residual_escape_candidate"
    elif beats_all_nulls("mrna") and not beats_all_nulls("fitness_resid"):
        verdict = "causal_execution_like"
    elif per_target["mrna"]["delta_dl_bits"] <= per_target["mrna"]["null95_matched"] or per_target["mrna"]["delta_dl_bits"] <= per_target["mrna"]["null95_recoding"]:
        verdict = "composition_artifact"
    else:
        verdict = "yeast_endogenous_perturbation_null"
    if per_target["mrna"]["delta_dl_bits"] <= 0.0 and per_target["fitness"]["delta_dl_bits"] <= 0.0 and per_target["fitness_resid"]["delta_dl_bits"] <= 0.0:
        verdict = "yeast_endogenous_perturbation_null"
    checks["perturbation_verdict"] = True
    result = {
        "n_genes": len(set(r["gene"] for r in rows)),
        "n_synonymous_mutants": len(rows),
        "cds_map_hit": sum(1 for v in payload.get("cds_map", {}).values() if v.get("hit")),
        "actual_B": NULL_B,
        "runtime_sec": round(time.time() - t0, 3),
        "per_target": per_target,
        "beta_b_sign_by_fold": beta_sign,
    }
    emit("passed", checks, verdict, result, cannot_claim)


if __name__ == "__main__":
    main()

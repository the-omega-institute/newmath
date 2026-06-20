#!/usr/bin/env python3
"""Cross-dataset 9D B_window axis transfer meta-analysis.

纯 stdlib 单文件实验。运行目录应为 repo 根目录。
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import re
import sys
import time
import zipfile
import xml.etree.ElementTree as ET
from typing import Any


EXPERIMENT_ID = "b_star_window_cross_dataset_axis_transfer_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation_meta.b_star_window_cross_dataset_axis_transfer_powered"

FOLD_COUNT = 5
NULL_B = 200
RIDGE = 1e-6
EPS = 1e-12
MAX_NIU_ANALYSIS_PER_CELL_LINE = 3000
SEED = "sha256:b_star_window_cross_dataset_axis_transfer_powered:deterministic"

DATA_SHEN = pathlib.Path("tools/bio_reality/data/shen2022_yeast_synonymous_perturbation.json")
DATA_NIEU_XLSX = pathlib.Path("tools/bio_reality/data/nieuwkoop_mrfp.xlsx")
DATA_NIEU_CAI = pathlib.Path("tools/bio_reality/data/ecoli_genome_cai_weights.json")
DATA_CHEN = pathlib.Path("tools/bio_reality/data/chen2017_gfp_synonymous.json")
DATA_NIU = pathlib.Path("tools/bio_reality/data/niu_human_prime_editor_synonymous.json")

Q_NAMES = [
    "K_AAA",
    "Arg_AGR",
    "Ile_AUA",
    "Leu_CUN_vs_UUR",
    "Leu_UUA_vs_UUG",
    "Ser_UCR_vs_AGY",
    "Ser_UCA_vs_UCG",
    "Thr_ACR_vs_ACY",
    "f3_stress",
]

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]
STANDARD_CODE_RNA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "GCA", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}
STANDARD_CODE_RNA["GCC"] = "A"


class FoldCache:
    def __init__(
        self,
        train: list[int],
        test: list[int],
        fold_id: str,
        c_train: list[list[float]],
        c_test: list[list[float]],
        chol: list[list[float]],
    ) -> None:
        self.train = train
        self.test = test
        self.fold_id = fold_id
        self.c_train = c_train
        self.c_test = c_test
        self.chol = chol
        width = len(c_train[0])
        self.c_train_sums = [sum(row[j] for row in c_train) for j in range(width)]


class Dataset:
    def __init__(
        self,
        name: str,
        rows: list[dict[str, Any]],
        b: list[list[float]],
        y: list[float],
        controls: list[list[float]],
        folds: list[tuple[list[int], list[int], str]],
        perm_keys: list[Any],
        notes: dict[str, Any],
    ) -> None:
        self.name = name
        self.rows = rows
        self.b = b
        self.y = y
        self.controls = controls
        self.folds = folds
        self.perm_keys = perm_keys
        self.notes = notes
        self.fold_cache = make_fold_cache(controls, folds)
        base_pred, base_betas = control_predictions(y, self.fold_cache)
        self.base_pred = base_pred
        self.base_betas = base_betas
        self.target_cache = build_target_cache(y, self.fold_cache, base_betas)


def emit(status: str, checks: dict[str, bool], verdict: str, result: dict[str, Any]) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


def finite(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    c = mean(values)
    return sum((x - c) ** 2 for x in values) / len(values)


def sse(y: list[float], pred: list[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(y, pred))


def tss(y: list[float]) -> float:
    c = mean(y)
    out = sum((v - c) ** 2 for v in y)
    return out if out > EPS else EPS


def delta_ll(base_sse: float, full_sse: float, n: int) -> float:
    return 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def p_ge(null_values: list[float], observed: float) -> float:
    return (1.0 + sum(1 for value in null_values if value >= observed)) / (len(null_values) + 1.0)


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


def dot(row: list[float], beta: list[float]) -> float:
    return sum(row[i] * beta[i] for i in range(len(beta)))


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
        pv = aug[col][col] if abs(aug[col][col]) > EPS else EPS
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
                chol[i][j] = math.sqrt(value if value > EPS else EPS)
            else:
                chol[i][j] = value / chol[j][j]
    return chol


def cholesky_solve(chol: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    y = [0.0 for _ in range(n)]
    for i in range(n):
        value = rhs[i]
        for k in range(i):
            value -= chol[i][k] * y[k]
        y[i] = value / chol[i][i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        value = y[i]
        for k in range(i + 1, n):
            value -= chol[k][i] * x[k]
        x[i] = value / chol[i][i]
    return x


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


def standardize_train_apply(matrix: list[list[float]], train: list[int], test: list[int]) -> tuple[list[list[float]], list[list[float]], list[tuple[float, float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test], []
    width = len(matrix[0])
    stats: list[tuple[float, float]] = []
    for col in range(width):
        vals = [matrix[i][col] for i in train]
        c = mean(vals)
        sd = math.sqrt(variance(vals))
        stats.append((c, sd if sd > EPS else 1.0))
    tr = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in train]
    te = [[(matrix[i][col] - stats[col][0]) / stats[col][1] for col in range(width)] for i in test]
    return tr, te, stats


def one_hot(values: list[str]) -> list[list[float]]:
    cats = sorted(set(values))
    if len(cats) <= 1:
        return [[] for _ in values]
    cats = cats[1:]
    return [[1.0 if value == cat else 0.0 for cat in cats] for value in values]


def make_fold_cache(controls: list[list[float]], folds: list[tuple[list[int], list[int], str]]) -> list[FoldCache]:
    caches: list[FoldCache] = []
    for train, test, fold_id in folds:
        c_train, c_test, _stats = standardize_train_apply(controls, train, test)
        x_train = [[1.0] + row for row in c_train]
        x_test = [[1.0] + row for row in c_test]
        caches.append(FoldCache(train, test, fold_id, x_train, x_test, ridge_xtx_cholesky(x_train)))
    return caches


def control_beta_vector(fold: FoldCache, values: list[float]) -> list[float]:
    width = len(fold.c_train[0])
    rhs = [0.0 for _ in range(width)]
    for local, idx in enumerate(fold.train):
        row = fold.c_train[local]
        value = values[idx]
        for j in range(width):
            rhs[j] += row[j] * value
    return cholesky_solve(fold.chol, rhs)


def control_predictions(target: list[float], fold_cache: list[FoldCache]) -> tuple[list[float], list[list[float]]]:
    pred = [0.0 for _ in target]
    betas: list[list[float]] = []
    for fold in fold_cache:
        beta = control_beta_vector(fold, target)
        betas.append(beta)
        for local, idx in enumerate(fold.test):
            pred[idx] = dot(fold.c_test[local], beta)
    return pred, betas


def build_target_cache(target: list[float], fold_cache: list[FoldCache], base_betas: list[list[float]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for fold_index, fold in enumerate(fold_cache):
        p = len(fold.c_train[0])
        beta_c = base_betas[fold_index]
        yres = []
        cty = [0.0 for _ in range(p)]
        for local, idx in enumerate(fold.train):
            value = target[idx] - dot(fold.c_train[local], beta_c)
            yres.append(value)
            row_c = fold.c_train[local]
            for jj in range(p):
                cty[jj] += row_c[jj] * value
        out.append({"yres": yres, "yres_sum": sum(yres), "ctyres_solve": cholesky_solve(fold.chol, cty)})
    return out


def sparse_rows(matrix: list[list[float]]) -> list[list[tuple[int, float]]]:
    return [[(j, value) for j, value in enumerate(row) if abs(value) > EPS] for row in matrix]


def evaluate_b_fast(dataset: Dataset, b: list[list[float]], cols: list[int] | None = None) -> dict[str, Any]:
    if cols is not None:
        b_use = [[row[col] for col in cols] for row in b]
    else:
        b_use = b
    q = len(b_use[0])
    sparse = sparse_rows(b_use)
    full_pred = list(dataset.base_pred)
    fold_betas: list[list[float]] = []
    for fold_index, fold in enumerate(dataset.fold_cache):
        p = len(fold.c_train[0])
        n_train = len(fold.train)
        s = [[0.0 for _ in range(q)] for _ in range(p)]
        bt_b = [[0.0 for _ in range(q)] for _ in range(q)]
        b_sum = [0.0 for _ in range(q)]
        bty = [0.0 for _ in range(q)]
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
                for c, vc in brow:
                    bt_b[a][c] += va * vc
            yres = dataset.target_cache[fold_index]["yres"][local]
            for col, value in brow:
                bty[col] += value * yres
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
        centers = [rb_sum[col] / max(1, n_train) for col in range(q)]
        scales = []
        for col in range(q):
            centered_ss = g[col][col] - 2.0 * centers[col] * rb_sum[col] + n_train * centers[col] * centers[col]
            scales.append(math.sqrt(centered_ss / max(1, n_train)) if centered_ss > EPS else 1.0)
        gz = [[0.0 for _ in range(q)] for _ in range(q)]
        for a in range(q):
            for c in range(q):
                centered = g[a][c] - centers[c] * rb_sum[a] - centers[a] * rb_sum[c] + n_train * centers[a] * centers[c]
                gz[a][c] = centered / (scales[a] * scales[c])
            gz[a][a] += RIDGE
        h = [0.0 for _ in range(q)]
        yres_sum = dataset.target_cache[fold_index]["yres_sum"]
        ctyres_solve = dataset.target_cache[fold_index]["ctyres_solve"]
        for col in range(q):
            raw_h = bty[col] - sum(s[row][col] * ctyres_solve[row] for row in range(p))
            h[col] = (raw_h - centers[col] * yres_sum) / scales[col]
        gamma = solve_linear_system(gz, h)
        fold_betas.append(gamma if cols is None else expand_beta(gamma, cols))
        for local, idx in enumerate(fold.test):
            raw = [0.0 for _ in range(q)]
            for col, value in sparse[idx]:
                raw[col] = value
            row_c = fold.c_test[local]
            z = []
            for col in range(q):
                cres = raw[col] - sum(row_c[jj] * beta_s[jj][col] for jj in range(p))
                z.append((cres - centers[col]) / scales[col])
            full_pred[idx] = dataset.base_pred[idx] + dot(z, gamma)
    s2 = sse(dataset.y, dataset.base_pred)
    s3 = sse(dataset.y, full_pred)
    total = tss(dataset.y)
    return {
        "delta_r2": (s2 - s3) / total,
        "delta_ll": delta_ll(s2, s3, len(dataset.y)),
        "sse_L2": s2,
        "sse_L3": s3,
        "R2_L2": 1.0 - s2 / total,
        "R2_L3": 1.0 - s3 / total,
        "beta_b_by_fold": fold_betas,
        "pred": full_pred,
    }


def evaluate_full_and_axis_drops(dataset: Dataset, b: list[list[float]]) -> dict[str, Any]:
    """CV score full 9D and all leave-one-axis-out models after one B residualization pass."""
    q = 9
    sparse = sparse_rows(b)
    pred_full = list(dataset.base_pred)
    pred_drop = [[value for value in dataset.base_pred] for _ in range(q)]
    for fold_index, fold in enumerate(dataset.fold_cache):
        p = len(fold.c_train[0])
        n_train = len(fold.train)
        s = [[0.0 for _ in range(q)] for _ in range(p)]
        bt_b = [[0.0 for _ in range(q)] for _ in range(q)]
        b_sum = [0.0 for _ in range(q)]
        bty = [0.0 for _ in range(q)]
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
                for c, vc in brow:
                    bt_b[a][c] += va * vc
            yres = dataset.target_cache[fold_index]["yres"][local]
            for col, value in brow:
                bty[col] += value * yres

        beta_s = [[0.0 for _ in range(q)] for _ in range(p)]
        for col in range(q):
            sol = cholesky_solve(fold.chol, [s[row][col] for row in range(p)])
            for row in range(p):
                beta_s[row][col] = sol[row]
        rb_sum = [b_sum[col] - sum(fold.c_train_sums[row] * beta_s[row][col] for row in range(p)) for col in range(q)]
        g = [[0.0 for _ in range(q)] for _ in range(q)]
        for a in range(q):
            for c in range(q):
                g[a][c] = bt_b[a][c] - sum(s[row][a] * beta_s[row][c] for row in range(p))
        centers = [rb_sum[col] / max(1, n_train) for col in range(q)]
        scales = []
        for col in range(q):
            centered_ss = g[col][col] - 2.0 * centers[col] * rb_sum[col] + n_train * centers[col] * centers[col]
            scales.append(math.sqrt(centered_ss / max(1, n_train)) if centered_ss > EPS else 1.0)
        gz = [[0.0 for _ in range(q)] for _ in range(q)]
        for a in range(q):
            for c in range(q):
                centered = g[a][c] - centers[c] * rb_sum[a] - centers[a] * rb_sum[c] + n_train * centers[a] * centers[c]
                gz[a][c] = centered / (scales[a] * scales[c])
            gz[a][a] += RIDGE
        h = [0.0 for _ in range(q)]
        yres_sum = dataset.target_cache[fold_index]["yres_sum"]
        ctyres_solve = dataset.target_cache[fold_index]["ctyres_solve"]
        for col in range(q):
            raw_h = bty[col] - sum(s[row][col] * ctyres_solve[row] for row in range(p))
            h[col] = (raw_h - centers[col] * yres_sum) / scales[col]

        gamma_full = solve_linear_system(gz, h)
        gamma_drop: list[tuple[list[int], list[float]]] = []
        for axis in range(q):
            cols = [col for col in range(q) if col != axis]
            sub_g = [[gz[a][c] for c in cols] for a in cols]
            sub_h = [h[col] for col in cols]
            gamma_drop.append((cols, solve_linear_system(sub_g, sub_h)))

        test_z: list[list[float]] = []
        for local, idx in enumerate(fold.test):
            raw = [0.0 for _ in range(q)]
            for col, value in sparse[idx]:
                raw[col] = value
            row_c = fold.c_test[local]
            z = []
            for col in range(q):
                cres = raw[col] - sum(row_c[jj] * beta_s[jj][col] for jj in range(p))
                z.append((cres - centers[col]) / scales[col])
            test_z.append(z)

        for local, idx in enumerate(fold.test):
            z = test_z[local]
            pred_full[idx] = dataset.base_pred[idx] + dot(z, gamma_full)
            for axis, (cols, gamma) in enumerate(gamma_drop):
                pred_drop[axis][idx] = dataset.base_pred[idx] + sum(z[col] * value for col, value in zip(cols, gamma))

    s2 = sse(dataset.y, dataset.base_pred)
    full_ll = delta_ll(s2, sse(dataset.y, pred_full), len(dataset.y))
    drop_ll = [delta_ll(s2, sse(dataset.y, pred_drop[axis]), len(dataset.y)) for axis in range(q)]
    return {"full_delta_ll": full_ll, "drop_delta_ll": drop_ll}


def expand_beta(beta: list[float], cols: list[int]) -> list[float]:
    out = [0.0 for _ in range(9)]
    for value, col in zip(beta, cols):
        out[col] = value
    return out


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    if not values:
        return []
    ordered = sorted(values)
    return [ordered[max(0, min(len(ordered) - 1, math.ceil(len(ordered) * i / bins) - 1))] for i in range(1, bins)]


def bin_index(value: float, cuts: list[float]) -> int:
    out = 0
    while out < len(cuts) and value > cuts[out]:
        out += 1
    return out


def balanced_group_folds(groups: list[str], fold_count: int, label: str) -> list[tuple[list[int], list[int], str]]:
    by_group: dict[str, list[int]] = {}
    for i, group in enumerate(groups):
        by_group.setdefault(group, []).append(i)
    bins = [[] for _ in range(fold_count)]
    sizes = [0 for _ in range(fold_count)]
    ordered = sorted(by_group.items(), key=lambda item: (-len(item[1]), item[0]))
    for group, idxs in ordered:
        target = min(range(fold_count), key=lambda k: (sizes[k], k))
        bins[target].extend(idxs)
        sizes[target] += len(idxs)
    all_idx = set(range(len(groups)))
    folds = []
    for fold_id, test in enumerate(bins):
        test_sorted = sorted(test)
        train = sorted(all_idx.difference(test_sorted))
        folds.append((train, test_sorted, f"{label}_{fold_id}"))
    return folds


def round_robin_folds(n: int, sort_values: list[float], label: str) -> list[tuple[list[int], list[int], str]]:
    ordered = sorted(range(n), key=lambda i: (sort_values[i], i))
    bins = [[] for _ in range(FOLD_COUNT)]
    for rank, idx in enumerate(ordered):
        bins[rank % FOLD_COUNT].append(idx)
    all_idx = set(range(n))
    folds = []
    for fold_id, test in enumerate(bins):
        test = deterministic_shuffle(test, f"{SEED}|fold|{label}|{fold_id}")
        train = sorted(all_idx.difference(test))
        folds.append((train, sorted(test), f"{label}_{fold_id}"))
    return folds


def oof_residual_y_on_x(y: list[float], x: list[float], folds: list[tuple[list[int], list[int], str]]) -> list[float]:
    pred = [0.0 for _ in y]
    for train, test, _fold_id in folds:
        vals = [x[i] for i in train]
        c = mean(vals)
        sd = math.sqrt(variance(vals))
        if sd <= EPS:
            sd = 1.0
        x_train = [[1.0, (x[i] - c) / sd] for i in train]
        beta = ridge_fit(x_train, [y[i] for i in train])
        for idx in test:
            pred[idx] = beta[0] + beta[1] * ((x[idx] - c) / sd)
    return [y[i] - pred[i] for i in range(len(y))]


def permute_b_by_keys(b: list[list[float]], keys: list[Any], iteration: int, label: str) -> list[list[float]]:
    groups: dict[str, list[int]] = {}
    for i, key in enumerate(keys):
        groups.setdefault(repr(key), []).append(i)
    out = [list(row) for row in b]
    for key in sorted(groups):
        idxs = groups[key]
        if len(idxs) < 2:
            continue
        src = deterministic_shuffle(idxs, f"{SEED}|perm|{label}|{iteration}|{key}")
        for dst, source in zip(idxs, src):
            out[dst] = list(b[source])
    return out


def permute_values_by_keys(values: list[float], keys: list[Any], iteration: int, label: str) -> list[float]:
    groups: dict[str, list[int]] = {}
    for i, key in enumerate(keys):
        groups.setdefault(repr(key), []).append(i)
    out = list(values)
    for key in sorted(groups):
        idxs = groups[key]
        if len(idxs) < 2:
            continue
        src = deterministic_shuffle(idxs, f"{SEED}|perm_scalar|{label}|{iteration}|{key}")
        for dst, source in zip(idxs, src):
            out[dst] = values[source]
    return out


def one_hot_join(*parts: list[list[float]]) -> list[list[float]]:
    if not parts:
        return []
    n = len(parts[0])
    out = []
    for i in range(n):
        row: list[float] = []
        for part in parts:
            row.extend(part[i])
        out.append(row)
    return out


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_shen(repo: pathlib.Path) -> Dataset:
    payload = load_json(repo / DATA_SHEN)
    if [str(x) for x in payload.get("q_names", [])] != Q_NAMES:
        raise ValueError("Shen q_names mismatch")
    rows = []
    for row in payload.get("rows", []):
        if not isinstance(row, dict) or row.get("mutation_type") != "Synonymous_mutation":
            continue
        b = row.get("delta_b")
        required = ["fitness_ypd_mean", "mrna_rel_mean", "codon_pos_norm", "delta_cai", "delta_tai", "delta_csc", "delta_gc3"]
        if isinstance(b, list) and len(b) == 9 and all(finite(row.get(k)) for k in required):
            rows.append(row)
    genes = [str(r["gene"]) for r in rows]
    folds = balanced_group_folds(genes, FOLD_COUNT, "shen_gene_block")
    b = [list(map(float, r["delta_b"])) for r in rows]
    mrna = [float(r["mrna_rel_mean"]) for r in rows]
    fitness = [float(r["fitness_ypd_mean"]) for r in rows]
    y = oof_residual_y_on_x(fitness, mrna, folds)
    gene_oh = one_hot(genes)
    fam_oh = one_hot([str(r["codon_family"]) for r in rows])
    wt_oh = one_hot([str(r["wt_codon"]) for r in rows])
    joined = one_hot_join(gene_oh, fam_oh, wt_oh)
    controls = []
    for i, r in enumerate(rows):
        controls.append([
            float(r["codon_pos_norm"]),
            float(r["delta_cai"]),
            float(r["delta_tai"]),
            float(r["delta_csc"]),
            float(r["delta_gc3"]),
        ] + joined[i])
    pos_cuts = quantile_cuts([float(r["codon_pos_norm"]) for r in rows], 5)
    perm_keys = [(str(r["gene"]), bin_index(float(r["codon_pos_norm"]), pos_cuts)) for r in rows]
    return Dataset("shen", rows, b, y, controls, folds, perm_keys, {"outcome": "fitness|mRNA_oof", "n_genes": len(set(genes))})


def col_to_index(column: str) -> int:
    out = 0
    for char in column:
        out = out * 26 + ord(char) - ord("A") + 1
    return out - 1


def xlsx_cell_text(cell: ET.Element, shared_strings: list[str], ns: str) -> str:
    cell_type = cell.attrib.get("t")
    value = cell.find(ns + "v")
    if cell_type == "s" and value is not None:
        return shared_strings[int(value.text or "0")]
    if cell_type == "inlineStr":
        inline = cell.find(ns + "is")
        if inline is None:
            return ""
        return "".join(text.text or "" for text in inline.iter(ns + "t"))
    return value.text if value is not None and value.text is not None else ""


def parse_xlsx_rows(path: pathlib.Path) -> list[dict[str, Any]]:
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    with zipfile.ZipFile(path) as zf:
        shared_strings: list[str] = []
        shared_xml = ET.fromstring(zf.read("xl/sharedStrings.xml"))
        for item in shared_xml.iter(ns + "si"):
            shared_strings.append("".join(text.text or "" for text in item.iter(ns + "t")))
        sheet_xml = ET.fromstring(zf.read("xl/worksheets/sheet2.xml"))
        raw_rows: list[dict[int, str]] = []
        for row in sheet_xml.iter(ns + "row"):
            values: dict[int, str] = {}
            for cell in row.iter(ns + "c"):
                match = re.match(r"([A-Z]+)", cell.attrib["r"])
                if match:
                    values[col_to_index(match.group(1))] = xlsx_cell_text(cell, shared_strings, ns)
            if values:
                raw_rows.append(values)
    if not raw_rows:
        raise ValueError("xlsx sheet2 is empty")
    header = {value: idx for idx, value in raw_rows[0].items()}
    required = ["Header", "Plate+location", "mRFP Mean Corrected", "Sequence Data"]
    missing = [name for name in required if name not in header]
    if missing:
        raise ValueError(f"missing required columns: {missing}")
    out = []
    for raw_index, raw in enumerate(raw_rows[1:], start=2):
        seq = str(raw.get(header["Sequence Data"], "")).strip().upper()
        corrected_text = str(raw.get(header["mRFP Mean Corrected"], "")).strip()
        try:
            corrected = float(corrected_text)
        except ValueError:
            continue
        if corrected <= 0.0 or len(seq) % 3 != 0 or seq[:3] != "ATG" or set(seq) - {"A", "T", "G", "C"}:
            continue
        codons = [seq[i:i + 3].replace("T", "U") for i in range(0, len(seq), 3)]
        if any(STANDARD_CODE_RNA.get(codon) is None for codon in codons):
            continue
        if any(STANDARD_CODE_RNA[codon] == "*" for codon in codons[:-1]):
            continue
        out.append({
            "id": len(out),
            "xlsx_row": raw_index,
            "header": raw.get(header["Header"], ""),
            "plate_location": raw.get(header["Plate+location"], ""),
            "sequence": seq,
            "mrfp_mean_corrected": corrected,
            "log_protein_output": math.log(corrected),
        })
    return out


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        aa = code[codon]
        if aa != "*":
            fibers.setdefault(aa, []).append(codon)
    return fibers


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def q_vectors(codons: list[str]) -> dict[str, dict[str, float]]:
    raw: dict[str, dict[str, float]] = {}
    q = zero(codons); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero(codons)
    for codon in ["AGA", "AGG"]:
        q[codon] = 1.0
    for codon in ["CGU", "CGC", "CGA", "CGG"]:
        q[codon] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for codon in CUN_CODONS:
        q[codon] = 0.25
    for codon in UUR_CODONS:
        q[codon] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for codon in ["UCA", "UCG"]:
        q[codon] = 0.5
    for codon in ["AGU", "AGC"]:
        q[codon] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for codon in ["ACA", "ACG"]:
        q[codon] = 0.5
    for codon in ["ACU", "ACC"]:
        q[codon] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def q_context() -> dict[str, Any]:
    codons = sorted(codon for codon, aa in STANDARD_CODE_RNA.items() if aa != "*")
    fibers = fibers_for(STANDARD_CODE_RNA, codons)
    projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    denoms = {name: math.sqrt(sum(projected[name][codon] ** 2 for codon in codons)) for name in Q_NAMES}
    return {"codons": codons, "fibers": fibers, "q_projected": projected, "q_denoms": denoms}


def codon_counts(sequence: str, codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in codons}
    for index in range(0, len(sequence) - 2, 3):
        codon = sequence[index:index + 3].replace("T", "U")
        if codon in counts:
            counts[codon] += 1
    return counts


def q_row_from_counts(counts: dict[str, int], context: dict[str, Any]) -> list[float]:
    codons = context["codons"]
    total = sum(counts[codon] for codon in codons)
    if total <= 0:
        raise ValueError("empty codon counts")
    row = []
    for name in Q_NAMES:
        qvec = context["q_projected"][name]
        denom = float(context["q_denoms"][name])
        row.append(sum((counts[codon] / total) * float(qvec[codon]) for codon in codons) / denom)
    return row


def geometric_index(counts: dict[str, int], weights: dict[str, float]) -> float:
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    return math.exp(sum(counts[codon] * math.log(max(weights[codon], EPS)) for codon in counts) / total)


def load_genome_cai_reference(path: pathlib.Path, context: dict[str, Any]) -> dict[str, Any]:
    payload = load_json(path)
    weights = payload.get("weights_rna")
    rscu_dna = payload.get("rscu_dna", {})
    counts_dna = payload.get("codon_counts_dna", {})
    if not isinstance(weights, dict):
        raise ValueError("E.coli CAI weights malformed")
    codons = context["codons"]
    fibers = context["fibers"]
    cai_weight = {codon: max(float(weights[codon]), EPS) for codon in codons}
    total_counts = sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons)
    genome_gc3 = 0.5 if total_counts <= EPS else sum(float(counts_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons if codon[2] in {"G", "C"}) / total_counts
    rscu = {codon: float(rscu_dna.get(codon.replace("U", "T"), 0.0)) for codon in codons}
    tai_weight: dict[str, float] = {}
    for fiber in fibers.values():
        raw = {}
        for codon in fiber:
            gc_class = genome_gc3 if codon[2] in {"G", "C"} else (1.0 - genome_gc3)
            raw[codon] = max(rscu.get(codon, 0.0), EPS) * max(gc_class, EPS)
        max_raw = max(raw.values()) if raw else 1.0
        for codon in fiber:
            tai_weight[codon] = max(raw[codon] / max_raw, EPS)
    return {"cai_weight": cai_weight, "tai_weight": tai_weight, "path": str(path)}


def load_nieuwkoop(repo: pathlib.Path) -> Dataset:
    rows = parse_xlsx_rows(repo / DATA_NIEU_XLSX)
    context = q_context()
    refs = load_genome_cai_reference(repo / DATA_NIEU_CAI, context)
    codons = context["codons"]
    b: list[list[float]] = []
    controls: list[list[float]] = []
    target: list[float] = []
    cai_values: list[float] = []
    gc3_values: list[float] = []
    lengths: list[float] = []
    kept: list[dict[str, Any]] = []
    for row in rows:
        seq = str(row["sequence"])
        counts = codon_counts(seq, codons)
        total_codons = sum(counts.values())
        if total_codons <= 0:
            continue
        gc = (seq.count("G") + seq.count("C")) / len(seq)
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total_codons
        cai = geometric_index(counts, refs["cai_weight"])
        tai = geometric_index(counts, refs["tai_weight"])
        length = math.log(total_codons * 3)
        b.append(q_row_from_counts(counts, context))
        controls.append([cai, tai, gc, gc3, length])
        target.append(float(row["log_protein_output"]))
        cai_values.append(cai)
        gc3_values.append(gc3)
        lengths.append(length)
        kept.append(row)
    folds = round_robin_folds(len(target), target, "nieuwkoop_library")
    y = oof_residual_y_on_x(target, cai_values, folds)
    cai_cuts = quantile_cuts(cai_values, 5)
    gc3_cuts = quantile_cuts(gc3_values, 3)
    len_cuts = quantile_cuts(lengths, 3)
    perm_keys = [(bin_index(cai_values[i], cai_cuts), bin_index(gc3_values[i], gc3_cuts), bin_index(lengths[i], len_cuts)) for i in range(len(target))]
    return Dataset("nieuwkoop", kept, b, y, controls, folds, perm_keys, {"outcome": "log_protein|CAI_oof", "cai_source": refs["path"]})


def load_chen(repo: pathlib.Path) -> Dataset:
    payload = load_json(repo / DATA_CHEN)
    if [str(x) for x in payload.get("q_names", [])] != Q_NAMES:
        raise ValueError("Chen q_names mismatch")
    rows = []
    for row in payload.get("rows", []):
        b = row.get("b_window") if isinstance(row, dict) else None
        c = row.get("controls", {}) if isinstance(row, dict) else {}
        t = row.get("targets", {}) if isinstance(row, dict) else {}
        if (
            isinstance(b, list) and len(b) == 9 and all(finite(x) for x in b)
            and all(finite(c.get(k)) for k in ("CAI", "tAI", "MFE", "GC3"))
            and finite(t.get("mrna")) and finite(t.get("protein"))
            and int(row.get("region")) in (1, 2)
        ):
            rows.append(row)
    controls = []
    for row in rows:
        c = row["controls"]
        region = int(row["region"])
        controls.append([1.0 if region == 2 else 0.0, float(c["CAI"]), float(c["tAI"]), float(c["MFE"]), float(c["GC3"])])
    by_region: dict[int, list[int]] = {1: [], 2: []}
    for i, row in enumerate(rows):
        by_region[int(row["region"])].append(i)
    fold_tests = [[] for _ in range(FOLD_COUNT)]
    for region in sorted(by_region):
        idxs = deterministic_shuffle(by_region[region], f"{SEED}|chen_folds|region={region}")
        for pos, idx in enumerate(idxs):
            fold_tests[pos % FOLD_COUNT].append(idx)
    all_idx = set(range(len(rows)))
    folds = []
    for fold_id, test in enumerate(fold_tests):
        test = sorted(test)
        folds.append((sorted(all_idx.difference(test)), test, f"chen_region_mixed_{fold_id}"))
    mrna = [float(row["targets"]["mrna"]) for row in rows]
    protein = [float(row["targets"]["protein"]) for row in rows]
    y = oof_residual_y_on_x(protein, mrna, folds)
    b = [list(map(float, row["b_window"])) for row in rows]
    mrna_cuts = quantile_cuts(mrna, 5)
    perm_keys = [(int(row["region"]), bin_index(mrna[i], mrna_cuts)) for i, row in enumerate(rows)]
    return Dataset("chen", rows, b, y, controls, folds, perm_keys, {"outcome": "protein|mRNA_oof", "window": "12-codon"})


def niu_finite_row(row: dict[str, Any]) -> bool:
    required = ["median_lfc", "old_codon_freq", "new_codon_freq", "delta_freq", "delta_gc", "expression_tpm", "essentiality", "editing_efficiency_proxy", "delta_b"]
    for key in required[:-1]:
        if not finite(row.get(key)):
            return False
    return isinstance(row.get("delta_b"), list) and len(row["delta_b"]) == 9


def niu_sample(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for cell_line in sorted(set(str(r["cell_line"]) for r in rows)):
        subset = [r for r in rows if str(r["cell_line"]) == cell_line]
        ranked = sorted(subset, key=lambda r: stable_digest(f"{SEED}|niu_sample|{cell_line}|{r['mutation_name']}"))
        out.extend(ranked[:MAX_NIU_ANALYSIS_PER_CELL_LINE])
    return sorted(out, key=lambda r: (str(r["cell_line"]), str(r["gene"]), str(r["mutation_name"])))


def load_niu(repo: pathlib.Path) -> Dataset:
    payload = load_json(repo / DATA_NIU)
    if [str(x) for x in payload.get("q_names", [])] != Q_NAMES:
        raise ValueError("Niu q_names mismatch")
    compact_rows = [r for r in payload.get("rows", []) if isinstance(r, dict) and niu_finite_row(r)]
    rows = niu_sample(compact_rows)
    families = one_hot([str(r["codon_family"]) for r in rows])
    cell_lines = one_hot([str(r["cell_line"]) for r in rows])
    joined = one_hot_join(families, cell_lines)
    controls = []
    for i, r in enumerate(rows):
        controls.append([
            float(r["old_codon_freq"]),
            float(r["new_codon_freq"]),
            float(r["delta_freq"]),
            float(r["delta_gc"]),
            math.log1p(max(0.0, float(r["expression_tpm"]))),
            float(r["essentiality"]),
            float(r["editing_efficiency_proxy"]),
        ] + joined[i])
    genes = [str(r["gene"]) for r in rows]
    folds = balanced_group_folds(genes, FOLD_COUNT, "niu_gene_block")
    b = [list(map(float, r["delta_b"])) for r in rows]
    y = [float(r["median_lfc"]) for r in rows]
    perm_keys = [(str(r["gene"]), str(r["cell_line"])) for r in rows]
    return Dataset("niu", rows, b, y, controls, folds, perm_keys, {"outcome": "fitness|editing_controls", "n_compact": len(compact_rows), "max_per_cell_line": MAX_NIU_ANALYSIS_PER_CELL_LINE})


def omnibus_with_null(dataset: Dataset) -> dict[str, Any]:
    actual = evaluate_b_fast(dataset, dataset.b)
    null_values = []
    for trial in range(NULL_B):
        b_null = permute_b_by_keys(dataset.b, dataset.perm_keys, trial, dataset.name)
        null_values.append(float(evaluate_b_fast(dataset, b_null)["delta_ll"]))
    p = p_ge(null_values, float(actual["delta_ll"]))
    null95 = percentile_nearest_rank(null_values, 0.95)
    passed = actual["delta_r2"] > 0.0 and actual["delta_ll"] > null95 and p <= 0.05
    return {
        "delta_r2": float(actual["delta_r2"]),
        "delta_ll": float(actual["delta_ll"]),
        "p_block": p,
        "null95": null95,
        "passed": bool(passed),
        "beta_b_by_fold": actual["beta_b_by_fold"],
    }


def full_fit_beta(dataset: Dataset) -> list[float]:
    n = len(dataset.y)
    all_idx = list(range(n))
    c_std, _empty, _stats = standardize_train_apply(dataset.controls, all_idx, [])
    x = [[1.0] + row for row in c_std]
    chol = ridge_xtx_cholesky(x)
    beta_y = cholesky_solve(chol, [sum(x[i][j] * dataset.y[i] for i in range(n)) for j in range(len(x[0]))])
    yres = [dataset.y[i] - dot(x[i], beta_y) for i in range(n)]
    b_res_cols: list[list[float]] = []
    for col in range(9):
        vals = [dataset.b[i][col] for i in range(n)]
        rhs = [sum(x[i][j] * vals[i] for i in range(n)) for j in range(len(x[0]))]
        beta_b = cholesky_solve(chol, rhs)
        resid = [vals[i] - dot(x[i], beta_b) for i in range(n)]
        b_res_cols.append(resid)
    b_std = [[b_res_cols[col][i] for col in range(9)] for i in range(n)]
    gamma = ridge_fit(b_std, yres)
    norm = math.sqrt(sum(v * v for v in gamma))
    if norm <= EPS:
        return [0.0 for _ in gamma]
    return [v / norm for v in gamma]


def projection_eval_values(dataset: Dataset, raw_projection: list[float]) -> dict[str, float]:
    full_pred = list(dataset.base_pred)
    for fold_index, fold in enumerate(dataset.fold_cache):
        rhs = [0.0 for _ in range(len(fold.c_train[0]))]
        for local, idx in enumerate(fold.train):
            row = fold.c_train[local]
            value = raw_projection[idx]
            for j in range(len(rhs)):
                rhs[j] += row[j] * value
        beta_proj = cholesky_solve(fold.chol, rhs)
        proj_train = [raw_projection[idx] - dot(fold.c_train[local], beta_proj) for local, idx in enumerate(fold.train)]
        proj_test = [raw_projection[idx] - dot(fold.c_test[local], beta_proj) for local, idx in enumerate(fold.test)]
        yres = dataset.target_cache[fold_index]["yres"]
        denom = sum(v * v for v in proj_train) + RIDGE
        scale = sum(v * y for v, y in zip(proj_train, yres)) / denom
        for local, idx in enumerate(fold.test):
            full_pred[idx] = dataset.base_pred[idx] + scale * proj_test[local]
    s2 = sse(dataset.y, dataset.base_pred)
    s3 = sse(dataset.y, full_pred)
    return {"proj_delta_ll": delta_ll(s2, s3, len(dataset.y)), "proj_delta_r2": (s2 - s3) / tss(dataset.y)}


def projection_with_null(dataset: Dataset, direction: list[float], label: str) -> dict[str, float]:
    raw_projection = [dot(row, direction) for row in dataset.b]
    actual = projection_eval_values(dataset, raw_projection)
    null_values = []
    for trial in range(NULL_B):
        proj_null = permute_values_by_keys(raw_projection, dataset.perm_keys, trial, f"{dataset.name}|{label}")
        null_values.append(projection_eval_values(dataset, proj_null)["proj_delta_ll"])
    p = p_ge(null_values, actual["proj_delta_ll"])
    return {
        "proj_delta_ll": float(actual["proj_delta_ll"]),
        "proj_delta_r2": float(actual["proj_delta_r2"]),
        "p": p,
        "null95": percentile_nearest_rank(null_values, 0.95),
    }


def bh_fdr(p_values: list[float]) -> list[float]:
    m = len(p_values)
    ordered = sorted(range(m), key=lambda i: p_values[i])
    q = [1.0 for _ in p_values]
    running = 1.0
    for rank in range(m - 1, -1, -1):
        i = ordered[rank]
        value = min(running, p_values[i] * m / (rank + 1))
        running = value
        q[i] = min(1.0, value)
    return q


def axis_meta(datasets: list[Dataset], omnibus: dict[str, dict[str, Any]]) -> dict[str, dict[str, float]]:
    passing = [dataset for dataset in datasets if omnibus[dataset.name]["passed"]]
    if not passing:
        return {name: {"beta_re": 0.0, "loo_delta_ll": 0.0, "p": 1.0, "fdr_q": 1.0} for name in Q_NAMES}
    beta_re_values = random_effects_beta(passing, omnibus)
    observed_scores = {dataset.name: evaluate_full_and_axis_drops(dataset, dataset.b) for dataset in passing}
    observed = []
    for axis in range(9):
        loss = 0.0
        for dataset in passing:
            scores = observed_scores[dataset.name]
            loss += float(scores["full_delta_ll"]) - float(scores["drop_delta_ll"][axis])
        observed.append(loss)
    null_by_axis = [[] for _ in range(9)]
    for trial in range(NULL_B):
        for dataset in passing:
            b_null = permute_b_by_keys(dataset.b, dataset.perm_keys, trial, f"{dataset.name}|axis_meta")
            scores = evaluate_full_and_axis_drops(dataset, b_null)
            full = float(scores["full_delta_ll"])
            for axis in range(9):
                null_by_axis[axis].append(full - float(scores["drop_delta_ll"][axis]))
    p_values = [p_ge(null_by_axis[axis], observed[axis]) for axis in range(9)]
    q_values = bh_fdr(p_values)
    return {
        Q_NAMES[axis]: {
            "beta_re": beta_re_values[axis],
            "loo_delta_ll": observed[axis],
            "p": p_values[axis],
            "fdr_q": q_values[axis],
        }
        for axis in range(9)
    }


def random_effects_beta(datasets: list[Dataset], omnibus: dict[str, dict[str, Any]]) -> list[float]:
    out = []
    for axis in range(9):
        estimates = []
        variances = []
        for dataset in datasets:
            folds = omnibus[dataset.name]["beta_b_by_fold"]
            vals = [float(beta[axis]) for beta in folds]
            estimates.append(mean(vals))
            if len(vals) > 1:
                v = sum((x - mean(vals)) ** 2 for x in vals) / (len(vals) - 1)
                variances.append(max(v / len(vals), 1e-6))
            else:
                variances.append(1e-6)
        if len(estimates) == 1:
            out.append(estimates[0])
            continue
        weights = [1.0 / v for v in variances]
        fixed = sum(w * e for w, e in zip(weights, estimates)) / sum(weights)
        q = sum(w * (e - fixed) ** 2 for w, e in zip(weights, estimates))
        c = sum(weights) - sum(w * w for w in weights) / sum(weights)
        tau2 = max(0.0, (q - (len(estimates) - 1)) / c) if c > EPS else 0.0
        re_weights = [1.0 / (v + tau2) for v in variances]
        out.append(sum(w * e for w, e in zip(re_weights, estimates)) / sum(re_weights))
    return out


def round_float(value: Any, digits: int = 6) -> Any:
    if isinstance(value, float):
        return round(value, digits)
    if isinstance(value, dict):
        return {k: round_float(v, digits) for k, v in value.items()}
    if isinstance(value, list):
        return [round_float(v, digits) for v in value]
    return value


def main() -> None:
    started = time.time()
    repo = pathlib.Path.cwd()
    cannot_claim = [
        "4 数据集物种/读出/尺度异质(yeast fitness vs E.coli protein vs GFP reporter vs human PE)",
        "冻结方向迁移=统计非机制证据",
        "9D basis 预定义非穷尽",
        "Niu editing-confound",
        "Nieuwkoop 无 mRNA(protein|CAI 非 beyond-mRNA)",
        "Chen 12-codon window",
    ]
    checks = {
        "four_datasets_loaded": False,
        "b9_consistent_construction": False,
        "per_dataset_omnibus": False,
        "positive_transfer": False,
        "negative_falsification": False,
        "axis_fdr": False,
        "anti_posthoc_permutation": False,
        "transfer_verdict": False,
    }
    try:
        for path in (DATA_SHEN, DATA_NIEU_XLSX, DATA_NIEU_CAI, DATA_CHEN, DATA_NIU):
            if not (repo / path).exists():
                result = {
                    "datasets_loaded": [],
                    "n_per_dataset": {},
                    "actual_B": 0,
                    "runtime_sec": round(time.time() - started, 3),
                    "cannot_claim": cannot_claim + [f"missing {path}"],
                }
                emit("needs_data", checks, "needs_data", result)
        datasets = [load_shen(repo), load_nieuwkoop(repo), load_chen(repo), load_niu(repo)]
        by_name = {dataset.name: dataset for dataset in datasets}
        checks["four_datasets_loaded"] = all(len(dataset.rows) > 0 for dataset in datasets)
        checks["b9_consistent_construction"] = all(all(len(row) == 9 for row in dataset.b) for dataset in datasets)

        omnibus_raw = {dataset.name: omnibus_with_null(dataset) for dataset in datasets}
        omnibus = {
            name: {
                "delta_r2": value["delta_r2"],
                "delta_ll": value["delta_ll"],
                "p_block": value["p_block"],
                "null95": value["null95"],
                "passed": value["passed"],
            }
            for name, value in omnibus_raw.items()
        }
        checks["per_dataset_omnibus"] = True

        beta_shen = full_fit_beta(by_name["shen"])
        beta_nieu = full_fit_beta(by_name["nieuwkoop"])
        transfer = {
            "shen_to_nieu": projection_with_null(by_name["nieuwkoop"], beta_shen, "shen_frozen"),
            "nieu_to_shen": projection_with_null(by_name["shen"], beta_nieu, "nieu_frozen"),
        }
        checks["positive_transfer"] = True

        chen_sh = projection_with_null(by_name["chen"], beta_shen, "shen_frozen_negative")
        chen_ni = projection_with_null(by_name["chen"], beta_nieu, "nieu_frozen_negative")
        niu_sh = projection_with_null(by_name["niu"], beta_shen, "shen_frozen_negative")
        niu_ni = projection_with_null(by_name["niu"], beta_nieu, "nieu_frozen_negative")
        negative_falsification = {
            "chen": {
                "proj_p": min(chen_sh["p"], chen_ni["p"]),
                "shen_direction_p": chen_sh["p"],
                "nieu_direction_p": chen_ni["p"],
                "shen_proj_delta_ll": chen_sh["proj_delta_ll"],
                "nieu_proj_delta_ll": chen_ni["proj_delta_ll"],
            },
            "niu": {
                "proj_p": min(niu_sh["p"], niu_ni["p"]),
                "shen_direction_p": niu_sh["p"],
                "nieu_direction_p": niu_ni["p"],
                "shen_proj_delta_ll": niu_sh["proj_delta_ll"],
                "nieu_proj_delta_ll": niu_ni["proj_delta_ll"],
            },
        }
        checks["negative_falsification"] = True

        axis = axis_meta(datasets, omnibus_raw)
        checks["axis_fdr"] = True
        checks["anti_posthoc_permutation"] = True

        positive_omnibus = omnibus["shen"]["passed"] and omnibus["nieuwkoop"]["passed"]
        transfer_sig = transfer["shen_to_nieu"]["p"] <= 0.05 or transfer["nieu_to_shen"]["p"] <= 0.05
        negative_ok = negative_falsification["chen"]["proj_p"] > 0.05 and negative_falsification["niu"]["proj_p"] > 0.05
        if positive_omnibus and transfer_sig and negative_ok:
            verdict = "transferable_axis"
        elif positive_omnibus and not transfer_sig:
            verdict = "dataset_specific_axes"
        else:
            verdict = "no_stable_axis"
        checks["transfer_verdict"] = True

        result = {
            "datasets_loaded": [dataset.name for dataset in datasets],
            "n_per_dataset": {dataset.name: len(dataset.rows) for dataset in datasets},
            "omnibus": omnibus,
            "transfer": transfer,
            "negative_falsification": negative_falsification,
            "axis_meta": axis,
            "actual_B": NULL_B,
            "runtime_sec": round(time.time() - started, 3),
            "cannot_claim": cannot_claim,
            "dataset_notes": {dataset.name: dataset.notes for dataset in datasets},
            "frozen_directions": {"shen": beta_shen, "nieuwkoop": beta_nieu},
        }
        emit("passed", checks, verdict, round_float(result))
    except Exception as exc:
        result = {
            "datasets_loaded": [],
            "n_per_dataset": {},
            "omnibus": {},
            "transfer": {},
            "negative_falsification": {},
            "axis_meta": {},
            "actual_B": NULL_B,
            "runtime_sec": round(time.time() - started, 3),
            "cannot_claim": cannot_claim + [f"failed: {type(exc).__name__}: {exc}"],
        }
        emit("failed", checks, "no_stable_axis", result)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Niu human prime-editor synonymous fitness test for B*_Q6 window axes.

纯 stdlib离线脚本。cwd 应为 repo 根目录；数据读自
tools/bio_reality/data/niu_human_prime_editor_synonymous.json。
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


EXPERIMENT_ID = "b_star_window_human_prime_editor_fitness_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_human_prime_editor_fitness_powered"
DATA_REL = pathlib.Path("tools/bio_reality/data/niu_human_prime_editor_synonymous.json")
RIDGE = 1e-6
EPS = 1e-12
NULL_B = 200
FOLD_COUNT = 5
MAX_ANALYSIS_PER_CELL_LINE = 3000
SEED = "sha256:b_star_window_human_prime_editor_fitness_powered:deterministic"
WORKER_STATE: dict[str, Any] = {}


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


def dot(row: list[float], beta: list[float]) -> float:
    return sum(row[i] * beta[i] for i in range(len(beta)))


def dot_matrix_row(row: list[float], beta: list[list[float]], col: int) -> float:
    return sum(row[i] * beta[i][col] for i in range(len(row)))


def control_beta_vector(fold: FoldCache, values: list[float]) -> list[float]:
    width = len(fold.c_train[0])
    rhs = [0.0 for _ in range(width)]
    for local, idx in enumerate(fold.train):
        row = fold.c_train[local]
        value = values[idx]
        for j in range(width):
            rhs[j] += row[j] * value
    return cholesky_solve(fold.chol, rhs)


def standardize_train_apply(matrix: list[list[float]], train: list[int], test: list[int]) -> tuple[list[list[float]], list[list[float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test]
    width = len(matrix[0])
    centers: list[float] = []
    scales: list[float] = []
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


def build_controls(rows: list[dict[str, Any]], include_efficiency: bool) -> list[list[float]]:
    families = one_hot([str(r["codon_family"]) for r in rows])
    cell_lines = one_hot([str(r["cell_line"]) for r in rows])
    numeric = []
    for r in rows:
        values = [
            float(r["old_codon_freq"]),
            float(r["new_codon_freq"]),
            float(r["delta_freq"]),
            float(r["delta_gc"]),
            math.log1p(max(0.0, float(r["expression_tpm"]))),
            float(r["essentiality"]),
        ]
        if include_efficiency:
            values.append(float(r["editing_efficiency_proxy"]))
        numeric.append(values)
    out = []
    for i in range(len(rows)):
        out.append([1.0] + numeric[i] + families[i] + cell_lines[i])
    return out


def group_folds(rows: list[dict[str, Any]], fold_count: int) -> list[tuple[list[int], list[int], str]]:
    groups: dict[str, list[int]] = {}
    for i, row in enumerate(rows):
        groups.setdefault(str(row["gene"]), []).append(i)
    bins = [[] for _ in range(fold_count)]
    sizes = [0 for _ in range(fold_count)]
    ordered = sorted(groups.items(), key=lambda item: (-len(item[1]), item[0]))
    for gene, idx in ordered:
        target = min(range(fold_count), key=lambda k: (sizes[k], k))
        bins[target].extend(idx)
        sizes[target] += len(idx)
    folds = []
    all_idx = set(range(len(rows)))
    for fold_id, test in enumerate(bins):
        test_sorted = sorted(test)
        train = sorted(all_idx.difference(test_sorted))
        folds.append((train, test_sorted, f"gene_block_{fold_id}"))
    return folds


def make_fold_cache(controls: list[list[float]], folds: list[tuple[list[int], list[int], str]]) -> list[FoldCache]:
    raw_numeric = [row[1:] for row in controls]
    caches = []
    for train, test, fold_id in folds:
        c_train, c_test = standardize_train_apply(raw_numeric, train, test)
        x_train = [[1.0] + row for row in c_train]
        x_test = [[1.0] + row for row in c_test]
        caches.append(FoldCache(train, test, fold_id, x_train, x_test, ridge_xtx_cholesky(x_train)))
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


def sparse_rows(matrix: list[list[float]]) -> list[list[tuple[int, float]]]:
    return [[(j, value) for j, value in enumerate(row) if abs(value) > EPS] for row in matrix]


def evaluate_b_for_targets_fast(
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
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
                for c, vc in brow:
                    bt_b[a][c] += va * vc
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
            gamma = solve_linear_system(gz, h)
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


def sse(y: list[float], pred: list[float]) -> float:
    return sum((yy - pp) ** 2 for yy, pp in zip(y, pred))


def tss(y: list[float]) -> float:
    m = mean(y)
    value = sum((yy - m) ** 2 for yy in y)
    return value if value > EPS else EPS


def delta_dl_bits(base_sse: float, full_sse: float, n: int) -> float:
    return 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS), 2.0)


def matched_bin_key(row: dict[str, Any]) -> tuple[int, int, int]:
    return (
        int(math.floor((float(row["delta_freq"]) + 20.0) / 5.0)),
        int(float(row["delta_gc"]) + 3.0),
        int(math.floor((float(row["essentiality"]) + 2.0) / 0.5)),
    )


def shuffle_within_gene_b(rows: list[dict[str, Any]], b: list[list[float]], iteration: int) -> list[list[float]]:
    out = [list(row) for row in b]
    groups: dict[str, list[int]] = {}
    for i, row in enumerate(rows):
        groups.setdefault(str(row["gene"]), []).append(i)
    for gene in sorted(groups):
        idx = groups[gene]
        vals = deterministic_shuffle([b[i] for i in idx], f"{SEED}|within_gene|{iteration}|{gene}")
        for i, val in zip(idx, vals):
            out[i] = list(val)
    return out


def shuffle_matched_b(rows: list[dict[str, Any]], b: list[list[float]], iteration: int) -> list[list[float]]:
    out = [list(row) for row in b]
    groups: dict[tuple[int, int, int], list[int]] = {}
    for i, row in enumerate(rows):
        groups.setdefault(matched_bin_key(row), []).append(i)
    for key in sorted(groups):
        idx = groups[key]
        vals = deterministic_shuffle([b[i] for i in idx], f"{SEED}|matched|{iteration}|{key}")
        for i, val in zip(idx, vals):
            out[i] = list(val)
    return out


def recoding_null_b(rows: list[dict[str, Any]], iteration: int) -> list[list[float]]:
    out = []
    for i, row in enumerate(rows):
        choices = [row["delta_b"]] + [
            alt for alt in row.get("synonymous_recoding_alternatives", [])
            if isinstance(alt, list) and len(alt) == len(row["delta_b"])
        ]
        rng = stable_random(f"{SEED}|recoding|{iteration}|{i}|{row['mutation_name']}")
        out.append(list(choices[rng.randrange(len(choices))]))
    return out


def run_nulls(
    rows: list[dict[str, Any]],
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
    target_cache: dict[str, list[dict[str, Any]]],
) -> dict[str, dict[str, list[float]]]:
    out = {name: {"within_gene": [], "matched": [], "recoding": []} for name in targets}
    jobs = [("within_gene", it) for it in range(NULL_B)] + [("matched", it) for it in range(NULL_B)] + [("recoding", it) for it in range(NULL_B)]
    workers = max(1, min(8, os.cpu_count() or 2, len(jobs)))
    if workers == 1:
        results = [_null_worker_direct(rows, b, targets, fold_cache, base_preds, target_cache, job) for job in jobs]
    else:
        ctx = mp.get_context("fork")
        with ctx.Pool(
            processes=workers,
            initializer=_init_null_worker,
            initargs=(rows, b, targets, fold_cache, base_preds, target_cache),
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
    target_cache: dict[str, list[dict[str, Any]]],
) -> None:
    WORKER_STATE["rows"] = rows
    WORKER_STATE["b"] = b
    WORKER_STATE["targets"] = targets
    WORKER_STATE["fold_cache"] = fold_cache
    WORKER_STATE["base_preds"] = base_preds
    WORKER_STATE["target_cache"] = target_cache


def _null_worker(job: tuple[str, int]) -> tuple[str, int, dict[str, float]]:
    return _null_worker_direct(
        WORKER_STATE["rows"],
        WORKER_STATE["b"],
        WORKER_STATE["targets"],
        WORKER_STATE["fold_cache"],
        WORKER_STATE["base_preds"],
        WORKER_STATE["target_cache"],
        job,
    )


def _null_worker_direct(
    rows: list[dict[str, Any]],
    b: list[list[float]],
    targets: dict[str, list[float]],
    fold_cache: list[FoldCache],
    base_preds: dict[str, list[float]],
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
    stats = evaluate_b_for_targets_fast(b_null, targets, fold_cache, base_preds, target_cache)
    return null_name, iteration, {name: stats[name]["delta_dl_bits"] for name in targets}


def p_ge(null_values: list[float], actual: float) -> float:
    return (1.0 + sum(1 for value in null_values if value >= actual)) / (len(null_values) + 1.0)


def sign_summary(folds: list[list[float]], q_names: list[str]) -> dict[str, Any]:
    rows = []
    for col, q in enumerate(q_names):
        vals = [fold[col] for fold in folds if col < len(fold)]
        rows.append({
            "axis": q,
            "mean_beta": mean(vals),
            "positive_folds": sum(1 for v in vals if v > 0.0),
            "negative_folds": sum(1 for v in vals if v < 0.0),
        })
    best = max(rows, key=lambda item: abs(float(item["mean_beta"]))) if rows else None
    return {"axes": rows, "dominant": best}


def summarize_actual(
    actual: dict[str, Any],
    nulls: dict[str, dict[str, list[float]]],
    target_name: str,
    q_names: list[str],
) -> dict[str, Any]:
    dl = float(actual["delta_dl_bits"])
    bsign = sign_summary(actual["beta_b_by_fold"], q_names)
    return {
        "delta_r2": actual["delta_r2"],
        "delta_dl_bits": dl,
        "R2_L2": actual["R2_L2"],
        "R2_L3": actual["R2_L3"],
        "p_within": p_ge(nulls[target_name]["within_gene"], dl),
        "p_matched": p_ge(nulls[target_name]["matched"], dl),
        "p_recoding": p_ge(nulls[target_name]["recoding"], dl),
        "null95_within": percentile_nearest_rank(nulls[target_name]["within_gene"], 0.95),
        "null95_matched": percentile_nearest_rank(nulls[target_name]["matched"], 0.95),
        "null95_recoding": percentile_nearest_rank(nulls[target_name]["recoding"], 0.95),
        "beta_b_sign": bsign["dominant"],
    }


def observed_target_summary(actual: dict[str, Any], q_names: list[str]) -> dict[str, Any]:
    bsign = sign_summary(actual["beta_b_by_fold"], q_names)
    return {
        "delta_r2": actual["delta_r2"],
        "delta_dl_bits": actual["delta_dl_bits"],
        "R2_L2": actual["R2_L2"],
        "R2_L3": actual["R2_L3"],
        "beta_b_sign": bsign["dominant"],
    }


def run_panel(rows: list[dict[str, Any]], q_names: list[str], include_efficiency: bool, want_secondary: bool) -> dict[str, Any]:
    controls = build_controls(rows, include_efficiency)
    folds = group_folds(rows, FOLD_COUNT)
    fold_cache = make_fold_cache(controls, folds)
    primary_targets = {"median_lfc": [float(r["median_lfc"]) for r in rows]}
    b = [list(map(float, r["delta_b"])) for r in rows]
    base_info = {name: control_predictions(target, fold_cache) for name, target in primary_targets.items()}
    base_preds = {name: item[0] for name, item in base_info.items()}
    base_betas = {name: item[1] for name, item in base_info.items()}
    target_cache = build_target_cache(primary_targets, fold_cache, base_betas)
    actual_all = evaluate_b_for_targets_fast(b, primary_targets, fold_cache, base_preds, target_cache)
    nulls = run_nulls(rows, b, primary_targets, fold_cache, base_preds, target_cache)
    summarized = {"median_lfc": summarize_actual(actual_all["median_lfc"], nulls, "median_lfc", q_names)}
    if want_secondary:
        secondary_targets = {"mean_score": [float(r["mean_score"]) for r in rows]}
        secondary_base_info = {name: control_predictions(target, fold_cache) for name, target in secondary_targets.items()}
        secondary_base_preds = {name: item[0] for name, item in secondary_base_info.items()}
        secondary_base_betas = {name: item[1] for name, item in secondary_base_info.items()}
        secondary_cache = build_target_cache(secondary_targets, fold_cache, secondary_base_betas)
        secondary_actual = evaluate_b_for_targets_fast(b, secondary_targets, fold_cache, secondary_base_preds, secondary_cache)
        summarized["mean_score"] = observed_target_summary(secondary_actual["mean_score"], q_names)
    return {
        "n": len(rows),
        "n_genes": len(set(r["gene"] for r in rows)),
        "fold_count": len(folds),
        "targets": summarized,
    }


def finite_row(row: dict[str, Any]) -> bool:
    required = [
        "median_lfc", "mean_score", "old_codon_freq", "new_codon_freq", "delta_freq",
        "delta_gc", "expression_tpm", "essentiality", "editing_efficiency_proxy", "delta_b",
    ]
    for key in required:
        if key not in row:
            return False
    for key in required[:-1]:
        try:
            value = float(row[key])
        except (TypeError, ValueError):
            return False
        if not math.isfinite(value):
            return False
    return isinstance(row["delta_b"], list) and len(row["delta_b"]) == 9


def analysis_sample(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for cell_line in sorted(set(str(r["cell_line"]) for r in rows)):
        subset = [r for r in rows if str(r["cell_line"]) == cell_line]
        ranked = sorted(
            subset,
            key=lambda r: stable_digest(f"{SEED}|analysis_sample|{cell_line}|{r['mutation_name']}"),
        )
        out.extend(ranked[:MAX_ANALYSIS_PER_CELL_LINE])
    return sorted(out, key=lambda r: (str(r["cell_line"]), str(r["gene"]), str(r["mutation_name"])))


def passed_all_nulls(row: dict[str, Any]) -> bool:
    return (
        row["delta_r2"] > 0.0
        and row["delta_dl_bits"] > row["null95_within"]
        and row["delta_dl_bits"] > row["null95_matched"]
        and row["delta_dl_bits"] > row["null95_recoding"]
    )


def stable_sign(per_cellline: dict[str, dict[str, Any]]) -> tuple[bool, dict[str, int]]:
    votes: dict[str, int] = {}
    signs = []
    for stat in per_cellline.values():
        dom = stat.get("beta_b_sign")
        if not dom:
            continue
        axis = str(dom["axis"])
        sign = 1 if float(dom["mean_beta"]) > 0 else -1 if float(dom["mean_beta"]) < 0 else 0
        signs.append(sign)
        votes[axis] = votes.get(axis, 0) + 1
    nonzero = [s for s in signs if s != 0]
    return bool(nonzero) and (all(s > 0 for s in nonzero) or all(s < 0 for s in nonzero)), votes


def main() -> None:
    t0 = time.time()
    repo = pathlib.Path.cwd()
    data_path = repo / DATA_REL
    checks = {
        "data_read": False,
        "synonymous_filtered": False,
        "delta_b_window": False,
        "controls_with_efficiency": False,
        "ladder_L2_L3_leavegeneout": False,
        "nulls_run": False,
        "per_cellline_replication": False,
        "verdict": False,
    }
    cannot_claim = [
        "human 非 yeast；这是跨物种 human prime-editor fitness 屏的弱复制检验，不是 Shen 酵母实验本身。",
        "无 mRNA 故不能测 beyond-mRNA escape(只 raw fitness), 不等价 Shen。",
        "prime-editing 效率重混淆(已控 proxy)：原始 feature/performance 表头未发现直接 editing-efficiency 列；使用 log1p(mean_ctrl) 作为装入/基线表示 proxy，并做加/不加 proxy 敏感性。",
        "editing-context/local-DNA 混淆：PE guide、RTT/PBS、局部序列和 DNA 修复上下文未完整建模。",
        "单 codon Δb 稀疏；不能外推到整基因或多位点 recoding。",
        "非 RQC；没有核糖体质量控制 readout。",
        "leave-gene-out 测试基因在训练折未出现，严格 gene fixed-effect dummy 无法对 held-out gene 估计；本脚本用 gene-block held-out 评估，并在 controls 中控制 codon family/old codon/cell-line 与数值协变量。",
    ]
    if not data_path.exists():
        result = {"missing": str(DATA_REL), "cannot_claim": cannot_claim, "actual_B": NULL_B, "runtime_sec": round(time.time() - t0, 3)}
        emit("needs_data", checks, "needs_data", result)
    payload = load_json(data_path)
    checks["data_read"] = True
    compact_rows = [r for r in payload.get("rows", []) if isinstance(r, dict) and finite_row(r)]
    rows = analysis_sample(compact_rows)
    checks["synonymous_filtered"] = bool(rows)
    checks["delta_b_window"] = bool(rows) and all(any(abs(float(v)) > EPS for v in r["delta_b"]) for r in rows)
    q_names = payload.get("q_names", [f"b{i}" for i in range(9)])
    q_names = [str(x) for x in q_names]
    if len(rows) < 500 or len(set(r["gene"] for r in rows)) < 25:
        result = {
            "n_synonymous": len(rows),
            "n_synonymous_compact": len(compact_rows),
            "n_genes": len(set(r.get("gene") for r in rows)),
            "cell_lines": sorted(set(str(r.get("cell_line")) for r in rows)),
            "actual_B": NULL_B,
            "runtime_sec": round(time.time() - t0, 3),
            "cannot_claim": cannot_claim,
        }
        emit("needs_data", checks, "needs_data", result)
    checks["controls_with_efficiency"] = bool(payload.get("editing_efficiency", {}).get("control_columns_used_as_proxy"))

    per_cellline: dict[str, dict[str, Any]] = {}
    secondary: dict[str, dict[str, Any]] = {}
    for cell_line in sorted(set(str(r["cell_line"]) for r in rows)):
        subset = [r for r in rows if str(r["cell_line"]) == cell_line]
        panel = run_panel(subset, q_names, include_efficiency=True, want_secondary=True)
        per_cellline[cell_line] = panel["targets"]["median_lfc"]
        secondary[cell_line] = panel["targets"]["mean_score"]

    pooled_panel = run_panel(rows, q_names, include_efficiency=True, want_secondary=True)
    pooled = pooled_panel["targets"]["median_lfc"]
    pooled_secondary = pooled_panel["targets"]["mean_score"]
    checks["ladder_L2_L3_leavegeneout"] = True
    checks["nulls_run"] = True

    # Sensitivity: no efficiency proxy, observed statistic only to check whether the
    # proxy control removes or reverses the apparent signal.
    sensitivity: dict[str, Any] = {}
    for label, subset in [("pooled", rows)] + [(cl, [r for r in rows if str(r["cell_line"]) == cl]) for cl in sorted(set(str(r["cell_line"]) for r in rows))]:
        controls = build_controls(subset, include_efficiency=False)
        folds = group_folds(subset, FOLD_COUNT)
        fold_cache = make_fold_cache(controls, folds)
        target = {"median_lfc": [float(r["median_lfc"]) for r in subset]}
        b = [list(map(float, r["delta_b"])) for r in subset]
        base_info = {name: control_predictions(vals, fold_cache) for name, vals in target.items()}
        base_preds = {name: item[0] for name, item in base_info.items()}
        base_betas = {name: item[1] for name, item in base_info.items()}
        target_cache = build_target_cache(target, fold_cache, base_betas)
        actual = evaluate_b_for_targets_fast(b, target, fold_cache, base_preds, target_cache)["median_lfc"]
        sensitivity[label] = {
            "without_efficiency_delta_r2": actual["delta_r2"],
            "without_efficiency_delta_dl_bits": actual["delta_dl_bits"],
            "with_efficiency_delta_r2": pooled["delta_r2"] if label == "pooled" else per_cellline[label]["delta_r2"],
            "with_efficiency_delta_dl_bits": pooled["delta_dl_bits"] if label == "pooled" else per_cellline[label]["delta_dl_bits"],
        }

    consistent = sum(1 for stat in per_cellline.values() if passed_all_nulls(stat))
    sign_ok, sign_votes = stable_sign(per_cellline)
    checks["per_cellline_replication"] = consistent >= 2 and sign_ok
    direct_eff = bool(payload.get("editing_efficiency", {}).get("direct_column_found"))
    if not direct_eff:
        verdict = "prime_editing_confounded_null"
    elif passed_all_nulls(pooled) and checks["per_cellline_replication"]:
        verdict = "human_synonymous_fitness_candidate"
    elif pooled["delta_dl_bits"] > 0 and (
        pooled["delta_dl_bits"] <= pooled["null95_matched"] or pooled["delta_dl_bits"] <= pooled["null95_recoding"]
    ):
        verdict = "composition_artifact"
    elif consistent < 2 or not passed_all_nulls(pooled):
        verdict = "prime_editing_confounded_null"
    else:
        verdict = "null"
    if pooled["delta_dl_bits"] <= 0 or not sign_ok:
        verdict = "null" if direct_eff else "prime_editing_confounded_null"
    checks["verdict"] = True

    result = {
        "n_synonymous": len(rows),
        "n_synonymous_compact": len(compact_rows),
        "max_analysis_per_cell_line": MAX_ANALYSIS_PER_CELL_LINE,
        "n_genes": len(set(r["gene"] for r in rows)),
        "cell_lines": sorted(set(str(r["cell_line"]) for r in rows)),
        "per_cellline": per_cellline,
        "secondary_mean_score": {"per_cellline": secondary, "pooled": pooled_secondary},
        "pooled": pooled,
        "efficiency_sensitivity": sensitivity,
        "actual_B": NULL_B,
        "runtime_sec": round(time.time() - t0, 3),
        "gene_control_note": "Held-out folds are gene-block folds. Direct gene dummy fixed effects are not included in the predictive held-out design because test genes are unseen in train folds.",
        "beta_b_sign": {"per_cellline_stable": sign_ok, "dominant_axis_votes": sign_votes, "pooled": pooled.get("beta_b_sign")},
        "cannot_claim": cannot_claim,
    }
    emit("passed", checks, verdict, result)


if __name__ == "__main__":
    main()

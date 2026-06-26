#!/usr/bin/env python3
"""Yang2024 E. coli endogenous synonymous-edit B_window fitness test.

纯 stdlib离线脚本：读 compact JSON，按 gene 留一 CV 评估
L2(y~C) vs L3(y~C+ΔB*_Q6_9D⊥)，控制 codon optimality 与编辑设计混淆，
并运行 within-gene/matched-bin/gene-guide-block 三类 null。
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import time


EXPERIMENT_ID = "b_star_window_yang_ecoli_endogenous_fitness_powered"
CLAIM_ID = "h3.cross_layer_relation.synonymous_perturbation.b_star_window_yang_ecoli_endogenous_fitness_powered"

REPO_JSON = pathlib.Path("tools/bio_reality/data/yang_ecoli_endogenous_synonymous.json")
TMP_JSON = pathlib.Path("/tmp/yang-exp/yang_ecoli_endogenous_synonymous.json")
NIEUWKOOP_LOG = pathlib.Path(
    "tools/bio_reality/state/writeback_codex_logs/"
    "namecert-h3.cross_layer_relation.synonymous_perturbation.b_star_window_nieuwkoop_ecoli_mrfp_protein_output_powered.raw.txt"
)

SEED = "sha256:b_star_window_yang_ecoli_endogenous_fitness_powered:deterministic"
NULL_B = 200
RIDGE = 1e-6
EPS = 1e-12
MAX_ROWS_PER_CONDITION = 360
MAX_ROWS_PER_GENE = 12

Q_NAMES = [
    "K_AAA", "Arg_AGR", "Ile_AUA", "Leu_CUN_vs_UUR", "Leu_UUA_vs_UUG",
    "Ser_UCR_vs_AGY", "Ser_UCA_vs_UCG", "Thr_ACR_vs_ACY", "f3_stress",
]

FROZEN_NIEUWKOOP_BETA: list[float] | None = None


def emit(status: str, checks: dict[str, object], verdict: str, result: dict[str, object], started: float) -> None:
    result["runtime_sec"] = round(time.time() - started, 3)
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


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(indices: list[int], material: str) -> list[int]:
    out = list(indices)
    for index in range(len(out) - 1, 0, -1):
        digest = stable_digest(f"{material}|i={index}|n={len(out)}")
        swap = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def deterministic_sample(indices: list[int], limit: int, material: str) -> list[int]:
    if len(indices) <= limit:
        return list(indices)
    return sorted(deterministic_permutation(indices, material)[:limit])


def deterministic_stratified_sample(
    rows: list[dict[str, object]],
    indices: list[int],
    max_total: int,
    max_per_gene: int,
    material: str,
) -> list[int]:
    groups: dict[str, list[int]] = {}
    for index in indices:
        groups.setdefault(str(rows[index]["gene"]), []).append(index)
    selected: list[int] = []
    for gene, gene_indices in sorted(groups.items()):
        take = min(max_per_gene, len(gene_indices))
        selected.extend(deterministic_sample(gene_indices, take, f"{material}|gene={gene}"))
    if len(selected) > max_total:
        selected = deterministic_sample(selected, max_total, f"{material}|cap")
    return sorted(selected)


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    center = mean(values)
    return sum((value - center) ** 2 for value in values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def p_value_greater_equal(null_values: list[float], actual: float) -> float:
    return (1 + sum(1 for value in null_values if value >= actual)) / (len(null_values) + 1)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def pearson(x: list[float], y: list[float]) -> float:
    if len(x) != len(y) or len(x) < 2:
        return 0.0
    mx = mean(x)
    my = mean(y)
    vx = sum((v - mx) ** 2 for v in x)
    vy = sum((v - my) ** 2 for v in y)
    if vx <= EPS or vy <= EPS:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(vx * vy)


def cholesky_decompose(matrix: list[list[float]]) -> list[list[float]]:
    n = len(matrix)
    lower = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            value = matrix[i][j] - sum(lower[i][k] * lower[j][k] for k in range(j))
            if i == j:
                if value <= EPS:
                    raise ValueError("matrix not positive definite")
                lower[i][j] = math.sqrt(value)
            else:
                lower[i][j] = value / lower[j][j]
    return lower


def cholesky_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    jitter = RIDGE
    for _attempt in range(10):
        adjusted = [list(row) for row in matrix]
        for i in range(n):
            adjusted[i][i] += jitter
        try:
            lower = cholesky_decompose(adjusted)
            y = [0.0 for _ in range(n)]
            for i in range(n):
                y[i] = (rhs[i] - sum(lower[i][k] * y[k] for k in range(i))) / lower[i][i]
            x = [0.0 for _ in range(n)]
            for i in range(n - 1, -1, -1):
                x[i] = (y[i] - sum(lower[k][i] * x[k] for k in range(i + 1, n))) / lower[i][i]
            return x
        except ValueError:
            jitter *= 10.0
    raise ValueError("Cholesky ridge solve failed")


def ridge_fit(x_rows: list[list[float]], y: list[float]) -> list[float]:
    if not x_rows:
        return []
    width = len(x_rows[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    rhs = [0.0 for _ in range(width)]
    for row, value in zip(x_rows, y):
        for i in range(width):
            rhs[i] += row[i] * value
            ri = row[i]
            for j in range(i, width):
                xtx[i][j] += ri * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    return cholesky_solve(xtx, rhs)


def predict_rows(x_rows: list[list[float]], beta: list[float]) -> list[float]:
    return [dot(row, beta) for row in x_rows]


def sse(y: list[float], pred: list[float]) -> float:
    return sum((actual - fitted) ** 2 for actual, fitted in zip(y, pred))


def tss(y: list[float]) -> float:
    center = mean(y)
    return max(EPS, sum((value - center) ** 2 for value in y))


def delta_r2(base_sse: float, full_sse: float, total_tss: float) -> float:
    return (base_sse - full_sse) / total_tss


def delta_ll(base_sse: float, full_sse: float, n: int, added_dim: int) -> float:
    improvement = 0.5 * n * math.log(max(base_sse, EPS) / max(full_sse, EPS))
    penalty = 0.5 * added_dim * math.log(max(n, 2))
    return improvement - penalty


def standardize_train_apply(
    matrix: list[list[float]],
    train: list[int],
    test: list[int],
) -> tuple[list[list[float]], list[list[float]]]:
    if not matrix or not matrix[0]:
        return [[] for _ in train], [[] for _ in test]
    width = len(matrix[0])
    stats: list[tuple[float, float]] = []
    for col in range(width):
        values = [matrix[index][col] for index in train]
        center = mean(values)
        sd = math.sqrt(variance(values))
        stats.append((center, sd if sd > EPS else 1.0))
    train_out = [[(matrix[index][col] - stats[col][0]) / stats[col][1] for col in range(width)] for index in train]
    test_out = [[(matrix[index][col] - stats[col][0]) / stats[col][1] for col in range(width)] for index in test]
    return train_out, test_out


def one_hot_maps(rows: list[dict[str, object]]) -> dict[str, list[str]]:
    return {
        "gene": sorted({str(row["gene"]) for row in rows}),
        "codon_family": sorted({str(row["codon_family"]) for row in rows}),
        "wild_type_codon": sorted({str(row["wild_type_codon"]) for row in rows}),
    }


def numeric(row: dict[str, object], key: str, default: float = 0.0) -> float:
    value = row.get(key)
    try:
        out = float(value)
    except (TypeError, ValueError):
        return default
    return out if math.isfinite(out) else default


def build_controls(rows: list[dict[str, object]], condition: str, maps: dict[str, list[str]]) -> list[list[float]]:
    controls: list[list[float]] = []
    gene_levels = maps["gene"]
    family_levels = maps["codon_family"]
    wt_levels = maps["wild_type_codon"]
    # Drop first level in each categorical group; intercept is added fold-wise.
    for row in rows:
        c_r2 = row.get("c_r2", {})
        c_r2_value = 0.0
        if isinstance(c_r2, dict):
            c_r2_value = numeric(c_r2, condition, 0.0)
        base = [
            numeric(row, "residue_norm"),
            numeric(row, "delta_cai"),
            numeric(row, "delta_tai_proxy"),
            numeric(row, "delta_gc"),
            numeric(row, "number_of_mutations"),
            numeric(row, "number_of_immunizing_mutations"),
            c_r2_value,
        ]
        gene = str(row["gene"])
        family = str(row["codon_family"])
        wt = str(row["wild_type_codon"])
        base.extend(1.0 if gene == level else 0.0 for level in gene_levels[1:])
        base.extend(1.0 if family == level else 0.0 for level in family_levels[1:])
        base.extend(1.0 if wt == level else 0.0 for level in wt_levels[1:])
        controls.append(base)
    return controls


def make_leave_gene_folds(rows: list[dict[str, object]], controls: list[list[float]]) -> list[dict[str, object]]:
    genes = sorted({str(row["gene"]) for row in rows})
    folds: list[dict[str, object]] = []
    indices = list(range(len(rows)))
    for gene in genes:
        test = [index for index, row in enumerate(rows) if str(row["gene"]) == gene]
        test_set = set(test)
        train = [index for index in indices if index not in test_set]
        if not train or not test:
            continue
        c_train_raw, c_test_raw = standardize_train_apply(controls, train, test)
        folds.append({
            "gene": gene,
            "train": train,
            "test": test,
            "c_train": [[1.0] + row for row in c_train_raw],
            "c_test": [[1.0] + row for row in c_test_raw],
        })
    return folds


def fit_controls_and_residual_b(
    y: list[float],
    b_matrix: list[list[float]],
    folds: list[dict[str, object]],
) -> dict[str, object]:
    n = len(y)
    base_preds = [0.0 for _ in range(n)]
    for fold in folds:
        train = fold["train"]
        test = fold["test"]
        c_train = fold["c_train"]
        c_test = fold["c_test"]
        if not isinstance(train, list) or not isinstance(test, list) or not isinstance(c_train, list) or not isinstance(c_test, list):
            raise ValueError("bad fold")
        beta_y = ridge_fit(c_train, [y[index] for index in train])
        pred_train_y = predict_rows(c_train, beta_y)
        pred = predict_rows(c_test, beta_y)
        fold["y_train_resid"] = [y[index] - pred_train_y[local] for local, index in enumerate(train)]
        for local, index in enumerate(test):
            base_preds[index] = pred[local]
        raw_resid = [[0.0 for _ in range(len(Q_NAMES))] for _ in range(n)]
        for col in range(len(Q_NAMES)):
            beta_b = ridge_fit(c_train, [b_matrix[index][col] for index in train])
            pred_train = predict_rows(c_train, beta_b)
            pred_test = predict_rows(c_test, beta_b)
            for local, index in enumerate(train):
                raw_resid[index][col] = b_matrix[index][col] - pred_train[local]
            for local, index in enumerate(test):
                raw_resid[index][col] = b_matrix[index][col] - pred_test[local]
        train_std, test_std = standardize_train_apply(raw_resid, train, test)
        b_by_index = [[0.0 for _ in range(len(Q_NAMES))] for _ in range(n)]
        for local, index in enumerate(train):
            b_by_index[index] = train_std[local]
        for local, index in enumerate(test):
            b_by_index[index] = test_std[local]
        fold["b_by_index"] = b_by_index
    return {"base_preds": base_preds}


def evaluate_incremental(
    y: list[float],
    folds: list[dict[str, object]],
    base_preds: list[float],
    source_map: list[int] | None = None,
    direction: list[float] | None = None,
    added_dim: int = 9,
) -> dict[str, object]:
    preds = [0.0 for _ in y]
    beta_b_by_fold: list[list[float]] = []
    contribution_cor: list[float] = []
    if source_map is None:
        source_map = list(range(len(y)))
    for fold in folds:
        train = fold["train"]
        test = fold["test"]
        b_by_index = fold.get("b_by_index")
        y_train_resid = fold.get("y_train_resid")
        if not isinstance(train, list) or not isinstance(test, list) or not isinstance(b_by_index, list) or not isinstance(y_train_resid, list):
            raise ValueError("bad fold")
        if direction is None:
            x_train = [b_by_index[source_map[index]] for index in train]
            x_test = [b_by_index[source_map[index]] for index in test]
        else:
            x_train = [[dot(b_by_index[source_map[index]], direction)] for index in train]
            x_test = [[dot(b_by_index[source_map[index]], direction)] for index in test]
        beta_b = ridge_fit(x_train, y_train_resid)
        beta_b_by_fold.append(beta_b)
        pred_delta = predict_rows(x_test, beta_b)
        contrib = predict_rows(x_test, beta_b)
        contribution_cor.append(pearson(contrib, [y[index] for index in test]))
        for local, index in enumerate(test):
            preds[index] = base_preds[index] + pred_delta[local]
    base = sse(y, base_preds)
    full = sse(y, preds)
    total = tss(y)
    return {
        "preds": preds,
        "base_sse": base,
        "full_sse": full,
        "delta_r2": delta_r2(base, full, total),
        "delta_ll": delta_ll(base, full, len(y), added_dim),
        "beta_b_by_fold": beta_b_by_fold,
        "fold_contribution_cor": contribution_cor,
    }


def evaluate_projection(
    y: list[float],
    direction: list[float],
    folds: list[dict[str, object]],
    base_preds: list[float],
    source_map: list[int] | None = None,
) -> dict[str, float]:
    out = evaluate_incremental(y, folds, base_preds, source_map=source_map, direction=direction, added_dim=1)
    return {"delta_r2": float(out["delta_r2"]), "delta_ll": float(out["delta_ll"])}


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    ordered = sorted(values)
    cuts = []
    for i in range(1, bins):
        cuts.append(ordered[max(0, min(len(ordered) - 1, math.ceil(len(ordered) * i / bins) - 1))])
    return cuts


def bin_index(value: float, cuts: list[float]) -> int:
    out = 0
    while out < len(cuts) and value > cuts[out]:
        out += 1
    return out


def shuffle_within_gene(rows: list[dict[str, object]], trial: int) -> list[int]:
    out = list(range(len(rows)))
    groups: dict[str, list[int]] = {}
    for index, row in enumerate(rows):
        groups.setdefault(str(row["gene"]), []).append(index)
    for gene, indices in sorted(groups.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|within-gene|trial={trial}|gene={gene}")
        for dest, src in zip(indices, permuted):
            out[dest] = src
    return out


def shuffle_matched_bins(rows: list[dict[str, object]], trial: int) -> list[int]:
    delta_cai = [numeric(row, "delta_cai") for row in rows]
    delta_tai = [numeric(row, "delta_tai_proxy") for row in rows]
    delta_gc = [numeric(row, "delta_gc") for row in rows]
    num_mut = [numeric(row, "number_of_mutations") for row in rows]
    cai_cuts = quantile_cuts(delta_cai, 3)
    tai_cuts = quantile_cuts(delta_tai, 3)
    gc_cuts = quantile_cuts(delta_gc, 3)
    mut_cuts = quantile_cuts(num_mut, 3)
    groups: dict[tuple[int, int, int, int, str], list[int]] = {}
    for index, row in enumerate(rows):
        key = (
            bin_index(delta_cai[index], cai_cuts),
            bin_index(delta_tai[index], tai_cuts),
            bin_index(delta_gc[index], gc_cuts),
            bin_index(num_mut[index], mut_cuts),
            str(row["gene"]),
        )
        groups.setdefault(key, []).append(index)
    out = list(range(len(rows)))
    for key, indices in sorted(groups.items()):
        if len(indices) < 2:
            continue
        permuted = deterministic_permutation(indices, f"{SEED}|matched|trial={trial}|bin={key}")
        for dest, src in zip(indices, permuted):
            out[dest] = src
    return out


def shuffle_block(rows: list[dict[str, object]], trial: int) -> list[int]:
    blocks: dict[str, list[int]] = {}
    gene_blocks: dict[str, list[str]] = {}
    for index, row in enumerate(rows):
        block = str(row["block_id"])
        gene = str(row["gene"])
        blocks.setdefault(block, []).append(index)
        gene_blocks.setdefault(gene, [])
        if block not in gene_blocks[gene]:
            gene_blocks[gene].append(block)
    out = list(range(len(rows)))
    for gene, block_ids in sorted(gene_blocks.items()):
        if len(block_ids) < 2:
            continue
        permuted = deterministic_permutation(block_ids, f"{SEED}|block|trial={trial}|gene={gene}")
        for dest_block, src_block in zip(block_ids, permuted):
            src_indices = blocks[src_block]
            dest_indices = blocks[dest_block]
            src_cycle = deterministic_permutation(src_indices, f"{SEED}|block-src|trial={trial}|src={src_block}|dest={dest_block}")
            for local, dest in enumerate(dest_indices):
                out[dest] = src_cycle[local % len(src_cycle)]
    return out


def summarize_sign(beta_b_by_fold: list[list[float]], contribution_cor: list[float]) -> dict[str, object]:
    dimensions = []
    stable_dims = []
    if beta_b_by_fold:
        for col, name in enumerate(Q_NAMES):
            values = [row[col] for row in beta_b_by_fold]
            pos = sum(1 for value in values if value > 1e-10)
            neg = sum(1 for value in values if value < -1e-10)
            avg = mean(values)
            sign = "+" if avg > 1e-10 else ("-" if avg < -1e-10 else "0")
            stable = max(pos, neg) >= max(1, math.ceil(0.75 * len(values))) and sign != "0"
            if stable:
                stable_dims.append(name)
            dimensions.append({"name": name, "mean_beta": avg, "sign": sign, "fold_pos": pos, "fold_neg": neg, "stable": stable})
    cpos = sum(1 for value in contribution_cor if value > 1e-10)
    cneg = sum(1 for value in contribution_cor if value < -1e-10)
    cmean = mean(contribution_cor)
    stable_threshold = max(1, math.ceil(0.75 * len(contribution_cor)))
    return {
        "dimensions": dimensions,
        "stable_dimensions": stable_dims,
        "fold_contribution_correlations": contribution_cor,
        "aggregate_direction": "+" if cmean > 1e-10 else ("-" if cmean < -1e-10 else "0"),
        "aggregate_stable": max(cpos, cneg) >= stable_threshold and abs(cmean) > 1e-10,
        "sign_stable": bool(stable_dims) and max(cpos, cneg) >= stable_threshold and abs(cmean) > 1e-10,
    }


def run_condition(rows_all: list[dict[str, object]], condition: str, maps: dict[str, list[str]]) -> dict[str, object]:
    available = [index for index, row in enumerate(rows_all) if isinstance(row.get("conditions"), dict) and condition in row["conditions"]]
    selected = deterministic_stratified_sample(
        rows_all,
        available,
        MAX_ROWS_PER_CONDITION,
        MAX_ROWS_PER_GENE,
        f"{SEED}|subsample|{condition}",
    )
    rows = [rows_all[index] for index in selected]
    y = [numeric(row["conditions"], condition) for row in rows]  # type: ignore[arg-type]
    b_matrix = [list(map(float, row["delta_b9"])) for row in rows]  # type: ignore[arg-type]
    controls = build_controls(rows, condition, maps)
    folds = make_leave_gene_folds(rows, controls)
    fitted = fit_controls_and_residual_b(y, b_matrix, folds)
    base_preds = fitted["base_preds"]
    if not isinstance(base_preds, list):
        raise ValueError("bad fit")
    actual = evaluate_incremental(y, folds, base_preds)
    base_r2 = 1.0 - float(actual["base_sse"]) / tss(y)
    full_r2 = 1.0 - float(actual["full_sse"]) / tss(y)
    beta_sign = summarize_sign(actual["beta_b_by_fold"], actual["fold_contribution_cor"])  # type: ignore[arg-type]
    nulls = {"within_gene": [], "matched_bin": [], "block": []}
    null_r2 = {"within_gene": [], "matched_bin": [], "block": []}
    for trial in range(NULL_B):
        for name, matrix in (
            ("within_gene", shuffle_within_gene(rows, trial)),
            ("matched_bin", shuffle_matched_bins(rows, trial)),
            ("block", shuffle_block(rows, trial)),
        ):
            result = evaluate_incremental(y, folds, base_preds, source_map=matrix)
            nulls[name].append(float(result["delta_ll"]))
            null_r2[name].append(float(result["delta_r2"]))
    actual_ll = float(actual["delta_ll"])
    pvals = {name: p_value_greater_equal(values, actual_ll) for name, values in nulls.items()}
    null95 = {name: percentile_nearest_rank(values, 0.95) for name, values in nulls.items()}
    null95_r2 = {name: percentile_nearest_rank(values, 0.95) for name, values in null_r2.items()}
    transfer = None
    if FROZEN_NIEUWKOOP_BETA is not None:
        proj_actual = evaluate_projection(y, FROZEN_NIEUWKOOP_BETA, folds, base_preds)
        proj_null = []
        for trial in range(NULL_B):
            matrix = shuffle_block(rows, trial)
            proj_null.append(evaluate_projection(y, FROZEN_NIEUWKOOP_BETA, folds, base_preds, source_map=matrix)["delta_ll"])
        transfer = {
            "delta_r2": proj_actual["delta_r2"],
            "delta_ll": proj_actual["delta_ll"],
            "proj_p": p_value_greater_equal(proj_null, proj_actual["delta_ll"]),
            "null": "block permutation using frozen Nieuwkoop beta direction; Yang fits only scalar scale",
        }
    return {
        "condition": condition,
        "n": len(rows),
        "subsampled_from": len(available),
        "subsample_rule": f"deterministic stratified sample up to {MAX_ROWS_PER_GENE} synonymous edits per gene, capped at {MAX_ROWS_PER_CONDITION} rows per condition",
        "n_genes": len({row["gene"] for row in rows}),
        "fold_sizes": [len(fold["test"]) for fold in folds],
        "base_r2": base_r2,
        "full_r2": full_r2,
        "delta_r2": float(actual["delta_r2"]),
        "delta_ll": actual_ll,
        "p_within_gene": pvals["within_gene"],
        "p_matched_bin": pvals["matched_bin"],
        "p_block": pvals["block"],
        "null95": null95,
        "null95_delta_r2": null95_r2,
        "beta_b_sign": beta_sign,
        "transfer": transfer,
    }


def load_data() -> tuple[dict[str, object], pathlib.Path]:
    path = REPO_JSON if REPO_JSON.exists() else TMP_JSON
    return json.loads(path.read_text(encoding="utf-8")), path


def load_transfer_status() -> dict[str, object] | None:
    if FROZEN_NIEUWKOOP_BETA is not None:
        return {"source": "embedded_frozen_beta", "beta": FROZEN_NIEUWKOOP_BETA, "proj_p": None}
    if NIEUWKOOP_LOG.exists():
        return {
            "source": str(NIEUWKOOP_LOG),
            "proj_p": None,
            "skipped": "Nieuwkoop parsed/raw logs available only as scalar chapter summary; no reusable 9D beta vector found without rerunning/relearning.",
        }
    return {"proj_p": None, "skipped": "Nieuwkoop 9D beta vector unavailable; transfer skipped per protocol."}


def verdict_from_conditions(per_condition: dict[str, dict[str, object]]) -> tuple[str, str]:
    positives = []
    confounded = []
    for condition, result in per_condition.items():
        delta_ll_value = float(result["delta_ll"])
        delta_r2_value = float(result["delta_r2"])
        sign = result["beta_b_sign"]
        if not isinstance(sign, dict):
            continue
        pass_all = (
            delta_ll_value > 0.0
            and delta_r2_value > 0.0
            and bool(sign.get("sign_stable"))
            and delta_ll_value > max(float(v) for v in result["null95"].values())  # type: ignore[union-attr]
            and float(result["p_within_gene"]) <= 0.05
            and float(result["p_matched_bin"]) <= 0.05
            and float(result["p_block"]) <= 0.05
        )
        if pass_all:
            positives.append(condition)
        elif delta_ll_value > 0.0 and float(result["p_block"]) > 0.05:
            confounded.append(condition)
    if positives and len(positives) == len(per_condition):
        return "endogenous_fitness_escape_candidate", "passed"
    if positives:
        return "condition_specific", "passed"
    if confounded:
        return "edit_design_confounded_null", "passed"
    return "null", "passed"


def main() -> None:
    started = time.time()
    checks: dict[str, object] = {
        "data_parsed": False,
        "synonymous_filtered": False,
        "delta_b_window": False,
        "controls_with_editdesign": False,
        "ladder_L2_L3_leavegeneout": False,
        "nulls_run": False,
        "transfer_or_na": False,
        "endogenous_fitness_verdict": False,
    }
    try:
        payload, data_path = load_data()
        rows_all = payload.get("rows", [])
        if not isinstance(rows_all, list) or not rows_all:
            emit("needs_data", checks, "null", {
                "n_synonymous_edits": 0,
                "n_genes": 0,
                "conditions": [],
                "actual_B": 0,
                "per_condition": {},
                "transfer_nieuwkoop": {"proj_p": None, "skipped": "compact JSON missing rows"},
                "beta_b_sign": {},
                "cannot_claim": ["compact JSON 缺行，无法运行。"],
            }, started)
        conditions = list(payload.get("source", {}).get("conditions", {}).values()) if isinstance(payload.get("source"), dict) else []
        if not conditions:
            condition_set = set()
            for row in rows_all:
                if isinstance(row, dict) and isinstance(row.get("conditions"), dict):
                    condition_set.update(row["conditions"].keys())
            conditions = sorted(condition_set)
        maps = one_hot_maps(rows_all)  # type: ignore[arg-type]
        checks["data_parsed"] = {"passed": True, "path": str(data_path), "n_rows": len(rows_all)}
        checks["synonymous_filtered"] = {
            "passed": True,
            "definition": "compact prep retained rows where standard genetic code maps Target codon and Mutated codon to same non-stop amino acid and Target aa agrees with Target codon",
            "n_synonymous_edits": len(rows_all),
            "n_genes": len({row["gene"] for row in rows_all if isinstance(row, dict)}),
        }
        checks["delta_b_window"] = {
            "passed": True,
            "q_names": Q_NAMES,
            "definition": "Δb = B*_Q6_9D(Mutated local seq) - B*_Q6_9D(Target local seq), using sibling aa-fiber-centered projected codon-count coordinates",
            "local_not_whole_gene": True,
        }
        checks["controls_with_editdesign"] = {
            "passed": True,
            "controls": [
                "Gene fixed effect", "Residue position normalized", "codon-family",
                "ΔCAI true E.coli genome", "ΔtAI proxy", "ΔGC", "WildTypeCodon identity",
                "NumberofMutations", "NumberOfImmunizingMutations", "c_r2_mean measurement quality",
            ],
            "tai_note": "proxy: genome RSCU weighted by GC3-ending availability; no tRNA copy/wobble table",
            "edit_design": "NumberofMutations and NumberOfImmunizingMutations are included in C before Δb residualization.",
        }
        per_condition: dict[str, dict[str, object]] = {}
        transfer_best = load_transfer_status()
        for condition in conditions:
            per_condition[condition] = run_condition(rows_all, condition, maps)  # type: ignore[arg-type]
            if per_condition[condition].get("transfer") is not None:
                transfer_best = per_condition[condition]["transfer"]  # type: ignore[assignment]
        checks["ladder_L2_L3_leavegeneout"] = {
            "passed": True,
            "folding": "leave-gene-out; each held-out fold is an entire gene",
            "residualization": "Δb⊥ = Δb - Ê[Δb|C] fit on train fold and applied to held-out gene",
            "conditions": {condition: {"delta_r2": result["delta_r2"], "delta_ll": result["delta_ll"]} for condition, result in per_condition.items()},
        }
        checks["nulls_run"] = {
            "passed": True,
            "actual_B": NULL_B,
            "nulls": [
                "within-gene shuffle Δb⊥",
                "matched ΔCAI/ΔtAI/ΔGC/NumMutations bin shuffle within gene",
                "gene/guide block permutation using Gene|Residue|ImmunizingMutations|NumMutations|NumImmunizing block_id",
            ],
        }
        checks["transfer_or_na"] = {
            "passed": True,
            "transfer_nieuwkoop": transfer_best,
            "anti_post_hoc": "transfer uses frozen Nieuwkoop direction only if a 9D beta vector is available; otherwise skipped rather than fitting a Yang direction for transfer",
        }
        verdict, status = verdict_from_conditions(per_condition)
        checks["endogenous_fitness_verdict"] = {
            "passed": True,
            "rule": "candidate requires ΔLL>0, ΔR²>0, stable sign, and actual ΔLL above all three null95 with p<=0.05; condition_specific if only a subset passes; edit_design_confounded_null if apparent signal fails block permutation.",
            "verdict": verdict,
        }
        aggregate_sign = {
            condition: result["beta_b_sign"]
            for condition, result in per_condition.items()
        }
        cannot_claim = [
            "编辑多是 PAM/immunizing cluster 非单 codon 因果；已控 NumberofMutations/NumberOfImmunizingMutations 但不完整。",
            "editing-efficiency 混淆未直接测量，不能声称完全排除编辑效率影响。",
            "E.coli 非真核；不能外推到 yeast/human 真核同义调控。",
            "内源但 fitness 多因素；competition coefficient 不是单一翻译或蛋白输出 readout。",
            "Δb 在 local Target/Mutated seq 上计算，不是全基因 CDS ΔB。",
            "真 RNA MFE 未控：本脚本纯 stdlib，无 RNA 热力学模型。",
            "tAI 为 genome RSCU+GC3 proxy，不是真实 E.coli tRNA/wobble 模型。",
        ]
        result = {
            "n_synonymous_edits": len(rows_all),
            "n_genes": len({row["gene"] for row in rows_all if isinstance(row, dict)}),
            "conditions": conditions,
            "actual_B": NULL_B,
            "per_condition": {
                condition: {
                    "delta_r2": value["delta_r2"],
                    "delta_ll": value["delta_ll"],
                    "p_block": value["p_block"],
                    "p_within_gene": value["p_within_gene"],
                    "p_matched_bin": value["p_matched_bin"],
                    "n": value["n"],
                    "n_genes": value["n_genes"],
                    "base_r2": value["base_r2"],
                    "full_r2": value["full_r2"],
                    "null95": value["null95"],
                }
                for condition, value in per_condition.items()
            },
            "transfer_nieuwkoop": transfer_best,
            "beta_b_sign": aggregate_sign,
            "cannot_claim": cannot_claim,
        }
        emit(status, checks, verdict, result, started)
    except Exception as exc:
        emit("failed", checks, "null", {
            "n_synonymous_edits": 0,
            "n_genes": 0,
            "conditions": [],
            "actual_B": 0,
            "per_condition": {},
            "transfer_nieuwkoop": {"proj_p": None},
            "beta_b_sign": {},
            "cannot_claim": [f"脚本异常: {exc}"],
        }, started)


if __name__ == "__main__":
    main()

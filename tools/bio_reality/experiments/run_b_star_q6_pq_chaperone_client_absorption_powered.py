#!/usr/bin/env python3
"""Chaperone-client membership absorption test for the yeast B*_Q6 residual U."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from typing import Any

import run_b_star_q6_pq_proteostasis_mismatch_absorption_powered as proteostasis
from run_b_star_q6_translation_complement_residual_powered import vector_norm2


EXPERIMENT_ID = "b_star_q6_pq_chaperone_client_absorption_powered"
CLAIM_ID = "h3.cross_layer_relation.chaperone_client.b_star_q6_pq_chaperone_client_absorption_powered"

ORGANISM_KEY = "saccharomyces_cerevisiae"
DATA_PATH = "tools/bio_reality/data/chaperone_client_gong2009_saccharomyces_cerevisiae.json"
B = 200
FOLDS = 5
SEED = 138451
EPS = 1e-12
RIDGE = 1e-6
BASE_R2_QP_MIN = 0.25
BASE_R2_QP_MAX = 0.34
MIN_JOIN_N = 800
CROSS_HELDOUT_DELTA_R2 = 0.01
ABUNDANCE_BINS = 10
LENGTH_BINS = 10


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def strip_4932(identifier: str) -> str:
    return identifier.split(".", 1)[1] if identifier.startswith("4932.") else identifier


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = hashlib.sha256(f"{material}|seed={SEED}|index={index}|n={n}".encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def sse(values: list[float], pred: list[float]) -> float:
    return sum((value - fit) * (value - fit) for value, fit in zip(values, pred))


def r2_from_predictions(values: list[float], pred: list[float]) -> float:
    center = mean(values)
    total = sum((value - center) * (value - center) for value in values)
    if total <= EPS:
        return 0.0
    return 1.0 - sse(values, pred) / total


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = 1e-12) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            aug[pivot][col] = tol
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for item in range(col, n + 1):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(col, n + 1):
                aug[row][item] -= factor * aug[col][item]
    return [aug[row][n] for row in range(n)]


def fit_sparse_binary_ridge(
    feature_rows: list[list[int]],
    y_values: list[float],
    train_indices: list[int],
    width: int,
) -> list[float]:
    cols = width + 1
    gram = [[0.0 for _ in range(cols)] for _ in range(cols)]
    rhs = [0.0 for _ in range(cols)]
    for index in train_indices:
        active = feature_rows[index]
        y_value = y_values[index]
        gram[0][0] += 1.0
        rhs[0] += y_value
        for feature in active:
            col = feature + 1
            gram[0][col] += 1.0
            gram[col][0] += 1.0
            rhs[col] += y_value
        for left in active:
            left_col = left + 1
            for right in active:
                gram[left_col][right + 1] += 1.0
    gram[0][0] += RIDGE * 1e-3
    for col in range(1, cols):
        gram[col][col] += RIDGE
    return solve_linear_system(gram, rhs)


def predict_sparse_binary(coeff: list[float], feature_rows: list[list[int]], indices: list[int]) -> list[float]:
    out: list[float] = []
    for index in indices:
        value = coeff[0]
        for feature in feature_rows[index]:
            value += coeff[feature + 1]
        out.append(value)
    return out


def fold_indices(n: int) -> list[tuple[list[int], list[int]]]:
    order = deterministic_permutation(n, f"{EXPERIMENT_ID}|heldout-folds")
    folds = []
    for fold in range(FOLDS):
        test = [index for position, index in enumerate(order) if position % FOLDS == fold]
        train = [index for position, index in enumerate(order) if position % FOLDS != fold]
        folds.append((train, test))
    return folds


def heldout_delta_r2_sparse(feature_rows: list[list[int]], y_values: list[float], width: int) -> dict[str, object]:
    folds = fold_indices(len(y_values))
    model_pred = [0.0 for _ in y_values]
    baseline_pred = [0.0 for _ in y_values]
    for train, test in folds:
        coeff = fit_sparse_binary_ridge(feature_rows, y_values, train, width)
        pred = predict_sparse_binary(coeff, feature_rows, test)
        train_mean = mean([y_values[index] for index in train])
        for index, value in zip(test, pred):
            model_pred[index] = value
            baseline_pred[index] = train_mean
    center = mean(y_values)
    total = sum((value - center) * (value - center) for value in y_values)
    delta = 0.0 if total <= EPS else (sse(y_values, baseline_pred) - sse(y_values, model_pred)) / total
    y_norm2 = vector_norm2(y_values)
    pred_norm2 = vector_norm2(model_pred)
    return {
        "heldout_delta_r2": delta,
        "heldout_model_r2": r2_from_predictions(y_values, model_pred),
        "heldout_baseline_r2": r2_from_predictions(y_values, baseline_pred),
        "cross_fitted_prediction_energy_ratio": pred_norm2 / y_norm2 if y_norm2 > EPS else 0.0,
        "folds": [{"train_n": len(train), "test_n": len(test)} for train, test in folds],
    }


def dense_binary_rows(feature_rows: list[list[int]], width: int) -> list[list[float]]:
    out: list[list[float]] = []
    for active in feature_rows:
        row = [0.0 for _ in range(width)]
        for index in active:
            row[index] = 1.0
        out.append(row)
    return out


def bin_assignments(values: list[float], bin_count: int) -> list[int]:
    ordered = sorted(range(len(values)), key=lambda index: (values[index], index))
    out = [0 for _ in values]
    n = len(values)
    for rank, index in enumerate(ordered):
        out[index] = min(bin_count - 1, (rank * bin_count) // n) if n else 0
    return out


def groups_for_rows(rows: list[dict[str, object]]) -> tuple[list[list[int]], dict[str, object]]:
    abundance = [float(row["abundance_log10"]) for row in rows]
    length = [float(row["protein_length_aa_proxy"]) for row in rows]
    abundance_bin = bin_assignments(abundance, ABUNDANCE_BINS)
    length_bin = bin_assignments(length, LENGTH_BINS)
    grouped: dict[tuple[int, int], list[int]] = defaultdict(list)
    for index in range(len(rows)):
        grouped[(abundance_bin[index], length_bin[index])].append(index)
    groups = [grouped[key] for key in sorted(grouped)]
    sizes = sorted(len(group) for group in groups)
    movable = sum(size for size in sizes if size >= 2)
    return groups, {
        "matched_axes": ["protein_abundance_decile", "protein_length_decile"],
        "abundance_bins": ABUNDANCE_BINS,
        "length_bins": LENGTH_BINS,
        "strata_n": len(groups),
        "singleton_strata_n": sum(1 for size in sizes if size == 1),
        "movable_rows_n": movable,
        "movable_rows_fraction": movable / len(rows) if rows else 0.0,
        "min_stratum_size": sizes[0] if sizes else 0,
        "median_stratum_size": sizes[len(sizes) // 2] if sizes else 0,
        "max_stratum_size": sizes[-1] if sizes else 0,
    }


def permute_feature_rows(feature_rows: list[list[int]], groups: list[list[int]], trial: int) -> list[list[int]]:
    out = [list(row) for row in feature_rows]
    for group_index, positions in enumerate(groups):
        if len(positions) < 2:
            continue
        order = deterministic_permutation(len(positions), f"{EXPERIMENT_ID}|matched-null|trial={trial}|group={group_index}")
        for dest_local, src_local in enumerate(order):
            out[positions[dest_local]] = list(feature_rows[positions[src_local]])
    return out


def matched_permutation_null(
    feature_rows: list[list[int]],
    target: list[float],
    width: int,
    groups: list[list[int]],
) -> dict[str, object]:
    values: list[float] = []
    for trial in range(B):
        permuted = permute_feature_rows(feature_rows, groups, trial)
        cv = heldout_delta_r2_sparse(permuted, target, width)
        values.append(float(cv["heldout_delta_r2"]))
    return {
        "B": B,
        "values": values,
        "null95": percentile_nearest_rank(values, 0.95),
        "null_mean": mean(values),
        "null_max": max(values) if values else 0.0,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|seed={SEED}|matched-null",
    }


def load_chaperone_payload(repo: pathlib.Path) -> tuple[list[str], dict[str, list[str]], dict[str, object]]:
    payload = load_json(repo / DATA_PATH)
    if not isinstance(payload, dict):
        raise ValueError(f"{DATA_PATH} must contain an object")
    chaperones = payload.get("chaperone_orfs")
    clients = payload.get("client_chaperones")
    meta = payload.get("meta")
    if not isinstance(chaperones, list) or not all(isinstance(item, str) and item for item in chaperones):
        raise ValueError(f"{DATA_PATH} chaperone_orfs must be a nonempty string list")
    if not isinstance(clients, dict):
        raise ValueError(f"{DATA_PATH} client_chaperones must be an object")
    out_clients: dict[str, list[str]] = {}
    skipped = Counter()
    chaperone_set = set(chaperones)
    raw_interactions = 0
    for client, values in clients.items():
        if not isinstance(client, str) or not isinstance(values, list):
            skipped["malformed_client_record"] += 1
            continue
        raw_interactions += len(values)
        kept = []
        for value in values:
            if isinstance(value, str) and value in chaperone_set:
                kept.append(value)
            else:
                skipped["unknown_chaperone_reference"] += 1
        out_clients[client] = sorted(set(kept))
    summary = {
        "path": DATA_PATH,
        "n_chaperones": len(chaperones),
        "n_client_orfs": len(out_clients),
        "raw_n_interactions": raw_interactions,
        "n_binary_memberships": sum(len(values) for values in out_clients.values()),
        "source_meta": meta if isinstance(meta, dict) else {},
        "skipped": dict(sorted(skipped.items())),
    }
    return list(chaperones), out_clients, summary


def build_chaperone_rows(
    *,
    reconstructed: dict[str, object],
    chaperones: list[str],
    client_chaperones: dict[str, list[str]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    rows = reconstructed.get("rows")
    row_ids = reconstructed.get("row_ids")
    p_q = reconstructed.get("p_q")
    u = reconstructed.get("u")
    if not isinstance(rows, dict) or not isinstance(row_ids, list) or not isinstance(p_q, list) or not isinstance(u, list):
        raise ValueError("reconstructed U payload malformed")
    chaperone_index = {chaperone: index for index, chaperone in enumerate(chaperones)}
    out: list[dict[str, object]] = []
    missing = Counter()
    n_client_join = 0
    joined_interactions = 0
    for index, protein_id_obj in enumerate(row_ids):
        protein_id = str(protein_id_obj)
        gene_id = strip_4932(protein_id)
        compression_row = rows.get(protein_id)
        if not isinstance(compression_row, dict):
            missing["compression_row"] += 1
            continue
        abundance_values = compression_row.get("p")
        z_values = compression_row.get("z")
        if not isinstance(abundance_values, list) or not abundance_values or not finite_number(abundance_values[0]):
            missing["protein_abundance"] += 1
            continue
        if not isinstance(z_values, list) or len(z_values) < 2 or not finite_number(z_values[1]):
            missing["protein_length"] += 1
            continue
        clients = client_chaperones.get(gene_id)
        active: list[int] = []
        if isinstance(clients, list):
            n_client_join += 1
            active = sorted(chaperone_index[chaperone] for chaperone in clients if chaperone in chaperone_index)
            joined_interactions += len(active)
        log_cds_len_nt = float(z_values[1])
        out.append(
            {
                "gene_id": gene_id,
                "protein_id": protein_id,
                "u": float(u[index]),
                "p_q": float(p_q[index]),
                "active_indices": active,
                "degree": len(active),
                "abundance_log10": float(abundance_values[0]),
                "protein_length_aa_proxy": math.exp(log_cds_len_nt) / 3.0,
                "log_cds_len_nt": log_cds_len_nt,
                "in_gong2009_client_atlas": isinstance(clients, list),
            }
        )
    degree_values = [int(row["degree"]) for row in out]
    joined_degree_values = [int(row["degree"]) for row in out if row["in_gong2009_client_atlas"]]
    summary = {
        "active_dictionary_u_gene_set_n": len(row_ids),
        "analysis_n": len(out),
        "n_join": n_client_join,
        "joined_interactions_on_analysis_rows": joined_interactions,
        "atlas_missing_rows_encoded_as_zero": len(out) - n_client_join,
        "feature_width": len(chaperones),
        "feature_definition": "64 binary columns C_{g,m}; C=1 when yeast gene g appears as a Gong2009 client of chaperone m; active dictionary rows absent from the atlas are retained as all-zero rows",
        "degree_summary": {
            "mean_all_rows": mean([float(value) for value in degree_values]) if degree_values else 0.0,
            "mean_joined_rows": mean([float(value) for value in joined_degree_values]) if joined_degree_values else 0.0,
            "max_all_rows": max(degree_values) if degree_values else 0,
            "zero_degree_rows": sum(1 for value in degree_values if value == 0),
        },
        "matched_length_axis": "protein_length_aa_proxy = exp(log_cds_len_nt control column) / 3",
        "dropped_active_rows": dict(sorted(missing.items())),
    }
    return out, summary


def dominant_chaperones(
    rows: list[dict[str, object]],
    chaperones: list[str],
    target: list[float],
) -> dict[str, object]:
    controls = [[float(row["abundance_log10"]), float(row["log_cds_len_nt"])] for row in rows]
    entries = []
    for feature_index, chaperone in enumerate(chaperones):
        feature = [1.0 if feature_index in row["active_indices"] else 0.0 for row in rows]  # type: ignore[operator]
        prevalence = int(sum(feature))
        rho = proteostasis.partial_spearman(feature, target, controls) if prevalence > 1 else 0.0
        entries.append({"chaperone_orf": chaperone, "partial_spearman_rho": rho, "client_count_in_u_set": prevalence})
    entries.sort(key=lambda item: abs(float(item["partial_spearman_rho"])), reverse=True)
    degree = [float(row["degree"]) for row in rows]
    return {
        "top_by_abs_partial_spearman": entries[:10],
        "controls": ["protein_abundance_log10", "log_cds_len_nt"],
        "degree_partial_spearman_rho": proteostasis.partial_spearman(degree, target, controls) if len(set(degree)) > 1 else 0.0,
    }


def cannot_claim() -> list[str]:
    return [
        "观测性投影检验不是因果扰动实验，不能推出 chaperone-client membership 导致 U。",
        "Gong2009 是 affinity-capture chaperone-client atlas，bait/prey、indirect/co-complex 与直接 folding-client 关系没有被本检验区分。",
        "64 维稀疏 membership 经过 held-out 与 matched permutation 控制过拟合，但高维稀疏描述仍有残余选择风险。",
        "Gong2009 atlas 只覆盖 4345 个 client ORF，不是全蛋白质组；覆盖可能偏向高表达或可溶蛋白。",
        "chaperone interaction 不等价于 folding dependency、folding flux 或 chaperone capacity。",
        "U = P_Q - Pi_D P_Q 依赖最小 dictionary D 的选择；本检验只说明该 U 对 chaperone-client membership 的描述性可吸收性。",
    ]


def analyze(repo: pathlib.Path) -> dict[str, object]:
    reconstructed = proteostasis.reconstruct_yeast_u(repo)
    if reconstructed.get("status") != "computed":
        return {
            "status": "needs_data",
            "verdict": "needs_data",
            "checks": {
                "pq_u_reconstructed": False,
                "base_r2_qp_validated": False,
                "chaperone_membership_built": False,
                "crossfit_heldout": False,
                "a_chap_reported": False,
                "matched_perm_null": False,
                "n_join_reported": False,
                "chaperone_verdict": "needs_data",
            },
            "result": {"reason": reconstructed.get("reason"), "cannot_claim": cannot_claim()},
        }

    chaperones, client_chaperones, chaperone_payload_summary = load_chaperone_payload(repo)
    rows, row_summary = build_chaperone_rows(
        reconstructed=reconstructed,
        chaperones=chaperones,
        client_chaperones=client_chaperones,
    )
    base_r2 = float(reconstructed["base_r2_qp"])
    base_r2_valid = BASE_R2_QP_MIN <= base_r2 <= BASE_R2_QP_MAX
    n_join = int(row_summary["n_join"])
    enough_join = n_join >= MIN_JOIN_N
    feature_width = len(chaperones)

    if not base_r2_valid or not enough_join or feature_width != 64 or not rows:
        verdict = "needs_data"
        checks = {
            "pq_u_reconstructed": True,
            "base_r2_qp_validated": base_r2_valid,
            "chaperone_membership_built": feature_width == 64 and bool(rows),
            "crossfit_heldout": False,
            "a_chap_reported": False,
            "matched_perm_null": False,
            "n_join_reported": isinstance(n_join, int),
            "chaperone_verdict": verdict,
        }
        return {
            "status": "needs_data",
            "verdict": verdict,
            "checks": checks,
            "result": {
                "organism": "Saccharomyces cerevisiae",
                "base_r2_qp": base_r2,
                "base_r2_qp_gate": [BASE_R2_QP_MIN, BASE_R2_QP_MAX],
                "n_join": n_join,
                "n_join_gate": MIN_JOIN_N,
                "chaperone_payload_summary": chaperone_payload_summary,
                "row_summary": row_summary,
                "cannot_claim": cannot_claim(),
            },
        }

    feature_rows = [list(row["active_indices"]) for row in rows]  # type: ignore[arg-type]
    dense_features = dense_binary_rows(feature_rows, feature_width)
    target_u = [float(row["u"]) for row in rows]
    p_q_subset = [float(row["p_q"]) for row in rows]
    p_q_norm2 = vector_norm2(p_q_subset)
    u_norm2 = vector_norm2(target_u)

    a_chap_insample, projected_energy, rank_chap = proteostasis.project_absorption(dense_features, target_u)
    cv = heldout_delta_r2_sparse(feature_rows, target_u, feature_width)
    groups, strata_summary = groups_for_rows(rows)
    null = matched_permutation_null(feature_rows, target_u, feature_width, groups)
    null95 = float(null["null95"])
    a_chap = float(cv["heldout_delta_r2"])
    p_chap = (1 + sum(1 for value in null["values"] if float(value) >= a_chap)) / (1 + B)  # type: ignore[index]

    exceeds_null = a_chap > null95
    heldout_gate = a_chap >= CROSS_HELDOUT_DELTA_R2
    if exceeds_null and heldout_gate:
        verdict = "crosses_boundary"
    elif exceeds_null:
        verdict = "bounded_descriptor_only"
    else:
        verdict = "composition_artifact"

    dominant = dominant_chaperones(rows, chaperones, target_u)
    best = reconstructed["best"]
    best_dictionary = best.get("D_o") if isinstance(best, dict) else None
    checks = {
        "pq_u_reconstructed": True,
        "base_r2_qp_validated": base_r2_valid,
        "chaperone_membership_built": feature_width == 64 and len(dense_features) == len(target_u),
        "crossfit_heldout": math.isfinite(a_chap) and len(cv["folds"]) == FOLDS,
        "a_chap_reported": math.isfinite(a_chap) and math.isfinite(a_chap_insample),
        "matched_perm_null": len(null["values"]) == B and math.isfinite(null95),  # type: ignore[arg-type]
        "n_join_reported": isinstance(n_join, int) and n_join >= 0,
        "chaperone_verdict": verdict,
    }
    status = "passed" if all(value is True or key == "chaperone_verdict" for key, value in checks.items()) else "failed"

    result = {
        "organism": "Saccharomyces cerevisiae",
        "base_r2_qp": base_r2,
        "base_r2_qp_gate": [BASE_R2_QP_MIN, BASE_R2_QP_MAX],
        "best_dictionary_D": best_dictionary,
        "base_n_before_dictionary_join": reconstructed.get("base_ids_n"),
        "u_gene_set_n": row_summary["active_dictionary_u_gene_set_n"],
        "analysis_n": row_summary["analysis_n"],
        "n_join": n_join,
        "n_join_gate": MIN_JOIN_N,
        "u_energy_ratio_full_active": reconstructed["u_energy_ratio_full_active"],
        "u_energy_ratio_analysis_rows": bounded_unit(u_norm2 / p_q_norm2) if p_q_norm2 > EPS else 0.0,
        "A_chap": a_chap,
        "A_chap_definition": "5-fold cross-fitted held-out Delta R2 of U predicted from the 64-dimensional chaperone-client membership matrix C, relative to fold training-mean baselines",
        "A_chap_insample_projection": a_chap_insample,
        "A_chap_insample_projected_energy": projected_energy,
        "A_chap_rank": rank_chap,
        "heldout_delta_r2": cv["heldout_delta_r2"],
        "heldout_model_r2": cv["heldout_model_r2"],
        "heldout_baseline_r2": cv["heldout_baseline_r2"],
        "cross_fitted_prediction_energy_ratio": cv["cross_fitted_prediction_energy_ratio"],
        "null95": null95,
        "null_mean": null["null_mean"],
        "null_max": null["null_max"],
        "p_chap": p_chap,
        "matched_null": {
            "B": B,
            "model": "within protein_abundance_decile x protein_length_decile, permute complete 64-dimensional client-chaperone membership rows and recompute the same 5-fold held-out Delta R2",
            "strata": strata_summary,
            "deterministic_seed": null["deterministic_seed"],
        },
        "dominant_chaperones": dominant,
        "chaperone_payload_summary": chaperone_payload_summary,
        "row_summary": row_summary,
        "decision_rule": {
            "needs_data": "base R2_QP outside [0.25,0.34] or Gong2009 client join n < 800",
            "crosses_boundary": "cross-fitted A_chap exceeds matched-null 95th percentile and heldout_delta_r2 >= 0.01",
            "bounded_descriptor_only": "cross-fitted A_chap exceeds matched-null 95th percentile but is below 0.01",
            "composition_artifact": "membership does not exceed the matched null under held-out scoring",
        },
        "verdict": verdict,
        "cannot_claim": cannot_claim(),
    }
    return {"status": status, "verdict": verdict, "checks": checks, "result": result}


def main() -> None:
    started = time.time()
    started_at = now_iso()
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        analysis = analyze(repo)
        payload = {
            "status": analysis["status"],
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": analysis["checks"],
            "verdict": analysis["verdict"],
            "result": analysis["result"],
            "started_at": started_at,
            "completed_at": now_iso(),
            "runtime_sec": time.time() - started,
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(0 if analysis["status"] == "passed" else (2 if analysis["status"] == "failed" else 3))
    except Exception as exc:
        payload = {
            "status": "failed",
            "experiment_id": EXPERIMENT_ID,
            "claim_id": CLAIM_ID,
            "checks": {"runtime_exception": True},
            "verdict": "needs_data",
            "result": {"error": str(exc), "cannot_claim": cannot_claim()},
            "started_at": started_at,
            "completed_at": now_iso(),
            "runtime_sec": time.time() - started,
        }
        print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
        sys.exit(2)


if __name__ == "__main__":
    main()

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np

from _g2n_horizon_labels import ANCHOR_TOL, HISTORY_SIZE, MAX_CLEAN_H, QUANTILES, compute_labels, compute_tau
from _g2n_native_ledger import HORIZONS, Q_TO_IDX, build_clean_examples, evaluate_clean, predict_logits, train_arm
from _phase1c_gap_ledger import (
    BOOTSTRAP_SEED,
    BOOTSTRAPS,
    bootstrap_metrics_by_episode,
    fit_logistic_head,
    predict_logistic_head,
)


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
NPZ_PATH = ROOT / "pusht_latent_large.npz"
LABELS_PATH = REPORT_DIR / "crossenv_horizon_labels_pusht.npz"
JSON_PATH = REPORT_DIR / "lewm_pusht_replication.json"
MD_PATH = REPORT_DIR / "lewm_pusht_replication.md"

REQUIRED = (
    NPZ_PATH,
    LABELS_PATH,
    ROOT / "_crossenv_horizon_ledger.py",
    ROOT / "_phase1c_gap_ledger.py",
    ROOT / "_g2n_native_ledger.py",
)

C1_SPLIT_SEEDS = (1701, 2718, 314159)
C2_SPLIT_SEEDS = (11, 101, 1701, 2718, 314159, 90210)
PRIMARY_Q = 75
Q75_IDX = int(np.where(QUANTILES == PRIMARY_Q)[0][0])
STATE_MEDIAN_DIMS = 2


def clean_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): clean_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [clean_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return clean_json(v.tolist())
    if isinstance(v, (np.integer,)):
        return int(v)
    if isinstance(v, (np.floating,)):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def require_inputs() -> None:
    missing = [str(p) for p in REQUIRED if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(missing))


def load_npz_dict(path: Path) -> dict[str, np.ndarray]:
    raw = np.load(path, allow_pickle=False)
    return {k: raw[k] for k in raw.files}


def prediction_mse_identity(data: dict[str, np.ndarray]) -> dict[str, Any]:
    tm = data["transition_mask"].astype(bool)
    pred = data["pred"].astype(np.float64)
    target = data["transition_target_emb"].astype(np.float64)
    direct = np.mean((pred - target) ** 2, axis=-1)
    delta = np.abs(direct[tm] - data["prediction_mse"].astype(np.float64)[tm])
    max_abs = float(delta.max()) if delta.size else float("nan")
    stored = float(np.asarray(data.get("prediction_mse_identity_max_abs", np.nan)).item())
    return {
        "rule": "prediction_mse == mean((pred - transition_target_emb)^2) over transition_mask",
        "tolerance": ANCHOR_TOL,
        "max_abs_delta": max_abs,
        "stored_prediction_mse_identity_max_abs": stored,
        "passed": bool(np.isfinite(max_abs) and max_abs < ANCHOR_TOL),
    }


def merge_label_parts(labels: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    parts: dict[str, list[np.ndarray]] = {
        "anchors": [],
        "valid": [],
        "err_at_h": [],
        "mean_err_to_h": [],
        "pred_z": [],
    }
    for split in ("train", "calibration", "eval"):
        parts["anchors"].append(labels[f"{split}_anchor_ep_t0"].astype(np.int64))
        parts["valid"].append(labels[f"{split}_valid"].astype(bool))
        parts["err_at_h"].append(labels[f"{split}_err_at_h"].astype(np.float64))
        parts["mean_err_to_h"].append(labels[f"{split}_mean_err_to_h"].astype(np.float64))
        parts["pred_z"].append(labels[f"{split}_pred_z"].astype(np.float32))

    merged = {k: np.concatenate(v, axis=0) for k, v in parts.items()}
    order = np.lexsort((merged["anchors"][:, 1], merged["anchors"][:, 0]))
    merged = {k: v[order] for k, v in merged.items()}

    pairs = merged["anchors"]
    if len(pairs) and np.any(np.all(pairs[1:] == pairs[:-1], axis=1)):
        raise RuntimeError("duplicate anchors in merged horizon label npz")
    return merged


def label_h1_anchor_identity(data: dict[str, np.ndarray], merged: dict[str, np.ndarray]) -> dict[str, Any]:
    anchors = merged["anchors"]
    ref = np.asarray([data["prediction_mse"][int(ep), int(t)] for ep, t in anchors], dtype=np.float64)
    h1 = merged["err_at_h"][:, 0].astype(np.float64)
    valid = merged["valid"][:, 0].astype(bool)
    delta = np.abs(ref[valid] - h1[valid])
    max_abs = float(delta.max()) if delta.size else float("nan")
    return {
        "rule": "merged horizon-label h=1 err_at_h matches pusht prediction_mse at anchor (episode,t0)",
        "tolerance": ANCHOR_TOL,
        "max_abs_delta": max_abs,
        "passed": bool(np.isfinite(max_abs) and max_abs < ANCHOR_TOL),
    }


def split_episode_values(episodes: np.ndarray, seed: int) -> dict[str, np.ndarray]:
    eps = np.asarray(sorted(int(e) for e in episodes), dtype=np.int64)
    rng = np.random.default_rng(seed)
    perm = rng.permutation(eps)
    n_train = int(round(0.60 * len(eps)))
    n_cal = int(round(0.20 * len(eps)))
    return {
        "train": np.sort(perm[:n_train]),
        "calibration": np.sort(perm[n_train : n_train + n_cal]),
        "eval": np.sort(perm[n_train + n_cal :]),
    }


def subset_definitions(data: dict[str, np.ndarray]) -> list[dict[str, Any]]:
    n_ep = int(data["emb"].shape[0])
    all_eps = np.arange(n_ep, dtype=np.int64)
    selected = data["selected_ep_idx"].astype(np.int64) if "selected_ep_idx" in data else all_eps
    by_selected = all_eps[np.argsort(selected, kind="mergesort")]
    half = len(by_selected) // 2

    subsets: list[dict[str, Any]] = [
        {
            "id": "C1a_early_selected_block",
            "group": "C1a",
            "fold": "early",
            "episodes": np.sort(by_selected[:half]),
            "definition": "first half after sorting exported episodes by selected_ep_idx",
        },
        {
            "id": "C1b_late_selected_block",
            "group": "C1b",
            "fold": "late",
            "episodes": np.sort(by_selected[half:]),
            "definition": "second half after sorting exported episodes by selected_ep_idx",
        },
        {
            "id": "C1c_selected_ep_idx_even",
            "group": "C1c",
            "fold": "even",
            "episodes": np.sort(all_eps[(selected % 2) == 0]),
            "definition": "selected_ep_idx % 2 == 0",
        },
        {
            "id": "C1c_selected_ep_idx_odd",
            "group": "C1c",
            "fold": "odd",
            "episodes": np.sort(all_eps[(selected % 2) == 1]),
            "definition": "selected_ep_idx % 2 == 1",
        },
    ]

    source = "state" if "state" in data else "proprio"
    arr = data[source].astype(np.float64)
    vm = data["valid_mask"].astype(bool) if "valid_mask" in data else np.ones(arr.shape[:2], dtype=bool)
    score = np.zeros(n_ep, dtype=np.float64)
    for ep in range(n_ep):
        vals = arr[ep, vm[ep], :STATE_MEDIAN_DIMS]
        score[ep] = float(vals.mean()) if vals.size else float("nan")
    median = float(np.nanmedian(score))
    low = all_eps[score <= median]
    high = all_eps[score > median]
    subsets.extend(
        [
            {
                "id": f"C1d_{source}01_mean_low",
                "group": "C1d",
                "fold": "low",
                "episodes": np.sort(low),
                "definition": f"episode mean of {source} first two dims <= median",
                "median": median,
            },
            {
                "id": f"C1d_{source}01_mean_high",
                "group": "C1d",
                "fold": "high",
                "episodes": np.sort(high),
                "definition": f"episode mean of {source} first two dims > median",
                "median": median,
            },
        ]
    )
    return subsets


def make_clean_part(merged: dict[str, np.ndarray], split_eps: np.ndarray, tau: np.ndarray | None = None) -> dict[str, np.ndarray]:
    m = np.isin(merged["anchors"][:, 0], split_eps)
    part = {
        "anchors": merged["anchors"][m].astype(np.int64),
        "valid": merged["valid"][m].astype(bool),
        "err_at_h": merged["err_at_h"][m].astype(np.float64),
        "mean_err_to_h": merged["mean_err_to_h"][m].astype(np.float64),
        "pred_z": merged["pred_z"][m].astype(np.float32),
    }
    if tau is not None:
        part["y"] = compute_labels(part["err_at_h"], part["valid"], tau, MAX_CLEAN_H)
    return part


def clean_for_build(parts: dict[str, dict[str, np.ndarray]]) -> dict[str, np.ndarray]:
    out: dict[str, np.ndarray] = {}
    for split, part in parts.items():
        out[f"{split}_anchor_ep_t0"] = part["anchors"].astype(np.int64)
        out[f"{split}_valid"] = part["valid"].astype(bool)
        out[f"{split}_err_at_h"] = part["err_at_h"].astype(np.float64)
        out[f"{split}_mean_err_to_h"] = part["mean_err_to_h"].astype(np.float64)
        out[f"{split}_pred_z"] = part["pred_z"].astype(np.float32)
        out[f"{split}_y"] = part["y"].astype(np.int8)
    return out


def finite_metric(m: dict[str, Any]) -> dict[str, Any]:
    out = {}
    for key, val in m.items():
        if isinstance(val, dict):
            out[key] = {kk: float(vv) for kk, vv in val.items()}
        else:
            out[key] = val
    return out


def posthoc_by_h(merged: dict[str, np.ndarray], parts: dict[str, dict[str, np.ndarray]]) -> dict[str, Any]:
    rows: dict[str, Any] = {}
    for h in HORIZONS:
        h_idx = int(h) - 1
        train = parts["train"]
        eval_part = parts["eval"]
        train_valid = train["valid"][:, h_idx]
        eval_valid = eval_part["valid"][:, h_idx]
        train_y = train["y"][train_valid, h_idx, Q75_IDX].astype(np.int8)
        eval_y = eval_part["y"][eval_valid, h_idx, Q75_IDX].astype(np.int8)
        train_anchors = train["anchors"][train_valid]
        eval_anchors = eval_part["anchors"][eval_valid]

        x_train = merged["emb_by_anchor"][train["global_idx"][train_valid]].astype(np.float64)
        x_eval = merged["emb_by_anchor"][eval_part["global_idx"][eval_valid]].astype(np.float64)
        single_class = bool(np.unique(train_y).size < 2 or np.unique(eval_y).size < 2)

        head, info = fit_logistic_head(x_train, train_y, steps=2500, lr=0.05, l2=1e-4)
        prob, _ = predict_logistic_head(head, x_eval)
        metrics = bootstrap_metrics_by_episode(
            eval_y,
            prob,
            prob,
            eval_anchors[:, 0].astype(np.int64),
            seed=BOOTSTRAP_SEED,
            n_boot=BOOTSTRAPS,
        )
        rows[f"h{h}_q75"] = {
            "method": "posthoc_learned_logistic_emb_only",
            "h": int(h),
            "q": PRIMARY_Q,
            "metrics": finite_metric(metrics),
            "single_class": single_class,
            "class_counts": {
                "train_positive": int(train_y.sum()),
                "train_negative": int(len(train_y) - train_y.sum()),
                "eval_positive": int(eval_y.sum()),
                "eval_negative": int(len(eval_y) - eval_y.sum()),
            },
            "fit": info,
        }
    return rows


def add_global_indices(merged: dict[str, np.ndarray], parts: dict[str, dict[str, np.ndarray]]) -> None:
    pair_to_idx = {(int(ep), int(t)): i for i, (ep, t) in enumerate(merged["anchors"])}
    for part in parts.values():
        part["global_idx"] = np.asarray([pair_to_idx[(int(ep), int(t))] for ep, t in part["anchors"]], dtype=np.int64)


def native_by_h(data: dict[str, np.ndarray], parts: dict[str, dict[str, np.ndarray]]) -> dict[str, Any]:
    clean = clean_for_build(parts)
    train_ex = build_clean_examples(data, clean, "train", None)
    eval_ex = build_clean_examples(data, clean, "eval", None)
    model, info, norm = train_arm(
        "E",
        train_ex,
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    logits = predict_logits(model, eval_ex, norm)
    raw = evaluate_clean(logits, eval_ex)
    out: dict[str, Any] = {}
    for h in HORIZONS:
        h_i = HORIZONS.index(h)
        q_i = Q_TO_IDX[PRIMARY_Q]
        train_valid = train_ex["valid"][:, h_i, q_i]
        eval_valid = eval_ex["valid"][:, h_i, q_i]
        train_y = train_ex["y"][train_valid, h_i, q_i].astype(np.int8)
        eval_y = eval_ex["y"][eval_valid, h_i, q_i].astype(np.int8)
        single_class = bool(np.unique(train_y).size < 2 or np.unique(eval_y).size < 2)
        out[f"h{h}_q75"] = {
            "method": "native_E_horizon_ledger",
            "h": int(h),
            "q": PRIMARY_Q,
            "metrics": finite_metric(raw[f"h{h}_q75"]),
            "single_class": single_class,
            "class_counts": {
                "train_positive": int(train_y.sum()),
                "train_negative": int(len(train_y) - train_y.sum()),
                "eval_positive": int(eval_y.sum()),
                "eval_negative": int(len(eval_y) - eval_y.sum()),
            },
        }
    return {"info": info, "by_h": out}


def split_counts(parts: dict[str, dict[str, np.ndarray]], splits: dict[str, np.ndarray]) -> dict[str, Any]:
    out = {}
    for split, eps in splits.items():
        row: dict[str, Any] = {"episodes": int(len(eps)), "anchors": int(len(parts[split]["anchors"]))}
        for h in HORIZONS:
            row[f"valid_h{h}"] = int(parts[split]["valid"][:, int(h) - 1].sum())
        out[split] = row
    return out


def run_cell(
    *,
    cell_id: str,
    kind: str,
    subset: dict[str, Any],
    split_seed: int,
    data: dict[str, np.ndarray],
    merged: dict[str, np.ndarray],
) -> dict[str, Any]:
    t0 = time.perf_counter()
    episodes = np.asarray(subset["episodes"], dtype=np.int64)
    splits = split_episode_values(episodes, split_seed)
    train_part = make_clean_part(merged, splits["train"])
    tau = compute_tau(train_part["err_at_h"], train_part["valid"], MAX_CLEAN_H)
    parts = {
        "train": make_clean_part(merged, splits["train"], tau),
        "calibration": make_clean_part(merged, splits["calibration"], tau),
        "eval": make_clean_part(merged, splits["eval"], tau),
    }
    add_global_indices(merged, parts)

    print(f"[posthoc] {cell_id}", flush=True)
    posthoc = posthoc_by_h(merged, parts)
    print(f"[native] {cell_id}", flush=True)
    native = native_by_h(data, parts)

    return {
        "cell_id": cell_id,
        "kind": kind,
        "subset_id": subset["id"],
        "group": subset.get("group"),
        "fold": subset.get("fold"),
        "subset_definition": subset.get("definition"),
        "split_seed": int(split_seed),
        "episodes": int(len(episodes)),
        "selected_ep_idx_min": int(data["selected_ep_idx"][episodes].min()) if "selected_ep_idx" in data else int(episodes.min()),
        "selected_ep_idx_max": int(data["selected_ep_idx"][episodes].max()) if "selected_ep_idx" in data else int(episodes.max()),
        "split_counts": split_counts(parts, splits),
        "tau_q75_by_h": {f"h{h}": float(tau[int(h) - 1, Q75_IDX]) for h in HORIZONS},
        "posthoc": posthoc,
        "native": native["by_h"],
        "native_train_info": native["info"],
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
    }


def metric_at(cell: dict[str, Any], method: str, h: int) -> dict[str, Any]:
    return cell[method][f"h{h}_q75"]


def metric_pass(cell: dict[str, Any], method: str, h: int, low_threshold: float) -> bool:
    row = metric_at(cell, method, h)
    if row["single_class"]:
        return False
    return bool(row["metrics"]["failure_detection_auroc"]["ci95_low"] >= low_threshold)


def h1_artifact_alert(cell: dict[str, Any], method: str) -> bool:
    row = metric_at(cell, method, 1)
    if row["single_class"]:
        return False
    auroc = row["metrics"]["failure_detection_auroc"]
    uer = row["metrics"]["unlogged_error_rate"]
    return bool(auroc["ci95_high"] < 0.95 or uer["ci95_low"] > 0.02)


def summarize_confirmation(c1_cells: list[dict[str, Any]], c2_cells: list[dict[str, Any]]) -> dict[str, Any]:
    methods = ("posthoc", "native")
    c1: dict[str, Any] = {}
    for method in methods:
        group_rows = {}
        for group in ("C1a", "C1b", "C1c", "C1d"):
            group_cells = [c for c in c1_cells if c["group"] == group]
            h1_ok = all(metric_pass(c, method, 1, 0.98) for c in group_cells)
            h5_ok = all(metric_pass(c, method, 5, 0.95) for c in group_cells)
            h10_ok = all(metric_pass(c, method, 10, 0.95) for c in group_cells)
            group_rows[group] = {
                "cells": int(len(group_cells)),
                "h1_all_seed_fold_ci_low_ge_0p98": bool(h1_ok),
                "h5_all_seed_fold_ci_low_ge_0p95": bool(h5_ok),
                "h10_all_seed_fold_ci_low_ge_0p95": bool(h10_ok),
                "passes_group": bool(h1_ok and h5_ok and h10_ok),
            }
        passed = sum(1 for row in group_rows.values() if row["passes_group"])
        c1[method] = {
            "groups": group_rows,
            "groups_passed": int(passed),
            "passes_c1_rule": bool(passed >= 3),
            "rule": "at least 3/4 C1 groups pass all folds/seeds: h1 ci95_low>=0.98 and h5/h10 ci95_low>=0.95",
        }

    c2: dict[str, Any] = {}
    for method in methods:
        seed_rows = {}
        for cell in c2_cells:
            seed = int(cell["split_seed"])
            seed_rows[str(seed)] = {
                "h1_ci95_low_ge_0p99": bool(metric_pass(cell, method, 1, 0.99)),
                "h1_ci95_low": metric_at(cell, method, 1)["metrics"]["failure_detection_auroc"]["ci95_low"],
                "single_class": bool(metric_at(cell, method, 1)["single_class"]),
            }
        passed = sum(1 for row in seed_rows.values() if row["h1_ci95_low_ge_0p99"])
        c2[method] = {
            "seeds": seed_rows,
            "seeds_passed": int(passed),
            "passes_c2_rule": bool(passed >= 5),
            "rule": "at least 5/6 split seeds h1 ci95_low>=0.99",
        }

    alerts = []
    for cell in c1_cells + c2_cells:
        for method in methods:
            if h1_artifact_alert(cell, method):
                row = metric_at(cell, method, 1)
                alerts.append(
                    {
                        "cell_id": cell["cell_id"],
                        "method": method,
                        "auroc": row["metrics"]["failure_detection_auroc"],
                        "uer": row["metrics"]["unlogged_error_rate"],
                    }
                )

    single_class_cells = []
    for cell in c1_cells + c2_cells:
        for method in methods:
            for h in HORIZONS:
                row = metric_at(cell, method, int(h))
                if row["single_class"]:
                    single_class_cells.append(
                        {
                            "cell_id": cell["cell_id"],
                            "method": method,
                            "h": int(h),
                            "class_counts": row["class_counts"],
                        }
                    )

    confirmed = all(c1[m]["passes_c1_rule"] and c2[m]["passes_c2_rule"] for m in methods)
    if confirmed:
        conclusion = "confirmed"
    elif alerts:
        conclusion = "artifact-bounded"
    elif single_class_cells:
        conclusion = "inconclusive"
    else:
        conclusion = "artifact-bounded"

    return {
        "c1": c1,
        "c2": c2,
        "artifact_alerts": alerts,
        "single_class_cells": single_class_cells,
        "conclusion": conclusion,
    }


def compact_cell_table(cells: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for cell in cells:
        row: dict[str, Any] = {
            "cell_id": cell["cell_id"],
            "group": cell.get("group"),
            "fold": cell.get("fold"),
            "split_seed": cell["split_seed"],
            "episodes": cell["episodes"],
            "eval_episodes": cell["split_counts"]["eval"]["episodes"],
        }
        for method in ("posthoc", "native"):
            for h in HORIZONS:
                m = metric_at(cell, method, int(h))
                prefix = f"{method}_h{h}"
                row[f"{prefix}_auroc"] = m["metrics"]["failure_detection_auroc"]
                row[f"{prefix}_uer"] = m["metrics"]["unlogged_error_rate"]
                row[f"{prefix}_single_class"] = bool(m["single_class"])
                row[f"{prefix}_eval_pos"] = int(m["class_counts"]["eval_positive"])
                row[f"{prefix}_eval_neg"] = int(m["class_counts"]["eval_negative"])
        rows.append(row)
    return rows


def fmt_metric(m: dict[str, float]) -> str:
    return f"{m['observed']:.4f} [{m['ci95_low']:.4f}, {m['ci95_high']:.4f}]"


def md_summary(report: dict[str, Any]) -> str:
    lines = [
        "# PushT Export-Internal Replication",
        "",
        f"- status: {report['status']}",
        f"- conclusion: **{report['conclusion']['conclusion']}**",
        f"- anchor direct max |delta|: {report['anchor_checks']['prediction_mse_identity']['max_abs_delta']:.9g}",
        f"- anchor label h1 max |delta|: {report['anchor_checks']['label_h1_identity']['max_abs_delta']:.9g}",
        "- not_claimed: still a single-export, export-internal replication; C3 true independent export is not run here.",
        "",
        "## C1 Summary",
        "",
        "| method | C1 groups passed | pass C1 | C2 seeds passed | pass C2 |",
        "|---|---:|---:|---:|---:|",
    ]
    for method in ("posthoc", "native"):
        c1 = report["conclusion"]["c1"][method]
        c2 = report["conclusion"]["c2"][method]
        lines.append(
            f"| {method} | {c1['groups_passed']}/4 | {str(c1['passes_c1_rule']).lower()} | "
            f"{c2['seeds_passed']}/6 | {str(c2['passes_c2_rule']).lower()} |"
        )

    lines.extend(["", "## C1 Cells", "", "| cell | seed | post h1 | native h1 | post h5 | native h5 | post h10 | native h10 |", "|---|---:|---:|---:|---:|---:|---:|---:|"])
    for cell in report["c1_cells"]:
        lines.append(
            f"| {cell['cell_id']} | {cell['split_seed']} | "
            f"{fmt_metric(cell['posthoc']['h1_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h1_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['posthoc']['h5_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h5_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['posthoc']['h10_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h10_q75']['metrics']['failure_detection_auroc'])} |"
        )

    lines.extend(["", "## C2 Cells", "", "| seed | post h1 | native h1 | post h5 | native h5 | post h10 | native h10 |", "|---:|---:|---:|---:|---:|---:|---:|"])
    for cell in report["c2_cells"]:
        lines.append(
            f"| {cell['split_seed']} | "
            f"{fmt_metric(cell['posthoc']['h1_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h1_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['posthoc']['h5_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h5_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['posthoc']['h10_q75']['metrics']['failure_detection_auroc'])} | "
            f"{fmt_metric(cell['native']['h10_q75']['metrics']['failure_detection_auroc'])} |"
        )

    alerts = report["conclusion"]["artifact_alerts"]
    lines.extend(["", "## Artifact Alerts", ""])
    if alerts:
        for alert in alerts:
            lines.append(
                f"- {alert['cell_id']} {alert['method']}: h1 AUROC {fmt_metric(alert['auroc'])}; "
                f"UER {fmt_metric(alert['uer'])}"
            )
    else:
        lines.append("- none under the preregistered h1/UER alert rule.")
    return "\n".join(lines) + "\n"


def main() -> None:
    require_inputs()
    REPORT_DIR.mkdir(exist_ok=True)
    data = load_npz_dict(NPZ_PATH)
    labels = load_npz_dict(LABELS_PATH)

    anchor = prediction_mse_identity(data)
    if not anchor["passed"]:
        report = {"status": "stopped_anchor_failed", "anchor_checks": {"prediction_mse_identity": anchor}}
        JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text("# PushT Export-Internal Replication\n\nStopped: direct prediction_mse identity failed.\n", encoding="utf-8")
        raise SystemExit("anchor failed: prediction_mse identity")

    merged = merge_label_parts(labels)
    label_anchor = label_h1_anchor_identity(data, merged)
    if not label_anchor["passed"]:
        report = {
            "status": "stopped_anchor_failed",
            "anchor_checks": {"prediction_mse_identity": anchor, "label_h1_identity": label_anchor},
        }
        JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text("# PushT Export-Internal Replication\n\nStopped: label h1 identity failed.\n", encoding="utf-8")
        raise SystemExit("anchor failed: label h1 identity")

    emb_by_anchor = np.asarray([data["emb"][int(ep), int(t)] for ep, t in merged["anchors"]], dtype=np.float64)
    merged["emb_by_anchor"] = emb_by_anchor

    c1_cells: list[dict[str, Any]] = []
    for subset in subset_definitions(data):
        for seed in C1_SPLIT_SEEDS:
            cell_id = f"{subset['id']}_seed{seed}"
            print(f"[cell] {cell_id}", flush=True)
            c1_cells.append(
                run_cell(cell_id=cell_id, kind="C1", subset=subset, split_seed=seed, data=data, merged=merged)
            )

    all_subset = {
        "id": "C2_all_episodes",
        "group": "C2",
        "fold": "all",
        "episodes": np.arange(data["emb"].shape[0], dtype=np.int64),
        "definition": "all 150 exported episodes",
    }
    c2_cells: list[dict[str, Any]] = []
    for seed in C2_SPLIT_SEEDS:
        cell_id = f"C2_all_episodes_seed{seed}"
        print(f"[cell] {cell_id}", flush=True)
        c2_cells.append(run_cell(cell_id=cell_id, kind="C2", subset=all_subset, split_seed=seed, data=data, merged=merged))

    conclusion = summarize_confirmation(c1_cells, c2_cells)
    report = {
        "status": "ok",
        "schema_id": "pusht.export_internal_replication.round2c",
        "protocol": {
            "scientific_question": "Whether PushT h=1 AUROC 1.000 is robust within the existing export or a single-export/episode-selection artifact.",
            "no_reexport": True,
            "inputs": [str(p) for p in REQUIRED],
            "bootstrap": {"unit": "eval episodes", "resamples": BOOTSTRAPS, "seed": BOOTSTRAP_SEED},
            "split_seeds": {"C1": list(C1_SPLIT_SEEDS), "C2": list(C2_SPLIT_SEEDS)},
            "failure_truth": "err_at_h > this subset/seed train q75, recomputed independently for every cell",
            "posthoc": "learned logistic regression, emb-only, same optimizer settings as crossenv gap ledger",
            "native": "arm E horizon ledger from _g2n_native_ledger.py",
            "horizons": list(HORIZONS),
            "primary_quantile": PRIMARY_Q,
            "single_class_policy": "fail-closed; never counted as AUROC 1.0 confirmation",
        },
        "anchor_checks": {"prediction_mse_identity": anchor, "label_h1_identity": label_anchor},
        "sample_counts": {
            "episodes": int(data["emb"].shape[0]),
            "valid_transitions": int(data["transition_mask"].astype(bool).sum()),
            "merged_horizon_anchors": int(len(merged["anchors"])),
        },
        "c1_cells": c1_cells,
        "c2_cells": c2_cells,
        "c1_table": compact_cell_table(c1_cells),
        "c2_table": compact_cell_table(c2_cells),
        "conclusion": conclusion,
        "not_claimed": [
            "This is still a single-export, export-internal replication.",
            "C3 true independent export would be stronger and is not run in this round.",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    MD_PATH.write_text(md_summary(clean_json(report)), encoding="utf-8")
    print(f"[done] conclusion={conclusion['conclusion']} json={JSON_PATH}", flush=True)


if __name__ == "__main__":
    main()

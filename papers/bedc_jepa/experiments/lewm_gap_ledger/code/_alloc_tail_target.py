from __future__ import annotations

import json
import os
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn

import _g2n_native_ledger as g2n
from _allocation_bridge import (
    BOOTSTRAP_SEED,
    BOOTSTRAPS,
    CLEAN_LABELS,
    PYTHON_SEED,
    ScalarLedgerTransformer,
    SPLIT_SEED,
    TARGET_H,
    TARGET_H_INDEX,
    TORCH_SEED,
    budget_eval_for_score,
    pairwise_logistic_loss,
    predict_scalar,
    spearman_one,
    tensorize_examples,
    within_episode_spearman,
)
from _lat_lewm_port import NPZ_PATH, REPORT_DIR
from _ledger_gated_rollout import (
    HIGH_H,
    LOW_H,
    MID_H,
    UNIFORM_H,
    allocation_uniform,
    summarize_allocation,
)
from _phase1c_gap_ledger import flatten_transition_rows
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
NATIVE_LEDGER = ROOT / "_g2n_native_ledger.py"
ALLOCATION_BRIDGE = ROOT / "_allocation_bridge.py"
RHO_THRESHOLD = ROOT / "_allocation_rho_threshold.py"
JSON_PATH = REPORT_DIR / "lewm_alloc_tail_target.json"
MD_PATH = REPORT_DIR / "lewm_alloc_tail_target.md"

ORACLE_DELTA_ANCHOR = -0.015867561326231905
ORACLE_TOL = 1e-9


def require_inputs() -> None:
    missing = [
        p
        for p in (CLEAN_LABELS, ALLOCATION_BRIDGE, RHO_THRESHOLD, NATIVE_LEDGER)
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def tail_target(err_at_h: np.ndarray, valid: np.ndarray, arm: str) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    first5_valid = valid[:, :TARGET_H].all(axis=1)
    err5 = err_at_h[:, :TARGET_H].astype(np.float64)
    if arm == "T1_CVaR":
        # beta=0.8 over five steps leaves the top 20%, i.e. the single largest step.
        target = np.sort(err5, axis=1)[:, -1:].mean(axis=1)
        spec = {
            "name": "CVaR",
            "beta": 0.8,
            "definition": "mean of top 20% of err_at_h[:, :5] per anchor",
            "top_count": 1,
        }
    elif arm == "T2_max_step":
        target = np.max(err5, axis=1)
        spec = {
            "name": "max-step",
            "definition": "max(err_at_h[:, :5]) per anchor",
        }
    elif arm == "T3_q90":
        target = np.quantile(err5, 0.90, axis=1, method="linear")
        spec = {
            "name": "top-quantile",
            "quantile": 0.9,
            "definition": "q90(err_at_h[:, :5]) per anchor using numpy linear quantile",
        }
    else:
        raise ValueError(f"unknown arm: {arm}")
    finite = np.isfinite(target)
    return target.astype(np.float64), (first5_valid & finite), spec


def train_tail_ranker(
    name: str,
    train_ex: dict[str, np.ndarray],
    target_all: np.ndarray,
    keep: np.ndarray,
    spec: dict[str, Any],
) -> tuple[ScalarLedgerTransformer, dict[str, Any], dict[str, np.ndarray]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)

    ex = {
        k: (v[keep] if isinstance(v, np.ndarray) and len(v) == len(keep) else v)
        for k, v in train_ex.items()
    }
    target = target_all[keep].astype(np.float32)

    norm = g2n.compute_norm(ex)
    exn = g2n.normalize_examples(ex, norm)
    tensors = tensorize_examples(exn)
    target_t = torch.from_numpy(target)
    episode_t = torch.from_numpy(exn["episode"].astype(np.int64))
    model = ScalarLedgerTransformer(exn["past_z"].shape[-1], exn["past_a"].shape[-1])
    opt = torch.optim.AdamW(model.parameters(), lr=g2n.LR)
    generator = torch.Generator().manual_seed(TORCH_SEED)
    steps = 0
    skipped_batches = 0
    t0 = time.perf_counter()

    model.train()
    for epoch in range(1, g2n.EPOCHS + 1):
        order = torch.randperm(len(target), generator=generator)
        for start in range(0, len(target), g2n.BATCH):
            idx = order[start : start + g2n.BATCH]
            score = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                tensors["future_z"][idx],
                tensors["future_delta"][idx],
                tensors["future_avail"][idx],
                tensors["t_scalar"][idx],
            )
            maybe_loss = pairwise_logistic_loss(score, target_t[idx], episode_t[idx])
            if maybe_loss is None:
                skipped_batches += 1
                continue
            loss = maybe_loss
            if not torch.isfinite(loss):
                raise RuntimeError(f"non-finite loss in {name}")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
        if epoch == 1 or epoch % 5 == 0 or epoch == g2n.EPOCHS:
            print(f"[train] {name} epoch={epoch}/{g2n.EPOCHS} steps={steps}", flush=True)

    info = {
        "status": "trained",
        "objective": "within_episode_pairwise_logistic_ranking",
        "tail_target": spec,
        "model": "ScalarLedgerTransformer from _allocation_bridge",
        "epochs": g2n.EPOCHS,
        "batch": g2n.BATCH,
        "optimizer": "AdamW",
        "lr": g2n.LR,
        "optimizer_steps": int(steps),
        "skipped_batches_without_pairs": int(skipped_batches),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(len(target)),
    }
    return model.eval(), info, norm


def anchors_from_eval(clean_eval_ex: dict[str, np.ndarray], valid_h5: np.ndarray) -> tuple[list[dict[str, Any]], dict[int, list[int]]]:
    anchors_arr = clean_eval_ex["anchor_ep_t0"][valid_h5]
    anchors = [
        {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
        for i, (ep, t) in enumerate(anchors_arr)
    ]
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    return anchors, anchors_by_ep


def target_spearman(score: np.ndarray, target: np.ndarray, anchors: list[dict[str, Any]], target_name: str) -> dict[str, Any]:
    out = within_episode_spearman(score, target, anchors)
    out["definition"] = f"Spearman(score, {target_name}), computed within episode then averaged"
    return out


def target_correlation_summary(clean: np.lib.npyio.NpzFile) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for split in ("train", "eval"):
        true_mean = clean[f"{split}_mean_err_to_h"][:, TARGET_H_INDEX].astype(np.float64)
        valid_h5 = clean[f"{split}_valid"][:, TARGET_H_INDEX].astype(bool)
        anchors_arr = clean[f"{split}_anchor_ep_t0"]
        anchors = [
            {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
            for i, (ep, t) in enumerate(anchors_arr[valid_h5])
        ]
        split_out: dict[str, Any] = {}
        for arm in ("T1_CVaR", "T2_max_step", "T3_q90"):
            tgt, keep, spec = tail_target(clean[f"{split}_err_at_h"], clean[f"{split}_valid"], arm)
            mask = valid_h5 & keep
            split_anchors = [
                {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
                for i, (ep, t) in enumerate(anchors_arr[mask])
            ]
            split_out[arm] = {
                "target": spec,
                "pearson_to_mean_err_to_5": float(np.corrcoef(tgt[mask], true_mean[mask])[0, 1]),
                "within_episode_spearman_to_mean_err_to_5": target_spearman(
                    tgt[mask],
                    true_mean[mask],
                    split_anchors,
                    "true mean_err_to_5",
                ),
            }
        out[split] = split_out
    return out


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# Allocation Tail Targets",
        "",
        f"- status: `{report['status']}`",
        f"- oracle delta anchor: `{report['oracle_anchor']['observed_delta']:.12f}` "
        f"(target `{report['oracle_anchor']['target_delta']:.12f}`)",
        f"- decision rule: {report['decision_rule']}",
        "",
        "## Results",
        "",
        "| arm | rho to mean_err_to_5 | rho to own target | delta vs uniform | 95% CI | oracle gap | verdict |",
        "|---|---:|---:|---:|---:|---:|---|",
    ]
    for name in ("T1_CVaR", "T2_max_step", "T3_q90"):
        row = report["arms"][name]
        d = row["delta_vs_uniform"]
        lines.append(
            f"| `{name}` | {row['spearman_to_mean_err_to_5']['episode_mean']:.6f} | "
            f"{row['spearman_to_own_training_target']['episode_mean']:.6f} | "
            f"{d['observed']:.9f} | [{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | "
            f"{row['oracle_gap']:.9f} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Controls",
            "",
            f"- uniform h: `{UNIFORM_H}` for every anchor",
            f"- score-sorted allocation: low score half h=`{LOW_H}`, high score half h=`{HIGH_H}`, odd median h=`{MID_H}`",
            f"- oracle delta vs uniform: `{report['controls']['oracle']['delta_vs_uniform']['observed']:.9f}` "
            f"[{report['controls']['oracle']['delta_vs_uniform']['ci95_low']:.9f}, "
            f"{report['controls']['oracle']['delta_vs_uniform']['ci95_high']:.9f}]",
            "",
            "## Not Claimed",
            "",
        ]
    )
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    _ = flatten_transition_rows(data)
    splits = g2n.split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(CLEAN_LABELS)
    clean_train_ex = g2n.build_clean_examples(data, clean, "train", None)
    clean_eval_ex = g2n.build_clean_examples(data, clean, "eval", None)

    valid_h5 = clean["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    errors_h5 = clean["eval_err_at_h"][valid_h5, :TARGET_H].astype(np.float64)
    true_mean_h5 = clean["eval_mean_err_to_h"][valid_h5, TARGET_H_INDEX].astype(np.float64)
    anchors, anchors_by_ep = anchors_from_eval(clean_eval_ex, valid_h5)
    uniform_h = allocation_uniform(anchors_by_ep)
    uniform_alloc = summarize_allocation("uniform", uniform_h, errors_h5, anchors)

    oracle = budget_eval_for_score("oracle", true_mean_h5.copy(), anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_delta = float(oracle["delta_vs_uniform"]["observed"])
    if abs(oracle_delta - ORACLE_DELTA_ANCHOR) > ORACLE_TOL:
        stopped = {
            "status": "stopped_oracle_anchor_failed",
            "oracle_anchor": {
                "observed_delta": oracle_delta,
                "target_delta": ORACLE_DELTA_ANCHOR,
                "abs_delta": abs(oracle_delta - ORACLE_DELTA_ANCHOR),
                "tolerance": ORACLE_TOL,
            },
        }
        JSON_PATH.write_text(json.dumps(clean_json(stopped), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text(
            "# Allocation Tail Targets\n\n"
            f"Stopped: oracle delta anchor failed. observed `{oracle_delta:.17g}`, "
            f"target `{ORACLE_DELTA_ANCHOR:.17g}`.\n",
            encoding="utf-8",
        )
        raise SystemExit(f"oracle anchor mismatch: observed={oracle_delta:.17g}, target={ORACLE_DELTA_ANCHOR:.17g}")

    target_corr = target_correlation_summary(clean)
    out_arms: dict[str, Any] = {}
    for name in ("T1_CVaR", "T2_max_step", "T3_q90"):
        train_target, train_keep, spec = tail_target(clean["train_err_at_h"], clean["train_valid"], name)
        eval_target_all, eval_keep, _ = tail_target(clean["eval_err_at_h"], clean["eval_valid"], name)
        eval_keep_h5 = valid_h5 & eval_keep
        if not np.array_equal(eval_keep_h5, valid_h5):
            raise RuntimeError(f"{name} eval target validity differs from h=5 validity")

        print(f"[train] {name}", flush=True)
        model, info, norm = train_tail_ranker(name, clean_train_ex, train_target, train_keep, spec)
        score_all = predict_scalar(model, clean_eval_ex, norm)
        score = score_all[valid_h5]
        own_target = eval_target_all[valid_h5].astype(np.float64)

        budget = budget_eval_for_score(name, score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
        delta = budget["delta_vs_uniform"]
        rho_mean = within_episode_spearman(score, true_mean_h5, anchors)
        rho_own = target_spearman(score, own_target, anchors, spec["definition"])
        positive = bool(float(rho_mean["episode_mean"]) >= 0.58 and float(delta["ci95_high"]) < 0.0)

        out_arms[name] = {
            "info": info,
            "allocation": budget["allocation"],
            "delta_vs_uniform": delta,
            "spearman_to_mean_err_to_5": rho_mean,
            "spearman_to_own_training_target": rho_own,
            "oracle_gap": float(delta["observed"] - oracle_delta),
            "decision": {
                "rho_to_mean_err_to_5_at_least_0p58": bool(float(rho_mean["episode_mean"]) >= 0.58),
                "ci95_high_below_zero": bool(float(delta["ci95_high"]) < 0.0),
            },
            "verdict": "positive" if positive else "not_positive",
        }

    report = {
        "status": "ok",
        "schema_id": "lewm.alloc_tail_target",
        "question": "Can tail-risk training targets push allocation rank quality past rho*=0.58?",
        "protocol": {
            "reused_from": "_allocation_bridge evaluation skeleton: same eval anchors, 5/1 depth split, matched budget, uniform/oracle, paired episode bootstrap",
            "seeds": {
                "numpy": PYTHON_SEED,
                "torch": TORCH_SEED,
                "split": SPLIT_SEED,
                "bootstrap": BOOTSTRAP_SEED,
            },
            "bootstrap_resamples": BOOTSTRAPS,
            "training": {
                "epochs": g2n.EPOCHS,
                "batch": g2n.BATCH,
                "optimizer": "AdamW",
                "lr": g2n.LR,
                "no_hyperparameter_scan": True,
            },
            "allocation_rule": {
                "uniform": f"h={UNIFORM_H} for every anchor",
                "score_sorted": f"within episode low score half h={LOW_H}, high score half h={HIGH_H}, odd median h={MID_H}",
                "oracle": "same rule, sorted by true h=5 mean error",
            },
            "eval": {
                "anchors": int(len(anchors)),
                "episodes": int(len(anchors_by_ep)),
                "episode_split": "eval",
                "budget_errors": "eval_err_at_h first five steps",
                "key_rho": "within-episode Spearman(ranker score, true mean_err_to_5)",
            },
        },
        "precursors": {
            "clean_npz": str(CLEAN_LABELS),
            "allocation_bridge_script": str(ALLOCATION_BRIDGE),
            "allocation_rho_threshold_script": str(RHO_THRESHOLD),
            "native_ledger_script": str(NATIVE_LEDGER),
        },
        "oracle_anchor": {
            "observed_delta": oracle_delta,
            "target_delta": ORACLE_DELTA_ANCHOR,
            "abs_delta": abs(oracle_delta - ORACLE_DELTA_ANCHOR),
            "tolerance": ORACLE_TOL,
            "status": "passed",
        },
        "arms": out_arms,
        "controls": {
            "uniform": {"allocation": uniform_alloc},
            "oracle": {
                "allocation": oracle["allocation"],
                "delta_vs_uniform": oracle["delta_vs_uniform"],
                "spearman": within_episode_spearman(true_mean_h5.copy(), true_mean_h5, anchors),
                "oracle_gap": 0.0,
            },
        },
        "target_correlations": target_corr,
        "decision_rule": "per arm positive iff rho(score, true mean_err_to_5) >= 0.58 and paired episode-bootstrap CI95_high for allocation minus uniform is < 0",
        "not_claimed": [
            "single checkpoint single export",
            "prediction budget allocation rather than planning or control",
            "tail statistics are synthetic training targets",
            "no hyperparameter scan",
            "no selection of only the best arm",
        ],
    }
    clean_report = clean_json(report)
    JSON_PATH.write_text(json.dumps(clean_report, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_report)
    summary = {
        name: {
            "rho_to_mean_err_to_5": row["spearman_to_mean_err_to_5"]["episode_mean"],
            "delta": row["delta_vs_uniform"],
            "verdict": row["verdict"],
        }
        for name, row in out_arms.items()
    }
    print(json.dumps(clean_json(summary), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

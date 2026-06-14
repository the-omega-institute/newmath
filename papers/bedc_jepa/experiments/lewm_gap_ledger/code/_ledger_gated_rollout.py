from __future__ import annotations

import json
import math
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase1c_gap_ledger import BOOTSTRAP_SEED, predict_logistic_head
from _phase2a_brittleness_gap import MODEL_REPO, NPZ_PATH, clean_json, fit_clean_protocol
from _phase2c_ood_aware_gap import fit_gap_head_for_parts, materialize_clean_split
from _phase1c_gap_ledger import flatten_transition_rows


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_ledger_gated_rollout.json"
MD_PATH = REPORT_DIR / "lewm_ledger_gated_rollout.md"

HORIZON_FOR_BUDGET = 5
UNIFORM_H = 3
LOW_H = 5
MID_H = 3
HIGH_H = 1
ROLL_BATCH = 512
ANCHOR_TOL = 1e-4
BOOTSTRAPS = 500
ROLLOUT_BOOTSTRAP_SEED = 314159


def load_data() -> dict[str, np.ndarray]:
    raw = np.load(NPZ_PATH)
    return {k: raw[k] for k in raw.files}


def load_predictor(device: torch.device) -> tuple[Any, dict[str, Any], str, str]:
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)
    return model, config, checkpoint_path, config_path


def build_anchor_rows(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    eval_episodes: np.ndarray,
    row_to_gap_score: dict[int, float],
) -> list[dict[str, Any]]:
    history_size = int(data["history_size"])
    anchors: list[dict[str, Any]] = []
    for ep_raw in eval_episodes:
        ep = int(ep_raw)
        valid_transition_count = int(data["transition_mask"][ep].sum())
        for t0 in range(history_size - 1, valid_transition_count + 1):
            if t0 + HORIZON_FOR_BUDGET > valid_transition_count:
                continue
            row_idx = np.where((rows["episode"] == ep) & (rows["t"] == t0))[0]
            if len(row_idx) != 1:
                raise RuntimeError(f"expected one row for ep={ep}, t0={t0}, found {len(row_idx)}")
            row = int(row_idx[0])
            anchors.append(
                {
                    "episode": ep,
                    "t0": int(t0),
                    "row_idx": row,
                    "gap_score": float(row_to_gap_score[row]),
                }
            )
    return anchors


def rollout_errors_for_horizon(
    model: Any,
    data: dict[str, np.ndarray],
    anchors: list[dict[str, Any]],
    *,
    device: torch.device,
    history_size: int,
    horizon: int,
    batch_size: int = ROLL_BATCH,
) -> np.ndarray:
    emb_np = data["emb"].astype(np.float32)
    action_np = data["action"].astype(np.float32)
    out = np.zeros((len(anchors), horizon), dtype=np.float64)

    with torch.inference_mode():
        for lo in range(0, len(anchors), batch_size):
            hi = min(lo + batch_size, len(anchors))
            batch = anchors[lo:hi]
            b = len(batch)
            ctx_emb = np.zeros((b, history_size, emb_np.shape[-1]), dtype=np.float32)
            ctx_action = np.zeros((b, history_size, action_np.shape[-1]), dtype=np.float32)
            true_future = np.zeros((b, horizon, emb_np.shape[-1]), dtype=np.float32)
            future_action = np.zeros((b, horizon, action_np.shape[-1]), dtype=np.float32)
            for j, anchor in enumerate(batch):
                ep = int(anchor["episode"])
                t0 = int(anchor["t0"])
                start = t0 - history_size + 1
                ctx_emb[j] = emb_np[ep, start : t0 + 1]
                ctx_action[j] = action_np[ep, start : t0 + 1]
                true_future[j] = emb_np[ep, t0 + 1 : t0 + horizon + 1]
                future_action[j] = action_np[ep, t0 + 1 : t0 + horizon + 1]

            emb = torch.from_numpy(ctx_emb).to(device)
            act = torch.from_numpy(ctx_action).to(device)
            true = torch.from_numpy(true_future).to(device)
            future_act = torch.from_numpy(future_action).to(device)

            preds = []
            for step in range(horizon):
                act_emb = model.action_encoder(act[:, -history_size:])
                pred = model.predict(emb[:, -history_size:], act_emb)[:, -1]
                preds.append(pred)
                emb = torch.cat([emb, pred[:, None, :]], dim=1)
                act = torch.cat([act, future_act[:, step : step + 1]], dim=1)
            pred_stack = torch.stack(preds, dim=1)
            err = torch.mean((pred_stack - true) ** 2, dim=-1)
            out[lo:hi] = err.detach().cpu().numpy().astype(np.float64)
    return out


def allocation_uniform(anchors_by_ep: dict[int, list[int]]) -> np.ndarray:
    h = np.zeros(sum(len(v) for v in anchors_by_ep.values()), dtype=np.int64)
    for idxs in anchors_by_ep.values():
        h[np.asarray(idxs, dtype=np.int64)] = UNIFORM_H
    return h


def allocation_by_score(
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    score: np.ndarray,
) -> np.ndarray:
    h = np.zeros(len(anchors), dtype=np.int64)
    for idxs in anchors_by_ep.values():
        ordered = sorted(idxs, key=lambda i: (float(score[i]), anchors[i]["t0"], anchors[i]["row_idx"]))
        n = len(ordered)
        half = n // 2
        low = ordered[:half]
        high = ordered[n - half :]
        h[np.asarray(low, dtype=np.int64)] = LOW_H
        h[np.asarray(high, dtype=np.int64)] = HIGH_H
        if n % 2:
            h[ordered[half]] = MID_H
        if int(h[np.asarray(idxs, dtype=np.int64)].sum()) != UNIFORM_H * n:
            raise RuntimeError("episode allocation budget mismatch")
    return h


def summarize_allocation(
    name: str,
    h: np.ndarray,
    errors_h5: np.ndarray,
    anchors: list[dict[str, Any]],
) -> dict[str, Any]:
    anchor_error = np.asarray([float(errors_h5[i, : h_i].sum()) for i, h_i in enumerate(h)], dtype=np.float64)
    emitted_steps = int(h.sum())
    total_error = float(anchor_error.sum())
    per_step = float(total_error / emitted_steps)

    by_ep: dict[int, float] = defaultdict(float)
    steps_by_ep: dict[int, int] = defaultdict(int)
    for i, anchor in enumerate(anchors):
        ep = int(anchor["episode"])
        by_ep[ep] += float(anchor_error[i])
        steps_by_ep[ep] += int(h[i])
    episode_total = {str(ep): float(v) for ep, v in sorted(by_ep.items())}
    episode_steps = {str(ep): int(v) for ep, v in sorted(steps_by_ep.items())}
    return {
        "name": name,
        "anchors": int(len(h)),
        "emitted_steps": emitted_steps,
        "mean_h": float(np.mean(h)),
        "h_counts": {str(int(k)): int(v) for k, v in zip(*np.unique(h, return_counts=True))},
        "total_error": total_error,
        "per_emitted_step_mse": per_step,
        "episode_total_error_mean": float(np.mean(list(by_ep.values()))),
        "episode_total_error": episode_total,
        "episode_emitted_steps": episode_steps,
    }


def paired_bootstrap_delta(
    ledger_ep_error: dict[str, float],
    uniform_ep_error: dict[str, float],
    ledger_ep_steps: dict[str, int],
    uniform_ep_steps: dict[str, int],
) -> dict[str, float]:
    eps = sorted(uniform_ep_error.keys(), key=int)
    if eps != sorted(ledger_ep_error.keys(), key=int):
        raise RuntimeError("episode keys do not match for paired bootstrap")
    diff_ep = np.asarray([ledger_ep_error[ep] - uniform_ep_error[ep] for ep in eps], dtype=np.float64)
    ledger_err = np.asarray([ledger_ep_error[ep] for ep in eps], dtype=np.float64)
    uniform_err = np.asarray([uniform_ep_error[ep] for ep in eps], dtype=np.float64)
    ledger_steps = np.asarray([ledger_ep_steps[ep] for ep in eps], dtype=np.float64)
    uniform_steps = np.asarray([uniform_ep_steps[ep] for ep in eps], dtype=np.float64)
    observed = float(ledger_err.sum() / ledger_steps.sum() - uniform_err.sum() / uniform_steps.sum())

    rng = np.random.default_rng(ROLLOUT_BOOTSTRAP_SEED)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for b in range(BOOTSTRAPS):
        idx = rng.integers(0, len(eps), size=len(eps))
        samples[b] = float(ledger_err[idx].sum() / ledger_steps[idx].sum() - uniform_err[idx].sum() / uniform_steps[idx].sum())
    return {
        "observed": observed,
        "episode_total_error_difference_mean": float(diff_ep.mean()),
        "bootstrap_mean": float(np.mean(samples)),
        "ci95_low": float(np.percentile(samples, 2.5)),
        "ci95_high": float(np.percentile(samples, 97.5)),
        "seed": ROLLOUT_BOOTSTRAP_SEED,
        "resamples": BOOTSTRAPS,
    }


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# Ledger-gated rollout",
        "",
        f"- latent: `tworooms_latent_large.npz`; model: `{MODEL_REPO}`",
        f"- h=1 anchor max abs delta vs `prediction_mse`: `{report['anchors']['h1_prediction_mse_max_abs_delta']:.8g}`",
        f"- conclusion: **{report['conclusion']['claim']}** - {report['conclusion']['summary']}",
        "",
        "| allocation | anchors | emitted steps | mean h | per emitted-step MSE | episode total error mean |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ("uniform", "ledger", "oracle"):
        m = report["allocations"][name]
        lines.append(
            f"| `{name}` | {m['anchors']} | {m['emitted_steps']} | {m['mean_h']:.6f} | "
            f"{m['per_emitted_step_mse']:.9f} | {m['episode_total_error_mean']:.9f} |"
        )
    d = report["paired_delta_ledger_minus_uniform_per_step_mse"]
    lines.extend(
        [
            "",
            "## Paired Delta",
            "",
            f"- delta = ledger - uniform per emitted-step MSE: `{d['observed']:.9f}`",
            f"- episode bootstrap 95% CI, {d['resamples']} resamples, seed {d['seed']}: "
            f"`[{d['ci95_low']:.9f}, {d['ci95_high']:.9f}]`",
            "",
            "## Oracle Ceiling",
            "",
            f"- oracle per emitted-step MSE: `{report['allocations']['oracle']['per_emitted_step_mse']:.9f}`",
            f"- oracle - uniform per emitted-step MSE: "
            f"`{report['oracle_minus_uniform_per_step_mse']:.9f}`",
            "",
            "## Not Claimed",
            "",
            "- This reports prediction budget allocation only.",
            "- It does not claim planning or control benefit.",
            "- It uses one checkpoint and one latent export.",
            "",
        ]
    )
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    np.random.seed(0)
    torch.manual_seed(0)
    torch.set_num_threads(1)
    REPORT_DIR.mkdir(exist_ok=True)
    device = torch.device("cpu")

    data = load_data()
    rows = flatten_transition_rows(data)
    protocol = fit_clean_protocol(data, rows)
    train_clean = materialize_clean_split(protocol, rows, "train")
    eval_clean = materialize_clean_split(protocol, rows, "eval")
    clean_head, clean_fit = fit_gap_head_for_parts([train_clean])
    clean_eval_gap_score, _ = predict_logistic_head(clean_head, eval_clean["x"])

    phase2c = json.loads((REPORT_DIR / "lewm_ood_aware_gap.json").read_text(encoding="utf-8"))
    target_auroc = float(phase2c["arms"]["clean_only"]["clean_eval"]["observed"]["failure_detection_auroc"])
    observed_auroc = float(protocol["clean_eval_metrics"]["failure_detection_auroc"]["observed"])
    if abs(observed_auroc - target_auroc) > 1e-9:
        raise RuntimeError(
            f"clean eval AUROC anchor failed: observed={observed_auroc:.17g}, target={target_auroc:.17g}"
        )

    row_to_gap_score = {int(row): float(score) for row, score in zip(eval_clean["row_idx"], clean_eval_gap_score)}
    anchors = build_anchor_rows(data, rows, protocol["splits_ep"]["eval"], row_to_gap_score)
    history_size = int(data["history_size"])

    model, config, checkpoint_path, config_path = load_predictor(device)
    errors_h5 = rollout_errors_for_horizon(
        model,
        data,
        anchors,
        device=device,
        history_size=history_size,
        horizon=HORIZON_FOR_BUDGET,
    )
    npz_h1 = np.asarray([data["prediction_mse"][int(a["episode"]), int(a["t0"])] for a in anchors], dtype=np.float64)
    max_delta = float(np.max(np.abs(errors_h5[:, 0] - npz_h1))) if len(anchors) else float("nan")
    if not np.isfinite(max_delta) or max_delta >= ANCHOR_TOL:
        report = {
            "status": "stopped_anchor_failed",
            "reason": "h=1 rollout errors did not match npz prediction_mse",
            "h1_prediction_mse_max_abs_delta": max_delta,
            "tolerance": ANCHOR_TOL,
            "anchors_checked": int(len(anchors)),
        }
        JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text(
            "# Ledger-gated rollout\n\n"
            f"Stopped: h=1 anchor failed. max |delta| = `{max_delta:.9g}`, tolerance = `{ANCHOR_TOL}`.\n",
            encoding="utf-8",
        )
        raise SystemExit(f"h=1 anchor failed: max_delta={max_delta:.9g}")

    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)

    uniform_h = allocation_uniform(anchors_by_ep)
    ledger_score = np.asarray([a["gap_score"] for a in anchors], dtype=np.float64)
    oracle_score = np.mean(errors_h5, axis=1)
    ledger_h = allocation_by_score(anchors, anchors_by_ep, ledger_score)
    oracle_h = allocation_by_score(anchors, anchors_by_ep, oracle_score)

    allocations = {
        "uniform": summarize_allocation("uniform", uniform_h, errors_h5, anchors),
        "ledger": summarize_allocation("ledger", ledger_h, errors_h5, anchors),
        "oracle": summarize_allocation("oracle", oracle_h, errors_h5, anchors),
    }
    delta = paired_bootstrap_delta(
        allocations["ledger"]["episode_total_error"],
        allocations["uniform"]["episode_total_error"],
        allocations["ledger"]["episode_emitted_steps"],
        allocations["uniform"]["episode_emitted_steps"],
    )
    claim = "positive" if delta["ci95_high"] < 0.0 else "negative_or_inconclusive"
    summary = (
        "ledger-guided allocation has a paired episode-bootstrap CI entirely below zero"
        if claim == "positive"
        else "ledger-guided allocation did not establish a paired CI entirely below zero"
    )

    report = {
        "status": "ok",
        "protocol": "ledger-gated rollout budget allocation, same total budget as uniform, eval split only",
        "model": {
            "repo": MODEL_REPO,
            "checkpoint_path": checkpoint_path,
            "config_path": config_path,
            "config_history_size": int(config["predictor"]["num_frames"]),
            "npz_history_size": history_size,
        },
        "split": {
            "seed": 1701,
            "eval_episode_count": int(len(protocol["splits_ep"]["eval"])),
            "eval_transition_rows": int(protocol["split_masks"]["eval"].sum()),
        },
        "anchors": {
            "count": int(len(anchors)),
            "definition": "eval episodes, t0 >= history_size-1, t0+5 <= valid transition count",
            "h1_prediction_mse_max_abs_delta": max_delta,
            "h1_prediction_mse_tolerance": ANCHOR_TOL,
        },
        "gap_head_anchor": {
            "source": "clean_only gap head rebuilt with materialize_clean_split + fit_gap_head_for_parts",
            "clean_fit": clean_fit,
            "clean_eval_auroc_observed": observed_auroc,
            "phase2c_report_clean_eval_auroc_observed": target_auroc,
            "abs_delta": abs(observed_auroc - target_auroc),
            "tolerance": 1e-9,
        },
        "allocation_rule": {
            "uniform": "h=3 for every anchor",
            "ledger": "within each episode, lower gap-score half h=5, higher gap-score half h=1, odd median h=3",
            "oracle": "same 5/1/3 rule, sorted by true h=5 mean per-step rollout error",
        },
        "allocations": allocations,
        "paired_delta_ledger_minus_uniform_per_step_mse": delta,
        "oracle_minus_uniform_per_step_mse": float(
            allocations["oracle"]["per_emitted_step_mse"] - allocations["uniform"]["per_emitted_step_mse"]
        ),
        "conclusion": {
            "claim": claim,
            "summary": summary,
            "positive_rule": "positive iff paired episode-bootstrap CI for delta=ledger-uniform is entirely < 0",
            "not_claimed": [
                "planning benefit",
                "control benefit",
                "multi-checkpoint generality",
                "multi-export generality",
            ],
        },
        "bootstrap": {
            "resamples": BOOTSTRAPS,
            "seed": ROLLOUT_BOOTSTRAP_SEED,
            "unit": "eval episodes",
        },
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(report)
    print(json.dumps(clean_json(report["conclusion"]), indent=2, ensure_ascii=False))
    print(f"wrote {JSON_PATH}")
    print(f"wrote {MD_PATH}")


if __name__ == "__main__":
    main()

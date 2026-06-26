from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn.functional as F

import _compute_value_model as cvm
import _compute_value_policy as cvp


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_tail_policy.json"
DEFAULT_MD = REPORT_DIR / "compute_value_tail_policy.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_tail_policy_predictions.npz"
DEFAULT_BASELINE = REPORT_DIR / "compute_value_policy_stability_predictions.npz"


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def parse_int_list(raw: str) -> list[int]:
    out = [int(item.strip()) for item in raw.split(",") if item.strip()]
    if not out:
        raise ValueError("empty integer list")
    return out


def episode_oracle_gain(payload: dict[str, np.ndarray]) -> dict[int, float]:
    oracle_score = cvp.rank_target(payload)
    oracle_choice = choice_from_score(payload, oracle_score)
    oracle_error = payload["option_error"][np.arange(len(oracle_choice)), oracle_choice]
    oracle_steps = cvm.OPTION_DEPTHS[oracle_choice].astype(np.float64)
    uniform_error = payload["uniform_error"]
    uniform_steps = np.full(len(oracle_choice), cvm.UNIFORM_DEPTH, dtype=np.float64)
    gains: dict[int, float] = {}
    for idxs in cvm.episode_groups(payload["episode"]):
        ep = int(payload["episode"][idxs[0]])
        oracle_rate = float(np.sum(oracle_error[idxs]) / np.sum(oracle_steps[idxs]))
        uniform_rate = float(np.sum(uniform_error[idxs]) / np.sum(uniform_steps[idxs]))
        gains[ep] = max(0.0, uniform_rate - oracle_rate)
    return gains


def choice_from_score(payload: dict[str, np.ndarray], score: np.ndarray) -> np.ndarray:
    predicted_mv = cvp.scalar_to_predicted_mv(score.astype(np.float64))
    chosen, _ = cvm.balanced_depth_choice(payload["episode"], predicted_mv)
    return chosen


def episode_weights(payload: dict[str, np.ndarray], *, gamma: float, cap: float) -> np.ndarray:
    gains = episode_oracle_gain(payload)
    values = np.asarray([gains[int(ep)] for ep in payload["episode"]], dtype=np.float64)
    positive = values[values > 0.0]
    scale = float(np.median(positive)) if len(positive) else 1.0
    if scale < 1.0e-8:
        scale = 1.0
    weights = 1.0 + gamma * values / scale
    return np.clip(weights, 1.0, cap).astype(np.float32)


def pair_groups(payload: dict[str, np.ndarray], labels: np.ndarray, weights: np.ndarray) -> list[tuple[np.ndarray, np.ndarray, float]]:
    groups: list[tuple[np.ndarray, np.ndarray, float]] = []
    for idxs in cvm.episode_groups(payload["episode"]):
        low = idxs[labels[idxs] == 0.0].astype(np.int64)
        high = idxs[labels[idxs] == 1.0].astype(np.int64)
        if len(low) and len(high):
            groups.append((low, high, float(np.mean(weights[idxs]))))
    return groups


def weighted_bce(logits: torch.Tensor, labels: torch.Tensor, weights: torch.Tensor) -> torch.Tensor:
    raw = F.binary_cross_entropy_with_logits(logits, labels, reduction="none")
    return torch.sum(raw * weights) / torch.clamp(torch.sum(weights), min=1.0)


def train_tail_policy(
    train_payload: dict[str, np.ndarray],
    cal_payload: dict[str, np.ndarray],
    x_train: np.ndarray,
    x_cal: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    epochs: int,
    batch: int,
    lr: float,
    gamma: float,
    cap: float,
) -> tuple[cvp.PolicyNet, dict[str, Any]]:
    torch.manual_seed(seed + 331)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 331)
    model = cvp.PolicyNet(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    train_labels, base_train_weights = cvp.top_bottom_labels(train_payload)
    cal_labels, cal_weights = cvp.top_bottom_labels(cal_payload)
    train_ep_weights = episode_weights(train_payload, gamma=gamma, cap=cap)
    train_weights = (base_train_weights * train_ep_weights).astype(np.float32)
    train_mask = train_labels >= 0.0
    cal_mask = cal_labels >= 0.0
    pairs = pair_groups(train_payload, train_labels, train_weights)

    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_labels.astype(np.float32)).to(device)
    w_t = torch.from_numpy(train_weights.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(cal_labels.astype(np.float32)).to(device)
    w_c = torch.from_numpy(cal_weights.astype(np.float32)).to(device)
    train_labeled = np.where(train_mask)[0].astype(np.int64)
    cal_labeled = torch.as_tensor(np.where(cal_mask)[0].astype(np.int64), dtype=torch.long, device=device)
    pair_probs = np.asarray([max(item[2], 1.0e-6) for item in pairs], dtype=np.float64)
    pair_probs /= float(np.sum(pair_probs))
    rng = np.random.default_rng(seed + 331)

    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    steps = max(1, math.ceil(len(train_labeled) / batch))

    for epoch in range(epochs):
        model.train()
        losses: list[float] = []
        for _ in range(steps):
            sample_probs = train_weights[train_labeled].astype(np.float64)
            sample_probs /= float(np.sum(sample_probs))
            idx = rng.choice(train_labeled, size=min(batch, len(train_labeled)), replace=len(train_labeled) < batch, p=sample_probs)
            idx_t = torch.as_tensor(idx, dtype=torch.long, device=device)
            cls_loss = weighted_bce(model(x_t[idx_t]), y_t[idx_t], w_t[idx_t])

            pair_low: list[int] = []
            pair_high: list[int] = []
            pair_w: list[float] = []
            while len(pair_low) < max(8, batch // 2):
                group_id = int(rng.choice(len(pairs), p=pair_probs))
                low, high, group_weight = pairs[group_id]
                pair_low.append(int(low[int(rng.integers(0, len(low)))]))
                pair_high.append(int(high[int(rng.integers(0, len(high)))]))
                pair_w.append(group_weight)
            low_t = torch.as_tensor(pair_low, dtype=torch.long, device=device)
            high_t = torch.as_tensor(pair_high, dtype=torch.long, device=device)
            pw_t = torch.as_tensor(pair_w, dtype=torch.float32, device=device)
            pair_raw = F.softplus(-(model(x_t[high_t]) - model(x_t[low_t])))
            pair_loss = torch.sum(pair_raw * pw_t) / torch.clamp(torch.sum(pw_t), min=1.0)
            loss = cls_loss + 0.75 * pair_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))

        model.eval()
        with torch.inference_mode():
            cal_logits = model(x_c[cal_labeled])
            cal_loss = float(weighted_bce(cal_logits, y_c[cal_labeled], w_c[cal_labeled]).detach().cpu())
        cal_score = cvp.predict(model, x_cal, device, batch)
        cal_eval = cvp.evaluate_score(cal_payload, cal_score, seed=seed + 1201)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), cal_loss)
        history.append(
            {
                "epoch": float(epoch + 1),
                "train": clean_float(float(np.mean(losses)) if losses else float("inf")),
                "cal_bce": clean_float(cal_loss),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_delta_observed": clean_float(float(delta["observed"])),
            }
        )
        if key < best_key:
            best_key = key
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
            best_report = {"epoch": epoch + 1, "calibration": cal_eval, "cal_bce": clean_float(cal_loss)}

    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "weighting": {
            "gamma": clean_float(gamma),
            "cap": clean_float(cap),
            "train_weight_mean": clean_float(float(np.mean(train_weights[train_mask]))),
            "train_weight_max": clean_float(float(np.max(train_weights[train_mask]))),
        },
    }


def baseline_score(path: Path) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        if "policy_score" in data.files:
            return data["policy_score"].astype(np.float64)
        predicted = data["predicted_mv"].astype(np.float64)
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return predicted[:, high_idx] - predicted[:, low_idx]


def selection_key(row: dict[str, Any]) -> tuple[float, float, int, int]:
    delta = row["calibration"]["allocation_delta"]
    return (float(delta["high"]), float(delta["observed"]), int(row["epochs"]), int(row["seed"]))


def write_npz(path: Path, payload: dict[str, np.ndarray], score: np.ndarray) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    predicted_mv = cvp.scalar_to_predicted_mv(score)
    np.savez_compressed(
        path,
        episode=payload["episode"].astype(np.int64),
        t0=payload["t0"].astype(np.int64),
        anchor_ep_t0=payload["anchor_ep_t0"].astype(np.int64),
        option_depths=cvm.OPTION_DEPTHS.astype(np.int64),
        option_steps=cvm.OPTION_DEPTHS.astype(np.float64),
        uniform_steps=payload["uniform_steps"].astype(np.float64),
        option_error=payload["option_error"].astype(np.float64),
        uniform_error=payload["uniform_error"].astype(np.float64),
        true_mv=payload["true_mv"].astype(np.float64),
        predicted_mv=predicted_mv.astype(np.float64),
        policy_score=score.astype(np.float64),
        model_name=np.asarray("tail_episode_policy", dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["selected_run"]
    sel = selected["eval"]["allocation_delta"]
    base = report["references"]["episode_policy"]["allocation_delta"]
    oracle = report["references"]["oracle"]["allocation_delta"]
    lines = [
        "# Compute-Value Tail Policy",
        "",
        f"- device: `{report['device']}`",
        f"- selected run: seed `{selected['seed']}`, epochs `{selected['epochs']}`",
        f"- selected eval allocation delta: `{sel['observed']:.9g}` `[{sel['low']:.9g}, {sel['high']:.9g}]`",
        f"- episode policy reference: `{base['observed']:.9g}` `[{base['low']:.9g}, {base['high']:.9g}]`",
        f"- oracle reference: `{oracle['observed']:.9g}` `[{oracle['low']:.9g}, {oracle['high']:.9g}]`",
        "",
        "| seed | epochs | cal delta | eval delta | eval rho |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in report["runs"]:
        cal = row["calibration"]["allocation_delta"]
        ev = row["eval"]["allocation_delta"]
        lines.append(
            f"| {row['seed']} | {row['epochs']} | {cal['observed']:.9g} [{cal['low']:.9g}, {cal['high']:.9g}] | "
            f"{ev['observed']:.9g} [{ev['low']:.9g}, {ev['high']:.9g}] | {row['eval']['mv_spearman']:.9g} |"
        )
    lines.extend(
        [
            "",
            "Episode weights are computed only from train-split oracle gains; run selection uses calibration allocation delta.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train tail-episode-aware compute-value policy")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", default="3,7,11")
    parser.add_argument("--epoch-budgets", default="5,20,100")
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    parser.add_argument("--gamma", type=float, default=2.0)
    parser.add_argument("--cap", type=float, default=8.0)
    args = parser.parse_args()

    start = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    labels_path = cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = cvm.load_npz(labels_path)
    latents = cvm.load_npz(latents_path)
    train = cvm.split_payload(labels, latents, "train")
    cal = cvm.split_payload(labels, latents, "calibration")
    eval_payload = cvm.split_payload(labels, latents, "eval")
    x_mean, x_scale = cvm.fit_standardizer(train["x"])
    x_train = cvm.apply_standardizer(train["x"], x_mean, x_scale)
    x_cal = cvm.apply_standardizer(cal["x"], x_mean, x_scale)
    x_eval = cvm.apply_standardizer(eval_payload["x"], x_mean, x_scale)

    runs: list[dict[str, Any]] = []
    scores: dict[tuple[int, int], np.ndarray] = {}
    for seed in parse_int_list(args.seeds):
        for epochs in parse_int_list(args.epoch_budgets):
            model, health = train_tail_policy(
                train,
                cal,
                x_train,
                x_cal,
                device=device,
                seed=seed,
                hidden=int(args.hidden),
                epochs=epochs,
                batch=int(args.batch),
                lr=float(args.lr),
                gamma=float(args.gamma),
                cap=float(args.cap),
            )
            cal_score = cvp.predict(model, x_cal, device, int(args.batch))
            eval_score = cvp.predict(model, x_eval, device, int(args.batch))
            scores[(seed, epochs)] = eval_score
            runs.append(
                {
                    "seed": int(seed),
                    "epochs": int(epochs),
                    "health": health,
                    "calibration": cvp.evaluate_score(cal, cal_score, seed=seed + 1409),
                    "eval": cvp.evaluate_score(eval_payload, eval_score, seed=seed + 1601),
                }
            )

    selected = min(runs, key=selection_key)
    selected_score = scores[(int(selected["seed"]), int(selected["epochs"]))]
    write_npz(Path(args.out), eval_payload, selected_score)
    oracle_score = cvp.rank_target(eval_payload)
    baseline_path = Path(args.baseline)
    episode_policy_score = baseline_score(baseline_path) if baseline_path.exists() else np.zeros(len(selected_score), dtype=np.float64)
    references = {
        "oracle": cvp.evaluate_score(eval_payload, oracle_score, seed=2001),
        "episode_policy": cvp.evaluate_score(eval_payload, episode_policy_score, seed=2003),
    }
    eval_observed = np.asarray([float(row["eval"]["allocation_delta"]["observed"]) for row in runs], dtype=np.float64)
    eval_high = np.asarray([float(row["eval"]["allocation_delta"]["high"]) for row in runs], dtype=np.float64)
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_tail_policy",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path), "baseline_prediction": str(baseline_path)},
        "grid": {
            "seeds": parse_int_list(args.seeds),
            "epoch_budgets": parse_int_list(args.epoch_budgets),
            "hidden": int(args.hidden),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "gamma": float(args.gamma),
            "cap": float(args.cap),
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "selection_rule": "minimize calibration allocation_delta CI high, then observed delta",
        "selected_run": selected,
        "summary": {
            "runs": int(len(runs)),
            "eval_delta_observed_min": clean_float(float(np.min(eval_observed))),
            "eval_delta_observed_median": clean_float(float(np.median(eval_observed))),
            "eval_delta_observed_max": clean_float(float(np.max(eval_observed))),
            "eval_delta_high_min": clean_float(float(np.min(eval_high))),
            "eval_delta_high_max": clean_float(float(np.max(eval_high))),
            "runs_with_eval_ci_high_below_zero": int(np.sum(eval_high < 0.0)),
        },
        "references": references,
        "runs": runs,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "episode_weights": "computed from train split oracle gains only",
            "run_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after policy scores are produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(
        json.dumps(
            clean_json({"selected": selected["eval"], "summary": report["summary"], "oracle": references["oracle"]}),
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

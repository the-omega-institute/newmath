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
DEFAULT_JSON = REPORT_DIR / "compute_value_budget_surrogate.json"
DEFAULT_MD = REPORT_DIR / "compute_value_budget_surrogate.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_budget_surrogate_predictions.npz"
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


def low_mid_high_indices() -> tuple[int, int, int]:
    low = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    mid = int(np.where(cvm.OPTION_DEPTHS == cvm.UNIFORM_DEPTH)[0][0])
    high = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return low, mid, high


def episode_index_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [idx.astype(np.int64) for idx in cvm.episode_groups(episode.astype(np.int64)) if len(idx) >= 2]


def soft_budget_loss(
    score: torch.Tensor,
    option_error: torch.Tensor,
    groups: list[np.ndarray],
    *,
    tau: float,
    tail_beta: float,
) -> torch.Tensor:
    low_idx, mid_idx, high_idx = low_mid_high_indices()
    losses: list[torch.Tensor] = []
    for idxs_np in groups:
        idxs = torch.as_tensor(idxs_np, dtype=torch.long, device=score.device)
        s = score[idxs]
        n = int(idxs.numel())
        half = n // 2
        if half == 0:
            continue
        probs_high = torch.softmax(s / tau, dim=0)
        probs_low = torch.softmax(-s / tau, dim=0)
        soft_error = torch.sum(probs_high * option_error[idxs, high_idx]) + torch.sum(probs_low * option_error[idxs, low_idx])
        soft_steps = float(cvm.OPTION_DEPTHS[high_idx] + cvm.OPTION_DEPTHS[low_idx])
        if n % 2:
            center = torch.softmax(-torch.abs(s - torch.median(s.detach())) / tau, dim=0)
            soft_error = soft_error + torch.sum(center * option_error[idxs, mid_idx])
            soft_steps += float(cvm.OPTION_DEPTHS[mid_idx])
        loss = soft_error / soft_steps
        if tail_beta > 0.0:
            with torch.no_grad():
                uniform_rate = torch.mean(option_error[idxs, mid_idx] / float(cvm.UNIFORM_DEPTH))
                tail_weight = torch.clamp(uniform_rate - loss.detach(), min=0.0)
            loss = loss * (1.0 + tail_beta * tail_weight)
        losses.append(loss)
    if not losses:
        return torch.mean(score * 0.0)
    return torch.stack(losses).mean()


def true_rank_target(payload: dict[str, np.ndarray]) -> np.ndarray:
    low_idx, _, high_idx = low_mid_high_indices()
    return (payload["true_mv"][:, high_idx] - payload["true_mv"][:, low_idx]).astype(np.float32)


def train_surrogate(
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
    tau: float,
    tail_beta: float,
    rank_weight: float,
) -> tuple[cvp.PolicyNet, dict[str, Any]]:
    torch.manual_seed(seed + 501)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 501)
    model = cvp.PolicyNet(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    option_error_t = torch.from_numpy(train_payload["option_error"].astype(np.float32)).to(device)
    groups = episode_index_groups(train_payload["episode"])
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    rank_target = torch.from_numpy(true_rank_target(train_payload)).to(device)
    pair_groups = [idx for idx in groups if len(idx) >= 2]
    rng = np.random.default_rng(seed + 501)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []

    for epoch in range(epochs):
        model.train()
        losses: list[float] = []
        order = rng.permutation(len(groups))
        for start in range(0, len(order), max(1, batch // 32)):
            batch_groups = [groups[int(i)] for i in order[start : start + max(1, batch // 32)]]
            score = model(x_t)
            loss = soft_budget_loss(score, option_error_t, batch_groups, tau=tau, tail_beta=tail_beta)
            if rank_weight > 0.0 and pair_groups:
                pair_i: list[int] = []
                pair_j: list[int] = []
                while len(pair_i) < min(batch, 512):
                    group = pair_groups[int(rng.integers(0, len(pair_groups)))]
                    a, b = rng.choice(group, size=2, replace=False)
                    if float(rank_target[int(a)]) == float(rank_target[int(b)]):
                        continue
                    pair_i.append(int(a))
                    pair_j.append(int(b))
                i_t = torch.as_tensor(pair_i, dtype=torch.long, device=device)
                j_t = torch.as_tensor(pair_j, dtype=torch.long, device=device)
                sign = torch.sign(rank_target[i_t] - rank_target[j_t])
                score_all = model(x_t)
                rank_loss = F.softplus(-sign * (score_all[i_t] - score_all[j_t])).mean()
                loss = loss + rank_weight * rank_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))

        model.eval()
        cal_score = cvp.predict(model, x_cal, device, batch)
        cal_eval = cvp.evaluate_score(cal_payload, cal_score, seed=seed + 1801)
        delta = cal_eval["allocation_delta"]
        train_loss = float(np.mean(losses)) if losses else float("inf")
        key = (float(delta["high"]), float(delta["observed"]), train_loss)
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_surrogate": clean_float(train_loss),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_delta_observed": clean_float(float(delta["observed"])),
            }
        )
        if key < best_key:
            best_key = key
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
            best_report = {"epoch": epoch + 1, "calibration": cal_eval, "train_surrogate": clean_float(train_loss)}

    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "surrogate": {"tau": clean_float(tau), "tail_beta": clean_float(tail_beta), "rank_weight": clean_float(rank_weight)},
    }


def baseline_score(path: Path) -> np.ndarray:
    with np.load(path, allow_pickle=False) as data:
        if "policy_score" in data.files:
            return data["policy_score"].astype(np.float64)
        predicted = data["predicted_mv"].astype(np.float64)
    low_idx, _, high_idx = low_mid_high_indices()
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
        model_name=np.asarray("budget_surrogate_policy", dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    selected = report["selected_run"]
    sel = selected["eval"]["allocation_delta"]
    base = report["references"]["episode_policy"]["allocation_delta"]
    oracle = report["references"]["oracle"]["allocation_delta"]
    lines = [
        "# Compute-Value Budget Surrogate",
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
            "The training loss uses train-split option errors inside a soft balanced-depth surrogate; run selection uses calibration allocation delta.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a budget-feasible compute-value policy surrogate")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seeds", default="3,7,11")
    parser.add_argument("--epoch-budgets", default="5,20,60")
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    parser.add_argument("--tau", type=float, default=0.25)
    parser.add_argument("--tail-beta", type=float, default=0.0)
    parser.add_argument("--rank-weight", type=float, default=0.1)
    args = parser.parse_args()

    start_time = time.time()
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
            model, health = train_surrogate(
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
                tau=float(args.tau),
                tail_beta=float(args.tail_beta),
                rank_weight=float(args.rank_weight),
            )
            cal_score = cvp.predict(model, x_cal, device, int(args.batch))
            eval_score = cvp.predict(model, x_eval, device, int(args.batch))
            scores[(seed, epochs)] = eval_score
            runs.append(
                {
                    "seed": int(seed),
                    "epochs": int(epochs),
                    "health": health,
                    "calibration": cvp.evaluate_score(cal, cal_score, seed=seed + 2201),
                    "eval": cvp.evaluate_score(eval_payload, eval_score, seed=seed + 2401),
                }
            )

    selected = min(runs, key=selection_key)
    selected_score = scores[(int(selected["seed"]), int(selected["epochs"]))]
    write_npz(Path(args.out), eval_payload, selected_score)
    oracle_score = cvp.rank_target(eval_payload)
    baseline_path = Path(args.baseline)
    episode_policy_score = baseline_score(baseline_path) if baseline_path.exists() else np.zeros(len(selected_score), dtype=np.float64)
    references = {
        "oracle": cvp.evaluate_score(eval_payload, oracle_score, seed=2601),
        "episode_policy": cvp.evaluate_score(eval_payload, episode_policy_score, seed=2603),
    }
    eval_observed = np.asarray([float(row["eval"]["allocation_delta"]["observed"]) for row in runs], dtype=np.float64)
    eval_high = np.asarray([float(row["eval"]["allocation_delta"]["high"]) for row in runs], dtype=np.float64)
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_budget_surrogate",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path), "baseline_prediction": str(baseline_path)},
        "grid": {
            "seeds": parse_int_list(args.seeds),
            "epoch_budgets": parse_int_list(args.epoch_budgets),
            "hidden": int(args.hidden),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "tau": float(args.tau),
            "tail_beta": float(args.tail_beta),
            "rank_weight": float(args.rank_weight),
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
            "training_truth_usage": "train option errors used only inside train-split budget surrogate",
            "run_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after policy scores are produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start_time),
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

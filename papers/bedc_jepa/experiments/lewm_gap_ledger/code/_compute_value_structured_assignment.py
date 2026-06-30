from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _compute_value_model as cvm
import _compute_value_option_set as optset
import _compute_value_refined_option_model as refined


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_structured_assignment.json"
DEFAULT_MD = REPORT_DIR / "compute_value_structured_assignment.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_structured_assignment_predictions.npz"
REFINED_PRED = REPORT_DIR / "compute_value_refined_option_model_predictions.npz"
POLICY_PRED = REPORT_DIR / "compute_value_policy_stability_predictions.npz"
DEPTHS = refined.DEPTHS


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


def option_features(depths: np.ndarray) -> np.ndarray:
    d = depths.astype(np.float32)
    centered = (d - 3.0) / 2.0
    return np.stack(
        [
            centered,
            centered * centered,
            (d < 3.0).astype(np.float32),
            (d == 3.0).astype(np.float32),
            (d > 3.0).astype(np.float32),
        ],
        axis=1,
    )


def expand_options(x: np.ndarray, depths: np.ndarray) -> np.ndarray:
    opt = option_features(depths)
    rows = np.repeat(x.astype(np.float32), len(depths), axis=0)
    tiled = np.tile(opt, (len(x), 1)).astype(np.float32)
    return np.concatenate([rows, tiled], axis=1).astype(np.float32)


def fit_standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    return cvm.fit_standardizer(x.astype(np.float32))


def standardize(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return cvm.apply_standardizer(x.astype(np.float32), mean, scale)


def train_ridge(expanded_x: np.ndarray, y: np.ndarray, *, alpha: float) -> tuple[np.ndarray, float]:
    x_aug = np.concatenate([expanded_x, np.ones((len(expanded_x), 1), dtype=np.float32)], axis=1).astype(np.float64)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    weights = np.linalg.solve(x_aug.T @ x_aug + alpha * eye, x_aug.T @ y.astype(np.float64))
    return weights[:-1].astype(np.float64), float(weights[-1])


def predict_ridge(expanded_x: np.ndarray, w: np.ndarray, b: float) -> np.ndarray:
    return (expanded_x.astype(np.float64) @ w + float(b)).astype(np.float64)


class OptionUtilityNet(nn.Module):
    def __init__(self, in_dim: int, hidden: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, hidden),
            nn.SiLU(),
            nn.LayerNorm(hidden),
            nn.Dropout(0.05),
            nn.Linear(hidden, hidden // 2),
            nn.SiLU(),
            nn.LayerNorm(hidden // 2),
            nn.Linear(hidden // 2, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def reshape_scores(flat: np.ndarray, n: int) -> np.ndarray:
    return flat.reshape(n, len(DEPTHS)).astype(np.float64)


def exact_budget_choice(episode: np.ndarray, option_score: np.ndarray, depths: np.ndarray) -> np.ndarray:
    chosen = np.zeros(len(episode), dtype=np.int64)
    for idxs in cvm.episode_groups(episode.astype(np.int64)):
        idxs = idxs.astype(np.int64)
        n = len(idxs)
        target = int(3 * n)
        dp = np.full((n + 1, target + 1), np.inf, dtype=np.float64)
        prev_budget = np.full((n + 1, target + 1), -1, dtype=np.int64)
        prev_choice = np.full((n + 1, target + 1), -1, dtype=np.int64)
        dp[0, 0] = 0.0
        for row, item in enumerate(idxs):
            for budget in range(target + 1):
                base = dp[row, budget]
                if not math.isfinite(float(base)):
                    continue
                for col, depth in enumerate(depths):
                    new_budget = budget + int(depth)
                    if new_budget > target:
                        continue
                    value = base + float(option_score[item, col])
                    if value < dp[row + 1, new_budget]:
                        dp[row + 1, new_budget] = value
                        prev_budget[row + 1, new_budget] = budget
                        prev_choice[row + 1, new_budget] = col
        if not math.isfinite(float(dp[n, target])):
            raise RuntimeError("exact budget assignment is infeasible")
        budget = target
        for row in range(n, 0, -1):
            col = int(prev_choice[row, budget])
            if col < 0:
                raise RuntimeError("broken exact budget traceback")
            chosen[idxs[row - 1]] = col
            budget = int(prev_budget[row, budget])
    return chosen


def evaluate_choice(payload: dict[str, np.ndarray], chosen: np.ndarray, *, seed: int) -> dict[str, Any]:
    return optset.evaluate(payload["episode"], payload["option_error"], DEPTHS, chosen.astype(np.int64), seed=seed)


def evaluate_scores(payload: dict[str, np.ndarray], option_score: np.ndarray, *, seed: int) -> dict[str, Any]:
    chosen = exact_budget_choice(payload["episode"], option_score.astype(np.float64), DEPTHS)
    metrics = evaluate_choice(payload, chosen, seed=seed)
    metrics["score_error_spearman"] = cvm.spearman(option_score.reshape(-1), payload["option_error"].reshape(-1))
    metrics["chosen_depth_counts"] = {str(int(k)): int(v) for k, v in zip(*np.unique(DEPTHS[chosen], return_counts=True))}
    return metrics


def exact_oracle(payload: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    chosen = exact_budget_choice(payload["episode"], payload["option_error"], DEPTHS)
    metrics = evaluate_choice(payload, chosen, seed=seed)
    metrics["score_error_spearman"] = 1.0
    metrics["chosen_depth_counts"] = {str(int(k)): int(v) for k, v in zip(*np.unique(DEPTHS[chosen], return_counts=True))}
    return metrics


def per_step_oracle(payload: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    choice = optset.oracle_choice(payload["option_error"], DEPTHS)
    metrics = evaluate_choice(payload, choice, seed=seed)
    metrics["score_error_spearman"] = 1.0
    return metrics


def balanced_policy_reference(payload: dict[str, np.ndarray], policy_path: Path, *, seed: int) -> dict[str, Any]:
    with np.load(policy_path, allow_pickle=False) as data:
        score = data["policy_score"].astype(np.float64)
    choice = optset.balanced_choice(payload["episode"], score, DEPTHS)
    metrics = evaluate_choice(payload, choice, seed=seed)
    target = optset.target_score(payload["option_error"], DEPTHS)
    metrics["policy_target_spearman"] = cvm.spearman(score, target)
    return metrics


def refined_reference(payload: dict[str, np.ndarray], refined_path: Path, *, seed: int) -> dict[str, Any]:
    with np.load(refined_path, allow_pickle=False) as data:
        predicted_mv = data["predicted_mv"].astype(np.float64)
    return evaluate_scores(payload, -predicted_mv, seed=seed)


def train_mlp(
    x_train: np.ndarray,
    y_train: np.ndarray,
    train_option_error: np.ndarray,
    x_cal: np.ndarray,
    y_cal: np.ndarray,
    cal_payload: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[OptionUtilityNet, dict[str, Any]]:
    torch.manual_seed(seed + 907)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 907)
    model = OptionUtilityNet(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(y_train.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(y_cal.astype(np.float32)).to(device)
    true_rank = torch.from_numpy(train_option_error.astype(np.float32)).to(device)
    rng = np.random.default_rng(seed + 907)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n_train = train_option_error.shape[0]
    flat_count = len(x_train)
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(flat_count)
        losses: list[float] = []
        for start in range(0, flat_count, batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            point_loss = F.smooth_l1_loss(pred, y_t[idx])
            anchors = rng.integers(0, n_train, size=max(8, batch // len(DEPTHS)))
            pair_rows = torch.as_tensor(anchors, dtype=torch.long, device=device)
            base = pair_rows * len(DEPTHS)
            pred_options = torch.stack([model(x_t[base + j]) for j in range(len(DEPTHS))], dim=1)
            diff_pred = pred_options[:, :, None] - pred_options[:, None, :]
            diff_true = true_rank[pair_rows, :, None] - true_rank[pair_rows, None, :]
            sign = torch.sign(diff_true)
            mask = torch.abs(diff_true) > 1.0e-6
            rank_loss = F.softplus(-sign[mask] * diff_pred[mask]).mean() if torch.any(mask) else point_loss * 0.0
            loss = point_loss + 0.25 * rank_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        model.eval()
        with torch.inference_mode():
            cal_pred = model(x_c)
            cal_loss = float(F.smooth_l1_loss(cal_pred, y_c).detach().cpu())
        cal_scores = reshape_scores(predict_mlp(model, x_cal, device, batch), len(cal_payload["episode"]))
        cal_eval = evaluate_scores(cal_payload, cal_scores, seed=seed + 409)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), cal_loss)
        history.append(
            {
                "epoch": float(epoch + 1),
                "train": clean_float(float(np.mean(losses))),
                "cal_smooth_l1": clean_float(cal_loss),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_delta_observed": clean_float(float(delta["observed"])),
            }
        )
        if key < best_key:
            best_key = key
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
            best_report = {"epoch": int(epoch + 1), "calibration": cal_eval, "cal_smooth_l1": clean_float(cal_loss)}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta, then smooth L1",
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def predict_mlp(model: OptionUtilityNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def write_npz(path: Path, payload: dict[str, np.ndarray], option_score: np.ndarray, chosen: np.ndarray, model_name: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        episode=payload["episode"].astype(np.int64),
        t0=payload["t0"].astype(np.int64),
        anchor_ep_t0=payload["anchor_ep_t0"].astype(np.int64),
        option_depths=DEPTHS.astype(np.int64),
        option_error=payload["option_error"].astype(np.float64),
        uniform_error=payload["uniform_error"].astype(np.float64),
        true_mv=payload["true_mv"].astype(np.float64),
        predicted_option_score=option_score.astype(np.float64),
        chosen_depth=DEPTHS[chosen].astype(np.int64),
        chosen_col=chosen.astype(np.int64),
        model_name=np.asarray(model_name, dtype=np.str_),
    )


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# Compute-Value Structured Assignment",
        "",
        f"- selected model: `{report['selected_model']}`",
        f"- device: `{report['device']}`",
        f"- eval anchors: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        "",
        "| policy | allocation delta | score/error rho |",
        "|---|---:|---:|",
    ]
    for name in ["exact_budget_oracle", "learned_structured", "ridge_structured", "refined_mv_dp", "policy_score_balanced", "per_step_oracle"]:
        row = rows[name]
        d = row["allocation_delta"]
        rho = row.get("score_error_spearman", row.get("policy_target_spearman", 0.0))
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {rho:.9g} |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an option-conditioned exact-budget compute-value assignment model")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--epochs", type=int, default=420)
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    labels_path = cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = cvm.load_npz(labels_path)
    latents = cvm.load_npz(latents_path)
    train = refined.split_payload(labels, latents, "train")
    cal = refined.split_payload(labels, latents, "calibration")
    eval_payload = refined.split_payload(labels, latents, "eval")
    x_mean, x_scale = fit_standardizer(train["x"])
    x_train = standardize(train["x"], x_mean, x_scale)
    x_cal = standardize(cal["x"], x_mean, x_scale)
    x_eval = standardize(eval_payload["x"], x_mean, x_scale)
    ex_train = expand_options(x_train, DEPTHS)
    ex_cal = expand_options(x_cal, DEPTHS)
    ex_eval = expand_options(x_eval, DEPTHS)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    y_train = ((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    y_cal = ((cal["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)

    ridge_w, ridge_b = train_ridge(ex_train, y_train, alpha=10.0)
    ridge_cal = reshape_scores(predict_ridge(ex_cal, ridge_w, ridge_b) * y_scale + y_mean, len(cal["episode"]))
    ridge_eval = reshape_scores(predict_ridge(ex_eval, ridge_w, ridge_b) * y_scale + y_mean, len(eval_payload["episode"]))
    ridge_cal_metrics = evaluate_scores(cal, ridge_cal, seed=int(args.seed) + 211)

    mlp, health = train_mlp(
        ex_train,
        y_train,
        train["option_error"],
        ex_cal,
        y_cal,
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    learned_eval = reshape_scores(predict_mlp(mlp, ex_eval, device, int(args.batch)) * y_scale + y_mean, len(eval_payload["episode"]))
    learned_metrics = evaluate_scores(eval_payload, learned_eval, seed=int(args.seed) + 307)
    learned_choice = exact_budget_choice(eval_payload["episode"], learned_eval, DEPTHS)
    write_npz(Path(args.out), eval_payload, learned_eval, learned_choice, "option_conditioned_exact_budget")

    eval_rows = {
        "exact_budget_oracle": exact_oracle(eval_payload, seed=int(args.seed) + 311),
        "learned_structured": learned_metrics,
        "ridge_structured": evaluate_scores(eval_payload, ridge_eval, seed=int(args.seed) + 313),
        "refined_mv_dp": refined_reference(eval_payload, REFINED_PRED, seed=int(args.seed) + 317),
        "policy_score_balanced": balanced_policy_reference(eval_payload, POLICY_PRED, seed=int(args.seed) + 319),
        "per_step_oracle": per_step_oracle(eval_payload, seed=int(args.seed) + 323),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_structured_assignment",
        "selected_model": "option_conditioned_exact_budget",
        "device": str(device),
        "inputs": {
            "labels": str(labels_path),
            "latents": str(latents_path),
            "refined_prediction": str(REFINED_PRED),
            "policy_prediction": str(POLICY_PRED),
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "target": {
            "option_depths": DEPTHS.tolist(),
            "assignment_rule": "exact per-episode budget sum(depth)=3*episode_anchor_count using dynamic programming",
            "learned_score": "predicted option error; lower score is selected by the DP",
        },
        "calibration": {
            "ridge_structured": ridge_cal_metrics,
            "learned_structured": health["best"]["calibration"],
        },
        "health": health,
        "eval": eval_rows,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "target_standardizer": "fit on train option_error only",
            "model_selection": "calibration split exact-budget allocation only",
            "eval_truth_usage": "eval option_error used only after predicted option scores are written for final metrics and references",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "eval": eval_rows}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

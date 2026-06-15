from __future__ import annotations

import argparse
import json
import math
import random
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _compute_value_model as cvm


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_policy.json"
DEFAULT_MD = REPORT_DIR / "compute_value_policy.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_policy_predictions.npz"
DEFAULT_BASELINE = REPORT_DIR / "compute_value_model_predictions.npz"
BOOTSTRAPS = 1000


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


def rank_target(payload: dict[str, np.ndarray]) -> np.ndarray:
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return (payload["true_mv"][:, high_idx] - payload["true_mv"][:, low_idx]).astype(np.float64)


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return cvm.episode_groups(episode.astype(np.int64))


def top_bottom_labels(payload: dict[str, np.ndarray]) -> tuple[np.ndarray, np.ndarray]:
    target = rank_target(payload)
    labels = np.full(len(target), -1.0, dtype=np.float32)
    weights = np.zeros(len(target), dtype=np.float32)
    for idxs in episode_groups(payload["episode"]):
        ordered = sorted((int(i) for i in idxs), key=lambda i: (float(target[i]), int(i)))
        n = len(ordered)
        half = n // 2
        if half == 0:
            continue
        low_set = np.asarray(ordered[:half], dtype=np.int64)
        high_set = np.asarray(ordered[n - half :], dtype=np.int64)
        labels[low_set] = 0.0
        labels[high_set] = 1.0
        lo_max = float(np.max(target[low_set]))
        hi_min = float(np.min(target[high_set]))
        margin = max(hi_min - lo_max, 1.0e-6)
        weights[low_set] = np.clip((lo_max - target[low_set]) / margin + 1.0, 1.0, 8.0)
        weights[high_set] = np.clip((target[high_set] - hi_min) / margin + 1.0, 1.0, 8.0)
    return labels, weights


def scalar_to_predicted_mv(score: np.ndarray) -> np.ndarray:
    predicted_mv = np.zeros((len(score), len(cvm.OPTION_DEPTHS)), dtype=np.float64)
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    predicted_mv[:, high_idx] = score.astype(np.float64)
    return predicted_mv


def write_prediction_npz(path: Path, payload: dict[str, np.ndarray], score: np.ndarray, model_name: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    predicted_mv = scalar_to_predicted_mv(score)
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
        model_name=np.asarray(model_name, dtype=np.str_),
    )


def baseline_from_npz(path: Path) -> tuple[np.ndarray, str]:
    with np.load(path, allow_pickle=False) as data:
        predicted_mv = data["predicted_mv"].astype(np.float64)
        model_name = str(data["model_name"].item())
    low_idx = int(np.where(cvm.OPTION_DEPTHS < cvm.UNIFORM_DEPTH)[0][0])
    high_idx = int(np.where(cvm.OPTION_DEPTHS > cvm.UNIFORM_DEPTH)[0][-1])
    return predicted_mv[:, high_idx] - predicted_mv[:, low_idx], model_name


class PolicyNet(nn.Module):
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


def pair_groups(payload: dict[str, np.ndarray], labels: np.ndarray) -> list[tuple[np.ndarray, np.ndarray]]:
    groups: list[tuple[np.ndarray, np.ndarray]] = []
    for idxs in episode_groups(payload["episode"]):
        low = idxs[labels[idxs] == 0.0].astype(np.int64)
        high = idxs[labels[idxs] == 1.0].astype(np.int64)
        if len(low) and len(high):
            groups.append((low, high))
    return groups


def weighted_bce(logits: torch.Tensor, labels: torch.Tensor, weights: torch.Tensor) -> torch.Tensor:
    raw = F.binary_cross_entropy_with_logits(logits, labels, reduction="none")
    return torch.sum(raw * weights) / torch.clamp(torch.sum(weights), min=1.0)


def predict(model: PolicyNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for lo in range(0, len(x), batch):
            hi = min(lo + batch, len(x))
            xb = torch.from_numpy(x[lo:hi].astype(np.float32)).to(device)
            out[lo:hi] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def train_policy(
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
) -> tuple[PolicyNet, dict[str, Any]]:
    torch.manual_seed(seed + 211)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 211)
    model = PolicyNet(x_train.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    train_labels, train_weights = top_bottom_labels(train_payload)
    cal_labels, cal_weights = top_bottom_labels(cal_payload)
    train_mask = train_labels >= 0.0
    cal_mask = cal_labels >= 0.0
    train_pairs = pair_groups(train_payload, train_labels)

    x_t = torch.from_numpy(x_train.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_labels.astype(np.float32)).to(device)
    w_t = torch.from_numpy(train_weights.astype(np.float32)).to(device)
    x_c = torch.from_numpy(x_cal.astype(np.float32)).to(device)
    y_c = torch.from_numpy(cal_labels.astype(np.float32)).to(device)
    w_c = torch.from_numpy(cal_weights.astype(np.float32)).to(device)
    train_labeled = np.where(train_mask)[0].astype(np.int64)
    cal_labeled = torch.as_tensor(np.where(cal_mask)[0].astype(np.int64), dtype=torch.long, device=device)
    rng = np.random.default_rng(seed + 211)

    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    steps = max(1, math.ceil(len(train_labeled) / batch))

    for epoch in range(epochs):
        model.train()
        losses: list[float] = []
        for _ in range(steps):
            idx = rng.choice(train_labeled, size=min(batch, len(train_labeled)), replace=len(train_labeled) < batch)
            idx_t = torch.as_tensor(idx, dtype=torch.long, device=device)
            logits = model(x_t[idx_t])
            cls_loss = weighted_bce(logits, y_t[idx_t], w_t[idx_t])

            pair_low: list[int] = []
            pair_high: list[int] = []
            while len(pair_low) < max(8, batch // 2):
                low, high = train_pairs[int(rng.integers(0, len(train_pairs)))]
                pair_low.append(int(low[int(rng.integers(0, len(low)))]))
                pair_high.append(int(high[int(rng.integers(0, len(high)))]))
            low_t = torch.as_tensor(pair_low, dtype=torch.long, device=device)
            high_t = torch.as_tensor(pair_high, dtype=torch.long, device=device)
            pair_loss = F.softplus(-(model(x_t[high_t]) - model(x_t[low_t]))).mean()
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
        cal_score = predict(model, x_cal, device, batch)
        cal_eval = cvm.evaluate_prediction(cal_payload, scalar_to_predicted_mv(cal_score), seed=seed + 503)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), cal_loss)
        train_loss = float(np.mean(losses)) if losses else float("inf")
        history.append(
            {
                "epoch": float(epoch + 1),
                "train": clean_float(train_loss),
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
        "selection_rule": "minimize calibration allocation_delta CI high, then observed delta, then weighted BCE",
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "labeled_train": int(np.sum(train_mask)),
        "labeled_calibration": int(np.sum(cal_mask)),
    }


def evaluate_score(payload: dict[str, np.ndarray], score: np.ndarray, seed: int) -> dict[str, Any]:
    return cvm.evaluate_prediction(payload, scalar_to_predicted_mv(score), seed=seed)


def random_reference(payload: dict[str, np.ndarray], seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(seed)
    score = rng.standard_normal(len(payload["episode"])).astype(np.float64)
    return evaluate_score(payload, score, seed=seed + 1)


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    eval_rows = report["eval"]
    lines = [
        "# Compute-Value Policy",
        "",
        f"- device: `{report['device']}`",
        f"- selected policy: `{report['selected_policy']}`",
        f"- train anchors: `{report['counts']['train']}`",
        f"- eval anchors: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        "",
        "| policy | allocation delta | MV Spearman |",
        "|---|---:|---:|",
    ]
    for name in ["oracle", "learned_policy", "scalar_ranknet", "inverted_oracle", "random_reference"]:
        row = eval_rows[name]
        delta = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {delta['observed']:.9g} [{delta['low']:.9g}, {delta['high']:.9g}] | {row['mv_spearman']:.9g} |"
        )
    lines.extend(
        [
            "",
            "The learned policy is trained on train episodes and selected on calibration episodes under the same balanced depth gate used for eval.",
            "Eval option errors are used only after the policy scores are written.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an episode-balanced compute-value policy scorer")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--baseline", default=str(DEFAULT_BASELINE))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--epochs", type=int, default=600)
    parser.add_argument("--batch", type=int, default=256)
    parser.add_argument("--hidden", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    random.seed(int(args.seed))
    np.random.seed(int(args.seed))
    torch.manual_seed(int(args.seed))
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(int(args.seed))
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

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

    model, health = train_policy(
        train,
        cal,
        x_train,
        x_cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    learned_score = predict(model, x_eval, device, int(args.batch))
    write_prediction_npz(Path(args.out), eval_payload, learned_score, "episode_balanced_policy")

    oracle_score = rank_target(eval_payload)
    baseline_path = Path(args.baseline)
    baseline_score, baseline_name = baseline_from_npz(baseline_path) if baseline_path.exists() else (np.zeros(len(learned_score)), "missing")
    eval_rows = {
        "oracle": evaluate_score(eval_payload, oracle_score, seed=int(args.seed) + 31),
        "learned_policy": evaluate_score(eval_payload, learned_score, seed=int(args.seed) + 37),
        "scalar_ranknet": evaluate_score(eval_payload, baseline_score, seed=int(args.seed) + 41),
        "inverted_oracle": evaluate_score(eval_payload, -oracle_score, seed=int(args.seed) + 43),
        "random_reference": random_reference(eval_payload, seed=int(args.seed) + 47),
    }

    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_policy",
        "selected_policy": "episode_balanced_policy",
        "device": str(device),
        "inputs": {
            "labels": str(labels_path),
            "latents": str(latents_path),
            "baseline_prediction": str(baseline_path),
            "baseline_model": baseline_name,
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "target": {
            "option_depths": cvm.OPTION_DEPTHS.tolist(),
            "uniform_depth": cvm.UNIFORM_DEPTH,
            "policy_label": "episode-local top half of true high-minus-low marginal value goes to depth 5; bottom half goes to depth 1",
        },
        "health": health,
        "eval": eval_rows,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "policy_labels": "constructed from train/cal true_mv only for training and calibration selection",
            "model_selection": "calibration split only",
            "eval_truth_usage": "eval option_error and true_mv used only after policy scores are written for final metrics and references",
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
            clean_json(
                {
                    "device": str(device),
                    "learned_policy": eval_rows["learned_policy"],
                    "oracle": eval_rows["oracle"],
                    "scalar_ranknet": eval_rows["scalar_ranknet"],
                }
            ),
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

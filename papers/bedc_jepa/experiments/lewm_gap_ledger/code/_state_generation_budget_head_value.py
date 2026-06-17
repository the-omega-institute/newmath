from __future__ import annotations

import argparse
import json
import math
import os
import random
import time
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _state_generation_budget_conditioned_value as conditioned_value
import _state_generation_budget_replacement_value as replacement_value
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_head_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_head_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_budget_head_value_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BUDGETS = np.asarray([2, 3, 4], dtype=np.int64)


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


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def configure(seed: int) -> torch.device:
    os.environ["PYTHONHASHSEED"] = str(seed)
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")


class BudgetHeadNet(nn.Module):
    def __init__(self, in_dim: int, hidden: int, depth: int, heads: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        dim = in_dim
        for _ in range(depth):
            blocks.extend([nn.Linear(dim, hidden), nn.SiLU(), nn.LayerNorm(hidden), nn.Dropout(0.05)])
            dim = hidden
        self.trunk = nn.Sequential(*blocks)
        self.heads = nn.ModuleList([nn.Linear(dim, 1) for _ in range(heads)])

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        h = self.trunk(x)
        return torch.stack([head(h).squeeze(-1) for head in self.heads], dim=1)


def predict(model: BudgetHeadNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros((len(x), len(BUDGETS)), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def reshape_scores(pred: np.ndarray, n: int, depths: np.ndarray) -> dict[int, np.ndarray]:
    out: dict[int, np.ndarray] = {}
    for head_index, budget in enumerate(BUDGETS.astype(np.int64)):
        out[int(budget)] = pred[:, head_index].reshape(n, len(depths)).astype(np.float64)
    return out


def train_model(
    train_x: np.ndarray,
    train_targets: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    depths: np.ndarray,
    y_mean: np.ndarray,
    y_scale: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[BudgetHeadNet, dict[str, Any]]:
    model = BudgetHeadNet(train_x.shape[1], hidden, depth, len(BUDGETS)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_targets.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 1700)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n = len(cal_split["episode"])
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(order_base)
        losses: list[float] = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            point = F.smooth_l1_loss(pred, y_t[idx])
            worst_head = torch.max(torch.mean(F.smooth_l1_loss(pred, y_t[idx], reduction="none"), dim=0))
            loss = 0.75 * point + 0.25 * worst_head
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred = predict(model, cal_x, device, batch)
        cal_pred = cal_pred * y_scale[None, :] + y_mean[None, :]
        cal_scores = reshape_scores(cal_pred, n, depths)
        deltas = [
            conditioned_value.oracle_gap.episode_values(cal_split, cal_scores[int(multiplier)], np.ones(n, dtype=bool), int(multiplier))[1]
            for multiplier in BUDGETS.astype(np.int64)
        ]
        observed = float(np.mean([np.mean(v) for v in deltas]))
        high = float(
            max(
                conditioned_value.oracle_gap.bootstrap_mean(v, seed=seed + 9100 + epoch * 17 + i, samples=300)["high"]
                for i, v in enumerate(deltas)
            )
        )
        key = (high, observed, float(np.mean(losses)))
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_budget_mean_observed": clean_float(observed),
                "cal_budget_max_high": clean_float(high),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "selection_key": [clean_float(v) for v in key]}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration max CI high across budget-specific heads, then mean observed delta, then training loss",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    row = report["summary"]
    lines = [
        "# State-Generation Budget-Head Value Audit",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['training']['best']['epoch']}`",
        "",
        "| row | mean capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|",
        (
            f"| `budget_head_replacement` | {row['mean_capture_ratio']:.6g} | "
            f"{row['budget3_capture_ratio']:.6g} | {row['budget4_capture_ratio']:.6g} | "
            f"{row['mean_regret_to_oracle']:.6g} |"
        ),
        "",
        "## Verdict",
        "",
        report["verdict"],
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train shared-trunk budget-specific replacement value heads")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--conditioned-report", default=str(REPORT_DIR / "state_generation_budget_conditioned_value.json"))
    parser.add_argument("--replacement-report", default=str(REPORT_DIR / "state_generation_budget_replacement_value.json"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1409)
    parser.add_argument("--epochs", type=int, default=80)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=5.0e-4)
    parser.add_argument("--bootstrap-samples", type=int, default=4000)
    args = parser.parse_args()

    start_time = time.time()
    device = configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    features, feature_dims = replacement_value.prepare_features(data, latents, depths)
    targets = replacement_value.target_rows(train, cal, eval_split, depths)
    train_targets = np.stack(
        [targets[f"replacement_budget{int(b)}"]["train"].reshape(-1) for b in BUDGETS],
        axis=1,
    ).astype(np.float64)
    y_mean = np.mean(train_targets, axis=0).astype(np.float64)
    y_scale = np.std(train_targets, axis=0).astype(np.float64)
    y_scale[y_scale < 1.0e-6] = 1.0
    train_targets_std = ((train_targets - y_mean[None, :]) / y_scale[None, :]).astype(np.float32)
    model, training = train_model(
        features["train"],
        train_targets_std,
        features["calibration"],
        cal,
        depths,
        y_mean,
        y_scale,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    eval_pred = predict(model, features["eval"], device, int(args.batch))
    eval_pred = eval_pred * y_scale[None, :] + y_mean[None, :]
    eval_scores = reshape_scores(eval_pred, len(eval_split["episode"]), depths)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    summary_payload = conditioned_value.summarize_budget_conditioned(
        eval_split,
        eval_scores,
        hard_mask,
        seed=int(args.seed) + 100000,
        samples=int(args.bootstrap_samples),
    )
    summary = summary_payload["summary"]
    conditioned_report = json.loads(Path(args.conditioned_report).read_text(encoding="utf-8"))
    conditioned_diag = conditioned_report.get("diagnosis", {})
    conditioned_mean = float(conditioned_diag.get("budget_conditioned_mean_capture_ratio", 0.0))
    conditioned_budget4 = float(conditioned_diag.get("budget_conditioned_budget4_capture_ratio", 0.0))
    replacement_report = json.loads(Path(args.replacement_report).read_text(encoding="utf-8"))
    replacement_diag = replacement_report.get("diagnosis", {})
    replacement_mean = float(replacement_diag.get("best_replacement_mean_capture_ratio", 0.0))
    replacement_budget4 = float(replacement_diag.get("best_replacement_budget4_capture_ratio", 0.0))
    closes = bool(float(summary["mean_capture_ratio"]) >= 0.5 and float(summary["budget4_capture_ratio"]) > 0.0)
    beats_conditioned = bool(float(summary["mean_capture_ratio"]) > conditioned_mean)
    beats_replacement = bool(float(summary["mean_capture_ratio"]) > replacement_mean)
    repairs_budget4 = bool(float(summary["budget4_capture_ratio"]) > replacement_budget4 and float(summary["budget4_capture_ratio"]) > 0.0)
    if closes:
        verdict = (
            "Budget-specific heads capture a substantial share of hard oracle headroom across budget stress. "
            "Independent export validation remains required."
        )
    elif beats_conditioned or beats_replacement or repairs_budget4:
        verdict = (
            "Budget-specific heads improve at least one stress statistic over pooled or single-budget baselines, "
            "but allocation closure remains open."
        )
    else:
        verdict = (
            "Budget-specific heads do not improve over the current budget-replacement boundary; allocation remains open."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_head_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "heads": BUDGETS.tolist(),
        },
        "feature_dims": feature_dims,
        "hard_episode_union": hard_episodes,
        "training": training,
        "budgets": summary_payload["budgets"],
        "summary": summary,
        "diagnosis": {
            "budget_head_closes": closes,
            "budget_head_beats_pooled_mean_capture": beats_conditioned,
            "budget_head_beats_single_replacement_mean_capture": beats_replacement,
            "budget_head_repairs_budget4_capture": repairs_budget4,
            "budget_head_mean_capture_ratio": clean_float(float(summary["mean_capture_ratio"])),
            "budget_head_budget3_capture_ratio": clean_float(float(summary["budget3_capture_ratio"])),
            "budget_head_budget4_capture_ratio": clean_float(float(summary["budget4_capture_ratio"])),
            "budget_head_mean_regret_to_oracle": clean_float(float(summary["mean_regret_to_oracle"])),
            "pooled_budget_conditioned_mean_capture_ratio": clean_float(conditioned_mean),
            "pooled_budget_conditioned_budget4_capture_ratio": clean_float(conditioned_budget4),
            "single_budget_replacement_mean_capture_ratio": clean_float(replacement_mean),
            "single_budget_replacement_budget4_capture_ratio": clean_float(replacement_budget4),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, geometry, predicted rollout mechanism summaries, and option interactions",
            "training_targets": "train/cal split forced-replacement exact-budget values with separate heads for budget multipliers 2, 3, and 4",
            "selection": "calibration split budget-head metrics only; held-out hard ids are not used for training or model selection",
            "oracle_scope": "eval option_error is used only after fixed budget-head scores are generated",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": [
            "deployable allocation policy",
            "independent export validation",
            "complete BEDC-native world model",
            "prediction parity",
        ],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        budget_multipliers=BUDGETS.astype(np.int64),
        **{f"budget_{int(k)}_score": v.astype(np.float64) for k, v in eval_scores.items()},
    )
    Path(args.json).write_text(
        json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

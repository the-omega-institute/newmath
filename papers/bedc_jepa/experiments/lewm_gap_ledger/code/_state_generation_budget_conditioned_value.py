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

import _state_generation_budget_replacement_value as replacement_value
import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_geometry_option_conditioned_allocation as option_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_budget_conditioned_value.json"
DEFAULT_MD = REPORT_DIR / "state_generation_budget_conditioned_value.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_budget_conditioned_value_predictions.npz"
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


def budget_features(budgets: np.ndarray) -> np.ndarray:
    b = budgets.astype(np.float32)
    centered = b - 3.0
    return np.stack(
        [
            centered,
            centered * centered,
            (b == 2.0).astype(np.float32),
            (b == 3.0).astype(np.float32),
            (b == 4.0).astype(np.float32),
        ],
        axis=1,
    ).astype(np.float32)


def expand_budget_conditioned_features(option_x: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> np.ndarray:
    opt = option_alloc.option_features(depths).astype(np.float32)
    opt_tiled = np.tile(opt, (n, 1)).astype(np.float32)
    budget_tokens = budget_features(budgets)
    rows: list[np.ndarray] = []
    for budget_index in range(len(budgets)):
        b = np.repeat(budget_tokens[budget_index : budget_index + 1], len(option_x), axis=0).astype(np.float32)
        interaction = (opt_tiled[:, :, None] * b[:, None, :]).reshape(len(option_x), -1).astype(np.float32)
        rows.append(np.concatenate([option_x.astype(np.float32), b, interaction], axis=1).astype(np.float32))
    return np.concatenate(rows, axis=0).astype(np.float32)


class BudgetConditionedNet(nn.Module):
    def __init__(self, in_dim: int, hidden: int, depth: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        dim = in_dim
        for _ in range(depth):
            blocks.extend([nn.Linear(dim, hidden), nn.SiLU(), nn.LayerNorm(hidden), nn.Dropout(0.05)])
            dim = hidden
        blocks.append(nn.Linear(dim, 1))
        self.net = nn.Sequential(*blocks)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def predict(model: BudgetConditionedNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def reshape_budget_scores(flat: np.ndarray, n: int, depths: np.ndarray, budgets: np.ndarray) -> dict[int, np.ndarray]:
    m = len(depths)
    out: dict[int, np.ndarray] = {}
    offset = 0
    for budget in budgets.astype(np.int64):
        out[int(budget)] = flat[offset : offset + n * m].reshape(n, m).astype(np.float64)
        offset += n * m
    return out


def summarize_budget_conditioned(
    split: dict[str, np.ndarray],
    scores: dict[int, np.ndarray],
    hard_mask: np.ndarray,
    *,
    seed: int,
    samples: int,
) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, multiplier in enumerate((2, 3, 4)):
        oracle_eps, oracle_values = oracle_gap.episode_values(split, oracle_score, hard_mask, multiplier)
        score_eps, score_values = oracle_gap.episode_values(split, scores[int(multiplier)], hard_mask, multiplier)
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {multiplier}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{multiplier}"] = {
            "score_delta": oracle_gap.bootstrap_mean(score_values, seed=seed + 1009 * budget_index, samples=samples),
            "oracle_delta": oracle_gap.bootstrap_mean(oracle_values, seed=seed + 1009 * budget_index + 17, samples=samples),
            "regret_to_oracle": oracle_gap.bootstrap_mean(regret, seed=seed + 1009 * budget_index + 31, samples=samples),
            "headroom_capture_ratio": clean_float(float(capture)),
        }
    return {
        "budgets": budgets,
        "summary": {
            "mean_capture_ratio": clean_float(float(np.mean(captures))),
            "min_capture_ratio": clean_float(float(np.min(captures))),
            "max_capture_ratio": clean_float(float(np.max(captures))),
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
        },
    }


def train_model(
    train_x: np.ndarray,
    train_target: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    depths: np.ndarray,
    budgets: np.ndarray,
    y_mean: float,
    y_scale: float,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[BudgetConditionedNet, dict[str, Any]]:
    model = BudgetConditionedNet(train_x.shape[1], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 700)
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
            loss = F.smooth_l1_loss(pred, y_t[idx])
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_flat = predict(model, cal_x, device, batch) * y_scale + y_mean
        cal_scores = reshape_budget_scores(cal_flat, n, depths, budgets)
        deltas = [
            oracle_gap.episode_values(cal_split, cal_scores[int(multiplier)], np.ones(n, dtype=bool), int(multiplier))[1]
            for multiplier in budgets.astype(np.int64)
        ]
        observed = float(np.mean([np.mean(v) for v in deltas]))
        high = float(max(oracle_gap.bootstrap_mean(v, seed=seed + 9000 + epoch * 17 + i, samples=300)["high"] for i, v in enumerate(deltas)))
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
        "selection_rule": "minimize calibration max CI high across budget-conditioned exact-budget deltas, then mean observed delta, then training loss",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    row = report["summary"]
    lines = [
        "# State-Generation Budget-Conditioned Value Audit",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['training']['best']['epoch']}`",
        "",
        "| row | mean capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|",
        (
            f"| `budget_conditioned_replacement` | {row['mean_capture_ratio']:.6g} | "
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
    parser = argparse.ArgumentParser(description="Train budget-conditioned multi-budget replacement value scorer")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--replacement-report", default=str(REPORT_DIR / "state_generation_budget_replacement_value.json"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1301)
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
    base_features, feature_dims = replacement_value.prepare_features(data, latents, depths)
    train_option_x = base_features["train"]
    cal_option_x = base_features["calibration"]
    eval_option_x = base_features["eval"]
    targets = replacement_value.target_rows(train, cal, eval_split, depths)
    train_budget_x = expand_budget_conditioned_features(train_option_x, len(train["episode"]), depths, BUDGETS)
    cal_budget_x = expand_budget_conditioned_features(cal_option_x, len(cal["episode"]), depths, BUDGETS)
    eval_budget_x = expand_budget_conditioned_features(eval_option_x, len(eval_split["episode"]), depths, BUDGETS)
    train_target = np.concatenate(
        [targets[f"replacement_budget{int(b)}"]["train"].reshape(-1) for b in BUDGETS],
        axis=0,
    ).astype(np.float64)
    y_mean = float(np.mean(train_target))
    y_scale = float(np.std(train_target))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_target_std = ((train_target - y_mean) / y_scale).astype(np.float32)
    model, training = train_model(
        train_budget_x,
        train_target_std,
        cal_budget_x,
        cal,
        depths,
        BUDGETS,
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
    eval_flat = predict(model, eval_budget_x, device, int(args.batch)) * y_scale + y_mean
    eval_scores = reshape_budget_scores(eval_flat, len(eval_split["episode"]), depths, BUDGETS)
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    summary_payload = summarize_budget_conditioned(
        eval_split,
        eval_scores,
        hard_mask,
        seed=int(args.seed) + 100000,
        samples=int(args.bootstrap_samples),
    )
    summary = summary_payload["summary"]
    replacement_report = json.loads(Path(args.replacement_report).read_text(encoding="utf-8"))
    replacement_diag = replacement_report.get("diagnosis", {})
    replacement_mean = float(replacement_diag.get("best_replacement_mean_capture_ratio", 0.0))
    replacement_budget3 = float(replacement_diag.get("best_replacement_budget3_capture_ratio", 0.0))
    replacement_budget4 = float(replacement_diag.get("best_replacement_budget4_capture_ratio", 0.0))
    closes = bool(float(summary["mean_capture_ratio"]) >= 0.5 and float(summary["budget4_capture_ratio"]) > 0.0)
    beats_replacement_mean = bool(float(summary["mean_capture_ratio"]) > replacement_mean)
    repairs_budget4 = bool(float(summary["budget4_capture_ratio"]) > replacement_budget4 and float(summary["budget4_capture_ratio"]) > 0.0)
    if closes:
        verdict = (
            "Budget-conditioned replacement value captures a substantial share of hard oracle headroom across budget stress. "
            "Independent export validation is still required."
        )
    elif beats_replacement_mean or repairs_budget4:
        verdict = (
            "Budget-conditioned replacement value improves at least one stress statistic over the single-budget replacement row, "
            "but allocation closure remains open."
        )
    else:
        verdict = (
            "Budget-conditioned replacement value does not improve over the single-budget replacement boundary; allocation remains open."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_budget_conditioned_value",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "conditioned_budgets": BUDGETS.tolist(),
        },
        "feature_dims": {
            **feature_dims,
            "budget_feature_dim": int(budget_features(BUDGETS).shape[1]),
            "expanded_budget_conditioned_feature_dim": int(train_budget_x.shape[1]),
        },
        "hard_episode_union": hard_episodes,
        "training": training,
        "budgets": summary_payload["budgets"],
        "summary": summary,
        "diagnosis": {
            "budget_conditioned_closes": closes,
            "budget_conditioned_beats_replacement_mean_capture": beats_replacement_mean,
            "budget_conditioned_repairs_budget4_capture": repairs_budget4,
            "budget_conditioned_mean_capture_ratio": clean_float(float(summary["mean_capture_ratio"])),
            "budget_conditioned_budget3_capture_ratio": clean_float(float(summary["budget3_capture_ratio"])),
            "budget_conditioned_budget4_capture_ratio": clean_float(float(summary["budget4_capture_ratio"])),
            "budget_conditioned_mean_regret_to_oracle": clean_float(float(summary["mean_regret_to_oracle"])),
            "single_budget_replacement_mean_capture_ratio": clean_float(replacement_mean),
            "single_budget_replacement_budget3_capture_ratio": clean_float(replacement_budget3),
            "single_budget_replacement_budget4_capture_ratio": clean_float(replacement_budget4),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, geometry, predicted rollout mechanism summaries, option interactions, and budget multiplier token",
            "training_targets": "train/cal split forced-replacement exact-budget values for budget multipliers 2, 3, and 4",
            "selection": "calibration split budget-conditioned metrics only; held-out hard ids are not used for training or model selection",
            "oracle_scope": "eval option_error is used only after fixed budget-conditioned scores are generated",
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

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
import _state_generation_episode_budget_transfer_audit as budget_audit
import _state_generation_minimax_budget_policy as minimax_policy


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_coupled_budget_policy.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_coupled_budget_policy.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_coupled_budget_policy_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BUDGETS = minimax_policy.BUDGETS


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


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    out: list[np.ndarray] = []
    for ep in np.unique(episode.astype(np.int64)):
        out.append(np.flatnonzero(episode.astype(np.int64) == int(ep)).astype(np.int64))
    return out


def rank01(values: np.ndarray) -> np.ndarray:
    values = values.astype(np.float64)
    order = np.argsort(values, kind="mergesort")
    ranks = np.zeros(len(values), dtype=np.float64)
    if len(values) <= 1:
        return ranks
    ranks[order] = np.arange(len(values), dtype=np.float64) / float(len(values) - 1)
    return ranks


def raw_episode_coupled_features(split: dict[str, np.ndarray], depths: np.ndarray) -> np.ndarray:
    episode = split["episode"].astype(np.int64)
    t0_raw = split["anchor_ep_t0"].astype(np.float64)
    t0 = t0_raw.reshape(len(episode), -1)[:, -1]
    x = split["x"].astype(np.float64)
    x_norm = np.linalg.norm(x, axis=1)
    rows = np.zeros((len(episode), len(depths), 13), dtype=np.float64)
    for idxs in episode_groups(episode):
        idxs = idxs.astype(np.int64)
        n = len(idxs)
        pos_rank = rank01(t0[idxs])
        norm_rank = rank01(x_norm[idxs])
        local_t0 = t0[idxs]
        local_t0 = (local_t0 - float(np.mean(local_t0))) / float(np.std(local_t0) + 1.0e-6)
        for local_i, anchor in enumerate(idxs):
            for option_index, depth in enumerate(depths.astype(np.float64)):
                rows[anchor, option_index] = np.asarray(
                    [
                        math.log1p(float(n)),
                        1.0 / float(max(n, 1)),
                        pos_rank[local_i],
                        pos_rank[local_i] - 0.5,
                        norm_rank[local_i],
                        norm_rank[local_i] - 0.5,
                        local_t0[local_i],
                        (depth - 3.0) / 2.0,
                        ((depth - 3.0) / 2.0) ** 2,
                        abs(depth - 2.0),
                        abs(depth - 3.0),
                        abs(depth - 4.0),
                        float(depth),
                    ],
                    dtype=np.float64,
                )
    return rows.reshape(len(episode) * len(depths), -1).astype(np.float32)


def append_coupled_features(
    base: dict[str, np.ndarray],
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_split: dict[str, np.ndarray],
    depths: np.ndarray,
) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    raw_train = raw_episode_coupled_features(train, depths)
    raw_cal = raw_episode_coupled_features(cal, depths)
    raw_eval = raw_episode_coupled_features(eval_split, depths)
    mean = np.mean(raw_train.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(raw_train.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return {
        "train": np.concatenate([base["train"].astype(np.float32), ((raw_train - mean) / scale).astype(np.float32)], axis=1),
        "calibration": np.concatenate([base["calibration"].astype(np.float32), ((raw_cal - mean) / scale).astype(np.float32)], axis=1),
        "eval": np.concatenate([base["eval"].astype(np.float32), ((raw_eval - mean) / scale).astype(np.float32)], axis=1),
    }, {
        "episode_coupled_feature_dim": int(raw_train.shape[1]),
        "episode_coupled_expanded_dim": int(base["train"].shape[1] + raw_train.shape[1]),
    }


class EpisodeCoupledBudgetNet(nn.Module):
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


def predict(model: EpisodeCoupledBudgetNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
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
    train_split: dict[str, np.ndarray],
    train_assignment: np.ndarray,
    train_centered_error: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    depths: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch_episodes: int,
    lr: float,
) -> tuple[EpisodeCoupledBudgetNet, dict[str, Any]]:
    model = EpisodeCoupledBudgetNet(train_x.shape[1], hidden, depth, len(BUDGETS)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    assign_t = torch.from_numpy(train_assignment.astype(np.int64)).to(device)
    err_t = torch.from_numpy(train_centered_error.astype(np.float32)).to(device)
    depths_t = torch.from_numpy(depths.astype(np.float32)).to(device)
    budget_t = torch.from_numpy(BUDGETS.astype(np.float32)).to(device)
    groups = episode_groups(train_split["episode"].astype(np.int64))
    rng = np.random.default_rng(seed + 3100)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n_options = len(depths)
    n_cal = len(cal_split["episode"])
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(np.arange(len(groups)))
        losses: list[float] = []
        for start in range(0, len(order), batch_episodes):
            episode_batch = order[start : start + batch_episodes]
            parts = [groups[int(i)] for i in episode_batch]
            anchors = np.concatenate(parts).astype(np.int64)
            row_idx = np.concatenate([np.arange(int(anchor) * n_options, int(anchor + 1) * n_options) for anchor in anchors])
            idx = torch.as_tensor(row_idx, dtype=torch.long, device=device)
            pred = model(x_t[idx]).reshape(len(anchors), n_options, len(BUDGETS)).permute(0, 2, 1)
            target = assign_t[torch.as_tensor(anchors, dtype=torch.long, device=device)]
            err = err_t[torch.as_tensor(anchors, dtype=torch.long, device=device)]
            ce_by_head = torch.stack([F.cross_entropy(-pred[:, head, :], target[:, head]) for head in range(len(BUDGETS))])
            reg_by_head = torch.stack(
                [F.smooth_l1_loss(pred[:, head, :] - torch.mean(pred[:, head, :], dim=1, keepdim=True), err) for head in range(len(BUDGETS))]
            )
            depth_losses: list[torch.Tensor] = []
            cursor = 0
            probs = torch.softmax(-pred, dim=2)
            for idxs in parts:
                count = len(idxs)
                local_probs = probs[cursor : cursor + count]
                expected_depth_sum = torch.sum(local_probs * depths_t[None, None, :], dim=(0, 2))
                target_sum = budget_t * float(count)
                depth_losses.append(F.smooth_l1_loss(expected_depth_sum / target_sum, torch.ones_like(target_sum)))
                cursor += count
            depth_loss = torch.stack(depth_losses).mean()
            loss = (
                0.45 * torch.max(ce_by_head)
                + 0.20 * torch.mean(ce_by_head)
                + 0.15 * depth_loss
                + 0.10 * torch.max(reg_by_head)
                + 0.10 * torch.mean(reg_by_head)
            )
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred = predict(model, cal_x, device, 1024)
        cal_scores = reshape_scores(cal_pred, n_cal, depths)
        deltas = [
            minimax_policy.conditioned_value.oracle_gap.episode_values(cal_split, cal_scores[int(multiplier)], np.ones(n_cal, dtype=bool), int(multiplier))[1]
            for multiplier in BUDGETS.astype(np.int64)
        ]
        highs = [
            float(minimax_policy.conditioned_value.oracle_gap.bootstrap_mean(v, seed=seed + 15000 + epoch * 23 + i, samples=300)["high"])
            for i, v in enumerate(deltas)
        ]
        observed = float(np.mean([np.mean(v) for v in deltas]))
        key = (float(max(highs)), observed, float(np.mean(losses)))
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_budget_mean_observed": clean_float(observed),
                "cal_budget_max_high": clean_float(float(max(highs))),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "selection_key": [clean_float(v) for v in key]}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "episode-batched training; minimize calibration worst budget CI high, then mean observed delta, then training loss",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    row = report["summary"]
    lines = [
        "# State-Generation Episode-Coupled Budget Policy",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['training']['best']['epoch']}`",
        "",
        "| row | mean capture | budget-2 capture | budget-3 capture | budget-4 capture | mean regret |",
        "|---|---:|---:|---:|---:|---:|",
        (
            f"| `episode_coupled_budget_policy` | {row['mean_capture_ratio']:.6g} | "
            f"{report['budgets']['budget_2']['headroom_capture_ratio']:.6g} | "
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
    parser = argparse.ArgumentParser(description="Train an episode-coupled budget competition policy for state-generation allocation")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--minimax-report", default=str(REPORT_DIR / "state_generation_minimax_budget_policy.json"))
    parser.add_argument("--budget-head-report", default=str(REPORT_DIR / "state_generation_budget_head_value.json"))
    parser.add_argument("--replacement-report", default=str(REPORT_DIR / "state_generation_budget_replacement_value.json"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=1613)
    parser.add_argument("--epochs", type=int, default=120)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch-episodes", type=int, default=8)
    parser.add_argument("--lr", type=float, default=3.0e-4)
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
    features, coupled_dims = append_coupled_features(base_features, train, cal, eval_split, depths)
    train_assignment = minimax_policy.oracle_assignments(train, depths)
    eval_assignment = minimax_policy.oracle_assignments(eval_split, depths)
    model, training = train_model(
        features["train"],
        train,
        train_assignment,
        minimax_policy.centered_error_targets(train["option_error"]),
        features["calibration"],
        cal,
        depths,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch_episodes=int(args.batch_episodes),
        lr=float(args.lr),
    )
    eval_pred = predict(model, features["eval"], device, 1024)
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
    minimax_diag = json.loads(Path(args.minimax_report).read_text(encoding="utf-8")).get("diagnosis", {})
    budget_head_diag = json.loads(Path(args.budget_head_report).read_text(encoding="utf-8")).get("diagnosis", {})
    replacement_diag = json.loads(Path(args.replacement_report).read_text(encoding="utf-8")).get("diagnosis", {})
    minimax_mean = float(minimax_diag.get("minimax_policy_mean_capture_ratio", 0.0))
    budget_head_mean = float(budget_head_diag.get("budget_head_mean_capture_ratio", 0.0))
    replacement_mean = float(replacement_diag.get("best_replacement_mean_capture_ratio", 0.0))
    closes = bool(float(summary["mean_capture_ratio"]) >= 0.5 and float(summary["min_capture_ratio"]) > 0.0)
    beats_minimax = bool(float(summary["mean_capture_ratio"]) > minimax_mean)
    beats_budget_head = bool(float(summary["mean_capture_ratio"]) > budget_head_mean)
    beats_replacement = bool(float(summary["mean_capture_ratio"]) > replacement_mean)
    if closes:
        verdict = (
            "Episode-coupled budget policy captures substantial hard oracle headroom across budget stress. "
            "Independent export validation remains required."
        )
    elif beats_minimax or beats_budget_head or beats_replacement:
        verdict = (
            "Episode-coupled budget policy improves at least one policy boundary statistic, but allocation closure remains open."
        )
    else:
        verdict = (
            "Episode-coupled budget policy does not improve over the current budget-value boundary; allocation remains open."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_coupled_budget_policy",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch_episodes": int(args.batch_episodes),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
            "budgets": BUDGETS.tolist(),
            "loss": "0.45*worst_budget_assignment_ce + 0.20*mean_assignment_ce + 0.15*episode_depth_budget + 0.10*worst_centered_error_reg + 0.10*mean_centered_error_reg",
        },
        "feature_dims": {**feature_dims, **coupled_dims},
        "hard_episode_union": hard_episodes,
        "training": training,
        "budgets": summary_payload["budgets"],
        "summary": summary,
        "assignment_match": minimax_policy.assignment_match(eval_scores, eval_assignment, eval_split, depths),
        "diagnosis": {
            "episode_coupled_policy_closes": closes,
            "episode_coupled_policy_beats_minimax_mean_capture": beats_minimax,
            "episode_coupled_policy_beats_budget_head_mean_capture": beats_budget_head,
            "episode_coupled_policy_beats_replacement_mean_capture": beats_replacement,
            "episode_coupled_policy_mean_capture_ratio": clean_float(float(summary["mean_capture_ratio"])),
            "episode_coupled_policy_budget2_capture_ratio": clean_float(float(summary_payload["budgets"]["budget_2"]["headroom_capture_ratio"])),
            "episode_coupled_policy_budget3_capture_ratio": clean_float(float(summary["budget3_capture_ratio"])),
            "episode_coupled_policy_budget4_capture_ratio": clean_float(float(summary["budget4_capture_ratio"])),
            "episode_coupled_policy_mean_regret_to_oracle": clean_float(float(summary["mean_regret_to_oracle"])),
            "minimax_policy_mean_capture_ratio": clean_float(minimax_mean),
            "budget_head_mean_capture_ratio": clean_float(budget_head_mean),
            "single_budget_replacement_mean_capture_ratio": clean_float(replacement_mean),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, geometry, predicted rollout mechanism summaries, option interactions, and non-label episode rank/size/position features",
            "training_targets": "train split exact-budget oracle assignments for budget multipliers 2, 3, and 4",
            "selection": "calibration split worst-budget exact-budget CI high; held-out hard ids are not used for training or model selection",
            "oracle_scope": "eval option_error is used only after fixed episode-coupled scores are generated",
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
        oracle_assignment=eval_assignment.astype(np.int64),
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

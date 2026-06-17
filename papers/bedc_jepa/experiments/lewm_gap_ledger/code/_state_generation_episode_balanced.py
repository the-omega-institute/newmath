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
import torch.nn.functional as F

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_balanced.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_balanced.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_balanced_predictions.npz"


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


def episode_index_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.flatnonzero(episode.astype(np.int64) == int(value)).astype(np.int64) for value in np.unique(episode.astype(np.int64))]


def episode_balanced_indices(groups: list[np.ndarray], rng: np.random.Generator, *, episodes_per_batch: int, anchors_per_episode: int) -> np.ndarray:
    chosen_groups = rng.choice(len(groups), size=episodes_per_batch, replace=len(groups) < episodes_per_batch)
    parts: list[np.ndarray] = []
    for group_id in chosen_groups:
        group = groups[int(group_id)]
        parts.append(rng.choice(group, size=anchors_per_episode, replace=len(group) < anchors_per_episode).astype(np.int64))
    return np.concatenate(parts).astype(np.int64)


def train_model(
    train_x: np.ndarray,
    train_episode: np.ndarray,
    train_target: np.ndarray,
    train_oracle: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    episodes_per_batch: int,
    anchors_per_episode: int,
    lr: float,
) -> tuple[episode_alloc.EpisodeAllocationNet, dict[str, Any]]:
    model = episode_alloc.EpisodeAllocationNet(train_x.shape[1], structured.DEPTHS.shape[0], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    target_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    oracle_t = torch.from_numpy(train_oracle.astype(np.int64)).to(device)
    depths_t = torch.from_numpy(structured.DEPTHS.astype(np.float32)).to(device)
    groups = episode_index_groups(train_episode)
    steps_per_epoch = max(1, math.ceil(len(train_x) / float(episodes_per_batch * anchors_per_episode)))
    rng = np.random.default_rng(seed + 5100)
    best_state = None
    best_key = (float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        losses: list[float] = []
        for _ in range(steps_per_epoch):
            idx_np = episode_balanced_indices(
                groups,
                rng,
                episodes_per_batch=episodes_per_batch,
                anchors_per_episode=anchors_per_episode,
            )
            idx = torch.as_tensor(idx_np, dtype=torch.long, device=device)
            score = model(x_t[idx])
            centered_score = score - torch.mean(score, dim=1, keepdim=True)
            ce = F.cross_entropy(-score, oracle_t[idx])
            rank = episode_alloc.pairwise_loss(centered_score, target_t[idx])
            reg = F.smooth_l1_loss(centered_score, target_t[idx])
            balance = episode_alloc.depth_balance_loss(score, oracle_t[idx], depths_t)
            loss = 0.50 * ce + 0.25 * rank + 0.15 * balance + 0.10 * reg
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_score = episode_alloc.predict(model, cal_x, device, 256)
        cal_eval = episode_alloc.evaluate(cal_split, cal_score, seed=seed + 5800 + epoch)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_delta_observed": clean_float(float(delta["observed"])),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_oracle_match": clean_float(float(cal_eval["oracle_match"])),
                "cal_spearman": clean_float(float(cal_eval["score_error_spearman"])),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "calibration": cal_eval, "selection_key": list(key)}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "steps_per_epoch": int(steps_per_epoch),
        "train_episode_count": int(len(groups)),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# State-Generation Episode Balanced",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        "",
        "| scorer | allocation delta | rho | oracle match |",
        "|---|---:|---:|---:|",
    ]
    for name in ["episode_balanced", "episode_allocation", "best_seed", "allocation_native", "oracle_true_error"]:
        row = rows[name]
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('oracle_match', 0.0):.6g} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an episode-balanced allocation objective")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--allocation-native", default=str(REPORT_DIR / "state_generation_allocation_native_predictions.npz"))
    parser.add_argument("--episode-allocation", default=str(REPORT_DIR / "state_generation_episode_allocation_predictions.npz"))
    parser.add_argument("--best-seed", default=str(REPORT_DIR / "state_generation_episode_allocation_seed_617_predictions.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=997)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--episodes-per-batch", type=int, default=16)
    parser.add_argument("--anchors-per-episode", type=int, default=8)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    with np.load(Path(args.export), allow_pickle=False) as archive:
        data = {key: archive[key] for key in archive.files}
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    mean, scale = episode_alloc.standardizer(train["x"])
    train_x = episode_alloc.apply_standardizer(train["x"], mean, scale)
    cal_x = episode_alloc.apply_standardizer(cal["x"], mean, scale)
    eval_x = episode_alloc.apply_standardizer(eval_split["x"], mean, scale)
    train_oracle = episode_alloc.oracle_choice(train)
    eval_oracle = episode_alloc.oracle_choice(eval_split)
    model, selection = train_model(
        train_x,
        train["episode"],
        episode_alloc.centered_errors(train["option_error"]),
        train_oracle,
        cal_x,
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        episodes_per_batch=int(args.episodes_per_batch),
        anchors_per_episode=int(args.anchors_per_episode),
        lr=float(args.lr),
    )
    eval_score = episode_alloc.predict(model, eval_x, device, 256)
    with np.load(Path(args.allocation_native), allow_pickle=False) as native:
        allocation_native_score = native["allocation_native_score"].astype(np.float64)
    with np.load(Path(args.episode_allocation), allow_pickle=False) as episode_pred:
        episode_score = episode_pred["episode_allocation_score"].astype(np.float64)
    with np.load(Path(args.best_seed), allow_pickle=False) as best_seed:
        best_seed_score = best_seed["episode_allocation_score"].astype(np.float64)
    rows = {
        "episode_balanced": episode_alloc.evaluate(eval_split, eval_score, seed=int(args.seed) + 1301),
        "episode_allocation": episode_alloc.evaluate(eval_split, episode_score, seed=int(args.seed) + 1301),
        "best_seed": episode_alloc.evaluate(eval_split, best_seed_score, seed=int(args.seed) + 1301),
        "allocation_native": episode_alloc.evaluate(eval_split, allocation_native_score, seed=int(args.seed) + 1301),
        "oracle_true_error": episode_alloc.evaluate(eval_split, eval_split["option_error"], seed=int(args.seed) + 1301),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_balanced",
        "device": str(device),
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "lr": float(args.lr),
            "episodes_per_batch": int(args.episodes_per_batch),
            "anchors_per_episode": int(args.anchors_per_episode),
            "loss": "episode-balanced sampling with 0.50*oracle_choice_ce + 0.25*pairwise_order + 0.15*expected_depth + 0.10*centered_smooth_l1",
        },
        "counts": {
            "train": int(len(train_x)),
            "train_episodes": int(len(np.unique(train["episode"]))),
            "calibration": int(len(cal_x)),
            "eval": int(len(eval_x)),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "selection": selection,
        "eval": rows,
        "diagnosis": {
            "allocation_closed": bool(float(rows["episode_balanced"]["allocation_delta"]["high"]) < 0.0),
            "beats_episode_objective_observed": bool(float(rows["episode_balanced"]["allocation_delta"]["observed"]) < float(rows["episode_allocation"]["allocation_delta"]["observed"])),
            "beats_episode_objective_ci_high": bool(float(rows["episode_balanced"]["allocation_delta"]["high"]) < float(rows["episode_allocation"]["allocation_delta"]["high"])),
            "beats_best_seed_observed": bool(float(rows["episode_balanced"]["allocation_delta"]["observed"]) < float(rows["best_seed"]["allocation_delta"]["observed"])),
            "beats_best_seed_ci_high": bool(float(rows["episode_balanced"]["allocation_delta"]["high"]) < float(rows["best_seed"]["allocation_delta"]["high"])),
            "beats_allocation_native_observed": bool(float(rows["episode_balanced"]["allocation_delta"]["observed"]) < float(rows["allocation_native"]["allocation_delta"]["observed"])),
            "beats_allocation_native_ci_high": bool(float(rows["episode_balanced"]["allocation_delta"]["high"]) < float(rows["allocation_native"]["allocation_delta"]["high"])),
            "oracle_closed": bool(float(rows["oracle_true_error"]["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "features": "aligned export x only",
            "targets": "train option_error is converted to exact-budget oracle choices; eval option_error used only after score generation for metrics",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    chosen = structured.exact_budget_choice(eval_split["episode"], eval_score, structured.DEPTHS)
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=option_depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        episode_balanced_score=eval_score.astype(np.float64),
        episode_allocation_score=episode_score.astype(np.float64),
        best_seed_score=best_seed_score.astype(np.float64),
        allocation_native_score=allocation_native_score.astype(np.float64),
        oracle_choice=eval_oracle.astype(np.int64),
        chosen_col=chosen.astype(np.int64),
        chosen_depth=option_depths[chosen].astype(np.int64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

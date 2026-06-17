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
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_geometry_conditioned_allocation as geometry_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_geometry_regime_weighted_allocation.json"
DEFAULT_MD = REPORT_DIR / "state_generation_geometry_regime_weighted_allocation.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_geometry_regime_weighted_allocation_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"


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


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def weighted_mean(loss: torch.Tensor, weight: torch.Tensor) -> torch.Tensor:
    return torch.sum(loss * weight) / torch.clamp(torch.sum(weight), min=1.0e-8)


def weighted_pairwise_loss(score: torch.Tensor, target: torch.Tensor, weight: torch.Tensor) -> torch.Tensor:
    diff_score = score[:, :, None] - score[:, None, :]
    diff_target = target[:, :, None] - target[:, None, :]
    sign = torch.sign(diff_target)
    mask = torch.abs(diff_target) > 1.0e-7
    raw = F.softplus(-sign * diff_score) * mask.to(score.dtype)
    denom = torch.sum(mask.to(score.dtype), dim=(1, 2)).clamp_min(1.0)
    per_row = torch.sum(raw, dim=(1, 2)) / denom
    return weighted_mean(per_row, weight)


def weighted_depth_balance_loss(
    score: torch.Tensor,
    oracle: torch.Tensor,
    depths: torch.Tensor,
    weight: torch.Tensor,
) -> torch.Tensor:
    probs = torch.softmax(-score, dim=1)
    expected_depth = probs @ depths
    target_depth = depths[oracle]
    per_row = F.smooth_l1_loss(expected_depth, target_depth, reduction="none")
    return weighted_mean(per_row, weight)


def regime_weights(
    train_env: np.ndarray,
    *,
    low_y_quantile: float,
    low_y_weight: float,
    different_room_weight: float,
    interaction_weight: float,
) -> tuple[np.ndarray, dict[str, Any]]:
    agent_y = train_env[:, 3].astype(np.float64)
    different_room = (train_env[:, 9].astype(np.float64) >= 0.5).astype(np.float64)
    threshold = float(np.quantile(agent_y, low_y_quantile))
    low_y = (agent_y <= threshold).astype(np.float64)
    interaction = low_y * different_room
    weight = (
        1.0
        + float(low_y_weight) * low_y
        + float(different_room_weight) * different_room
        + float(interaction_weight) * interaction
    )
    weight = np.maximum(weight, 1.0e-6)
    weight = weight / float(np.mean(weight))
    diagnostics = {
        "agent_y_threshold": clean_float(threshold),
        "low_y_quantile": clean_float(float(low_y_quantile)),
        "low_y_count": int(np.sum(low_y)),
        "different_room_count": int(np.sum(different_room)),
        "interaction_count": int(np.sum(interaction)),
        "weight_min": clean_float(float(np.min(weight))),
        "weight_mean": clean_float(float(np.mean(weight))),
        "weight_max": clean_float(float(np.max(weight))),
        "weight_rule": {
            "low_y_weight": clean_float(float(low_y_weight)),
            "different_room_weight": clean_float(float(different_room_weight)),
            "interaction_weight": clean_float(float(interaction_weight)),
        },
    }
    return weight.astype(np.float32), diagnostics


def train_weighted_model(
    train_x: np.ndarray,
    train_target: np.ndarray,
    train_oracle: np.ndarray,
    train_weight: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch: int,
    lr: float,
) -> tuple[episode_alloc.EpisodeAllocationNet, dict[str, Any]]:
    model = episode_alloc.EpisodeAllocationNet(train_x.shape[1], structured.DEPTHS.shape[0], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    target_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    oracle_t = torch.from_numpy(train_oracle.astype(np.int64)).to(device)
    weight_t = torch.from_numpy(train_weight.astype(np.float32)).to(device)
    depths_t = torch.from_numpy(structured.DEPTHS.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 900)
    best_state = None
    best_key = (float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(order_base)
        losses: list[float] = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            score = model(x_t[idx])
            centered_score = score - torch.mean(score, dim=1, keepdim=True)
            wb = weight_t[idx]
            wb = wb / torch.clamp(torch.mean(wb), min=1.0e-8)
            ce = weighted_mean(F.cross_entropy(-score, oracle_t[idx], reduction="none"), wb)
            rank = weighted_pairwise_loss(centered_score, target_t[idx], wb)
            reg = weighted_mean(F.smooth_l1_loss(centered_score, target_t[idx], reduction="none").mean(dim=1), wb)
            balance = weighted_depth_balance_loss(score, oracle_t[idx], depths_t, wb)
            loss = 0.50 * ce + 0.25 * rank + 0.15 * balance + 0.10 * reg
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_score = episode_alloc.predict(model, cal_x, device, batch)
        cal_eval = episode_alloc.evaluate(cal_split, cal_score, seed=seed + 1900 + epoch)
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
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Geometry-Regime Weighted Allocation",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        f"- geometry feature dim: `{report['feature_dims']['geometry_feature_dim']}`",
        f"- agent-y threshold: `{report['regime_weighting']['agent_y_threshold']:.6g}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |",
        "|---|---:|---:|---:|---:|",
    ]
    for name in ["geometry_regime_weighted", "geometry_conditioned", "episode_best_seed", "episode_objective", "seed_mean"]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard['observed']:.6g} | {hard['high']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a geometry-regime weighted episode allocation model")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--geometry-conditioned", default=str(REPORT_DIR / "state_generation_geometry_conditioned_allocation_predictions.npz"))
    parser.add_argument("--seed", type=int, default=643)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    parser.add_argument("--low-y-quantile", type=float, default=0.30)
    parser.add_argument("--low-y-weight", type=float, default=0.75)
    parser.add_argument("--different-room-weight", type=float, default=0.50)
    parser.add_argument("--interaction-weight", type=float, default=1.25)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    features, feature_dims = geometry_alloc.augment_features(data, latents)
    train_env_raw = geometry_alloc.env_feature_matrix(data, latents, "train")
    train_weight, weighting = regime_weights(
        train_env_raw,
        low_y_quantile=float(args.low_y_quantile),
        low_y_weight=float(args.low_y_weight),
        different_room_weight=float(args.different_room_weight),
        interaction_weight=float(args.interaction_weight),
    )
    train_oracle = episode_alloc.oracle_choice(train)
    model, selection = train_weighted_model(
        features["train"],
        episode_alloc.centered_errors(train["option_error"]),
        train_oracle,
        train_weight,
        features["calibration"],
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    eval_score = episode_alloc.predict(model, features["eval"], device, int(args.batch))
    geometry_conditioned = load_npz(Path(args.geometry_conditioned))["geometry_conditioned_score"].astype(np.float64)
    rows = {
        "geometry_regime_weighted": eval_score,
        "geometry_conditioned": geometry_conditioned,
    }
    rows.update(geometry_alloc.load_reference_rows())
    eval_rows = geometry_alloc.evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 5000)
    weighted_hard = eval_rows["geometry_regime_weighted"]["hard_only"]["allocation_delta"]
    conditioned_hard = eval_rows["geometry_conditioned"]["hard_only"]["allocation_delta"]
    weighted_full = eval_rows["geometry_regime_weighted"]["full"]["allocation_delta"]
    conditioned_full = eval_rows["geometry_conditioned"]["full"]["allocation_delta"]
    hard_improves = float(weighted_hard["observed"]) < float(conditioned_hard["observed"])
    hard_high_improves = float(weighted_hard["high"]) < float(conditioned_hard["high"])
    hard_closes = float(weighted_hard["high"]) < 0.0
    full_not_degraded = float(weighted_full["observed"]) <= float(conditioned_full["observed"]) + 1.0e-9
    if hard_closes:
        verdict = (
            "Train-defined geometry-regime weighting closes the hard-only allocation slice under the current diagnostic. "
            "This is a candidate allocation-control result requiring independent export validation."
        )
    elif hard_improves and hard_high_improves:
        verdict = (
            "Train-defined geometry-regime weighting improves hard-slice observed damage and CI high relative to append-only "
            "geometry conditioning, but it does not close hard-only allocation."
        )
    elif hard_improves:
        verdict = (
            "Train-defined geometry-regime weighting improves hard-slice observed damage relative to append-only geometry "
            "conditioning, but uncertainty remains bounded above zero."
        )
    else:
        verdict = (
            "Train-defined geometry-regime weighting does not improve the hard-only allocation boundary relative to append-only "
            "geometry conditioning."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_geometry_regime_weighted_allocation",
        "device": str(device),
        "feature_dims": feature_dims,
        "regime_weighting": weighting,
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "seed": int(args.seed),
            "loss": "same episode exact-budget objective with train-defined geometry-regime sample weights",
        },
        "counts": {
            "train": int(len(features["train"])),
            "calibration": int(len(features["calibration"])),
            "eval": int(len(features["eval"])),
            "hard_eval_anchors": int(np.sum(np.isin(eval_split["episode"], np.asarray(hard_episodes, dtype=np.int64)))),
        },
        "hard_episode_union": hard_episodes,
        "selection": selection,
        "eval": eval_rows,
        "diagnosis": {
            "hard_beats_geometry_conditioned_observed": bool(hard_improves),
            "hard_beats_geometry_conditioned_ci_high": bool(hard_high_improves),
            "hard_closes": bool(hard_closes),
            "full_not_degraded_vs_geometry_conditioned_observed": bool(full_not_degraded),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x plus explicit two-rooms state/action geometry from source latent export",
            "training_targets": "train option_error is converted to exact-budget oracle choices; hard eval ids are never used for training or calibration selection",
            "weighting": "sample weights use only train geometry: low agent_y train quantile, different_room, and their interaction",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "eval_targets": "eval option_error used only after fixed score generation for metrics",
            "source_latents": str(Path(args.latents)),
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=structured.DEPTHS.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        geometry_regime_weighted_score=eval_score.astype(np.float64),
        geometry_conditioned_score=geometry_conditioned.astype(np.float64),
        train_agent_y_threshold=np.asarray([weighting["agent_y_threshold"]], dtype=np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

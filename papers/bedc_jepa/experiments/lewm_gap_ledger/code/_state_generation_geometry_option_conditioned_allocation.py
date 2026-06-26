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

import _compute_value_structured_assignment as structured
import _state_generation_episode_allocation as episode_alloc
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_geometry_conditioned_allocation as geometry_alloc


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_geometry_option_conditioned_allocation.json"
DEFAULT_MD = REPORT_DIR / "state_generation_geometry_option_conditioned_allocation.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_geometry_option_conditioned_allocation_predictions.npz"
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
    ).astype(np.float32)


def expand_option_features(x: np.ndarray, env_z: np.ndarray, depths: np.ndarray) -> np.ndarray:
    opt = option_features(depths)
    rows = np.repeat(x.astype(np.float32), len(depths), axis=0)
    env = np.repeat(env_z.astype(np.float32), len(depths), axis=0)
    tiled = np.tile(opt, (len(x), 1)).astype(np.float32)
    interaction = (env[:, :, None] * tiled[:, None, :]).reshape(len(rows), -1).astype(np.float32)
    return np.concatenate([rows, tiled, interaction], axis=1).astype(np.float32)


class OptionErrorNet(nn.Module):
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


def reshape_scores(flat: np.ndarray, n: int, depths: np.ndarray) -> np.ndarray:
    return flat.reshape(n, len(depths)).astype(np.float64)


def predict(model: OptionErrorNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros(len(x), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def score_error_spearman(score: np.ndarray, truth: np.ndarray) -> float:
    return episode_alloc.clean_float(structured.cvm.spearman(score.reshape(-1), truth.reshape(-1)))


def evaluate_rows(
    eval_split: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    hard_episodes: list[int],
    *,
    seed: int,
) -> dict[str, Any]:
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    masks = {
        "full": np.ones(len(eval_split["episode"]), dtype=bool),
        "non_hard": ~hard_mask,
        "hard_only": hard_mask,
    }
    out: dict[str, Any] = {}
    for row_idx, (name, score) in enumerate(rows.items()):
        row: dict[str, Any] = {}
        for slice_idx, (slice_name, mask) in enumerate(masks.items()):
            local = geometry_alloc.slice_eval(eval_split, mask)
            local_score = score[mask.astype(bool)].astype(np.float64)
            metrics = structured.evaluate_scores(local, local_score, seed=seed + row_idx * 97 + slice_idx * 13)
            metrics["score_error_spearman"] = score_error_spearman(local_score, local["option_error"])
            row[slice_name] = metrics
        out[name] = row
    return out


def train_model(
    train_x: np.ndarray,
    train_target: np.ndarray,
    train_option_error: np.ndarray,
    cal_x: np.ndarray,
    cal_split: dict[str, np.ndarray],
    depths: np.ndarray,
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
) -> tuple[OptionErrorNet, dict[str, Any]]:
    model = OptionErrorNet(train_x.shape[1], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    true_rank = torch.from_numpy(train_option_error.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 1200)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n_train = train_option_error.shape[0]
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(order_base)
        losses: list[float] = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            point = F.smooth_l1_loss(pred, y_t[idx])
            anchors = rng.integers(0, n_train, size=max(8, batch // len(depths)))
            pair_rows = torch.as_tensor(anchors, dtype=torch.long, device=device)
            base = pair_rows * len(depths)
            pred_options = torch.stack([model(x_t[base + col]) for col in range(len(depths))], dim=1)
            diff_pred = pred_options[:, :, None] - pred_options[:, None, :]
            diff_true = true_rank[pair_rows, :, None] - true_rank[pair_rows, None, :]
            sign = torch.sign(diff_true)
            mask = torch.abs(diff_true) > 1.0e-7
            rank = F.softplus(-sign[mask] * diff_pred[mask]).mean() if torch.any(mask) else point * 0.0
            loss = point + 0.25 * rank
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_score = reshape_scores(predict(model, cal_x, device, batch) * y_scale + y_mean, len(cal_split["episode"]), depths)
        cal_eval = structured.evaluate_scores(cal_split, cal_score, seed=seed + 2200 + epoch)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), float(np.mean(losses)))
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_delta_observed": clean_float(float(delta["observed"])),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_spearman": clean_float(score_error_spearman(cal_score, cal_split["option_error"])),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "calibration": cal_eval, "selection_key": list(key)}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta, then training loss",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Geometry-Option Conditioned Allocation",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        f"- option feature dim: `{report['feature_dims']['option_feature_dim']}`",
        f"- geometry-option interaction dim: `{report['feature_dims']['geometry_option_interaction_dim']}`",
        "",
        "| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in [
        "geometry_option_conditioned",
        "geometry_regime_weighted",
        "geometry_conditioned",
        "episode_best_seed",
        "episode_objective",
    ]:
        row = report["eval"][name]
        full = row["full"]["allocation_delta"]
        non_hard = row["non_hard"]["allocation_delta"]
        hard = row["hard_only"]["allocation_delta"]
        lines.append(
            f"| `{name}` | {full['observed']:.6g} | {non_hard['observed']:.6g} | "
            f"{hard['observed']:.6g} | {hard['high']:.6g} | {row['hard_only']['score_error_spearman']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train geometry-option conditioned exact-budget allocation")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--geometry-conditioned", default=str(REPORT_DIR / "state_generation_geometry_conditioned_allocation_predictions.npz"))
    parser.add_argument("--geometry-regime-weighted", default=str(REPORT_DIR / "state_generation_geometry_regime_weighted_allocation_predictions.npz"))
    parser.add_argument("--seed", type=int, default=659)
    parser.add_argument("--epochs", type=int, default=220)
    parser.add_argument("--hidden", type=int, default=384)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=6.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {depths} vs {structured.DEPTHS}")
    features, feature_dims = geometry_alloc.augment_features(data, latents)
    train_x = expand_option_features(features["train"], features["train_env"], depths)
    cal_x = expand_option_features(features["calibration"], features["calibration_env"], depths)
    eval_x = expand_option_features(features["eval"], features["eval_env"], depths)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_target = ((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    model, selection = train_model(
        train_x,
        train_target,
        train["option_error"],
        cal_x,
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
    eval_score = reshape_scores(predict(model, eval_x, device, int(args.batch)) * y_scale + y_mean, len(eval_split["episode"]), depths)
    geometry_conditioned = load_npz(Path(args.geometry_conditioned))["geometry_conditioned_score"].astype(np.float64)
    geometry_regime_weighted = load_npz(Path(args.geometry_regime_weighted))["geometry_regime_weighted_score"].astype(np.float64)
    rows = {
        "geometry_option_conditioned": eval_score,
        "geometry_regime_weighted": geometry_regime_weighted,
        "geometry_conditioned": geometry_conditioned,
    }
    rows.update(geometry_alloc.load_reference_rows())
    eval_rows = evaluate_rows(eval_split, rows, hard_episodes, seed=int(args.seed) + 6000)
    option_hard = eval_rows["geometry_option_conditioned"]["hard_only"]["allocation_delta"]
    conditioned_hard = eval_rows["geometry_conditioned"]["hard_only"]["allocation_delta"]
    regime_hard = eval_rows["geometry_regime_weighted"]["hard_only"]["allocation_delta"]
    option_full = eval_rows["geometry_option_conditioned"]["full"]["allocation_delta"]
    conditioned_full = eval_rows["geometry_conditioned"]["full"]["allocation_delta"]
    hard_beats_conditioned = float(option_hard["observed"]) < float(conditioned_hard["observed"])
    hard_beats_regime = float(option_hard["observed"]) < float(regime_hard["observed"])
    hard_closes = float(option_hard["high"]) < 0.0
    full_not_degraded = float(option_full["observed"]) <= float(conditioned_full["observed"]) + 1.0e-9
    if hard_closes:
        verdict = (
            "Geometry-option conditioning closes the hard-only allocation slice under the current diagnostic. "
            "This is a candidate allocation-control result requiring independent export validation."
        )
    elif hard_beats_conditioned and hard_beats_regime:
        verdict = (
            "Geometry-option conditioning improves hard-only observed damage relative to both append-only geometry and "
            "geometry-regime weighting, but the hard-only interval remains open."
        )
    elif hard_beats_regime:
        verdict = (
            "Geometry-option conditioning improves over train-regime weighting but not over append-only geometry on the hard slice."
        )
    else:
        verdict = (
            "Geometry-option conditioning does not improve the hard-only allocation boundary relative to the existing geometry rows."
        )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_geometry_option_conditioned_allocation",
        "device": str(device),
        "feature_dims": {
            **feature_dims,
            "option_feature_dim": int(option_features(depths).shape[1]),
            "geometry_option_interaction_dim": int(features["train_env"].shape[1] * option_features(depths).shape[1]),
            "expanded_option_feature_dim": int(train_x.shape[1]),
        },
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "seed": int(args.seed),
            "loss": "option-error smooth L1 plus within-anchor pairwise ordering, selected by calibration exact-budget DP",
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
            "hard_beats_geometry_conditioned_observed": bool(hard_beats_conditioned),
            "hard_beats_geometry_regime_weighted_observed": bool(hard_beats_regime),
            "hard_closes": bool(hard_closes),
            "full_not_degraded_vs_geometry_conditioned_observed": bool(full_not_degraded),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "features": "aligned export x, explicit two-rooms geometry, candidate depth option token, and geometry-option interactions",
            "training_targets": "train option_error only; held-out hard episode identities are never used for training or calibration selection",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta, then train loss",
            "eval_targets": "eval option_error used only after fixed option scores are generated for metrics",
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
        option_depths=depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        geometry_option_conditioned_score=eval_score.astype(np.float64),
        geometry_conditioned_score=geometry_conditioned.astype(np.float64),
        geometry_regime_weighted_score=geometry_regime_weighted.astype(np.float64),
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

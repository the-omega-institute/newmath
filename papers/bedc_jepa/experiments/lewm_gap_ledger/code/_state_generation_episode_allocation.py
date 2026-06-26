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


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_allocation.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_allocation.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_episode_allocation_predictions.npz"


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


def standardizer(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = np.mean(x.astype(np.float64), axis=0).astype(np.float32)
    scale = np.std(x.astype(np.float64), axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def apply_standardizer(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def load_split(data: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    return {
        "x": data[f"{split}_x"].astype(np.float32),
        "episode": data[f"{split}_episode"].astype(np.int64),
        "anchor_ep_t0": data[f"{split}_anchor_ep_t0"].astype(np.int64),
        "option_error": data[f"{split}_option_error"].astype(np.float64),
        "uniform_error": data[f"{split}_uniform_error"].astype(np.float64),
        "true_mv": data[f"{split}_true_mv"].astype(np.float64),
    }


def option_payload(split: dict[str, np.ndarray], option_depths: np.ndarray) -> dict[str, np.ndarray]:
    uniform_col = int(np.where(option_depths == 3)[0][0])
    return {
        "episode": split["episode"].astype(np.int64),
        "option_error": split["option_error"].astype(np.float64),
        "uniform_error": split["option_error"][:, uniform_col].astype(np.float64),
        "true_mv": split["true_mv"].astype(np.float64),
    }


def centered_errors(option_error: np.ndarray) -> np.ndarray:
    return (option_error.astype(np.float64) - np.mean(option_error.astype(np.float64), axis=1, keepdims=True)).astype(np.float32)


def oracle_choice(split: dict[str, np.ndarray]) -> np.ndarray:
    return structured.exact_budget_choice(split["episode"], split["option_error"], structured.DEPTHS).astype(np.int64)


class EpisodeAllocationNet(nn.Module):
    def __init__(self, in_dim: int, options: int, hidden: int, depth: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        dim = in_dim
        for _ in range(depth):
            blocks.extend([nn.Linear(dim, hidden), nn.SiLU(), nn.LayerNorm(hidden), nn.Dropout(0.05)])
            dim = hidden
        self.trunk = nn.Sequential(*blocks)
        self.score = nn.Linear(dim, options)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.score(self.trunk(x))


def pairwise_loss(score: torch.Tensor, target: torch.Tensor) -> torch.Tensor:
    diff_score = score[:, :, None] - score[:, None, :]
    diff_target = target[:, :, None] - target[:, None, :]
    sign = torch.sign(diff_target)
    mask = torch.abs(diff_target) > 1.0e-7
    if not torch.any(mask):
        return score.sum() * 0.0
    return F.softplus(-sign[mask] * diff_score[mask]).mean()


def depth_balance_loss(score: torch.Tensor, oracle: torch.Tensor, depths: torch.Tensor) -> torch.Tensor:
    probs = torch.softmax(-score, dim=1)
    expected_depth = probs @ depths
    target_depth = depths[oracle]
    return F.smooth_l1_loss(expected_depth, target_depth)


def predict(model: EpisodeAllocationNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros((len(x), structured.DEPTHS.shape[0]), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def pair_accuracy(score: np.ndarray, truth: np.ndarray) -> float:
    good = 0
    total = 0
    for i in range(score.shape[1]):
        for j in range(i + 1, score.shape[1]):
            td = truth[:, i] - truth[:, j]
            sd = score[:, i] - score[:, j]
            mask = np.abs(td) > 1.0e-9
            good += int(np.sum(np.sign(td[mask]) == np.sign(sd[mask])))
            total += int(np.sum(mask))
    return clean_float(float(good / total)) if total else 0.0


def oracle_match(score: np.ndarray, oracle: np.ndarray) -> float:
    return clean_float(float(np.mean(np.argmin(score, axis=1).astype(np.int64) == oracle.astype(np.int64))))


def evaluate(split: dict[str, np.ndarray], score: np.ndarray, *, seed: int) -> dict[str, Any]:
    metrics = structured.evaluate_scores(option_payload(split, structured.DEPTHS), score, seed=seed)
    metrics["pair_accuracy"] = pair_accuracy(score, split["option_error"])
    metrics["oracle_match"] = oracle_match(score, oracle_choice(split))
    return metrics


def train_model(
    train_x: np.ndarray,
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
    batch: int,
    lr: float,
) -> tuple[EpisodeAllocationNet, dict[str, Any]]:
    model = EpisodeAllocationNet(train_x.shape[1], structured.DEPTHS.shape[0], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    target_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    oracle_t = torch.from_numpy(train_oracle.astype(np.int64)).to(device)
    depths_t = torch.from_numpy(structured.DEPTHS.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 800)
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
            ce = F.cross_entropy(-score, oracle_t[idx])
            rank = pairwise_loss(centered_score, target_t[idx])
            reg = F.smooth_l1_loss(centered_score, target_t[idx])
            balance = depth_balance_loss(score, oracle_t[idx], depths_t)
            loss = 0.50 * ce + 0.25 * rank + 0.15 * balance + 0.10 * reg
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_score = predict(model, cal_x, device, batch)
        cal_eval = evaluate(cal_split, cal_score, seed=seed + 1800 + epoch)
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
    rows = report["eval"]
    lines = [
        "# State-Generation Episode Allocation",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        "",
        "| scorer | allocation delta | rho | oracle match |",
        "|---|---:|---:|---:|",
    ]
    for name in ["episode_allocation", "allocation_native", "oracle_true_error"]:
        row = rows[name]
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('oracle_match', 0.0):.6g} |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an episode-level exact-budget allocation objective")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--allocation-native", default=str(REPORT_DIR / "state_generation_allocation_native_predictions.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=431)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    with np.load(Path(args.export), allow_pickle=False) as archive:
        data = {key: archive[key] for key in archive.files}
    train = load_split(data, "train")
    cal = load_split(data, "calibration")
    eval_split = load_split(data, "eval")
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    mean, scale = standardizer(train["x"])
    train_x = apply_standardizer(train["x"], mean, scale)
    cal_x = apply_standardizer(cal["x"], mean, scale)
    eval_x = apply_standardizer(eval_split["x"], mean, scale)
    train_oracle = oracle_choice(train)
    cal_oracle = oracle_choice(cal)
    eval_oracle = oracle_choice(eval_split)
    model, selection = train_model(
        train_x,
        centered_errors(train["option_error"]),
        train_oracle,
        cal_x,
        cal,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
    )
    eval_score = predict(model, eval_x, device, int(args.batch))
    with np.load(Path(args.allocation_native), allow_pickle=False) as native:
        allocation_native_score = native["allocation_native_score"].astype(np.float64)
    rows = {
        "episode_allocation": evaluate(eval_split, eval_score, seed=int(args.seed) + 901),
        "allocation_native": evaluate(eval_split, allocation_native_score, seed=int(args.seed) + 901),
        "oracle_true_error": evaluate(eval_split, eval_split["option_error"], seed=int(args.seed) + 901),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_allocation",
        "device": str(device),
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "loss": "0.50*oracle_choice_ce + 0.25*pairwise_order + 0.15*expected_depth + 0.10*centered_smooth_l1",
        },
        "counts": {
            "train": int(len(train_x)),
            "calibration": int(len(cal_x)),
            "eval": int(len(eval_x)),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "oracle_choice_counts": {
            "train": {str(int(k)): int(v) for k, v in zip(*np.unique(structured.DEPTHS[train_oracle], return_counts=True))},
            "calibration": {str(int(k)): int(v) for k, v in zip(*np.unique(structured.DEPTHS[cal_oracle], return_counts=True))},
            "eval": {str(int(k)): int(v) for k, v in zip(*np.unique(structured.DEPTHS[eval_oracle], return_counts=True))},
        },
        "selection": selection,
        "eval": rows,
        "diagnosis": {
            "allocation_closed": bool(float(rows["episode_allocation"]["allocation_delta"]["high"]) < 0.0),
            "beats_allocation_native_observed": bool(float(rows["episode_allocation"]["allocation_delta"]["observed"]) < float(rows["allocation_native"]["allocation_delta"]["observed"])),
            "beats_allocation_native_ci_high": bool(float(rows["episode_allocation"]["allocation_delta"]["high"]) < float(rows["allocation_native"]["allocation_delta"]["high"])),
            "oracle_closed": bool(float(rows["oracle_true_error"]["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "features": "aligned export x only",
            "targets": "train option_error is converted to exact-budget oracle choices; eval option_error used only after score generation for metrics",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["deployable policy", "complete BEDC-native world model"],
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
        episode_allocation_score=eval_score.astype(np.float64),
        allocation_native_score=allocation_native_score.astype(np.float64),
        oracle_choice=eval_oracle.astype(np.int64),
        chosen_col=chosen.astype(np.int64),
        chosen_depth=option_depths[chosen].astype(np.int64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

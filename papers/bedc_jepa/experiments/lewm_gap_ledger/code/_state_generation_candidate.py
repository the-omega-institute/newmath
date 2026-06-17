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

import _compute_value_model as cvm
import _compute_value_structured_assignment as structured
import _g2n_integrated_a100 as g2n
from _native_parity_candidate import bootstrap_mean, mse


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_candidate.json"
DEFAULT_MD = REPORT_DIR / "state_generation_candidate.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_candidate_predictions.npz"
BOOTSTRAPS = 500


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


class StateGenerationNet(nn.Module):
    def __init__(self, in_dim: int, z_dim: int, options: int, horizon_logits: int, hidden: int, depth: int) -> None:
        super().__init__()
        blocks: list[nn.Module] = []
        dim = in_dim
        for _ in range(depth):
            blocks.extend([nn.Linear(dim, hidden), nn.SiLU(), nn.LayerNorm(hidden), nn.Dropout(0.04)])
            dim = hidden
        self.trunk = nn.Sequential(*blocks)
        self.delta = nn.Linear(dim, z_dim)
        self.option_error = nn.Linear(dim, options)
        self.horizon = nn.Linear(dim, horizon_logits)

    def forward(self, x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
        h = self.trunk(x)
        return self.delta(h), self.option_error(h), self.horizon(h)


def load_split(data: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    return {
        "x": data[f"{split}_x"].astype(np.float32),
        "current_z": data[f"{split}_current_z"].astype(np.float32),
        "next_target": data[f"{split}_next_target"].astype(np.float32),
        "lewm_h1_mse": data[f"{split}_lewm_h1_mse"].astype(np.float64),
        "option_error": data[f"{split}_option_error"].astype(np.float64),
        "true_mv": data[f"{split}_true_mv"].astype(np.float64),
        "uniform_error": data[f"{split}_uniform_error"].astype(np.float64),
        "horizon_y": data[f"{split}_horizon_y"].astype(np.float32),
        "episode": data[f"{split}_episode"].astype(np.int64),
        "anchor_ep_t0": data[f"{split}_anchor_ep_t0"].astype(np.int64),
    }


def predict(model: StateGenerationNet, x: np.ndarray, current_z: np.ndarray, device: torch.device, batch: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    pred_z = np.zeros_like(current_z, dtype=np.float32)
    opt = np.zeros((len(x), 5), dtype=np.float64)
    horizon = np.zeros((len(x), 30), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            dz, oe, hy = model(xb)
            pred_z[start : start + batch] = current_z[start : start + batch] + dz.detach().cpu().numpy().astype(np.float32)
            opt[start : start + batch] = oe.detach().cpu().numpy().astype(np.float64)
            horizon[start : start + batch] = hy.detach().cpu().numpy().astype(np.float64)
    return pred_z, opt, horizon


def option_payload(split: dict[str, np.ndarray], option_depths: np.ndarray) -> dict[str, np.ndarray]:
    uniform_col = int(np.where(option_depths == 3)[0][0])
    return {
        "episode": split["episode"].astype(np.int64),
        "option_error": split["option_error"].astype(np.float64),
        "uniform_error": split["option_error"][:, uniform_col].astype(np.float64),
        "true_mv": split["true_mv"].astype(np.float64),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# State-Generation Candidate",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best_epoch']}`",
        "",
        "| metric | value | interval |",
        "|---|---:|---:|",
        f"| native h1 MSE | {rows['native_h1_mse']['observed']:.6g} | [{rows['native_h1_mse']['low']:.6g}, {rows['native_h1_mse']['high']:.6g}] |",
        f"| LeWM h1 MSE | {rows['lewm_h1_mse']['observed']:.6g} | [{rows['lewm_h1_mse']['low']:.6g}, {rows['lewm_h1_mse']['high']:.6g}] |",
        f"| parity margin | {rows['prediction_parity_margin']['observed']:.6g} | [{rows['prediction_parity_margin']['low']:.6g}, {rows['prediction_parity_margin']['high']:.6g}] |",
        f"| allocation delta | {rows['allocation_delta']['observed']:.6g} | [{rows['allocation_delta']['low']:.6g}, {rows['allocation_delta']['high']:.6g}] |",
        f"| mean horizon AUROC | {rows['mean_horizon_auroc']:.6g} | -- |",
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a first aligned BEDC-native state-generation candidate")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=191)
    parser.add_argument("--epochs", type=int, default=80)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4e-4)
    parser.add_argument("--epsilon", type=float, default=0.10)
    args = parser.parse_args()
    start_time = time.time()
    device = configure(int(args.seed))
    with np.load(Path(args.export), allow_pickle=False) as z:
        data = {k: z[k] for k in z.files}
    option_depths = data["option_depths"].astype(np.int64)
    train = load_split(data, "train")
    cal = load_split(data, "calibration")
    eval_split = load_split(data, "eval")
    x_mean, x_scale = standardizer(train["x"])
    train_x = apply_standardizer(train["x"], x_mean, x_scale)
    cal_x = apply_standardizer(cal["x"], x_mean, x_scale)
    eval_x = apply_standardizer(eval_split["x"], x_mean, x_scale)
    dz_train = train["next_target"] - train["current_z"]
    dz_cal = cal["next_target"] - cal["current_z"]
    y_h_train = train["horizon_y"].reshape(len(train["x"]), -1)
    y_h_cal = cal["horizon_y"].reshape(len(cal["x"]), -1)
    model = StateGenerationNet(train_x.shape[1], train["current_z"].shape[1], len(option_depths), y_h_train.shape[1], int(args.hidden), int(args.depth)).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=float(args.lr), weight_decay=1e-4)
    rng = np.random.default_rng(int(args.seed) + 300)
    train_idx = np.arange(len(train_x))
    x_t = torch.from_numpy(train_x).to(device)
    dz_t = torch.from_numpy(dz_train.astype(np.float32)).to(device)
    opt_t = torch.from_numpy(train["option_error"].astype(np.float32)).to(device)
    h_t = torch.from_numpy(y_h_train.astype(np.float32)).to(device)
    best_state = None
    best_key = (float("inf"), float("inf"))
    history: list[dict[str, float]] = []
    for epoch in range(int(args.epochs)):
        model.train()
        order = rng.permutation(train_idx)
        losses: list[float] = []
        for pos in range(0, len(order), int(args.batch)):
            idx_np = order[pos : pos + int(args.batch)]
            idx = torch.as_tensor(idx_np, dtype=torch.long, device=device)
            dz, oe, hy = model(x_t[idx])
            pred_loss = F.smooth_l1_loss(dz, dz_t[idx])
            opt_loss = F.smooth_l1_loss(oe, opt_t[idx])
            h_loss = F.binary_cross_entropy_with_logits(hy, h_t[idx])
            loss = pred_loss + 0.35 * opt_loss + 0.10 * h_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_pred, cal_opt, cal_h = predict(model, cal_x, cal["current_z"], device, int(args.batch))
        cal_native = mse(cal_pred, cal["next_target"])
        cal_option_mse = float(np.mean((cal_opt - cal["option_error"]) ** 2))
        cal_key = (float(np.mean(cal_native)), cal_option_mse)
        history.append({"epoch": float(epoch + 1), "train_loss": clean_float(float(np.mean(losses))), "cal_h1_mse": clean_float(cal_key[0]), "cal_option_mse": clean_float(cal_key[1])})
        if cal_key < best_key:
            best_key = cal_key
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    eval_pred, eval_opt, eval_h = predict(model, eval_x, eval_split["current_z"], device, int(args.batch))
    native_h1 = mse(eval_pred, eval_split["next_target"])
    lewm_h1 = eval_split["lewm_h1_mse"].astype(np.float64)
    threshold = (1.0 + float(args.epsilon)) * float(np.mean(lewm_h1))
    parity_values = threshold - native_h1
    allocation = structured.evaluate_scores(option_payload(eval_split, option_depths), eval_opt, seed=int(args.seed) + 17)
    horizon_flat = eval_split["horizon_y"].reshape(len(eval_split["x"]), -1)
    aurocs = []
    for col in range(horizon_flat.shape[1]):
        y = horizon_flat[:, col]
        if len(np.unique(y)) == 2:
            aurocs.append(float(g2n.auroc_rank(y.astype(np.int64), eval_h[:, col].astype(np.float64))))
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_candidate",
        "device": str(device),
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "epsilon": float(args.epsilon),
            "loss": "smooth_l1_next_delta + 0.35*smooth_l1_option_error + 0.10*horizon_bce",
        },
        "counts": {
            "train": int(len(train_x)),
            "calibration": int(len(cal_x)),
            "eval": int(len(eval_x)),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "selection": {"best_epoch": int(min(history, key=lambda r: (r["cal_h1_mse"], r["cal_option_mse"]))["epoch"]), "best_key": list(best_key)},
        "eval": {
            "native_h1_mse": bootstrap_mean(native_h1, eval_split["episode"], int(args.seed) + 1),
            "lewm_h1_mse": bootstrap_mean(lewm_h1, eval_split["episode"], int(args.seed) + 2),
            "prediction_parity_margin": bootstrap_mean(parity_values, eval_split["episode"], int(args.seed) + 3),
            "allocation_delta": allocation["allocation_delta"],
            "score_error_spearman": clean_float(float(allocation["score_error_spearman"])),
            "mean_horizon_auroc": clean_float(float(np.mean(aurocs))) if aurocs else 0.0,
            "valid_horizon_auc_count": int(len(aurocs)),
        },
        "history": history,
        "leakage_attestation": {
            "features": "Only aligned export x is used as input.",
            "targets": "next_target, option_error, and horizon_y are used only as supervised targets.",
            "selection": "epoch selection uses calibration next-latent and option-error losses before eval readout.",
        },
        "not_claimed": ["prediction parity", "universal control", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    np.savez_compressed(
        Path(args.out),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        pred_next_z=eval_pred.astype(np.float32),
        target_next_z=eval_split["next_target"].astype(np.float32),
        lewm_h1_mse=lewm_h1.astype(np.float64),
        native_h1_mse=native_h1.astype(np.float64),
        predicted_option_error=eval_opt.astype(np.float64),
        option_error=eval_split["option_error"].astype(np.float64),
        horizon_logits=eval_h.astype(np.float64),
        horizon_y=eval_split["horizon_y"].astype(np.int8),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

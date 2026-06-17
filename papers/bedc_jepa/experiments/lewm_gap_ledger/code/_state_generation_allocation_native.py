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


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_allocation_native.json"
DEFAULT_MD = REPORT_DIR / "state_generation_allocation_native.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_allocation_native_predictions.npz"


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


class AllocationScoreNet(nn.Module):
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


def uniform_margin_loss(score: torch.Tensor, target: torch.Tensor, uniform_col: int) -> torch.Tensor:
    diff_target = target - target[:, [uniform_col]]
    diff_score = score - score[:, [uniform_col]]
    sign = torch.sign(diff_target)
    mask = torch.abs(diff_target) > 1.0e-7
    if not torch.any(mask):
        return score.sum() * 0.0
    return F.softplus(-sign[mask] * diff_score[mask]).mean()


def predict(model: AllocationScoreNet, x: np.ndarray, device: torch.device, batch: int) -> np.ndarray:
    out = np.zeros((len(x), structured.DEPTHS.shape[0]), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            out[start : start + batch] = model(xb).detach().cpu().numpy().astype(np.float64)
    return out


def exact_budget_oracle(payload: dict[str, np.ndarray], *, seed: int) -> dict[str, Any]:
    return structured.exact_oracle(payload, seed=seed)


def train_model(
    train_x: np.ndarray,
    train_target: np.ndarray,
    cal_x: np.ndarray,
    cal_payload: dict[str, np.ndarray],
    *,
    device: torch.device,
    seed: int,
    hidden: int,
    depth: int,
    epochs: int,
    batch: int,
    lr: float,
    uniform_col: int,
) -> tuple[AllocationScoreNet, dict[str, Any]]:
    model = AllocationScoreNet(train_x.shape[1], structured.DEPTHS.shape[0], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    rng = np.random.default_rng(seed + 501)
    order_base = np.arange(len(train_x))
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(order_base)
        losses: list[float] = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            score = model(x_t[idx])
            target = y_t[idx]
            centered_score = score - torch.mean(score, dim=1, keepdim=True)
            reg = F.smooth_l1_loss(centered_score, target)
            rank = pairwise_loss(centered_score, target)
            margin = uniform_margin_loss(centered_score, target, uniform_col)
            loss = 0.30 * reg + 0.55 * rank + 0.15 * margin
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_score = predict(model, cal_x, device, batch)
        cal_eval = structured.evaluate_scores(cal_payload, cal_score, seed=seed + 1300 + epoch)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), -float(cal_eval["pair_accuracy"]) if "pair_accuracy" in cal_eval else 0.0)
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_delta_observed": clean_float(float(delta["observed"])),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_spearman": clean_float(float(cal_eval["score_error_spearman"])),
            }
        )
        if key < best_key:
            best_key = key
            best_report = {"epoch": int(epoch + 1), "calibration": cal_eval, "selection_key": list(key)}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta",
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def pair_accuracy(score: np.ndarray, truth: np.ndarray) -> float:
    good = 0
    total = 0
    for i in range(score.shape[1]):
        for j in range(i + 1, score.shape[1]):
            true_diff = truth[:, i] - truth[:, j]
            score_diff = score[:, i] - score[:, j]
            mask = np.abs(true_diff) > 1.0e-9
            good += int(np.sum(np.sign(true_diff[mask]) == np.sign(score_diff[mask])))
            total += int(np.sum(mask))
    return clean_float(float(good / total)) if total else 0.0


def add_score_diagnostics(metrics: dict[str, Any], score: np.ndarray, truth: np.ndarray) -> dict[str, Any]:
    out = dict(metrics)
    out["pair_accuracy"] = pair_accuracy(score, truth)
    return out


def fit_depth_affine(score: np.ndarray, truth: np.ndarray) -> dict[str, np.ndarray]:
    coef = np.zeros((score.shape[1], 2), dtype=np.float64)
    for col in range(score.shape[1]):
        x = np.stack([score[:, col], np.ones(score.shape[0], dtype=np.float64)], axis=1)
        coef[col] = np.linalg.lstsq(x, truth[:, col], rcond=None)[0]
    return {"coef": coef}


def apply_depth_affine(score: np.ndarray, fit: dict[str, np.ndarray]) -> np.ndarray:
    coef = fit["coef"]
    return (score * coef[:, 0][None, :] + coef[:, 1][None, :]).astype(np.float64)


def flat_calibration_features(score: np.ndarray, depths: np.ndarray) -> np.ndarray:
    centered_depth = ((depths.astype(np.float64) - 3.0) / 2.0).reshape(1, -1)
    d = np.repeat(centered_depth, score.shape[0], axis=0)
    s = score.astype(np.float64)
    return np.stack(
        [
            s.reshape(-1),
            d.reshape(-1),
            (d * d).reshape(-1),
            (s * d).reshape(-1),
            (s * d * d).reshape(-1),
            np.ones(s.size, dtype=np.float64),
        ],
        axis=1,
    )


def fit_ridge_calibrator(score: np.ndarray, truth: np.ndarray, depths: np.ndarray, alpha: float) -> dict[str, np.ndarray]:
    x = flat_calibration_features(score, depths)
    y = truth.reshape(-1).astype(np.float64)
    eye = np.eye(x.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    coef = np.linalg.solve(x.T @ x + float(alpha) * eye, x.T @ y)
    return {"coef": coef.astype(np.float64), "alpha": np.asarray([float(alpha)], dtype=np.float64)}


def apply_ridge_calibrator(score: np.ndarray, depths: np.ndarray, fit: dict[str, np.ndarray]) -> np.ndarray:
    x = flat_calibration_features(score, depths)
    pred = x @ fit["coef"]
    return pred.reshape(score.shape).astype(np.float64)


def select_calibrated_score(
    cal_payload: dict[str, np.ndarray],
    cal_score: np.ndarray,
    eval_score: np.ndarray,
    cal_truth: np.ndarray,
    *,
    seed: int,
) -> dict[str, Any]:
    candidates: list[tuple[str, np.ndarray, np.ndarray]] = [("raw", cal_score.astype(np.float64), eval_score.astype(np.float64))]
    depth_fit = fit_depth_affine(cal_score, cal_truth)
    candidates.append(("depth_affine", apply_depth_affine(cal_score, depth_fit), apply_depth_affine(eval_score, depth_fit)))
    for alpha in [1.0e-4, 1.0e-3, 1.0e-2, 1.0e-1, 1.0, 10.0]:
        fit = fit_ridge_calibrator(cal_score, cal_truth, structured.DEPTHS.astype(np.int64), alpha)
        candidates.append((f"ridge_{alpha:g}", apply_ridge_calibrator(cal_score, structured.DEPTHS, fit), apply_ridge_calibrator(eval_score, structured.DEPTHS, fit)))
    rows: dict[str, Any] = {}
    best_name = ""
    best_key = (float("inf"), float("inf"))
    best_cal = cal_score
    best_eval = eval_score
    for offset, (name, cal_variant, eval_variant) in enumerate(candidates):
        metrics = structured.evaluate_scores(cal_payload, cal_variant, seed=seed + offset)
        rows[name] = metrics
        delta = metrics["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]))
        if key < best_key:
            best_key = key
            best_name = name
            best_cal = cal_variant
            best_eval = eval_variant
    return {
        "selected": best_name,
        "selection_key": list(best_key),
        "calibration": rows,
        "calibration_score": best_cal.astype(np.float64),
        "eval_score": best_eval.astype(np.float64),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    rows = report["eval"]
    lines = [
        "# State-Generation Allocation-Native Candidate",
        "",
        f"- device: `{report['device']}`",
        f"- selected epoch: `{report['selection']['best']['epoch']}`",
        "",
        "| scorer | allocation delta | rho | pair accuracy |",
        "|---|---:|---:|---:|",
    ]
    for name in ["allocation_native", "calibrated_allocation_native", "raw_state_generation_candidate", "oracle_true_error"]:
        row = rows[name]
        d = row["allocation_delta"]
        lines.append(
            f"| `{name}` | {d['observed']:.6g} [{d['low']:.6g}, {d['high']:.6g}] | "
            f"{row['score_error_spearman']:.6g} | {row.get('pair_accuracy', 0.0):.6g} |"
        )
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train an allocation-native option scorer on the aligned state-generation export")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--baseline", default=str(REPORT_DIR / "state_generation_candidate_predictions.npz"))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=281)
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    args = parser.parse_args()
    start = time.time()
    device = configure(int(args.seed))
    with np.load(Path(args.export), allow_pickle=False) as archive:
        data = {key: archive[key] for key in archive.files}
    option_depths = data["option_depths"].astype(np.int64)
    if not np.array_equal(option_depths, structured.DEPTHS.astype(np.int64)):
        raise ValueError(f"option depths mismatch: {option_depths} vs {structured.DEPTHS}")
    train = load_split(data, "train")
    cal = load_split(data, "calibration")
    eval_split = load_split(data, "eval")
    mean, scale = standardizer(train["x"])
    train_x = apply_standardizer(train["x"], mean, scale)
    cal_x = apply_standardizer(cal["x"], mean, scale)
    eval_x = apply_standardizer(eval_split["x"], mean, scale)
    train_target = centered_errors(train["option_error"])
    uniform_col = int(np.where(option_depths == 3)[0][0])
    cal_payload = option_payload(cal, option_depths)
    eval_payload = option_payload(eval_split, option_depths)
    model, selection = train_model(
        train_x,
        train_target,
        cal_x,
        cal_payload,
        device=device,
        seed=int(args.seed),
        hidden=int(args.hidden),
        depth=int(args.depth),
        epochs=int(args.epochs),
        batch=int(args.batch),
        lr=float(args.lr),
        uniform_col=uniform_col,
    )
    eval_score = predict(model, eval_x, device, int(args.batch))
    cal_score = predict(model, cal_x, device, int(args.batch))
    calibration = select_calibrated_score(
        cal_payload,
        cal_score,
        eval_score,
        cal["option_error"],
        seed=int(args.seed) + 1700,
    )
    calibrated_eval_score = calibration["eval_score"]
    native_metrics = add_score_diagnostics(
        structured.evaluate_scores(eval_payload, eval_score, seed=int(args.seed) + 701),
        eval_score,
        eval_split["option_error"],
    )
    calibrated_metrics = add_score_diagnostics(
        structured.evaluate_scores(eval_payload, calibrated_eval_score, seed=int(args.seed) + 702),
        calibrated_eval_score,
        eval_split["option_error"],
    )
    baseline_path = Path(args.baseline)
    with np.load(baseline_path, allow_pickle=False) as baseline:
        raw_score = baseline["predicted_option_error"].astype(np.float64)
    raw_metrics = add_score_diagnostics(
        structured.evaluate_scores(eval_payload, raw_score, seed=int(args.seed) + 703),
        raw_score,
        eval_split["option_error"],
    )
    oracle_metrics = add_score_diagnostics(
        exact_budget_oracle(eval_payload, seed=int(args.seed) + 709),
        eval_split["option_error"],
        eval_split["option_error"],
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_allocation_native",
        "device": str(device),
        "config": {
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "loss": "0.30*centered_smooth_l1 + 0.55*pairwise_order + 0.15*uniform_margin",
        },
        "counts": {
            "train": int(len(train_x)),
            "calibration": int(len(cal_x)),
            "eval": int(len(eval_x)),
            "eval_episodes": int(len(np.unique(eval_split["episode"]))),
        },
        "selection": selection,
        "score_calibration": {
            "selection_rule": "fit transforms on calibration split and choose the transform with lowest calibration exact-budget allocation_delta CI high, then observed delta",
            "selected": calibration["selected"],
            "selection_key": calibration["selection_key"],
            "calibration": calibration["calibration"],
        },
        "eval": {
            "allocation_native": native_metrics,
            "calibrated_allocation_native": calibrated_metrics,
            "raw_state_generation_candidate": raw_metrics,
            "oracle_true_error": oracle_metrics,
        },
        "diagnosis": {
            "allocation_closed": bool(float(native_metrics["allocation_delta"]["high"]) < 0.0),
            "calibrated_allocation_closed": bool(float(calibrated_metrics["allocation_delta"]["high"]) < 0.0),
            "beats_raw_observed": bool(float(native_metrics["allocation_delta"]["observed"]) < float(raw_metrics["allocation_delta"]["observed"])),
            "beats_raw_ci_high": bool(float(native_metrics["allocation_delta"]["high"]) < float(raw_metrics["allocation_delta"]["high"])),
            "calibrated_beats_raw_observed": bool(float(calibrated_metrics["allocation_delta"]["observed"]) < float(raw_metrics["allocation_delta"]["observed"])),
            "calibrated_beats_raw_ci_high": bool(float(calibrated_metrics["allocation_delta"]["high"]) < float(raw_metrics["allocation_delta"]["high"])),
            "oracle_closed": bool(float(oracle_metrics["allocation_delta"]["high"]) < 0.0),
        },
        "leakage_attestation": {
            "features": "aligned export x only",
            "targets": "option_error is used for allocation-native training; eval option_error is used only after score generation for metrics",
            "selection": "calibration exact-budget allocation_delta CI high, then observed delta",
            "baseline": str(baseline_path),
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["prediction parity", "deployable policy", "complete BEDC-native world model"],
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    chosen = structured.exact_budget_choice(eval_payload["episode"], eval_score, structured.DEPTHS)
    np.savez_compressed(
        Path(args.out),
        calibration_episode=cal["episode"].astype(np.int64),
        calibration_anchor_ep_t0=cal["anchor_ep_t0"].astype(np.int64),
        calibration_option_error=cal["option_error"].astype(np.float64),
        calibration_allocation_native_score=cal_score.astype(np.float64),
        calibration_calibrated_allocation_native_score=calibration["calibration_score"].astype(np.float64),
        episode=eval_split["episode"].astype(np.int64),
        anchor_ep_t0=eval_split["anchor_ep_t0"].astype(np.int64),
        option_depths=option_depths.astype(np.int64),
        option_error=eval_split["option_error"].astype(np.float64),
        allocation_native_score=eval_score.astype(np.float64),
        calibrated_allocation_native_score=calibrated_eval_score.astype(np.float64),
        raw_state_generation_score=raw_score.astype(np.float64),
        allocation_native_chosen_depth=option_depths[chosen].astype(np.int64),
        allocation_native_chosen_col=chosen.astype(np.int64),
    )
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

import _compute_value_model as cvm
import _compute_value_refined_option_model as refined
import _compute_value_structured_assignment as structured
import _g2n_integrated_a100 as g2n


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_joint_horizon_option.json"
DEFAULT_MD = REPORT_DIR / "compute_value_joint_horizon_option.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_joint_horizon_option_predictions.npz"
DEPTHS = refined.DEPTHS
Q75 = 75


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


def q75_index(labels: dict[str, np.ndarray]) -> int:
    quantiles = [int(item) for item in labels["quantiles"].reshape(-1)]
    if Q75 not in quantiles:
        raise RuntimeError("missing q75")
    return int(quantiles.index(Q75))


def horizon_indices(labels: dict[str, np.ndarray]) -> list[int]:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    missing = [int(depth) for depth in DEPTHS if int(depth) not in horizons]
    if missing:
        raise RuntimeError(f"missing horizons: {missing}")
    return [horizons.index(int(depth)) for depth in DEPTHS]


def split_joint_payload(labels: dict[str, np.ndarray], latents: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    payload = refined.split_payload(labels, latents, split)
    indices = horizon_indices(labels)
    q75 = q75_index(labels)
    valid = labels[f"{split}_valid"][:, indices].all(axis=1)
    y = labels[f"{split}_y"][valid][:, indices, q75].astype(np.float32)
    if len(y) != len(payload["episode"]):
        raise RuntimeError(f"joint payload mismatch for {split}: {len(y)} vs {len(payload['episode'])}")
    out = dict(payload)
    out["horizon_y"] = y
    return out


class JointHorizonOptionNet(nn.Module):
    def __init__(self, x_dim: int, hidden: int) -> None:
        super().__init__()
        self.trunk = nn.Sequential(
            nn.Linear(x_dim, hidden),
            nn.SiLU(),
            nn.LayerNorm(hidden),
            nn.Dropout(0.05),
            nn.Linear(hidden, hidden),
            nn.SiLU(),
            nn.LayerNorm(hidden),
        )
        self.horizon = nn.Linear(hidden, len(DEPTHS))
        self.option = nn.Sequential(
            nn.Linear(hidden + 5, hidden // 2),
            nn.SiLU(),
            nn.LayerNorm(hidden // 2),
            nn.Linear(hidden // 2, 1),
        )

    def forward(self, x: torch.Tensor, opt_feat: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        state = self.trunk(x)
        logits = self.horizon(state)
        expanded_state = state.repeat_interleave(len(DEPTHS), dim=0)
        option_score = self.option(torch.cat([expanded_state, opt_feat], dim=1)).squeeze(-1)
        return logits, option_score


def tiled_option_features(n: int) -> np.ndarray:
    opt = structured.option_features(DEPTHS)
    return np.tile(opt, (n, 1)).astype(np.float32)


def predict(model: JointHorizonOptionNet, x: np.ndarray, device: torch.device, batch: int) -> tuple[np.ndarray, np.ndarray]:
    logits = np.zeros((len(x), len(DEPTHS)), dtype=np.float64)
    scores = np.zeros((len(x), len(DEPTHS)), dtype=np.float64)
    model.eval()
    with torch.inference_mode():
        for start in range(0, len(x), batch):
            xb = torch.from_numpy(x[start : start + batch].astype(np.float32)).to(device)
            opt = torch.from_numpy(tiled_option_features(len(xb))).to(device)
            logit, flat = model(xb, opt)
            logits[start : start + len(xb)] = logit.detach().cpu().numpy().astype(np.float64)
            scores[start : start + len(xb)] = flat.detach().cpu().numpy().reshape(len(xb), len(DEPTHS)).astype(np.float64)
    return logits, scores


def train_row(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    *,
    train_x: np.ndarray,
    cal_x: np.ndarray,
    device: torch.device,
    seed: int,
    epochs: int,
    hidden: int,
    batch: int,
    lr: float,
    horizon_weight: float,
) -> tuple[JointHorizonOptionNet, dict[str, Any]]:
    torch.manual_seed(seed + 1901)
    if device.type == "cuda":
        torch.cuda.manual_seed_all(seed + 1901)
    model = JointHorizonOptionNet(train_x.shape[1], hidden).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_train = torch.from_numpy(train_x.astype(np.float32)).to(device)
    x_cal = torch.from_numpy(cal_x.astype(np.float32)).to(device)
    opt_train = torch.from_numpy(tiled_option_features(len(train_x))).to(device)
    opt_cal = torch.from_numpy(tiled_option_features(len(cal_x))).to(device)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    option_train = torch.from_numpy(((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)).to(device)
    option_cal = torch.from_numpy(((cal["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)).to(device)
    horizon_train = torch.from_numpy(train["horizon_y"].astype(np.float32)).to(device)
    horizon_cal = torch.from_numpy(cal["horizon_y"].astype(np.float32)).to(device)
    true_rank = torch.from_numpy(train["option_error"].astype(np.float32)).to(device)
    rng = np.random.default_rng(seed + 1901)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best_report: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n_train = len(train_x)
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(n_train)
        losses: list[float] = []
        for start in range(0, n_train, batch):
            rows = order[start : start + batch]
            row_t = torch.as_tensor(rows, dtype=torch.long, device=device)
            flat_idx = torch.cat([row_t * len(DEPTHS) + j for j in range(len(DEPTHS))], dim=0)
            logits, flat_score = model(x_train[row_t], opt_train[flat_idx])
            point_loss = F.smooth_l1_loss(flat_score, option_train[flat_idx])
            pred_options = flat_score.reshape(len(row_t), len(DEPTHS))
            diff_pred = pred_options[:, :, None] - pred_options[:, None, :]
            diff_true = true_rank[row_t, :, None] - true_rank[row_t, None, :]
            sign = torch.sign(diff_true)
            mask = torch.abs(diff_true) > 1.0e-6
            rank_loss = F.softplus(-sign[mask] * diff_pred[mask]).mean() if torch.any(mask) else point_loss * 0.0
            horizon_loss = F.binary_cross_entropy_with_logits(logits, horizon_train[row_t])
            loss = point_loss + 0.25 * rank_loss + float(horizon_weight) * horizon_loss
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        model.eval()
        with torch.inference_mode():
            cal_logits, cal_flat = model(x_cal, opt_cal)
            cal_option_loss = float(F.smooth_l1_loss(cal_flat, option_cal).detach().cpu())
            cal_horizon_loss = float(F.binary_cross_entropy_with_logits(cal_logits, horizon_cal).detach().cpu())
        _, cal_score = predict(model, cal_x, device, batch)
        cal_score = cal_score * y_scale + y_mean
        cal_eval = structured.evaluate_scores(cal, cal_score, seed=seed + 2011)
        delta = cal_eval["allocation_delta"]
        key = (float(delta["high"]), float(delta["observed"]), cal_option_loss + float(horizon_weight) * cal_horizon_loss)
        history.append(
            {
                "epoch": float(epoch + 1),
                "train_loss": clean_float(float(np.mean(losses))),
                "cal_option_loss": clean_float(cal_option_loss),
                "cal_horizon_loss": clean_float(cal_horizon_loss),
                "cal_delta_high": clean_float(float(delta["high"])),
                "cal_delta_observed": clean_float(float(delta["observed"])),
            }
        )
        if key < best_key:
            best_key = key
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
            best_report = {
                "epoch": int(epoch + 1),
                "calibration": cal_eval,
                "cal_option_loss": clean_float(cal_option_loss),
                "cal_horizon_loss": clean_float(cal_horizon_loss),
            }
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "minimize calibration exact-budget allocation_delta CI high, then observed delta, then joint loss",
        "horizon_weight": clean_float(float(horizon_weight)),
        "best": best_report,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
        "y_mean": clean_float(y_mean),
        "y_scale": clean_float(y_scale),
    }


def horizon_risk_scores(logits: np.ndarray) -> np.ndarray:
    probs = 1.0 / (1.0 + np.exp(-logits.astype(np.float64)))
    centered = probs - probs[:, [int(np.where(DEPTHS == 3)[0][0])]]
    return centered.astype(np.float64)


def horizon_auc(payload: dict[str, np.ndarray], logits: np.ndarray) -> dict[str, float]:
    out: dict[str, float] = {}
    for col, depth in enumerate(DEPTHS):
        y = payload["horizon_y"][:, col].astype(np.int64)
        if len(np.unique(y)) < 2:
            out[f"h{int(depth)}"] = 0.5
        else:
            out[f"h{int(depth)}"] = clean_float(g2n.auroc_rank(y, logits[:, col].astype(np.float64)))
    return out


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Joint Horizon Option",
        "",
        f"- device: `{report['device']}`",
        f"- selected row: `{report['selected_row']}`",
        f"- eval anchors: `{report['counts']['eval']}` across `{report['counts']['eval_episodes']}` episodes",
        "",
        "| row | allocation delta | score/error rho | mean horizon AUROC |",
        "|---|---:|---:|---:|",
    ]
    for name in report["row_order"]:
        row = report["eval"][name]
        d = row["allocation_delta"]
        mean_auc = float(np.mean(list(report["horizon_auc"][name].values()))) if name in report["horizon_auc"] else 0.0
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {row.get('score_error_spearman', 0.0):.9g} | {mean_auc:.9g} |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a joint horizon-logit and option-conditioned compute-value model")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=41)
    parser.add_argument("--epochs", type=int, default=280)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--batch", type=int, default=512)
    parser.add_argument("--lr", type=float, default=8.0e-4)
    args = parser.parse_args()

    start = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    labels_path = cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = cvm.load_npz(labels_path)
    latents = cvm.load_npz(latents_path)
    train = split_joint_payload(labels, latents, "train")
    cal = split_joint_payload(labels, latents, "calibration")
    eval_payload = split_joint_payload(labels, latents, "eval")
    x_mean, x_scale = structured.fit_standardizer(train["x"])
    x_train = structured.standardize(train["x"], x_mean, x_scale)
    x_cal = structured.standardize(cal["x"], x_mean, x_scale)
    x_eval = structured.standardize(eval_payload["x"], x_mean, x_scale)

    rows: dict[str, Any] = {}
    eval_scores: dict[str, np.ndarray] = {}
    eval_logits: dict[str, np.ndarray] = {}
    for name, horizon_weight in [("option_only", 0.0), ("joint_horizon_option", 0.25)]:
        model, health = train_row(
            train,
            cal,
            train_x=x_train,
            cal_x=x_cal,
            device=device,
            seed=int(args.seed) + (0 if name == "option_only" else 100),
            epochs=int(args.epochs),
            hidden=int(args.hidden),
            batch=int(args.batch),
            lr=float(args.lr),
            horizon_weight=float(horizon_weight),
        )
        logits, score = predict(model, x_eval, device, int(args.batch))
        score = score * float(health["y_scale"]) + float(health["y_mean"])
        rows[name] = {"health": health, "eval": structured.evaluate_scores(eval_payload, score, seed=int(args.seed) + 301)}
        eval_scores[name] = score
        eval_logits[name] = logits

    selected = min(
        rows,
        key=lambda name: (
            float(rows[name]["health"]["best"]["calibration"]["allocation_delta"]["high"]),
            float(rows[name]["health"]["best"]["calibration"]["allocation_delta"]["observed"]),
            name,
        ),
    )
    chosen = structured.exact_budget_choice(eval_payload["episode"], eval_scores[selected], DEPTHS)
    structured.write_npz(Path(args.out), eval_payload, eval_scores[selected], chosen, selected)
    horizon_score = horizon_risk_scores(eval_logits["joint_horizon_option"])
    horizon_choice = structured.exact_budget_choice(eval_payload["episode"], horizon_score, DEPTHS)
    eval_rows = {
        "exact_budget_oracle": structured.exact_oracle(eval_payload, seed=int(args.seed) + 311),
        "option_only": rows["option_only"]["eval"],
        "joint_horizon_option": rows["joint_horizon_option"]["eval"],
        "horizon_risk_dp": structured.evaluate_choice(eval_payload, horizon_choice, seed=int(args.seed) + 313),
    }
    eval_rows["horizon_risk_dp"]["score_error_spearman"] = cvm.spearman(horizon_score.reshape(-1), eval_payload["option_error"].reshape(-1))
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_joint_horizon_option",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
            "feature_dim": int(train["x"].shape[1]),
        },
        "target": {
            "option_depths": DEPTHS.tolist(),
            "horizon_quantile": Q75,
            "assignment_rule": "exact per-episode budget sum(depth)=3*episode_anchor_count using dynamic programming",
        },
        "row_order": ["exact_budget_oracle", "option_only", "joint_horizon_option", "horizon_risk_dp"],
        "selected_row": selected,
        "calibration": {name: rows[name]["health"]["best"]["calibration"] for name in rows},
        "health": {name: rows[name]["health"] for name in rows},
        "eval": eval_rows,
        "horizon_auc": {name: horizon_auc(eval_payload, eval_logits[name]) for name in eval_logits},
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only",
            "target_standardizer": "fit on train option_error only per row",
            "model_selection": "calibration split exact-budget allocation only",
            "eval_truth_usage": "eval option_error and horizon labels used only after predicted scores/logits are produced",
            "distillation": "absent",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "selected_row": selected, "eval": eval_rows}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn.functional as F

import _state_generation_budget_conditioned_value as budget_value
import _state_generation_candidate_oracle_gap as oracle_gap
import _state_generation_environment_state_descriptors as env_desc
import _state_generation_episode_allocation as episode_alloc
import _state_generation_hard_perturbation_value as hard_value
import _state_generation_hard_perturbation_value_learner as base_learner


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_mechanism_target_learner.json"
DEFAULT_MD = REPORT_DIR / "state_generation_mechanism_target_learner.md"
DEFAULT_OUT = REPORT_DIR / "state_generation_mechanism_target_learner_predictions.npz"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BASE_LEARNER_PRED = REPORT_DIR / "state_generation_hard_perturbation_value_learner_predictions.npz"
TARGET_AUDIT_PRED = REPORT_DIR / "state_generation_mechanism_aware_assignment_target_predictions.npz"
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


def flatten_targets(targets: dict[int, np.ndarray], budgets: np.ndarray) -> np.ndarray:
    return np.concatenate([targets[int(budget)].reshape(-1) for budget in budgets.astype(np.int64)], axis=0).astype(np.float64)


def tail_weights(targets: dict[int, np.ndarray], budgets: np.ndarray, tail_weight: float) -> np.ndarray:
    rows: list[np.ndarray] = []
    for budget in budgets.astype(np.int64):
        y = targets[int(budget)].reshape(-1).astype(np.float64)
        threshold = float(np.quantile(y, 0.90))
        rows.append((1.0 + float(tail_weight) * (y >= threshold).astype(np.float64)).astype(np.float32))
    return np.concatenate(rows, axis=0).astype(np.float32)


def mean_label_rho(split: dict[str, np.ndarray], depths: np.ndarray, scores: dict[int, np.ndarray]) -> float:
    labels = base_learner.forced_delta_targets(split, depths, BUDGETS)
    return mean_label_rho_from_labels(labels, scores)


def mean_label_rho_from_labels(labels: dict[int, np.ndarray], scores: dict[int, np.ndarray]) -> float:
    rhos = [
        hard_value.spearman(scores[int(budget)].reshape(-1), labels[int(budget)].reshape(-1))
        for budget in BUDGETS.astype(np.int64)
    ]
    return clean_float(float(np.mean(rhos)))


def observed_capture(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray) -> tuple[float, float]:
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget in BUDGETS.astype(np.int64):
        oracle_eps, oracle_values = oracle_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = oracle_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        captures.append(float(score_mean / oracle_mean) if oracle_mean < 0.0 else 0.0)
        regrets.append(float(np.mean(score_values - oracle_values)))
    return clean_float(float(np.mean(captures))), clean_float(float(np.mean(regrets)))


def capture_summary(split: dict[str, np.ndarray], scores: dict[int, np.ndarray], mask: np.ndarray, *, seed: int, samples: int) -> dict[str, Any]:
    budgets: dict[str, Any] = {}
    captures: list[float] = []
    regrets: list[float] = []
    oracle_score = split["option_error"].astype(np.float64)
    for budget_index, budget in enumerate(BUDGETS.astype(np.int64)):
        oracle_eps, oracle_values = oracle_gap.episode_values(split, oracle_score, mask.astype(bool), int(budget))
        score_eps, score_values = oracle_gap.episode_values(split, scores[int(budget)], mask.astype(bool), int(budget))
        if oracle_eps != score_eps:
            raise ValueError(f"episode mismatch for budget {budget}")
        regret = score_values - oracle_values
        oracle_mean = float(np.mean(oracle_values))
        score_mean = float(np.mean(score_values))
        capture = score_mean / oracle_mean if oracle_mean < 0.0 else 0.0
        captures.append(float(capture))
        regrets.append(float(np.mean(regret)))
        budgets[f"budget_{int(budget)}"] = {
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
            "mean_regret_to_oracle": clean_float(float(np.mean(regrets))),
            "budget2_capture_ratio": clean_float(float(captures[0])),
            "budget3_capture_ratio": clean_float(float(captures[1])),
            "budget4_capture_ratio": clean_float(float(captures[2])),
        },
    }


def weighted_train_model(
    train_x: np.ndarray,
    train_target: np.ndarray,
    train_weight: np.ndarray,
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
) -> tuple[budget_value.BudgetConditionedNet, dict[str, Any]]:
    model = budget_value.BudgetConditionedNet(train_x.shape[1], hidden, depth).to(device)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=1.0e-4)
    x_t = torch.from_numpy(train_x.astype(np.float32)).to(device)
    y_t = torch.from_numpy(train_target.astype(np.float32)).to(device)
    w_t = torch.from_numpy(train_weight.astype(np.float32)).to(device)
    order_base = np.arange(len(train_x))
    rng = np.random.default_rng(seed + 901)
    best_state = None
    best_key = (float("inf"), float("inf"), float("inf"))
    best: dict[str, Any] = {}
    history: list[dict[str, float]] = []
    n_cal = len(cal_split["episode"])
    cal_labels = base_learner.forced_delta_targets(cal_split, depths, budgets)
    cal_mask = np.ones(n_cal, dtype=bool)
    for epoch in range(epochs):
        model.train()
        order = rng.permutation(order_base)
        losses: list[float] = []
        for start in range(0, len(order), batch):
            idx = torch.as_tensor(order[start : start + batch], dtype=torch.long, device=device)
            pred = model(x_t[idx])
            per_row = F.smooth_l1_loss(pred, y_t[idx], reduction="none")
            loss = torch.mean(per_row * w_t[idx])
            opt.zero_grad(set_to_none=True)
            loss.backward()
            torch.nn.utils.clip_grad_norm_(model.parameters(), 5.0)
            opt.step()
            losses.append(float(loss.detach().cpu()))
        cal_flat = budget_value.predict(model, cal_x, device, batch) * y_scale + y_mean
        cal_scores = budget_value.reshape_budget_scores(cal_flat, n_cal, depths, budgets)
        cal_rho = mean_label_rho_from_labels(cal_labels, cal_scores)
        mean_capture, mean_regret = observed_capture(cal_split, cal_scores, cal_mask)
        train_loss = float(np.mean(losses))
        key = (-mean_capture, -cal_rho, mean_regret, train_loss)
        history.append(
            {
                "epoch": clean_float(float(epoch + 1)),
                "train_loss": clean_float(train_loss),
                "cal_mean_capture_ratio": clean_float(mean_capture),
                "cal_mean_label_rho": clean_float(cal_rho),
                "cal_mean_regret_to_oracle": clean_float(mean_regret),
            }
        )
        if key < best_key:
            best_key = key
            best = {"epoch": int(epoch + 1), "selection_key": [clean_float(v) for v in key], **history[-1]}
            best_state = {name: value.detach().cpu().clone() for name, value in model.state_dict().items()}
    if best_state is not None:
        model.load_state_dict(best_state)
    return model, {
        "selection_rule": "maximize calibration exact-budget oracle-headroom capture, then calibration forced-delta label Spearman, then minimize regret and weighted training loss",
        "best": best,
        "history_first": history[0] if history else {},
        "history_last": history[-1] if history else {},
        "params_count": int(sum(p.numel() for p in model.parameters())),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    d = report["diagnosis"]
    lines = [
        "# State-Generation Mechanism Target Learner",
        "",
        f"- device: `{report['device']}`",
        f"- selected tail weight: `{d['selected_tail_weight']}`",
        f"- hard mean capture: `{d['hard_mean_capture_ratio']:.6g}`",
        f"- base hard mean capture: `{d['base_hard_mean_capture_ratio']:.6g}`",
        f"- target hard mean capture: `{d['target_hard_mean_capture_ratio']:.6g}`",
        "",
        "| row | mean capture | budget-2 | budget-3 | budget-4 | label rho |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for name in ["mechanism_target_learner", "base_perturbation_value_learner", "mechanism_target_ceiling"]:
        row = report["hard_rows"][name]
        s = row["capture"]["summary"]
        rho = row["label_alignment"]["mean_score_label_spearman"]
        lines.append(
            f"| `{name}` | {s['mean_capture_ratio']:.6g} | {s['budget2_capture_ratio']:.6g} | "
            f"{s['budget3_capture_ratio']:.6g} | {s['budget4_capture_ratio']:.6g} | {rho:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Train a non-leaky learner for the mechanism-aware forced-delta assignment target")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--latents", default=str(env_desc.DEFAULT_LATENTS))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--base-learner-pred", default=str(BASE_LEARNER_PRED))
    parser.add_argument("--target-audit-pred", default=str(TARGET_AUDIT_PRED))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--seed", type=int, default=2291)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--hidden", type=int, default=128)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=2048)
    parser.add_argument("--lr", type=float, default=5.0e-4)
    parser.add_argument("--bootstrap-samples", type=int, default=300)
    args = parser.parse_args()

    start_time = time.time()
    device = budget_value.configure(int(args.seed))
    data = load_npz(Path(args.export))
    latents = load_npz(Path(args.latents))
    hard_episodes = env_desc.read_hard_episodes(Path(args.hard_diagnostic))
    train = episode_alloc.load_split(data, "train")
    cal = episode_alloc.load_split(data, "calibration")
    eval_split = episode_alloc.load_split(data, "eval")
    depths = data["option_depths"].astype(np.int64)
    features, feature_dims = base_learner.geometry_alloc.augment_features(data, latents)
    train_x, feature_dims = base_learner.option_features(features, feature_dims, data, "train", depths)
    cal_x, _ = base_learner.option_features(features, feature_dims, data, "calibration", depths)
    eval_x, _ = base_learner.option_features(features, feature_dims, data, "eval", depths)
    train_targets = base_learner.forced_delta_targets(train, depths, BUDGETS)
    train_flat = flatten_targets(train_targets, BUDGETS)
    y_mean = float(np.mean(train_flat))
    y_scale = float(np.std(train_flat))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    train_y = ((train_flat - y_mean) / y_scale).astype(np.float32)
    train_budget_x = base_learner.expand_with_budgets(train_x, len(train["episode"]), depths, BUDGETS)
    cal_budget_x = base_learner.expand_with_budgets(cal_x, len(cal["episode"]), depths, BUDGETS)
    eval_budget_x = base_learner.expand_with_budgets(eval_x, len(eval_split["episode"]), depths, BUDGETS)

    candidates: list[dict[str, Any]] = []
    best_model = None
    best_key = (float("inf"), float("inf"), float("inf"))
    for index, tail_weight in enumerate((0.0, 1.0, 2.0, 4.0)):
        weights = tail_weights(train_targets, BUDGETS, tail_weight)
        model, training = weighted_train_model(
            train_budget_x,
            train_y,
            weights,
            cal_budget_x,
            cal,
            depths,
            BUDGETS,
            y_mean,
            y_scale,
            device=device,
            seed=int(args.seed) + 101 * index,
            hidden=int(args.hidden),
            depth=int(args.depth),
            epochs=int(args.epochs),
            batch=int(args.batch),
            lr=float(args.lr),
        )
        key = tuple(float(v) for v in training["best"]["selection_key"][:3])
        candidates.append({"tail_weight": clean_float(tail_weight), "training": training})
        if key < best_key:
            best_key = key
            best_model = model
    if best_model is None:
        raise RuntimeError("no candidate model trained")

    selected = min(candidates, key=lambda row: tuple(float(v) for v in row["training"]["best"]["selection_key"][:3]))
    eval_flat = budget_value.predict(best_model, eval_budget_x, device, int(args.batch)) * y_scale + y_mean
    eval_scores = budget_value.reshape_budget_scores(eval_flat, len(eval_split["episode"]), depths, BUDGETS)
    base_npz = load_npz(Path(args.base_learner_pred))
    target_npz = load_npz(Path(args.target_audit_pred))
    base_scores = {int(budget): base_npz[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    target_scores = {int(budget): target_npz[f"budget_{int(budget)}_score"].astype(np.float64) for budget in BUDGETS}
    hard_mask = np.isin(eval_split["episode"].astype(np.int64), np.asarray(hard_episodes, dtype=np.int64))
    hard_rows: dict[str, Any] = {}
    for index, (name, scores) in enumerate(
        {
            "mechanism_target_learner": eval_scores,
            "base_perturbation_value_learner": base_scores,
            "mechanism_target_ceiling": target_scores,
        }.items()
    ):
        hard_rows[name] = {
            "capture": capture_summary(eval_split, scores, hard_mask, seed=int(args.seed) + 3000 + 1000 * index, samples=int(args.bootstrap_samples)),
            "label_alignment": base_learner.hard_label_alignment(eval_split, depths, BUDGETS, hard_episodes, scores),
        }

    learner_summary = hard_rows["mechanism_target_learner"]["capture"]["summary"]
    base_summary = hard_rows["base_perturbation_value_learner"]["capture"]["summary"]
    target_summary = hard_rows["mechanism_target_ceiling"]["capture"]["summary"]
    learner_rho = float(hard_rows["mechanism_target_learner"]["label_alignment"]["mean_score_label_spearman"])
    base_rho = float(hard_rows["base_perturbation_value_learner"]["label_alignment"]["mean_score_label_spearman"])
    capture_gain = float(learner_summary["mean_capture_ratio"]) - float(base_summary["mean_capture_ratio"])
    rho_gain = learner_rho - base_rho
    closes = bool(float(learner_summary["mean_capture_ratio"]) > 0.0 and float(learner_summary["min_capture_ratio"]) > 0.0)
    verdict = (
        "A non-leaky mechanism-target learner closes the held-out hard exact-budget gate on this export; independent export validation is required."
        if closes
        else "The non-leaky mechanism-target learner improves the mechanism route but does not close the held-out hard exact-budget gate."
        if capture_gain > 0.0 or rho_gain > 0.0
        else "The non-leaky mechanism-target learner does not improve over the perturbation-value learner on the held-out hard exact-budget gate."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_mechanism_target_learner",
        "device": str(device),
        "config": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
            "bootstrap_samples": int(args.bootstrap_samples),
        },
        "feature_dims": feature_dims,
        "target_stats": {"mean": clean_float(y_mean), "scale": clean_float(y_scale)},
        "candidate_training": candidates,
        "hard_rows": hard_rows,
        "diagnosis": {
            "mechanism_target_learner_closes": closes,
            "selected_tail_weight": selected["tail_weight"],
            "hard_mean_capture_ratio": learner_summary["mean_capture_ratio"],
            "base_hard_mean_capture_ratio": base_summary["mean_capture_ratio"],
            "target_hard_mean_capture_ratio": target_summary["mean_capture_ratio"],
            "hard_min_capture_ratio": learner_summary["min_capture_ratio"],
            "hard_capture_gain_over_base": clean_float(capture_gain),
            "hard_mean_score_label_spearman": clean_float(learner_rho),
            "base_mean_score_label_spearman": clean_float(base_rho),
            "label_rho_gain_over_base": clean_float(rho_gain),
        },
        "verdict": verdict,
        "leakage_attestation": {
            "train_label_scope": "train option_error constructs forced-delta mechanism labels for supervised training",
            "selection_scope": "calibration option_error constructs forced-delta labels and exact-budget capture only for model selection",
            "eval_scope": "eval option_error is used only for held-out hard capture and label-alignment measurement",
            "feature_scope": "model inputs are latent, environment, rollout-internal, option-depth, and budget features; eval option_error is not a feature",
            "slurm_or_ssh": "not used",
        },
        "not_claimed": ["independent export validation", "complete BEDC-native world model", "A100 training result"],
        "wall_time_sec": clean_float(time.time() - start_time),
    }
    np.savez_compressed(
        Path(args.out),
        **{f"budget_{int(budget)}_score": eval_scores[int(budget)].astype(np.float32) for budget in BUDGETS},
    )
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

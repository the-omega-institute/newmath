from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch

import _compute_value_model as cvm
import _compute_value_refined_option_model as refined
import _compute_value_structured_assignment as structured
import _g2n_integrated_a100 as g2n


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_feature_group_ablation.json"
DEFAULT_MD = REPORT_DIR / "compute_value_feature_group_ablation.md"
DEFAULT_OUT = REPORT_DIR / "compute_value_feature_group_ablation_predictions.npz"
DEPTHS = structured.DEPTHS


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


def feature_slices(latents: dict[str, np.ndarray]) -> dict[str, slice]:
    z_dim = int(latents["emb"].shape[-1])
    a_dim = int(latents["action"].shape[-1])
    cursor = 0
    spans: dict[str, slice] = {}

    def add(name: str, width: int) -> None:
        nonlocal cursor
        spans[name] = slice(cursor, cursor + int(width))
        cursor += int(width)

    add("latent_window_z_t_minus_4_to_t", (g2n.WINDOW_BACK + 1) * z_dim)
    add("future_action_sequence_t_to_t_plus_9", g2n.MAX_ACTION_H * a_dim)
    add("future_action_validity", g2n.MAX_ACTION_H)
    add("time_features", 2)
    add("lewm_pred_z_rollout", g2n.MAX_ACTION_H * z_dim)
    add("rollout_delta_z", g2n.MAX_ACTION_H * z_dim)
    add("rollout_delta_norm", g2n.MAX_ACTION_H)
    add("rollout_spread_norm", g2n.MAX_ACTION_H)
    add("past_one_step_gap_proxy_pred_vs_emb", g2n.MAX_ACTION_H)
    add("rollout_validity", g2n.MAX_ACTION_H)
    return spans


def select_columns(x: np.ndarray, spans: dict[str, slice], names: list[str]) -> np.ndarray:
    return np.concatenate([x[:, spans[name]] for name in names], axis=1).astype(np.float32)


def build_feature_sets(x: np.ndarray, spans: dict[str, slice]) -> dict[str, np.ndarray]:
    return {
        "full": x.astype(np.float32),
        "base_latent_action": select_columns(
            x,
            spans,
            [
                "latent_window_z_t_minus_4_to_t",
                "future_action_sequence_t_to_t_plus_9",
                "future_action_validity",
                "time_features",
            ],
        ),
        "rollout_trajectory": select_columns(
            x,
            spans,
            [
                "lewm_pred_z_rollout",
                "rollout_delta_z",
                "rollout_validity",
            ],
        ),
        "rollout_norm_gap": select_columns(
            x,
            spans,
            [
                "rollout_delta_norm",
                "rollout_spread_norm",
                "past_one_step_gap_proxy_pred_vs_emb",
                "rollout_validity",
            ],
        ),
        "base_plus_norm_gap": select_columns(
            x,
            spans,
            [
                "latent_window_z_t_minus_4_to_t",
                "future_action_sequence_t_to_t_plus_9",
                "future_action_validity",
                "time_features",
                "rollout_delta_norm",
                "rollout_spread_norm",
                "past_one_step_gap_proxy_pred_vs_emb",
                "rollout_validity",
            ],
        ),
        "base_plus_trajectory": select_columns(
            x,
            spans,
            [
                "latent_window_z_t_minus_4_to_t",
                "future_action_sequence_t_to_t_plus_9",
                "future_action_validity",
                "time_features",
                "lewm_pred_z_rollout",
                "rollout_delta_z",
                "rollout_validity",
            ],
        ),
    }


def train_row(
    train: dict[str, np.ndarray],
    cal: dict[str, np.ndarray],
    eval_payload: dict[str, np.ndarray],
    train_x: np.ndarray,
    cal_x: np.ndarray,
    eval_x: np.ndarray,
    *,
    device: torch.device,
    seed: int,
    epochs: int,
    hidden: int,
    batch: int,
    lr: float,
) -> tuple[dict[str, Any], np.ndarray, np.ndarray]:
    x_mean, x_scale = structured.fit_standardizer(train_x)
    x_train = structured.standardize(train_x, x_mean, x_scale)
    x_cal = structured.standardize(cal_x, x_mean, x_scale)
    x_eval = structured.standardize(eval_x, x_mean, x_scale)
    ex_train = structured.expand_options(x_train, DEPTHS)
    ex_cal = structured.expand_options(x_cal, DEPTHS)
    ex_eval = structured.expand_options(x_eval, DEPTHS)
    y_mean = float(np.mean(train["option_error"].reshape(-1)))
    y_scale = float(np.std(train["option_error"].reshape(-1)))
    if y_scale < 1.0e-6:
        y_scale = 1.0
    y_train = ((train["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    y_cal = ((cal["option_error"].reshape(-1) - y_mean) / y_scale).astype(np.float32)
    model, health = structured.train_mlp(
        ex_train,
        y_train,
        train["option_error"],
        ex_cal,
        y_cal,
        cal,
        device=device,
        seed=seed,
        hidden=hidden,
        epochs=epochs,
        batch=batch,
        lr=lr,
    )
    cal_score = structured.reshape_scores(structured.predict_mlp(model, ex_cal, device, batch) * y_scale + y_mean, len(cal["episode"]))
    eval_score = structured.reshape_scores(
        structured.predict_mlp(model, ex_eval, device, batch) * y_scale + y_mean,
        len(eval_payload["episode"]),
    )
    choice = structured.exact_budget_choice(eval_payload["episode"], eval_score, DEPTHS)
    row = {
        "health": health,
        "calibration": structured.evaluate_scores(cal, cal_score, seed=seed + 3101),
        "eval": structured.evaluate_scores(eval_payload, eval_score, seed=seed + 3201),
    }
    return row, eval_score, choice


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Feature Group Ablation",
        "",
        f"- device: `{report['device']}`",
        f"- seed: `{report['grid']['seed']}`",
        f"- epochs: `{report['grid']['epochs']}`",
        "",
        "| row | eval allocation delta | score/error rho |",
        "|---|---:|---:|",
    ]
    for name in report["row_order"]:
        row = report["rows"][name]["eval"]
        d = row["allocation_delta"]
        lines.append(f"| `{name}` | {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] | {row['score_error_spearman']:.9g} |")
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Ablate rollout/internal feature groups for structured compute-value assignment")
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
    torch.backends.cudnn.benchmark = False
    torch.backends.cudnn.deterministic = True
    labels_path = cvm.resolve_path(str(args.labels), [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])
    latents_path = cvm.resolve_path(str(args.latents), [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])
    labels = cvm.load_npz(labels_path)
    latents = cvm.load_npz(latents_path)
    train = refined.split_payload(labels, latents, "train")
    cal = refined.split_payload(labels, latents, "calibration")
    eval_payload = refined.split_payload(labels, latents, "eval")
    spans = feature_slices(latents)
    train_sets = build_feature_sets(train["x"], spans)
    cal_sets = build_feature_sets(cal["x"], spans)
    eval_sets = build_feature_sets(eval_payload["x"], spans)
    row_order = [
        "full",
        "base_latent_action",
        "rollout_trajectory",
        "rollout_norm_gap",
        "base_plus_norm_gap",
        "base_plus_trajectory",
    ]
    rows: dict[str, Any] = {}
    scores: dict[str, np.ndarray] = {}
    choices: dict[str, np.ndarray] = {}
    for offset, name in enumerate(row_order):
        row, score, choice = train_row(
            train,
            cal,
            eval_payload,
            train_sets[name],
            cal_sets[name],
            eval_sets[name],
            device=device,
            seed=int(args.seed) + offset,
            epochs=int(args.epochs),
            hidden=int(args.hidden),
            batch=int(args.batch),
            lr=float(args.lr),
        )
        rows[name] = row
        scores[name] = score
        choices[name] = choice

    selected = min(
        row_order,
        key=lambda name: (
            float(rows[name]["calibration"]["allocation_delta"]["high"]),
            float(rows[name]["calibration"]["allocation_delta"]["observed"]),
            name,
        ),
    )
    structured.write_npz(Path(args.out), eval_payload, scores[selected], choices[selected], f"feature_group_{selected}")
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_feature_group_ablation",
        "device": str(device),
        "inputs": {"labels": str(labels_path), "latents": str(latents_path)},
        "grid": {
            "seed": int(args.seed),
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "batch": int(args.batch),
            "lr": float(args.lr),
        },
        "counts": {
            "train": int(len(train["episode"])),
            "calibration": int(len(cal["episode"])),
            "eval": int(len(eval_payload["episode"])),
            "eval_episodes": int(len(np.unique(eval_payload["episode"]))),
        },
        "feature_spans": {name: [int(span.start), int(span.stop)] for name, span in spans.items()},
        "row_order": row_order,
        "selected_row": selected,
        "rows": rows,
        "leakage_attestation": {
            "feature_standardizer": "fit on train features only per row",
            "target_standardizer": "fit on train option_error only",
            "model_selection": "per-row checkpoint selection uses calibration split exact-budget allocation only; selected_row uses calibration only",
            "eval_truth_usage": "eval option_error used only after predicted option scores are produced",
            "slurm_or_ssh": "not used",
        },
        "outputs": {"predictions_npz": str(args.out), "json": str(args.json), "md": str(args.md)},
        "wall_time_sec": clean_float(time.time() - start),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json({"device": str(device), "selected_row": selected, "rows": {k: v["eval"] for k, v in rows.items()}}), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_model as cvm
import _g2n_integrated_a100 as g2n


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "aligned_state_generation_export.json"
DEFAULT_MD = REPORT_DIR / "aligned_state_generation_export.md"
DEFAULT_OUT = REPORT_DIR / "aligned_state_generation_export.npz"
OPTION_DEPTHS = np.asarray([1, 2, 3, 4, 5], dtype=np.int64)
UNIFORM_DEPTH = 3


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


def horizon_indices(labels: dict[str, np.ndarray], depths: np.ndarray) -> list[int]:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    return [horizons.index(int(depth)) for depth in depths]


def build_split(labels: dict[str, np.ndarray], latents: dict[str, np.ndarray], split: str) -> dict[str, np.ndarray]:
    indices = horizon_indices(labels, OPTION_DEPTHS)
    valid = labels[f"{split}_valid"][:, indices].all(axis=1)
    rows = g2n.build_features(latents, labels, split, use_rollout=True)
    anchors = rows["anchor_ep_t0"][valid].astype(np.int64)
    err_at_h = labels[f"{split}_err_at_h"][valid].astype(np.float64)
    pred_z_valid = labels[f"{split}_valid"][valid].astype(bool)
    pred_z = labels[f"{split}_pred_z"][valid].astype(np.float32)
    pred_z = np.where(pred_z_valid[:, :, None], pred_z, 0.0).astype(np.float32)
    option_error = np.zeros((len(anchors), len(OPTION_DEPTHS)), dtype=np.float64)
    for col, depth in enumerate(OPTION_DEPTHS):
        option_error[:, col] = np.sum(err_at_h[:, : int(depth)], axis=1)
    uniform_col = int(np.where(OPTION_DEPTHS == UNIFORM_DEPTH)[0][0])
    uniform_error = option_error[:, uniform_col].copy()
    true_mv = uniform_error[:, None] / float(UNIFORM_DEPTH) - option_error / OPTION_DEPTHS[None, :]
    next_target = np.zeros((len(anchors), latents["emb"].shape[-1]), dtype=np.float32)
    lewm_h1_mse = np.zeros(len(anchors), dtype=np.float64)
    for i, (ep_raw, t_raw) in enumerate(anchors):
        ep = int(ep_raw)
        t = int(t_raw)
        next_target[i] = latents["emb"][ep, t + 1]
        lewm_h1_mse[i] = float(latents["prediction_mse"][ep, t])
    return {
        "x": rows["x"][valid].astype(np.float32),
        "current_z": rows["current_z"][valid].astype(np.float32),
        "next_target": next_target,
        "pred_z": pred_z,
        "pred_z_valid": pred_z_valid.astype(np.float32),
        "lewm_h1_mse": lewm_h1_mse,
        "episode": anchors[:, 0].astype(np.int64),
        "t0": anchors[:, 1].astype(np.int64),
        "anchor_ep_t0": anchors,
        "option_error": option_error.astype(np.float64),
        "uniform_error": uniform_error.astype(np.float64),
        "true_mv": true_mv.astype(np.float64),
        "horizon_y": labels[f"{split}_y"][valid].astype(np.int8),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Aligned State-Generation Export",
        "",
        f"- schema: `{report['schema_id']}`",
        f"- option depths: `{report['option_depths']}`",
        "",
        "| split | anchors | episodes | feature dim |",
        "|---|---:|---:|---:|",
    ]
    for split in ["train", "calibration", "eval"]:
        row = report["counts"][split]
        lines.append(f"| {split} | {row['anchors']} | {row['episodes']} | {row['feature_dim']} |")
    lines.extend(
        [
            "",
            "The export aligns prediction targets, compute-value option labels, horizon labels, rollout features, and BEDC ledger variables on identical anchors.",
        ]
    )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Build an aligned export for BEDC-native state-generation training")
    parser.add_argument("--labels", default=str(cvm.DEFAULT_LABELS))
    parser.add_argument("--latents", default=str(cvm.DEFAULT_LATENTS))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    args = parser.parse_args()
    labels = cvm.load_npz(cvm.resolve_path(args.labels, [cvm.DEFAULT_LABELS, cvm.ALT_LABELS]))
    latents = cvm.load_npz(cvm.resolve_path(args.latents, [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS]))
    splits = {name: build_split(labels, latents, name) for name in ["train", "calibration", "eval"]}
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.aligned_state_generation_export",
        "source": {
            "labels": str(cvm.resolve_path(args.labels, [cvm.DEFAULT_LABELS, cvm.ALT_LABELS])),
            "latents": str(cvm.resolve_path(args.latents, [cvm.DEFAULT_LATENTS, cvm.ALT_LATENTS])),
        },
        "option_depths": OPTION_DEPTHS.tolist(),
        "uniform_depth": UNIFORM_DEPTH,
        "counts": {
            split: {
                "anchors": int(len(payload["episode"])),
                "episodes": int(len(np.unique(payload["episode"]))),
                "feature_dim": int(payload["x"].shape[1]),
            }
            for split, payload in splits.items()
        },
        "fields": [
            "x",
            "current_z",
            "next_target",
            "pred_z",
            "pred_z_valid",
            "lewm_h1_mse",
            "option_error",
            "uniform_error",
            "true_mv",
            "horizon_y",
            "anchor_ep_t0",
        ],
        "leakage_attestation": {
            "features": "x uses current/past latent-action context and predicted rollout-internal features from the carrier.",
            "labels": "next_target, option_error, true_mv, and horizon_y are stored as supervised targets and must not be fed as input features.",
            "split": "train, calibration, and eval are exported separately from the existing label split.",
        },
    }
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    arrays: dict[str, np.ndarray] = {
        "option_depths": OPTION_DEPTHS.astype(np.int64),
    }
    for split, payload in splits.items():
        for key, value in payload.items():
            arrays[f"{split}_{key}"] = value
    np.savez_compressed(out_path, **arrays)
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

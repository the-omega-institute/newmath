#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "aligned_state_generation_export.json"
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
HYPOTHESIS_ID = "fi-046.aligned-state-generation-export"
REQUIRED_FIELDS = [
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
]


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "aligned_export_ready",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["aligned_state_generation_export", "world_model_gate"],
        "reported_claim": f"aligned state-generation export fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate aligned BEDC-native state-generation export")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    export_path = Path(args.export)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    elif not export_path.exists():
        payload = fail_closed(f"missing export at {export_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        export = np.load(export_path, allow_pickle=False)
        missing: list[str] = []
        bad_shapes: list[str] = []
        for split in ["train", "calibration", "eval"]:
            n = int(report["counts"][split]["anchors"])
            for field in REQUIRED_FIELDS:
                key = f"{split}_{field}"
                if key not in export.files:
                    missing.append(key)
                    continue
                if int(export[key].shape[0]) != n:
                    bad_shapes.append(f"{key}:{export[key].shape[0]}!={n}")
        counts = report["counts"]
        thresholds = {
            "train_anchors": 1000,
            "train_episodes": 100,
            "eval_anchors": 500,
            "eval_episodes": 40,
        }
        count_ok = (
            int(counts["train"]["anchors"]) >= thresholds["train_anchors"]
            and int(counts["train"]["episodes"]) >= thresholds["train_episodes"]
            and int(counts["eval"]["anchors"]) >= thresholds["eval_anchors"]
            and int(counts["eval"]["episodes"]) >= thresholds["eval_episodes"]
        )
        finite_ok = True
        for split in ["train", "calibration", "eval"]:
            for field in ["x", "current_z", "next_target", "pred_z", "lewm_h1_mse", "option_error", "true_mv"]:
                key = f"{split}_{field}"
                if key in export.files and not bool(np.isfinite(export[key]).all()):
                    finite_ok = False
                    bad_shapes.append(f"{key}:nonfinite")
        ready = 1.0 if not missing and not bad_shapes and count_ok and finite_ok else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": ready},
            "metric": "aligned_export_ready",
            "metric_value": ready,
            "ci": {"low": ready, "high": ready},
            "status": "positive" if ready > 0.0 else "fail-closed",
            "measured_scope": [
                "aligned_state_generation_export",
                "prediction_target",
                "compute_value_labels",
                "horizon_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "aligned state-generation export validation: "
                f"train={counts['train']['anchors']} anchors/{counts['train']['episodes']} episodes, "
                f"eval={counts['eval']['anchors']} anchors/{counts['eval']['episodes']} episodes, "
                f"feature_dim={counts['train']['feature_dim']}, ready={ready:.0f}. "
                "The export is a training substrate, not a trained BEDC-native world model."
            ),
            "diagnostics": {
                "counts": counts,
                "thresholds": thresholds,
                "missing": missing,
                "bad_shapes": bad_shapes,
                "not_claimed": [
                    "trained state-generation model",
                    "prediction parity",
                    "universal control",
                ],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

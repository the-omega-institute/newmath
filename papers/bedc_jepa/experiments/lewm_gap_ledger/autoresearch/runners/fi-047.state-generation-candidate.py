#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_candidate.json"
DEFAULT_PREDICTIONS = REPORT_DIR / "state_generation_candidate_predictions.npz"
HYPOTHESIS_ID = "fi-047.state-generation-candidate"
REQUIRED_EVAL_METRICS = [
    "native_h1_mse",
    "lewm_h1_mse",
    "prediction_parity_margin",
    "allocation_delta",
    "score_error_spearman",
    "mean_horizon_auroc",
    "valid_horizon_auc_count",
]
REQUIRED_PREDICTION_FIELDS = [
    "episode",
    "anchor_ep_t0",
    "pred_next_z",
    "target_next_z",
    "lewm_h1_mse",
    "native_h1_mse",
    "predicted_option_error",
    "option_error",
    "horizon_logits",
    "horizon_y",
]


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "state_generation_candidate_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["state_generation_candidate", "world_model_gate"],
        "reported_claim": f"state-generation candidate validation fail-closed: {reason}",
    }


def interval(report: dict[str, Any], metric: str) -> dict[str, float]:
    row = report["eval"][metric]
    return {
        "observed": float(row["observed"]),
        "low": float(row["low"]),
        "high": float(row["high"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate the first aligned BEDC-native state-generation candidate")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--predictions", default=str(DEFAULT_PREDICTIONS))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    prediction_path = Path(args.predictions)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    elif not prediction_path.exists():
        payload = fail_closed(f"missing prediction archive at {prediction_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        missing_metrics = [name for name in REQUIRED_EVAL_METRICS if name not in report.get("eval", {})]
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_candidate"
        status_ok = str(report.get("status") or "") == "ok"
        counts = report.get("counts") if isinstance(report.get("counts"), dict) else {}
        count_ok = (
            int(counts.get("train", 0)) >= 1000
            and int(counts.get("calibration", 0)) >= 500
            and int(counts.get("eval", 0)) >= 500
            and int(counts.get("eval_episodes", 0)) >= 40
        )
        finite_metrics = True
        finite_failures: list[str] = []
        for name in REQUIRED_EVAL_METRICS:
            if name in missing_metrics:
                continue
            value = report["eval"][name]
            if isinstance(value, dict):
                for key in ["observed", "low", "high"]:
                    if key not in value or not np.isfinite(float(value[key])):
                        finite_metrics = False
                        finite_failures.append(f"{name}.{key}")
            elif not np.isfinite(float(value)):
                finite_metrics = False
                finite_failures.append(name)
        with np.load(prediction_path, allow_pickle=False) as archive:
            missing_fields = [field for field in REQUIRED_PREDICTION_FIELDS if field not in archive.files]
            bad_shapes: list[str] = []
            finite_arrays = True
            eval_count = int(counts.get("eval", 0))
            for field in REQUIRED_PREDICTION_FIELDS:
                if field in missing_fields:
                    continue
                arr = archive[field]
                if int(arr.shape[0]) != eval_count:
                    bad_shapes.append(f"{field}:{arr.shape[0]}!={eval_count}")
                if not bool(np.isfinite(arr).all()):
                    finite_arrays = False
                    bad_shapes.append(f"{field}:nonfinite")
            pred_shape_ok = (
                "pred_next_z" not in missing_fields
                and "target_next_z" not in missing_fields
                and archive["pred_next_z"].shape == archive["target_next_z"].shape
            )
            if not pred_shape_ok:
                bad_shapes.append("pred_next_z/target_next_z shape mismatch")
        valid = (
            schema_ok
            and status_ok
            and count_ok
            and not missing_metrics
            and finite_metrics
            and not missing_fields
            and not bad_shapes
            and finite_arrays
        )
        score = 1.0 if valid else 0.0
        parity = interval(report, "prediction_parity_margin") if "prediction_parity_margin" not in missing_metrics else {"observed": 0.0, "low": 0.0, "high": 0.0}
        allocation = interval(report, "allocation_delta") if "allocation_delta" not in missing_metrics else {"observed": 0.0, "low": 0.0, "high": 0.0}
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": score},
            "metric": "state_generation_candidate_valid",
            "metric_value": score,
            "ci": {"low": score, "high": score},
            "status": "positive" if score > 0.0 else "fail-closed",
            "measured_scope": [
                "state_generation_candidate",
                "prediction_parity_boundary",
                "compute_value_labels",
                "horizon_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "state-generation candidate validation: the aligned candidate trains on the shared export "
                f"with eval={counts.get('eval')} anchors/{counts.get('eval_episodes')} episodes, "
                f"native h1 MSE={interval(report, 'native_h1_mse')['observed']:.6g}, "
                f"LeWM h1 MSE={interval(report, 'lewm_h1_mse')['observed']:.6g}, "
                f"parity margin={parity['observed']:.6g}, "
                f"allocation delta={allocation['observed']:.6g}, "
                f"mean horizon AUROC={float(report['eval'].get('mean_horizon_auroc', 0.0)):.6g}. "
                "This validates a measured candidate and preserves the boundary that prediction parity, "
                "allocation closure, and a complete BEDC-native world model are not claimed."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "count_ok": count_ok,
                "missing_metrics": missing_metrics,
                "finite_failures": finite_failures,
                "missing_prediction_fields": missing_fields,
                "bad_shapes": bad_shapes,
                "metrics": report.get("eval", {}),
                "not_claimed": report.get("not_claimed", []),
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_calibration_transform.json"
HYPOTHESIS_ID = "fi-066.state-generation-episode-calibration-transform"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_calibration_transform_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_calibration_transform", "world_model_gate"],
        "reported_claim": f"episode calibration transform validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode calibration transform diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_calibration_transform"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        cal = rows.get("calibrated", {}) if isinstance(rows.get("calibrated"), dict) else {}
        raw = rows.get("base_geometry_option", {}) if isinstance(rows.get("base_geometry_option"), dict) else {}
        cal_hard = cal.get("hard_only", {}).get("allocation_delta", {}) if isinstance(cal.get("hard_only"), dict) else {}
        raw_hard = raw.get("hard_only", {}).get("allocation_delta", {}) if isinstance(raw.get("hard_only"), dict) else {}
        hard_improves = bool(diagnosis.get("hard_beats_raw_geometry_option_observed", False))
        hard_closes = bool(diagnosis.get("hard_closes", False))
        movement_valid = schema_ok and status_ok and hard_improves and not hard_closes
        metric = 1.0 if movement_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_calibration_transform_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_calibration_transform",
                "geometry_option_conditioned_allocation",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Episode calibration transform is evaluated against raw geometry-option scores: "
                f"calibrated hard-only observed delta={float(cal_hard.get('observed', 0.0)):.6g}, "
                f"raw hard-only observed delta={float(raw_hard.get('observed', 0.0)):.6g}, "
                f"calibrated hard-only CI high={float(cal_hard.get('high', 0.0)):.6g}. "
                "Allocation closure is claimed only if the hard-only CI high is below zero."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "movement_valid": movement_valid,
                "hard_improves": hard_improves,
                "hard_closes": hard_closes,
                "calibrated_hard_observed": float(cal_hard.get("observed", 0.0)),
                "calibrated_hard_high": float(cal_hard.get("high", 0.0)),
                "raw_hard_observed": float(raw_hard.get("observed", 0.0)),
                "raw_hard_high": float(raw_hard.get("high", 0.0)),
                "not_claimed": ["independent export validation", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

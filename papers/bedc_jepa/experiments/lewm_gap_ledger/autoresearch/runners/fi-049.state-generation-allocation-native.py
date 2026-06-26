#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_allocation_native.json"
HYPOTHESIS_ID = "fi-049.state-generation-allocation-native"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "allocation_native_boundary_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_native_boundary", "world_model_gate"],
        "reported_claim": f"allocation-native boundary validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate allocation-native state-generation boundary")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_allocation_native"
        status_ok = str(report.get("status") or "") == "ok"
        eval_rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        native = eval_rows.get("allocation_native", {})
        calibrated = eval_rows.get("calibrated_allocation_native", {})
        raw = eval_rows.get("raw_state_generation_candidate", {})
        oracle = eval_rows.get("oracle_true_error", {})
        selection = report.get("selection", {}).get("best", {}).get("calibration", {})
        cal_delta = selection.get("allocation_delta", {})
        native_delta = native.get("allocation_delta", {})
        calibrated_delta = calibrated.get("allocation_delta", {})
        oracle_delta = oracle.get("allocation_delta", {})
        calibration_closed = float(cal_delta.get("high", 1.0)) < 0.0
        eval_not_closed = float(native_delta.get("high", -1.0)) >= 0.0
        calibrated_not_closed = float(calibrated_delta.get("high", -1.0)) >= 0.0
        oracle_closed = float(oracle_delta.get("high", 1.0)) < 0.0
        valid = schema_ok and status_ok and calibration_closed and eval_not_closed and calibrated_not_closed and oracle_closed
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "allocation_native_boundary_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "allocation_native_boundary",
                "state_generation_candidate",
                "compute_value_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "allocation-native state-generation boundary: calibration exact-budget selection closes "
                f"with CI high={float(cal_delta.get('high', 0.0)):.6g}, but held-out eval remains open "
                f"with allocation-native delta={float(native_delta.get('observed', 0.0)):.6g} "
                f"[{float(native_delta.get('low', 0.0)):.6g}, {float(native_delta.get('high', 0.0)):.6g}] "
                f"and calibrated delta={float(calibrated_delta.get('observed', 0.0)):.6g} "
                f"[{float(calibrated_delta.get('low', 0.0)):.6g}, {float(calibrated_delta.get('high', 0.0)):.6g}]. "
                f"The same eval labels retain oracle exact-budget closure at {float(oracle_delta.get('observed', 0.0)):.6g}. "
                "This diagnoses a calibration-to-eval allocation gap, not an allocation-closed policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "calibration_closed": calibration_closed,
                "eval_not_closed": eval_not_closed,
                "calibrated_not_closed": calibrated_not_closed,
                "oracle_closed": oracle_closed,
                "native": native,
                "calibrated": calibrated,
                "raw": raw,
                "oracle": oracle,
                "selection": report.get("selection", {}),
                "score_calibration": report.get("score_calibration", {}),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

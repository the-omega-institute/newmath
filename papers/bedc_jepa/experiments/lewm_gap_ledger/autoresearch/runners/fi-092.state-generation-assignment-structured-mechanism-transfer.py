#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_assignment_structured_mechanism_transfer.json"
HYPOTHESIS_ID = "fi-092.state-generation-assignment-structured-mechanism-transfer"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "assignment_structured_mechanism_transfer_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["assignment_structured_transfer", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"assignment-structured mechanism transfer audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate assignment-structured mechanism transfer audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_assignment_structured_mechanism_transfer"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("assignment_structured_transfer_closes", False))
        selected = str(diagnosis.get("selected_candidate", ""))
        selected_capture = float(diagnosis.get("selected_hard_mean_capture_ratio", 0.0))
        selected_min = float(diagnosis.get("selected_hard_min_capture_ratio", 0.0))
        raw_capture = float(diagnosis.get("raw_hard_mean_capture_ratio", 0.0))
        base_capture = float(diagnosis.get("base_hard_mean_capture_ratio", 0.0))
        target_capture = float(diagnosis.get("target_hard_mean_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "assignment_structured_mechanism_transfer_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "assignment_structured_transfer",
                "mechanism_target_learner",
                "hard_assignment_mechanism_labels",
                "exact_budget_policy",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Assignment-structured transfer: "
                f"selected={selected}, hard_capture={selected_capture:.6g}, hard_min={selected_min:.6g}, "
                f"raw_capture={raw_capture:.6g}, base_capture={base_capture:.6g}, target_capture={target_capture:.6g}. "
                "Target ceiling is reference-only and excluded from selection."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "assignment_structured_transfer_closes": closes,
                "selected_candidate": selected,
                "selected_hard_mean_capture_ratio": selected_capture,
                "selected_hard_min_capture_ratio": selected_min,
                "raw_hard_mean_capture_ratio": raw_capture,
                "base_hard_mean_capture_ratio": base_capture,
                "target_hard_mean_capture_ratio": target_capture,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

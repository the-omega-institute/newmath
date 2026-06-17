#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_structured_assignment_energy.json"
HYPOTHESIS_ID = "fi-098.state-generation-structured-assignment-energy"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "structured_assignment_energy_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["structured_assignment_energy", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"structured assignment-energy audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate structured assignment-energy audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_structured_assignment_energy"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("structured_assignment_energy_closes", False))
        hard_capture = float(diagnosis.get("energy_hard_mean_capture_ratio", 0.0))
        hard_min = float(diagnosis.get("energy_hard_min_capture_ratio", 0.0))
        scalar_capture = float(diagnosis.get("scalar_hard_mean_capture_ratio", 0.0))
        compat_capture = float(diagnosis.get("compatibility_hard_mean_capture_ratio", 0.0))
        target_capture = float(diagnosis.get("target_hard_mean_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "structured_assignment_energy_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "structured_assignment_energy",
                "anchor_depth_compatibility_learner",
                "exact_budget_policy",
                "hard_assignment_mechanism_labels",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Structured assignment-energy learner: "
                f"hard_capture={hard_capture:.6g}, hard_min={hard_min:.6g}, "
                f"scalar_capture={scalar_capture:.6g}, compatibility_capture={compat_capture:.6g}, "
                f"target_capture={target_capture:.6g}. "
                "The gate closes only if hard mean and all-budget capture are positive."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "structured_assignment_energy_closes": closes,
                "energy_hard_mean_capture_ratio": hard_capture,
                "energy_hard_min_capture_ratio": hard_min,
                "scalar_hard_mean_capture_ratio": scalar_capture,
                "compatibility_hard_mean_capture_ratio": compat_capture,
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

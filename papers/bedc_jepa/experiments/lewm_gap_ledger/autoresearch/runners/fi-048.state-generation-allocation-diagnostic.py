#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_allocation_diagnostic.json"
HYPOTHESIS_ID = "fi-048.state-generation-allocation-diagnostic"


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "allocation_diagnostic_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["allocation_diagnostic", "world_model_gate"],
        "reported_claim": f"state-generation allocation diagnostic fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate state-generation allocation diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        variants = report.get("variants") if isinstance(report.get("variants"), dict) else {}
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        required = ["raw_predicted_error", "negated_predicted_error", "oracle_true_error", "row_centered_truth"]
        missing = [name for name in required if name not in variants]
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_allocation_diagnostic"
        status_ok = str(report.get("status") or "") == "ok"
        raw = variants.get("raw_predicted_error", {})
        oracle = variants.get("oracle_true_error", {})
        raw_delta = raw.get("allocation_delta", {}) if isinstance(raw, dict) else {}
        oracle_delta = oracle.get("allocation_delta", {}) if isinstance(oracle, dict) else {}
        raw_has_rank = bool(diagnosis.get("raw_score_has_global_rank_signal") is True)
        raw_not_closed = bool(diagnosis.get("raw_allocation_closed") is False)
        oracle_closed = bool(diagnosis.get("oracle_allocation_closed") is True)
        valid = schema_ok and status_ok and not missing and raw_has_rank and raw_not_closed and oracle_closed
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "allocation_diagnostic_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "allocation_diagnostic",
                "state_generation_candidate",
                "compute_value_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "state-generation allocation diagnostic: raw candidate option scores have global rank signal "
                f"rho={float(raw.get('score_error_spearman', 0.0)):.6g} and pair accuracy={float(raw.get('pair_accuracy', 0.0)):.6g}, "
                f"but raw exact-budget allocation delta={float(raw_delta.get('observed', 0.0)):.6g} "
                f"[{float(raw_delta.get('low', 0.0)):.6g}, {float(raw_delta.get('high', 0.0)):.6g}]. "
                f"The same eval substrate has an oracle exact-budget delta={float(oracle_delta.get('observed', 0.0)):.6g} "
                f"[{float(oracle_delta.get('low', 0.0)):.6g}, {float(oracle_delta.get('high', 0.0)):.6g}], so allocation is possible "
                "on these labels but not closed by the candidate score. This is a boundary diagnostic, not a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "missing": missing,
                "raw": raw,
                "oracle": oracle,
                "diagnosis": diagnosis,
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

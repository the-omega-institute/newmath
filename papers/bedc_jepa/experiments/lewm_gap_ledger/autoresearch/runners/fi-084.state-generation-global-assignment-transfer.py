#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_global_assignment_transfer.json"
HYPOTHESIS_ID = "fi-084.state-generation-global-assignment-transfer"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "global_assignment_transfer_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["global_assignment_transfer", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"global assignment transfer audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate non-hard selected global assignment transfer to held-out hard episodes")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_global_assignment_transfer"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("global_assignment_transfer_closes", False))
        positive = bool(diagnosis.get("global_assignment_transfer_positive", False))
        selected = str(diagnosis.get("selected_candidate", ""))
        non_hard = float(diagnosis.get("selected_non_hard_mean_capture_ratio", 0.0))
        hard_mean = float(diagnosis.get("selected_hard_mean_capture_ratio", 0.0))
        budget2 = float(diagnosis.get("selected_hard_budget2_capture_ratio", 0.0))
        budget3 = float(diagnosis.get("selected_hard_budget3_capture_ratio", 0.0))
        budget4 = float(diagnosis.get("selected_hard_budget4_capture_ratio", 0.0))
        regret = float(diagnosis.get("selected_hard_mean_regret_to_oracle", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "global_assignment_transfer_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "global_assignment_transfer",
                "candidate_oracle_gap",
                "minimax_budget_policy",
                "episode_coupled_budget_policy",
                "oracle_budget_ceiling",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Non-hard selected global assignment transfer: "
                f"selected={selected}, non-hard mean capture={non_hard:.6g}, "
                f"held-out hard mean capture={hard_mean:.6g}, budget-2={budget2:.6g}, "
                f"budget-3={budget3:.6g}, budget-4={budget4:.6g}, hard mean regret={regret:.6g}. "
                "This is a diagnostic transfer audit, not independent export validation or allocation closure."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "global_assignment_transfer_closes": closes,
                "global_assignment_transfer_positive": positive,
                "selected_candidate": selected,
                "selected_non_hard_mean_capture_ratio": non_hard,
                "selected_hard_mean_capture_ratio": hard_mean,
                "selected_hard_budget2_capture_ratio": budget2,
                "selected_hard_budget3_capture_ratio": budget3,
                "selected_hard_budget4_capture_ratio": budget4,
                "selected_hard_mean_regret_to_oracle": regret,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

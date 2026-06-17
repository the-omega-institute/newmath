#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_perturbation_episode_transfer.json"
HYPOTHESIS_ID = "fi-088.state-generation-hard-perturbation-episode-transfer"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_perturbation_episode_transfer_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_perturbation_episode_transfer", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"hard perturbation episode-transfer audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode/depth transfer calibration for perturbation-value scores")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_perturbation_episode_transfer"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("hard_perturbation_episode_transfer_closes", False))
        improves = bool(diagnosis.get("hard_transfer_improves_base_learner", False))
        selected = str(diagnosis.get("selected_candidate", ""))
        hard_capture = float(diagnosis.get("selected_hard_mean_capture_ratio", 0.0))
        base_capture = float(diagnosis.get("base_hard_mean_capture_ratio", 0.0))
        regret = float(diagnosis.get("selected_hard_mean_regret_to_oracle", 0.0))
        rho = float(diagnosis.get("selected_hard_label_spearman", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_perturbation_episode_transfer_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_perturbation_episode_transfer",
                "forced_option_value_labels",
                "exact_budget_policy",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Hard perturbation episode-transfer audit: "
                f"selected={selected}, hard_capture={hard_capture:.6g}, base_capture={base_capture:.6g}, "
                f"hard_regret={regret:.6g}, hard_label_rho={rho:.6g}, improves={improves}. "
                "This is a non-hard-to-hard transfer audit over fixed scores, not independent export validation or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "hard_perturbation_episode_transfer_closes": closes,
                "hard_transfer_improves_base_learner": improves,
                "selected_candidate": selected,
                "selected_hard_mean_capture_ratio": hard_capture,
                "base_hard_mean_capture_ratio": base_capture,
                "selected_hard_mean_regret_to_oracle": regret,
                "selected_hard_label_spearman": rho,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

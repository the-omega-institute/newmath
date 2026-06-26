#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_coupled_budget_policy.json"
HYPOTHESIS_ID = "fi-083.state-generation-episode-coupled-budget-policy"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_coupled_budget_policy_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_coupled_budget_policy", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"episode-coupled budget policy audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode-coupled budget-policy hard oracle gap audit")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_coupled_budget_policy"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        closes = bool(diagnosis.get("episode_coupled_policy_closes", False))
        beats_minimax = bool(diagnosis.get("episode_coupled_policy_beats_minimax_mean_capture", False))
        beats_budget_head = bool(diagnosis.get("episode_coupled_policy_beats_budget_head_mean_capture", False))
        beats_replacement = bool(diagnosis.get("episode_coupled_policy_beats_replacement_mean_capture", False))
        mean_capture = float(diagnosis.get("episode_coupled_policy_mean_capture_ratio", 0.0))
        budget2 = float(diagnosis.get("episode_coupled_policy_budget2_capture_ratio", 0.0))
        budget3 = float(diagnosis.get("episode_coupled_policy_budget3_capture_ratio", 0.0))
        budget4 = float(diagnosis.get("episode_coupled_policy_budget4_capture_ratio", 0.0))
        regret = float(diagnosis.get("episode_coupled_policy_mean_regret_to_oracle", 0.0))
        minimax_mean = float(diagnosis.get("minimax_policy_mean_capture_ratio", 0.0))
        budget_head_mean = float(diagnosis.get("budget_head_mean_capture_ratio", 0.0))
        replacement_mean = float(diagnosis.get("single_budget_replacement_mean_capture_ratio", 0.0))
        metric = 1.0 if schema_ok and status_ok and closes else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_coupled_budget_policy_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_coupled_budget_policy",
                "minimax_budget_policy",
                "budget_head_value",
                "budget_replacement_value",
                "oracle_budget_ceiling",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Episode-coupled budget policy relative to the hard oracle ceiling: "
                f"mean capture={mean_capture:.6g}, budget-2 capture={budget2:.6g}, "
                f"budget-3 capture={budget3:.6g}, budget-4 capture={budget4:.6g}, "
                f"mean regret={regret:.6g}; minimax mean capture={minimax_mean:.6g}; "
                f"budget-head mean capture={budget_head_mean:.6g}; single-budget replacement mean capture={replacement_mean:.6g}. "
                "This is a set-context policy diagnostic, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "episode_coupled_policy_closes": closes,
                "episode_coupled_policy_beats_minimax_mean_capture": beats_minimax,
                "episode_coupled_policy_beats_budget_head_mean_capture": beats_budget_head,
                "episode_coupled_policy_beats_replacement_mean_capture": beats_replacement,
                "episode_coupled_policy_mean_capture_ratio": mean_capture,
                "episode_coupled_policy_budget2_capture_ratio": budget2,
                "episode_coupled_policy_budget3_capture_ratio": budget3,
                "episode_coupled_policy_budget4_capture_ratio": budget4,
                "episode_coupled_policy_mean_regret_to_oracle": regret,
                "minimax_policy_mean_capture_ratio": minimax_mean,
                "budget_head_mean_capture_ratio": budget_head_mean,
                "single_budget_replacement_mean_capture_ratio": replacement_mean,
                "not_claimed": ["deployable policy", "independent export validation", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

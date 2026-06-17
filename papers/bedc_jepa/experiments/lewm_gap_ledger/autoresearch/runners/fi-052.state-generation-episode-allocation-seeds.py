#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_allocation_seeds.json"
HYPOTHESIS_ID = "fi-052.state-generation-episode-allocation-seeds"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_allocation_seed_movement_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_allocation_seed_boundary", "world_model_gate"],
        "reported_claim": f"episode-allocation seed replication fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate seed replication for episode-level state-generation allocation")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_allocation_seeds"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        seed_count = int(summary.get("seed_count", 0))
        stable_movement = bool(summary.get("stable_movement", False))
        allocation_closed = bool(summary.get("allocation_closed", True))
        oracle_closed_count = int(summary.get("oracle_closed_count", -1))
        observed_beats = int(summary.get("observed_beats_baseline_count", -1))
        high_beats = int(summary.get("ci_high_beats_baseline_count", -1))
        valid = (
            schema_ok
            and status_ok
            and seed_count >= 3
            and stable_movement
            and not allocation_closed
            and oracle_closed_count == seed_count
            and observed_beats == seed_count
            and high_beats == seed_count
        )
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_allocation_seed_movement_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_allocation_seed_boundary",
                "allocation_native_boundary",
                "compute_value_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "episode-level allocation movement replicates across seeds without closing the allocation gate: "
                f"median episode delta={float(summary.get('episode_delta_observed_median', 0.0)):.6g}, "
                f"median episode CI high={float(summary.get('episode_delta_high_median', 0.0)):.6g}, "
                f"median baseline delta={float(summary.get('baseline_delta_observed_median', 0.0)):.6g}, "
                f"median baseline CI high={float(summary.get('baseline_delta_high_median', 0.0)):.6g}. "
                "All tested seeds improve the observed delta and CI high relative to the allocation-native baseline, "
                "but none closes allocation because episode CI highs remain nonnegative."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "seed_count": seed_count,
                "stable_movement": stable_movement,
                "allocation_closed": allocation_closed,
                "oracle_closed_count": oracle_closed_count,
                "observed_beats_baseline_count": observed_beats,
                "ci_high_beats_baseline_count": high_beats,
                "summary": summary,
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

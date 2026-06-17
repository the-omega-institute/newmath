#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_allocation.json"
HYPOTHESIS_ID = "fi-051.state-generation-episode-allocation"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_allocation_movement_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_allocation_boundary", "world_model_gate"],
        "reported_claim": f"episode-allocation boundary validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode-level state-generation allocation objective")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_allocation"
        status_ok = str(report.get("status") or "") == "ok"
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        episode = rows.get("episode_allocation", {})
        baseline = rows.get("allocation_native", {})
        oracle = rows.get("oracle_true_error", {})
        ep_delta = episode.get("allocation_delta", {})
        base_delta = baseline.get("allocation_delta", {})
        oracle_delta = oracle.get("allocation_delta", {})
        movement = (
            float(ep_delta.get("observed", 1.0)) < float(base_delta.get("observed", -1.0))
            and float(ep_delta.get("high", 1.0)) < float(base_delta.get("high", -1.0))
        )
        not_closed = float(ep_delta.get("high", -1.0)) >= 0.0
        oracle_closed = float(oracle_delta.get("high", 1.0)) < 0.0
        valid = schema_ok and status_ok and movement and not_closed and oracle_closed
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_allocation_movement_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_allocation_boundary",
                "allocation_native_boundary",
                "compute_value_labels",
                "world_model_gate",
            ],
            "reported_claim": (
                "episode-level allocation objective moves held-out eval toward allocation closure: "
                f"episode delta={float(ep_delta.get('observed', 0.0)):.6g} "
                f"[{float(ep_delta.get('low', 0.0)):.6g}, {float(ep_delta.get('high', 0.0)):.6g}], "
                f"baseline delta={float(base_delta.get('observed', 0.0)):.6g} "
                f"[{float(base_delta.get('low', 0.0)):.6g}, {float(base_delta.get('high', 0.0)):.6g}], "
                f"oracle delta={float(oracle_delta.get('observed', 0.0)):.6g}. "
                "The result is movement, not allocation closure, because the episode objective CI high remains nonnegative."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "movement": movement,
                "not_closed": not_closed,
                "oracle_closed": oracle_closed,
                "episode": episode,
                "baseline": baseline,
                "oracle": oracle,
                "selection": report.get("selection", {}),
                "oracle_choice_counts": report.get("oracle_choice_counts", {}),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

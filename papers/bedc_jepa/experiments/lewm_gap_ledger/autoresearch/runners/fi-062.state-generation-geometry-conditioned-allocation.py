#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_geometry_conditioned_allocation.json"
HYPOTHESIS_ID = "fi-062.state-generation-geometry-conditioned-allocation"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "geometry_conditioned_movement_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["geometry_conditioned_allocation", "world_model_gate"],
        "reported_claim": f"geometry-conditioned allocation validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate geometry-conditioned allocation diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_geometry_conditioned_allocation"
        status_ok = str(report.get("status") or "") == "ok"
        diagnosis = report.get("diagnosis") if isinstance(report.get("diagnosis"), dict) else {}
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        geom = rows.get("geometry_conditioned", {}) if isinstance(rows.get("geometry_conditioned"), dict) else {}
        best = rows.get("episode_best_seed", {}) if isinstance(rows.get("episode_best_seed"), dict) else {}
        geom_hard = geom.get("hard_only", {}).get("allocation_delta", {}) if isinstance(geom.get("hard_only"), dict) else {}
        best_hard = best.get("hard_only", {}).get("allocation_delta", {}) if isinstance(best.get("hard_only"), dict) else {}
        hard_improves = bool(diagnosis.get("hard_beats_best_seed_observed", False))
        full_improves = bool(diagnosis.get("full_beats_episode_objective_observed", False))
        hard_closes = bool(diagnosis.get("hard_closes", False))
        movement_valid = schema_ok and status_ok and hard_improves and full_improves and not hard_closes
        metric = 1.0 if movement_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "geometry_conditioned_movement_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "geometry_conditioned_allocation",
                "environment_state_descriptors",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Geometry-conditioned allocation gives bounded movement but not closure: "
                f"hard-only observed delta={float(geom_hard.get('observed', 0.0)):.6g}, "
                f"best-seed hard-only observed delta={float(best_hard.get('observed', 0.0)):.6g}, "
                f"geometry hard-only CI high={float(geom_hard.get('high', 0.0)):.6g}. "
                "This supports geometry conditioning as a mechanism lever while keeping allocation closure unclaimed."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "movement_valid": movement_valid,
                "hard_improves": hard_improves,
                "full_improves": full_improves,
                "hard_closes": hard_closes,
                "geometry_hard_observed": float(geom_hard.get("observed", 0.0)),
                "geometry_hard_high": float(geom_hard.get("high", 0.0)),
                "best_seed_hard_observed": float(best_hard.get("observed", 0.0)),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_environment_state_descriptors.json"
HYPOTHESIS_ID = "fi-061.state-generation-environment-state-descriptors"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "environment_state_descriptor_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["environment_state_descriptors", "world_model_gate"],
        "reported_claim": f"environment-state descriptor validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate environment-state hard-regime descriptor diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_environment_state_descriptors"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        hit_count = int(summary.get("descriptor_hit_count", 0))
        strongest_p = float(summary.get("strongest_permutation_p", 1.0))
        route_valid = schema_ok and status_ok and hit_count > 0 and strongest_p <= 0.05
        metric = 1.0 if route_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "environment_state_descriptor_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "environment_state_descriptors",
                "hard_regime_descriptors",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Explicit two-rooms environment-state descriptors separate the recurring hard episodes: "
                f"hits={hit_count}, strongest descriptor={summary.get('strongest_descriptor')}, "
                f"strongest permutation p={strongest_p:.6g}. "
                "This supports environment-state or causal-geometry conditioning, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "route_valid": route_valid,
                "descriptor_hit_count": hit_count,
                "descriptor_hits": summary.get("descriptor_hits", []),
                "strongest_descriptor": summary.get("strongest_descriptor"),
                "strongest_permutation_p": strongest_p,
                "hard_episode_union": report.get("hard_episode_union", []),
                "not_claimed": ["allocation closure", "deployable policy", "hard-regime training result"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

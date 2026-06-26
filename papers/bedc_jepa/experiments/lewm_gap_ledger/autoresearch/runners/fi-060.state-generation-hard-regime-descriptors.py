#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_regime_descriptors.json"
HYPOTHESIS_ID = "fi-060.state-generation-hard-regime-descriptors"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_regime_descriptor_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_regime_descriptors", "world_model_gate"],
        "reported_claim": f"hard-regime descriptor validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard-regime descriptor diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_regime_descriptors"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        hit_count = int(summary.get("decision_boundary_hit_count", 0))
        strongest_p = float(summary.get("strongest_permutation_p", 1.0))
        route_valid = schema_ok and status_ok and hit_count > 0 and strongest_p <= 0.10
        metric = 1.0 if route_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_regime_descriptor_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_regime_descriptors",
                "hard_episode_diagnostic",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Fixed scorer margins, scorer disagreement, exact-budget assignment flips, and rollout geometry "
                "do not separate the recurring hard episodes at the diagnostic gate: "
                f"decision-boundary hits={hit_count}, strongest descriptor={summary.get('strongest_descriptor')}, "
                f"strongest permutation p={strongest_p:.6g}. "
                "The next route needs richer causal perturbations or environment-state descriptors."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "route_valid": route_valid,
                "decision_boundary_hit_count": hit_count,
                "decision_boundary_hits": summary.get("decision_boundary_hits", []),
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

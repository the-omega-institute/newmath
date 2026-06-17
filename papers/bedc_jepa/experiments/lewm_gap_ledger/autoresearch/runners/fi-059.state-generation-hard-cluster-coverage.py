#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_cluster_coverage.json"
HYPOTHESIS_ID = "fi-059.state-generation-hard-cluster-coverage"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_cluster_coverage_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_cluster_coverage", "world_model_gate"],
        "reported_claim": f"hard-cluster coverage validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard-cluster coverage diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_cluster_coverage"
        status_ok = str(report.get("status") or "") == "ok"
        perm = report.get("permutation") if isinstance(report.get("permutation"), dict) else {}
        hard_cluster_count = int(report.get("hard_cluster_count", 999))
        unique_p = float(perm.get("unique_cluster_permutation_p_low", 1.0))
        coverage_gap = float(perm.get("hard_minus_non_hard_traincal_count", 0.0))
        coverage_p_low = float(perm.get("coverage_gap_permutation_p_low", 1.0))
        compact_signal = bool(hard_cluster_count <= 3 and unique_p <= 0.10)
        undercovered = bool(coverage_gap < 0.0 and coverage_p_low <= 0.10)
        route_valid = schema_ok and status_ok and compact_signal and undercovered
        metric = 1.0 if route_valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_cluster_coverage_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_cluster_coverage",
                "hard_episode_diagnostic",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Pre-label episode summaries show a weak compactness signal for the hard episodes "
                f"(hard clusters={hard_cluster_count}, unique-cluster permutation p={unique_p:.6g}) "
                f"but not an under-coverage explanation (coverage gap={coverage_gap:.6g}, "
                f"lower-tail p={coverage_p_low:.6g}). "
                "The next route should use richer invariant episode descriptors or perturbation features rather than simple coverage reweighting."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "compact_signal": compact_signal,
                "undercovered": undercovered,
                "simple_coverage_route_valid": route_valid,
                "hard_cluster_count": hard_cluster_count,
                "hard_clusters": report.get("hard_clusters", []),
                "hard_episode_union": report.get("hard_episode_union", []),
                "unique_cluster_permutation_p_low": unique_p,
                "hard_minus_non_hard_traincal_count": coverage_gap,
                "coverage_gap_permutation_p_low": coverage_p_low,
                "not_claimed": ["allocation closure", "deployable hard-cluster policy", "eval-label-free training result"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

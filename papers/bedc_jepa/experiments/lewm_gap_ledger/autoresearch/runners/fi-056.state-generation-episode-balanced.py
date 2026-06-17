#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_balanced.json"
HYPOTHESIS_ID = "fi-056.state-generation-episode-balanced"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_balanced_boundary_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_balanced_boundary", "world_model_gate"],
        "reported_claim": f"episode-balanced boundary validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode-balanced allocation boundary")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_balanced"
        status_ok = str(report.get("status") or "") == "ok"
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        balanced = rows.get("episode_balanced", {})
        episode = rows.get("episode_allocation", {})
        best_seed = rows.get("best_seed", {})
        baseline = rows.get("allocation_native", {})
        oracle = rows.get("oracle_true_error", {})
        b_delta = balanced.get("allocation_delta", {})
        ep_delta = episode.get("allocation_delta", {})
        seed_delta = best_seed.get("allocation_delta", {})
        base_delta = baseline.get("allocation_delta", {})
        oracle_delta = oracle.get("allocation_delta", {})
        beats_baseline = (
            float(b_delta.get("observed", 1.0)) < float(base_delta.get("observed", -1.0))
            and float(b_delta.get("high", 1.0)) < float(base_delta.get("high", -1.0))
        )
        fails_episode_objective = (
            float(b_delta.get("observed", -1.0)) >= float(ep_delta.get("observed", 1.0))
            or float(b_delta.get("high", -1.0)) >= float(ep_delta.get("high", 1.0))
        )
        fails_best_seed = (
            float(b_delta.get("observed", -1.0)) >= float(seed_delta.get("observed", 1.0))
            or float(b_delta.get("high", -1.0)) >= float(seed_delta.get("high", 1.0))
        )
        not_closed = float(b_delta.get("high", -1.0)) >= 0.0
        oracle_closed = float(oracle_delta.get("high", 1.0)) < 0.0
        valid_boundary = (
            schema_ok
            and status_ok
            and beats_baseline
            and fails_episode_objective
            and fails_best_seed
            and not_closed
            and oracle_closed
        )
        metric = 1.0 if valid_boundary else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_balanced_boundary_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "negative" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_balanced_boundary",
                "episode_allocation_boundary",
                "episode_seed_ensemble_boundary",
                "allocation_native_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "episode-balanced sampling is a bounded negative route: "
                f"balanced delta={float(b_delta.get('observed', 0.0)):.6g} "
                f"[{float(b_delta.get('low', 0.0)):.6g}, {float(b_delta.get('high', 0.0)):.6g}], "
                f"episode-objective delta={float(ep_delta.get('observed', 0.0)):.6g}, "
                f"best-seed delta={float(seed_delta.get('observed', 0.0)):.6g}. "
                "It improves over the allocation-native baseline but does not transfer better than existing episode objectives."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "beats_baseline": beats_baseline,
                "fails_episode_objective": fails_episode_objective,
                "fails_best_seed": fails_best_seed,
                "not_closed": not_closed,
                "oracle_closed": oracle_closed,
                "episode_balanced": balanced,
                "episode_allocation": episode,
                "best_seed": best_seed,
                "allocation_native": baseline,
                "oracle_true_error": oracle,
                "selection": report.get("selection", {}),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_transfer_anatomy.json"
HYPOTHESIS_ID = "fi-057.state-generation-episode-transfer-anatomy"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "episode_transfer_anatomy_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_transfer_anatomy", "world_model_gate"],
        "reported_claim": f"episode-transfer anatomy validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate held-out episode transfer anatomy")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_transfer_anatomy"
        status_ok = str(report.get("status") or "") == "ok"
        cross = report.get("cross_row") if isinstance(report.get("cross_row"), dict) else {}
        rows = report.get("rows") if isinstance(report.get("rows"), dict) else {}
        top_union_count = int(cross.get("top_harm_union_count", 999))
        shared_count = int(cross.get("shared_top_harm_episode_count", 0))
        shares = []
        harmful_counts = []
        for row in rows.values():
            summary = row.get("summary", {}) if isinstance(row, dict) else {}
            shares.append(float(summary.get("top_harm_episode_share", 0.0)))
            harmful_counts.append(int(summary.get("harmful_episode_count", 0)))
        concentrated = bool(shares and min(shares) > 0.80 and top_union_count <= 10 and shared_count >= 3)
        nontrivial = bool(harmful_counts and min(harmful_counts) >= 15)
        valid = schema_ok and status_ok and concentrated and nontrivial
        metric = 1.0 if valid else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "episode_transfer_anatomy_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_transfer_anatomy",
                "episode_seed_ensemble_boundary",
                "episode_balanced_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "held-out allocation transfer error is concentrated in a small recurring episode set: "
                f"shared top-harm episodes={cross.get('shared_top_harm_episodes', [])}, "
                f"top-harm union count={top_union_count}, "
                f"minimum top-harm share={min(shares) if shares else 0.0:.6g}. "
                "This supports hard-episode or cluster-transfer diagnostics over generic seed ensembling or episode reweighting."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "concentrated": concentrated,
                "nontrivial": nontrivial,
                "top_harm_union_count": top_union_count,
                "shared_top_harm_episode_count": shared_count,
                "shared_top_harm_episodes": cross.get("shared_top_harm_episodes", []),
                "top_harm_union_episodes": cross.get("top_harm_union_episodes", []),
                "min_top_harm_share": min(shares) if shares else 0.0,
                "row_count": len(rows),
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
HYPOTHESIS_ID = "fi-058.state-generation-hard-episode-diagnostic"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_episode_diagnostic_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_episode_diagnostic", "world_model_gate"],
        "reported_claim": f"hard-episode diagnostic validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard-episode allocation diagnostic")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_episode_diagnostic"
        status_ok = str(report.get("status") or "") == "ok"
        rows = report.get("rows") if isinstance(report.get("rows"), dict) else {}
        hard_count = int(report.get("hard_episode_count", 0))
        non_hard_closes = []
        hard_harmful = []
        hard_minus = []
        for row in rows.values():
            if not isinstance(row, dict):
                continue
            non_hard_closes.append(bool(row.get("non_hard_closes_ci", False)))
            hard_harmful.append(bool(row.get("hard_only_harmful", False)))
            hard_minus.append(float(row.get("hard_minus_non_hard_delta", 0.0)))
        localized = bool(rows and all(non_hard_closes) and all(hard_harmful) and min(hard_minus) > 0.0)
        valid = schema_ok and status_ok and hard_count <= 10 and localized
        metric = 1.0 if valid else 0.0
        summary = report.get("summary", {}) if isinstance(report.get("summary"), dict) else {}
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_episode_diagnostic_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_episode_diagnostic",
                "episode_transfer_anatomy",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "The recurring hard episode union localizes the allocation boundary: "
                f"hard episodes={report.get('hard_episode_union', [])}, "
                f"non-hard closure rows={summary.get('non_hard_closure_count', 0)}/{summary.get('row_count', 0)}, "
                f"hard-only harmful rows={summary.get('hard_only_harmful_count', 0)}/{summary.get('row_count', 0)}. "
                "This is a diagnostic localization claim, not an allocation-closure or deployable-policy claim."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "localized": localized,
                "hard_episode_count": hard_count,
                "hard_episode_union": report.get("hard_episode_union", []),
                "row_count": len(rows),
                "non_hard_closure_count": int(sum(non_hard_closes)),
                "hard_only_harmful_count": int(sum(hard_harmful)),
                "minimum_hard_minus_non_hard_delta": min(hard_minus) if hard_minus else 0.0,
                "not_claimed": ["allocation closure", "deployable policy", "hard episode training result"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

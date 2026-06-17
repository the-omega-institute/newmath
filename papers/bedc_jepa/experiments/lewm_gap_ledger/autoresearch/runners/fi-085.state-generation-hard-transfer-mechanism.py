#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_hard_transfer_mechanism.json"
HYPOTHESIS_ID = "fi-085.state-generation-hard-transfer-mechanism"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "hard_transfer_mechanism_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["hard_transfer_mechanism", "state_generation_allocation_boundary", "world_model_gate"],
        "reported_claim": f"hard transfer mechanism audit fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate hard transfer regret explanation by fixed non-label descriptors")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_hard_transfer_mechanism"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        strong = bool(summary.get("has_strong_descriptor_explanation", False))
        descriptor = str(summary.get("strongest_regret_descriptor", ""))
        abs_rho = float(summary.get("strongest_abs_spearman_all", 0.0))
        rho = float(summary.get("strongest_spearman_all", 0.0))
        count = int(summary.get("descriptor_count", 0))
        metric = 1.0 if schema_ok and status_ok and strong else 0.0
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "hard_transfer_mechanism_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "positive" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "hard_transfer_mechanism",
                "global_assignment_transfer",
                "hard_regime_descriptors",
                "environment_state_descriptors",
                "state_generation_allocation_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "Fixed non-label descriptor explanation for selected-vs-oracle hard transfer regret: "
                f"descriptor_count={count}, strongest={descriptor}, rho={rho:.6g}, abs_rho={abs_rho:.6g}. "
                "This is a descriptor audit, not allocation closure or a deployable policy."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "has_strong_descriptor_explanation": strong,
                "strongest_regret_descriptor": descriptor,
                "strongest_spearman_all": rho,
                "strongest_abs_spearman_all": abs_rho,
                "descriptor_count": count,
                "not_claimed": ["allocation closure", "deployable policy", "independent export validation"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

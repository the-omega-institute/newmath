#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "prediction_parity_gate.json"
HYPOTHESIS_ID = "fi-026.prediction-parity-gate"


def fail_closed(reason: str, report_path: Path) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "prediction_parity_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["prediction_parity", "world_model_gate"],
        "reported_claim": f"prediction parity gate fail-closed: {reason}; expected report at {report_path}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate prediction parity as a BEDC-native world-model gate")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed("missing prediction parity report", report_path)
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        gate = report.get("gate", {})
        threshold = float(gate.get("parity_threshold", 0.0))
        native = float(gate.get("native_mean_mse", 0.0))
        margin = threshold - native
        decision = str(gate.get("decision", "fail-closed"))
        status = "positive" if decision == "pass" else ("negative" if decision == "fail-closed" else "unidentifiable")
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": margin},
            "metric": "prediction_parity_margin",
            "metric_value": margin,
            "ci": {"low": margin, "high": margin},
            "status": status,
            "measured_scope": ["prediction_parity", "world_model_gate", "native_vs_lewm_next_latent_mse"],
            "reported_claim": (
                f"prediction parity gate decision={decision}: native_mean_mse={native:.9g}, "
                f"threshold={(threshold):.9g}, margin={margin:.9g}. "
                "A failing row remains a monitor or diagnostic ledger, not a BEDC-native world model."
            ),
            "diagnostics": gate,
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

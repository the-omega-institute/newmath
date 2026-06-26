#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "native_parity_candidate.json"
HYPOTHESIS_ID = "fi-027.native-parity-candidate"


def fail_closed(reason: str, report_path: Path) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "prediction_parity_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["native_parity_candidate", "prediction_parity"],
        "reported_claim": f"native parity candidate fail-closed: {reason}; expected report at {report_path}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate the direct native parity candidate run")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed("missing native parity candidate report", report_path)
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        gate = report["parity_gate"]
        metrics = report["metrics"]
        margin = float(gate["margin"])
        threshold = float(gate["threshold"])
        native_mse = metrics["native_mse"]
        margin_ci = {
            "low": threshold - float(native_mse["high"]),
            "high": threshold - float(native_mse["low"]),
        }
        if margin_ci["low"] > 0.0:
            status = "positive"
        elif margin_ci["high"] < 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": margin},
            "metric": "prediction_parity_margin",
            "metric_value": margin,
            "ci": margin_ci,
            "status": status,
            "measured_scope": ["native_parity_candidate", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"direct native parity candidate: native_mse={metrics['native_mse']['observed']:.9g}, "
                f"LeWM_mse={metrics['lewm_mse']['observed']:.9g}, "
                f"trivial_mse={metrics['trivial_mse']['observed']:.9g}, "
                f"native/LeWM={gate['native_to_lewm_ratio']:.9g}, parity_margin={margin:.9g}. "
                "The candidate beats trivial persistence but fails the world-model parity gate."
            ),
            "diagnostics": {
                "native_mse": metrics["native_mse"],
                "lewm_mse": metrics["lewm_mse"],
                "trivial_mse": metrics["trivial_mse"],
                "native_minus_lewm": metrics["native_minus_lewm"],
                "native_minus_trivial": metrics["native_minus_trivial"],
                "parity_gate": gate,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

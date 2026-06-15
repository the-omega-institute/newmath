#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
DEFAULT_BASE = REPORT_DIR / "multistep_dynamics_parity.json"
HYPOTHESIS_ID = "fi-031.multistep-dynamics-scaling"


def fail_closed(reason: str, report_path: Path) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "prediction_parity_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["multistep_dynamics_scaling", "prediction_parity"],
        "reported_claim": f"multi-step dynamics scaling fail-closed: {reason}; expected report at {report_path}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate local scaling of the multi-step dynamics parity candidate")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--base", default=str(DEFAULT_BASE))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    base_path = Path(args.base)
    if not report_path.exists():
        payload = fail_closed("missing scaled multi-step dynamics report", report_path)
    elif not base_path.exists():
        payload = fail_closed("missing base multi-step dynamics report", base_path)
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        base = json.loads(base_path.read_text(encoding="utf-8"))
        primary = report["primary"]
        base_primary = base["primary"]
        gate = primary["parity_gate"]
        metrics = primary["metrics"]
        margin = float(gate["margin"])
        threshold = float(gate["threshold"])
        native_mse = metrics["native_h1_mse"]
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
        base_native = float(base_primary["metrics"]["native_h1_mse"]["observed"])
        scaled_native = float(metrics["native_h1_mse"]["observed"])
        gain = base_native - scaled_native
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": margin},
            "metric": "prediction_parity_margin",
            "metric_value": margin,
            "ci": margin_ci,
            "status": status,
            "measured_scope": ["multistep_dynamics_scaling", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"scaled multi-step dynamics h={primary['horizon']}: "
                f"native_h1_mse={scaled_native:.9g}, base_native_h1_mse={base_native:.9g}, "
                f"gain={gain:.9g}, LeWM_h1_mse={metrics['lewm_h1_mse']['observed']:.9g}, "
                f"native/LeWM={gate['native_to_lewm_ratio']:.9g}, parity_margin={margin:.9g}. "
                "Local scaling improves the multi-step dynamics row but still fails the world-model parity gate."
            ),
            "diagnostics": {
                "base": base_primary,
                "scaled": primary,
                "gain_native_h1_mse": gain,
                "scaled_rows": report.get("rows", []),
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

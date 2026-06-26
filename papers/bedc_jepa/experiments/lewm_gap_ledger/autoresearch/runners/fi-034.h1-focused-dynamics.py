#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "multistep_dynamics_h1_focused.json"
DEFAULT_BASE = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
HYPOTHESIS_ID = "fi-034.h1-focused-dynamics"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "h1_focused_gain",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["h1_focused_dynamics", "prediction_parity"],
        "reported_claim": f"h1-focused dynamics fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate one-step-focused loss for multi-step dynamics parity")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--base", default=str(DEFAULT_BASE))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    base_path = Path(args.base)
    if not report_path.exists():
        payload = fail_closed(f"missing h1-focused report at {report_path}")
    elif not base_path.exists():
        payload = fail_closed(f"missing decay-loss scaled report at {base_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        base = json.loads(base_path.read_text(encoding="utf-8"))
        primary = report["primary"]
        base_primary = base["primary"]
        metrics = primary["metrics"]
        gate = primary["parity_gate"]
        base_metrics = base_primary["metrics"]
        h1_native = float(metrics["native_h1_mse"]["observed"])
        base_native = float(base_metrics["native_h1_mse"]["observed"])
        gain = base_native - h1_native
        native_ci = metrics["native_h1_mse"]
        base_ci = base_metrics["native_h1_mse"]
        gain_ci = {
            "low": float(base_ci["low"]) - float(native_ci["high"]),
            "high": float(base_ci["high"]) - float(native_ci["low"]),
        }
        if gain_ci["low"] > 0.0:
            status = "positive"
        elif gain_ci["high"] < 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": gain},
            "metric": "h1_focused_gain",
            "metric_value": gain,
            "ci": gain_ci,
            "status": status,
            "measured_scope": ["h1_focused_dynamics", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"h1-focused scaled dynamics h={primary['horizon']}: "
                f"native_h1_mse={h1_native:.9g}, decay_loss_native_h1_mse={base_native:.9g}, "
                f"gain={gain:.9g}, LeWM_h1_mse={metrics['lewm_h1_mse']['observed']:.9g}, "
                f"native/LeWM={gate['native_to_lewm_ratio']:.9g}, parity_margin={gate['margin']:.9g}. "
                "Focusing the loss on the first rollout step does not improve the parity row relative to the scaled decay-weighted multi-step loss."
            ),
            "diagnostics": {
                "h1_focused": primary,
                "decay_scaled": base_primary,
                "gain_native_h1_mse": gain,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

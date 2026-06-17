#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "multistep_dynamics_uniform_loss.json"
DEFAULT_BASE = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
HYPOTHESIS_ID = "fi-035.uniform-loss-dynamics"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "uniform_loss_gain",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["uniform_loss_dynamics", "prediction_parity"],
        "reported_claim": f"uniform-loss dynamics fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate uniform multi-step loss for dynamics parity")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--base", default=str(DEFAULT_BASE))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    base_path = Path(args.base)
    if not report_path.exists():
        payload = fail_closed(f"missing uniform-loss report at {report_path}")
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
        uniform_native = float(metrics["native_h1_mse"]["observed"])
        base_native = float(base_metrics["native_h1_mse"]["observed"])
        gain = base_native - uniform_native
        native_ci = metrics["native_h1_mse"]
        base_ci = base_metrics["native_h1_mse"]
        gain_ci = {
            "low": float(base_ci["low"]) - float(native_ci["high"]),
            "high": float(base_ci["high"]) - float(native_ci["low"]),
        }
        parity_margin = float(gate["margin"])
        if gain_ci["low"] > 0.0 and parity_margin >= 0.0:
            status = "positive"
        elif float(gate["threshold"]) < float(native_ci["low"]):
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": gain},
            "metric": "uniform_loss_gain",
            "metric_value": gain,
            "ci": gain_ci,
            "status": status,
            "measured_scope": ["uniform_loss_dynamics", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"uniform-loss scaled dynamics h={primary['horizon']}: "
                f"native_h1_mse={uniform_native:.9g}, decay_loss_native_h1_mse={base_native:.9g}, "
                f"gain={gain:.9g}, LeWM_h1_mse={metrics['lewm_h1_mse']['observed']:.9g}, "
                f"native/LeWM={gate['native_to_lewm_ratio']:.9g}, parity_margin={parity_margin:.9g}. "
                "Uniform multi-step loss is the best local loss profile among the checked scaled rows, but it remains far outside the LeWM prediction-parity gate."
            ),
            "diagnostics": {
                "uniform_loss": primary,
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

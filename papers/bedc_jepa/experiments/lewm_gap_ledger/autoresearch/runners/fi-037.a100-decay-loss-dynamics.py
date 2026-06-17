#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "multistep_dynamics_a100_scale.json"
DEFAULT_LOCAL = REPORT_DIR / "multistep_dynamics_parity_scaled.json"
HYPOTHESIS_ID = "fi-037.a100-decay-loss-dynamics"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "prediction_parity_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["a100_decay_loss_dynamics", "prediction_parity"],
        "reported_claim": f"A100 decay-loss dynamics fail-closed: {reason}",
    }


def parity_ci(primary: dict[str, object]) -> dict[str, float]:
    gate = primary["parity_gate"]
    native = primary["metrics"]["native_h1_mse"]
    threshold = float(gate["threshold"])
    return {
        "low": threshold - float(native["high"]),
        "high": threshold - float(native["low"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate A100 decay-loss multi-step dynamics parity result")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--local", default=str(DEFAULT_LOCAL))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    local_path = Path(args.local)
    if not report_path.exists():
        payload = fail_closed(f"missing A100 decay-loss report at {report_path}")
    elif not local_path.exists():
        payload = fail_closed(f"missing local decay-loss scaled report at {local_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        local = json.loads(local_path.read_text(encoding="utf-8"))
        primary = report["primary"]
        local_primary = local["primary"]
        metrics = primary["metrics"]
        gate = primary["parity_gate"]
        margin = float(gate["margin"])
        margin_ci = parity_ci(primary)
        if margin_ci["low"] > 0.0:
            status = "positive"
        elif margin_ci["high"] < 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        a100_native = float(metrics["native_h1_mse"]["observed"])
        local_native = float(local_primary["metrics"]["native_h1_mse"]["observed"])
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": margin},
            "metric": "prediction_parity_margin",
            "metric_value": margin,
            "ci": margin_ci,
            "status": status,
            "measured_scope": ["a100_decay_loss_dynamics", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"A100 decay-loss dynamics h={primary['horizon']}: "
                f"native_h1_mse={a100_native:.9g}, local_decay_native_h1_mse={local_native:.9g}, "
                f"A100_minus_local={a100_native - local_native:.9g}, "
                f"LeWM_h1_mse={metrics['lewm_h1_mse']['observed']:.9g}, "
                f"native/LeWM={gate['native_to_lewm_ratio']:.9g}, parity_margin={margin:.9g}. "
                "This row tests whether the decay-weighted multi-step dynamics recipe continues to improve under A100 scaling."
            ),
            "diagnostics": {
                "a100_decay": primary,
                "local_decay": local_primary,
                "a100_minus_local_native_h1_mse": a100_native - local_native,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

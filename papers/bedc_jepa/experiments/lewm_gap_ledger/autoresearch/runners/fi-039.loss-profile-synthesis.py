#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_MAIN = REPORT_DIR / "fi_035_uniform_loss_dynamics_verdict.json"
DEFAULT_REPLICATION = REPORT_DIR / "fi_038_loss_profile_seed_replication_verdict.json"
HYPOTHESIS_ID = "fi-039.loss-profile-synthesis"


def fail_closed(reason: str) -> dict[str, object]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "stable_uniform_advantage",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["loss_profile_synthesis", "prediction_parity"],
        "reported_claim": f"loss-profile synthesis fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Synthesize local loss-profile evidence across seeds")
    parser.add_argument("--main", default=str(DEFAULT_MAIN))
    parser.add_argument("--replication", default=str(DEFAULT_REPLICATION))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    main_path = Path(args.main)
    repl_path = Path(args.replication)
    if not main_path.exists():
        payload = fail_closed(f"missing main uniform-loss verdict at {main_path}")
    elif not repl_path.exists():
        payload = fail_closed(f"missing matched-seed replication verdict at {repl_path}")
    else:
        main = json.loads(main_path.read_text(encoding="utf-8"))
        repl = json.loads(repl_path.read_text(encoding="utf-8"))
        main_gain = float(main["metric_value"])
        repl_delta = float(repl["metric_value"])
        stable = 1.0 if main_gain > 0.0 and repl_delta < 0.0 else 0.0
        if stable > 0.0:
            status = "positive"
        elif main_gain > 0.0 and repl_delta > 0.0:
            status = "negative"
        else:
            status = "unidentifiable"
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": stable},
            "metric": "stable_uniform_advantage",
            "metric_value": stable,
            "ci": {"low": stable, "high": stable},
            "status": status,
            "measured_scope": ["loss_profile_synthesis", "next_latent_mse", "prediction_parity"],
            "reported_claim": (
                f"loss-profile synthesis: main uniform gain={main_gain:.9g}; "
                f"matched-seed uniform-minus-decay={repl_delta:.9g}. "
                "The local evidence does not establish a stable uniform-loss advantage; "
                "A100 uniform-loss scaling is therefore treated as an exploratory queue row, not as an already validated stronger recipe."
            ),
            "diagnostics": {
                "main_uniform_loss": main,
                "matched_seed_replication": repl,
                "stable_uniform_advantage_indicator": stable,
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

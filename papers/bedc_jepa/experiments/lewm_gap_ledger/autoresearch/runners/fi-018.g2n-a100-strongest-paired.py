#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
SOURCE = REPORT_DIR / "g2n_integrated_a100_strongest_paired.json"
HYPOTHESIS_ID = "fi-018.g2n-a100-strongest-paired"
METRIC = "native_minus_strongest_posthoc_auroc"


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"expected JSON object: {path}")
    return data


def make_payload(metric: float, low: float, high: float, claim: str, *, fail_closed: bool) -> dict[str, Any]:
    out: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": 0.0},
        "metric": METRIC,
        "metric_value": float(metric),
        "ci": {"low": float(low), "high": float(high)},
        "measured_scope": [METRIC, "auroc", "direct_paired_strongest_posthoc"],
        "reported_claim": claim,
    }
    if fail_closed:
        out["status"] = "fail-closed"
    return out


def build_payload() -> dict[str, Any]:
    data = load_json(SOURCE)
    if data is None:
        return make_payload(
            0.0,
            0.0,
            0.0,
            f"fail-closed: missing {SOURCE}; direct strongest-paired G2N A100 claim is pending.",
            fail_closed=True,
        )
    status = str(data.get("status") or "")
    ci = data.get("ci") if isinstance(data.get("ci"), dict) else {}
    low = float(ci.get("low", 0.0))
    high = float(ci.get("high", 0.0))
    metric = float(data.get("metric_value", 0.0))
    claim = str(data.get("reported_claim") or "direct strongest-paired G2N A100 result recorded.")
    return make_payload(metric, low, high, claim, fail_closed=(status == "fail-closed"))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    payload = build_payload()
    Path(args.out).write_text(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

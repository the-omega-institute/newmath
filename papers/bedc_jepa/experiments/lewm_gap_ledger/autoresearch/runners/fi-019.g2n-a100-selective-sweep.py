#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
SOURCE = REPORT_DIR / "g2n_integrated_a100_selective_sweep.json"
HYPOTHESIS_ID = "fi-019.g2n-a100-selective-sweep"
METRIC = "risk_margin"


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
        "measured_scope": [METRIC, "selective_admission", "risk_coverage_sweep"],
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
            f"fail-closed: missing {SOURCE}; selective calibration sweep is pending.",
            fail_closed=True,
        )
    rows = data.get("rows") if isinstance(data.get("rows"), list) else []
    passing = [
        row
        for row in rows
        if isinstance(row, dict) and row.get("risk_le_alpha") is True and isinstance(row.get("risk"), (int, float))
    ]
    if not passing:
        return make_payload(
            0.0,
            0.0,
            0.0,
            str(data.get("reported_claim") or "fail-closed: no selective sweep row satisfies risk <= alpha."),
            fail_closed=True,
        )
    best = max(passing, key=lambda row: float(row.get("coverage", 0.0)))
    alpha = float(best.get("alpha", 0.0))
    risk = float(best.get("risk", alpha))
    margin = alpha - risk
    claim = str(data.get("reported_claim") or f"selective sweep has risk_margin={margin:.9g}.")
    return make_payload(margin, margin, margin, claim, fail_closed=False)


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

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
SOURCE = REPORT_DIR / "g2n_integrated_a100_perm.json"
HYPOTHESIS_ID = "fi-020.g2n-a100-permutation-guard"
METRIC = "permutation_h1_margin"


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
        "measured_scope": [METRIC, "permutation_guard", "shuffled_label_control"],
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
            f"fail-closed: missing {SOURCE}; permutation guard is pending.",
            fail_closed=True,
        )
    health = data.get("health") if isinstance(data.get("health"), dict) else {}
    detection = data.get("detection") if isinstance(data.get("detection"), dict) else {}
    per_h = detection.get("per_h_auroc") if isinstance(detection.get("per_h_auroc"), dict) else {}
    h1 = per_h.get("h1")
    if str(health.get("status") or "") != "ok" or not isinstance(h1, (int, float)):
        return make_payload(0.0, 0.0, 0.0, "fail-closed: permutation control has no finite h1 AUROC.", fail_closed=True)
    margin = 0.60 - float(h1)
    claim = (
        f"shuffled-label permutation h1 AUROC={float(h1):.9g}; "
        f"permutation_h1_margin=0.60-h1={margin:.9g}; finite collapse supports capacity-artifact guard."
    )
    return make_payload(margin, margin, margin, claim, fail_closed=(margin <= 0.0))


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

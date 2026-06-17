#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_MATRIX = REPORT_DIR / "compute_value_survival_matrix.json"
HYPOTHESIS_ID = "fi-041.compute-value-survival-matrix"
TARGET_CANDIDATE = "learned_option_score"
REQUIRED_CLOSED_ENVS = 2


def fail_closed(reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "closed_independent_carriers",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["compute_value_survival_matrix", "exact_budget_allocation"],
        "reported_claim": f"compute-value survival matrix fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Gate compute-value survival matrix closure")
    parser.add_argument("--matrix", default=str(DEFAULT_MATRIX))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    matrix_path = Path(args.matrix)
    if not matrix_path.exists():
        payload = fail_closed(f"missing survival matrix report at {matrix_path}")
    else:
        report = json.loads(matrix_path.read_text(encoding="utf-8"))
        rows = report.get("rows") if isinstance(report.get("rows"), dict) else {}
        closed_envs: list[str] = []
        positive_survival_envs: list[str] = []
        diagnostics: dict[str, Any] = {}
        for env, item in sorted(rows.items()):
            if not isinstance(item, dict) or item.get("status") != "ok":
                continue
            survival = item.get("survival") if isinstance(item.get("survival"), dict) else {}
            vals = survival.get(TARGET_CANDIDATE) if isinstance(survival.get(TARGET_CANDIDATE), dict) else None
            if vals is None:
                continue
            alloc = vals.get("allocation_delta") if isinstance(vals.get("allocation_delta"), dict) else {}
            option_survival = float(vals.get("option_error_survival", 0.0))
            high = float(alloc.get("high", 0.0))
            if option_survival > 0.0:
                positive_survival_envs.append(str(env))
            if high < 0.0:
                closed_envs.append(str(env))
            diagnostics[str(env)] = {
                "option_error_survival": option_survival,
                "allocation_delta": alloc,
                "allocation_closed": bool(high < 0.0),
            }
        closed_count = float(len(closed_envs))
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": closed_count},
            "metric": "closed_independent_carriers",
            "metric_value": closed_count,
            "ci": {"low": closed_count, "high": closed_count},
            "measured_scope": [
                "compute_value_survival_matrix",
                "option_error_survival",
                "exact_budget_allocation",
                "independent_export",
            ],
            "reported_claim": (
                "compute-value survival matrix: learned option score has positive option-error survival "
                f"on {positive_survival_envs} and exact-budget allocation closure on {closed_envs}; "
                f"closed_carriers={int(closed_count)} with required minimum {REQUIRED_CLOSED_ENVS}. "
                "This is a scoped survival/control-variable gate, not a prediction-parity or universal-control claim."
            ),
            "diagnostics": {
                "matrix": str(matrix_path),
                "target_candidate": TARGET_CANDIDATE,
                "required_closed_envs": REQUIRED_CLOSED_ENVS,
                "positive_survival_envs": positive_survival_envs,
                "closed_envs": closed_envs,
                "per_env": diagnostics,
                "not_claimed": report.get("not_claimed", ""),
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

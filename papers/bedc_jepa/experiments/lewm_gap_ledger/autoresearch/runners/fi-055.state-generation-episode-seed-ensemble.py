#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_REPORT = REPORT_DIR / "state_generation_episode_seed_ensemble.json"
HYPOTHESIS_ID = "fi-055.state-generation-episode-seed-ensemble"


def fail_closed(reason: str) -> dict:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.metric", "value": 0.0},
        "metric": "seed_ensemble_boundary_valid",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["episode_seed_ensemble_boundary", "world_model_gate"],
        "reported_claim": f"episode seed-ensemble boundary validation fail-closed: {reason}",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate episode-allocation seed ensemble boundary")
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    report_path = Path(args.report)
    if not report_path.exists():
        payload = fail_closed(f"missing report at {report_path}")
    else:
        report = json.loads(report_path.read_text(encoding="utf-8"))
        schema_ok = str(report.get("schema_id") or "") == "bedc_jepa.state_generation_episode_seed_ensemble"
        status_ok = str(report.get("status") or "") == "ok"
        summary = report.get("summary") if isinstance(report.get("summary"), dict) else {}
        agreement = report.get("choice_agreement") if isinstance(report.get("choice_agreement"), dict) else {}
        rows = report.get("eval") if isinstance(report.get("eval"), dict) else {}
        best_row = str(summary.get("best_row") or "")
        best_is_ensemble = bool(summary.get("best_is_ensemble", True))
        allocation_closed = bool(summary.get("allocation_closed", True))
        oracle_closed = bool(summary.get("oracle_closed", False))
        seed_rows = [name for name in rows if name.startswith("seed_")]
        ensemble_rows = [name for name in rows if name in {"mean_score", "median_score", "mean_normalized", "median_normalized"}]
        best_seed_high = min(float(rows[name]["allocation_delta"]["high"]) for name in seed_rows) if seed_rows else 1.0
        best_ensemble_high = min(float(rows[name]["allocation_delta"]["high"]) for name in ensemble_rows) if ensemble_rows else 0.0
        ensemble_fails_best_seed = best_ensemble_high >= best_seed_high
        stable_but_wrong = (
            float(agreement.get("majority_choice_rate", 0.0)) > 0.80
            and float(agreement.get("oracle_choice_majority_match", 1.0)) < 0.50
        )
        valid_boundary = (
            schema_ok
            and status_ok
            and not allocation_closed
            and oracle_closed
            and not best_is_ensemble
            and ensemble_fails_best_seed
            and stable_but_wrong
        )
        metric = 1.0 if valid_boundary else 0.0
        best_delta = rows.get(best_row, {}).get("allocation_delta", {})
        payload = {
            "hypothesis_id": HYPOTHESIS_ID,
            "anchor": {"field": "anchor.metric", "value": metric},
            "metric": "seed_ensemble_boundary_valid",
            "metric_value": metric,
            "ci": {"low": metric, "high": metric},
            "status": "negative" if metric > 0.0 else "fail-closed",
            "measured_scope": [
                "episode_seed_ensemble_boundary",
                "episode_allocation_boundary",
                "allocation_native_boundary",
                "world_model_gate",
            ],
            "reported_claim": (
                "seed ensembling does not close the episode-allocation boundary: "
                f"best row={best_row}, delta={float(best_delta.get('observed', 0.0)):.6g} "
                f"[{float(best_delta.get('low', 0.0)):.6g}, {float(best_delta.get('high', 0.0)):.6g}], "
                f"best ensemble CI high={best_ensemble_high:.6g}, best seed CI high={best_seed_high:.6g}. "
                f"Seed majority choice rate={float(agreement.get('majority_choice_rate', 0.0)):.6g}, "
                f"oracle-majority match={float(agreement.get('oracle_choice_majority_match', 0.0)):.6g}."
            ),
            "diagnostics": {
                "schema_ok": schema_ok,
                "status_ok": status_ok,
                "best_row": best_row,
                "best_is_ensemble": best_is_ensemble,
                "allocation_closed": allocation_closed,
                "oracle_closed": oracle_closed,
                "ensemble_fails_best_seed": ensemble_fails_best_seed,
                "stable_but_wrong": stable_but_wrong,
                "best_seed_high": best_seed_high,
                "best_ensemble_high": best_ensemble_high,
                "choice_agreement": agreement,
                "summary": summary,
                "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
            },
        }
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

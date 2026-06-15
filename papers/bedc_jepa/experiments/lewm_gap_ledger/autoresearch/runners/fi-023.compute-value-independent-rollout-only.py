#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_ARTIFACT = REPORT_DIR / "compute_value_independent_rollout_only_predictions.npz"
HYPOTHESIS_ID = "fi-023.compute-value-independent-rollout-only"
BASE_RUNNER = Path(__file__).with_name("fi-022.compute-value-structured-assignment.py")


def load_base_runner() -> Any:
    spec = importlib.util.spec_from_file_location("fi022_structured_assignment", BASE_RUNNER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rewrite_payload(payload: dict[str, Any], artifact: Path) -> dict[str, Any]:
    out = dict(payload)
    out["hypothesis_id"] = HYPOTHESIS_ID
    if payload.get("status") == "fail-closed":
        out["reported_claim"] = (
            "independent rollout-only structured assignment runner fail-closed: "
            f"{payload.get('reported_claim', '')}; expected artifact at {artifact}"
        )
        return out
    rho = float(payload.get("diagnostics", {}).get("score_error_spearman", 0.0))
    low = float(payload["ci"]["low"])
    high = float(payload["ci"]["high"])
    value = float(payload["metric_value"])
    out["measured_scope"] = [
        "allocation_delta",
        "independent_export",
        "rollout_only_features",
        "structured_exact_budget_assignment",
        "score_error_spearman",
    ]
    out["reported_claim"] = (
        "On the independent PushT horizon export, a rollout-only option-conditioned "
        f"structured assignment artifact gives allocation_delta={value:.9g}, "
        f"95% CI=[{low:.9g},{high:.9g}], score/error Spearman={rho:.9g}. "
        "This is not a full-feature structured-assignment replication because base "
        "latent/action features are absent from the independent export."
    )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate independent rollout-only structured compute-value assignment")
    parser.add_argument("--artifact", default=str(DEFAULT_ARTIFACT))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    artifact = Path(args.artifact)
    base = load_base_runner()
    if not artifact.exists():
        payload = base.fail_closed("missing independent rollout-only artifact", artifact=artifact)
    else:
        arrays = base.load_npz(artifact)
        reason = base.validate(arrays)
        payload = base.fail_closed(reason, artifact=artifact) if reason else base.evaluate(arrays, seed=int(args.seed))
    payload = rewrite_payload(payload, artifact)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

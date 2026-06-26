#!/usr/bin/env python3
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
REPORT_DIR = ROOT / "reports"
DEFAULT_ARTIFACT = REPORT_DIR / "compute_value_independent_full_feature_predictions.npz"
DEFAULT_MANIFEST = REPORT_DIR / "compute_value_independent_full_feature.json"
HYPOTHESIS_ID = "fi-025.compute-value-independent-full-feature"
BASE_RUNNER = Path(__file__).with_name("fi-022.compute-value-structured-assignment.py")


def load_base_runner() -> Any:
    spec = importlib.util.spec_from_file_location("fi022_structured_assignment", BASE_RUNNER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load base runner: {BASE_RUNNER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_manifest(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        return {"status": "unreadable", "error": str(exc)}


def rewrite_payload(payload: dict[str, Any], artifact: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    out = dict(payload)
    out["hypothesis_id"] = HYPOTHESIS_ID
    out["measured_scope"] = [
        "allocation_delta",
        "independent_export",
        "full_feature_state_action_rollout",
        "structured_exact_budget_assignment",
    ]
    if payload.get("status") == "fail-closed":
        missing = manifest.get("missing_or_invalid", [])
        reason = "; ".join(str(item) for item in missing) if missing else payload.get("reported_claim", "")
        out["reported_claim"] = (
            "independent full-feature structured assignment runner fail-closed: "
            f"{reason}; expected artifact at {artifact}. "
            "No full-feature independent replication is claimed."
        )
        out["diagnostics"] = {
            "manifest_status": manifest.get("status", "missing"),
            "missing_or_invalid": missing,
            "manifest": str(DEFAULT_MANIFEST),
        }
        return out
    rho = float(payload.get("diagnostics", {}).get("score_error_spearman", 0.0))
    low = float(payload["ci"]["low"])
    high = float(payload["ci"]["high"])
    value = float(payload["metric_value"])
    out["reported_claim"] = (
        "On an independent export with aligned base latent/action and rollout-internal features, "
        f"the full-feature option-conditioned structured assignment artifact gives allocation_delta={value:.9g}, "
        f"95% CI=[{low:.9g},{high:.9g}], score/error Spearman={rho:.9g}."
    )
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="Evaluate independent full-feature structured compute-value assignment")
    parser.add_argument("--artifact", default=str(DEFAULT_ARTIFACT))
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    artifact = Path(args.artifact)
    manifest_path = Path(args.manifest)
    manifest = load_manifest(manifest_path)
    base = load_base_runner()
    if not artifact.exists():
        payload = base.fail_closed("missing independent full-feature artifact", artifact=artifact)
    else:
        arrays = base.load_npz(artifact)
        reason = base.validate(arrays)
        payload = base.fail_closed(reason, artifact=artifact) if reason else base.evaluate(arrays, seed=int(args.seed))
    payload = rewrite_payload(payload, artifact, manifest)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

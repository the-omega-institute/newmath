"""Public JEPA-family baseline registry for BEDC-JEPA contact readiness."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def _vjepa2_ac_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "vjepa2-ac",
        "name": "V-JEPA 2-AC",
        "repository_url": "https://github.com/facebookresearch/vjepa2",
        "baseline_role": "action-conditioned latent world-model baseline",
        "why_relevant": (
            "V-JEPA 2-AC is the closest public JEPA-family contact because it "
            "uses action-conditioned latent prediction for world modeling."
        ),
        "expected_input_contract": [
            "visual observations or video frames",
            "action sequence or action token stream",
        ],
        "expected_output_contract": [
            "latent rollout or predicted representation",
            "planning or control-facing latent state",
        ],
        "bedc_comparison_contract": [
            "same observation/action stream",
            "matched latent readback scope where feasible",
            "BEDC distinction head and gap head evaluated on the same rollout cases",
            "unlogged error, gap AUROC, certified coverage, and debt reported beside baseline scores",
        ],
        "current_artifact_status": "not_executed",
    }


def _leworldmodel_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "leworldmodel-lejepa",
        "name": "LeWorldModel / LeJEPA baseline",
        "repository_url": "https://github.com/lucas-maes/le-wm",
        "baseline_role": "LeJEPA-style pixel world-model baseline",
        "why_relevant": (
            "LeWorldModel reports stable end-to-end JEPA world modeling from "
            "pixels and publishes LeJEPA baseline checkpoints and data pointers."
        ),
        "expected_input_contract": [
            "pixel observations",
            "benchmark configuration and checkpoint/data path",
        ],
        "expected_output_contract": [
            "next-embedding prediction score",
            "planning or rollout quality metrics where available",
        ],
        "bedc_comparison_contract": [
            "same pixel benchmark split",
            "baseline next-embedding prediction metrics",
            "BEDC objective readback metrics on the declared distinction/gap scope",
        ],
        "current_artifact_status": "not_executed",
    }


def build_public_jepa_baseline_registry() -> dict[str, Any]:
    candidates = [_vjepa2_ac_candidate(), _leworldmodel_candidate()]
    return {
        "schema_id": "bedc-jepa-public-baseline-registry",
        "status": "contract_only",
        "selected_candidate_id": "vjepa2-ac",
        "candidates": candidates,
        "execution_status": {
            "status": "missing",
            "reason": "no public JEPA-family baseline has been cloned, vendored, or executed in this workspace",
        },
        "next_actions": [
            "clone or vendor the selected public baseline in an approved environment",
            "record the exact commit, checkpoint, dataset, and command line",
            "run the selected baseline on a public visual/action benchmark",
            "export baseline metrics into a BEDC-JEPA comparison artifact",
        ],
    }


def build_public_jepa_baseline_comparison() -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    selected = next(
        candidate for candidate in registry["candidates"] if candidate["candidate_id"] == registry["selected_candidate_id"]
    )
    return {
        "schema_id": "bedc-jepa-public-baseline-comparison",
        "status": "missing",
        "selected_candidate_id": registry["selected_candidate_id"],
        "selected_repository_url": selected["repository_url"],
        "comparison_contract": {
            "baseline_role": selected["baseline_role"],
            "bedc_comparison_contract": selected["bedc_comparison_contract"],
            "expected_input_contract": selected["expected_input_contract"],
            "expected_output_contract": selected["expected_output_contract"],
        },
        "baseline_metrics": {
            "latent_prediction_score": None,
            "rollout_or_planning_score": None,
            "reported_benchmark_name": None,
        },
        "bedc_metrics_source": "reports/bedc_jepa_torch_objective.json",
        "bedc_metrics_required": [
            "gap_auc_gain_mean",
            "unlogged_error_reduction_mean",
            "debt_reduction_mean",
            "latent_r2_delta_abs_max",
        ],
        "blocking_reason": "selected public baseline has not been executed in this workspace",
        "cannot_claim": [
            "public JEPA baseline comparison",
            "JEPA-family checkpoint parity",
            "public benchmark score superiority",
        ],
    }


def import_public_jepa_baseline_metrics(result: dict[str, Any]) -> dict[str, Any]:
    required = {
        "candidate_id",
        "commit",
        "checkpoint",
        "reported_benchmark_name",
        "latent_prediction_score",
        "rollout_or_planning_score",
    }
    missing = sorted(required - set(result))
    if missing:
        raise ValueError(f"missing public baseline result fields: {', '.join(missing)}")
    registry = build_public_jepa_baseline_registry()
    candidates = {candidate["candidate_id"]: candidate for candidate in registry["candidates"]}
    candidate_id = str(result["candidate_id"])
    if candidate_id not in candidates:
        raise ValueError(f"unknown public baseline candidate: {candidate_id}")
    selected = candidates[candidate_id]
    comparison = build_public_jepa_baseline_comparison()
    comparison["status"] = "executed"
    comparison["selected_candidate_id"] = candidate_id
    comparison["selected_repository_url"] = selected["repository_url"]
    comparison["comparison_contract"] = {
        "baseline_role": selected["baseline_role"],
        "bedc_comparison_contract": selected["bedc_comparison_contract"],
        "expected_input_contract": selected["expected_input_contract"],
        "expected_output_contract": selected["expected_output_contract"],
    }
    comparison["baseline_metrics"] = {
        "latent_prediction_score": float(result["latent_prediction_score"]),
        "rollout_or_planning_score": float(result["rollout_or_planning_score"]),
        "reported_benchmark_name": str(result["reported_benchmark_name"]),
    }
    comparison["execution_record"] = {
        "commit": str(result["commit"]),
        "checkpoint": str(result["checkpoint"]),
    }
    comparison["blocking_reason"] = None
    comparison["cannot_claim"] = []
    return comparison


def write_public_jepa_baseline_registry(path: str | Path) -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return registry


def write_public_jepa_baseline_comparison(path: str | Path) -> dict[str, Any]:
    comparison = build_public_jepa_baseline_comparison()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return comparison


def import_public_jepa_baseline_metrics_file(source: str | Path, target: str | Path) -> dict[str, Any]:
    result = json.loads(Path(source).read_text(encoding="utf-8"))
    comparison = import_public_jepa_baseline_metrics(result)
    target_path = Path(target)
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return comparison

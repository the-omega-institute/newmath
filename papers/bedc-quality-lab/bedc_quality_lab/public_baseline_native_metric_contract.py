"""Native-metric contract for importing public JEPA-family baseline results."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from bedc_quality_lab.public_jepa_baselines import build_public_jepa_baseline_registry


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


REQUIRED_EXECUTION_FIELDS = (
    "candidate_id",
    "repository_commit",
    "checkpoint_identity",
    "dataset_identity",
    "environment_or_benchmark_name",
    "execution_command",
    "observation_action_stream_contract",
    "native_metric_contract",
    "latent_prediction_score",
    "rollout_or_planning_score",
    "bedc_readback_metrics",
    "lccp_certificate_metrics",
    "cannot_claim_boundary",
)

BEDC_READBACK_FIELDS = (
    "distinction_accuracy",
    "gap_detection_auc",
    "unlogged_error",
    "certified_coverage",
    "debt",
)

LCCP_FIELDS = (
    "alpha_grid",
    "certified_claim_count",
    "gap_claim_count",
    "mean_certified_coverage",
    "mean_unlogged_error",
    "mean_conformal_miscoverage",
)


def _load_optional_json(name: str) -> dict[str, Any] | None:
    path = REPORTS / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _is_unrecorded(value: Any) -> bool:
    text = str(value).strip()
    lowered = text.lower()
    return (
        not text
        or (text.startswith("<") and text.endswith(">"))
        or lowered in {"none", "null", "unknown", "not_evaluated"}
        or "not recorded" in lowered
    )


def _selected_candidate() -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    selected_id = registry["selected_candidate_id"]
    return next(candidate for candidate in registry["candidates"] if candidate["candidate_id"] == selected_id)


def build_public_baseline_native_metric_contract() -> dict[str, Any]:
    selected = _selected_candidate()
    near_native = _load_optional_json("bedc_vjepa2_ac_native_reproduction.json")
    comparison = _load_optional_json("bedc_jepa_public_baseline_comparison.json")
    fixed_checkpoint_metric_import = "not_evaluated"
    if comparison is not None and comparison.get("status") == "executed":
        fixed_checkpoint_metric_import = "executed"
    near_native_status = (
        str(near_native.get("status")) if near_native is not None else "not_recorded"
    )
    near_native_commit = (
        near_native.get("vjepa2_repository_commit") if near_native is not None else None
    )
    near_native_importable = near_native_status == "evaluated_near_native" and not _is_unrecorded(
        near_native_commit
    )
    return {
        "schema_id": "bedc-jepa-public-baseline-native-metric-contract",
        "status": "contract_ready",
        "selected_candidate_id": selected["candidate_id"],
        "selected_candidate_name": selected["name"],
        "repository_url": selected["repository_url"],
        "required_execution_fields": list(REQUIRED_EXECUTION_FIELDS),
        "native_metric_contract": {
            "score_fields": [
                "latent_prediction_score",
                "rollout_or_planning_score",
            ],
            "bedc_readback_fields": list(BEDC_READBACK_FIELDS),
            "lccp_certificate_fields": list(LCCP_FIELDS),
            "same_protocol_requirements": [
                "same public observation/action stream",
                "same split or declared split mapping",
                "same predicate set",
                "same alpha grid for LCCP",
                "same BEDC gap and debt definitions",
                "declared preprocessing and action encoding",
            ],
            "native_result_requirements": [
                "repository commit is recorded",
                "checkpoint identity is recorded",
                "dataset identity is recorded",
                "execution command is recorded",
                "native metric names and score directions are recorded",
                "cannot-claim boundary is recorded",
            ],
        },
        "execution_template": {
            "candidate_id": selected["candidate_id"],
            "repository_commit": "<git commit or release tag>",
            "checkpoint_identity": "<checkpoint URL, hash, or model card identity>",
            "dataset_identity": "<dataset or environment stream identity>",
            "environment_or_benchmark_name": "<public benchmark name>",
            "execution_command": "<exact command used to run the baseline>",
            "observation_action_stream_contract": {
                "observation_preprocessing": "<image or video preprocessing contract>",
                "action_encoding": "<action token or action vector contract>",
                "split": "<train/cal/test or declared split mapping>",
            },
            "native_metric_contract": {
                "latent_prediction_score": "<score name, direction, and aggregation>",
                "rollout_or_planning_score": "<score name, direction, and aggregation>",
            },
            "latent_prediction_score": "<float>",
            "rollout_or_planning_score": "<float>",
            "bedc_readback_metrics": {field: "<float>" for field in BEDC_READBACK_FIELDS},
            "lccp_certificate_metrics": {field: "<value>" for field in LCCP_FIELDS},
            "cannot_claim_boundary": [
                "public benchmark superiority unless comparative acceptance rule passes",
                "official reproduction unless the official protocol is executed",
            ],
        },
        "current_status": {
            "official_protocol_execution": "not_evaluated",
            "fixed_checkpoint_metric_import": fixed_checkpoint_metric_import,
            "near_native_fixed_checkpoint_record": near_native_status,
            "near_native_metric_importable": "yes" if near_native_importable else "no",
            "near_native_metric_import_gap": (
                "none" if near_native_importable else "repository commit is not recorded"
            ),
            "near_native_record": "reports/bedc_vjepa2_ac_native_reproduction.json",
            "public_baseline_comparison": "reports/bedc_jepa_public_baseline_comparison.json",
        },
        "accepted_import_status": "executed only when every required execution field is present",
        "cannot_claim": [
            "official V-JEPA2-AC benchmark reproduction",
            "public benchmark superiority",
            "native external baseline comparison without an executed result import",
        ],
    }


def validate_public_baseline_native_metric_result(result: dict[str, Any]) -> None:
    missing = sorted(set(REQUIRED_EXECUTION_FIELDS) - set(result))
    if missing:
        raise ValueError(f"missing public baseline native-metric fields: {', '.join(missing)}")
    for field in (
        "repository_commit",
        "checkpoint_identity",
        "dataset_identity",
        "environment_or_benchmark_name",
        "execution_command",
    ):
        if _is_unrecorded(result[field]):
            raise ValueError(f"{field} must be recorded before native-metric import")
    selected = _selected_candidate()
    if str(result["candidate_id"]) != selected["candidate_id"]:
        raise ValueError(f"unknown public baseline candidate: {result['candidate_id']}")
    bedc_metrics = result.get("bedc_readback_metrics")
    if not isinstance(bedc_metrics, dict):
        raise ValueError("bedc_readback_metrics must be a JSON object")
    missing_bedc = sorted(set(BEDC_READBACK_FIELDS) - set(bedc_metrics))
    if missing_bedc:
        raise ValueError(f"missing BEDC readback metric fields: {', '.join(missing_bedc)}")
    lccp_metrics = result.get("lccp_certificate_metrics")
    if not isinstance(lccp_metrics, dict):
        raise ValueError("lccp_certificate_metrics must be a JSON object")
    missing_lccp = sorted(set(LCCP_FIELDS) - set(lccp_metrics))
    if missing_lccp:
        raise ValueError(f"missing LCCP certificate metric fields: {', '.join(missing_lccp)}")
    native_contract = result.get("native_metric_contract")
    if not isinstance(native_contract, dict):
        raise ValueError("native_metric_contract must be a JSON object")
    stream_contract = result.get("observation_action_stream_contract")
    if not isinstance(stream_contract, dict):
        raise ValueError("observation_action_stream_contract must be a JSON object")
    cannot_claim = result.get("cannot_claim_boundary")
    if not isinstance(cannot_claim, list) or not all(isinstance(item, str) for item in cannot_claim):
        raise ValueError("cannot_claim_boundary must be a list of strings")


def write_public_baseline_native_metric_contract(path: str | Path) -> dict[str, Any]:
    contract = build_public_baseline_native_metric_contract()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(contract, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return contract


def build_public_baseline_native_metric_template() -> dict[str, Any]:
    contract = build_public_baseline_native_metric_contract()
    return {
        "schema_id": "bedc-jepa-public-baseline-native-metric-template",
        "template_for": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
        "candidate_id": contract["selected_candidate_id"],
        "repository_url": contract["repository_url"],
        "required_execution_fields": contract["required_execution_fields"],
        "native_metric_contract": contract["native_metric_contract"],
        "result": contract["execution_template"],
        "instructions": [
            "Fill every placeholder before importing the result.",
            "Do not change cannot_claim_boundary unless the corresponding evidence is present.",
            "Import with: python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
        ],
        "cannot_claim": [
            "executed external baseline result",
            "official V-JEPA2-AC benchmark reproduction",
            "public benchmark superiority",
        ],
    }


def write_public_baseline_native_metric_template(path: str | Path) -> dict[str, Any]:
    template = build_public_baseline_native_metric_template()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(template, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return template

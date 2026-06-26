"""Fail-closed scope contracts for public pixel and object-interaction benchmarks."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


PUBLIC_BENCHMARK_CONTRACTS: tuple[dict[str, Any], ...] = (
    {
        "contract_id": "public_pixel_world_benchmark",
        "scope": "public pixel-world benchmark comparison",
        "target_artifact": "reports/bedc_jepa_public_pixel_world_benchmark_contract.json",
        "required_execution_fields": [
            "benchmark_name",
            "dataset_or_environment_identity",
            "repository_or_dataset_commit",
            "observation_preprocessing",
            "action_or_transition_contract",
            "train_cal_test_split",
            "latent_or_rollout_metric",
            "bedc_readback_metrics",
            "lccp_certificate_metrics",
            "cannot_claim_boundary",
        ],
        "required_bedc_metrics": [
            "distinction_accuracy",
            "gap_detection_auc",
            "unlogged_error",
            "certified_coverage",
            "debt",
        ],
        "accepted_result_status": "executed_public_pixel_world_result",
        "source_gap_status": "source_gap_until_public_pixel_world_result_is_imported",
        "cannot_claim": [
            "public pixel-world benchmark superiority",
            "large-scale real-world world modeling",
            "robotics benchmark result",
        ],
    },
    {
        "contract_id": "public_object_interaction_benchmark",
        "scope": "public object-interaction benchmark with natural clutter or control",
        "target_artifact": "reports/bedc_jepa_public_object_interaction_benchmark_contract.json",
        "required_execution_fields": [
            "benchmark_name",
            "dataset_or_environment_identity",
            "repository_or_dataset_commit",
            "object_source_contract",
            "intervention_or_action_contract",
            "target_predicate_set",
            "distractor_or_clutter_contract",
            "train_cal_test_split",
            "counterfactual_or_intervention_metric",
            "bedc_readback_metrics",
            "lccp_certificate_metrics",
            "cannot_claim_boundary",
        ],
        "required_bedc_metrics": [
            "counterfactual_accuracy",
            "intervention_sensitivity",
            "target_minus_distractor_masking_drop",
            "gap_detection_auc",
            "unlogged_error",
            "certified_coverage",
            "debt",
        ],
        "accepted_result_status": "executed_public_object_interaction_result",
        "source_gap_status": "source_gap_until_public_object_interaction_result_is_imported",
        "cannot_claim": [
            "public object-interaction benchmark superiority",
            "natural-language semantic grounding",
            "robotics benchmark result",
        ],
    },
)


def build_public_benchmark_scope_contracts() -> dict[str, Any]:
    contracts = []
    for contract in PUBLIC_BENCHMARK_CONTRACTS:
        contracts.append(
            {
                **contract,
                "status": "contract_ready",
                "current_result_status": "not_imported",
                "claim_rule": (
                    "A public benchmark claim is admissible only after an executed result "
                    "satisfying every required execution field is imported; otherwise the "
                    "scope remains a source gap."
                ),
            }
        )
    return {
        "schema_id": "bedc-jepa-public-benchmark-scope-contracts",
        "status": "contract_ready",
        "contracts": contracts,
        "cannot_claim": [
            "public pixel-world benchmark result",
            "public object-interaction benchmark result",
            "public benchmark superiority",
        ],
    }


def write_public_benchmark_scope_contracts(path: str | Path) -> dict[str, Any]:
    packet = build_public_benchmark_scope_contracts()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

"""External execution contract for closing BEDC-JEPA readiness gates."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def build_external_run_kit() -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-external-run-kit",
        "status": "review_ready",
        "required_external_results": {
            "public_jepa_checkpoint_evaluation": {
                "readiness_gate": "public_jepa_checkpoint_evaluation",
                "target_artifact": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
                "run_command": "python scripts/run_public_jepa_ac_giant_adapter.py",
                "comparison_command": "python scripts/build_public_jepa_cuda_comparison.py",
                "pass_condition": "target record status is executed and AC Giant checkpoint_status is loaded under CUDA",
            },
            "public_minigrid_execution": {
                "readiness_gate": "public_minigrid_execution",
                "target_artifact": "reports/bedc_jepa_public_minigrid_benchmark_packet.json",
                "export_command": "python scripts/export_public_minigrid_benchmark_result.py",
                "import_command": "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>",
                "required_fields": [
                    "environment_id",
                    "seed",
                    "sample_count_requested",
                    "sample_count_collected",
                    "distinction_accuracy",
                    "gap_detection_auc",
                    "unlogged_error_rate",
                    "certified_coverage",
                    "bedc_debt_score",
                ],
                "pass_condition": "target record status is available and sample_count_collected is positive",
            },
            "public_jepa_baseline": {
                "readiness_gate": "native_public_jepa_benchmark",
                "target_artifact": "reports/bedc_jepa_public_native_minigrid_benchmark.json",
                "run_command": "python scripts/run_public_minigrid_native_benchmark.py",
                "seed_sweep_command": "python scripts/run_public_minigrid_native_seed_sweep.py",
                "probe_command": "python scripts/probe_public_jepa_baseline.py",
                "export_command": "python scripts/export_public_jepa_baseline_result.py",
                "import_command": "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
                "required_fields": [
                    "environment_id",
                    "systems",
                    "planning_lambda_sweep",
                    "jepa_family_baseline_boundary",
                    "deltas",
                ],
                "pass_condition": "target record status is executed with S0/S1/S2/S3, baseline boundary, and nonzero planning high-gap reduction",
            },
            "torch_retraining_loss_ablation": {
                "readiness_gate": "full_retraining_loss_ablation",
                "target_artifact": "reports/bedc_jepa_retraining_loss_ablation.json",
                "run_command": "python scripts/run_torch_retraining_loss_ablation.py",
                "required_systems": [
                    "full_s3",
                    "minus_l_unlogged",
                    "minus_l_gap",
                    "minus_l_stab",
                    "minus_l_intervention",
                ],
                "source_surface_contract": {
                    "stability_consistency": [
                        "stability_source_split",
                        "paired_observations_or_augmentations",
                        "stability_label_or_invariance_target",
                        "same_train_cal_test_split",
                    ],
                    "intervention_bce": [
                        "intervention_source_split",
                        "pre_intervention_observation",
                        "intervention_or_action",
                        "post_intervention_label",
                        "same_train_cal_test_split",
                    ],
                },
                "pass_condition": "target record status is executed and full S3, minus L_unlogged, minus L_gap, minus L_stab, and minus L_intervention are true retraining rows under the declared OU-pair stability and intervention surfaces",
            },
            "vjepa2_ac_native_reproduction": {
                "readiness_gate": "vjepa2_ac_native_reproduction",
                "target_artifact": "reports/bedc_vjepa2_ac_native_reproduction.json",
                "comparison_artifact": "reports/bedc_vjepa2_ac_native_readback_comparison.json",
                "boundary_record": "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
                "required_fields": [
                    "public_environment_id",
                    "image_action_stream_split",
                    "vjepa2_repository_commit",
                    "checkpoint_identity",
                    "execution_command",
                    "native_or_near_native_rollout_score",
                    "latent_prediction_score",
                    "bedc_readback_metrics",
                    "lccp_certificate_metrics",
                    "cannot_claim_boundary",
                ],
                "parity_protocol_fields": [
                    "same_observation_preprocessing",
                    "same_action_encoding",
                    "same_train_cal_test_split",
                    "same_planning_or_rollout_target",
                    "same_bedc_predicate_set",
                    "same_alpha_grid",
                ],
                "pass_condition": "native reproduction remains unevaluated until the native score, checkpoint identity, command, stream split, and BEDC readback metrics are recorded together",
            },
            "vjepa2_ac_minigrid_claim_certificate": {
                "readiness_gate": "vjepa2_ac_fixed_carrier_lccp",
                "target_artifact": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
                "run_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
                "required_fields": [
                    "execution_contract",
                    "checkpoint_contract",
                    "feature_contract",
                    "claims",
                    "cannot_claim",
                ],
                "required_predicates": [
                    "door_key_context_visible",
                    "unsafe_transition",
                    "has_key",
                    "door_open_or_unlocked",
                    "goal_reachable_with_current_state",
                ],
                "pass_condition": "target record includes execution, checkpoint, and feature contracts and assigns each predicate to certified, coverage-debt, or source-debt status under LCCP",
            },
            "vjepa2_ac_minigrid_latent_prediction": {
                "readiness_gate": "vjepa2_ac_minigrid_latent_prediction",
                "target_artifact": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
                "run_command": "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
                "required_fields": [
                    "candidate_id",
                    "environment_id",
                    "sample_counts",
                    "execution_contract",
                    "checkpoint_contract",
                    "feature_contract",
                    "metrics",
                    "claim_scope",
                    "cannot_claim",
                ],
                "pass_condition": "target record status is executed and reports latent_prediction_score beside execution, checkpoint, feature, and cannot-claim contracts",
            },
        },
        "readiness_command": "python scripts/build_bedc_jepa_readiness.py",
        "review_bundle_command": "python scripts/build_bedc_jepa_review_bundle.py",
        "quality_backend_candidate_command": "python scripts/build_bedc_jepa_quality_backend_candidate.py",
        "latent_claim_certificate_command": "python scripts/run_bedc_latent_claim_certificate.py",
        "torch_retraining_loss_ablation_command": "python scripts/run_torch_retraining_loss_ablation.py",
        "vjepa2_ac_minigrid_claim_certificate_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
        "vjepa2_ac_minigrid_latent_prediction_command": "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
        "verification_commands": [
            "python -m pytest -q",
            "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        ],
        "cannot_claim_until_ready": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
        ],
    }


def write_external_run_kit(path: str | Path) -> dict[str, Any]:
    kit = build_external_run_kit()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(kit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return kit

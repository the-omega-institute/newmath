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
            "public_baseline_native_metric_contract": {
                "readiness_gate": "public_baseline_native_metric_contract",
                "target_artifact": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
                "template_artifact": "reports/bedc_jepa_public_baseline_native_metric_template.json",
                "build_command": "python scripts/build_public_baseline_native_metric_contract.py",
                "template_command": "python scripts/build_public_baseline_native_metric_template.py",
                "import_command": "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
                "required_execution_fields": [
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
                ],
                "pass_condition": "contract record is ready; external baseline comparison remains unevaluated until a result satisfying this contract is imported",
            },
            "public_minigrid_calibration_extension": {
                "readiness_gate": "public_minigrid_calibration_extension",
                "target_artifact": "reports/bedc_jepa_public_minigrid_calibration_extension.json",
                "run_command": "python scripts/build_public_minigrid_calibration_extension.py",
                "required_fields": [
                    "task_variants",
                    "seeds",
                    "planning_state_counts",
                    "summary",
                    "rows",
                    "cannot_claim",
                ],
                "coverage_requirements": {
                    "minimum_executed_rows": 30,
                    "minimum_seed_count": 5,
                    "minimum_task_variant_count": 3,
                    "minimum_planning_budget_count": 3,
                },
                "pass_condition": "target record executes at least 30 public MiniGrid calibration rows across at least five seeds, three task variants, and three planning budgets",
            },
            "public_benchmark_scope_contracts": {
                "readiness_gate": "public_benchmark_scope_contracts",
                "target_artifact": "reports/bedc_jepa_public_benchmark_scope_contracts.json",
                "build_command": "python scripts/build_public_benchmark_scope_contracts.py",
                "required_contracts": [
                    "public_pixel_world_benchmark",
                    "public_object_interaction_benchmark",
                ],
                "pass_condition": "scope contracts are ready; public pixel-world and object-interaction benchmark claims remain source gaps until executed results satisfying the contracts are imported",
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
                "boundary_command": "python scripts/build_vjepa2_ac_native_boundary.py",
                "run_command": "python scripts/build_vjepa2_ac_near_native_reproduction.py",
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
                "pass_condition": "near-native fixed-checkpoint record may be evaluated when fixed-checkpoint score, checkpoint identity, command, stream split, and BEDC readback metrics are recorded together; official native reproduction remains unevaluated until the official benchmark protocol is run",
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
            "quality_lab_export": {
                "readiness_gate": "quality_lab_export_registry",
                "target_artifact": "reports/bedc_jepa_quality_lab_exports.json",
                "build_command": "python scripts/build_bedc_jepa_quality_lab_export.py",
                "required_fields": [
                    "schema_id",
                    "generated_at",
                    "exports",
                ],
                "pass_condition": "target record compiles the BEDC-JEPA review bundle, readiness, manifest, and quality backend into a rollup-style quality-lab export registry",
            },
            "paper_writeback_packet": {
                "readiness_gate": "paper_writeback_packet",
                "target_artifact": "reports/bedc_jepa_paper_writeback_packet.json",
                "build_command": "python scripts/build_bedc_jepa_paper_writeback_packet.py",
                "required_fields": [
                    "schema_id",
                    "status",
                    "source_records",
                    "metrics",
                    "ledger_rows",
                    "not_claimed",
                    "record",
                    "fact_owner",
                ],
                "pass_condition": "target record projects the admitted paper-facing claims from the review bundle and quality-lab export without adding empirical claims",
            },
        },
        "readiness_command": "python scripts/build_bedc_jepa_readiness.py",
        "review_bundle_command": "python scripts/build_bedc_jepa_review_bundle.py",
        "quality_backend_candidate_command": "python scripts/build_bedc_jepa_quality_backend_candidate.py",
        "quality_lab_export_command": "python scripts/build_bedc_jepa_quality_lab_export.py",
        "paper_writeback_packet_command": "python scripts/build_bedc_jepa_paper_writeback_packet.py",
        "latent_claim_certificate_command": "python scripts/run_bedc_latent_claim_certificate.py",
        "torch_retraining_loss_ablation_command": "python scripts/run_torch_retraining_loss_ablation.py",
        "public_baseline_native_metric_contract_command": (
            "python scripts/build_public_baseline_native_metric_contract.py"
        ),
        "public_baseline_native_metric_template_command": (
            "python scripts/build_public_baseline_native_metric_template.py"
        ),
        "public_minigrid_calibration_extension_command": "python scripts/build_public_minigrid_calibration_extension.py",
        "public_benchmark_scope_contracts_command": "python scripts/build_public_benchmark_scope_contracts.py",
        "vjepa2_ac_minigrid_claim_certificate_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
        "vjepa2_ac_minigrid_latent_prediction_command": "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
        "vjepa2_ac_native_boundary_command": "python scripts/build_vjepa2_ac_native_boundary.py",
        "vjepa2_ac_near_native_reproduction_command": "python scripts/build_vjepa2_ac_near_native_reproduction.py",
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

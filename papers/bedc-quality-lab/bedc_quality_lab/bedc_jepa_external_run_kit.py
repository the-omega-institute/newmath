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
            "public_jepa_checkpoint_contact": {
                "readiness_gate": "public_jepa_checkpoint_contact",
                "target_artifact": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
                "run_command": "python scripts/run_public_jepa_ac_giant_adapter.py",
                "comparison_command": "python scripts/build_public_jepa_cuda_comparison.py",
                "pass_condition": "target artifact status is executed and AC Giant checkpoint_status is loaded under CUDA",
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
                "pass_condition": "target artifact status is available and sample_count_collected is positive",
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
                "pass_condition": "target artifact status is executed with S0/S1/S2/S3, baseline boundary, and nonzero planning high-gap reduction",
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
                "pass_condition": "target artifact status is executed; full S3, minus L_unlogged, and minus L_gap are retrained rows; unavailable stability or intervention surfaces are recorded as source debt",
            },
            "vjepa2_ac_minigrid_claim_certificate": {
                "readiness_gate": "vjepa2_ac_fixed_carrier_lccp",
                "target_artifact": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
                "run_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
                "required_predicates": [
                    "door_key_context_visible",
                    "unsafe_transition",
                    "has_key",
                    "door_open_or_unlocked",
                    "goal_reachable_with_current_state",
                ],
                "pass_condition": "target artifact records each predicate as certified, coverage debt, or source debt under the Latent Claim Certificate Protocol",
            },
            "vjepa2_ac_minigrid_latent_prediction": {
                "readiness_gate": "vjepa2_ac_minigrid_latent_prediction",
                "target_artifact": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
                "run_command": "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
                "required_fields": [
                    "candidate_id",
                    "environment_id",
                    "sample_counts",
                    "metrics",
                    "claim_scope",
                    "cannot_claim",
                ],
                "pass_condition": "target artifact status is executed and reports latent_prediction_score beside explicit cannot-claim rows",
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

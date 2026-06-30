#!/usr/bin/env python3
"""Build the machine-readable BEDC-JEPA artifact manifest."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def _load_summary() -> dict[str, object]:
    path = ROOT / "reports" / "bedc_jepa_four_system_experiment.json"
    return json.loads(path.read_text(encoding="utf-8"))


def _load_optional_json(name: str) -> dict[str, object] | None:
    path = ROOT / "reports" / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _system_delta(section: dict[str, object], key: str) -> float:
    systems = section["systems"]
    return float(systems["S3"][key]) - float(systems["S2"][key])


def build_manifest(summary: dict[str, object]) -> dict[str, object]:
    grid = summary["grid_transition"]
    minigrid = summary["minigrid_visual_planning"]
    object_sweep = summary["object_intervention_sweep"]
    multi_sweep = summary["multi_object_distractor_sweep"]
    cluttered = summary["cluttered_object_sweep"]
    torch_objective = _load_optional_json("bedc_jepa_torch_objective.json")
    torch_claims = {}
    if torch_objective is not None:
        torch_single = torch_objective.get("single", torch_objective)
        torch_sweep = torch_objective.get("sweep")
        torch_claims = {
            "torch_objective_gap_auc_gain": torch_single["deltas"]["gap_auc_gain"],
            "torch_objective_debt_reduction": torch_single["deltas"]["debt_reduction"],
            "torch_objective_unlogged_error": torch_single["systems"]["bedc_objective"][
                "unlogged_error_rate"
            ],
            "torch_objective_latent_r2_delta": torch_single["deltas"]["latent_r2_delta"],
        }
        if torch_sweep is not None:
            torch_claims.update(
                {
                    "torch_objective_seed_count": torch_sweep["seed_count"],
                    "torch_objective_gap_auc_gain_mean": torch_sweep["gap_auc_gain_mean"],
                    "torch_objective_gap_auc_win_rate": torch_sweep["gap_auc_win_rate"],
                    "torch_objective_debt_reduction_mean": torch_sweep["debt_reduction_mean"],
                    "torch_objective_debt_win_rate": torch_sweep["debt_win_rate"],
                    "torch_objective_unlogged_error_reduction_mean": torch_sweep[
                        "unlogged_error_reduction_mean"
                    ],
                    "torch_objective_latent_r2_delta_abs_max": torch_sweep[
                        "latent_r2_delta_abs_max"
                    ],
                }
            )
    return {
        "schema_id": "bedc-jepa-artifact-manifest",
        "artifact": "reports/bedc_jepa_four_system_experiment.json",
        "commands": {
            "generate": "python scripts/run_bedc_jepa_experiment.py",
            "torch_objective": "python scripts/run_torch_bedc_jepa.py",
            "torch_retraining_loss_ablation": "python scripts/run_torch_retraining_loss_ablation.py",
            "public_minigrid_probe": "python scripts/probe_public_minigrid.py",
            "public_minigrid_native_benchmark": "python scripts/run_public_minigrid_native_benchmark.py",
            "public_minigrid_native_seed_sweep": "python scripts/run_public_minigrid_native_seed_sweep.py",
            "public_minigrid_debt_closure": "python scripts/build_public_minigrid_debt_closure.py",
            "public_minigrid_calibration_extension": "python scripts/build_public_minigrid_calibration_extension.py",
            "public_benchmark_scope_contracts": "python scripts/build_public_benchmark_scope_contracts.py",
            "vjepa2_ac_native_boundary": "python scripts/build_vjepa2_ac_native_boundary.py",
            "vjepa2_ac_near_native_reproduction": "python scripts/build_vjepa2_ac_near_native_reproduction.py",
            "latent_claim_certificate": "python scripts/run_bedc_latent_claim_certificate.py",
            "vjepa2_ac_minigrid_claim_certificate": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
            "vjepa2_ac_minigrid_latent_prediction": "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
            "export_public_minigrid_benchmark_result": "python scripts/export_public_minigrid_benchmark_result.py",
            "import_public_minigrid_benchmark_metrics": "python scripts/import_public_minigrid_benchmark_metrics.py <minigrid-result.json>",
            "public_jepa_baseline_registry": "python scripts/build_public_jepa_baseline_registry.py",
            "public_baseline_native_metric_contract": (
                "python scripts/build_public_baseline_native_metric_contract.py"
            ),
            "public_baseline_native_metric_template": (
                "python scripts/build_public_baseline_native_metric_template.py"
            ),
            "probe_public_jepa_baseline": "python scripts/probe_public_jepa_baseline.py",
            "run_public_jepa_structure_adapter": "python scripts/run_public_jepa_structure_adapter.py",
            "build_public_jepa_adapter_comparison": "python scripts/build_public_jepa_adapter_comparison.py",
            "run_public_jepa_ac_giant_adapter": "python scripts/run_public_jepa_ac_giant_adapter.py",
            "build_public_jepa_cuda_comparison": "python scripts/build_public_jepa_cuda_comparison.py",
            "export_public_jepa_baseline_result": "python scripts/export_public_jepa_baseline_result.py",
            "import_public_jepa_baseline_metrics": "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
            "external_run_kit": "python scripts/build_bedc_jepa_external_run_kit.py",
            "review_bundle": "python scripts/build_bedc_jepa_review_bundle.py",
            "quality_backend_candidate": "python scripts/build_bedc_jepa_quality_backend_candidate.py",
            "quality_lab_export": "python scripts/build_bedc_jepa_quality_lab_export.py",
            "paper_writeback_packet": "python scripts/build_bedc_jepa_paper_writeback_packet.py",
            "readiness": "python scripts/build_bedc_jepa_readiness.py",
            "test": "python -m pytest -q",
            "paper": "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        },
        "evidence_ready_claims": {
            "four_system_ablation": sorted(summary["systems"].keys()),
            "grid_transition_one_step_r2": grid["transition"]["one_step_r2"],
            "minigrid_transition_one_step_accuracy": minigrid["transition"]["one_step_accuracy"],
            "minigrid_gap_auc_gain": _system_delta(minigrid, "gap_detection_auc"),
            "minigrid_risk_adjusted_planning_gain": minigrid["planning"][
                "vanilla_minus_gap_aware_risk_adjusted_cost"
            ],
            "object_intervention_counterfactual_accuracy_mean": object_sweep[
                "counterfactual_accuracy_mean"
            ],
            "multi_object_counterfactual_accuracy_mean": multi_sweep[
                "counterfactual_accuracy_mean"
            ],
            "cluttered_object_counterfactual_accuracy_mean": cluttered[
                "counterfactual_accuracy_mean"
            ],
            "cluttered_object_gap_auc_gain_mean": cluttered[
                "s3_minus_s2_gap_auc_mean"
            ],
            "cluttered_object_unlogged_error_reduction_mean": cluttered[
                "s2_minus_s3_unlogged_error_mean"
            ],
            **torch_claims,
        },
        "objective_artifacts": {
            "boundary_envelope": "reports/bedc_jepa_boundary_envelope.json",
            "torch": "reports/bedc_jepa_torch_objective.json",
            "torch_retraining_loss_ablation": "reports/bedc_jepa_retraining_loss_ablation.json",
        },
        "public_adapters": {
            "minigrid_benchmark_packet": "reports/bedc_jepa_public_minigrid_benchmark_packet.json",
            "minigrid_external_result": "reports/bedc_jepa_public_minigrid_external_result.json",
            "minigrid": "reports/bedc_jepa_public_minigrid_probe.json",
            "minigrid_native_benchmark": "reports/bedc_jepa_public_native_minigrid_benchmark.json",
            "minigrid_native_seed_sweep": "reports/bedc_jepa_public_native_minigrid_seed_sweep.json",
            "minigrid_public_debt_decomposition": "reports/bedc_jepa_public_debt_decomposition.json",
            "minigrid_certified_coverage_curve": "reports/bedc_jepa_certified_coverage_curve.json",
            "minigrid_risk_constrained_planning": "reports/bedc_jepa_risk_constrained_planning.json",
            "minigrid_public_debt_closure_report": "reports/bedc_jepa_public_debt_closure_report.md",
            "minigrid_conformal_certified_coverage": "reports/bedc_jepa_conformal_certified_coverage.json",
            "minigrid_risk_success_pareto": "reports/bedc_jepa_risk_success_pareto.json",
            "minigrid_calibration_extension": "reports/bedc_jepa_public_minigrid_calibration_extension.json",
            "minigrid_loss_ablation": "reports/bedc_jepa_loss_ablation.json",
            "minigrid_transition_packet": "reports/bedc_jepa_public_minigrid_transition_packet.json",
        },
        "readiness": "reports/bedc_jepa_readiness.json",
        "external_run_kit": "reports/bedc_jepa_external_run_kit.json",
        "review_bundle": "reports/bedc_jepa_review_bundle.json",
        "quality_backend_candidate": "reports/bedc_jepa_quality_backend_candidate.json",
        "quality_lab_export": "reports/bedc_jepa_quality_lab_exports.json",
        "paper_writeback_packet": "reports/bedc_jepa_paper_writeback_packet.json",
        "latent_claim_certificates": {
            "certificates": "reports/bedc_latent_claim_certificates.json",
            "conformal_gap_sweep": "reports/bedc_conformal_gap_sweep.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
            "vjepa2_ac_minigrid_claim_certificate": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
        },
        "public_baselines": {
            "public_benchmark_scope_contracts": "reports/bedc_jepa_public_benchmark_scope_contracts.json",
            "jepa_ac_native_boundary": "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
            "jepa_ac_near_native_reproduction": "reports/bedc_vjepa2_ac_native_reproduction.json",
            "jepa_ac_near_native_readback_comparison": "reports/bedc_vjepa2_ac_native_readback_comparison.json",
            "jepa_ac_giant_adapter": "reports/bedc_jepa_public_ac_giant_adapter.json",
            "jepa_ac_minigrid_latent_prediction": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
            "jepa_cuda_adapter_comparison": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
            "jepa_public_adapter_comparison": "reports/bedc_jepa_public_adapter_comparison.json",
            "jepa_public_pretrained_vitb_adapter": "reports/bedc_jepa_public_pretrained_vitb_adapter.json",
            "jepa_public_structure_adapter": "reports/bedc_jepa_public_structure_adapter.json",
            "jepa_comparison": "reports/bedc_jepa_public_baseline_comparison.json",
            "jepa_native_metric_contract": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
            "jepa_native_metric_template": "reports/bedc_jepa_public_baseline_native_metric_template.json",
            "jepa_external_result": "reports/bedc_jepa_public_baseline_external_result.json",
            "jepa_probe": "reports/bedc_jepa_public_baseline_probe.json",
            "jepa_registry": "reports/bedc_jepa_public_baseline_registry.json",
        },
        "cannot_claim": [
            "native public JEPA benchmark comparison",
            "public benchmark superiority",
            "robotics benchmark result",
            "natural-video object interaction",
            "general autonomous intelligence",
        ],
    }


def write_manifest() -> Path:
    manifest = build_manifest(_load_summary())
    path = ROOT / "reports" / "bedc_jepa_artifact_manifest.json"
    path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def main() -> None:
    path = write_manifest()
    print(f"wrote {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

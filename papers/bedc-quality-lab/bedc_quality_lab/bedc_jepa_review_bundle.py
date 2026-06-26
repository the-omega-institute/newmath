"""Clean review bundle contract for BEDC-JEPA evidence packets."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


def _load_json(name: str) -> dict[str, Any]:
    return json.loads((REPORTS / name).read_text(encoding="utf-8"))


def _load_optional_json(name: str) -> dict[str, Any] | None:
    path = REPORTS / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _git_head() -> str | None:
    try:
        completed = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT.parents[1],
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    return completed.stdout.strip()


def _check(condition: bool, name: str, failures: list[str]) -> None:
    if not condition:
        failures.append(name)


def build_review_bundle() -> dict[str, Any]:
    readiness = _load_json("bedc_jepa_readiness.json")
    boundary_envelope = _load_json("bedc_jepa_boundary_envelope.json")
    native = _load_json("bedc_jepa_public_native_minigrid_benchmark.json")
    sweep = _load_json("bedc_jepa_public_native_minigrid_seed_sweep.json")
    public_debt = _load_json("bedc_jepa_public_debt_decomposition.json")
    public_calibration_extension = _load_optional_json("bedc_jepa_public_minigrid_calibration_extension.json")
    conformal = _load_json("bedc_jepa_conformal_certified_coverage.json")
    ablation = _load_json("bedc_jepa_loss_ablation.json")
    retraining_ablation = _load_optional_json("bedc_jepa_retraining_loss_ablation.json")
    public_baseline_native_metric_contract = _load_optional_json(
        "bedc_jepa_public_baseline_native_metric_contract.json"
    )
    public_baseline_native_metric_template = _load_optional_json(
        "bedc_jepa_public_baseline_native_metric_template.json"
    )
    public_benchmark_scope_contracts = _load_optional_json("bedc_jepa_public_benchmark_scope_contracts.json")
    quality_lab_export = _load_optional_json("bedc_jepa_quality_lab_exports.json")
    paper_writeback_packet = _load_optional_json("bedc_jepa_paper_writeback_packet.json")
    vjepa_lccp = _load_optional_json("bedc_vjepa2_ac_minigrid_claim_certificate.json")
    vjepa_latent_prediction = _load_optional_json("bedc_vjepa2_ac_minigrid_latent_prediction.json")
    vjepa_near_native = _load_optional_json("bedc_vjepa2_ac_native_reproduction.json")
    vjepa_readback_comparison = _load_optional_json("bedc_vjepa2_ac_native_readback_comparison.json")
    public_adapter_comparison = _load_optional_json("bedc_jepa_public_adapter_comparison.json")
    public_structure_adapter = _load_optional_json("bedc_jepa_public_structure_adapter.json")
    public_pretrained_vitb_adapter = _load_optional_json("bedc_jepa_public_pretrained_vitb_adapter.json")
    cuda = _load_json("bedc_jepa_public_cuda_adapter_comparison.json")
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    failures: list[str] = []
    _check(
        readiness["evidence_boundary"]["checkpoint_evaluation"] == "closed",
        "checkpoint evaluation boundary",
        failures,
    )
    _check(readiness["evidence_boundary"]["native_public_benchmark"] == "closed", "native public benchmark boundary", failures)
    _check(
        boundary_envelope.get("schema_id") == "bedc-quality-lab:evidence-envelope",
        "boundary envelope schema",
        failures,
    )
    _check(native.get("status") == "executed", "native MiniGrid benchmark executed", failures)
    _check(set(native.get("systems", {})) == {"S0", "S1", "S2", "S3"}, "native MiniGrid S0/S1/S2/S3 systems", failures)
    _check(float(native["deltas"]["s0_minus_s3_unlogged_error"]) > 0.05, "native MiniGrid UER reduction", failures)
    _check(float(native["deltas"]["lambda_0_minus_best_high_gap_rate"]) > 0.05, "native MiniGrid planning high-gap reduction", failures)
    _check(public_debt.get("status") == "executed", "public MiniGrid debt decomposition executed", failures)
    _check(
        public_debt["interpretation"]["diagnosis"] == "silent debt falls while coverage debt rises",
        "public MiniGrid debt diagnosis",
        failures,
    )
    _check(conformal.get("status") == "executed", "public MiniGrid conformal certified coverage executed", failures)
    if public_calibration_extension is not None:
        _check(
            public_calibration_extension.get("schema_id")
            == "bedc-jepa-public-minigrid-calibration-extension",
            "public MiniGrid calibration extension schema",
            failures,
        )
        _check(
            public_calibration_extension.get("status") == "executed",
            "public MiniGrid calibration extension executed",
            failures,
        )
        _check(
            float(public_calibration_extension.get("summary", {}).get("executed_row_count", 0.0)) >= 1.0,
            "public MiniGrid calibration extension executed rows",
            failures,
        )
    _check(ablation.get("status") == "executed", "public MiniGrid local ablation executed", failures)
    retraining_executed = retraining_ablation is not None and retraining_ablation.get("status") == "executed"
    if retraining_executed:
        _check(
            retraining_ablation.get("schema_id") == "bedc-jepa-retraining-loss-ablation",
            "torch retraining ablation schema",
            failures,
        )
    if public_baseline_native_metric_contract is not None:
        _check(
            public_baseline_native_metric_contract.get("schema_id")
            == "bedc-jepa-public-baseline-native-metric-contract",
            "public baseline native metric contract schema",
            failures,
        )
        _check(
            public_baseline_native_metric_contract.get("status") == "contract_ready",
            "public baseline native metric contract ready",
            failures,
        )
        _check(
            "repository_commit"
            in public_baseline_native_metric_contract.get("required_execution_fields", []),
            "public baseline native metric contract repository commit",
            failures,
        )
        _check(
            "execution_command"
            in public_baseline_native_metric_contract.get("required_execution_fields", []),
            "public baseline native metric contract execution command",
            failures,
        )
    if public_baseline_native_metric_template is not None:
        _check(
            public_baseline_native_metric_template.get("schema_id")
            == "bedc-jepa-public-baseline-native-metric-template",
            "public baseline native metric template schema",
            failures,
        )
    if public_benchmark_scope_contracts is not None:
        _check(
            public_benchmark_scope_contracts.get("schema_id")
            == "bedc-jepa-public-benchmark-scope-contracts",
            "public benchmark scope contract schema",
            failures,
        )
        _check(
            public_benchmark_scope_contracts.get("status") == "contract_ready",
            "public benchmark scope contract ready",
            failures,
        )
        contract_ids = {
            str(row.get("contract_id"))
            for row in public_benchmark_scope_contracts.get("contracts", [])
            if isinstance(row, dict)
        }
        _check(
            {"public_pixel_world_benchmark", "public_object_interaction_benchmark"} <= contract_ids,
            "public benchmark scope contract ids",
            failures,
        )
        _check(
            public_baseline_native_metric_template.get("template_for")
            == "reports/bedc_jepa_public_baseline_native_metric_contract.json",
            "public baseline native metric template target",
            failures,
        )
        _check(
            "official V-JEPA2-AC benchmark reproduction"
            in public_baseline_native_metric_template.get("cannot_claim", []),
            "public baseline native metric template claim boundary",
            failures,
        )
    if quality_lab_export is not None:
        _check(
            quality_lab_export.get("schema_id") == "bedc-jepa:quality-lab-exports",
            "BEDC-JEPA quality-lab export schema",
            failures,
        )
        _check(
            len(quality_lab_export.get("exports", [])) >= 1,
            "BEDC-JEPA quality-lab export row",
            failures,
        )
    if paper_writeback_packet is not None:
        _check(
            paper_writeback_packet.get("schema_id") == "bedc-jepa-paper-writeback-packet",
            "BEDC-JEPA paper writeback packet schema",
            failures,
        )
        _check(
            paper_writeback_packet.get("status") in {"paper_ready", "partial"},
            "BEDC-JEPA paper writeback packet status",
            failures,
        )
        _check(
            paper_writeback_packet.get("record", {}).get("admitted_operational_name")
            == "door_key_context_visible",
            "BEDC-JEPA paper writeback admitted name",
            failures,
        )
    if vjepa_lccp is not None:
        _check(
            vjepa_lccp.get("schema_id") == "bedc-vjepa2-ac-minigrid-claim-certificate",
            "V-JEPA2-AC MiniGrid LCCP schema",
            failures,
        )
    if vjepa_latent_prediction is not None:
        _check(
            vjepa_latent_prediction.get("schema_id") == "bedc-vjepa2-ac-minigrid-latent-prediction",
            "V-JEPA2-AC MiniGrid latent-prediction schema",
            failures,
        )
        _check(
            vjepa_latent_prediction.get("status") == "executed",
            "V-JEPA2-AC MiniGrid latent-prediction evaluated",
            failures,
        )
        _check(
            "official V-JEPA2-AC benchmark reproduction" in vjepa_latent_prediction.get("cannot_claim", []),
            "V-JEPA2-AC MiniGrid latent-prediction claim boundary",
            failures,
        )
        _check(
            vjepa_lccp.get("status") in {"executed", "source_gap"},
            "V-JEPA2-AC MiniGrid LCCP fail-closed status",
            failures,
        )
        _check(
            len(vjepa_lccp.get("claims", [])) >= 1,
            "V-JEPA2-AC MiniGrid LCCP claim rows",
            failures,
        )
        _check(retraining_ablation.get("status") == "executed", "torch retraining ablation executed", failures)
        _check(
            set(retraining_ablation.get("systems", {}))
            == {"full_s3", "minus_l_unlogged", "minus_l_gap", "minus_l_stab", "minus_l_intervention"},
            "torch retraining ablation systems",
            failures,
        )
    if vjepa_near_native is not None:
        _check(
            vjepa_near_native.get("schema_id") == "bedc-vjepa2-ac-near-native-minigrid-reproduction",
            "V-JEPA2-AC near-native MiniGrid schema",
            failures,
        )
        _check(
            vjepa_near_native.get("status") == "evaluated_near_native",
            "V-JEPA2-AC near-native MiniGrid evaluated",
            failures,
        )
        _check(
            vjepa_near_native.get("official_native_reproduction_status") == "not_evaluated",
            "V-JEPA2-AC official benchmark boundary",
            failures,
        )
        _check(
            "official V-JEPA2-AC benchmark reproduction"
            in vjepa_near_native.get("cannot_claim_boundary", []),
            "V-JEPA2-AC near-native cannot-claim boundary",
            failures,
        )
    if vjepa_readback_comparison is not None:
        _check(
            vjepa_readback_comparison.get("schema_id") == "bedc-vjepa2-ac-native-readback-comparison",
            "V-JEPA2-AC readback comparison schema",
            failures,
        )
    _check(sweep.get("status") == "executed", "native MiniGrid seed sweep executed", failures)
    _check(float(sweep.get("seed_count_executed", 0.0)) >= 5.0, "native MiniGrid seed sweep count", failures)
    _check(float(sweep["summary"]["unlogged_error_win_rate"]) >= 0.6, "seed sweep UER win rate", failures)
    _check(cuda.get("status") == "executed", "CUDA checkpoint-scope comparison", failures)
    _check(cuda["public_adapters"]["ac_giant"]["model"]["checkpoint_status"] == "loaded", "AC Giant checkpoint loaded", failures)
    if public_adapter_comparison is not None:
        _check(
            public_adapter_comparison.get("schema_id") == "bedc-jepa-public-adapter-comparison",
            "public adapter comparison schema",
            failures,
        )
        _check(public_adapter_comparison.get("status") == "executed", "public adapter comparison executed", failures)
    if public_structure_adapter is not None:
        _check(
            public_structure_adapter.get("schema_id") == "bedc-jepa-public-structure-adapter",
            "public structure adapter schema",
            failures,
        )
        _check(public_structure_adapter.get("status") == "available", "public structure adapter available", failures)
    if public_pretrained_vitb_adapter is not None:
        _check(
            public_pretrained_vitb_adapter.get("schema_id") == "bedc-jepa-public-structure-adapter",
            "public pretrained adapter schema",
            failures,
        )
        _check(
            public_pretrained_vitb_adapter.get("status") == "available",
            "public pretrained adapter available",
            failures,
        )
    _check(manifest.get("schema_id") == "bedc-jepa-artifact-manifest", "artifact manifest schema", failures)
    status = "review_ready" if not failures else "incomplete"
    source_commit = _git_head()
    return {
        "schema_id": "bedc-jepa-review-bundle",
        "status": status,
        "source_commit_at_build": source_commit,
        "source_commit_observed_at_build": source_commit,
        "source_commit_semantics": (
            "commit observed by the review-bundle builder before the generated bundle is committed; "
            "not a self-referential assertion about the commit that contains this JSON file"
        ),
        "required_artifacts": {
            "readiness": "reports/bedc_jepa_readiness.json",
            "boundary_envelope": "reports/bedc_jepa_boundary_envelope.json",
            "native_minigrid": "reports/bedc_jepa_public_native_minigrid_benchmark.json",
            "native_minigrid_seed_sweep": "reports/bedc_jepa_public_native_minigrid_seed_sweep.json",
            "public_debt_decomposition": "reports/bedc_jepa_public_debt_decomposition.json",
            "certified_coverage_curve": "reports/bedc_jepa_certified_coverage_curve.json",
            "risk_constrained_planning": "reports/bedc_jepa_risk_constrained_planning.json",
            "public_debt_closure_report": "reports/bedc_jepa_public_debt_closure_report.md",
            "conformal_certified_coverage": "reports/bedc_jepa_conformal_certified_coverage.json",
            "risk_success_pareto": "reports/bedc_jepa_risk_success_pareto.json",
            "public_minigrid_calibration_extension": (
                "reports/bedc_jepa_public_minigrid_calibration_extension.json"
            ),
            "loss_ablation": "reports/bedc_jepa_loss_ablation.json",
            "retraining_loss_ablation": "reports/bedc_jepa_retraining_loss_ablation.json",
            "public_baseline_native_metric_contract": (
                "reports/bedc_jepa_public_baseline_native_metric_contract.json"
            ),
            "public_baseline_native_metric_template": (
                "reports/bedc_jepa_public_baseline_native_metric_template.json"
            ),
            "public_benchmark_scope_contracts": "reports/bedc_jepa_public_benchmark_scope_contracts.json",
            "public_adapter_comparison": "reports/bedc_jepa_public_adapter_comparison.json",
            "public_structure_adapter": "reports/bedc_jepa_public_structure_adapter.json",
            "public_pretrained_vitb_adapter": "reports/bedc_jepa_public_pretrained_vitb_adapter.json",
            "cuda_adapter_comparison": "reports/bedc_jepa_public_cuda_adapter_comparison.json",
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "quality_backend_candidate": "reports/bedc_jepa_quality_backend_candidate.json",
            "quality_lab_export": "reports/bedc_jepa_quality_lab_exports.json",
            "paper_writeback_packet": "reports/bedc_jepa_paper_writeback_packet.json",
            "latent_claim_certificates": "reports/bedc_latent_claim_certificates.json",
            "conformal_gap_sweep": "reports/bedc_conformal_gap_sweep.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
            "vjepa2_ac_minigrid_claim_certificate": "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json",
            "vjepa2_ac_minigrid_latent_prediction": "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json",
            "vjepa2_ac_near_native_reproduction": "reports/bedc_vjepa2_ac_native_reproduction.json",
            "vjepa2_ac_native_readback_comparison": "reports/bedc_vjepa2_ac_native_readback_comparison.json",
        },
        "reproduction_commands": [
            "python scripts/run_public_minigrid_native_benchmark.py",
            "python scripts/run_public_minigrid_native_seed_sweep.py",
            "python scripts/build_public_minigrid_debt_closure.py",
            "python scripts/build_public_minigrid_calibration_extension.py",
            "python scripts/run_torch_retraining_loss_ablation.py",
            "python scripts/build_public_baseline_native_metric_contract.py",
            "python scripts/build_public_baseline_native_metric_template.py",
            "python scripts/build_public_benchmark_scope_contracts.py",
            "python scripts/run_public_jepa_structure_adapter.py",
            "python scripts/build_public_jepa_adapter_comparison.py",
            "python scripts/build_public_jepa_cuda_comparison.py",
            "python scripts/build_bedc_jepa_artifact_manifest.py",
            "python scripts/build_bedc_jepa_readiness.py",
            "python scripts/build_bedc_jepa_review_bundle.py",
            "python scripts/build_bedc_jepa_quality_backend_candidate.py",
            "python scripts/build_bedc_jepa_quality_lab_export.py",
            "python scripts/build_bedc_jepa_paper_writeback_packet.py",
            "python scripts/run_bedc_latent_claim_certificate.py",
            "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
            "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py",
            "python scripts/build_vjepa2_ac_near_native_reproduction.py",
            "python -m pytest -q tests/test_public_jepa_baselines.py tests/test_public_minigrid_native_benchmark.py tests/test_bedc_jepa_readiness.py tests/test_bedc_jepa_external_run_kit.py tests/test_bedc_jepa_artifact_manifest.py tests/test_bedc_jepa_review_bundle.py tests/test_bedc_jepa_quality_backend.py tests/test_latent_claim_certificate.py",
            "pdflatex -interaction=nonstopmode -halt-on-error main.tex",
        ],
        "checks": {
            "checkpoint_evaluation": readiness["evidence_boundary"]["checkpoint_evaluation"],
            "native_public_benchmark": readiness["evidence_boundary"]["native_public_benchmark"],
            "native_unlogged_error_reduction": native["deltas"]["s0_minus_s3_unlogged_error"],
            "native_planning_high_gap_reduction": native["deltas"]["lambda_0_minus_best_high_gap_rate"],
            "public_debt_diagnosis": public_debt["interpretation"]["diagnosis"],
            "public_silent_debt_reduction": public_debt["interpretation"]["changes"][
                "silent_debt_change_s0_minus_s3"
            ],
            "public_coverage_debt_change": public_debt["interpretation"]["changes"][
                "coverage_debt_change_s0_minus_s3"
            ],
            "public_conformal_predicate_count": float(
                len(conformal["conformal_certified_coverage"]["predicates"])
            ),
            "public_minigrid_calibration_extension_status": (
                public_calibration_extension.get("status")
                if public_calibration_extension is not None
                else "not recorded"
            ),
            "public_minigrid_calibration_extension_executed_rows": (
                float(public_calibration_extension.get("summary", {}).get("executed_row_count", 0.0))
                if public_calibration_extension is not None
                else 0.0
            ),
            "public_minigrid_calibration_extension_silent_win_rate": (
                float(public_calibration_extension.get("summary", {}).get("silent_debt_direction_win_rate", 0.0))
                if public_calibration_extension is not None
                else 0.0
            ),
            "public_minigrid_calibration_extension_risk_win_rate": (
                float(public_calibration_extension.get("summary", {}).get("risk_reduction_win_rate", 0.0))
                if public_calibration_extension is not None
                else 0.0
            ),
            "public_ablation_unlogged_penalty_effect": ablation["loss_ablation"]["mechanism_readout"][
                "unlogged_penalty_effect"
            ],
            "retraining_ablation_status": (
                retraining_ablation.get("status") if retraining_ablation is not None else "not recorded"
            ),
            "retraining_ablation_system_count": (
                float(len(retraining_ablation.get("systems", {}))) if retraining_executed else 0.0
            ),
            "public_baseline_native_metric_contract_status": (
                public_baseline_native_metric_contract.get("status")
                if public_baseline_native_metric_contract is not None
                else "not recorded"
            ),
            "public_baseline_native_metric_required_field_count": (
                float(len(public_baseline_native_metric_contract.get("required_execution_fields", [])))
                if public_baseline_native_metric_contract is not None
                else 0.0
            ),
            "public_baseline_native_metric_template_status": (
                "recorded" if public_baseline_native_metric_template is not None else "not recorded"
            ),
            "public_benchmark_scope_contract_status": (
                public_benchmark_scope_contracts.get("status")
                if public_benchmark_scope_contracts is not None
                else "not recorded"
            ),
            "public_benchmark_scope_contract_count": (
                float(len(public_benchmark_scope_contracts.get("contracts", [])))
                if public_benchmark_scope_contracts is not None
                else 0.0
            ),
            "public_adapter_comparison_status": (
                public_adapter_comparison.get("status") if public_adapter_comparison is not None else "not recorded"
            ),
            "public_structure_adapter_status": (
                public_structure_adapter.get("status") if public_structure_adapter is not None else "not recorded"
            ),
            "public_pretrained_vitb_adapter_status": (
                public_pretrained_vitb_adapter.get("status")
                if public_pretrained_vitb_adapter is not None
                else "not recorded"
            ),
            "quality_lab_export_status": "recorded" if quality_lab_export is not None else "not recorded",
            "quality_lab_export_count": (
                float(len(quality_lab_export.get("exports", []))) if quality_lab_export is not None else 0.0
            ),
            "paper_writeback_packet_status": (
                paper_writeback_packet.get("status") if paper_writeback_packet is not None else "not recorded"
            ),
            "paper_writeback_admitted_name": (
                paper_writeback_packet.get("record", {}).get("admitted_operational_name")
                if paper_writeback_packet is not None
                else "not recorded"
            ),
            "vjepa2_ac_lccp_status": vjepa_lccp.get("status") if vjepa_lccp is not None else "not recorded",
            "vjepa2_ac_lccp_claim_count": float(len(vjepa_lccp.get("claims", []))) if vjepa_lccp is not None else 0.0,
            "vjepa2_ac_latent_prediction_status": (
                vjepa_latent_prediction.get("status") if vjepa_latent_prediction is not None else "not recorded"
            ),
            "vjepa2_ac_latent_prediction_score": (
                float(vjepa_latent_prediction.get("metrics", {}).get("latent_prediction_score", 0.0))
                if vjepa_latent_prediction is not None
                else 0.0
            ),
            "vjepa2_ac_near_native_status": (
                vjepa_near_native.get("status") if vjepa_near_native is not None else "not recorded"
            ),
            "vjepa2_ac_official_native_reproduction_status": (
                vjepa_near_native.get("official_native_reproduction_status")
                if vjepa_near_native is not None
                else "not recorded"
            ),
            "vjepa2_ac_near_native_latent_prediction_score": (
                float(vjepa_near_native.get("latent_prediction_score", 0.0))
                if vjepa_near_native is not None
                else 0.0
            ),
            "vjepa2_ac_near_native_gap_claim_count": (
                float(vjepa_near_native.get("bedc_readback_metrics", {}).get("gap_claim_count", 0.0))
                if vjepa_near_native is not None
                else 0.0
            ),
            "seed_sweep_count": sweep.get("seed_count_executed", 0.0),
            "seed_sweep_unlogged_error_win_rate": sweep["summary"].get("unlogged_error_win_rate") if sweep.get("summary") else None,
            "ac_giant_checkpoint_status": cuda["public_adapters"]["ac_giant"]["model"]["checkpoint_status"],
        },
        "remaining_evidence_contracts": readiness.get("remaining_evidence_contracts", {}),
        "failures": failures,
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC checkpoint reproduction",
            "robotics benchmark result",
            "large-scale real-world conclusion",
            "formal neural-network proof",
        ],
    }


def write_review_bundle(path: str | Path) -> dict[str, Any]:
    bundle = build_review_bundle()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(bundle, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return bundle

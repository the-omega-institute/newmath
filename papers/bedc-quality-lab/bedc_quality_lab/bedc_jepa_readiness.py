"""Machine-readable readiness record for BEDC-JEPA evidence."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


def _load_optional_json(name: str) -> dict[str, Any] | None:
    path = REPORTS / name
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _dependency_present(name: str) -> bool:
    return importlib.util.find_spec(name) is not None


def _gate(status: str, evidence: str, requirement: str) -> dict[str, str]:
    return {
        "status": status,
        "evidence": evidence,
        "requirement": requirement,
    }


def _torch_objective_gate(torch_objective: dict[str, Any] | None) -> dict[str, str]:
    if torch_objective is None or "sweep" not in torch_objective:
        return _gate("missing", "reports/bedc_jepa_torch_objective.json", "three-seed torch objective sweep")
    sweep = torch_objective["sweep"]
    passes = (
        float(sweep["gap_auc_gain_mean"]) > 0.20
        and float(sweep["debt_reduction_mean"]) > 0.05
        and float(sweep["latent_r2_delta_abs_max"]) < 1e-8
        and float(sweep["gap_auc_win_rate"]) >= 0.75
    )
    return _gate(
        "pass" if passes else "missing",
        "reports/bedc_jepa_torch_objective.json",
        "stable BEDC objective gain without latent R2 change",
    )


def _local_visual_gate(summary: dict[str, Any] | None) -> dict[str, str]:
    if summary is None:
        return _gate("missing", "reports/bedc_jepa_four_system_experiment.json", "local visual planning benchmark")
    planning = summary["minigrid_visual_planning"]["planning"]
    gain = float(planning["vanilla_minus_gap_aware_risk_adjusted_cost"])
    transition = float(summary["minigrid_visual_planning"]["transition"]["one_step_accuracy"])
    return _gate(
        "pass" if gain > 0.0 and transition > 0.94 else "missing",
        "reports/bedc_jepa_four_system_experiment.json",
        "local visual planning with learned transition and risk-adjusted gain",
    )


def _clutter_gate(summary: dict[str, Any] | None) -> dict[str, str]:
    if summary is None:
        return _gate("missing", "reports/bedc_jepa_four_system_experiment.json", "object counterfactual clutter sweep")
    clutter = summary["cluttered_object_sweep"]
    passes = (
        float(clutter["counterfactual_accuracy_mean"]) > 0.86
        and float(clutter["s3_minus_s2_gap_auc_mean"]) > 0.40
        and float(clutter["s2_minus_s3_unlogged_error_mean"]) > 0.20
    )
    return _gate(
        "pass" if passes else "missing",
        "reports/bedc_jepa_four_system_experiment.json",
        "object-level counterfactual readback under clutter",
    )


def _public_minigrid_gate(benchmark_packet: dict[str, Any] | None) -> dict[str, str]:
    if benchmark_packet is None:
        return _gate("missing", "reports/bedc_jepa_public_minigrid_benchmark_packet.json", "executed public MiniGrid benchmark")
    executed = benchmark_packet.get("status") == "available" and float(benchmark_packet["sample_count_collected"]) > 0.0
    dependency_status = benchmark_packet.get("dependency_status", {})
    external_executed = (
        dependency_status.get("gymnasium") == "external-executed"
        and dependency_status.get("minigrid") == "external-executed"
    )
    deps = external_executed or (_dependency_present("gymnasium") and _dependency_present("minigrid"))
    return _gate(
        "pass" if executed and deps else "missing",
        "reports/bedc_jepa_public_minigrid_benchmark_packet.json",
        "executed public MiniGrid DoorKey readback/gap benchmark",
    )


def _native_public_benchmark_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_public_native_minigrid_benchmark.json"
    if packet is None:
        return _gate("missing", evidence, "native public MiniGrid S0/S1/S2/S3 benchmark")
    systems = packet.get("systems", {})
    deltas = packet.get("deltas", {})
    baseline = packet.get("jepa_family_baseline_boundary", {})
    passes = (
        packet.get("status") == "executed"
        and set(systems) == {"S0", "S1", "S2", "S3"}
        and baseline.get("status") == "executed"
        and float(packet.get("sample_count_collected", 0.0)) >= 128.0
        and float(packet.get("planning_state_count_collected", 0.0)) >= 16.0
        and len(packet.get("planning_lambda_sweep", [])) >= 5
        and float(deltas.get("s0_minus_s3_unlogged_error", 0.0)) > 0.05
        and float(deltas.get("s0_minus_s3_debt", 0.0)) > 0.0
        and float(deltas.get("s3_minus_s0_gap_auc", 0.0)) > 0.05
        and float(deltas.get("lambda_0_minus_best_high_gap_rate", 0.0)) > 0.05
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "native public MiniGrid S0/S1/S2/S3 benchmark",
    )


def _public_jepa_gate(comparison: dict[str, Any] | None) -> dict[str, str]:
    evidence = (
        "reports/bedc_jepa_public_baseline_comparison.json"
        if comparison is not None
        else "no public JEPA baseline comparison record observed"
    )
    if comparison is not None and comparison.get("status") == "executed":
        return _gate(
            "pass",
            evidence,
            "public JEPA or JEPA-style baseline comparison",
        )
    return _gate(
        "missing",
        evidence,
        "public JEPA or JEPA-style baseline comparison",
    )


def _public_checkpoint_evaluation_gate(cuda_comparison: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_public_cuda_adapter_comparison.json"
    if cuda_comparison is None:
        return _gate(
            "missing",
            evidence,
            "public V-JEPA2-AC Giant CUDA checkpoint-scope adapter",
        )
    adapter = cuda_comparison.get("public_adapters", {}).get("ac_giant", {})
    model = adapter.get("model", {})
    cuda = adapter.get("cuda_environment", {})
    loaded = (
        cuda_comparison.get("status") == "executed"
        and adapter.get("status") == "available"
        and model.get("checkpoint_status") == "loaded"
        and cuda.get("cuda_available") is True
    )
    return _gate(
        "pass" if loaded else "missing",
        evidence,
        "public V-JEPA2-AC Giant CUDA checkpoint-scope adapter",
    )


def _vjepa2_latent_prediction_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    if packet is None:
        return _gate("missing", evidence, "V-JEPA2-AC MiniGrid fixed-checkpoint latent-prediction study")
    metrics = packet.get("metrics", {})
    passes = (
        packet.get("status") == "executed"
        and packet.get("candidate_id") == "vjepa2-ac-vit-giant"
        and float(packet.get("sample_counts", {}).get("test", 0.0)) > 0.0
        and float(metrics.get("latent_prediction_score", 0.0)) > 0.0
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "V-JEPA2-AC MiniGrid fixed-checkpoint latent-prediction study",
    )


def _vjepa2_near_native_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_vjepa2_ac_native_reproduction.json"
    if packet is None:
        return _gate("missing", evidence, "V-JEPA2-AC MiniGrid near-native fixed-checkpoint record")
    passes = (
        packet.get("schema_id") == "bedc-vjepa2-ac-near-native-minigrid-reproduction"
        and packet.get("status") == "evaluated_near_native"
        and packet.get("official_native_reproduction_status") == "not_evaluated"
        and float(packet.get("latent_prediction_score", 0.0)) > 0.0
        and bool(packet.get("bedc_readback_metrics"))
        and "official V-JEPA2-AC benchmark reproduction" in packet.get("cannot_claim_boundary", [])
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "V-JEPA2-AC MiniGrid near-native fixed-checkpoint record with official reproduction boundary",
    )


def _public_minigrid_calibration_pareto_gate(
    debt: dict[str, Any] | None,
    conformal: dict[str, Any] | None,
    pareto: dict[str, Any] | None,
) -> dict[str, str]:
    evidence = (
        "reports/bedc_jepa_public_debt_decomposition.json; "
        "reports/bedc_jepa_conformal_certified_coverage.json; "
        "reports/bedc_jepa_risk_success_pareto.json"
    )
    if debt is None or conformal is None or pareto is None:
        return _gate("missing", evidence, "public MiniGrid calibration and risk-success Pareto records")
    conformal_packet = conformal.get("conformal_certified_coverage", {})
    pareto_packet = pareto.get("risk_success_pareto", {})
    predicates = conformal_packet.get("predicates", {})
    frontier_rows = pareto_packet.get("frontier_rows", [])
    passes = (
        debt.get("status") == "executed"
        and conformal.get("status") == "executed"
        and pareto.get("status") == "executed"
        and debt.get("interpretation", {}).get("diagnosis") == "silent debt falls while coverage debt rises"
        and len(conformal_packet.get("alphas", [])) >= 5
        and len(predicates) >= 5
        and len(frontier_rows) >= 5
        and bool(pareto_packet.get("claim_rule"))
        and all("claim_status" in row for row in frontier_rows)
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "public MiniGrid threshold, conformal, debt-decomposition, and risk-success Pareto records",
    )


def _public_minigrid_calibration_extension_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_public_minigrid_calibration_extension.json"
    if packet is None:
        return _gate("missing", evidence, "public MiniGrid seed, planning-budget, and task-variant calibration extension")
    summary = packet.get("summary", {})
    passes = (
        packet.get("schema_id") == "bedc-jepa-public-minigrid-calibration-extension"
        and packet.get("status") == "executed"
        and float(summary.get("executed_row_count", 0.0)) >= 30.0
        and len(packet.get("seeds", [])) >= 5
        and len(packet.get("planning_state_counts", [])) >= 3
        and len(packet.get("task_variants", [])) >= 3
        and float(summary.get("task_family_count", 0.0)) >= 2.0
        and "public benchmark superiority" in packet.get("cannot_claim", [])
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "public MiniGrid seed, planning-budget, and task-variant calibration extension",
    )


def _public_baseline_native_metric_contract_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_public_baseline_native_metric_contract.json"
    if packet is None:
        return _gate("missing", evidence, "public baseline native metric contract")
    required_fields = set(packet.get("required_execution_fields", []))
    contract = packet.get("native_metric_contract", {})
    passes = (
        packet.get("schema_id") == "bedc-jepa-public-baseline-native-metric-contract"
        and packet.get("status") == "contract_ready"
        and packet.get("selected_candidate_id") == "vjepa2-ac"
        and {
            "repository_commit",
            "checkpoint_identity",
            "dataset_identity",
            "execution_command",
            "native_metric_contract",
            "bedc_readback_metrics",
            "lccp_certificate_metrics",
        }
        <= required_fields
        and "same public observation/action stream" in contract.get("same_protocol_requirements", [])
        and "official V-JEPA2-AC benchmark reproduction" in packet.get("cannot_claim", [])
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "public baseline native metric contract",
    )


def _public_baseline_native_metric_template_gate(packet: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_public_baseline_native_metric_template.json"
    if packet is None:
        return _gate("missing", evidence, "public baseline native metric template")
    result = packet.get("result", {})
    passes = (
        packet.get("schema_id") == "bedc-jepa-public-baseline-native-metric-template"
        and packet.get("template_for") == "reports/bedc_jepa_public_baseline_native_metric_contract.json"
        and packet.get("candidate_id") == "vjepa2-ac"
        and isinstance(result, dict)
        and "latent_prediction_score" in result
        and "rollout_or_planning_score" in result
        and "official V-JEPA2-AC benchmark reproduction" in packet.get("cannot_claim", [])
    )
    return _gate(
        "pass" if passes else "missing",
        evidence,
        "public baseline native metric template",
    )


def _artifact_review_bundle_gate(run_kit: dict[str, Any] | None) -> dict[str, str]:
    evidence = "reports/bedc_jepa_review_bundle.json"
    if run_kit is not None and run_kit.get("status") == "review_ready":
        return _gate("pass", evidence, "clean external review artifact bundle")
    return _gate("missing", evidence, "clean external review artifact bundle")


def _remaining_evidence_contracts(
    retraining_ablation: dict[str, Any] | None,
    native_boundary: dict[str, Any] | None,
    near_native_reproduction: dict[str, Any] | None,
    native_metric_contract: dict[str, Any] | None,
    native_metric_template: dict[str, Any] | None,
) -> dict[str, Any]:
    retraining_contract: dict[str, Any] = {
        "status": "missing",
        "evidence": "reports/bedc_jepa_retraining_loss_ablation.json",
        "required_record": "true retraining loss-term ablation for every declared loss removal row",
    }
    if retraining_ablation is not None:
        systems = retraining_ablation.get("systems", {})
        executed = sorted(name for name, row in systems.items() if row.get("status") == "executed")
        source_debt = sorted(name for name, row in systems.items() if row.get("status") == "source_debt")
        retraining_contract = {
            "status": "source_surfaces_required" if source_debt else "closed",
            "evidence": "reports/bedc_jepa_retraining_loss_ablation.json",
            "executed_rows": executed,
            "source_debt_rows": source_debt,
            "source_debt_contract": retraining_ablation.get("source_debt_contract", {}),
            "supervision_surface_contract": retraining_ablation.get("supervision_surface_contract", {}),
            "required_record": "true retraining loss-term ablation for every declared loss removal row",
        }

    native_contract: dict[str, Any] = {
        "status": "missing",
        "evidence": "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
        "required_record": "official or near-native V-JEPA2-AC rollout reproduction with BEDC readback metrics",
    }
    if native_boundary is not None:
        native_contract = {
            "status": native_boundary.get("native_reproduction_status", native_boundary.get("status")),
            "evidence": "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
            "native_acceptance_contract": native_boundary.get("native_acceptance_contract", {}),
            "native_metric_contract_status": (
                native_metric_contract.get("status") if native_metric_contract is not None else "missing"
            ),
            "native_metric_contract": "reports/bedc_jepa_public_baseline_native_metric_contract.json",
            "native_metric_template_status": (
                "recorded" if native_metric_template is not None else "missing"
            ),
            "native_metric_template": "reports/bedc_jepa_public_baseline_native_metric_template.json",
            "near_native_record_status": (
                near_native_reproduction.get("status") if near_native_reproduction is not None else "missing"
            ),
            "near_native_record": "reports/bedc_vjepa2_ac_native_reproduction.json",
            "required_record": "official or near-native V-JEPA2-AC rollout reproduction with BEDC readback metrics",
        }

    return {
        "true_retraining_loss_ablation": retraining_contract,
        "vjepa2_ac_native_reproduction": native_contract,
    }


def _decision(gates: dict[str, dict[str, str]], blocking: list[str]) -> str:
    if not blocking:
        return "external_bundle_ready"
    if (
        gates["public_jepa_checkpoint_evaluation"]["status"] == "pass"
        and gates["native_public_jepa_benchmark"]["status"] == "pass"
        and gates["artifact_review_bundle"]["status"] != "pass"
    ):
        return "native_public_benchmark_closed_artifact_bundle_open"
    local_evidence = [
        "torch_objective_seed_sweep",
        "local_visual_planning",
        "object_counterfactual_clutter",
        "public_minigrid_execution",
        "public_jepa_checkpoint_evaluation",
    ]
    if all(gates[name]["status"] == "pass" for name in local_evidence):
        return "checkpoint_evaluation_closed_native_public_benchmark_open"
    return "evidence_boundary_open"


def build_bedc_jepa_readiness() -> dict[str, Any]:
    summary = _load_optional_json("bedc_jepa_four_system_experiment.json")
    torch_objective = _load_optional_json("bedc_jepa_torch_objective.json")
    public_minigrid = _load_optional_json("bedc_jepa_public_minigrid_benchmark_packet.json")
    native_public_minigrid = _load_optional_json("bedc_jepa_public_native_minigrid_benchmark.json")
    public_jepa_comparison = _load_optional_json("bedc_jepa_public_baseline_comparison.json")
    public_cuda_comparison = _load_optional_json("bedc_jepa_public_cuda_adapter_comparison.json")
    vjepa2_latent_prediction = _load_optional_json("bedc_vjepa2_ac_minigrid_latent_prediction.json")
    vjepa2_near_native = _load_optional_json("bedc_vjepa2_ac_native_reproduction.json")
    public_debt = _load_optional_json("bedc_jepa_public_debt_decomposition.json")
    public_conformal = _load_optional_json("bedc_jepa_conformal_certified_coverage.json")
    public_pareto = _load_optional_json("bedc_jepa_risk_success_pareto.json")
    public_calibration_extension = _load_optional_json("bedc_jepa_public_minigrid_calibration_extension.json")
    retraining_ablation = _load_optional_json("bedc_jepa_retraining_loss_ablation.json")
    vjepa2_native_boundary = _load_optional_json("bedc_jepa_vjepa2_ac_native_boundary.json")
    public_baseline_native_metric_contract = _load_optional_json(
        "bedc_jepa_public_baseline_native_metric_contract.json"
    )
    public_baseline_native_metric_template = _load_optional_json(
        "bedc_jepa_public_baseline_native_metric_template.json"
    )
    run_kit = _load_optional_json("bedc_jepa_review_bundle.json")
    gates = {
        "torch_objective_seed_sweep": _torch_objective_gate(torch_objective),
        "local_visual_planning": _local_visual_gate(summary),
        "object_counterfactual_clutter": _clutter_gate(summary),
        "public_minigrid_execution": _public_minigrid_gate(public_minigrid),
        "public_jepa_checkpoint_evaluation": _public_checkpoint_evaluation_gate(public_cuda_comparison),
        "vjepa2_ac_minigrid_latent_prediction": _vjepa2_latent_prediction_gate(vjepa2_latent_prediction),
        "vjepa2_ac_near_native_reproduction": _vjepa2_near_native_gate(vjepa2_near_native),
        "public_minigrid_calibration_pareto": _public_minigrid_calibration_pareto_gate(
            public_debt,
            public_conformal,
            public_pareto,
        ),
        "public_minigrid_calibration_extension": _public_minigrid_calibration_extension_gate(
            public_calibration_extension,
        ),
        "public_baseline_native_metric_contract": _public_baseline_native_metric_contract_gate(
            public_baseline_native_metric_contract,
        ),
        "public_baseline_native_metric_template": _public_baseline_native_metric_template_gate(
            public_baseline_native_metric_template,
        ),
        "native_public_jepa_benchmark": _native_public_benchmark_gate(native_public_minigrid),
        "artifact_review_bundle": _artifact_review_bundle_gate(run_kit),
    }
    blocking = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "schema_id": "bedc-jepa-readiness",
        "decision": _decision(gates, blocking),
        "evidence_boundary": {
            "checkpoint_evaluation": "closed"
            if gates["public_jepa_checkpoint_evaluation"]["status"] == "pass"
            else "open",
            "vjepa2_ac_minigrid_latent_prediction": "closed"
            if gates["vjepa2_ac_minigrid_latent_prediction"]["status"] == "pass"
            else "open",
            "vjepa2_ac_near_native_reproduction": "closed"
            if gates["vjepa2_ac_near_native_reproduction"]["status"] == "pass"
            else "open",
            "native_public_benchmark": "closed" if gates["native_public_jepa_benchmark"]["status"] == "pass" else "open",
            "public_minigrid_calibration_pareto": "closed"
            if gates["public_minigrid_calibration_pareto"]["status"] == "pass"
            else "open",
            "public_minigrid_calibration_extension": "closed"
            if gates["public_minigrid_calibration_extension"]["status"] == "pass"
            else "open",
            "public_baseline_native_metric_contract": "closed"
            if gates["public_baseline_native_metric_contract"]["status"] == "pass"
            else "open",
            "public_baseline_native_metric_template": "closed"
            if gates["public_baseline_native_metric_template"]["status"] == "pass"
            else "open",
            "artifact_review_bundle": "closed" if gates["artifact_review_bundle"]["status"] == "pass" else "open",
        },
        "remaining_evidence_contracts": _remaining_evidence_contracts(
            retraining_ablation,
            vjepa2_native_boundary,
            vjepa2_near_native,
            public_baseline_native_metric_contract,
            public_baseline_native_metric_template,
        ),
        "gates": gates,
        "blocking_gates": blocking,
        "next_actions": [
            "run an official V-JEPA2-AC benchmark reproduction or rollout benchmark beyond the fixed-checkpoint and near-native MiniGrid studies",
            "execute the recorded public baseline native metric contract on an official or external benchmark stream",
            "extend public MiniGrid calibration beyond the current symbolic-control readback scope",
            "import a public pixel-world benchmark result satisfying the recorded scope contract",
            "run a public object-interaction benchmark with natural clutter or control",
        ],
    }


def write_bedc_jepa_readiness(path: str | Path) -> dict[str, Any]:
    readiness = build_bedc_jepa_readiness()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(readiness, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return readiness

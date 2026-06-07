import json
from copy import deepcopy
from pathlib import Path

import pytest

from bedc_quality_lab.discovery_regularized_training import (
    MECHANISM_ABLATION_REQUIRED_ARMS,
    default_drt_training_extension_spec,
    project_drt_training_extension,
    _training_mechanism_cert,
)
from bedc_quality_lab.mechanism_attribution import mechanism_evidence_pointers
from scripts import run_ledger_aware_transformer as lat_runner
from scripts import run_certificate_gated_attention as cga_runner
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_regularized_training as runner

MODEL_DESIGN_FIXTURE_ARTIFACT_IDS = {
    "ledger-aware-transformer": "bedc-quality-lab:ledger-aware-transformer",
    "certificate-gated-attention": "bedc-quality-lab:certificate-gated-attention",
    "discovery-regularized-training": "bedc-quality-lab:discovery-regularized-training",
    "mechanism-seeking-network": "bedc-quality-lab:mechanism-seeking-network",
    "discovery-gated-nas": "bedc-quality-lab:discovery-gated-nas",
}


def _atlas_fixture_rows():
    row = {
        "surface_id": "S12",
        "label": "optimizer_undertraining",
        "surface_kind": "observed_debt",
        "variation_axis": "optimizer_training_budget",
        "evaluation_role": "boundary_only",
        "runnable_status": "not_runnable",
        "counting_reason": "optimizer-budget arm is represented as boundary evidence only",
        "countable_for_multi_surface_d5_o": False,
    }
    return {
        "surface_registry": [dict(row)],
        "surfaces": [
            {
                **row,
                "verdict": {
                    "status": "pass",
                    "counts_for_multi_surface_d5_o": False,
                    "failed_gates": [],
                },
            }
        ],
        "boundary_ledger": [
            {
                **row,
                "kind": "boundary_only_surface",
                "failed_gates": [],
            }
        ],
    }


def _drt_mechanism_ablation_fixture():
    return {
        "status": "pass",
        "backend": "deterministic-mechanism-ablation",
        "required_arms": list(MECHANISM_ABLATION_REQUIRED_ARMS),
        "required_arms_present": True,
        "comparison_pointers_resolve": True,
        "full_beats_all_ablations": True,
        "full_positive_mechanism_signal": True,
        "no_ablation_net_positive_parity": True,
        "by_arm": {
            arm: {
                "row_count": 3,
                "quality_q_mean": 0.60,
                "classifier_shift_count_mean": 0.0,
                "net_positive_count": 0,
            }
            for arm in MECHANISM_ABLATION_REQUIRED_ARMS
        },
        "comparisons": [
            {
                "arm_id": arm,
                "comparison_pointers": {
                    "full_quality_q": "reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.drt.quality_q_mean",
                    "ablation_quality_q": f"reports/canonical/discovery-regularized-training.json:$.mechanism_ablation.by_arm.{arm}.quality_q_mean",
                    "ablation_row_count": f"reports/canonical/discovery-regularized-training.json:$.mechanism_ablation.by_arm.{arm}.row_count",
                    "ablation_net_positive_count": f"reports/canonical/discovery-regularized-training.json:$.mechanism_ablation.by_arm.{arm}.net_positive_count",
                },
            }
            for arm in MECHANISM_ABLATION_REQUIRED_ARMS
        ],
    }


def _write_payload(root: Path, spec, payload):
    if spec.name == "discovery-regularized-training":
        payload = dict(payload)
        payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)
        payload.update(
            project_drt_training_extension(
                [],
                default_drt_training_extension_spec(),
                {"raw_metrics": "reports/runs/discovery-regularized-training/raw_metrics.jsonl"},
                payload,
            )
        )
        payload["training_mechanism_cert"] = _training_mechanism_cert(payload)
        payload["hardgate"]["gates"]["DRT-HG8"]["status"] = payload["training_mechanism_cert"]["status"]
        payload["hardgate"]["status"] = (
            "pass"
            if all(row["status"] == "pass" for row in payload["hardgate"]["gates"].values())
            else "fail"
        )
        canonical._validate_discovery_regularized_training_payload(payload)
    path = root / spec.json_artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _ensure_pointer_value(payload, pointer, value):
    target = payload
    parts = pointer[2:].split(".")
    for part in parts[:-1]:
        child = target.get(part)
        if not isinstance(child, dict):
            child = {}
            target[part] = child
        target = child
    if target.get(parts[-1]) is None:
        target[parts[-1]] = value


def _audit_complete_payload(spec, payload):
    payload = dict(payload)
    _ensure_pointer_value(payload, spec.scope_pointer, {"status": "fixture"})
    _ensure_pointer_value(payload, spec.cost_pointer, "configs/default_cost_protocol.yaml")
    _ensure_pointer_value(payload, spec.not_claimed_pointer, ["fixture boundary"])
    if spec.control_pointer is not None:
        _ensure_pointer_value(payload, spec.control_pointer, {"status": "fixture-control"})
    if spec.no_control_rationale_pointer is not None:
        _ensure_pointer_value(payload, spec.no_control_rationale_pointer, {"status": "fixture-rationale"})
    payload["audit_decision"] = {"audit_status": "pass"}
    if spec.name == "gap-head-attribution-capsule":
        payload.setdefault("cost_protocol_pointer", "configs/default_cost_protocol.yaml")
        payload.setdefault("control_pointer", "$.control_evidence")
        payload.setdefault("control_evidence", {"status": "matched-random-negative"})
    if spec.name == "gap-head-transfer-atlas":
        payload.update(_atlas_fixture_rows())
    return payload


def _write_audit_complete_payload(root: Path, report: str):
    spec = canonical._specs_by_name()[report]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    _write_payload(root, spec, payload)
    return spec, payload


def _minimal_payload(spec):
    payload = {key: f"fixture-{key}" for key in spec.required_json_keys}
    if spec.name in MODEL_DESIGN_FIXTURE_ARTIFACT_IDS:
        payload["artifact_id"] = MODEL_DESIGN_FIXTURE_ARTIFACT_IDS[spec.name]
    if spec.name == "gap-head-on-h":
        payload.update({
            "treatment_verdict": {"positive": True},
            "control_protocol": {"same_budget_as_treatment": True},
            "control_verdict": {"positive": False},
        })
        return payload
    if spec.name == "gap-head-discovery":
        payload.update({
            "positive_discovery": True,
            "matched_random_control": {
                "control_verdict": {"positive": False},
                "control_projection": {"positive_discovery": True},
            },
        })
        return payload
    if spec.name == "gap-head-ablation":
        payload.update({"hardgate": {"status": "fail", "gates": {"learned_head": {"status": "pass"}}}})
        return payload
    if spec.name == "ledger-aware-transformer":
        return lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    if spec.name == "certificate-gated-attention":
        return cga_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    if spec.name == "discovery-regularized-training":
        payload.update({
            "config": {
                "steps": 12,
                "seeds": [11, 23, 37],
                "mixings": ["spiral", "parabolic", "realnvp"],
                "rhos": [0.5, 0.7, 0.9, 0.95],
                "discovery_lambdas": [0.0, 0.0001, 0.001, 0.005, 0.01],
                "arms": ["task_only", "sigreg", "drt", "matched_random"],
            },
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_rows": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
            },
                "discovery_map_signal": {
                    "control_pointer": "$.matched_random_control",
                    "evidence_pointer": "$.training_mechanism_cert",
                    "failed_gate": None,
                    "failed_gate_pointer": None,
                    "level_candidate": "D5-M",
                    "reason": "training-mechanism-certificate-positive",
                    "status": "d5-m-candidate",
                    "training_mechanism_cert_pointer": "$.training_mechanism_cert",
                    "torch_training_evidence_pointer": "$.torch_training_evidence",
                },
            "hardgate": {
                "failed_gate": None,
                "gates": {
                    f"DRT-HG{index}": {
                        "status": "pass",
                        "evidence_pointer": "$.training_mechanism_cert"
                        if index == 8
                        else "$.mechanism_ablation"
                        if index == 7
                        else "$.quality_promotion_boundary",
                    }
                    for index in range(1, 9)
                },
                "status": "pass",
            },
            "failed_gate": None,
            "lambda_summary": {
                "best_positive": {
                    "discovery_lambda": "0.01",
                    "quality_q_mean": 0.62,
                    "delta_quality_ci_low_mean": 0.003,
                },
                "ordered_discovery_lambdas": [0.0, 0.0001, 0.001, 0.005, 0.01],
            },
            "torch_training_evidence": {
                "classifier_surface_delta": {
                    "source_arm": "drt",
                    "control_arm": "matched_random",
                    "drt_minus_matched_random_classifier_shift_count": 1.0,
                    "net_positive_signal": True,
                },
                "expected_row_count": 1,
                "protocols": [{"status": "complete"}],
                "row_count": 1,
                "status": "available",
            },
            "records": {
                "raw_rows_pointer": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
                "extension_metrics": {
                    "loss_terms_enabled": [
                        "discovery",
                        "ledger",
                        "certificate",
                        "mechanism",
                        "cost",
                        "negative_witness",
                    ],
                    "comparison_family": "task-sigreg-drt-matched-random",
                    "compute_ledger_pointer": "$.compute_ledger",
                    "debt_marker_pointer": "$.constraint_summary",
                    "uer_mean": 0.11,
                    "uer_reduction_mean": 0.09,
                    "sidecar_metric_pointers": {
                        "raw_metrics": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
                        "torch_training_evidence": "$.torch_training_evidence",
                        "matched_random_control": "$.matched_random_control",
                    },
                },
            },
            "surface_registry": {
                "quality": {
                    "source": "deterministic-anchor",
                    "metric": "quality_q",
                    "by_arm": {
                        "task_only": {"quality_q_mean": 0.58},
                        "sigreg": {"quality_q_mean": 0.60},
                        "drt": {"quality_q_mean": 0.64},
                        "matched_random": {"quality_q_mean": 0.59},
                    },
                },
                "classifier_shift": {
                    "classifier_shift_count_mean": 1.0,
                    "classifier_shift_positive": True,
                    "net_positive_signal": True,
                    "net_positive_count": 1,
                },
                "task_accuracy_only": {"task_accuracy_only_rejected": True, "promoted_row_count": 0},
            },
            "constraint_summary": {
                "drt_minus_task_only_debt_q": -0.1,
                "drt_minus_task_only_benefit_q": 0.02,
                "debt_down": True,
                "benefit_nondecreasing": True,
            },
            "device_protocol": {
                "requested_device": "auto",
                "resolved_device": "cpu",
                "drift_tolerance": 0.0001,
                "status": "available",
            },
            "compute_ledger": {
                "status": "complete",
                "backend_row_counts": {
                    "deterministic-anchor": 720,
                    "torch-training-arm": 16,
                },
                "device": "cpu",
                "requested_device": "auto",
                "resolved_device": "cpu",
                "deterministic_seed_count": 3,
                "torch_seed_count": 2,
                "total_steps": 8832,
                "wall_time_seconds_proxy": 2.16,
                "flops_proxy": 36175872,
                "energy_proxy": 0.003618,
                "cost_protocol_pointer": "$.source_artifacts.cost_protocol",
                "raw_rows_pointer": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
                "protocols_pointer": "$.torch_training_evidence.protocols",
                "missing_fields": [],
                "evidence_pointer": "$.records",
            },
            "negative_witness_mutations": {
                "status": "armed",
                "source_arm": "drt",
                "mutation_arm": "matched_random",
            },
            "training_loop_trace": {
                "status": "available",
                "source_arm": "drt",
                "mutation_arm": "matched_random",
            },
            "matched_random_control": {"control_positive_discovery": False},
        })
        payload["mechanism_ablation"] = _drt_mechanism_ablation_fixture()
        return payload
    if spec.name == "mechanism-seeking-network":
        payload.update({
            "records": {
                "tensor_slice_registry": {
                    "copy_route": {"tensor_slice_ids": ["tensor-copy"]},
                    "parity_gate": {"tensor_slice_ids": ["tensor-parity"]},
                    "sparse_recall": {"tensor_slice_ids": ["tensor-sparse"]},
                },
                "ablation_row_registry": {
                    "copy_route": ["ablation-copy"],
                    "parity_gate": ["ablation-parity"],
                    "sparse_recall": ["ablation-sparse"],
                },
                "patch_row_registry": {
                    "copy_route": ["patch-copy"],
                    "parity_gate": ["patch-parity"],
                    "sparse_recall": ["patch-sparse"],
                },
            },
            "surface_registry": {
                "copy_route": {
                    "classifier_surface": {"classifier_surface_id": "classifier-surface:copy_route"},
                    "evidence_pointer": "$.mechanism_gate_summary.by_mechanism.copy_route",
                },
                "parity_gate": {
                    "classifier_surface": {"classifier_surface_id": "classifier-surface:parity_gate"},
                    "evidence_pointer": "$.mechanism_gate_summary.by_mechanism.parity_gate",
                },
                "sparse_recall": {
                    "classifier_surface": {"classifier_surface_id": "classifier-surface:sparse_recall"},
                    "evidence_pointer": "$.mechanism_gate_summary.by_mechanism.sparse_recall",
                },
                "forbidden_alias_audit": {"status": "pass", "forbidden_alias_count": 0},
            },
            "discovery_map_signal": {
                "control_pointer": "$.matched_random_control",
                "evidence_pointer": "$.mechanism_gate_summary",
                "failed_gate": None,
                "failed_gate_pointer": None,
                "level_candidate": "D4",
                "mechanism_evidence_pointer": "$.mechanism_gate_summary.by_mechanism",
                "reason": "mechanism-gate-positive",
                "status": "d4-candidate",
                "surface_registry_pointer": "$.surface_registry",
            },
            "hardgate": {
                "failed_gate": None,
                "gates": {f"MSN-HG{index}": {"status": "pass"} for index in range(1, 7)},
                "status": "pass",
            },
            "mechanism_gate_summary": {
                "accepted": True,
                "accepted_surface_count": 3,
                "by_mechanism": {
                    "copy_route": {"accepted": True},
                    "parity_gate": {"accepted": True},
                    "sparse_recall": {"accepted": True},
                },
            },
            "matched_random_control": {"control_positive_discovery": False},
            "distinction_module_evidence": {
                "schema_id": "bedc-quality-lab:mechanism-seeking-network#$.distinction_module_evidence",
                "owner_pointer": "$.distinction_module_evidence",
                "records": [
                    {
                        "module_id": "copy_route",
                        "tensor_slice_pointer": "$.records.tensor_slice_registry.copy_route",
                        "classifier_surface_pointer": "$.surface_registry.copy_route.classifier_surface",
                        "stability_score_pointer": "$.distinction_module_risk.copy_route.stability_score",
                        "shortcut_risk_pointer": "$.distinction_module_risk.copy_route.shortcut_risk",
                        "ledger_risk_pointer": "$.distinction_module_risk.copy_route.ledger_risk",
                        "ablation_rows_pointer": "$.records.ablation_row_registry.copy_route",
                        "patch_rows_pointer": "$.records.patch_row_registry.copy_route",
                        "ablation_status": "pass",
                        "patch_status": "pass",
                        "risk_audit_status": "pass",
                        "audit_status": "pass",
                    },
                    {
                        "module_id": "parity_gate",
                        "tensor_slice_pointer": "$.records.tensor_slice_registry.parity_gate",
                        "classifier_surface_pointer": "$.surface_registry.parity_gate.classifier_surface",
                        "stability_score_pointer": "$.distinction_module_risk.parity_gate.stability_score",
                        "shortcut_risk_pointer": "$.distinction_module_risk.parity_gate.shortcut_risk",
                        "ledger_risk_pointer": "$.distinction_module_risk.parity_gate.ledger_risk",
                        "ablation_rows_pointer": "$.records.ablation_row_registry.parity_gate",
                        "patch_rows_pointer": "$.records.patch_row_registry.parity_gate",
                        "ablation_status": "pass",
                        "patch_status": "pass",
                        "risk_audit_status": "pass",
                        "audit_status": "pass",
                    },
                    {
                        "module_id": "sparse_recall",
                        "tensor_slice_pointer": "$.records.tensor_slice_registry.sparse_recall",
                        "classifier_surface_pointer": "$.surface_registry.sparse_recall.classifier_surface",
                        "stability_score_pointer": "$.distinction_module_risk.sparse_recall.stability_score",
                        "shortcut_risk_pointer": "$.distinction_module_risk.sparse_recall.shortcut_risk",
                        "ledger_risk_pointer": "$.distinction_module_risk.sparse_recall.ledger_risk",
                        "ablation_rows_pointer": "$.records.ablation_row_registry.sparse_recall",
                        "patch_rows_pointer": "$.records.patch_row_registry.sparse_recall",
                        "ablation_status": "pass",
                        "patch_status": "pass",
                        "risk_audit_status": "pass",
                        "audit_status": "pass",
                    },
                ],
            },
            "distinction_module_risk": {
                "copy_route": {"stability_score": 0.7, "shortcut_risk": 0.1, "ledger_risk": 0.1},
                "parity_gate": {"stability_score": 0.7, "shortcut_risk": 0.1, "ledger_risk": 0.1},
                "sparse_recall": {"stability_score": 0.7, "shortcut_risk": 0.1, "ledger_risk": 0.1},
            },
            "d5_m_readiness": {
                "status": "blocked",
                "passed": False,
                "failed_gate": "d5_o_source",
                "hardgate_pointer": "$.hardgate.gates.MSN-HG6.status",
                "distinction_module_evidence_ref": "$.distinction_module_evidence",
                "d5_o_source_pointer": "$.source_artifacts.d5_o_source",
            },
            "source_artifacts": {"d5_o_source": None},
            "forbidden_claim_term_audit": {"status": "pass"},
        })
        return payload
    if spec.name == "discovery-gated-nas":
        payload.update({
            "discovery_map_signal": {
                "control_pointer": "$.matched_baseline_control",
                "evidence_pointer": "$.search_objective_summary.selected_candidate",
                "failed_gate": None,
                "failed_gate_pointer": None,
                "level_candidate": "D5-M",
                "negative_witness_pointer": "$.negative_witness_mutations",
                "reason": "discovery-gated-search-positive",
                "search_objective_pointer": "$.search_objective_summary",
                "search_space_pointer": "$.search_space",
                "status": "d5-m-candidate",
                "torch_nas_evidence_pointer": "$.torch_nas_evidence",
            },
            "hardgate": {
                "failed_gate": None,
                "gates": {f"DG-NAS-HG{index}": {"status": "pass"} for index in range(1, 9)},
                "status": "pass",
            },
            "search_space": {"status": "closed"},
            "candidate_protocol": {
                "search_space_pointer": "$.search_space",
                "design_search_certificate": {
                    "owner_pointer": "reports/canonical/discovery-gated-nas.json:$.candidate_protocol.design_search_certificate",
                    "slot_state": "present",
                },
            },
            "matched_baseline_control": {"control_positive_discovery": False},
            "negative_witness_mutations": {"rows": []},
            "search_objective_summary": {"selected_candidate": {"candidate_id": "fixture-candidate"}},
            "torch_nas_evidence": {"status": "available"},
        })
        return payload
    if spec.name == "gap-head-transfer-atlas":
        payload.update({
            "config": {"control_arm": "matched_random_gap_head"},
            "multi_surface_d5_o": {"decision": "pass", "discovery_level": "D5-O", "pass_surface_count": 3},
            "forbidden_claim_term_audit": {"status": "pass", "hits": []},
            "source_artifacts": {"metric_helper": "reports/canonical/gap_head_transfer_atlas.json:$.surfaces"},
        })
        return payload
    if spec.name == "spectral-ablation-hinge":
        payload.update({
            "ledger_summary": {"status": "negative"},
            "negative_control_summary": {"treatment_better_than_all_controls": False},
        })
        return payload
    if spec.name == "certificate-guided-training":
        payload.update({
            "result": {"status": "negative"},
            "deltas": {"after_minus_before": {"debt_delta": -0.25}},
            "arm_protocol": {"compat_roles": {"after": "constraint_lagrangian"}},
            "claim_gate": {"audit_improvement_tradeoff": True},
            "hardgate": {"failed_gate": "audit-improvement-tradeoff", "status": "failed"},
            "claim_capsule": {
                "run_local": {
                    "negative_witness": [
                        {
                            "artifact": "reports/runs/certificate-guided-constraint-training/claim_capsule.json",
                            "pointer": "$.run_local.negative_witness[0]",
                        }
                    ]
                },
                "terminal_verdict": "DN(audit-improvement-tradeoff)",
            },
        })
        return payload
    if spec.name == "certificate-guided-discovery":
        payload.update({
            "main_claim_status": "observed-negative",
            "positive_discovery": False,
            "verdicts": [{"deltas": {"debt_delta": -0.25}}],
            "claim_gate": {"training_audit_improvement_tradeoff": True},
        })
        return payload
    if spec.name == "anisotropic-ou-sweep":
        payload.update({"transition_debt_by_grid": {"cell": {"status": "open-or-partial"}}})
        return payload
    if spec.name == "nongaussian-distribution-sweep":
        payload.update({
            "negative_result_ledger": [{"status": "negative"}],
            "coverage_item": {"debt_item": {"status": "open"}},
        })
        return payload
    if spec.name == "mixing-family-sweep":
        payload.update({
            "coverage_item": {"debt_item": {"status": "open"}},
            "applicability_boundary": {"not_claimed": ["no global positive discovery claim"]},
            "source_artifacts": {"cost_protocol": "configs/default_cost_protocol.yaml"},
        })
        return payload
    if spec.name == "gap-head-attribution-capsule":
        payload.update({
            "d5_o": {"status": "ready"},
            "d5_m": {"status": "blocked", "passed": False, "failed_gate": "A1-HG3"},
            "mechanism_case": {"status": "D5-O retained, mechanism = probe-margin-channel"},
            "mechanism_evidence": {
                "evidence_level": "patch",
                "base_level": "D5-O",
                "base_status": "ready",
                "mechanism_level": "blocked",
                "mechanism_status": "blocked",
                "candidate_mechanism": "probe-margin-channel",
                "failed_gate": "A1-HG3",
                "residualized_significant": True,
                "control_clear": True,
                "score_margin_sufficient": True,
                "required_gate_pointers": [
                    "$.a4_hardgates.gates.A4-HG2.status",
                    "$.a4_hardgates.gates.A4-HG3.status",
                    "$.a4_hardgates.gates.A4-HG5.status",
                ],
                "metric_pointers": {
                    "residualized_status": "$.residualized_attribution.status",
                    "score_margin_channel_classification": "$.score_margin_causal_evidence.channel_classification",
                },
                "ledger_debt_pointer": "$.ledger_debt.0.status",
                "closure_pointer": "$.mechanism_evidence.mechanism_status",
                "source_issue": 747,
            },
            "scope_seal": {"not_claimed": ["no global mechanism closure claim"]},
            "ledger_debt": [{"debt_id": "gap-head-mechanism-evidence-closure", "status": "open"}],
            "not_implemented": ["nonlinear_residualization", "full_causal_replacement_scope"],
            "a4_hardgates": {"gates": {"A4-HG2": {"status": "pass"}, "A4-HG3": {"status": "pass"}, "A4-HG5": {"status": "fail"}}},
            "residualized_attribution": {"status": "pass"},
            "score_margin_causal_evidence": {"channel_classification": "score_margin_sufficient"},
        })
        return payload
    if spec.name == "sigreg-mini-grid":
        payload.update({
            "c3_hardgates": {
                "C3-HG1": {"status": "pass"},
                "C3-HG2": {"status": "pass"},
                "C3-HG3": {"status": "pass"},
                "C3-HG4": {"status": "pass"},
            },
            "discovery_map_signal": {
                "evidence_pointer": "$.trend_summary.expected_trend",
                "failed_gate": None,
                "failed_gate_pointer": None,
                "level_candidate": "D2",
                "reason": "expected-trend",
                "status": "d2-candidate",
            },
            "hardgate": {"failed_gate": None, "status": "pass"},
            "trend_summary": {"expected_trend": True},
        })
        return payload
    if spec.name == "lejepa-theorem-ledger":
        payload.update({
            "claim_gate": {"status": "pass"},
            "result": {"status": "pass"},
            "theorem_rows": [{"theorem": "fixture-theorem", "status": "pass"}],
        })
        return payload
    return payload


def _write_all_payloads(root: Path):
    for spec in canonical.CANONICAL_REPORTS:
        _write_payload(root, spec, _minimal_payload(spec))
    _write_dimension_mismatch_gap_witness_fixture(root)
    _write_lejepa_mini_grid_fixture(root)
    _write_json_artifact(root, discovery_map.QUALITY_SCORECARD_ARTIFACT, _scorecard_payload())
    _write_json_artifact(
        root,
        discovery_map.MECHANISM_NAMECERT_ARTIFACT,
        {
            "source_spec": {
                "scope_seal": {
                    "not_claimed": [
                        "not a formal BEDC NameCert",
                        "not Lean verification",
                        "not mechanism theorem closure",
                    ]
                }
            },
            "ledger_policy": {"mechanism_closure_debt": "open"},
            "closure_status": {"mechanism_spec": "partial"},
            "mechanism_spec": {
                "candidate_mechanism": "probe-margin-channel",
                "full_vs_score_plus_margin": "not separated",
                "a1_failed_gate": "A1-HG3",
            },
        },
    )


def _write_coverage_payloads(root: Path):
    _write_all_payloads(root)
    _write_gap_head_d5_context(root, transfer_metric=True)
    _write_json_artifact(
        root,
        discovery_map.DISCOVERY_GATED_TRANSFORMER_ARTIFACT,
        {
            "status": "present-but-fail-closed",
            "mechanism_certificate": {"status": "present"},
            "dgt_hardgate_slots": {"overall_state": "present-but-fail-closed"},
            "not_claimed": ["no broad architecture superiority claim"],
        },
    )
    _write_json_artifact(
        root,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="pass"),
    )
    owner_rows = discovery_map.build_negative_discovery_owner_rows(root=root)
    _write_json_artifact(
        root,
        discovery_map.NEGATIVE_DISCOVERY_REPORTS_ARTIFACT,
        {
            "schema_id": "bedc-quality-lab:negative-discovery-reports",
            "artifact_id": "bedc-quality-lab:negative-discovery-reports",
            "generated_at": "fixture-time",
            "json_artifact": discovery_map.NEGATIVE_DISCOVERY_REPORTS_ARTIFACT,
            "markdown_artifact": "reports/canonical/negative_discovery_reports.md",
            "status": "pointer-only",
            "row_count": len(owner_rows),
            "rows": owner_rows,
        },
    )


def _write_json_artifact(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _write_dimension_mismatch_gap_witness_fixture(root: Path):
    _write_json_artifact(
        root,
        "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json",
        {
            "run_local": {
                "negative_witness": [
                    {
                        "bedc_gap_field": "representation_scale_leakage",
                        "demotion_rule": "demote_to_DN_or_D1",
                        "regression_test": "$.run_local.test_artifact.regression_tests.scale_leakage_witness",
                    }
                ],
                "test_artifact": {
                    "regression_tests": {
                        "scale_leakage_witness": (
                            "tests/test_dimension_mismatch_debt_transfer.py::"
                            "test_scale_leakage_sidecar_maps_to_first_negative_witness"
                        )
                    }
                },
            }
        },
    )


def _write_lejepa_mini_grid_fixture(root: Path):
    _write_json_artifact(
        root,
        "reports/runs/lejepa-mini-grid/claim_capsule.json",
        {
            "claim_status": "failed",
            "failed_gate": "D2-HG2",
            "hardgates": {"D2-HG2": {"status": "fail"}},
            "not_claimed": ["full LeJEPA reproduction"],
            "run_local": {
                "negative_witness": [
                    {
                        "bedc_gap_field": "lambda_rho_trend_gap",
                        "demotion_rule": "demote_to_DN_on_D2_HG2_failure",
                        "evidence_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$.hardgates.D2-HG2",
                        "regression_test": (
                            "tests/test_lejepa_mini_grid.py::"
                            "test_lejepa_run_local_negative_witness_records_d2_hg2_failure"
                        ),
                        "source_artifact": "reports/runs/lejepa-mini-grid/claim_capsule.json",
                        "source_pointer": "$.failed_gate",
                        "status": "fail",
                        "witness_id": "lejepa-mini-grid:lambda-rho-trend-hardgate-failure",
                    }
                ],
                "negative_witness_hardgates": {"status": "pass"},
            },
        },
    )


def _write_release_pointer_fixture(root: Path):
    (root / "docs" / "lit").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "artifact_manifest.md").write_text(
        "# Artifact Manifest\n\n"
        "## Quality Baseline Surfaces\n\n"
        "| artifact id | path | discovery_level pointer | pointer status |\n"
        "| --- | --- | --- | --- |\n"
        "| `bedc-quality-lab:artifact-manifest` | `docs/artifact_manifest.md` | "
        "`## Quality Baseline Surfaces` | pointer-only |\n",
        encoding="utf-8",
    )
    (root / "docs" / "lit" / "literature_ledger.yaml").write_text(
        json.dumps({"records": [{"id": "lit-artifact-release-navigation"}]}) + "\n",
        encoding="utf-8",
    )
    (root / "VERSION").write_text("0.0.1\n", encoding="utf-8")


def _scorecard_payload(status="ready"):
    metrics = (
        "CertCov",
        "DebtQ",
        "CriticalDebt",
        "LedgerCompleteness",
        "ClassifierShiftCount",
        "PositiveDiscoveryCount",
        "AuditImprovementCount",
        "NegativeResultCount",
        "ScopeCompleteness",
        "CostProtocolCompleteness",
        "HardeningCoverage",
        "OverclaimRate",
    )
    return {
        "artifact_id": "bedc-quality-lab:quality-scorecard",
        "rows": [{"metric": metric, "status": status} for metric in metrics],
    }


def _read_json_artifact(root: Path, artifact: str):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _owner_by_pointer(root: Path, pointer: str):
    owners = discovery_map.build_negative_discovery_owner_rows(root=root)
    index_text = pointer.removeprefix("reports/canonical/negative_discovery_reports.json:$.rows[").removesuffix("]")
    assert index_text.isdigit()
    return owners[int(index_text)]


def _robustness_context_payload():
    return {
        "final_status": "pass",
        "acceptance_gates": {"status": "pass"},
        "A1_threshold_sweep": {"treatment_verdict": {"positive": True}},
        "A2_feature_ablation": {"status": "complete"},
        "A3_seed_expansion": {"status": "complete", "final_verdict": "robust_positive"},
        "A4_distribution_transfer": {
            "status": "complete",
            "policy": "pointer_only_existing_transfer_surfaces_no_retraining",
        },
    }


def _negative_witnesses_context_payload(*, expected_kind_count=8):
    return {
        "status": "pointer-only",
        "expected_kind_count": expected_kind_count,
        "witnesses": [
            {"kind": f"witness-{index}", "terminal_verdict": "rejected", "discovery_level": "DN"}
            for index in range(expected_kind_count)
        ],
    }


def _auroc_cell(*, mean, ci95_low, ci95_high):
    return {
        "ci95_half_width": 0.01,
        "ci95_high": ci95_high,
        "ci95_low": ci95_low,
        "mean": mean,
        "n": 10,
        "std": 0.01,
    }


def _learned_auroc_pass_cell():
    return _auroc_cell(mean=0.82, ci95_low=0.81, ci95_high=0.83)


def _matched_random_auroc_pass_cell():
    return _auroc_cell(mean=0.46, ci95_low=0.42, ci95_high=0.49)


def _observed_debt_transfer_context_payload(*, transfer_metric=False):
    payload = {
        "artifact_id": "bedc-quality-lab:gap-head-observed-debt-transfer",
        "hardgate_evidence": {
            "HG-A1": {"status": "pass"},
            "HG-A2": {"status": "pass"},
            "HG-A3": {"status": "pass"},
            "HG-A4": {"status": "pass"},
            "HG-A5": {"status": "pass" if transfer_metric else "fail"},
        },
        "surfaces": [
            {
                "control_verdict": {"positive": False},
                "hardgates": {
                    "HG-A1": {
                        "learned_auroc": _learned_auroc_pass_cell(),
                        "matched_random_auroc": _matched_random_auroc_pass_cell(),
                        "status": "pass" if transfer_metric else "fail",
                    }
                },
                "verdict": {"status": "pass" if transfer_metric else "failed"},
            }
        ],
        "not_claimed": ["no claim outside the listed observed-debt transfer surfaces"],
    }
    if transfer_metric:
        payload["gap_head_on_h_observed_debt_transfer"] = {"status": "pass"}
    return payload


def _dimension_mismatch_payload(*, status="pass", anti_triviality_status="scale_leakage_detected"):
    effective_level = "D4" if anti_triviality_status == "anti_triviality_passed" else "DN"
    terminal_verdict = "source_pass" if effective_level == "D4" else "negative_discovery"
    downgrade_reason = None if effective_level == "D4" else "scale_only_or_metadata_proxy_sufficient"
    failed_gate = None if effective_level == "D4" else "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    return {
        "artifact_id": "bedc-quality-lab:dimension-mismatch-debt-transfer",
        "status": "pointer-only",
        "control_protocol": {"control_arm": "matched_random_gap_head"},
        "dimension_mismatch_debt_transfer": {
            "status": status,
            "status_code": "scoped-d4-boundary" if status == "pass" else "failed-boundary",
            "reason": "fixture",
            "scope": "encoder_dim grid against producer reference latent dimension",
            "base_level": "D4",
            "anti_triviality_status": anti_triviality_status,
            "anti_triviality_evidence": {
                "artifact": "reports/canonical/dimension-mismatch-debt-transfer.json",
                "status_pointer": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            },
            "anti_triviality_projection": "no_level_change_signal_detected"
            if anti_triviality_status == "anti_triviality_passed"
            else "demote_to_DN_or_D1",
            "effective_level": effective_level,
            "downgrade_reason": downgrade_reason,
            "terminal_verdict": terminal_verdict,
            "discovery_level": effective_level,
            "hypothesis": "fixture hypothesis",
            "failed_gate": failed_gate,
            "what_was_learned": "fixture learned",
            "not_claimed": [
                "global dimension theory",
                "representation-geometric debt transfer",
                "D5 promotion",
            ],
        },
        "boundary_ledger": {"d5_shortcut": False},
        "hardgate_evidence": {
            "HG-B3": {
                "learned_auroc": _learned_auroc_pass_cell(),
                "matched_random_auroc": _matched_random_auroc_pass_cell(),
                "matched_random_positive": False,
                "status": "pass" if status == "pass" else "fail",
            }
        },
        "not_claimed": ["no claim outside the listed encoder_dim-grid debt-transfer surface"],
    }


def _write_gap_head_d5_context(root: Path, *, transfer_metric=False, witness_count=8):
    _write_json_artifact(root, discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT, _robustness_context_payload())
    _write_json_artifact(
        root,
        discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
        _negative_witnesses_context_payload(expected_kind_count=witness_count),
    )
    _write_json_artifact(
        root,
        discovery_map.OBSERVED_DEBT_ARTIFACT,
        _observed_debt_transfer_context_payload(transfer_metric=transfer_metric),
    )
    _write_json_artifact(
        root,
        discovery_map.MECHANISM_NAMECERT_ARTIFACT,
        {
            "ledger_policy": {"mechanism_closure_debt": "open"},
            "closure_status": {"mechanism_spec": "partial"},
            "mechanism_spec": {
                "candidate_mechanism": "probe-margin-channel",
                "full_vs_score_plus_margin": "not separated",
                "a1_failed_gate": "A1-HG3",
            },
        },
    )


def _rewrite_gap_head_d5_artifact(root: Path, artifact: str, mutate):
    payload = _read_json_artifact(root, artifact)
    mutate(payload)
    _write_json_artifact(root, artifact, payload)


def _without_key(key):
    def mutate(payload):
        payload.pop(key, None)

    return mutate


def _set_nested(path, value):
    def mutate(payload):
        target = payload
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value

    return mutate


def _pop_nested(path):
    def mutate(payload):
        target = payload
        for key in path[:-1]:
            target = target[key]
        target.pop(path[-1], None)

    return mutate


def _add_gate_breaking_witness(payload):
    mutated_witnesses = deepcopy(payload["witnesses"])
    mutated_witnesses[0]["terminal_verdict"] = "accepted"
    payload["witnesses"] = mutated_witnesses


def _row_by_report(payload):
    return {row["report"]: row for row in payload["rows"]}


def _coverage_cell(payload, target):
    return next(
        cell
        for cell in payload["coverage_matrix"]["cells"]
        if cell["component_id"] == target
    )


def _artifact_pointer_value(root: Path, pointer: str):
    artifact, local_pointer = pointer.split(":", 1)
    if local_pointer == "$":
        return _read_json_artifact(root, artifact)
    return discovery_map.pointer_value(_read_json_artifact(root, artifact), local_pointer)


def _payload_pointer_value(payload, pointer: str):
    artifact, local_pointer = pointer.split(":", 1)
    if artifact == "reports/canonical/discovery_map.json":
        return discovery_map.pointer_value(payload, local_pointer)
    raise AssertionError(f"unsupported payload pointer artifact: {artifact}")


def _contains_key(payload, key):
    if isinstance(payload, dict):
        return key in payload or any(_contains_key(value, key) for value in payload.values())
    if isinstance(payload, list):
        return any(_contains_key(value, key) for value in payload)
    return False


def test_discovery_map_coverage_matrix_has_single_owner(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert payload["coverage_matrix"]["status"] == "pointer-only"
    assert not (tmp_path / "reports" / "canonical" / "discovery_coverage.json").exists()
    assert all(spec.name != "discovery_coverage" for spec in canonical.CANONICAL_REPORTS)
    assert all(spec.name != "discovery-coverage" for spec in canonical.CANONICAL_REPORTS)
    assert all(spec.name != "bedc.model.discovery_coverage" for spec in canonical.CANONICAL_REPORTS)


def test_discovery_map_coverage_matrix_matches_target_set(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    cells = payload["coverage_matrix"]["cells"]

    assert {cell["component_id"] for cell in cells} == discovery_map.COVERAGE_COMPONENT_IDS
    assert len(cells) == 13
    assert all(set(cell) == discovery_map.COVERAGE_CELL_FIELDS for cell in cells)
    assert set(payload["coverage_matrix"]) == {"status", "hardgates", "cells"}
    assert set(payload["coverage_matrix"]["hardgates"]) == set(discovery_map.COVERAGE_HARDGATE_IDS)
    assert payload["coverage_matrix"]["status"] == "pointer-only"


def test_discovery_map_coverage_matrix_projects_drt_and_lat_cells(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    drt = _coverage_cell(payload, "DRT")
    lat = _coverage_cell(payload, "LAT")

    assert drt["canonical_owner_pointer"] == "reports/canonical/discovery-regularized-training.json:$"
    assert drt["mechanism_certificate_pointer"] == "reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert"
    assert drt["debt_pointer"] == "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary"
    assert drt["hardgate_status"] == "pass"
    assert _artifact_pointer_value(tmp_path, drt["mechanism_certificate_pointer"]) is not None
    assert "metric" not in drt
    assert "aggregate_score" not in drt
    assert "classifier_reasons" not in drt
    assert "training_rows" not in drt

    assert lat["canonical_owner_pointer"] == "reports/canonical/ledger-aware-transformer.json:$"
    assert lat["mechanism_certificate_pointer"] == "reports/canonical/ledger-aware-transformer.json:$.claim_capsule_ref"
    assert lat["hardgate_status"] == "pass"
    assert _artifact_pointer_value(tmp_path, lat["canonical_owner_pointer"]) is not None


def test_discovery_map_coverage_matrix_projects_gap_head_axes(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    capsule = _coverage_cell(payload, "gap-head-mech")

    assert capsule["canonical_owner_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence"
    assert capsule["mechanism_certificate_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence"
    assert capsule["debt_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt"
    assert capsule["hardgate_status"] == "pass"
    assert _artifact_pointer_value(tmp_path, capsule["canonical_owner_pointer"]) is not None


def test_discovery_map_coverage_matrix_resolves_target_pointers(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    for cell in payload["coverage_matrix"]["cells"]:
        for field in discovery_map.COVERAGE_POINTER_FIELDS:
            pointer = cell[field]
            if pointer is None:
                continue
            if pointer.startswith("reports/canonical/discovery_map.json:"):
                assert _payload_pointer_value(payload, pointer) is not None
            else:
                assert _artifact_pointer_value(tmp_path, pointer) is not None


def test_discovery_map_coverage_matrix_omits_non_discovery_suite_target(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert "discovery-gated-transformer" not in {cell["component_id"] for cell in payload["coverage_matrix"]["cells"]}


def test_discovery_map_coverage_matrix_dangling_pointer_fails_closed(tmp_path):
    _write_coverage_payloads(tmp_path)
    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    broken = deepcopy(payload["coverage_matrix"])
    broken["cells"] = [dict(cell) for cell in broken["cells"]]
    broken["cells"][0]["claim_verdict_pointer"] = "reports/canonical/missing.json:$.missing"
    broken["hardgates"] = discovery_map._coverage_hardgate_rows(broken["cells"], root=tmp_path)
    broken["cells"][0]["hardgate_status"] = "fail"
    broken["cells"][0]["hardgate_reason"] = "claim_verdict_pointer-unresolved"
    broken["status"] = "fail-closed"
    payload = discovery_map.build_discovery_map_payload(
        rows=payload["rows"],
        generated_at="fixture-time",
        coverage_matrix=broken,
        root=tmp_path,
    )

    assert payload["coverage_matrix"]["status"] == "fail-closed"
    assert payload["coverage_matrix"]["hardgates"]["COV-HG2-resolves"]["status"] == "fail"
    assert payload["coverage_matrix"]["cells"][0]["hardgate_status"] == "fail"


def test_discovery_map_coverage_matrix_has_no_terminal_verdict_key(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert not _contains_key(payload["coverage_matrix"], "terminal_verdict")
    assert not _contains_key(payload["coverage_matrix"], "metrics")
    assert not _contains_key(payload["coverage_matrix"], "classifier_reasons")
    for fact_key in discovery_map.DN_FACT_KEYS:
        assert not _contains_key(payload["coverage_matrix"], fact_key)


def test_discovery_map_coverage_matrix_dn_cells_are_pointer_only(tmp_path):
    _write_coverage_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    dimension = _coverage_cell(payload, "dimension-mismatch-DN")
    certificate = _coverage_cell(payload, "certificate-guided-DN")
    lejepa = _coverage_cell(payload, "LeJEPA-mini-grid-DN")

    assert dimension["negative_witness_pointer"] == discovery_map.DIMENSION_MISMATCH_GAP_WITNESS_POINTER
    assert certificate["negative_witness_pointer"] == "reports/canonical/negative_discovery_reports.json:$.rows[1]"
    assert lejepa["negative_witness_pointer"] == "reports/runs/lejepa-mini-grid/claim_capsule.json:$.run_local.negative_witness[0]"
    for cell in (dimension, certificate, lejepa):
        assert cell["hardgate_status"] == "pass"
        assert _artifact_pointer_value(tmp_path, cell["negative_witness_pointer"]) is not None
        for key in discovery_map.DN_FACT_KEYS | {"terminal_verdict"}:
            assert key not in cell


def test_discovery_map_payload_rejects_non_pointer_only_coverage_matrix():
    cell = {
        "component_id": "DGT",
        "canonical_owner_pointer": "reports/canonical/positive.json:$",
        "discovery_level_pointer": "reports/canonical/positive.json:$.level",
        "claim_verdict_pointer": "reports/canonical/positive.json:$.claim",
        "mechanism_certificate_pointer": "reports/canonical/positive.json:$.mechanism",
        "debt_pointer": None,
        "not_claimed_pointer": "reports/canonical/positive.json:$.not_claimed",
        "negative_witness_pointer": None,
        "hardgate_status": "pass",
        "hardgate_reason": "pass",
    }
    row = {
        "report": "positive-fixture",
        "json_artifact": "reports/canonical/positive.json",
        "markdown_artifact": "reports/canonical/positive.md",
        "discovery_level": "D4",
        "terminal_verdict": "",
        "projection_status": "projected",
        "evidence_pointer": "$.positive",
        "audit_status": "valid",
        "audit_reason": "",
    }

    with pytest.raises(ValueError, match="status must be pointer-only"):
        discovery_map.build_discovery_map_payload(
            rows=[row],
            generated_at="fixture-time",
            coverage_matrix={"status": "materialized", "hardgates": {}, "cells": [cell]},
        )
    with pytest.raises(ValueError, match="copies owner facts"):
        discovery_map.build_discovery_map_payload(
            rows=[row],
            generated_at="fixture-time",
            coverage_matrix={
                "status": "pointer-only",
                "hardgates": {gate: {"status": "pass", "reason": "pass"} for gate in discovery_map.COVERAGE_HARDGATE_IDS},
                "cells": [{**cell, "owner": {"terminal_verdict": "negative_discovery"}}],
            },
        )
    with pytest.raises(ValueError, match="schema mismatch"):
        discovery_map.build_discovery_map_payload(
            rows=[row],
            generated_at="fixture-time",
            coverage_matrix={
                "status": "pointer-only",
                "hardgates": {gate: {"status": "pass", "reason": "pass"} for gate in discovery_map.COVERAGE_HARDGATE_IDS},
                "cells": [{**cell, "owner_pointer": "$.rows[0]"}],
            },
        )


def test_discovery_map_has_one_row_per_canonical_report(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert [row["report"] for row in payload["rows"]] == [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert payload["row_count"] == len(canonical.CANONICAL_REPORTS)
    assert all(row["discovery_level"] in discovery_map.DISCOVERY_LEVELS for row in payload["rows"])


def test_threshold_frontier_without_projection_remains_d0_source_insufficient(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-threshold-frontier"]

    assert row["discovery_level"] == "D0"
    assert row["projection_status"] == "source-insufficient"
    assert row["audit_status"] == "valid"
    assert row["audit_reason"] == ""


def test_lat_current_lab_projection_maps_d5_o_and_resolves_pointers(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert row["discovery_level"] == "D5-O"
    assert row["terminal_verdict"] == ""
    assert row["audit_status"] == "valid"
    assert row["evidence_pointer"] == "$.aggregate_metrics.uer_reduction"
    assert row["control_pointer"] == "$.matched_random_control"
    assert row["robustness_pointer"] == "reports/canonical/ledger-aware-transformer.json:$.robustness_signal"
    assert row["scorecard_pointer"] == "reports/canonical/quality-scorecard.json:$.rows"
    assert discovery_map.pointer_value(lat_payload, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(lat_payload, row["control_pointer"]) is not None
    assert lat_payload["discovery_map_signal"]["parameter_matched_baseline_pointer"] == "$.parameter_matched_baseline"
    assert lat_payload["discovery_map_signal"]["compute_matched_baseline_pointer"] == "$.compute_matched_baseline"
    assert discovery_map.pointer_value(
        lat_payload,
        lat_payload["discovery_map_signal"]["parameter_matched_baseline_pointer"],
    ) is not None
    assert discovery_map.pointer_value(
        lat_payload,
        lat_payload["discovery_map_signal"]["compute_matched_baseline_pointer"],
    ) is not None
    robustness_artifact, robustness_pointer = row["robustness_pointer"].split(":", 1)
    assert robustness_artifact == "reports/canonical/ledger-aware-transformer.json"
    assert discovery_map.pointer_value(lat_payload, robustness_pointer) is not None


def test_lat_robustness_failure_does_not_project_ready_d5_o(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    for index in range(3):
        lat_payload["records"][index]["deltas"]["unlogged_error_rate"] = 0.0
    _lat_recompute(lat_payload)
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert lat_payload["robustness_signal"]["status"] == "fail"
    assert lat_payload["hardgate"]["status"] == "pass"
    assert row["discovery_level"] == "DN"
    assert "robustness_pointer" not in row
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])
    assert owner["failed_gate"] == "$.robustness_signal.status"
    assert owner["terminal_verdict"] == "rejected"


def _lat_recompute(payload):
    import bedc_quality_lab.ledger_aware_transformer as lat

    projection = lat.LedgerAwareTransformerProjection(
        config=lat.LedgerAwareTransformerConfig(**payload["config"]),
        records=payload["records"],
        generated_at=payload["generated_at"],
        run_artifacts=payload["run_artifacts"],
        torch_protocol=lat.TorchLedgerArmProtocol(**payload["torch_training_evidence"]["protocol"]),
        compute_protocol=payload["compute_matched_baseline"],
    )
    payload["robustness_signal"] = lat._LAT_SURFACE_SUITE.robustness_signal(payload)
    hardgates = projection.hardgate_verdicts(payload)
    failed = projection.failed_gate(hardgates)
    payload["hardgate"] = {"status": "pass" if failed is None else "fail", "gates": hardgates, "failed_gate": failed}
    payload["failed_gate"] = failed
    payload["discovery_map_signal"] = projection.discovery_map_signal(hardgates, payload)
    return payload


def test_lat_zero_rows_fail_closed_to_dn_in_discovery_map(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    lat_payload["records"] = []
    _lat_recompute(lat_payload)
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "valid"
    assert row["audit_reason"] == ""
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])
    assert owner["failed_gate"] == "$.hardgate.gates.LAT-HG1.status"
    assert owner["terminal_verdict"] == "rejected"


def test_lat_dangling_pointer_fail_closed_to_dn_in_discovery_map(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    lat_payload["discovery_map_signal"]["evidence_pointer"] = "$.aggregate_metrics.missing"
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "lat-dangling-evidence-pointer"


def test_lat_discovery_map_rejects_dangling_parameter_matched_pointer(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    lat_payload["discovery_map_signal"]["parameter_matched_baseline_pointer"] = "$.missing_parameter_matched_baseline"
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert row["discovery_level"] == "DN"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "lat-dangling-parameter-matched-baseline-pointer"


def test_lat_compute_matched_failure_projects_dn_owner_to_hg8(tmp_path):
    _write_all_payloads(tmp_path)
    lat_payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    lat_payload["compute_matched_baseline"]["candidate_arm"]["flops_per_step"] = (
        lat_payload["compute_matched_baseline"]["baseline_arm"]["flops_per_step"] * 1.2
    )
    lat_payload["compute_matched_baseline"]["failed_metrics"] = ["flops_per_step"]
    lat_payload["compute_matched_baseline"]["status"] = "fail"
    _lat_recompute(lat_payload)
    _write_json_artifact(tmp_path, "reports/canonical/ledger-aware-transformer.json", lat_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["ledger-aware-transformer"]

    assert lat_payload["failed_gate"] == "LAT-HG8"
    assert row["discovery_level"] == "DN"
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])
    assert owner["failed_gate"] == "$.hardgate.gates.LAT-HG8.status"
    assert owner["terminal_verdict"] == "rejected"


def test_attribution_capsule_projection_records_operational_and_mechanism_axes(tmp_path):
    _write_all_payloads(tmp_path)
    _write_audit_complete_payload(tmp_path, "gap-head-attribution-capsule")

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-attribution-capsule"]

    assert row["discovery_level"] == "D0"
    assert row["projection_status"] == "two-axis-recorded"
    assert row["base_level"] == "D5-O"
    assert row["base_status"] == "ready"
    assert row["mechanism_level"] == "blocked"
    assert row["mechanism_status"] == "blocked"
    assert row["mechanism_channel"] == "probe-margin-channel"
    assert row["mechanism_failed_gate"] == "A1-HG3"
    assert row["evidence_pointer"] == "$.mechanism_evidence"
    assert row["mechanism_evidence_level"] == "patch"
    assert row["mechanism_evidence_level_pointer"] == "$.mechanism_evidence.evidence_level"
    assert row["operational_pointer"] == "$.d5_o"
    assert row["mechanism_pointer"] == "$.mechanism_evidence"
    assert row["mechanism_case_pointer"] == "$.mechanism_evidence.candidate_mechanism"
    assert row["mechanism_namecert_pointer"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert row["mechanism_ledger_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status"
    assert row["mechanism_closure_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence.mechanism_status"
    assert row["audit_status"] == "valid"


def test_gap_head_mechanism_blockage_projects_negative_owner_row(tmp_path):
    _write_all_payloads(tmp_path)

    owners = discovery_map.build_negative_discovery_owner_rows(root=tmp_path)
    row = {item["report_id"]: item for item in owners}["gap-head-mechanism-blockage"]
    source_payload = _read_json_artifact(tmp_path, row["json_artifact"])

    assert row["negative_id"] == "dn:gap-head-mechanism-blockage"
    assert row["report"] == "gap-head-mechanism-blockage"
    assert row["json_artifact"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert row["failed_gate"] == "$.mechanism_evidence.failed_gate"
    assert row["evidence_pointer"] == "$.mechanism_evidence"
    assert row["debt_row_pointer"] == "$.ledger_debt.0.status"
    assert row["source"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence.failed_gate"
    assert discovery_map.pointer_value(source_payload, row["failed_gate"]) == "A1-HG3"
    assert discovery_map.pointer_value(source_payload, row["evidence_pointer"]) is not None
    assert discovery_map.pointer_value(source_payload, row["debt_row_pointer"]) == "open"
    assert row["audit_status"] == "pass"
    assert row["terminal_verdict"] == "negative_discovery"


def test_gap_head_mechanism_ready_does_not_project_blockage_owner_row(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _minimal_payload(spec)
    payload["mechanism_evidence"]["mechanism_level"] = "D5-M"
    payload["mechanism_evidence"]["mechanism_status"] = "ready"
    payload["d5_m"] = {"status": "ready", "passed": True, "failed_gate": None}
    _write_payload(tmp_path, spec, payload)

    owners = discovery_map.build_negative_discovery_owner_rows(root=tmp_path)

    assert "gap-head-mechanism-blockage" not in {item["report_id"] for item in owners}


def test_gap_head_mechanism_blockage_dangling_pointer_fails_closed(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _minimal_payload(spec)
    payload["mechanism_evidence"]["metric_pointers"]["head_patch_status"] = "$.missing.head_patch_status"
    _write_payload(tmp_path, spec, payload)

    owners = discovery_map.build_negative_discovery_owner_rows(root=tmp_path)

    assert "gap-head-mechanism-blockage" not in {item["report_id"] for item in owners}


@pytest.mark.parametrize("evidence_level", ["observational", "ablation"])
def test_attribution_capsule_noncausal_evidence_level_blocks_d5_m_but_allows_operational_row(tmp_path, evidence_level):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _minimal_payload(spec)
    payload["d5_m"] = {"status": "ready", "passed": True, "failed_gate": None}
    payload["mechanism_evidence"]["mechanism_level"] = "D5-M"
    payload["mechanism_evidence"]["mechanism_status"] = "ready"
    payload["mechanism_evidence"]["evidence_level"] = evidence_level
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-attribution-capsule"]

    assert row["mechanism_level"] == "D5-M"
    assert row["mechanism_evidence_level"] == evidence_level
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "mechanism-causal-evidence-not-ready"


@pytest.mark.parametrize(
    "mutator",
    [
        lambda payload: payload["mechanism_evidence"].pop("evidence_level"),
        lambda payload: payload["mechanism_evidence"].__setitem__("evidence_level", "malformed"),
    ],
)
def test_attribution_capsule_absent_or_malformed_evidence_level_fails_closed(tmp_path, mutator):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _minimal_payload(spec)
    mutator(payload)
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-attribution-capsule"]

    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "attribution-capsule-level-cells-missing"


def test_attribution_capsule_unresolved_evidence_level_pointer_fails_closed(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _minimal_payload(spec)
    payload["mechanism_evidence"].pop("evidence_level")
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-attribution-capsule"]

    assert discovery_map.pointer_value(payload, "$.mechanism_evidence.evidence_level") is None
    assert row["audit_status"] == "invalid"


def test_pointer_value_resolves_bracketed_list_index_and_fails_closed():
    payload = {"rows": [{"status": "ready"}, {"status": "blocked"}]}

    assert discovery_map.pointer_value(payload, "$.rows[0].status") == "ready"
    assert discovery_map.pointer_value(payload, "$.rows[2].status") is None
    assert discovery_map.pointer_value(payload, "$.rows[bad].status") is None


@pytest.mark.parametrize(
    ("mutator", "expected_pointer"),
    [
        (
            lambda payload: payload["mechanism_evidence"]["required_gate_pointers"].__setitem__(
                0,
                "$.a4_hardgates.gates.A4-HG2.missing_status",
            ),
            "$.a4_hardgates.gates.A4-HG2.missing_status",
        ),
        (
            lambda payload: payload["mechanism_evidence"]["metric_pointers"].__setitem__(
                "residualized_status",
                "$.residualized_attribution.missing_status",
            ),
            "$.residualized_attribution.missing_status",
        ),
    ],
)
def test_attribution_capsule_audit_rejects_unresolved_mechanism_evidence_pointer(
    tmp_path,
    mutator,
    expected_pointer,
):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    mutator(payload)
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-attribution-capsule"]

    assert expected_pointer in mechanism_evidence_pointers(
        discovery_map.project_gap_head_mechanism_evidence(payload),
    )
    assert discovery_map.pointer_value(payload, expected_pointer) is None
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-mechanism-evidence-pointer"


@pytest.mark.parametrize("report", ["gap-head-on-h", "gap-head-discovery"])
def test_d4_rows_have_resolvable_control_pointer(tmp_path, report):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()[report]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    context = discovery_map._load_gap_head_d5_context(root=tmp_path)
    projected = discovery_map.projection_payload(spec, payload, context)
    evidence = discovery_map._projection_evidence(spec, payload, context)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D4"
    assert evidence.control_pointer
    assert evidence.scorecard_pointer
    assert discovery_map.pointer_value(payload, evidence.control_pointer) is not None
    artifact, pointer = evidence.scorecard_pointer.split(":", 1)
    assert discovery_map.pointer_value(_read_json_artifact(tmp_path, artifact), pointer) is not None


@pytest.mark.parametrize(
    ("field", "expected_reason"),
    [
        ("scope_pointer", "unresolved-scope-pointer"),
        ("cost_pointer", "unresolved-cost-pointer"),
        ("not_claimed_pointer", "unresolved-not-claimed-pointer"),
    ],
)
def test_positive_row_rejects_unresolved_spec_boundary_pointers(tmp_path, field, expected_reason):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["ledger-aware-transformer"]
    payload = lat_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    _write_json_artifact(tmp_path, spec.json_artifact, payload)
    broken_spec = canonical.CanonicalReportSpec(
        **{
            **spec.__dict__,
            field: "$.missing.pointer",
        }
    )

    row = discovery_map.discovery_row(
        broken_spec,
        payload,
        discovery_map._load_gap_head_d5_context(root=tmp_path),
    )

    assert row["discovery_level"] == "D5-O"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == expected_reason


def test_positive_row_rejects_unresolved_no_control_rationale_pointer(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    payload = _minimal_payload(spec)
    payload["positive_discovery"] = True
    payload["net_positive_signal"] = True
    payload["audit_decision"] = {"audit_status": "valid"}
    payload["main_verdict"] = {
        "surface_delta_count": 1,
        "shift_information": 1,
        "structural_discovery": True,
    }
    payload["evidence_basis"] = {
        "control_positive_discovery": False,
        "scorecard_ready": True,
        "audit_status": "valid",
    }
    broken_spec = canonical.CanonicalReportSpec(
        **{
            **spec.__dict__,
            "no_control_rationale_pointer": "$.missing.rationale",
        }
    )

    status, reason = discovery_map._audit_row(
        broken_spec,
        payload,
        "D4",
        discovery_map.ProjectionEvidence(projection_status="projected"),
    )

    assert status == "invalid"
    assert reason == "unresolved-no-control-rationale-pointer"


def test_gap_head_on_h_current_readiness_stays_d4_with_observed_debt_transfer_missing(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=False)
    _write_audit_complete_payload(tmp_path, "gap-head-on-h")

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert row["robustness_pointer"] == (
        "reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive"
    )
    assert row["adversarial_pointer"] == "reports/canonical/discovery_negative_witnesses.json:$.witnesses"
    assert row["observed_debt_transfer_pointer"] == (
        "reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status"
    )
    assert row["d5_readiness"]["threshold"]["status"] == "pass"
    assert row["d5_readiness"]["ablation"]["status"] == "pass"
    assert row["d5_readiness"]["seed_expansion"]["status"] == "pass"
    assert row["d5_readiness"]["adversarial"]["status"] == "pass"
    assert row["d5_readiness"]["observed_debt_transfer"]["status"] == "missing"


def test_gap_head_on_h_without_audit_source_fails_closed_before_d5_o(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-scope-pointer"


def test_gap_head_on_h_projects_to_d5_o_with_audit_source(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)
    _write_audit_complete_payload(tmp_path, "gap-head-on-h")

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D5-O"
    assert row["audit_status"] == "valid"
    assert row["audit_reason"] == ""
    assert {criterion["status"] for criterion in row["d5_readiness"].values()} == {"pass"}


def test_gap_head_transfer_atlas_without_audit_source_fails_closed(tmp_path):
    _write_all_payloads(tmp_path)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-transfer-atlas"]
    atlas_payload = _read_json_artifact(tmp_path, "reports/canonical/gap_head_transfer_atlas.json")
    claim = atlas_payload["multi_surface_d5_o"]

    assert claim["discovery_level"] == "D5-O"
    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "missing-atlas-boundary-ledger"


def test_gap_head_transfer_atlas_discovery_row_matches_canonical_claim_with_audit_source(tmp_path):
    _write_all_payloads(tmp_path)
    _spec, atlas_payload = _write_audit_complete_payload(tmp_path, "gap-head-transfer-atlas")

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-transfer-atlas"]
    claim = atlas_payload["multi_surface_d5_o"]

    assert row["discovery_level"] == claim["discovery_level"]
    assert claim["decision"] == "pass"
    assert row["terminal_verdict"] == "mechanism_not_closed"
    assert row["projection_status"] == "projected"
    assert row["evidence_pointer"] == "$.multi_surface_d5_o.decision"
    assert row["control_pointer"] == "$.config.control_arm"
    assert row["scorecard_pointer"] == "reports/canonical/quality-scorecard.json:$.rows"
    assert row["audit_status"] == "valid"


def test_gap_head_transfer_atlas_audit_rejects_unresolved_control_pointer(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _minimal_payload(spec)
    payload.update(_atlas_fixture_rows())
    payload["config"].pop("control_arm")
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-transfer-atlas"]

    assert row["discovery_level"] == "DN"
    assert row["control_pointer"] == "$.config.control_arm"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-control-pointer"


def test_gap_head_transfer_atlas_missing_boundary_row_fails_closed(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    payload["boundary_ledger"] = []
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-transfer-atlas"]

    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "missing-atlas-boundary-ledger"


def test_gap_head_transfer_atlas_forbidden_global_claim_term_fails_closed(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    payload["multi_surface_d5_o"]["not_claimed"] = ["global model quality"]
    payload["forbidden_claim_term_audit"] = {
        "status": "fail",
        "hits": ["global model quality"],
    }
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-transfer-atlas"]

    assert row["discovery_level"] == "DN"
    assert "terminal_verdict" not in row
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "atlas-forbidden-claim-term-audit-failed"


def test_gap_head_transfer_atlas_audit_rejects_terminal_claim_mismatch(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    _write_payload(tmp_path, spec, payload)
    evidence = discovery_map.ProjectionEvidence(
        projection_status="projected",
        evidence_pointer="$.multi_surface_d5_o.decision",
        control_pointer="$.config.control_arm",
    )

    status, reason = discovery_map._audit_row(spec, payload, "D5-O", evidence, "pass")

    assert status == "invalid"
    assert reason == "atlas-terminal-claim-verdict-mismatch"


def test_gap_head_transfer_atlas_failed_claim_projects_dn(tmp_path):
    _write_all_payloads(tmp_path)
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _minimal_payload(spec)
    payload.update(_atlas_fixture_rows())
    payload["multi_surface_d5_o"] = {
        "decision": "failed",
        "discovery_level": "DN",
        "pass_surface_count": 3,
        "failed_gates": ["A2-HG4"],
    }
    _write_payload(tmp_path, spec, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["gap-head-transfer-atlas"]
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])

    assert row["discovery_level"] == "DN"
    assert row["negative_report_pointer"].startswith("reports/canonical/negative_discovery_reports.json:$.rows[")
    assert "terminal_verdict" not in row
    assert "failed_gate" not in row
    assert owner["terminal_verdict"] == "rejected"
    assert owner["failed_gate"] == "$.multi_surface_d5_o.decision"
    assert row["audit_status"] == "valid"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"surfaces": [], "not_claimed": ["no observed-debt overclaim"]}),
        _set_nested(("not_claimed",), ["stub"]),
        _pop_nested(("surfaces", 0, "control_verdict")),
        _set_nested(("surfaces", 0, "control_verdict", "positive"), True),
        _pop_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc")),
        _set_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc", "mean"), "0.82"),
        _pop_nested(("surfaces", 0, "hardgates", "HG-A1", "matched_random_auroc")),
        _set_nested(("surfaces", 0, "hardgates", "HG-A1", "learned_auroc", "ci95_low"), 0.49),
    ],
)
def test_gap_head_on_h_d5_readiness_rejects_malformed_transfer_artifact(tmp_path, mutate):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)
    _write_audit_complete_payload(tmp_path, "gap-head-on-h")
    _rewrite_gap_head_d5_artifact(tmp_path, discovery_map.OBSERVED_DEBT_ARTIFACT, mutate)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert row["d5_readiness"]["observed_debt_transfer"]["status"] == "missing"


@pytest.mark.parametrize(
    ("criterion", "artifact", "mutate", "expected_status"),
    [
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A1_threshold_sweep"),
            "missing",
        ),
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A1_threshold_sweep", "treatment_verdict", "positive"), False),
            "missing",
        ),
        (
            "threshold",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A1_threshold_sweep", "treatment_verdict", "positive"), "incomplete"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A2_feature_ablation"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A2_feature_ablation", "status"), "failed"),
            "missing",
        ),
        (
            "ablation",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A2_feature_ablation", "status"), "incomplete"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _without_key("A3_seed_expansion"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A3_seed_expansion", "status"), "incomplete"),
            "missing",
        ),
        (
            "seed_expansion",
            discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
            _set_nested(("A3_seed_expansion", "final_verdict"), "failed"),
            "missing",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _without_key("witnesses"),
            "failed",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _set_nested(("expected_kind_count",), 7),
            "failed",
        ),
        (
            "adversarial",
            discovery_map.NEGATIVE_WITNESSES_ARTIFACT,
            _add_gate_breaking_witness,
            "failed",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _without_key("gap_head_on_h_observed_debt_transfer"),
            "missing",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _set_nested(("gap_head_on_h_observed_debt_transfer", "status"), "failed"),
            "missing",
        ),
        (
            "observed_debt_transfer",
            discovery_map.OBSERVED_DEBT_ARTIFACT,
            _set_nested(("gap_head_on_h_observed_debt_transfer", "status"), "incomplete"),
            "missing",
        ),
    ],
)
def test_gap_head_on_h_d5_readiness_fails_closed_per_real_criterion(
    tmp_path,
    criterion,
    artifact,
    mutate,
    expected_status,
):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)
    _write_audit_complete_payload(tmp_path, "gap-head-on-h")
    _rewrite_gap_head_d5_artifact(tmp_path, artifact, mutate)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    statuses = {name: value["status"] for name, value in row["d5_readiness"].items()}
    assert row["discovery_level"] == "D4"
    assert row["audit_status"] == "valid"
    assert statuses[criterion] == expected_status
    assert {name for name, status in statuses.items() if status != "pass"} == {criterion}


def test_gap_head_on_h_d5_o_claim_with_unresolved_pointer_is_invalid(monkeypatch):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = _audit_complete_payload(spec, _minimal_payload(spec))
    context = {
        discovery_map.QUALITY_SCORECARD_ARTIFACT: _scorecard_payload(),
        discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT: {"final_status": "pass"},
    }
    ledger = discovery_map.GapHeadD5ReadinessLedger(
        criteria=(
            discovery_map.GapHeadD5Criterion(
                name="threshold",
                status="pass",
                artifact=discovery_map.GAP_HEAD_ROBUSTNESS_ARTIFACT,
                pointer="$.missing_positive_cell",
                reason="fixture",
            ),
        )
    )

    def fake_readiness(context):
        return ledger

    monkeypatch.setattr(discovery_map, "_gap_head_d5_readiness", fake_readiness)

    row = discovery_map.discovery_row(
        spec,
        payload,
        context,
    )

    assert row["discovery_level"] == "D5-O"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "unresolved-d5-pointer-threshold"


def test_adversarial_witness_count_does_not_create_positive_discovery(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True, witness_count=8)
    spec = canonical._specs_by_name()["gap-head-on-h"]
    _write_payload(
        tmp_path,
        spec,
        {
            "treatment_verdict": {"positive": False},
            "control_protocol": {"same_budget_as_treatment": True},
            "control_verdict": {"positive": False},
        },
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["gap-head-on-h"]

    assert row["d5_readiness"]["adversarial"]["status"] == "pass"
    assert row["discovery_level"] == "D0"
    assert row["classifier_reasons"] == ["no classifier shift or debt improvement"]


def test_discovery_map_has_no_generic_d5_level(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert all(row["discovery_level"] != "D5" for row in payload["rows"])
    assert "D5" not in payload["level_counts"]


def test_positive_discovery_rows_have_resolvable_gate_pointers(tmp_path):
    _write_all_payloads(tmp_path)
    _write_gap_head_d5_context(tmp_path, transfer_metric=True)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    for row in payload["rows"]:
        if row["discovery_level"] not in {"D4", "D5-O", "D5-M"}:
            continue
        source = _read_json_artifact(tmp_path, row["json_artifact"])
        assert discovery_map.pointer_value(source, row["evidence_pointer"]) is not None
        assert discovery_map.pointer_value(source, row["control_pointer"]) is not None
        scorecard_artifact, scorecard_pointer = row["scorecard_pointer"].split(":", 1)
        assert discovery_map.pointer_value(_read_json_artifact(tmp_path, scorecard_artifact), scorecard_pointer) is not None
        if row["discovery_level"] in {"D5-O", "D5-M"} and "robustness_pointer" in row:
            robustness_artifact, robustness_pointer = row["robustness_pointer"].split(":", 1)
            assert discovery_map.pointer_value(_read_json_artifact(tmp_path, robustness_artifact), robustness_pointer) is not None
            if row["discovery_level"] == "D5-M":
                if ":" in row["mechanism_pointer"]:
                    mechanism_artifact, mechanism_pointer = row["mechanism_pointer"].split(":", 1)
                    assert discovery_map.pointer_value(_read_json_artifact(tmp_path, mechanism_artifact), mechanism_pointer) is not None
                else:
                    assert discovery_map.pointer_value(source, row["mechanism_pointer"]) is not None
                if ":" in row["mechanism_case_pointer"]:
                    mechanism_case_artifact, mechanism_case_pointer = row["mechanism_case_pointer"].split(":", 1)
                    assert discovery_map.pointer_value(_read_json_artifact(tmp_path, mechanism_case_artifact), mechanism_case_pointer) is not None
                else:
                    assert discovery_map.pointer_value(source, row["mechanism_case_pointer"]) is not None


@pytest.mark.parametrize(
    "mutation",
    (
        lambda payload: payload.pop("route_patch_protocol"),
        lambda payload: payload["hardgate"]["gates"].pop("CGA-HG6"),
        lambda payload: (
            payload.__setitem__("entropy_only_control", payload["route_patch_protocol"]["entropy_only_control"]),
            payload["discovery_map_signal"].__setitem__("control_pointer", "$.entropy_only_control"),
        ),
    ),
)
def test_certificate_gated_attention_stale_route_payload_fails_closed(tmp_path, mutation):
    spec = canonical._specs_by_name()["certificate-gated-attention"]
    payload = _minimal_payload(spec)
    mutation(payload)
    _write_payload(tmp_path, spec, payload)

    discovery = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path, canonical_reports=(spec,))
    row = discovery["rows"][0]

    assert row["discovery_level"] == "DN"
    assert row["audit_status"] == "invalid"
    assert row.get("control_pointer") != "$.entropy_only_control"


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("certificate-guided-training", "$.claim_capsule.terminal_verdict"),
        ("certificate-guided-discovery", "$.positive_discovery"),
        ("gap-head-ablation", "$.hardgate.status"),
        ("spectral-ablation-hinge", "$.negative_control_summary.treatment_better_than_all_controls"),
    ],
)
def test_dn_rows_have_failed_gate_pointing_to_negative_cell(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "DN"
    assert evidence.failed_gate == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


def test_certificate_training_discovery_map_preserves_claim_capsule_terminal_verdict(tmp_path):
    spec = canonical._specs_by_name()["certificate-guided-training"]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    row = discovery_map.discovery_row(spec, payload)

    assert projected["verdict"] == payload["claim_capsule"]["terminal_verdict"]
    assert row["terminal_verdict"] == payload["claim_capsule"]["terminal_verdict"]
    assert row["discovery_level"] == "DN"
    assert row["evidence_pointer"] == "$.arm_protocol.compat_roles.after"
    assert row["evidence_label"] == "constraint_lagrangian"
    assert row["failed_gate"] == "$.claim_capsule.terminal_verdict"
    assert discovery_map.pointer_value(payload, "$.arm_protocol.compat_roles.after") == "constraint_lagrangian"


@pytest.mark.parametrize(
    ("report", "expected_pointer"),
    [
        ("mixing-family-sweep", "$.coverage_item.debt_item"),
        ("anisotropic-ou-sweep", "$.transition_debt_by_grid"),
        ("nongaussian-distribution-sweep", "$.negative_result_ledger"),
    ],
)
def test_d1_rows_have_debt_row_pointer_to_real_evidence(tmp_path, report, expected_pointer):
    spec = canonical._specs_by_name()[report]
    payload = _minimal_payload(spec)
    projected = discovery_map.projection_payload(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)
    verdict = discovery_map.assign_discovery_level(projected)

    assert verdict.discovery_level == "D1"
    assert evidence.debt_row_pointer == expected_pointer
    assert discovery_map.pointer_value(payload, expected_pointer) is not None


def test_run_reports_index_contains_discovery_map(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)

    def fake_run_producer(spec):
        _write_payload(tmp_path, spec, _minimal_payload(spec))
        markdown = tmp_path / spec.markdown_artifact
        markdown.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert (tmp_path / "reports" / "canonical" / "discovery_map.json").exists()
    assert (tmp_path / "reports" / "canonical" / "discovery_map.md").exists()


def test_strict_manifest_audit_marks_missing_control_invalid(tmp_path):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = {"treatment_verdict": {"positive": True}, "control_verdict": {"positive": False}}
    row = discovery_map.discovery_row(spec, payload)

    assert row["discovery_level"] == "DN"
    assert row["classifier_reasons"] == ["scorecard_ready=false", "audit_pass=false"]

    _write_all_payloads(tmp_path)
    _write_payload(tmp_path, spec, payload)
    discovery_map.write_discovery_map(root=tmp_path, generated_at="fixture-time")
    with pytest.raises(SystemExit):
        old_root = discovery_map.ROOT
        try:
            discovery_map.ROOT = tmp_path
            discovery_map.main(["--strict-manifest-audit"])
        finally:
            discovery_map.ROOT = old_root


def test_manifest_audit_reports_unregistered_json_and_strict_fails(tmp_path):
    _write_all_payloads(tmp_path)
    unregistered = tmp_path / "reports" / "canonical" / "unregistered-extra.json"
    unregistered.write_text(json.dumps({"schema_id": "fixture"}) + "\n", encoding="utf-8")

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert payload["manifest_audit"]["unregistered_json_artifacts"] == [
        "reports/canonical/unregistered-extra.json",
    ]

    old_root = discovery_map.ROOT
    try:
        discovery_map.ROOT = tmp_path
        with pytest.raises(SystemExit) as excinfo:
            discovery_map.main(["--strict-manifest-audit"])
    finally:
        discovery_map.ROOT = old_root

    assert excinfo.value.code == 1


def test_manifest_audit_registers_formal_hardening_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    formal = tmp_path / "reports" / "canonical" / "formal_hardening.json"
    formal.write_text(
        json.dumps(
            {
                "artifact_id": "bedc-quality-lab:formal-hardening",
                "ready": False,
                "verification_ledger": [],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert "reports/canonical/formal_hardening.json" not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_manifest_audit_registers_observed_debt_transfer_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.OBSERVED_DEBT_ARTIFACT,
        {
            "artifact_id": "bedc-quality-lab:gap-head-observed-debt-transfer",
            "gap_head_on_h_observed_debt_transfer": {"status": "failed"},
            "surfaces": [{"verdict": {"status": "failed"}}],
            "hardgate_evidence": {"HG-A5": {"status": "fail"}},
            "not_claimed": ["fixture"],
        },
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert discovery_map.OBSERVED_DEBT_ARTIFACT not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_manifest_audit_registers_dimension_mismatch_pointer_artifact(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="failed"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)

    assert discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT not in payload["manifest_audit"]["unregistered_json_artifacts"]


def test_dimension_mismatch_pass_with_scale_leakage_projects_terminal_dn(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="pass"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["dimension-mismatch-debt-transfer"]
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])

    assert row["discovery_level"] == "DN"
    assert "anti_triviality_status" not in row
    assert "effective_level" not in row
    assert "downgrade_reason" not in row
    assert "terminal_verdict" not in row
    assert owner["anti_triviality_status"] == "scale_leakage_detected"
    assert owner["effective_level"] == "DN"
    assert owner["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"
    assert owner["terminal_verdict"] == "negative_discovery"
    assert row["audit_status"] == "valid"
    assert owner["failed_gate"] == "$.dimension_mismatch_debt_transfer.anti_triviality_status"
    assert owner["hypothesis"] == "fixture hypothesis"
    assert owner["what_was_learned"] == "fixture learned"
    assert "control_pointer" not in row
    assert "d5_readiness" not in row


def test_dimension_mismatch_source_pass_keeps_canonical_d4_terminal(tmp_path):
    _write_all_payloads(tmp_path)
    canonical_payload = _dimension_mismatch_payload(
        status="pass",
        anti_triviality_status="anti_triviality_passed",
    )
    canonical_payload["audit_decision"] = {"audit_status": "pass"}
    _write_json_artifact(tmp_path, discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT, canonical_payload)

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["dimension-mismatch-debt-transfer"]
    claim = canonical_payload["dimension_mismatch_debt_transfer"]

    assert claim["effective_level"] == "D4"
    assert claim["terminal_verdict"] == "source_pass"
    assert row["effective_level"] == claim["effective_level"]
    assert row["discovery_level"] == claim["discovery_level"]
    assert row["terminal_verdict"] == claim["terminal_verdict"]
    assert row["projection_status"] == "projected"
    assert row["evidence_pointer"] == discovery_map.DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER
    assert row["audit_status"] == "valid"
    assert "failed_gate" not in row
    assert row["control_pointer"] == "$.hardgate_evidence.HG-B3.matched_random_positive"
    assert "d5_readiness" not in row


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"hardgate_evidence": {}, "not_claimed": ["no dimension-mismatch overclaim"]}),
        _set_nested(("not_claimed",), ["stub"]),
        _pop_nested(("hardgate_evidence", "HG-B3", "matched_random_auroc")),
        _set_nested(("hardgate_evidence", "HG-B3", "matched_random_positive"), True),
        _set_nested(("hardgate_evidence", "HG-B3", "learned_auroc", "ci95_low"), 0.49),
    ],
)
def test_dimension_mismatch_pass_rejects_malformed_transfer_artifact(tmp_path, mutate):
    _write_all_payloads(tmp_path)
    payload = _dimension_mismatch_payload(status="pass")
    mutate(payload)
    _write_json_artifact(tmp_path, discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT, payload)

    discovery_payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(discovery_payload)["dimension-mismatch-debt-transfer"]

    assert row["projection_status"] == "source-insufficient"
    assert row["evidence_pointer"] == discovery_map.DIMENSION_MISMATCH_TRANSFER_POINTER
    assert "control_pointer" not in row
    assert row["discovery_level"] != "D4"
    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "dimension-mismatch-discovery-level-disagrees-with-canonical-effective-level"


def test_dimension_mismatch_failed_projects_dn_with_failed_gate(tmp_path):
    _write_all_payloads(tmp_path)
    _write_json_artifact(
        tmp_path,
        discovery_map.DIMENSION_MISMATCH_TRANSFER_ARTIFACT,
        _dimension_mismatch_payload(status="failed"),
    )

    payload = discovery_map.build_discovery_map(generated_at="fixture-time", root=tmp_path)
    row = _row_by_report(payload)["dimension-mismatch-debt-transfer"]
    owner = _owner_by_pointer(tmp_path, row["negative_report_pointer"])

    assert row["discovery_level"] == "DN"
    assert row["audit_status"] == "valid"
    assert "failed_gate" not in row
    assert "terminal_verdict" not in row
    assert owner["failed_gate"] == "$.dimension_mismatch_debt_transfer.status"
    assert owner["terminal_verdict"] == "negative_discovery"

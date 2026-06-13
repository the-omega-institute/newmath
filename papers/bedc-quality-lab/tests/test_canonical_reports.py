import json
import os
from pathlib import Path
import re
import sys
import types

import pytest

from bedc_quality_lab.discovery_regularized_training import (
    MECHANISM_ABLATION_REQUIRED_ARMS,
    certificate_guided_dn_preservation,
    default_drt_training_extension_spec,
    project_drt_training_extension,
    _training_mechanism_cert,
)
from bedc_quality_lab.claim_complexity import DIMENSION_NAMES
from bedc_quality_lab.transformer_derivative_atlas import (
    ATTENTION_ROUTE_ARTIFACT,
    DEFAULT_CONFIG as TRANSFORMER_DERIVATIVE_ATLAS_CONFIG,
    LAYERWISE_JET_MAP_ARTIFACT,
    RAW_ROW_POINTER as TRANSFORMER_DERIVATIVE_RAW_ROW_POINTER,
    TransformerDerivativeAtlasProjection,
    render_attention_route_report,
)
from scripts import run_formal_hardening_report as formal_hardening
from scripts import run_claim_verdict_demo as claim_verdict_demo
from scripts import run_canonical_reports as canonical
from scripts import run_certificate_gated_attention as cga_runner
from scripts import run_certificate_guided_constraint_training as cgt_runner
from scripts import run_gap_head_attribution_capsule as attribution_capsule
from scripts import run_discovery_map as discovery_map
from scripts import run_discovery_regularized_training as runner
from scripts import run_mechanism_seeking_network as msn_runner
from scripts import run_sigreg_mini_grid as sigreg_grid_runner
from scripts import run_sigreg_training_proxy as sigreg_proxy_runner
from bedc_quality_lab.discovery_compiler.map import validate_coverage_matrix, validate_discovery_map_payload
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer, split_artifact_pointer
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.order_k_benchmark import OrderKBenchmarkProjection


HG_P_CORE = {
    "mixing-family-sweep",
    "anisotropic-ou-sweep",
    "gap-head-on-h",
    "gap-head-discovery",
    "gap-head-ablation",
    "irreducibility-report",
    "ledger-aware-transformer",
    "certificate-gated-attention",
    "gap-head-threshold-frontier",
    "gap-head-transfer-atlas",
    "gap-head-attribution-capsule",
    "certificate-guided-training",
    "certificate-guided-discovery",
    "sigreg-training-proxy",
    "sigreg-mini-grid",
    "discovery-regularized-training",
    "mechanism-seeking-network",
    "discovery-gated-transformer",
    "high-impact-review",
    "order-k-benchmark",
}
QUALITY_SCORECARD_METRICS = {
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
}
MODEL_DESIGN_FIXTURE_ARTIFACT_IDS = {
    "ledger-aware-transformer": "bedc-quality-lab:ledger-aware-transformer",
    "certificate-gated-attention": "bedc-quality-lab:certificate-gated-attention",
    "discovery-regularized-training": "bedc-quality-lab:discovery-regularized-training",
    "mechanism-seeking-network": "bedc-quality-lab:mechanism-seeking-network",
    "discovery-gated-transformer": "bedc-quality-lab:discovery-gated-transformer",
}


def _matched_random_audit_fixture() -> dict[str, object]:
    return {
        "parameter_match": True,
        "compute_match": True,
        "threshold_match": True,
        "surface_distribution_match": True,
        "metric_helper_match": True,
        "audit_status": "pass",
        "failure_reasons": [],
        "evidence_pointers": {
            key: [f"fixture:{key}"]
            for key in (
                "parameter_match",
                "compute_match",
                "threshold_match",
                "surface_distribution_match",
                "metric_helper_match",
            )
        },
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


def _drt_mechanism_ablation_fixture() -> dict[str, object]:
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


def _payload_for_spec(spec):
    if spec.name == "order-k-benchmark":
        return OrderKBenchmarkProjection.project(generated_at="fixture", seed=1004)
    if spec.name == "dgt-l0-controls":
        from bedc_quality_lab import dgt_l0_controls
        from bedc_quality_lab.construct_validity import ConstructValidityEvidence, construct_validity_projection

        payload = dgt_l0_controls.build_payload(generated_at="fixture", requested_device="cpu")
        public_payload = {key: value for key, value in payload.items() if key != "_raw_records"}
        public_payload["construct_validity_hardgates"] = construct_validity_projection(
            ConstructValidityEvidence(
                task_variables={"variables": ["x"]},
                label_variables={"variables": ["q"]},
                arm_input_access={
                    "label_invisibility_certificate": True,
                    "arms": {
                        "candidate": {"variables": ["x"], "label_variables": []},
                        "control": {"variables": ["x"], "label_variables": []},
                    },
                },
                arm_roles={"candidate": "candidate", "controls": ["control"]},
                finite_table={"support_count": 1, "rule_abstraction_claim": False, "coverage_status": "bounded-control"},
                hand_feature_ledger={"mode": "no-gate", "features": [], "candidate_only_features": []},
                metric_source={"source_kind": "held-out-evaluation", "metric_keys": ["accuracy"]},
            ),
            artifact=dgt_l0_controls.CANONICAL_JSON_ARTIFACT,
            pointer="$.construct_validity_hardgates",
        )
        return public_payload
    if spec.name == "dgt-l1-controls":
        from bedc_quality_lab import dgt_l1_controls

        payload = dgt_l1_controls.build_payload(generated_at="fixture", requested_device="cpu")
        return {key: value for key, value in payload.items() if key != "_raw_records"}
    if spec.name == "reproduction-package":
        from bedc_quality_lab import reproduction_package

        return reproduction_package.build_package(canonical.ROOT, generated_at="fixture")
    if spec.name == "reproduction-check-result":
        from bedc_quality_lab import reproduction_package

        package = reproduction_package.build_package(canonical.ROOT, generated_at="fixture")
        return reproduction_package.verify_package(package, canonical.ROOT, "structural", generated_at="fixture")
    if spec.name == "dgt-l1-boundary-report":
        from bedc_quality_lab import dgt_l1_boundary_report

        return dgt_l1_boundary_report.build_l1_boundary_report(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "winnability-certificates":
        from bedc_quality_lab import winnability

        split = {
            "experiment_id": "fixture",
            "task_id": "fixture-task",
            "task_family": "analytic-visibility",
            "resolver_family": "analytic-visibility",
            "split_id": "fixture-split",
            "split_kind": "held-out",
            "split_fingerprint": "fixture-fingerprint",
            "source_evidence_ref": "reports/canonical/fixture.json:$.row",
            "label_function_ref": "fixture.label",
            "visible_variables_ref": "reports/canonical/input-accessibility.json:$.visible",
            "required_variables_ref": "reports/canonical/input-accessibility.json:$.required",
            "visible_variables": ["x_left"],
            "required_variables": ["x_left"],
            "allow_inline_input_fixture": True,
            "chance_accuracy": 0.5,
            "observed_accuracy": 0.75,
        }
        return winnability.build_payload(root=canonical.ROOT, generated_at="fixture", registered_splits=[split])
    if spec.name == "dgt-neural-ablation":
        from bedc_quality_lab import dgt_neural_ablation

        return dgt_neural_ablation.build_payload(generated_at="fixture", requested_device="cpu")
    if spec.name == "dgt-ablation-null-decomposition":
        from bedc_quality_lab import dgt_ablation_null_decomposition

        return dgt_ablation_null_decomposition.build_payload(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "dgt-component-redundancy-audit":
        from bedc_quality_lab import dgt_component_redundancy_audit

        return dgt_component_redundancy_audit.build_payload(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "dgt-base-undertraining-audit":
        from bedc_quality_lab import dgt_base_undertraining_audit

        return dgt_base_undertraining_audit.build_payload(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "scaling-ladder":
        from bedc_quality_lab.scaling_ladder import build_scaling_ladder_payload

        return build_scaling_ladder_payload(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "fair-l1-decision":
        from bedc_quality_lab import fair_l1_decision

        return fair_l1_decision.build_payload(root=canonical.ROOT, generated_at="fixture")
    if spec.name == "dgt-model-card":
        return {
            "schema_id": canonical.DGT_MODEL_CARD_SCHEMA_ID,
            "card_id": canonical.DGT_MODEL_CARD_ARTIFACT_ID,
            "generated_at": "fixture",
            "status": "blocked",
            "source_artifacts": [],
            "intended_use": [],
            "not_intended_use": [
                {
                    "literal": literal,
                    "source_owner": "maintainer-policy",
                    "source_pointer": "github:issue:1220",
                }
                for literal in (
                    "bounded BEDC prototype",
                    "not production model",
                    "not LLM replacement",
                    "not global Transformer superiority",
                    "current L1 evidence invalid as fair architecture comparison",
                )
            ],
            "known_failure_modes": [],
            "evaluation_boundaries": [],
            "training_facts": {
                "protocol_pointers": [],
                "metric_cells": [],
                "evidence_provenance": {
                    "status": "blocked",
                    "source_owner": "canonical-index-evidence-provenance",
                    "source_pointer": "reports/canonical/index.json:$.evidence_provenance",
                },
            },
            "upstream_status": [],
            "card_hardgates": {"status": "blocked", "gates": {}},
            "not_claimed": ["fixture"],
        }
    if spec.name == "discovery-gated-transformer":
        from scripts import run_discovery_gated_transformer as dgt_runner

        return dgt_runner.build_payload(generated_at="fixture")
    if spec.name == "certificate-guided-training":
        payload = cgt_runner._payload(run_id="fixture", generated_at="fixture")
        return cgt_runner._public_payload(payload)
    if spec.name == "sigreg-training-proxy":
        payload = sigreg_proxy_runner.build_payload(generated_at="fixture", use_torch=False)
        return sigreg_proxy_runner.canonical_summary_payload(payload)
    if spec.name == "sigreg-mini-grid":
        return sigreg_grid_runner.build_projection(generated_at="fixture")["summary_payload"]
    if spec.name == "mechanism-seeking-network":
        return msn_runner.build_projection(generated_at="fixture")["summary_payload"]
    if spec.name == "model-comparison":
        return {
            "schema_id": canonical.MODEL_COMPARISON_SCHEMA_ID,
            "artifact_id": canonical.MODEL_COMPARISON_ARTIFACT_ID,
            "generated_at": "fixture-generated-at",
            "status": "not_ready",
            "ranking_key": list(canonical.MODEL_COMPARISON_RANKING_KEY),
            "hardgates": {
                gate_id: {"gate_id": gate_id, "status": "fail", "reason": "fixture"}
                for gate_id in canonical.MODEL_COMPARISON_HARDGATE_IDS
            },
            "not_claimed": ["fixture"],
            "models": [],
            "source_reports": [],
            "ordering": {"status": "not_ready"},
        }
    if spec.name == "high-impact-review":
        return {
            "schema_id": "bedc-quality-lab:high-impact-review",
            "artifact_id": "bedc-quality-lab:high-impact-review",
            "generated_at": "fixture-generated-at",
            "seed": 1131,
            "source_artifacts": {
                "dgt": "reports/canonical/discovery-gated-transformer.json",
                "model_comparison": "reports/canonical/model-comparison.json",
                "claim_graph": "reports/canonical/claim_graph.json",
            },
            "review_rows": [
                {
                    "claim_id": "claim:discovery-gated-transformer",
                    "status": "fail",
                    "review_level": "bounded-D4-terminal-gate",
                    "review_scope": "DGT bounded deterministic toy D4 positive-discovery terminal promotion only",
                    "ledger_pointer": "reports/canonical/high-impact-review.json:$.review_rows[0]",
                    "claim_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
                    "hardgate_pointer": "reports/canonical/high-impact-review.json:$.hardgates",
                    "not_claimed_pointer": "reports/canonical/high-impact-review.json:$.not_claimed",
                    "reason": "high-impact-review-required",
                }
            ],
            "hardgates": {
                f"HIR-HG{index}": {
                    "status": "fail",
                    "reason": "fixture; fail-closed",
                    "evidence_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
                }
                for index in range(1, 11)
            },
            "not_claimed": [
                "Bounded D4 prototype only.",
                "No production deployment authority is claimed.",
                "No global model superiority claim is made.",
                "No LLM replacement claim is made.",
                "No universal training recipe is claimed.",
                "No full BEDC closure is claimed.",
            ],
        }
    payload = {key: f"fixture-{key}" for key in spec.required_json_keys}
    if spec.name in MODEL_DESIGN_FIXTURE_ARTIFACT_IDS:
        payload["artifact_id"] = MODEL_DESIGN_FIXTURE_ARTIFACT_IDS[spec.name]
    payload.update(
        {
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "canonical_runner": "scripts/run_gaussian_ou_lejepa.py",
                "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            },
            "applicability_boundary": {
                "claimed_scope": "fixture scope",
                "not_claimed": "fixture nonclaim",
                "forbidden_inference_columns": ["z"],
            },
            "coverage_item": {"status": "fixture"},
            "transition_debt_by_grid": {"cell": {"status": "fixture"}},
            "config": {"arm": "baseline-only"},
            "control_protocol": {"status": "fixture", **_matched_random_audit_fixture()},
            "treatment_verdict": {"positive": spec.name == "gap-head-on-h"},
            "control_verdict": {"positive": False},
            "boundary_checks": {
                "forbidden_inference_columns": ["z"],
                "representation_boundary": "learned_h",
            },
            "claim_boundary": {
                "C4": {
                    "claim_surface": "observed-debt-availability-probe",
                    "evidence_pointer": "reports/gaussian_ou_dynamics_planning.json:$.applicability_boundary",
                    "not_claimed": [
                        "no full world model planning claim",
                        "no action-transition certificate",
                    ],
                }
            },
            "score_terms": {"status": "fixture"},
            "matched_random_control": {
                "status": "fixture",
                **_matched_random_audit_fixture(),
                "control_verdict": {"positive": False},
                "control_projection": {"positive_discovery": True},
            },
            "matched_controls": {"status": "pass"},
            "patch_records": [{"patch_type": "fixture", "status": "pass"}],
            "patch_types": ["fixture"],
            "side_effect_ledger": [{"status": "present"}],
            "hardgates": {"PATCH-HG1": {"status": "present-but-fail-closed"}},
            "dgt_mechanism_cert": {"status": "present-but-fail-closed"},
            "objective": {"required_rows": ["fixture"]},
            "cost_protocol": {"name": "fixture"},
            "not_claimed": ["fixture nonclaim"],
            "scope": {"not_claimed": ["fixture nonclaim"]},
            "claim_gate": {
                "status": "fixture",
                "audit_improvement_tradeoff": spec.name == "certificate-guided-training",
                "training_audit_improvement_tradeoff": spec.name == "certificate-guided-discovery",
            },
            "paired_seed_protocol": {"status": "fixture"},
            "arm_protocol": {"status": "fixture"},
            "arm_summaries": {"status": "fixture"},
            "grid_summary": {"record_count": 1, "by_arm": {"constraint_lagrangian": {"record_count": 1}}},
            "grid_metrics_artifact": "reports/runs/certificate-guided-constraint-training/grid_metrics.jsonl",
            "grid_summary_artifact": "reports/runs/certificate-guided-constraint-training/grid_summary.jsonl",
            "raw_metrics_artifact": "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl",
            "raw_metrics_record_count": 56,
            "raw_grid_record_count": 3024,
            "main_claim_status": "fixture status",
            "final_main_claim_status": "fixture status",
            "hardgate": {"status": "fail" if spec.name == "gap-head-ablation" else "pass"},
            "failed_gate": None,
            "verdict": "accepted",
            "discovery_level": "D0",
            "metrics": {
                "delta_debt": -0.25,
                "delta_benefit": -0.10,
                "delta_cost": 0.0,
                "delta_quality_q": 0.15,
                "UER": {"mean": 0.1},
                "FalseLedgerRate": {"mean": 0.05},
                "positive_quality_gate": False,
                "positive_discovery": False,
                "audit_improvement_tradeoff": spec.name == "certificate-guided-training",
                "ParetoDominance": False,
            },
            "claim_capsule": {
                "schema_id": "bedc.quality.claim_capsule",
                "terminal_verdict": "DN(audit-improvement-tradeoff)",
                "failed_gate": "audit-improvement-tradeoff" if spec.name == "certificate-guided-training" else None,
            },
            "readiness": {"status": "D4-at-threshold"},
            "threshold_curve": [
                {
                    "threshold": 0.05,
                    "metrics": {
                        "AUROC": {"mean": 0.6, "std": 0.0, "n": 2, "ci95_low": 0.6, "ci95_high": 0.6},
                        "UnloggedErrorRate": {"mean": 0.1, "std": 0.0, "n": 2, "ci95_low": 0.1, "ci95_high": 0.1},
                        "LoggedFalseAlarmRate": {"mean": 0.2, "std": 0.0, "n": 2, "ci95_low": 0.2, "ci95_high": 0.2},
                        "CriticalUnloggedErrorRate": {"mean": 0.1, "std": 0.0, "n": 2, "ci95_low": 0.1, "ci95_high": 0.1},
                        "QualityQ": {"mean": 0.3, "std": 0.0, "n": 2, "ci95_low": 0.3, "ci95_high": 0.3},
                        "NetInformation": {"mean": 1.2, "std": 0.0, "n": 2, "ci95_low": 1.2, "ci95_high": 1.2},
                    },
                }
            ],
            "threshold_summary": {
                "control_baseline": [
                    {
                        "threshold": 0.05,
                        "metrics": {
                            "CriticalUnloggedErrorRate": {"mean": 0.2, "std": 0.0, "n": 2, "ci95_low": 0.2, "ci95_high": 0.2}
                        },
                    }
                ]
            },
            "pareto_axis_spec": {
                "x": "AUROC",
                "x_direction": "maximize",
                "y": "CriticalLoggedCoverage",
                "y_definition": "1 - CriticalUnloggedErrorRate",
                "y_direction": "maximize",
            },
            "pareto_frontier": [
                {
                    "threshold": 0.05,
                    "metrics": {
                        "AUROC": {"mean": 0.6, "std": 0.0, "n": 2, "ci95_low": 0.6, "ci95_high": 0.6},
                        "CriticalLoggedCoverage": {"mean": 0.9, "std": 0.0, "n": 2, "ci95_low": 0.9, "ci95_high": 0.9},
                    },
                }
            ],
            "factor_attribution": {
                "learned_head": {
                    "auroc_delta": -0.2,
                    "status": "pass",
                }
            },
            "positive_discovery_pointer": "$.factor_attribution.learned_head.auroc_delta",
            "matched_random_baseline": {"status": "fixture", "positive_discovery": False},
            "negative_result_ledger": [{"status": "fixture"}],
            "ledger_summary": {
                "status": "negative" if spec.name == "spectral-ablation-hinge" else "fixture",
                "basis": {
                    "hardening_coverage": {
                        "recorded": 3,
                        "required": 4,
                        "items": [
                            {"name": "sameClass equivalence", "recorded": True},
                            {"name": "margin stability", "recorded": True},
                            {"name": "finite ledger coverage", "recorded": False},
                            {"name": "missing-row negative example", "recorded": True},
                        ],
                    }
                },
            },
            "negative_control_summary": {"status": "fixture", "treatment_better_than_all_controls": False},
            "surface_delta_count": 2,
            "positive_discovery": spec.name == "gap-head-discovery",
            "classifier_state": {
                "recorded_ledger_rows": 3,
                "required_ledger_rows": 4,
            },
            "debt_terms": {"classifier_ledger_rows": 0.25},
            "audit_decision": {"audit_status": "pass", "overclaim_rate": 0.4},
            "result": {"status": "negative" if spec.name == "certificate-guided-training" else "fixture"},
            "deltas": {"after_minus_before": {"debt_delta": -0.25}},
            "verdicts": [{"deltas": {"debt_delta": -0.25}}],
            "surface_registry": _atlas_fixture_rows()["surface_registry"],
            "surfaces": _atlas_fixture_rows()["surfaces"],
            "boundary_ledger": _atlas_fixture_rows()["boundary_ledger"],
            "hardgate_evidence": {"A2-HG5": {"status": "pass"}, "C-HG5": {"status": "pass"}},
            "global_claim_flag": False,
            "multi_surface_d5_o": {"decision": "pass", "discovery_level": "D5-O", "pass_surface_count": 3},
            "prior_observation_packet": {
                "status": "prior_observation",
                "counts_as_a2_hg_pass_evidence": False,
                "packet_pointer": "$.prior_observation_packet",
                "observations": {},
            },
            "run_id": "fixture-run",
            "run_artifacts": {
                "claim_capsule": "reports/runs/fixture/claim_capsule.json",
                "raw_metrics": "reports/runs/fixture/raw_metrics.jsonl",
                "summary": "reports/runs/fixture/summary.json",
                "report": "reports/runs/fixture/report.md",
            },
            "objective": {
                "required_rows": ["fixture"],
                "id": "sigreg_sliced_cf_training_proxy",
                "loss": "(1-lambda)*alignment + lambda*sigreg_sliced_cf",
            },
            "arm_protocol": {
                "exact_arm_count": 4,
                "arms": [
                    "covariance_proxy_current",
                    "true_sigreg_sliced_cf",
                    "vicreg_like_covariance",
                    "alignment_only",
                ],
            },
            "d1_evidence": {
                "debt_delta": -1.0,
                "d1_hardgates": {
                    "D1-HG1": {"status": "pass"},
                    "D1-HG2": {"status": "pass"},
                    "D1-HG3": {"status": "pass"},
                    "D1-HG4": {"status": "pass"},
                    "D1-HG5": {"status": "pass"},
                },
            },
            "positive_claim": {"text": "fixture D1 SIGReg training proxy", "scope": "fixture", "level": "D1"},
            "records": {
                "matched_random_control": _matched_random_audit_fixture(),
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
            "mechanism_gate_summary": {
                "accepted": True,
                "accepted_surface_count": 3,
                "by_mechanism": {
                    "copy_route": {"accepted": True},
                    "parity_gate": {"accepted": True},
                    "sparse_recall": {"accepted": True},
                },
            },
            "discovery_map_signal": {
                "status": "d5-m-candidate",
                "level_candidate": "D5-M",
                "reason": "distinction-module-evidence-present",
            },
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
                "status": "ready",
                "passed": True,
                "failed_gate": None,
                "hardgate_pointer": "$.hardgate.gates.MSN-HG6.status",
                "distinction_module_evidence_ref": "$.distinction_module_evidence",
                "d5_o_source_pointer": "$.source_artifacts.d5_o_source",
            },
            "gate_protocol": {"status": "fixture", "evidence_pointer": "$.mechanism_gate_summary"},
            "torch_evidence": {"status": "unavailable", "row_count": 0},
            "claim_capsule_ref": {
                "artifact": "reports/runs/fixture/claim_capsule.json",
                "pointer": "$",
            },
            "result_snapshot_ref": {
                "artifact": "reports/runs/fixture/result_snapshot.json",
                "pointer": "$",
            },
            "full_lejepa_boundary": {
                "claim": False,
                "required_to_claim": ["2D mixings", "grid", "distribution sweep"],
            },
            "what_was_learned": "fixture",
            "failed_gate": None,
            "forbidden_claim_term_audit": {"status": "pass", "hits": []},
        }
    )
    if spec.name == "gap-head-on-h":
        payload["records"] = [{"matched_random_control": _matched_random_audit_fixture()}]
    if spec.name == "irreducibility-report":
        payload.update(
            {
                "schema_id": canonical.IRREDUCIBILITY_REPORT_ARTIFACT_ID,
                "artifact_id": canonical.IRREDUCIBILITY_REPORT_ARTIFACT_ID,
                "producer": "scripts/run_irreducibility_report.py",
                "scope": {"not_claimed": ["fixture"]},
                "control_protocol": {"low_order_baseline": "D^{<k}", "same_split": True},
                "seed_aggregation": {
                    "orders": {
                        "2": {
                            "seed_count": 2,
                            "stable_positive_direction": True,
                            "matched_random_any_positive": False,
                        }
                    }
                },
                "hardgate": {
                    "status": "pass",
                    "failed_gate": None,
                    "positive_irreducibility": True,
                    "gates": {f"IRR-HG{index}": {"status": "pass"} for index in range(1, 5)},
                },
                "positive_claim": {
                    "positive_irreducibility": True,
                    "claim_pointer": "$.hardgate.positive_irreducibility",
                    "cmi_diagnostic_only": True,
                },
                "conditional_information_table": {
                    "artifact": canonical.IRREDUCIBILITY_CMI_JSON_ARTIFACT,
                    "pointer": "$.rows",
                    "diagnostic_only": True,
                    "can_set_positive_irreducibility": False,
                    "row_count": 2,
                },
                "records": [
                    {
                        "seed": 101,
                        "orders": [
                            {
                                "order": 2,
                                "low_order": 1,
                                "low_order_baseline_present": True,
                                "conditioned_residual_gain": 0.1,
                                "matched_random_control": {"positive": False},
                                "finite_metrics": True,
                            }
                        ],
                    }
                ],
            }
        )
    if spec.name == "discovery-regularized-training":
        return runner.build_projection(generated_at="fixture-time")["summary_payload"]
        payload.update(
            {
                "config": {
                    "steps": 12,
                    "seeds": [11, 23, 37],
                    "mixings": ["spiral", "parabolic", "realnvp"],
                    "rhos": [0.5, 0.7, 0.9, 0.95],
                    "discovery_lambdas": [0.0, 0.0001, 0.001, 0.005, 0.01],
                    "arms": ["task_only", "sigreg", "drt", "matched_random"],
                },
                "records": {
                    "raw_rows_pointer": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
                    "deterministic_anchor_rows": 720,
                    "torch_evidence_rows": 16,
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
                    "task_accuracy_only": {"task_accuracy_only_rejected": True, "promoted_row_count": 0},
                    "classifier_shift": {
                        "classifier_shift_count_mean": 1.0,
                        "classifier_shift_positive": True,
                        "net_positive_signal": True,
                        "net_positive_count": 1,
                    },
                },
                "lambda_summary": {
                    "best_positive": {
                        "discovery_lambda": "0.01",
                        "quality_q_mean": 0.62,
                        "delta_quality_ci_low_mean": 0.003,
                    },
                    "ordered_discovery_lambdas": [0.0, 0.0001, 0.001, 0.005, 0.01],
                },
                "torch_training_evidence": {
                    "status": "available",
                    "row_count": 16,
                    "expected_row_count": 16,
                    "protocols": [
                        {
                            "requested_device": "auto",
                            "resolved_device": "cpu",
                            "seed": 11,
                            "steps": 12,
                            "dtype": "float32",
                            "drift_tolerance": 0.0001,
                            "status": "available",
                            "evidence_pointer": "$.records.raw_rows_pointer",
                        }
                    ],
                    "classifier_surface_delta": {
                        "source_arm": "drt",
                        "control_arm": "matched_random",
                        "drt_minus_matched_random_classifier_shift_count": 1.0,
                        "net_positive_signal": True,
                    },
                    "evidence_pointer": "$.records.raw_rows_pointer",
                },
                "negative_witness_mutations": {
                    "source_arm": "drt",
                    "mutation_arm": "matched_random",
                    "retrain_rows_pointer": "$.torch_training_evidence",
                    "failed_gate_pointer": "$.hardgate.status",
                    "claim_capsule_pointer": "$.claim_capsule_ref",
                },
                "training_loop_trace": {
                    "source_arm": "drt",
                    "mutation_arm": "matched_random",
                    "retrain_rows_pointer": "$.torch_training_evidence",
                    "failed_gate_pointer": "$.hardgate.status",
                    "claim_capsule_pointer": "$.claim_capsule_ref",
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
                "constraint_summary": {
                    "drt_minus_task_only_debt_q": -0.1,
                    "drt_minus_task_only_benefit_q": 0.02,
                    "debt_down": True,
                    "benefit_nondecreasing": True,
                },
            }
        )
        payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)
        payload["hardgate"] = {
            "status": "pass",
            "failed_gate": None,
            "gates": {
                f"DRT-HG{index}": {
                    "status": "pass",
                    "evidence_pointer": "$.training_mechanism_cert"
                    if index == 9
                    else "$.mechanism_ablation"
                    if index == 8
                    else "$.certificate_guided_dn_preservation"
                    if index == 7
                    else "$.quality_promotion_boundary",
                }
                for index in range(1, 10)
            },
        }
        payload["certificate_guided_dn_preservation"] = certificate_guided_dn_preservation(
            {
                "reports/canonical/certificate-guided-training.json": "present",
                "reports/canonical/certificate-guided-discovery.json": "present",
            }
        )
        payload["mechanism_ablation"] = _drt_mechanism_ablation_fixture()
        extension_sections = project_drt_training_extension(
            [],
            default_drt_training_extension_spec(),
            {"raw_metrics": "reports/runs/discovery-regularized-training/raw_metrics.jsonl"},
            payload,
        )
        payload.update(extension_sections)
        payload["training_mechanism_cert"] = _training_mechanism_cert(payload)
        payload["hardgate"]["gates"]["DRT-HG9"]["status"] = payload["training_mechanism_cert"]["status"]
        payload["hardgate"]["status"] = (
            "pass"
            if all(row["status"] == "pass" for row in payload["hardgate"]["gates"].values())
            else "fail"
        )
    if spec.name == "certificate-gated-attention":
        return cga_runner.build_projection(generated_at="fixture-time")["summary_payload"]
    if spec.name == "gap-head-transfer-atlas":
        payload["config"] = {"control_arm": "matched_random_gap_head"}
        payload.update(_atlas_fixture_rows())
        payload["forbidden_claim_term_audit"] = {"status": "pass", "hits": []}
    if spec.name == "transformer-derivative-atlas":
        return TransformerDerivativeAtlasProjection(
            config=TRANSFORMER_DERIVATIVE_ATLAS_CONFIG,
            generated_at="fixture",
        ).project()
    if spec.name == "mixing-family-sweep":
        payload["coverage_item"] = {
            "canonical_families": ["a", "b", "c"],
            "covered_families": ["a", "b"],
            "debt_item": {"score": "0.125", "status": "partial"},
        }
        payload["negative_result_summary"] = {
            "cells": {
                "a": {"negative_result": True},
                "b": {"negative_result": False},
            }
        }
    if spec.name == "anisotropic-ou-sweep":
        payload["transition_debt_by_grid"] = {"cell": {"status": "open-or-partial"}}
        payload["negative_result_summary"] = {
            "cells": {
                "a": {"negative_result": True},
                "b": {"negative_result": True},
            }
        }
    if spec.name == "nongaussian-distribution-sweep":
        payload["negative_result_ledger"] = [{"status": "negative"}, {"status": "negative"}]
        payload["coverage_item"] = {"debt_item": {"status": "open"}}
    if spec.name == "gap-head-attribution-capsule":
        payload["cost_protocol_pointer"] = "$.source_artifacts.cost_protocol"
        payload["source_artifacts"]["cost_protocol"] = {
            "status": "recorded",
            "surface_protocol": {"surface_helper": "fixture-surface-helper"},
            "control_protocol": {"matched_random_helper": "fixture-control-helper"},
        }
        payload["d5_o"] = {"status": "ready"}
        payload["d5_m"] = {"status": "blocked", "passed": False, "failed_gate": "A4-HG5"}
        payload["residualized_attribution"] = {"status": "pass"}
        payload["score_margin_causal_evidence"] = {"channel_classification": "score_margin_sufficient"}
        payload["head_channel_patch_evidence"] = {"causal_patch_claim": {"status": "pass"}}
        payload["negative_witness"] = [{"status": "score-margin-channel-sufficient"}]
        payload["mechanism_evidence"] = {
            "evidence_level": "patch",
            "base_level": "D5-O",
            "base_status": "ready",
            "mechanism_level": "blocked",
            "mechanism_status": "blocked",
            "candidate_mechanism": "probe-margin-channel",
            "failed_gate": "A4-HG5",
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
        }
        payload["ledger_debt"] = [{"debt_id": "gap-head-mechanism-evidence-closure", "status": "open"}]
        payload["not_implemented"] = ["nonlinear_residualization", "full_causal_replacement_scope"]
        payload["source_issues"] = [692, 747]
        payload["a4_hardgates"] = {
            "status": "fail",
            "gates": {
                "A4-HG2": {"status": "pass"},
                "A4-HG3": {"status": "pass"},
                "A4-HG5": {"status": "fail"},
                "head_causal_patch": {"status": "pass"},
            },
        }
    return payload


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _resolve_artifact_pointer(root, artifact_pointer):
    artifact, pointer = artifact_pointer.split(":", 1)
    payload = json.loads((root / artifact).read_text(encoding="utf-8"))
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _write_payloads_for_all_specs(canonical_module, tmp_path):
    canonical_module.ROOT = tmp_path
    canonical_module.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    canonical_module.INDEX_ARTIFACT = tmp_path / "reports" / "canonical" / "index.json"
    for spec in canonical_module.CANONICAL_REPORTS:
        json_path = canonical_module._artifact_path(spec.json_artifact)
        md_path = canonical_module._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        payload = _payload_for_spec(spec)
        if spec.name == "discovery-regularized-training":
            payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)
            canonical_module._validate_discovery_regularized_training_payload(payload)
        json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")
    cmi_path = tmp_path / canonical_module.IRREDUCIBILITY_CMI_JSON_ARTIFACT
    cmi_path.parent.mkdir(parents=True, exist_ok=True)
    cmi_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:conditional-information-table",
                "artifact_id": "bedc-quality-lab:conditional-information-table",
                "diagnostic_only": True,
                "row_count": 1,
                "rows": [{"seed": 101, "order": 2, "can_set_positive_irreducibility": False}],
            }
        )
        + "\n",
        encoding="utf-8",
    )


def _patch_scaling_ladder_pass_run_spec(monkeypatch):
    real_run_spec = canonical._run_spec

    def fake_run_spec(spec, *args, **kwargs):
        if spec.name == "scaling-ladder":
            return {
                "name": spec.name,
                "status": "pass",
                "bundle_role": spec.bundle_role,
                "json_artifact": spec.json_artifact,
                "markdown_artifact": spec.markdown_artifact,
                "fingerprint_sidecar": canonical._fingerprint_path(spec).relative_to(canonical.ROOT).as_posix(),
                "discipline": canonical._discipline(spec),
                "fingerprint_status": "match",
                "producer_status": "skipped",
                "artifact_validation": {"status": "pass"},
            }
        return real_run_spec(spec, *args, **kwargs)

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)


def _mutate_payload(canonical_module, report_name, update):
    spec = canonical_module._specs_by_name()[report_name]
    json_path = canonical_module._artifact_path(spec.json_artifact)
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    update(payload)
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _write_fingerprint_fixture(canonical_module, root, spec, *, script_text="SEED = 7\n\ndef main(argv=None):\n    return None\n"):
    script = root / spec.command[1]
    script.parent.mkdir(parents=True, exist_ok=True)
    script.write_text(script_text, encoding="utf-8")
    json_path = canonical_module._artifact_path(spec.json_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    canonical_module._artifact_path(spec.markdown_artifact).write_text("# fixture\n", encoding="utf-8")
    if spec.name == "irreducibility-report":
        cmi_path = canonical_module._artifact_path(canonical_module.IRREDUCIBILITY_CMI_JSON_ARTIFACT)
        cmi_path.parent.mkdir(parents=True, exist_ok=True)
        cmi_path.write_text(
            json.dumps({"schema_id": "bedc-quality-lab:conditional-information-table", "rows": []}) + "\n",
            encoding="utf-8",
        )
    return canonical_module._write_fingerprint_sidecar(spec, generated_at="fixture")


def _write_derivative_bridge_sidecar_fixtures(canonical_module, root):
    sidecars = {
        canonical_module.LEJEPA_DERIVATIVE_BRIDGE_JSON_ARTIFACT: {"sidecar": "lejepa-derivative-bridge"},
        canonical_module.HERMITE_BEHAVIOR_MARKDOWN_ARTIFACT: "# Hermite fixture\n",
        canonical_module.SPECTRAL_JET_JSON_ARTIFACT: {"sidecar": "spectral-jet-report"},
    }
    for artifact, payload in sidecars.items():
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(payload, str):
            path.write_text(payload, encoding="utf-8")
        else:
            path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def test_order_k_benchmark_canonical_spec_required_keys():
    spec = canonical._specs_by_name()["order-k-benchmark"]

    assert spec.name == "order-k-benchmark"
    assert spec.command == ("python3", "scripts/run_order_k_benchmark.py")
    assert spec.json_artifact == "reports/canonical/order-k-benchmark.json"
    assert spec.markdown_artifact == "reports/canonical/order-k-benchmark.md"
    assert set(spec.required_json_keys) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "source_artifacts",
        "task_specs",
        "order_rows",
        "minimal_order_summary",
        "surface_required_order_ledger",
        "surface_required_order_ledger_ref",
        "hardgate",
        "discovery_map_signal",
        "matched_random_controls",
        "ood_stability",
        "not_claimed",
        "positive_claim",
        "forbidden_claim_term_audit",
    }


def test_input_accessibility_canonical_spec_requires_rows_and_row_count():
    spec = canonical._specs_by_name()["input-accessibility"]

    assert spec.json_artifact == canonical.INPUT_ACCESSIBILITY_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.INPUT_ACCESSIBILITY_MARKDOWN_ARTIFACT
    assert {"rows", "row_count"} <= set(spec.required_json_keys)


def test_input_accessibility_validation_fails_closed_without_rows(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["input-accessibility"]
    payload = {key: "fixture" for key in spec.required_json_keys if key not in {"rows", "row_count"}}
    payload["schema_id"] = canonical.INPUT_ACCESSIBILITY_SCHEMA_ID
    payload["artifact_id"] = canonical.INPUT_ACCESSIBILITY_ARTIFACT_ID
    payload["access_hardgates"] = {"status": "pass"}
    payload["ood_hardgates"] = {"status": "pass"}
    payload["boundary_ledger"] = []
    payload["consumer_pointers"] = {}
    payload["source_registry"] = []
    payload["visible_variables"] = {}
    payload["required_variables"] = {}
    payload["not_claimed"] = []
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["required_key_validation"]["status"] == "fail"
    assert set(validation["required_key_validation"]["missing_keys"]) == {"rows", "row_count"}


def test_order_k_benchmark_fingerprint_closure_has_runner_and_projector(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    spec = canonical._specs_by_name()["order-k-benchmark"]
    script = tmp_path / "scripts" / "run_order_k_benchmark.py"
    helper = tmp_path / "bedc_quality_lab" / "order_k_benchmark.py"
    claim_terms = tmp_path / "bedc_quality_lab" / "claim_terms.py"
    script.parent.mkdir(parents=True, exist_ok=True)
    helper.parent.mkdir(parents=True, exist_ok=True)
    script.write_text("from bedc_quality_lab.order_k_benchmark import OrderKBenchmarkProjection\n", encoding="utf-8")
    helper.write_text("from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS\n", encoding="utf-8")
    claim_terms.write_text("FORBIDDEN_POSITIVE_CLAIM_TERMS = ()\n", encoding="utf-8")

    paths = canonical._import_closure(spec.command)

    assert "scripts/run_order_k_benchmark.py" in paths
    assert "bedc_quality_lab/order_k_benchmark.py" in paths
    assert ".refactor-loop/host.env" not in paths


def test_order_k_benchmark_host_env_not_fingerprint_input(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["order-k-benchmark"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    host_env = tmp_path / ".refactor-loop" / "host.env"
    host_env.parent.mkdir(parents=True, exist_ok=True)
    host_env.write_text("HOST_REFACTOR_COMMENT_POLICY=none\n", encoding="utf-8")

    sidecar = canonical._write_fingerprint_sidecar(spec, generated_at="fixture")
    serialized = json.dumps(sidecar["inputs"], sort_keys=True)

    assert ".refactor-loop/host.env" not in serialized


def test_unreferenced_config_file_does_not_dirty_unrelated_fingerprint(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    unreferenced = tmp_path / "configs" / "unreferenced_knob.yaml"
    unreferenced.parent.mkdir(parents=True, exist_ok=True)
    unreferenced.write_text("knob: 1\n", encoding="utf-8")

    sidecar = canonical._write_fingerprint_sidecar(spec, generated_at="fixture")
    serialized = json.dumps(sidecar["inputs"], sort_keys=True)

    assert "config_inputs" not in sidecar["inputs"]
    assert "configs/unreferenced_knob.yaml" not in serialized
    assert canonical._fingerprint_matches(spec) == (True, "match")


def test_source_artifact_config_file_dirties_declared_report(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    cost_config = tmp_path / "configs" / "default_cost_protocol.yaml"
    cost_config.parent.mkdir(parents=True, exist_ok=True)
    cost_config.write_text("unit_cost: 1\n", encoding="utf-8")
    sidecar = _write_fingerprint_fixture(canonical, tmp_path, spec)

    cost_config.write_text("unit_cost: 2\n", encoding="utf-8")

    assert "configs/default_cost_protocol.yaml" in {
        row["path"] for row in sidecar["inputs"]["source_artifacts"]
    }
    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")


def test_literature_ledger_dirties_only_literature_reports(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    ledger = tmp_path / "docs" / "lit" / "literature_ledger.yaml"
    ledger.parent.mkdir(parents=True, exist_ok=True)
    ledger.write_text(json.dumps({"records": [{"id": "lit-lejepa-theorem-ledger"}]}) + "\n", encoding="utf-8")
    unrelated = canonical._specs_by_name()["mixing-family-sweep"]
    literature = canonical._specs_by_name()["certificate-gated-attention"]
    unrelated_sidecar = _write_fingerprint_fixture(canonical, tmp_path, unrelated)
    literature_sidecar = _write_fingerprint_fixture(canonical, tmp_path, literature)

    ledger.write_text(
        json.dumps({"records": [{"id": "lit-lejepa-theorem-ledger"}, {"id": "lit-fixture"}]}) + "\n",
        encoding="utf-8",
    )

    assert "docs/lit/literature_ledger.yaml" not in {
        row["path"] for row in unrelated_sidecar["inputs"]["source_artifacts"]
    }
    assert "docs/lit/literature_ledger.yaml" in {
        row["path"] for row in literature_sidecar["inputs"]["source_artifacts"]
    }
    assert canonical._fingerprint_matches(unrelated) == (True, "match")
    assert canonical._fingerprint_matches(literature) == (False, "input-fingerprint")


def test_metric_purity_registry_files_are_not_per_report_inputs(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    targets = tmp_path / "configs" / "metric_purity_targets.json"
    allowlist = tmp_path / "configs" / "metric_purity_allowlist.json"
    targets.parent.mkdir(parents=True, exist_ok=True)
    targets.write_text('{"schema_id":"fixture-targets"}\n', encoding="utf-8")
    allowlist.write_text('{"schema_id":"fixture-allowlist"}\n', encoding="utf-8")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    sidecar = _write_fingerprint_fixture(canonical, tmp_path, spec)

    targets.write_text('{"schema_id":"fixture-targets","rows":[]}\n', encoding="utf-8")
    allowlist.write_text('{"schema_id":"fixture-allowlist","rows":[]}\n', encoding="utf-8")
    serialized = json.dumps(sidecar["inputs"], sort_keys=True)

    assert "configs/metric_purity_targets.json" not in serialized
    assert "configs/metric_purity_allowlist.json" not in serialized
    assert canonical._fingerprint_matches(spec) == (True, "match")


def test_order_k_benchmark_has_no_standalone_ledger_spec_or_artifact_path():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    artifact_paths = [
        path
        for spec in canonical.CANONICAL_REPORTS
        for path in (spec.json_artifact, spec.markdown_artifact)
    ]

    assert names.count("order-k-benchmark") == 1
    assert "surface-required-order-ledger" not in names
    assert "surface_required_order_ledger" not in names
    assert "reports/surface_required_order_ledger.json" not in artifact_paths
    assert "reports/canonical/surface_required_order_ledger.json" not in artifact_paths
    assert "reports/canonical/surface_required_order_ledger.md" not in artifact_paths


def _set_canonical_tmp_root(monkeypatch, tmp_path):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    _write_dimension_mismatch_gap_witness_fixture(tmp_path)


def _write_release_pointer_fixture(root):
    (root / "docs" / "lit").mkdir(parents=True, exist_ok=True)
    canonical_dir = root / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    (canonical_dir / "new_model_hardgates.json").write_text(json.dumps({"gates": {"status": "pass"}}) + "\n", encoding="utf-8")
    (canonical_dir / "mechanism_dna.json").write_text(json.dumps({"rows": [{"status": "pass"}]}) + "\n", encoding="utf-8")
    (canonical_dir / "discovery-gated-transformer-training.json").write_text(json.dumps({"hardgates": {"status": "pass"}}) + "\n", encoding="utf-8")
    (canonical_dir / "dgt-l0-controls.json").write_text(
        json.dumps(
            {
                "construct_suspension": {
                    "headline_status": "suspended-construct-review",
                    "taint_status": "tainted-l0-construct-review-only",
                },
                "honest_metric_review": {"status": "scoped-boundary"},
                "ladder_consumption": {"status": "scoped-boundary"},
                "construct_validity_hardgates": {
                    "status": "fail",
                    "failed_gates": ["CV-HG4"],
                    "evidence": {"finite_table": {"rule_abstraction_claim": False}},
                },
                "l0_toy_projection": {
                    "review_status": "scoped-boundary",
                    "status": "scoped-boundary",
                    "ladder_consumption": {"status": "scoped-boundary"},
                },
                "negative_witness_sweep": {"status": "pass"},
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "dgt-l1-controls.json").write_text(
        json.dumps(
            {
                "l1_tiny_sequence_projection": {
                    "review_status": "pass",
                    "promotion_readiness": "ready-pass",
                    "not_claimed": [
                        "Bounded tiny-sequence order-k training only.",
                        "No production deployment claim.",
                        "No global superiority claim.",
                        "No LLM replacement claim.",
                        "No L2 or higher scaling claim.",
                    ],
                },
                "negative_witness_sweep": {
                    "status": "pass",
                    "rows": [
                        {"witness": "information_starved_baseline"},
                        {"witness": "unanswerable_ood"},
                        {"witness": "table_coverage_saturation"},
                        {"witness": "hand_engineered_task_aligned_gate"},
                    ],
                },
                "l1_ood_mechanism": {
                    "owner": "dgt-l1-controls",
                    "evidence_scope": "bounded-tiny-sequence-l1-ood-mechanism",
                    "verdict": "memorization",
                    "l2_implication": {
                        "verdict_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_ood_mechanism.verdict",
                        "status": "pointer-only",
                    },
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "fair-l1-decision.json").write_text(
        json.dumps(
            {
                "decision": {"status": "bounded-negative"},
                "ladder_state_projection": {
                    "state": "l1-bounded-negative",
                    "decision_status": "bounded-negative",
                    "decision_pointer": "reports/canonical/fair-l1-decision.json:$.decision.status",
                    "hardgate_pointer": "reports/canonical/fair-l1-decision.json:$.hardgates",
                    "boundary_ledger_pointer": "reports/canonical/fair-l1-decision.json:$.boundary_ledger",
                    "not_claimed": [
                        "Bounded tiny-sequence L1 decision only.",
                        "No L2 or higher scaling claim.",
                        "No production deployment claim.",
                        "No global superiority claim.",
                        "No LLM replacement claim.",
                        "No OOD generalization claim.",
                        "No architecture advantage claim.",
                    ],
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )
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


def _write_dimension_mismatch_gap_witness_fixture(root):
    path = root / "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "run_local": {
                    "negative_witness": [
                        {
                            "witness_id": "scale_leakage_witness",
                            "source_artifact": "reports/dimension_mismatch_anti_triviality.json",
                            "source_pointer": "$.status",
                            "bedc_gap_field": "representation_scale_leakage",
                            "demotion_rule": "demote_to_DN_or_D1",
                            "regression_test": "$.run_local.test_artifact.regression_tests.scale_leakage_witness",
                            "evidence_pointer": "reports/dimension_mismatch_anti_triviality.json:$.controlled_geometry.feature_partition",
                            "status": "valid",
                            "reason": "scale-only anti-triviality evidence demotes the debt-transfer claim",
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
            }
        )
        + "\n",
        encoding="utf-8",
    )
    sidecar_path = root / "reports/dimension_mismatch_anti_triviality.json"
    sidecar_path.parent.mkdir(parents=True, exist_ok=True)
    sidecar_path.write_text(
        json.dumps(
            {
                "status": "scale_leakage_detected",
                "controlled_geometry": {
                    "feature_partition": {"fixture": ["h_l2_mean"]},
                },
            }
        )
        + "\n",
        encoding="utf-8",
    )


def _write_lab_report_import_fixture(root, spec):
    (root / "bedc_quality_lab").mkdir(parents=True, exist_ok=True)
    (root / "bedc_quality_lab" / "__init__.py").write_text("", encoding="utf-8")
    (root / "bedc_quality_lab" / "report.py").write_text(
        "\n".join(
            [
                "from .cost_protocol import load_cost_protocol",
                "from .schema import QualityEvidenceEnvelope",
                "from .tensor_namecert_candidate import from_quality_evidence_envelope",
                "",
            ]
        ),
        encoding="utf-8",
    )
    for name in ("cost_protocol", "schema", "tensor_namecert_candidate"):
        (root / "bedc_quality_lab" / f"{name}.py").write_text(f"{name.upper()} = 'fixture'\n", encoding="utf-8")
    script = root / spec.command[1]
    script.parent.mkdir(parents=True, exist_ok=True)
    script.write_text(
        "from bedc_quality_lab.report import QualityEvidenceEnvelope\n\nSEED = 7\n",
        encoding="utf-8",
    )


def _patch_lightweight_run_reports(monkeypatch):
    def write_json(root, artifact, payload):
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    def write_markdown(root, artifact, text):
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def fake_formal_hardening(*, root, generated_at=None):
        write_json(root, canonical.FORMAL_HARDENING_JSON_ARTIFACT, {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
        write_markdown(root, canonical.FORMAL_HARDENING_MARKDOWN_ARTIFACT, "# formal\n")
        return {}

    def fake_discovery(*, root, generated_at=None, adapter=None):
        write_json(
            root,
            canonical.DISCOVERY_MAP_JSON_ARTIFACT,
            {"generated_at": generated_at, "row_count": 0, "level_counts": {}, "rows": []},
        )
        write_markdown(root, canonical.DISCOVERY_MAP_MARKDOWN_ARTIFACT, "# discovery\n")
        return {}

    def fake_transfer(*, root, generated_at=None, require_anti_triviality=False):
        write_json(
            root,
            canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
            {
                "dimension_mismatch_debt_transfer": {
                    "status": "pass",
                    "base_level": "D4",
                    "effective_level": "D4",
                    "terminal_verdict": "projected_discovery_required",
                }
            },
        )
        write_markdown(root, canonical.DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT, "# transfer\n")
        return {}

    def fake_anti_triviality(*, root, generated_at=None):
        return {}

    def fake_robustness(*, root, generated_at=None):
        write_json(root, canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT, {"status": "pass", "audit_status": "pass"})
        write_markdown(root, canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT, "# robust\n")
        return {}

    def fake_witness_summary(*, root, generated_at=None):
        write_json(root, canonical.NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT, {"status": "pointer-only", "row_count": 0, "audit_status": "pass", "rows": []})
        write_markdown(root, canonical.NEGATIVE_WITNESS_SUMMARY_MARKDOWN_ARTIFACT, "# witness\n")
        return {}

    def fake_mutation_ledger(*, root, generated_at=None):
        payload = {
            "schema_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID,
            "artifact_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID,
            "producer": "scripts/run_negative_witness_mutation_ledger.py",
            "generated_at": generated_at,
            "status": "ready",
            "entry_count": 0,
            "entries": [],
            "hardgates": {f"MUT-HG{index}": {"status": "pass"} for index in range(1, 6)},
            "forbidden_keys": [],
        }
        write_json(root, canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT, payload)
        write_markdown(root, canonical.MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT, "# mutation graph\n")
        write_json(
            root,
            canonical.DGT_MUTATION_REPORT_ARTIFACT,
            {
                "schema_id": "bedc-quality-lab:dgt-mutation-report",
                "ledger": {"artifact": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT, "pointer": "$.entries"},
                "graph": {"artifact": canonical.MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT, "pointer": "$"},
                "status": "ready",
                "entry_count": 0,
                "blocked_count": 0,
                "mut_hg_summary": {f"MUT-HG{index}": "pass" for index in range(1, 6)},
            },
        )
        return payload

    def fake_claim_graph(*, root, generated_at=None):
        write_json(root, canonical.CLAIM_GRAPH_JSON_ARTIFACT, {"status": "pointer-only", "nodes": [], "edges": []})
        write_markdown(root, canonical.CLAIM_GRAPH_MARKDOWN_ARTIFACT, "# graph\n")
        return {}

    def fake_release(*, root, generated_at=None):
        write_json(
            root,
            canonical.RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT,
            {
                "schema_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                "artifact_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
                "generated_at": generated_at,
                "version": "0.0.1",
                "tag_ref": None,
                "release_bundle_status": "ready",
                "tag_status": "absent",
                "source_pointers": {},
                "required_pointers": [
                    {
                        "id": "fixture-pointer",
                        "path": "reports/canonical/index.json",
                        "pointer": "$.schema_id",
                        "status": "resolved",
                        "failure": None,
                    }
                ],
                "not_claimed": ["fixture boundary"],
                "revoke_if": "Revoke if fixture pointer stops resolving.",
            },
        )
        write_markdown(root, canonical.RELEASE_MANIFEST_SIDECAR_MARKDOWN_ARTIFACT, "# release sidecar\n")
        return {}

    monkeypatch.setattr(
        canonical,
        "_build_quality_scorecard",
        lambda results, generated_at=None: {"generated_at": generated_at, "rows": [], "metrics": []},
    )
    monkeypatch.setattr(canonical, "_render_quality_scorecard_markdown", lambda payload: "# scorecard\n")
    monkeypatch.setattr(canonical, "_build_claim_capsule", lambda generated_at: {"status": "complete"})
    monkeypatch.setattr(
        canonical,
        "_index",
        lambda results, generated_at=None, claim_verdict_rows=None, discovery_gated_transformer_payload=None: {
            "schema_id": canonical.INDEX_SCHEMA_ID,
            "generated_at": generated_at,
            "reports": list(results),
            "claim_verdicts": list(claim_verdict_rows or []),
        },
    )
    monkeypatch.setattr(canonical, "_render_index_markdown", lambda payload: "# index\n")
    monkeypatch.setitem(sys.modules, "scripts.run_formal_hardening_report", types.SimpleNamespace(write_formal_hardening_report=fake_formal_hardening))
    monkeypatch.setitem(sys.modules, "bedc_quality_lab.backends.current_lab.adapter", types.SimpleNamespace(CurrentLabBackendEvidenceAdapter=lambda: object()))
    monkeypatch.setitem(sys.modules, "bedc_quality_lab.discovery_compiler.compiler", types.SimpleNamespace(compile_discovery=fake_discovery))
    monkeypatch.setitem(sys.modules, "scripts.run_claim_graph", types.SimpleNamespace(write_claim_graph=fake_claim_graph))
    monkeypatch.setitem(sys.modules, "scripts.run_claim_verdict_demo", types.SimpleNamespace(write_claim_verdicts=lambda root, generated_at=None: []))
    monkeypatch.setitem(sys.modules, "scripts.run_dimension_mismatch_debt_transfer", types.SimpleNamespace(write_dimension_mismatch_debt_transfer=fake_transfer))
    monkeypatch.setitem(sys.modules, "scripts.run_dimension_mismatch_anti_triviality", types.SimpleNamespace(write_dimension_mismatch_anti_triviality=fake_anti_triviality))
    monkeypatch.setitem(sys.modules, "scripts.run_dimension_mismatch_transfer_robustness", types.SimpleNamespace(write_dimension_mismatch_transfer_robustness=fake_robustness))
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_discovery_negative_witness_summary",
        types.SimpleNamespace(
            write_discovery_negative_witness_summary=fake_witness_summary,
            build_discovery_negative_witness_summary=lambda root, generated_at=None: {"status": "pointer-only", "row_count": 0, "audit_status": "pass"},
        ),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_negative_witness_mutation_ledger",
        types.SimpleNamespace(write_negative_witness_mutation_ledger=fake_mutation_ledger),
    )
    monkeypatch.setitem(sys.modules, "scripts.release_manifest_sidecar", types.SimpleNamespace(write_release_manifest_sidecar=fake_release))
    monkeypatch.setattr(canonical, "_run_metric_purity_preflight", lambda report_artifacts=None: {"status": "pass"})


def _file_digest_map(root):
    return {
        path.relative_to(root).as_posix(): canonical._path_digest(path)
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }


def _index_row_for_spec(spec):
    return {
        "name": spec.name,
        "bundle_role": spec.bundle_role,
        "status": "pass",
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "fingerprint_sidecar": canonical._artifact_path(spec.json_artifact).with_suffix(".fingerprint.json").relative_to(canonical.ROOT).as_posix(),
        "discipline": {
            "claim_promotion_eligible": spec.claim_promotion_eligible,
            "scope_pointer": spec.scope_pointer,
            "cost_pointer": spec.cost_pointer,
            "not_claimed_pointer": spec.not_claimed_pointer,
            "positive_claim_pointer": spec.positive_claim_pointer,
            "control_pointer": spec.control_pointer,
            "no_control_rationale_pointer": spec.no_control_rationale_pointer,
        },
    }


def _patch_dgt_owner_fixture(monkeypatch, calls):
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-gated-transformer"])

    def fake_build_dgt(*, generated_at=None):
        calls.append(("build-dgt", "discovery-gated-transformer"))
        return dict(payload, generated_at=generated_at)

    def fake_write_dgt_artifacts(payload, *, root):
        calls.append(("write-dgt-artifacts", payload["model_id"]))

    monkeypatch.setattr(canonical, "_build_discovery_gated_transformer_payload", fake_build_dgt)
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_discovery_gated_transformer",
        types.SimpleNamespace(write_artifacts=fake_write_dgt_artifacts),
    )


def _write_discovery_gated_transformer_owner_for_index(tmp_path):
    from scripts import run_discovery_gated_transformer as dgt_runner

    owner = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    dgt_runner.write_artifacts(owner, root=tmp_path)
    canonical._write_json_atomic(
        canonical._artifact_path(canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT),
        owner,
    )
    canonical._write_text_atomic(
        canonical._artifact_path(canonical.DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT),
        canonical._render_discovery_gated_transformer_markdown(owner),
    )
    canonical._write_fingerprint_sidecar(
        canonical._specs_by_name()["discovery-gated-transformer"],
        generated_at="2030-01-01T00:00:00+00:00",
    )
    return owner


def _write_observed_debt_projection_fixtures(root):
    fixtures = {
        "reports/canonical/nongaussian-distribution-sweep.json": {
            "main_claim_status": "observed-debt-pipeline-only",
            "claim_gate": {"HG-LD": {"status": "pass"}},
            "global_claim_flag": False,
            "records": [{"latent_distribution_debt_item": {"status": "closed"}}],
        },
        "reports/canonical/anisotropic-ou-sweep.json": {
            "transition_debt_by_grid": {
                "rho_axes_0p95_0p3": {
                    "status": "open-or-partial",
                    "debt_score_mean": 0.12,
                }
            }
        },
        "reports/canonical/dimension-mismatch-debt-transfer.json": {
            "dimension_mismatch_debt_transfer": {"status": "pass"},
            "hardgate_evidence": {"HG-B1": {"status": "pass"}},
            "boundary_ledger": {"status": "recorded"},
        },
        "reports/canonical/gap-head-observed-debt-transfer.json": {
            "gap_head_on_h_observed_debt_transfer": {"status": "pass"},
            "hardgate_evidence": {"HG-A1": {"status": "pass"}},
            "observed_debt_transfer_boundary": {"status": "recorded"},
            "surfaces": [{"status": "pass"}],
        },
        "reports/canonical/mixing-family-sweep.json": {
            "coverage_item": {"debt_item": {"status": "closed"}},
        },
        "runs/training_choice_observability.json": {
            "status": "pointer-only",
            "source_artifacts": {"gap_head_metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm"},
            "training_choice_observability": {
                "observed_debt_arm_count": 0,
                "ledger_risk_only_arm_count": 1,
                "arms": [{"hardgates": {"HG-TCO-3": {"status": "fail"}}}],
            },
            "boundary_ledger": [{"kind": "ledger-risk-only"}],
        },
        "reports/canonical/discovery_gate_escape_registry.json": {
            "capacity": {"overflow_policy": "fail-closed"},
        },
    }
    for artifact, payload in fixtures.items():
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _read_committed_claim_verdicts():
    path = canonical.ROOT / canonical.CLAIM_VERDICTS_JSONL_ARTIFACT
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


def _normalized_index_report(report):
    return dict(report)


def _canonical_bundle_payloads_for_timestamps(*, index_timestamp, discovery_timestamp):
    committed_index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    generated_claims = claim_verdict_demo.compile_claim_verdicts(canonical.ROOT, generated_at=index_timestamp)
    generated_index = canonical._index(
        [_normalized_index_report(report) for report in committed_index["reports"]],
        generated_at=index_timestamp,
        claim_verdict_rows=generated_claims,
    )
    generated_discovery = discovery_map.build_discovery_map(
        generated_at=discovery_timestamp,
        root=canonical.ROOT,
        canonical_reports=canonical._discovery_map_reports(),
    )
    return generated_index, generated_discovery, generated_claims


def _without_discovery_rows(payload, excluded_reports):
    assert "discovery-gated-transformer" not in set(excluded_reports)
    return {
        **{key: value for key, value in payload.items() if key != "rows"},
        "rows": [
            row
            for row in payload["rows"]
            if row.get("report") not in set(excluded_reports)
        ],
    }


def _assert_dgt_discovery_map_row_uses_l0_consumption(row):
    assert row["classifier_reasons"] == [
        "scaling-ladder-owner-closed:unresolved-pointer"
    ]
    assert row["failed_gate"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert row["evidence_pointer"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert row["scaling_ladder_pointer"] == "reports/canonical/scaling-ladder.json:$.levels[0]"


def _drop_dgt_l0_from_manifest(monkeypatch):
    monkeypatch.setattr(
        canonical,
        "CANONICAL_REPORTS",
        tuple(
            spec
            for spec in canonical.CANONICAL_REPORTS
            if spec.name != "dgt-l0-controls"
        ),
    )


def test_manifest_names_and_artifacts_are_unique_and_canonical_owned():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    json_artifacts = [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]
    markdown_artifacts = [spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS]

    assert "formal_hardening" not in names
    assert "reports/canonical/formal_hardening.json" not in json_artifacts
    assert "reports/canonical/formal_hardening.md" not in markdown_artifacts
    assert len(names) == len(set(names))
    assert names == [
        "mixing-family-sweep",
        "anisotropic-ou-sweep",
        "gap-head-on-h",
        "gap-head-discovery",
        "gap-head-ablation",
        "irreducibility-report",
        "ledger-aware-transformer",
        "certificate-gated-attention",
        "gap-head-threshold-frontier",
        "gap-head-transfer-atlas",
        "gap-head-attribution-capsule",
        "nongaussian-distribution-sweep",
        "certificate-guided-training",
        "certificate-guided-discovery",
        "sigreg-training-proxy",
        "sigreg-mini-grid",
        "discovery-regularized-training",
        "mechanism-seeking-network",
        "mechanism-dna",
        "dgt-l0-controls",
        "dgt-l1-controls",
        "dgt-l1-boundary-report",
        "reproduction-package",
        "reproduction-check-result",
        "winnability-certificates",
        "structural-generalization-splits",
        "dgt-base-undertraining-audit",
        "scaling-ladder",
        "input-accessibility",
        "fair-l1-decision",
        "discovery-gated-transformer",
        "dgt-neural-ablation",
        "dgt-ablation-null-decomposition",
        "dgt-component-redundancy-audit",
        "dgt-model-card",
        "order-k-benchmark",
        "transformer-derivative-atlas",
        "lejepa-theorem-ledger",
        "observed-debt-sweep",
        "spectral-ablation-hinge",
        "model-comparison",
        "high-impact-review",
        "causal-patch-suite",
        "claim-complexity",
        "experiment-stack-cards",
    ]
    assert "certificate-guided-arms" not in names
    assert "certificate-guided-training" in names
    assert "certificate-guided-discovery" in names
    assert "discovery-gated-transformer" in names
    assert "dgt-l0-controls" in names
    assert "scaling-ladder" in names
    assert "input-accessibility" in names
    assert "dgt-model-card" in names
    assert "mechanism-dna" in names
    assert "reproduction-package" in names
    assert "reproduction-check-result" in names
    assert "discovery_gated_transformer" not in names
    assert "tool-use-dgt" not in names
    assert "tool-use-toy-dgt" not in names
    assert len(json_artifacts) == len(set(json_artifacts))
    assert len(markdown_artifacts) == len(set(markdown_artifacts))
    forbidden_artifacts = {
        "reports/canonical/discovery_gated_transformer.json",
        "reports/canonical/discovery_gated_transformer.md",
        "reports/canonical/tool-use-dgt.json",
        "reports/canonical/tool-use-dgt.md",
        "reports/canonical/tool-use-toy-dgt.json",
        "reports/canonical/tool-use-toy-dgt.md",
    }
    assert forbidden_artifacts.isdisjoint(json_artifacts)
    assert forbidden_artifacts.isdisjoint(markdown_artifacts)
    for spec in canonical.CANONICAL_REPORTS:
        assert spec.json_artifact.startswith("reports/canonical/")
        assert spec.markdown_artifact.startswith("reports/canonical/")
        assert spec.json_artifact.endswith(".json")
        assert spec.markdown_artifact.endswith(".md")
        assert spec.required_json_keys
        assert spec.bundle_role in {"hg_p_core", "auxiliary"}
        assert spec.scope_pointer.startswith("$.")
        assert spec.cost_pointer.startswith("$.")
        assert spec.not_claimed_pointer.startswith("$.")
        assert spec.positive_claim_pointer.startswith("$.")


def test_dgt_owner_path_is_hyphen_only():
    spec = canonical._specs_by_name()["discovery-gated-transformer"]
    names = set(canonical._specs_by_name())

    assert spec.json_artifact == "reports/canonical/discovery-gated-transformer.json"
    assert spec.markdown_artifact == "reports/canonical/discovery-gated-transformer.md"
    assert "tool_route_evidence" in spec.required_json_keys
    assert "component_ablation" in spec.required_json_keys
    assert "d5_o_projection" in spec.required_json_keys
    assert "d5_m_projection" in spec.required_json_keys
    assert "scaling_ladder" in spec.required_json_keys
    assert spec.positive_claim_pointer == "$.scaling_ladder"
    assert spec.not_claimed_pointer == "$.scaling_ladder.not_claimed"
    assert spec.scope_pointer == "$.scaling_ladder"
    assert spec.control_pointer == "$.d4_projection.matched_control"
    assert "discovery_gated_transformer" not in names
    assert "dgt-scaling-ladder" not in names


def test_scaling_ladder_canonical_spec_is_auxiliary_owner():
    spec = canonical._specs_by_name()["scaling-ladder"]

    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_scaling_ladder.py")
    assert spec.json_artifact == "reports/canonical/scaling-ladder.json"
    assert spec.markdown_artifact == "reports/canonical/scaling-ladder.md"
    assert spec.required_json_keys[:8] == (
        "schema_id",
        "artifact_id",
        "generated_at",
        "source_artifacts",
        "levels",
        "boundary_ledger",
        "hardgates",
        "not_claimed",
    )
    assert spec.scope_pointer == "$.levels"
    assert spec.positive_claim_pointer == "$.levels"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.control_pointer is None
    assert "$.levels[*].owner_contracts" in spec.required_json_keys


def test_dgt_l0_controls_canonical_spec_is_single_auxiliary_owner():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "dgt-l0-controls"]
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}

    assert len(specs) == 1
    spec = specs[0]
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_l0_controls.py")
    assert spec.json_artifact == "reports/canonical/dgt-l0-controls.json"
    assert spec.markdown_artifact == "reports/canonical/dgt-l0-controls.md"
    assert spec.control_pointer == "$.l0_toy_projection"
    assert spec.cost_pointer == "$.compute_param_ledger"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.positive_claim_pointer == "$.l0_toy_projection.review_status"
    assert spec.construct_validity_pointer == "reports/canonical/dgt-l0-controls.json:$.construct_validity_hardgates"
    assert names.isdisjoint(
        {
            "base-transformer-l0",
            "matched-random-structural-control",
            "l0-compute-param-ledger",
            "l0-negative-witness-sweep",
            "l0-independent-replay",
            "l0-pass-decision",
        }
    )


def test_winnability_certificates_canonical_spec_and_index_section(tmp_path, monkeypatch):
    from bedc_quality_lab import winnability

    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["winnability-certificates"]
    split = {
        "experiment_id": "fixture",
        "task_id": "fixture-task",
        "task_family": "analytic-visibility",
        "resolver_family": "analytic-visibility",
        "split_id": "fixture-split",
        "split_kind": "held-out",
        "split_fingerprint": "fixture-fingerprint",
        "source_evidence_ref": "reports/canonical/fixture.json:$.row",
        "label_function_ref": "fixture.label",
        "visible_variables_ref": "reports/canonical/input-accessibility.json:$.visible",
        "required_variables_ref": "reports/canonical/input-accessibility.json:$.required",
        "visible_variables": ["x_left"],
        "required_variables": ["x_left"],
        "allow_inline_input_fixture": True,
        "chance_accuracy": 0.5,
        "observed_accuracy": 0.75,
    }
    payload = winnability.build_payload(root=tmp_path, generated_at="fixture", registered_splits=[split])
    canonical._write_json_atomic(canonical._artifact_path(spec.json_artifact), payload)
    canonical._write_text_atomic(canonical._artifact_path(spec.markdown_artifact), "# fixture\n")

    section = canonical._winnability_certificates_index_section()
    index_payload = canonical._index([], generated_at="fixture", claim_verdict_rows=[])
    markdown = canonical._render_index_markdown(index_payload)

    assert spec.command == ("python3", "scripts/run_winnability_certificates.py")
    assert spec.bundle_role == "auxiliary"
    assert spec.json_artifact == "reports/canonical/winnability-certificates.json"
    assert spec.markdown_artifact == "reports/canonical/winnability-certificates.md"
    assert {
        "schema_id",
        "artifact_id",
        "inputs",
        "registered_splits",
        "audit",
        "$.audit.fail_closed_count",
    } <= set(spec.required_json_keys)
    assert "winnability-certificates" not in canonical.DISCOVERY_MAP_EXCLUDED_REPORTS
    assert payload["inputs"]["registered_splits"] == (
        "reports/canonical/winnability-certificates.json:$.registered_splits"
    )
    resolved_registered_splits = resolve_artifact_pointer(tmp_path, payload["inputs"]["registered_splits"])
    assert isinstance(resolved_registered_splits, list)
    assert resolved_registered_splits[0]["task_id"] == "fixture-task"
    assert resolved_registered_splits[0]["split_id"] == "fixture-split"
    assert "resolver" not in resolved_registered_splits[0]
    assert section["winnability_certificates"] == "reports/canonical/winnability-certificates.json:$.certificates"
    assert "certificates" + "_pointer" not in section
    assert section["audit_pointer"] == "reports/canonical/winnability-certificates.json:$.audit"
    assert section["hardgates_pointer"] == "reports/canonical/winnability-certificates.json:$.hardgates"
    assert section["fail_closed_count"] == 0
    assert index_payload["winnability_certificates"] == section
    assert "## Winnability certificates" in markdown


def test_winnability_certificates_regen_is_idempotent(tmp_path, monkeypatch):
    from scripts import run_winnability_certificates as runner

    _set_canonical_tmp_root(monkeypatch, tmp_path)

    first = runner.write_winnability_certificates(root=tmp_path, generated_at="fixture")
    first_json = (tmp_path / canonical.WINNABILITY_CERTIFICATES_JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / canonical.WINNABILITY_CERTIFICATES_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    second = runner.write_winnability_certificates(root=tmp_path, generated_at="fixture")

    assert second == first
    assert (tmp_path / canonical.WINNABILITY_CERTIFICATES_JSON_ARTIFACT).read_text(encoding="utf-8") == first_json
    assert (tmp_path / canonical.WINNABILITY_CERTIFICATES_MARKDOWN_ARTIFACT).read_text(encoding="utf-8") == first_md
    assert second["audit"]["status"] == "fail"
    assert second["audit"]["failed_count"] == 3
    assert second["audit"]["fail_closed_count"] == 3


def test_winnability_certificates_missing_artifact_validation_fails_closed(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["winnability-certificates"]

    validation = canonical._artifact_validation(spec)

    assert validation["status"] == "fail"
    assert spec.json_artifact in validation["missing_artifacts"]
    assert "$.audit.fail_closed_count" in validation["required_key_validation"]["missing_keys"]
def test_dgt_controls_require_construct_validity_without_replacing_protocol_hardgates():
    specs = canonical._specs_by_name()
    l0 = specs["dgt-l0-controls"]
    assert l0.construct_validity_pointer == f"{l0.json_artifact}:$.construct_validity_hardgates"
    assert _payload_for_spec(l0)["construct_validity_hardgates"]["schema_id"] == "bedc.quality.construct_validity_hardgates"

    l1 = specs["dgt-l1-controls"]
    assert l1.construct_validity_pointer == f"{l1.json_artifact}:$.construct_validity_ledger"
    assert "construct_validity_ledger" in l1.required_json_keys
    payload = _payload_for_spec(l1)
    assert payload["construct_validity_ledger"]["split_protocol"]["heldout_pair_rule"] == "balanced_label_stratified_pairs_via_seeded_enumeration"

    for spec in (l0, l1):
        discipline = canonical._discipline(spec)
        assert discipline["construct_validity_pointer"] == spec.construct_validity_pointer
        assert "reporting_hardgate" in discipline
        assert discipline["reporting_hardgate"]["hardgate_id"] == canonical.REPORTING_HARDGATE_ID


def test_dgt_l1_controls_owns_l1_ood_mechanism_without_standalone_report(tmp_path, monkeypatch):
    spec = canonical._specs_by_name()["dgt-l1-controls"]
    names = {item.name for item in canonical.CANONICAL_REPORTS}
    artifacts = {item.json_artifact for item in canonical.CANONICAL_REPORTS}
    payload = _payload_for_spec(spec)
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    json_path = canonical._artifact_path(spec.json_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)

    assert "l1_ood_mechanism" in spec.required_json_keys
    assert payload["l1_ood_mechanism"]["verdict"] in {"memorization", "brittle-rule", "partial-rule"}
    assert payload["l1_ood_mechanism"]["owner"] == "dgt-l1-controls"
    assert "dgt-l1-ood-mechanism" not in names
    assert "reports/canonical/dgt-l1-ood-mechanism.json" not in artifacts


def test_reproduction_package_canonical_specs_are_auxiliary_pointer_owners():
    specs = canonical._specs_by_name()
    package = specs["reproduction-package"]
    check = specs["reproduction-check-result"]

    assert package.bundle_role == "auxiliary"
    assert check.bundle_role == "auxiliary"
    assert package.command == ("python3", "scripts/run_reproduction_package.py")
    assert check.command == ("python3", "scripts/run_reproduction_package.py")
    assert package.json_artifact == "reports/canonical/reproduction-package.json"
    assert package.markdown_artifact == "reports/canonical/reproduction-package.md"
    assert check.json_artifact == "reports/canonical/reproduction-check-result.json"
    assert check.markdown_artifact == "reports/canonical/reproduction-check-result.md"
    assert package.claim_capsule_pointer == "$.claim_capsule_ref"
    assert "reproduction_targets" in package.required_json_keys
    assert "target_results" in check.required_json_keys
    assert "source_artifacts" in check.required_json_keys
    assert "metric_ranges" not in package.required_json_keys
    assert package.name not in HG_P_CORE
    assert check.name not in HG_P_CORE


def test_reproduction_package_index_section_is_pointer_only():
    section = canonical._reproduction_package_index_section()
    payload = canonical._index([], generated_at="fixture", claim_verdict_rows=[])
    markdown = canonical._render_index_markdown(payload)

    assert section["status"] == "pointer-only"
    assert section["json_artifact"] == "reports/canonical/reproduction-package.json"
    assert section["check_result_json"] == "reports/canonical/reproduction-check-result.json"
    assert section["package_pointer"] == "reports/canonical/reproduction-package.json:$"
    assert section["check_result_pointer"] == "reports/canonical/reproduction-check-result.json:$"
    assert section["full_repro_target_count"] >= 3
    assert section["projection_only_target_count"] >= 1
    assert "hardgate_statuses" in section
    assert payload["reproduction_package"]["package_pointer"] == section["package_pointer"]
    assert "## Reproduction Package" in markdown
    serialized = json.dumps(section, sort_keys=True)
    assert "deterministic_seeds" not in serialized
    assert "metric_tolerance" not in serialized
    assert "ready-pass" not in serialized


def test_reproduction_package_producer_is_byte_stable_for_fixed_timestamp(tmp_path, monkeypatch):
    from scripts import run_reproduction_package as repro_runner

    for artifact in (
        "reports/canonical/dgt-l0-controls.json",
        "reports/canonical/dgt-l0-controls.fingerprint.json",
        "reports/canonical/dgt-l1-controls.json",
        "reports/canonical/dgt-l1-controls.fingerprint.json",
        "reports/canonical/dgt-neural-ablation.json",
        "reports/canonical/dgt-neural-ablation.fingerprint.json",
        "reports/canonical/dgt-ablation-null-decomposition.json",
        "reports/canonical/dgt-ablation-null-decomposition.fingerprint.json",
        "reports/canonical/discovery-gated-transformer.json",
        "reports/canonical/discovery-gated-transformer.fingerprint.json",
        "reports/canonical/claim_capsule.json",
        "reports/canonical/claim_graph.json",
        "reports/canonical/index.json",
        "reports/canonical/index.md",
        "configs/default_cost_protocol.yaml",
    ):
        source = canonical.SOURCE_ROOT / artifact
        if source.exists():
            target = tmp_path / artifact
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read_bytes())

    first = repro_runner.write_package(tmp_path, "fixture")
    first_json = (tmp_path / "reports/canonical/reproduction-package.json").read_text(encoding="utf-8")
    first_md = (tmp_path / "reports/canonical/reproduction-package.md").read_text(encoding="utf-8")
    second = repro_runner.write_package(tmp_path, "fixture")

    assert second == first
    assert (tmp_path / "reports/canonical/reproduction-package.json").read_text(encoding="utf-8") == first_json
    assert (tmp_path / "reports/canonical/reproduction-package.md").read_text(encoding="utf-8") == first_md


def test_run_reports_replaces_reproduction_package_result_after_regen(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    reports = canonical._specs_by_name()
    package = reports["reproduction-package"]
    check = reports["reproduction-check-result"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (package, check))
    calls = []

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name, mode))
        if mode == "verify":
            return _index_row_for_spec(spec) | {"fingerprint_status": "match", "fingerprint_reason": "match"}
        return _index_row_for_spec(spec) | {
            "status": "error",
            "fingerprint_status": "miss",
            "fingerprint_reason": "input-fingerprint",
        }

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", lambda spec, *, generated_at=None: calls.append(("fingerprint", spec.name)))
    monkeypatch.setattr(canonical, "_run_spec_producer", lambda spec, generated_at=None: calls.append(("producer", spec.name)))

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    by_name = {row["name"]: row for row in payload["reports"]}
    assert by_name["reproduction-package"]["fingerprint_status"] == "match"
    assert by_name["reproduction-check-result"]["fingerprint_status"] == "match"
    assert ("run-spec", "reproduction-package", "verify") in calls
    assert ("run-spec", "reproduction-check-result", "verify") in calls


def test_reproduction_package_validation_rejects_copied_owner_fact(tmp_path):
    spec = canonical._specs_by_name()["reproduction-package"]
    payload = _payload_for_spec(spec)
    payload["reproduction_targets"][0]["accuracy_mean"] = 1.0
    path = tmp_path / spec.json_artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    md_path = tmp_path / spec.markdown_artifact
    md_path.write_text("# fixture\n", encoding="utf-8")

    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    try:
        canonical.ROOT = tmp_path
        canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["reproduction_errors"]


def _write_fair_l1_decision_fixture(root: Path, *, comparison_id: str = "equal-validation-loss", gate_id: str = "FAIR-L1-HG2") -> None:
    path = root / "reports/canonical/fair-l1-decision.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    comparison_rows = [
        {"comparison_id": "equal-step", "decision": "resolved", "status": "pass"},
        {"comparison_id": "equal-compute", "decision": "resolved", "status": "pass"},
        {"comparison_id": "equal-loss-decrease", "decision": "resolved", "status": "pass"},
        {
            "comparison_id": comparison_id,
            "decision": "validation-loss-cell-missing",
            "status": "missing",
        },
    ]
    payload = {
        "schema_id": "bedc-quality-lab:fair-l1-decision",
        "artifact_id": "bedc-quality-lab:fair-l1-decision",
        "fair_alignment": {"comparison_rows": comparison_rows},
        "hardgates": {
            "FAIR-L1-HG2": {
                "gate_id": gate_id,
                "status": "fail",
            }
        },
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _reproduction_check_payload() -> dict[str, object]:
    return {
        "schema_id": "bedc-quality-lab:reproduction-check-result",
        "artifact_id": "bedc-quality-lab:reproduction-check-result",
        "generated_at": "fixture",
        "source_artifacts": {
            "package": "reports/canonical/reproduction-package.json",
            "runner": "scripts/run_reproduction_package.py",
        },
        "package_ref": "reports/canonical/reproduction-package.json:$",
        "profile": "structural",
        "target_results": [
            {
                "target_id": "dgt-l0-honest-rerun",
                "target_kind": "full-repro-ci",
                "status": "pass",
                "blocked_reason": None,
                "resolved_owner_pointers": [],
                "fingerprint_status": "pass",
                "tolerance_status": "pass",
                "rerun_artifact_refs": [],
                "failure_reasons": [],
                "ci_rehearsal_ref": None,
            },
            {
                "target_id": "fair-l1-training",
                "target_kind": "full-repro-ci",
                "status": "blocked",
                "blocked_reason": dict(canonical.FAIR_L1_BLOCKED_REASON),
                "resolved_owner_pointers": [],
                "fingerprint_status": "pass",
                "tolerance_status": "pass",
                "rerun_artifact_refs": [],
                "failure_reasons": ["fair-l1-training waits for seven-arm owner artifact"],
                "ci_rehearsal_ref": None,
            },
            {
                "target_id": "source-owned-block",
                "target_kind": "full-repro-ci",
                "status": "blocked",
                "blocked_reason": {
                    "category": "source-blocked",
                    "detail": "source-pointer-blocked",
                    "evidence_ref": "reports/canonical/reproduction-check-result.json:$.target_results",
                    "owner_gate_ref": None,
                    "dependency_ref": None,
                    "planning_context_ref": None,
                },
                "resolved_owner_pointers": [],
                "fingerprint_status": "pass",
                "tolerance_status": "blocked",
                "rerun_artifact_refs": [],
                "failure_reasons": ["pointer does not resolve: reports/canonical/missing.json:$"],
                "ci_rehearsal_ref": None,
            },
        ],
        "blocked_targets": ["fair-l1-training", "source-owned-block"],
        "failed_targets": [],
        "not_claimed": ["fixture"],
    }


def _write_reproduction_check_fixture(tmp_path: Path, payload: dict[str, object]) -> dict[str, object]:
    spec = canonical._specs_by_name()["reproduction-check-result"]
    canonical._write_json_atomic(canonical._artifact_path(spec.json_artifact), payload)
    canonical._write_text_atomic(canonical._artifact_path(spec.markdown_artifact), "# fixture\n")
    return canonical._artifact_validation(spec)


def test_reproduction_check_result_validation_accepts_six_key_blocked_reasons(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "pass"
    assert validation["reproduction_errors"] == []


@pytest.mark.parametrize("missing_key", ["owner_gate_ref", "dependency_ref", "planning_context_ref"])
def test_reproduction_check_result_validation_rejects_missing_blocked_reason_keys(tmp_path, monkeypatch, missing_key):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()
    fair_row = payload["target_results"][1]
    del fair_row["blocked_reason"][missing_key]

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert {
        "path": "$.target_results[1].blocked_reason",
        "message": f"blocked_reason missing key: {missing_key}",
    } in validation["reproduction_errors"]


def test_reproduction_check_result_validation_rejects_pass_row_with_blocked_reason(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()
    payload["target_results"][0]["blocked_reason"] = {
        "category": "source-blocked",
        "detail": "source-pointer-blocked",
        "evidence_ref": "reports/canonical/reproduction-check-result.json:$.target_results",
        "owner_gate_ref": None,
        "dependency_ref": None,
        "planning_context_ref": None,
    }

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert {
        "path": "$.target_results[0].blocked_reason",
        "message": "non-blocked rows require blocked_reason null",
    } in validation["reproduction_errors"]


def test_reproduction_check_result_validation_rejects_prose_only_blocked_row(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()
    payload["target_results"][2]["blocked_reason"] = None

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert {
        "path": "$.target_results[2].blocked_reason",
        "message": "blocked rows require structured blocked_reason",
    } in validation["reproduction_errors"]


def test_reproduction_check_result_validation_rejects_alias_fields(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()
    payload["target_results"][1]["dependency_ref"] = "github:issue:1196"
    payload["target_results"][1]["blocked_reason"]["evidence_pointer"] = canonical.FAIR_L1_BLOCKED_REASON["evidence_ref"]

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert any(error["message"] == "blocked_reason alias field is forbidden: dependency_ref" for error in validation["reproduction_errors"])
    assert any(error["message"] == "blocked_reason has unknown key: evidence_pointer" for error in validation["reproduction_errors"])


def test_reproduction_check_result_validation_treats_failure_reasons_as_non_authority(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path)
    payload = _reproduction_check_payload()
    source_row = payload["target_results"][2]
    source_row["failure_reasons"] = ["missing-validation-loss-cell"]
    source_row["blocked_reason"]["category"] = "source-blocked"

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "pass"
    assert validation["reproduction_errors"] == []


def test_reproduction_check_result_validation_rejects_fair_l1_evidence_drift(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path, comparison_id="equal-loss-decrease")
    payload = _reproduction_check_payload()

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert {
        "path": "$.target_results[1].blocked_reason.evidence_ref",
        "message": "fair-l1 evidence row does not match equal-validation-loss",
    } in validation["reproduction_errors"]


def test_reproduction_check_result_validation_rejects_fair_l1_owner_gate_drift(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_fair_l1_decision_fixture(tmp_path, gate_id="FAIR-L1-HG3")
    payload = _reproduction_check_payload()

    validation = _write_reproduction_check_fixture(tmp_path, payload)

    assert validation["status"] == "fail"
    assert {
        "path": "$.target_results[1].blocked_reason.owner_gate_ref",
        "message": "fair-l1 owner gate does not match FAIR-L1-HG2",
    } in validation["reproduction_errors"]


def test_reproduction_check_result_validation_rejects_malformed_target_row(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["reproduction-check-result"]
    payload = {
        "schema_id": "bedc-quality-lab:reproduction-check-result",
        "artifact_id": "bedc-quality-lab:reproduction-check-result",
        "generated_at": "fixture",
        "source_artifacts": {
            "package": "reports/canonical/reproduction-package.json",
            "runner": "scripts/run_reproduction_package.py",
        },
        "package_ref": "reports/canonical/reproduction-package.json:$",
        "profile": "projection",
        "target_results": [
            {
                "target_id": "canonical-index-view",
                "target_kind": "projection-only",
                "status": "pass",
                "resolved_owner_pointers": [],
                "fingerprint_status": "pass",
                "tolerance_status": "pass",
                "rerun_artifact_refs": [],
                "failure_reasons": [],
                "ci_rehearsal_ref": None,
            },
            {
                "target_id": "tampered-row",
                "target_kind": "projection-only",
                "status": "unknown",
            },
        ],
        "blocked_targets": [],
        "failed_targets": [],
        "not_claimed": ["fixture"],
    }
    canonical._write_json_atomic(canonical._artifact_path(spec.json_artifact), payload)
    canonical._write_text_atomic(canonical._artifact_path(spec.markdown_artifact), "# fixture\n")

    validation = canonical._artifact_validation(spec)

    assert validation["status"] == "fail"
    assert validation["reproduction_errors"] == [
        {"path": "$.target_results", "message": "invalid target result row"}
    ]


def test_reproduction_check_result_validation_rejects_wrong_schema(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["reproduction-check-result"]
    payload = {
        "schema_id": "bedc-quality-lab:reproduction-package",
        "artifact_id": "bedc-quality-lab:reproduction-check-result",
        "generated_at": "fixture",
        "source_artifacts": {
            "package": "reports/canonical/reproduction-package.json",
            "runner": "scripts/run_reproduction_package.py",
        },
        "package_ref": "reports/canonical/reproduction-package.json:$",
        "profile": "projection",
        "target_results": [],
        "blocked_targets": [],
        "failed_targets": [],
        "not_claimed": ["fixture"],
    }
    canonical._write_json_atomic(canonical._artifact_path(spec.json_artifact), payload)
    canonical._write_text_atomic(canonical._artifact_path(spec.markdown_artifact), "# fixture\n")

    validation = canonical._artifact_validation(spec)

    assert validation["status"] == "fail"
    assert validation["reproduction_errors"] == [
        {"path": "$.schema_id", "message": "invalid reproduction check-result schema"}
    ]


def test_boundary_report_spec_promotion_schema_is_exact():
    spec = canonical._specs_by_name()["dgt-l1-boundary-report"]

    assert spec.bundle_role == "auxiliary"
    assert spec.claim_promotion_eligible is False
    assert spec.positive_claim_pointer == "$.claim_promotion_exclusion"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.control_pointer is None
    assert spec.no_control_rationale_pointer == "$.claim_promotion_exclusion"
    assert "artifact_role" in spec.required_json_keys
    assert "claim_promotion_exclusion" in spec.required_json_keys
    assert "scaling_claim_block" in spec.required_json_keys


def test_positive_claim_cells_exclude_ineligible_reports(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    boundary_spec = canonical._specs_by_name()["dgt-l1-boundary-report"]
    core_spec = canonical._specs_by_name()["mixing-family-sweep"]
    for spec in (boundary_spec, core_spec):
        payload = _payload_for_spec(spec)
        canonical._write_json_atomic(canonical._artifact_path(spec.json_artifact), payload)
        canonical._write_text_atomic(canonical._artifact_path(spec.markdown_artifact), "# fixture\n")
    reports = [
        {
            "name": spec.name,
            "bundle_role": spec.bundle_role,
            "discipline": canonical._discipline(spec),
        }
        for spec in (boundary_spec, core_spec)
    ]

    cells = canonical._claims_nonclaims(reports)

    assert {cell["report"] for cell in cells["positive_claim_cells"]} == {"mixing-family-sweep"}
    assert cells["promotion_exclusion_cells"] == [
        {
            "report": "dgt-l1-boundary-report",
            "bundle_role": "auxiliary",
            "artifact_role": "boundary_block",
            "claim_promotion_eligible": False,
            "exclusion_pointer": "$.claim_promotion_exclusion",
            "block_pointer": "$.scaling_claim_block",
        }
    ]


def test_discovery_promotion_requires_claim_promotion_eligible():
    spec_names = {spec.name for spec in canonical._discovery_map_reports()}

    assert "dgt-l1-boundary-report" not in spec_names



def test_dgt_model_card_canonical_spec_is_auxiliary_pointer_projection():
    spec = canonical._specs_by_name()["dgt-model-card"]
    section = canonical._dgt_model_card_index_section()

    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_model_card.py")
    assert spec.json_artifact == "reports/canonical/dgt-model-card.json"
    assert spec.markdown_artifact == "reports/canonical/dgt-model-card.md"
    assert "schema_id" in spec.required_json_keys
    assert "not_intended_use" in spec.required_json_keys
    assert "card_hardgates" in spec.required_json_keys
    assert section["card_pointer"] == "reports/canonical/dgt-model-card.json:$"
    assert "status" not in section
    assert "upstream_status" not in section


def test_dgt_model_card_report_row_consumes_card_hardgates():
    spec = canonical._specs_by_name()["dgt-model-card"]
    result = canonical._run_spec(spec, reuse_existing=True)
    payload = json.loads((canonical.ROOT / spec.json_artifact).read_text(encoding="utf-8"))

    assert result["validation"]["model_card_errors"] == []
    assert result["validation"]["status"] == "pass"
    assert result["status"] == "pass"
    assert payload["status"] == "pass"
    assert payload["card_hardgates"]["status"] == "pass"
    assert payload["missing_source_refs"] == []
    assert payload["training_facts"]["evidence_provenance"]["status"] == "resolved"
    provenance = next(
        row
        for row in payload["source_artifacts"]
        if row["source_owner"] == "canonical-index-evidence-provenance"
    )
    assert provenance["source_pointer"] == "reports/canonical/index.json:$.evidence_provenance"
    assert provenance["status"] == "resolved"


def test_dgt_model_card_missing_source_fixture_fails_closed(tmp_path):
    source_root = canonical.SOURCE_ROOT
    source_artifacts = (
        "reports/canonical/dgt-l0-controls.json",
        "reports/canonical/dgt-l1-controls.json",
        "reports/canonical/fair-l1-decision.json",
        "reports/canonical/dgt-base-undertraining-audit.json",
        "reports/canonical/dgt-ablation-null-decomposition.json",
        "reports/canonical/discovery-gated-transformer.json",
    )
    for artifact in source_artifacts:
        target = tmp_path / artifact
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text((source_root / artifact).read_text(encoding="utf-8"), encoding="utf-8")

    index_payload = json.loads((source_root / "reports/canonical/index.json").read_text(encoding="utf-8"))
    index_payload.pop("evidence_provenance", None)
    index_path = tmp_path / "reports/canonical/index.json"
    index_path.parent.mkdir(parents=True, exist_ok=True)
    index_path.write_text(json.dumps(index_payload, sort_keys=True) + "\n", encoding="utf-8")

    card = canonical.write_dgt_model_card(root=tmp_path, generated_at="fixture-time")
    errors = [error.as_dict() for error in canonical.validate_dgt_model_card(card, tmp_path)]

    assert card["status"] == "blocked"
    assert card["card_hardgates"]["status"] == "blocked"
    assert card["missing_source_refs"] == ["reports/canonical/index.json:$.evidence_provenance"]
    assert card["training_facts"]["evidence_provenance"]["status"] == "blocked"
    provenance = next(
        row
        for row in card["source_artifacts"]
        if row["source_owner"] == "canonical-index-evidence-provenance"
    )
    provenance_index = card["source_artifacts"].index(provenance)
    assert provenance["source_pointer"] == "reports/canonical/index.json:$.evidence_provenance"
    assert provenance["status"] == "pointer-missing"
    assert errors == [
        {
            "gate_id": "CARD-HG9",
            "path": f"$.source_artifacts[{provenance_index}].status",
            "message": "source pointer is not resolved",
        }
    ]


def test_no_standalone_dgt_component_ablation_registered():
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert names.isdisjoint(
        {
            "dgt-component-ablation",
            "discovery-gated-transformer-ablation",
            "component-ablation",
        }
    )
    assert "reports/canonical/dgt-component-ablation.json" not in artifacts
    assert "reports/canonical/discovery-gated-transformer-ablation.json" not in artifacts
    assert "reports/canonical/dgt_d5o_readiness_ledger.json" not in artifacts
    assert "reports/canonical/discovery-gated-transformer-d5-o-readiness.json" not in artifacts


def test_no_standalone_tool_use_dgt_owner_registered():
    serialized = json.dumps(
        [
            {
                "name": spec.name,
                "json_artifact": spec.json_artifact,
                "markdown_artifact": spec.markdown_artifact,
                "command": list(spec.command),
            }
            for spec in canonical.CANONICAL_REPORTS
        ],
        sort_keys=True,
    )

    for forbidden in ("tool-use-dgt", "tool-use-toy-dgt", "tool_use_dgt", "tool_use_toy_dgt"):
        assert forbidden not in serialized


def test_drt_manifest_preserves_certificate_guided_sibling_specs():
    specs = canonical._specs_by_name()
    drt = specs["discovery-regularized-training"]

    assert "certificate_guided_dn_preservation" in drt.required_json_keys
    assert specs["certificate-guided-training"].json_artifact == "reports/canonical/certificate-guided-training.json"
    assert specs["certificate-guided-discovery"].json_artifact == "reports/canonical/certificate-guided-discovery.json"
    assert "certificate-guided-training" not in drt.name
    assert "certificate-guided-discovery" not in drt.name
    assert not any(
        token in json.dumps(
            {
                "name": drt.name,
                "command": drt.command,
                "required_json_keys": drt.required_json_keys,
                "scope_pointer": drt.scope_pointer,
                "positive_claim_pointer": drt.positive_claim_pointer,
            },
            sort_keys=True,
        ).lower()
        for token in ("replace certificate-guided", "cover certificate-guided")
    )


def test_ledger_aware_transformer_required_surface_is_signal_owner():
    spec = canonical._specs_by_name()["ledger-aware-transformer"]

    assert spec.command == ("python3", "scripts/run_ledger_aware_transformer.py")
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.control_pointer == "$.control_protocol"
    assert {
        "projector",
        "run_artifacts",
        "hardgate",
        "failed_gate",
        "discovery_map_signal",
        "matched_random_control",
        "parameter_matched_baseline",
        "mechanism_certificate",
        "torch_training_evidence",
        "revocation_rows",
        "forbidden_claim_term_audit",
    }.issubset(set(spec.required_json_keys))
    assert "terminal_verdict" not in spec.required_json_keys
    assert "surfaces" not in spec.required_json_keys


def test_lat_canonical_report_requires_parameter_matched_baseline():
    spec = canonical._specs_by_name()["ledger-aware-transformer"]
    payload = json.loads((canonical.ROOT / spec.json_artifact).read_text(encoding="utf-8"))

    assert "parameter_matched_baseline" in spec.required_json_keys
    assert payload["parameter_matched_baseline"]["status"] == "pass"
    assert payload["positive_claim"]["parameter_matched_baseline_pointer"] == "$.parameter_matched_baseline"
    assert payload["discovery_map_signal"]["parameter_matched_baseline_pointer"] == "$.parameter_matched_baseline"
    assert pointer_value(payload, payload["positive_claim"]["parameter_matched_baseline_pointer"]) is not None
    assert pointer_value(payload, payload["discovery_map_signal"]["parameter_matched_baseline_pointer"]) is not None
    assert {"artifact": spec.json_artifact, "pointer": "$.parameter_matched_baseline"} in payload["claim_capsule_ref"]["capsule"]["model_claim"]["baselines"]
    for row in payload["records"]:
        assert row["parameter_matched_baseline"]["arm"] == "parameter_matched_no_ledger_transformer"
        assert row["parameter_matched_baseline"]["uses_forbidden_columns"] is False
        assert pointer_value(payload, row["parameter_matched_baseline"]["cost_pointer"]) is not None


def test_lat_canonical_report_embeds_mechanism_certificate_under_existing_owner():
    spec = canonical._specs_by_name()["ledger-aware-transformer"]
    payload = json.loads((canonical.ROOT / spec.json_artifact).read_text(encoding="utf-8"))

    assert [item.name for item in canonical.CANONICAL_REPORTS].count("ledger-aware-transformer") == 1
    assert "mechanism_certificate" in spec.required_json_keys
    assert "component_ablation" in spec.required_json_keys
    assert payload["artifact_id"] == "bedc-quality-lab:ledger-aware-transformer"
    assert payload["mechanism_certificate"]["owner_pointer"] == (
        "reports/canonical/ledger-aware-transformer.json:$.mechanism_certificate"
    )
    assert payload["discovery_map_signal"]["mechanism_certificate_pointer"] == "$.mechanism_certificate"
    assert payload["positive_claim"]["mechanism_certificate_pointer"] == "$.mechanism_certificate"
    assert pointer_value(payload, payload["discovery_map_signal"]["mechanism_certificate_pointer"]) == payload["mechanism_certificate"]
    assert payload["mechanism_certificate"]["claim_component_ids"] == ["ledger_head", "gap_head"]
    assert "route_head" not in payload["mechanism_certificate"]["claim_component_ids"]


def test_committed_canonical_bundle_covers_every_registered_report():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    discovery_payload = json.loads((canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()
    registered = {spec.name: spec for spec in canonical.CANONICAL_REPORTS}
    discovery_registered = {spec.name: spec for spec in canonical._discovery_map_reports()}

    index_reports = {row["name"]: row for row in index_payload["reports"]}
    discovery_rows = {row["report"]: row for row in discovery_payload["rows"]}
    claim_ids = {row["claim_id"] for row in claim_rows}

    assert set(index_reports) == set(registered)
    assert set(discovery_registered).issubset(discovery_rows)
    assert {f"claim:{name}" for name in discovery_registered}.issubset(claim_ids)
    for name, spec in registered.items():
        assert index_reports[name]["json_artifact"] == spec.json_artifact
        assert (canonical.ROOT / spec.json_artifact).exists()
        assert (canonical.ROOT / spec.markdown_artifact).exists()
    for name, spec in discovery_registered.items():
        assert discovery_rows[name]["json_artifact"] == spec.json_artifact


def test_issue_1012_sidecars_are_committed_owner_sidecars_not_canonical_specs():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    spec_names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    spec_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    sidecar_section = index_payload["issue_1012_sidecars"]
    sidecars = {row["name"]: row for row in sidecar_section["sidecars"]}

    assert sidecar_section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert set(sidecars) == {
        "lejepa-derivative-bridge",
        "hermite-degree-vs-behavioral-derivative",
        "spectral-jet-report",
    }
    assert not set(sidecars).intersection(spec_names)
    for row in sidecars.values():
        assert row["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
        assert row["artifact"] not in spec_artifacts
        assert (canonical.ROOT / row["artifact"]).exists()

    lejepa = json.loads((canonical.ROOT / canonical.LEJEPA_DERIVATIVE_BRIDGE_JSON_ARTIFACT).read_text(encoding="utf-8"))
    spectral = json.loads((canonical.ROOT / canonical.SPECTRAL_JET_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert lejepa["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert spectral["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert "lejepa-hermite-spectral-bridge" not in spec_names
    assert "spectral-jet-report" not in spec_names


def test_issue_1012_sidecar_owner_pointers_and_nongaussian_refs_resolve():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    section = index_payload["issue_1012_sidecars"]
    owner_payloads = {
        "lejepa-theorem-ledger": json.loads((canonical.ROOT / "reports/canonical/lejepa_theorem_ledger.json").read_text(encoding="utf-8")),
        "spectral-ablation-hinge": json.loads((canonical.ROOT / "reports/canonical/spectral-ablation-hinge.json").read_text(encoding="utf-8")),
    }

    for row in section["sidecars"]:
        owner = owner_payloads[row["owner_report"]]
        artifact, pointer = split_artifact_pointer(row["owner_pointer"])
        assert artifact == row["owner_artifact"]
        assert pointer_value(owner, pointer) is not None

    spectral_row = next(row for row in section["sidecars"] if row["name"] == "spectral-jet-report")
    assert {ref["artifact"] for ref in spectral_row["nongaussian_references"]} == {
        "reports/canonical/nongaussian-distribution-sweep.json"
    }
    assert {ref["pointer"] for ref in spectral_row["nongaussian_references"]} == {"$.records", "$.not_claimed"}
    for ref in spectral_row["nongaussian_references"]:
        assert resolve_artifact_pointer(canonical.ROOT, f"{ref['artifact']}:{ref['pointer']}") is not None


def test_issue_1012_owner_specs_expose_sidecar_metadata_without_registration():
    reports = {
        row["name"]: row
        for row in json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))["reports"]
    }
    lejepa_sidecars = reports["lejepa-theorem-ledger"]["discipline"]["sidecars"]
    spectral_sidecars = reports["spectral-ablation-hinge"]["discipline"]["sidecars"]

    assert [row["artifact"] for row in lejepa_sidecars] == [
        canonical.LEJEPA_DERIVATIVE_BRIDGE_JSON_ARTIFACT,
        canonical.HERMITE_BEHAVIOR_MARKDOWN_ARTIFACT,
    ]
    assert [row["artifact"] for row in spectral_sidecars] == [canonical.SPECTRAL_JET_JSON_ARTIFACT]
    assert all(row["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS" for row in lejepa_sidecars + spectral_sidecars)


def test_bcd_sidecar_artifacts_are_schema_owned_and_fail_closed():
    schema = json.loads((canonical.ROOT / canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT).read_text(encoding="utf-8"))
    ledger = json.loads((canonical.ROOT / canonical.DERIVATIVE_ORDER_LEDGER_ARTIFACT).read_text(encoding="utf-8"))
    matrix = json.loads((canonical.ROOT / canonical.JET_COVERAGE_MATRIX_ARTIFACT).read_text(encoding="utf-8"))
    spec = (canonical.ROOT / canonical.BOUNDARY_CAUSAL_DERIVATIVE_SPEC_ARTIFACT).read_text(encoding="utf-8")

    assert schema["schema_id"] == canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ID
    assert schema["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert set(schema["$defs"]) == {
        "BoundarySpec",
        "DerivativeSpec",
        "CausalSpec",
        "IrreducibilitySpec",
        "HardGate",
        "LedgerEntry",
        "CoverageCell",
    }
    assert [gate["gate_id"] for gate in schema["hardgates"]] == [f"BCD-HG{index}" for index in range(1, 6)]
    assert all("fail_closed" in gate["status_values"] for gate in schema["hardgates"])

    for payload in (ledger, matrix):
        assert payload["schema_id"] == canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ID
        assert payload["schema_artifact"] == canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT
        assert payload["status"] == "no_rows_yet"
        assert payload["owner_pointers"]["schema" if payload is matrix else "hardgate"].startswith(
            canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT
        )

    assert ledger["entries"] == []
    assert matrix["surfaces"] == []
    assert matrix["orders"] == []
    assert matrix["cells"] == []
    assert "## Scope Seal" in spec
    assert "## Nonclaim Boundary" in spec
    assert canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT in spec


def test_bcd_index_sidecar_is_pointer_only_not_canonical_report():
    section = canonical._boundary_causal_derivative_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert "boundary-causal-derivative" not in names
    assert canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT not in artifacts
    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert payload["boundary_causal_derivative"] == section
    assert {
        section["schema_artifact"],
        section["spec_artifact"],
        section["derivative_order_ledger_artifact"],
        section["jet_coverage_matrix_artifact"],
    } == {
        canonical.BOUNDARY_CAUSAL_DERIVATIVE_SCHEMA_ARTIFACT,
        canonical.BOUNDARY_CAUSAL_DERIVATIVE_SPEC_ARTIFACT,
        canonical.DERIVATIVE_ORDER_LEDGER_ARTIFACT,
        canonical.JET_COVERAGE_MATRIX_ARTIFACT,
    }
    assert "Boundary-Causal-Derivative" in markdown
    assert "BoundarySpec resolves to an explicit lab-local scope seal" not in markdown
    assert "DerivativeSpec names a finite surface" not in markdown


def test_bcd_spec_ledger_and_matrix_do_not_report_rows_or_positive_facts():
    forbidden = {
        "detected",
        "positive_irred_jet_gain",
        "quality_gain_by_order",
        "ledger_debt_by_order",
        "minimal_sufficient_order",
    }
    spec = (canonical.ROOT / canonical.BOUNDARY_CAUSAL_DERIVATIVE_SPEC_ARTIFACT).read_text(encoding="utf-8")
    ledger = json.loads((canonical.ROOT / canonical.DERIVATIVE_ORDER_LEDGER_ARTIFACT).read_text(encoding="utf-8"))
    matrix = json.loads((canonical.ROOT / canonical.JET_COVERAGE_MATRIX_ARTIFACT).read_text(encoding="utf-8"))
    sidecar_text = json.dumps({"ledger": ledger, "matrix": matrix}, sort_keys=True)

    assert not forbidden.intersection(ledger)
    assert not forbidden.intersection(matrix)
    assert not any(term in sidecar_text for term in forbidden)
    assert "BoundarySpec resolves to an explicit lab-local scope seal" not in spec
    assert "DerivativeSpec names a finite surface" not in spec
    assert "does not claim" in spec


def test_committed_canonical_bundle_matches_generation_chain():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    discovery_payload = json.loads((canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()
    generated_index, generated_discovery, generated_claims = _canonical_bundle_payloads_for_timestamps(
        index_timestamp=index_payload["generated_at"],
        discovery_timestamp=discovery_payload["generated_at"],
    )

    assert index_payload == generated_index
    assert discovery_payload == generated_discovery
    _assert_dgt_discovery_map_row_uses_l0_consumption(
        next(row for row in discovery_payload["rows"] if row["report"] == "discovery-gated-transformer")
    )
    assert claim_rows == generated_claims


def test_canonical_index_dashboard_section_is_pointer_only():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    section = index_payload["dashboard"]
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    artifacts = {
        path
        for spec in canonical.CANONICAL_REPORTS
        for path in (spec.json_artifact, spec.markdown_artifact)
    }

    assert section["status"] == "pointer-only"
    assert section["artifact_id"] == "bedc-quality-lab:dashboard"
    assert section["canonical_role"] == "navigation_view_not_fact_source"
    assert section["source_index_artifact"] == "reports/canonical/index.json"
    assert len(section["panels"]) == 8
    assert "dashboard" not in names
    assert not (canonical.ROOT / "reports/canonical/dashboard.json").exists()
    assert not (canonical.ROOT / "reports/canonical/dashboard.md").exists()
    assert "reports/canonical/dashboard.json" not in artifacts
    assert "reports/canonical/dashboard.md" not in artifacts


def test_canonical_index_dashboard_panel_pointers_resolve():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    panels = index_payload["dashboard"]["panels"]

    assert [panel["panel_id"] for panel in panels] == [
        "discovery-map",
        "coverage-matrix",
        "claim-graph",
        "scorecard",
        "negative-witnesses",
        "negative-witness-summary",
        "d5-status",
        "model-comparison",
    ]
    for panel in panels:
        assert resolve_artifact_pointer(canonical.ROOT, panel["artifact_pointer"]) is not None


def test_canonical_index_dashboard_rejects_cached_owner_facts():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    keys = set(_walk_keys(index_payload["dashboard"]))

    assert keys.isdisjoint(
        {
            "rows",
            "records",
            "coverage_matrix",
            "level_counts",
            "hardgate_status",
            "node_count",
            "metric_count",
            "expected_kind_count",
            "discovery_level",
            "terminal_verdict",
            "scorecard_ready",
            "claim_verdict",
            "failed_gate",
            "what_was_learned",
        }
    )


def test_canonical_index_dashboard_missing_owner_fails_closed():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    section = json.loads(json.dumps(index_payload["dashboard"]))
    section["panels"][0]["artifact_pointer"] = "reports/canonical/missing-dashboard-owner.json:$"
    section["panels"][1]["artifact_pointer"] = "reports/canonical/discovery_map.json:$.missing_dashboard_panel"

    unresolved = canonical._validate_dashboard_index_section(section, root=canonical.ROOT)

    assert unresolved == [
        "reports/canonical/missing-dashboard-owner.json:$",
        "reports/canonical/discovery_map.json:$.missing_dashboard_panel",
    ]


def test_model_comparison_sidecar_is_indexed_pointer_only():
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")
    section = canonical._model_comparison_index_section(payload)
    index_payload = canonical._index([], generated_at="2030-01-01T00:00:00+00:00")
    markdown = canonical._render_index_markdown(index_payload)

    assert section["json_artifact"] == canonical.MODEL_COMPARISON_JSON_ARTIFACT
    assert section["markdown_artifact"] == canonical.MODEL_COMPARISON_MARKDOWN_ARTIFACT
    assert section["models_pointer"] == "reports/canonical/model-comparison.json:$.models"
    assert "models" not in section
    assert "rows" not in section
    assert index_payload["model_comparison"]["models_pointer"] == section["models_pointer"]
    assert "## Model Comparison" in markdown
    assert "| `base_transformer` |" not in markdown


def test_model_comparison_rows_cover_issue_model_set_fail_closed():
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")
    rows = {row["model_id"]: row for row in payload["models"]}

    assert list(rows) == [
        "dgt",
        "base_transformer",
        "matched_random_structural_control",
        "ledger-aware-transformer",
        "certificate-gated-attention",
        "discovery-regularized-training",
        "mechanism-seeking-network",
    ]
    assert rows["ledger-aware-transformer"]["status"] == "ready"
    assert rows["dgt"]["status"] == "resolved"
    assert rows["base_transformer"]["status"] == "resolved"
    assert rows["matched_random_structural_control"]["status"] == "resolved"


def test_model_comparison_rejects_accuracy_only_ranking():
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")
    keys = set(_walk_keys(payload))

    assert keys.isdisjoint({"rank", "total_score", "accuracy_rank", "winner", "global_winner"})
    assert payload["ranking_key"] == ["quality_q", "JetCoverage"]


def test_model_comparison_ranking_key_is_claim_specific(monkeypatch):
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")
    assert payload["ranking_key"] == ["quality_q", "JetCoverage"]
    assert payload["ordering"]["status"] == "ready"

    real_resolve = canonical._resolve_committed_artifact_pointer

    def missing_quality_q(root, pointer):
        if pointer == "reports/runs/model-comparison/dgt/evidence_envelope.json:$.metrics.quality_q":
            return None
        return real_resolve(root, pointer)

    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", missing_quality_q)
    blocked = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")

    assert blocked["hardgates"]["MC-HG7"]["status"] == "fail"
    assert blocked["ordering"]["status"] == "not_ready"


def test_model_comparison_hardgates_fail_closed(monkeypatch):
    real_resolve = canonical._resolve_committed_artifact_pointer

    def missing_required_controls(root, pointer):
        blocked_fragments = ("matched_random_structural_control/evidence_envelope.json",)
        if any(fragment in pointer for fragment in blocked_fragments):
            return None
        return real_resolve(root, pointer)

    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", missing_required_controls)
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")

    assert payload["hardgates"]["MC-HG2"]["status"] == "fail"
    assert payload["hardgates"]["MC-HG9"]["status"] == "pass"
    assert payload["status"] == "not_ready"


def test_model_comparison_metric_pointers_resolve_or_mark_missing():
    payload = canonical._build_model_comparison(generated_at="2030-01-01T00:00:00+00:00")
    expected_metrics = {
        "task_accuracy",
        "ood_accuracy",
            "UER",
            "UER_reduction",
            "FalseLedgerRate",
            "CriticalUER",
            "classifier_shift_count",
            "order",
            "quality_q",
            "cost",
            "negative_witnesses",
            "JetCoverage",
        }

    for row in payload["models"]:
        assert set(row["metrics"]) == expected_metrics
        for metric in row["metrics"].values():
            assert set(metric) == {"pointer", "status", "value"}
            assert metric["status"] in {"resolved", "missing"}


def test_model_discovery_suite_removed_from_backend_exports():
    import bedc_quality_lab.backends as backends

    assert "model_discovery" not in backends.__all__
    assert not hasattr(backends, "ModelDiscoveryBackendEvidenceAdapter")
    assert not (canonical.ROOT / "reports/runs/model-discovery-suite/claim_capsule.json").exists()
    assert not (canonical.ROOT / "reports/runs/model-discovery-suite/summary.json").exists()


def test_committed_discovery_map_coverage_matrix_is_full_target_set_and_round_trips():
    path = canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT
    payload = json.loads(path.read_text(encoding="utf-8"))
    reloaded = json.loads(json.dumps(payload))

    validate_discovery_map_payload(reloaded, root=canonical.ROOT)

    cells = payload["coverage_matrix"]["cells"]
    assert set(payload["coverage_matrix"]) == {"status", "hardgates", "cells"}
    assert {cell["component_id"] for cell in cells} == discovery_map.COVERAGE_COMPONENT_IDS
    assert all(set(cell) == discovery_map.COVERAGE_CELL_FIELDS for cell in cells)
    assert payload["coverage_matrix"]["status"] == "pointer-only"
    assert {gate["status"] for gate in payload["coverage_matrix"]["hardgates"].values()} == {"pass"}
    assert "models" not in payload["coverage_matrix"]
    assert "surfaces" not in payload["coverage_matrix"]


def _committed_discovery_map_row(report: str = "fixture") -> dict[str, object]:
    return {
        "report": report,
        "json_artifact": "reports/canonical/fixture.json",
        "markdown_artifact": "reports/canonical/fixture.md",
        "discovery_level": "D1",
        "projection_status": "projected",
        "evidence_pointer": "$.positive",
        "audit_status": "valid",
        "audit_reason": "",
        "evidence_type": "deterministic_projection",
        "evidence_provenance_pointer": evidence_provenance_pointer_for_report(report),
    }


@pytest.mark.parametrize(
    ("field_name", "replacement", "message"),
    [
        ("evidence_type", "__missing__", "requires owner evidence_type"),
        ("evidence_type", None, "requires owner evidence_type"),
        ("evidence_provenance_pointer", "__missing__", "requires owner evidence provenance pointer"),
        ("evidence_provenance_pointer", None, "requires owner evidence provenance pointer"),
        (
            "evidence_provenance_pointer",
            "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.missing",
            "requires owner evidence provenance pointer",
        ),
    ],
)
def test_committed_discovery_map_round_trip_rejects_provenance_field_mutations(
    tmp_path,
    monkeypatch,
    field_name,
    replacement,
    message,
):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True)
    row = _committed_discovery_map_row()
    if replacement == "__missing__":
        row.pop(field_name)
    else:
        row[field_name] = replacement
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"rows": [row]}), encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", canonical_dir)

    with pytest.raises(ValueError, match=message):
        canonical._validate_committed_discovery_map_round_trip()


def test_discovery_map_generation_error_fallback_validates_committed_payload(tmp_path, monkeypatch):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True)
    row = _committed_discovery_map_row()
    row.pop("evidence_type")
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"rows": [row]}), encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", canonical_dir)
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_discovery_map",
        types.SimpleNamespace(
            build_discovery_map=lambda *args, **kwargs: (_ for _ in ()).throw(
                ValueError("generated discovery map rejected")
            )
        ),
    )

    with pytest.raises(ValueError, match="requires owner evidence_type"):
        canonical._index([], generated_at="2030-01-01T00:00:00+00:00")


def test_evidence_provenance_owner_section_rejects_malformed_committed_discovery_map(tmp_path, monkeypatch):
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True)
    row = _committed_discovery_map_row()
    row["evidence_provenance_pointer"] = None
    (canonical_dir / "discovery_map.json").write_text(json.dumps({"rows": [row]}), encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", canonical_dir)

    with pytest.raises(ValueError, match="requires owner evidence provenance pointer"):
        canonical._write_evidence_provenance_owner_section(generated_at="2030-01-01T00:00:00+00:00")


def test_coverage_matrix_pointers_resolve_and_dn_cells_point_to_negative_witness():
    payload = json.loads((canonical.ROOT / canonical.DISCOVERY_MAP_JSON_ARTIFACT).read_text(encoding="utf-8"))

    for cell in payload["coverage_matrix"]["cells"]:
        for field in discovery_map.COVERAGE_POINTER_FIELDS:
            pointer = cell[field]
            if pointer is not None:
                assert _resolve_artifact_pointer(canonical.ROOT, pointer) is not None
        if cell["component_id"].endswith("-DN"):
            assert cell["negative_witness_pointer"] is not None
        else:
            assert cell["mechanism_certificate_pointer"] is not None or cell["debt_pointer"] is not None


def _coverage_fixture():
    return discovery_map._build_coverage_matrix(rows=[], root=canonical.ROOT)


def test_coverage_matrix_validator_rejects_forbidden_keys_and_component_set_drift():
    coverage = _coverage_fixture()
    coverage["cells"] = coverage["cells"][:-1]
    coverage["hardgates"] = discovery_map._coverage_hardgate_rows(coverage["cells"], root=canonical.ROOT)
    coverage["status"] = "fail-closed"
    with pytest.raises(ValueError, match="component set mismatch"):
        validate_coverage_matrix(coverage, root=canonical.ROOT, expected_component_ids=discovery_map.COVERAGE_COMPONENT_IDS)

    forbidden = _coverage_fixture()
    forbidden["cells"][0]["classifier_reasons"] = ["copied"]
    with pytest.raises(ValueError, match="schema mismatch|copies owner facts"):
        validate_coverage_matrix(forbidden, root=canonical.ROOT)


def test_coverage_matrix_cov_hg_fail_closed_semantics():
    base = _coverage_fixture()

    owner_missing = json.loads(json.dumps(base))
    owner_missing["cells"][0]["canonical_owner_pointer"] = None
    owner_missing["hardgates"] = discovery_map._coverage_hardgate_rows(owner_missing["cells"], root=canonical.ROOT)
    owner_missing["cells"][0]["hardgate_status"] = "fail"
    owner_missing["cells"][0]["hardgate_reason"] = "COV-HG1-owner"
    owner_missing["status"] = "fail-closed"
    validated = validate_coverage_matrix(owner_missing, root=canonical.ROOT)
    assert validated["hardgates"]["COV-HG1-owner"]["status"] == "fail"

    dangling = json.loads(json.dumps(base))
    dangling["cells"][1]["claim_verdict_pointer"] = "reports/canonical/missing.json:$.missing"
    dangling["hardgates"] = discovery_map._coverage_hardgate_rows(dangling["cells"], root=canonical.ROOT)
    dangling["cells"][1]["hardgate_status"] = "fail"
    dangling["cells"][1]["hardgate_reason"] = "claim_verdict_pointer-unresolved"
    dangling["status"] = "fail-closed"
    validated = validate_coverage_matrix(dangling, root=canonical.ROOT)
    assert validated["hardgates"]["COV-HG2-resolves"]["status"] == "fail"

    positive_support = json.loads(json.dumps(base))
    positive = next(cell for cell in positive_support["cells"] if not cell["component_id"].endswith("-DN"))
    positive["mechanism_certificate_pointer"] = None
    positive["debt_pointer"] = None
    positive_support["hardgates"] = discovery_map._coverage_hardgate_rows(positive_support["cells"], root=canonical.ROOT)
    positive["hardgate_status"] = "fail"
    positive["hardgate_reason"] = "COV-HG4-positive-support"
    positive_support["status"] = "fail-closed"
    validated = validate_coverage_matrix(positive_support, root=canonical.ROOT)
    assert validated["hardgates"]["COV-HG4-positive-support"]["status"] == "fail"

    dn_witness = json.loads(json.dumps(base))
    dn = next(cell for cell in dn_witness["cells"] if cell["component_id"].endswith("-DN"))
    dn["negative_witness_pointer"] = None
    dn_witness["hardgates"] = discovery_map._coverage_hardgate_rows(dn_witness["cells"], root=canonical.ROOT)
    dn["hardgate_status"] = "fail"
    dn["hardgate_reason"] = "COV-HG5-dn-witness"
    dn_witness["status"] = "fail-closed"
    validated = validate_coverage_matrix(dn_witness, root=canonical.ROOT)
    assert validated["hardgates"]["COV-HG5-dn-witness"]["status"] == "fail"

    complete_set = json.loads(json.dumps(base))
    complete_set["cells"][0]["component_id"] = "extra-component"
    complete_set["hardgates"] = discovery_map._coverage_hardgate_rows(complete_set["cells"], root=canonical.ROOT)
    complete_set["cells"][0]["hardgate_status"] = "fail"
    complete_set["cells"][0]["hardgate_reason"] = "COV-HG6-complete-set"
    complete_set["status"] = "fail-closed"
    with pytest.raises(ValueError, match="component set mismatch"):
        validate_coverage_matrix(complete_set, root=canonical.ROOT, expected_component_ids=discovery_map.COVERAGE_COMPONENT_IDS)


def test_gap_head_manifest_rows_are_canonical_and_keyed():
    on_h = canonical._specs_by_name()["gap-head-on-h"]
    discovery = canonical._specs_by_name()["gap-head-discovery"]

    assert on_h.command == ("python3", "scripts/run_gap_ledger_head_on_h.py")
    assert on_h.json_artifact == "reports/canonical/gap-head-on-h.json"
    assert on_h.markdown_artifact == "reports/canonical/gap-head-on-h.md"
    assert discovery.command == ("python3", "scripts/run_gap_head_discovery.py")
    assert discovery.json_artifact == "reports/canonical/gap-head-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/gap-head-discovery.md"
    assert {
        "boundary_no_z_audit",
        "forbidden_column_audit",
        "aggregate_metrics",
        "treatment_comparison",
        "control_protocol",
        "$.control_protocol.parameter_match",
        "$.control_protocol.compute_match",
        "$.control_protocol.threshold_match",
        "$.control_protocol.surface_distribution_match",
        "$.control_protocol.metric_helper_match",
        "$.control_protocol.audit_status",
        "$.control_protocol.failure_reasons",
        "$.control_protocol.evidence_pointers",
        "$.records[*].matched_random_control.parameter_match",
        "$.records[*].matched_random_control.compute_match",
        "$.records[*].matched_random_control.threshold_match",
        "$.records[*].matched_random_control.surface_distribution_match",
        "$.records[*].matched_random_control.metric_helper_match",
        "$.records[*].matched_random_control.audit_status",
        "$.records[*].matched_random_control.failure_reasons",
        "$.records[*].matched_random_control.evidence_pointers",
        "control_verdict",
        "main_claim_status",
    }.issubset(set(on_h.required_json_keys))
    assert {
        "boundary_checks",
        "matched_random_control",
        "$.matched_random_control.parameter_match",
        "$.matched_random_control.compute_match",
        "$.matched_random_control.threshold_match",
        "$.matched_random_control.surface_distribution_match",
        "$.matched_random_control.metric_helper_match",
        "$.matched_random_control.audit_status",
        "$.matched_random_control.failure_reasons",
        "$.matched_random_control.evidence_pointers",
        "main_claim_status",
        "final_main_claim_status",
    }.issubset(set(discovery.required_json_keys))
    assert "stronger-matched-random-controls" not in {
        spec.name for spec in canonical.CANONICAL_REPORTS
    }


def test_gap_head_strengthened_control_required_paths_fail_closed(tmp_path):
    spec = canonical._specs_by_name()["gap-head-on-h"]
    payload = _payload_for_spec(spec)
    json_path = tmp_path / "payload.json"
    json_path.write_text(json.dumps(payload), encoding="utf-8")

    valid = canonical._validate_json(json_path, spec.required_json_keys)
    assert valid["status"] == "pass"

    payload["records"][0]["matched_random_control"].pop("surface_distribution_match")
    json_path.write_text(json.dumps(payload), encoding="utf-8")
    invalid = canonical._validate_json(json_path, spec.required_json_keys)

    assert invalid["status"] == "fail"
    assert "$.records[*].matched_random_control.surface_distribution_match" in invalid["missing_keys"]


def test_canonical_reports_manifest_includes_gap_head_ablation():
    spec = canonical._specs_by_name()["gap-head-ablation"]

    assert spec.command == ("python3", "scripts/run_gap_head_ablation.py")
    assert spec.json_artifact == "reports/canonical/gap-head-ablation.json"
    assert spec.markdown_artifact == "reports/canonical/gap-head-ablation.md"
    assert {
        "records",
        "aggregate",
        "factor_attribution",
        "hardgate",
        "positive_discovery_pointer",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.control_protocol"
    assert spec.positive_claim_pointer == "$.factor_attribution.learned_head.auroc_delta"
    assert spec.control_pointer == "$.control_protocol"


def test_canonical_spec_registers_irreducibility_report():
    spec = canonical._specs_by_name()["irreducibility-report"]

    assert spec.command == ("python3", "scripts/run_irreducibility_report.py")
    assert spec.json_artifact == "reports/canonical/irreducibility_report.json"
    assert spec.markdown_artifact == "reports/canonical/order_residual_analysis.md"
    assert {
        "schema_id",
        "artifact_id",
        "source_artifacts",
        "seed_aggregation",
        "hardgate",
        "positive_claim",
        "conditional_information_table",
        "records",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.scope"
    assert spec.cost_pointer == "$.control_protocol"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.control_pointer == "$.control_protocol"
    section = canonical._irreducibility_report_index_section()
    assert section["json_artifact"] == canonical.IRREDUCIBILITY_REPORT_JSON_ARTIFACT
    assert section["markdown_artifact"] == canonical.IRREDUCIBILITY_REPORT_MARKDOWN_ARTIFACT
    assert section["conditional_information_table_json_artifact"] == canonical.IRREDUCIBILITY_CMI_JSON_ARTIFACT


def test_canonical_reports_manifest_includes_gap_head_threshold_frontier():
    spec = canonical._specs_by_name()["gap-head-threshold-frontier"]

    assert spec.command == ("python3", "scripts/run_gap_head_threshold_sweep.py")
    assert spec.json_artifact == "reports/canonical/gap-head-threshold-frontier.json"
    assert spec.markdown_artifact == "reports/canonical/gap-head-threshold-frontier.md"
    assert {
        "threshold_curve",
        "threshold_summary",
        "pareto_axis_spec",
        "pareto_frontier",
        "hardgate",
        "readiness",
        "main_claim_status",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert "threshold_records" not in spec.required_json_keys
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.source_artifacts"
    assert spec.positive_claim_pointer == "$.main_claim_status"
    assert spec.control_pointer == "$.threshold_summary.control_baseline"


def test_canonical_reports_manifest_includes_gap_head_transfer_atlas():
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]

    assert spec.command == ("python3", "scripts/run_gap_head_transfer_atlas.py")
    assert spec.json_artifact == "reports/canonical/gap_head_transfer_atlas.json"
    assert spec.markdown_artifact == "reports/canonical/gap_head_transfer_atlas.md"
    assert {
        "surface_registry",
        "prior_observation_packet",
        "surfaces",
        "boundary_ledger",
        "hardgate_evidence",
        "multi_surface_d5_o",
        "forbidden_claim_term_audit",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.not_claimed"
    assert spec.cost_pointer == "$.source_artifacts.metric_helper"
    assert spec.positive_claim_pointer == "$.multi_surface_d5_o"
    assert spec.control_pointer == "$.config.control_arm"


def test_gap_head_transfer_atlas_generated_payload_exposes_row_classification():
    spec = canonical._specs_by_name()["gap-head-transfer-atlas"]
    payload = _payload_for_spec(spec)

    assert spec.positive_claim_pointer == "$.multi_surface_d5_o"
    for row in payload["surface_registry"] + payload["surfaces"] + payload["boundary_ledger"]:
        assert {
            "variation_axis",
            "evaluation_role",
            "runnable_status",
            "counting_reason",
        } <= set(row)


def test_canonical_reports_manifest_includes_transformer_derivative_atlas():
    spec = canonical._specs_by_name()["transformer-derivative-atlas"]

    assert spec.command == ("python3", "scripts/run_transformer_derivative_atlas.py")
    assert spec.json_artifact == canonical.TRANSFORMER_DERIVATIVE_ATLAS_JSON_ARTIFACT
    assert spec.markdown_artifact == LAYERWISE_JET_MAP_ARTIFACT
    assert canonical.TRANSFORMER_DERIVATIVE_ROUTE_JSON_ARTIFACT == ATTENTION_ROUTE_ARTIFACT
    assert {
        "dgt_declaration",
        "raw_intervention_rows",
        "layerwise_derivative_rows",
        "margin_proxy_controls",
        "attention_routes",
        "hardgate",
        "hardgates",
        "failed_gate",
        "discovery_map_admission",
        "mechanism_claim_allowed",
        "bounded_lab_evidence",
        "forbidden_claim_term_audit",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "auxiliary"
    assert spec.scope_pointer == "$.scope"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.positive_claim_pointer == "$.mechanism_claim_allowed"
    assert spec.control_pointer == "$.margin_proxy_controls"


def test_transformer_derivative_atlas_fixture_is_pointer_derived():
    spec = canonical._specs_by_name()["transformer-derivative-atlas"]
    payload = _payload_for_spec(spec)
    route_report = render_attention_route_report(payload)

    assert payload["dgt_declaration"]["produces_dgt"] is False
    assert payload["dgt_declaration"]["discovery_map_authority"] is False
    assert payload["dgt_declaration"]["claim_graph_authority"] is False
    assert payload["dgt_declaration"]["non_authoritative_admission"] is True
    assert payload["hardgate"]["status"] == payload["hardgates"]["status"]
    assert payload["failed_gate"] is None
    assert payload["discovery_map_admission"]["admitted"] is False
    assert payload["mechanism_claim_allowed"]["allowed"] is False
    assert payload["bounded_lab_evidence"]["raw_row_pointer"] == TRANSFORMER_DERIVATIVE_RAW_ROW_POINTER
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert payload["layerwise_derivative_rows"]["schema"] == "LayerwiseDerivativeRow"
    assert payload["source_artifacts"]["raw_rows"] == TRANSFORMER_DERIVATIVE_RAW_ROW_POINTER
    assert route_report["source_artifacts"]["raw_rows"] == TRANSFORMER_DERIVATIVE_RAW_ROW_POINTER
    assert "dgt_relation" not in json.dumps(payload, sort_keys=True)


def test_transformer_derivative_atlas_stays_out_of_discovery_and_claim_artifacts():
    discovery = json.loads((canonical.ROOT / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    claim_graph = json.loads((canonical.ROOT / "reports/canonical/claim_graph.json").read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()

    assert not any(row.get("report") == "transformer-derivative-atlas" for row in discovery["rows"])
    assert not any("transformer-derivative-atlas" in row.get("claim_id", "") for row in claim_rows)
    assert not any("transformer-derivative-atlas" in node.get("node_id", "") for node in claim_graph["nodes"])


def test_canonical_reports_manifest_includes_gap_head_attribution_capsule():
    spec = canonical._specs_by_name()["gap-head-attribution-capsule"]

    assert spec.command == ("python3", "scripts/run_gap_head_attribution_capsule.py")
    assert spec.json_artifact == "reports/canonical/gap_head_attribution_capsule.json"
    assert spec.markdown_artifact == "reports/canonical/gap_head_attribution_capsule.md"
    assert {
        "schema_id",
        "source_issue",
        "source_issues",
        "artifact_id",
        "run_id",
        "d5_o",
        "d5_m",
        "mechanism_case",
        "mechanism_evidence",
        "not_implemented",
        "ledger_debt",
        "hardgates",
        "residualized_attribution",
        "residualized_attribution_claim",
        "e_hardgates",
        "score_margin_causal_evidence",
        "a4_hardgates",
        "claim_capsule_hardgates",
        "forbidden_column_audit",
        "source_artifacts",
        "aggregate",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.scope.not_claimed"
    assert spec.cost_pointer == "$.cost_protocol_pointer"
    assert spec.control_pointer == "$.control_pointer"
    assert "residualized-attribution" not in {item.name for item in canonical.CANONICAL_REPORTS}


def test_gap_head_attribution_index_exposes_residualized_e_hardgate_pointers(monkeypatch, tmp_path):
    payload = {
        "run_id": "fixture",
        "source_artifacts": {"run_artifacts": {"summary": "reports/runs/a1-canonical/summary.json"}},
        "d5_o": {"status": "ready"},
        "d5_m": {"status": "blocked", "failed_gate": "A4-HG5"},
        "mechanism_evidence": {"candidate_mechanism": "unresolved"},
        "ledger_debt": [{"status": "open"}],
        "residualized_attribution": {"status": "pass"},
        "residualized_attribution_claim": {"non_score_mechanism_claim_allowed": False},
        "e_hardgates": {"status": "fail"},
        "score_margin_causal_evidence": {"status": "pass", "channel_classification": "score_margin_sufficient"},
        "a4_hardgates": {"status": "fail", "gates": {"A4-HG5": {"status": "fail"}}},
    }
    target = tmp_path / canonical.GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT
    target.parent.mkdir(parents=True)
    target.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")

    section = canonical._gap_head_attribution_index_section()

    assert section["residualized_attribution_claim_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution_claim"
    assert section["e_hardgates_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.e_hardgates"
    assert section["e_hardgates_status_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.e_hardgates.status"
    assert section["non_score_mechanism_claim_allowed_pointer"] == (
        "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution_claim.non_score_mechanism_claim_allowed"
    )
    assert section["e_hardgates_status"] == "fail"
    assert section["non_score_mechanism_claim_allowed"] is False


def test_gap_head_attribution_score_margin_shortcut_alias_is_pointer_only(monkeypatch, tmp_path):
    payload = {
        "run_id": "fixture",
        "source_artifacts": {"run_artifacts": {"summary": "reports/runs/a1-canonical/summary.json"}},
        "d5_o": {"status": "ready"},
        "d5_m": {"status": "blocked", "passed": False, "failed_gate": "A4-HG5"},
        "mechanism_evidence": {"candidate_mechanism": "unresolved"},
        "ledger_debt": [{"status": "open"}],
        "residualized_attribution": {"status": "pass"},
        "residualized_attribution_claim": {"non_score_mechanism_claim_allowed": False},
        "e_hardgates": {"status": "fail"},
        "score_margin_causal_evidence": {"status": "pass", "channel_classification": "score_margin_sufficient"},
        "a4_hardgates": {"status": "fail", "gates": {"A4-HG5": {"status": "fail"}}},
    }
    target = tmp_path / canonical.GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT
    target.parent.mkdir(parents=True)
    target.write_text(json.dumps(payload), encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")

    alias = canonical._gap_head_attribution_index_section()["score_margin_shortcut_witness_alias"]

    assert alias == {
        "score_margin_causal_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "score_margin_channel_classification_pointer": (
            "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence.channel_classification"
        ),
        "a4_hg5_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
        "a4_hg5_status_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5.status",
        "d5_m_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_m",
        "d5_m_failed_gate_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_m.failed_gate",
    }
    assert {
        "status",
        "classification",
        "blocked_level",
        "blocked_target",
        "blocked_when",
        "active",
        "metric",
        "metrics",
        "evidence",
        "evidence_body",
        "passed",
        "failed_gate",
        "gate_status",
        "d5_m_status",
        "d5_m_passed",
        "candidate_mechanism",
        "score_margin",
        "score",
        "margin",
    }.isdisjoint(alias)
    assert all(key.endswith("_pointer") for key in alias)

    for pointer in alias.values():
        artifact, json_pointer = split_artifact_pointer(pointer)
        assert artifact == canonical.GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT
        assert pointer_value(payload, json_pointer) is not None


def test_committed_gap_head_attribution_residualized_claim_round_trip_validates():
    capsule = json.loads((canonical.ROOT / "reports/canonical/gap_head_attribution_capsule.json").read_text(encoding="utf-8"))

    assert "residualized-attribution" not in {item.name for item in canonical.CANONICAL_REPORTS}
    assert set(capsule["residualized_attribution_claim"]["slot_order"]) == {
        "full",
        "score_plus_margin",
        "full_residualized",
        "h_only",
        "h_normalized",
        "h_norm_only",
        "full_without_score",
        "margin",
    }
    assert attribution_capsule.validate_residualized_attribution_claim(capsule) == []
    assert capsule["e_hardgates"]["gates"]["E-HG2_pointer_resolution"]["status"] == "pass"
    assert capsule["e_hardgates"]["gates"]["E-HG6_committed_round_trip"]["status"] == "pass"


def test_canonical_reports_manifest_includes_distribution_sweep():
    spec = canonical._specs_by_name()["nongaussian-distribution-sweep"]

    assert spec.command == ("python3", "scripts/run_nongaussian_distribution_sweep.py")
    assert spec.json_artifact == "reports/canonical/nongaussian-distribution-sweep.json"
    assert spec.markdown_artifact == "reports/canonical/nongaussian-distribution-sweep.md"
    assert {
        "records",
        "family_aggregates",
        "coverage_item",
        "claim_gate",
        "main_claim_status",
        "negative_result_ledger",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "auxiliary"


def test_canonical_reports_manifest_includes_causal_patch_suite():
    spec = canonical._specs_by_name()["causal-patch-suite"]

    assert spec.command == ("python3", "scripts/run_causal_patch_suite.py")
    assert spec.json_artifact == "reports/canonical/causal_patch_suite.json"
    assert spec.markdown_artifact == "reports/canonical/patch_effect_summary.md"
    assert {
        "schema_id",
        "artifact_id",
        "producer",
        "source_artifacts",
        "patch_types",
        "patch_records",
        "matched_controls",
        "side_effect_ledger",
        "hardgates",
        "dgt_mechanism_cert",
        "not_claimed",
        "audit",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "auxiliary"
    assert spec.scope_pointer == "$.not_claimed"
    assert spec.cost_pointer == "$.source_artifacts"
    assert spec.positive_claim_pointer == "$.dgt_mechanism_cert"
    assert spec.control_pointer == "$.matched_controls"


def test_causal_patch_suite_fingerprint_sources_cover_runner_and_stats():
    spec = canonical._specs_by_name()["causal-patch-suite"]
    input_record = canonical._input_record(spec)
    source_paths = {row["path"] for row in input_record["producer_sources"]}

    assert "scripts/run_causal_patch_suite.py" in source_paths
    assert "bedc_quality_lab/causal_patch_suite.py" in source_paths


def test_canonical_reports_manifest_includes_mixing_and_anisotropic_sweeps():
    mixing = canonical._specs_by_name()["mixing-family-sweep"]
    anisotropic = canonical._specs_by_name()["anisotropic-ou-sweep"]

    assert mixing.command == ("python3", "scripts/run_mixing_family_sweep.py")
    assert mixing.json_artifact == "reports/canonical/mixing-family-sweep.json"
    assert mixing.markdown_artifact == "reports/canonical/mixing-family-sweep.md"
    assert mixing.bundle_role == "hg_p_core"
    assert {
        "applicability_boundary",
        "family_aggregates",
        "coverage_item",
        "negative_result_summary",
    }.issubset(set(mixing.required_json_keys))
    assert anisotropic.command == ("python3", "scripts/run_anisotropic_ou_sweep.py")
    assert anisotropic.json_artifact == "reports/canonical/anisotropic-ou-sweep.json"
    assert anisotropic.markdown_artifact == "reports/canonical/anisotropic-ou-sweep.md"
    assert anisotropic.bundle_role == "hg_p_core"
    assert {
        "applicability_boundary",
        "aggregates",
        "transition_debt_by_grid",
        "negative_result_summary",
    }.issubset(set(anisotropic.required_json_keys))


def test_canonical_reports_manifest_includes_certificate_guided_projection():
    training = canonical._specs_by_name()["certificate-guided-training"]
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]
    training_discipline = canonical._discipline(training)

    assert training.command == ("python3", "scripts/run_certificate_guided_constraint_training.py")
    assert training.json_artifact == "reports/canonical/certificate-guided-training.json"
    assert training.markdown_artifact == "reports/canonical/certificate-guided-training.md"
    assert discovery.command == ("python3", "scripts/run_certificate_guided_discovery.py")
    assert discovery.json_artifact == "reports/canonical/certificate-guided-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/certificate-guided-discovery.md"
    assert {
        "paired_seed_protocol",
        "paired_delta_ci",
        "arm_protocol",
        "arm_summaries",
        "grid_summary",
        "grid_metrics_artifact",
        "grid_summary_artifact",
        "raw_metrics_artifact",
        "metrics",
        "claim_gate",
        "hardgate",
        "failed_gate",
        "verdict",
        "discovery_level",
        "not_claimed",
        "claim_capsule",
    }.issubset(set(training.required_json_keys))
    assert training.bundle_role == "hg_p_core"
    assert training_discipline["evidence_pointer"] == "$.arm_protocol.compat_roles.after"
    assert training_discipline["evidence_label"] == "constraint_lagrangian"
    assert {
        "positive_discovery",
        "net_information",
        "matched_random_baseline",
        "claim_gate",
        "hardgate",
        "failed_gate",
        "verdict",
        "discovery_level",
        "revocation_decision",
        "revocation_ledger",
        "not_claimed",
        "main_claim_status",
    }.issubset(set(discovery.required_json_keys))
    assert discovery.bundle_role == "hg_p_core"


def test_canonical_msn_payload_exposes_module_evidence_without_terminal_verdict():
    spec = canonical._specs_by_name()["mechanism-seeking-network"]
    payload = json.loads((canonical.ROOT / spec.json_artifact).read_text(encoding="utf-8"))

    assert {"distinction_module_evidence", "d5_m_readiness"}.issubset(set(spec.required_json_keys))
    assert payload["distinction_module_evidence"]["owner_pointer"] == "$.distinction_module_evidence"
    assert payload["d5_m_readiness"]["distinction_module_evidence_ref"] == "$.distinction_module_evidence"
    assert "terminal_verdict" not in set(_walk_keys(payload))


def test_mechanism_dna_is_registered_without_terminal_verdict_surface():
    spec = canonical._specs_by_name()["mechanism-dna"]

    assert spec.json_artifact == "reports/canonical/mechanism_dna.json"
    assert "terminal_verdict" not in spec.required_json_keys
    assert "final_verdict" not in spec.required_json_keys
    assert set(
        (
            "schema_id",
            "artifact_id",
            "generated_at",
            "deterministic_seed",
            "source_artifacts",
            "rows",
            "hardgate",
            "not_claimed",
            "forbidden_alias_audit",
        )
    ) == set(spec.required_json_keys)


def test_mechanism_dna_index_section_is_pointer_only():
    payload = canonical._index([], generated_at="2030-01-01T00:00:00+00:00")
    section = payload["mechanism_dna"]
    serialized = json.dumps(section, sort_keys=True)

    assert section["status"] == "pointer-only"
    assert section["artifact_id"] == "bedc-quality-lab:mechanism-dna"
    assert section["rows_pointer"] == "reports/canonical/mechanism_dna.json:$.rows"
    assert "terminal_verdict" not in serialized
    assert ".refactor-loop/host.env" not in serialized


def test_canonical_reports_manifest_includes_sigreg_training_proxy():
    spec = canonical._specs_by_name()["sigreg-training-proxy"]

    assert spec.command == ("python3", "scripts/run_sigreg_training_proxy.py")
    assert spec.json_artifact == "reports/canonical/sigreg-training-proxy.json"
    assert spec.markdown_artifact == "reports/canonical/sigreg-training-proxy.md"
    assert {
        "run_artifacts",
        "objective",
        "arm_protocol",
        "d1_evidence",
        "positive_claim",
        "claim_capsule_ref",
        "result_snapshot_ref",
        "full_lejepa_boundary",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.arm_protocol"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.control_pointer is None
    assert spec.no_control_rationale_pointer == "$.full_lejepa_boundary"


def test_certificate_guided_discovery_required_keys_do_not_require_audit_fields():
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]

    assert "audit_decision" not in discovery.required_json_keys
    assert "audit_ledger" not in discovery.required_json_keys


def test_manifest_required_keys_cover_linked_control_evidence():
    for spec in canonical.CANONICAL_REPORTS:
        keys = set(spec.required_json_keys)
        if spec.name == "dgt-component-redundancy-audit":
            assert keys == {"component_redundancy_audit"}
            continue
        if spec.name == "dgt-base-undertraining-audit":
            assert keys == {"base_undertraining_audit"}
            continue
        if spec.name == "input-accessibility":
            assert {"source_registry", "consumer_pointers", "access_hardgates"}.issubset(keys)
            continue
        if spec.name == "dgt-model-card":
            assert {"card_id", "source_artifacts", "card_hardgates", "not_claimed"}.issubset(keys)
            continue
        assert "generated_at" in keys
        if spec.name == "model-comparison":
            assert {"models", "hardgates", "not_claimed", "source_reports"}.issubset(keys)
            continue
        if spec.name == "dgt-ablation-null-decomposition":
            assert "source_artifact" in keys
            continue
        if spec.name == "dgt-component-redundancy-audit":
            assert "component_redundancy_audit" in keys
            continue
        if spec.name == "input-accessibility":
            assert "source_registry" in keys
            continue
        assert "source_artifacts" in keys
    assert {"control_protocol", "control_verdict"}.issubset(
        set(canonical._specs_by_name()["gap-head-on-h"].required_json_keys)
    )
    assert {"matched_random_control", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["gap-head-discovery"].required_json_keys)
    )
    assert {"control_protocol", "hardgate", "factor_attribution"}.issubset(
        set(canonical._specs_by_name()["gap-head-ablation"].required_json_keys)
    )
    assert {"claim_gate", "negative_result_ledger", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["nongaussian-distribution-sweep"].required_json_keys)
    )
    assert {"positive_discovery", "net_information", "matched_random_baseline", "claim_gate", "hardgate", "failed_gate", "verdict", "discovery_level", "revocation_decision", "revocation_ledger", "not_claimed", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["certificate-guided-discovery"].required_json_keys)
    )


def test_hg_p_core_rows_are_exact_and_auxiliary_rows_cannot_substitute():
    core = {
        spec.name
        for spec in canonical.CANONICAL_REPORTS
        if spec.bundle_role == "hg_p_core"
    }
    auxiliary = {
        spec.name
        for spec in canonical.CANONICAL_REPORTS
        if spec.bundle_role == "auxiliary"
    }

    assert core == HG_P_CORE
    assert "nongaussian-distribution-sweep" in auxiliary
    assert "lejepa-theorem-ledger" in auxiliary
    assert "spectral-ablation-hinge" in auxiliary
    assert not HG_P_CORE.intersection(auxiliary)


def test_every_core_row_has_scope_cost_not_claimed_and_claim_discipline_pointers(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    for spec in canonical.CANONICAL_REPORTS:
        json_path = canonical._artifact_path(spec.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")

    for spec in canonical.CANONICAL_REPORTS:
        discipline = canonical._discipline(spec)
        if spec.bundle_role != "hg_p_core":
            continue
        assert discipline["scope_status"] == "present"
        assert discipline["cost_status"] == "present"
        assert discipline["not_claimed_status"] == "present"
        assert discipline["positive_claim_status"] == "present"


def test_positive_claims_have_control_or_no_control_rationale():
    for spec in canonical.CANONICAL_REPORTS:
        has_control = spec.control_pointer is not None
        has_rationale = spec.no_control_rationale_pointer is not None
        assert has_control or has_rationale


def test_generated_index_contains_outline_claims_nonclaims_and_honest_boundary_sections(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_dimension_mismatch_gap_witness_fixture(tmp_path)
    for spec in canonical.CANONICAL_REPORTS:
        json_path = canonical._artifact_path(spec.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    _write_observed_debt_projection_fixtures(tmp_path)
    transfer_path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
    transfer_path.parent.mkdir(parents=True, exist_ok=True)
    transfer_path.write_text(
        json.dumps(
            {
                "dimension_mismatch_debt_transfer": {
                    "status": "pass",
                    "base_level": "D4",
                    "anti_triviality_status": "scale_leakage_detected",
                    "effective_level": "DN",
                    "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
                    "terminal_verdict": "negative_discovery",
                    "hypothesis": "fixture hypothesis",
                    "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
                    "what_was_learned": "fixture learned",
                    "discovery_level": "DN",
                    "scope": "fixture scope",
                }
            }
        )
        + "\n",
        encoding="utf-8",
    )
    robustness_path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT
    robustness_path.write_text(json.dumps({"audit_status": "pass"}) + "\n", encoding="utf-8")
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 4, "required": 4, "gap_count": 0},
    )
    reports = [_index_row_for_spec(spec) for spec in canonical.CANONICAL_REPORTS]
    payload = canonical._index(reports)
    markdown = canonical._render_index_markdown(payload)

    assert {
        "paper_outline",
        "claims_nonclaims",
        "honest_boundary",
        "literature_ledger",
        "quality_scorecard",
        "observed_debt_axis_projection",
        "negative_witnesses",
        "claim_verdicts",
        "claim_capsule",
        "formal_hardening",
    }.issubset(payload)
    assert set(payload["paper_outline"]["core_reports"]) == HG_P_CORE
    assert payload["negative_witnesses"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:discovery-negative-witnesses",
        "json_artifact": "reports/canonical/discovery_negative_witnesses.json",
        "expected_kind_count": 9,
        "schema_role": "bedc-gap-witness-ledger",
        "witness_rows_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses",
    }
    assert not hasattr(canonical, "NEGATIVE_WITNESSES_REQUIRED_FIELDS")
    assert payload["claim_verdicts"]["status"] == "pointer-only"
    assert payload["claim_verdicts"]["artifact_id"] == "bedc-quality-lab:claim-verdicts"
    assert payload["claim_verdicts"]["jsonl_artifact"] == "reports/canonical/claim_verdicts.jsonl"
    assert isinstance(payload["claim_verdicts"]["row_count"], int)
    assert payload["claim_capsule"]["status"] == "pointer-only"
    assert payload["claim_capsule"]["artifact_id"] == "bedc-quality-lab:claim-capsule"
    assert payload["claim_capsule"]["schema_id"] == "bedc.quality.claim_capsule"
    assert payload["claim_capsule"]["json_artifact"] == "reports/canonical/claim_capsule.json"
    assert payload["claim_capsule"]["effective_level"] == "DN"
    assert payload["claim_capsule"]["terminal_verdict"] == "negative_discovery"
    assert payload["formal_hardening"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:formal-hardening",
        "json_artifact": "reports/canonical/formal_hardening.json",
        "markdown_artifact": "reports/canonical/formal_hardening.md",
        "ready": True,
        "recorded": 4,
        "required": 4,
        "gap_count": 0,
    }
    assert "HG-P core reports" in markdown
    assert "Auxiliary reports" in markdown
    assert "Quality scorecard" in markdown
    assert "Quality baseline pointers" in markdown
    assert "reports/canonical/discovery_map.json:$.rows[*].discovery_level" in markdown
    assert "Observed debt axis projection" in markdown
    assert "Negative witnesses" in markdown
    assert "Claim verdicts" in markdown
    assert "Claim capsule" in markdown
    assert "Formal hardening" in markdown
    assert "Paper outline" in markdown
    assert "Claims and non-claims" in markdown
    assert "Literature ledger pointer" in markdown
    assert "Honest boundary" in markdown


def test_canonical_index_observed_debt_axis_projection_is_pointer_only(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    _write_observed_debt_projection_fixtures(tmp_path)

    payload = canonical._index([_index_row_for_spec(spec) for spec in canonical.CANONICAL_REPORTS])
    section = payload["observed_debt_axis_projection"]
    rows = section["rows"]

    assert section["status"] == "pointer-only"
    assert [row["axis_id"] for row in rows] == list(canonical.OBSERVED_DEBT_AXIS_IDS)
    assert {row["axis_id"] for row in rows} == {
        "latent_distribution",
        "anisotropy",
        "dimension_mismatch",
        "sample_count",
        "optimizer",
        "mixing",
        "compute",
        "capacity",
    }
    assert section["classification_enum"] == ["observed-debt", "ledger-risk-only"]
    assert {row["classification"] for row in rows} <= {"observed-debt", "ledger-risk-only"}
    assert {row["axis_id"]: row["classification"] for row in rows} == {
        "latent_distribution": "ledger-risk-only",
        "anisotropy": "ledger-risk-only",
        "dimension_mismatch": "observed-debt",
        "sample_count": "observed-debt",
        "optimizer": "ledger-risk-only",
        "mixing": "ledger-risk-only",
        "compute": "ledger-risk-only",
        "capacity": "ledger-risk-only",
    }
    for row in rows:
        assert resolve_artifact_pointer(tmp_path, f"{row['source_artifact']}:{row['evidence_pointer']}") is not None
    assert ".refactor-loop/host.env" not in json.dumps(section)
    assert "observed-debt-atlas" not in {spec.name for spec in canonical.CANONICAL_REPORTS}
    assert not (tmp_path / "reports/canonical/observed-debt-atlas.json").exists()
    assert not (tmp_path / "reports/canonical/observed-debt-atlas.md").exists()


def test_observed_debt_axis_projection_fails_closed_for_missing_pointer(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    _write_observed_debt_projection_fixtures(tmp_path)
    sample_path = tmp_path / "reports/canonical/gap-head-observed-debt-transfer.json"
    sample_payload = json.loads(sample_path.read_text(encoding="utf-8"))
    sample_payload["gap_head_on_h_observed_debt_transfer"].pop("status")
    sample_path.write_text(json.dumps(sample_payload, sort_keys=True) + "\n", encoding="utf-8")

    section = canonical._observed_debt_axis_projection_section()
    rows = {row["axis_id"]: row for row in section["rows"]}

    assert rows["sample_count"]["classification"] == "ledger-risk-only"
    assert rows["sample_count"]["source_status"] is None


def test_observed_debt_axis_projection_fails_closed_for_non_pass_hardgate(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    _write_observed_debt_projection_fixtures(tmp_path)
    sample_path = tmp_path / "reports/canonical/gap-head-observed-debt-transfer.json"
    sample_payload = json.loads(sample_path.read_text(encoding="utf-8"))
    sample_payload["hardgate_evidence"]["HG-A1"]["status"] = "fail"
    sample_path.write_text(json.dumps(sample_payload, sort_keys=True) + "\n", encoding="utf-8")

    section = canonical._observed_debt_axis_projection_section()
    rows = {row["axis_id"]: row for row in section["rows"]}

    assert rows["sample_count"]["classification"] == "ledger-risk-only"
    assert rows["sample_count"]["source_status"] == "pass"


def test_observed_debt_axis_projection_fails_closed_for_global_claim_flag(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    _write_observed_debt_projection_fixtures(tmp_path)
    sample_path = tmp_path / "reports/canonical/gap-head-observed-debt-transfer.json"
    sample_payload = json.loads(sample_path.read_text(encoding="utf-8"))
    sample_payload["global_claim_flag"] = True
    sample_path.write_text(json.dumps(sample_payload, sort_keys=True) + "\n", encoding="utf-8")

    section = canonical._observed_debt_axis_projection_section()
    rows = {row["axis_id"]: row for row in section["rows"]}

    assert rows["sample_count"]["classification"] == "ledger-risk-only"
    assert rows["sample_count"]["source_status"] == "pass"


def test_new_model_hardgates_sidecar_written_and_indexed(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    _drop_dgt_l0_from_manifest(monkeypatch)
    real_index = canonical._index
    real_render_index_markdown = canonical._render_index_markdown
    _patch_lightweight_run_reports(monkeypatch)
    monkeypatch.setattr(canonical, "_index", real_index)
    monkeypatch.setattr(canonical, "_render_index_markdown", real_render_index_markdown)
    monkeypatch.setattr(
        canonical,
        "_build_claim_capsule",
        lambda generated_at: {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "DN",
            "terminal_verdict": "negative_discovery",
        },
    )
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)
    _patch_scaling_ladder_pass_run_spec(monkeypatch)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    sidecar = json.loads((tmp_path / canonical.NEW_MODEL_HARDGATES_JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / canonical.NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    section = payload["new_model_hardgates"]

    assert "new_model_hardgates" not in {spec.name for spec in canonical.CANONICAL_REPORTS}
    assert sidecar["schema_id"] == canonical.NEW_MODEL_HARDGATES_SCHEMA_ID
    assert sidecar["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert sidecar["gate_ids"] == [f"NEW-MODEL-HG{index}" for index in range(1, 21)]
    assert section == {
        "status": "pointer-only",
        "artifact_id": canonical.NEW_MODEL_HARDGATES_ARTIFACT_ID,
        "json_artifact": canonical.NEW_MODEL_HARDGATES_JSON_ARTIFACT,
        "markdown_artifact": canonical.NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT,
        "schema_id": canonical.NEW_MODEL_HARDGATES_SCHEMA_ID,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "gate_count": 20,
        "gate_ids_pointer": "reports/canonical/new_model_hardgates.json:$.gate_ids",
        "gates_pointer": "reports/canonical/new_model_hardgates.json:$.gates",
    }
    assert "candidate metrics" not in markdown.lower()
    assert "terminal_verdict" not in markdown
    assert "NEW-MODEL-HG20" not in json.dumps(section)
    assert "requirement" not in section
    from bedc_quality_lab.backends.current_lab import projection

    assert (
        canonical.NEW_MODEL_HARDGATES_JSON_ARTIFACT
        not in projection._manifest_audit(root=tmp_path, canonical_reports=canonical.CANONICAL_REPORTS)[
            "unregistered_json_artifacts"
        ]
    )


def test_new_model_hardgates_exact_gate_contract():
    payload = canonical._build_new_model_hardgates_payload(generated_at="2030-01-01T00:00:00+00:00")
    gates = payload["gates"]
    required_fields = {
        "requirement",
        "required_candidate_pointer",
        "required_evidence_pointer",
        "not_claimed_pointer",
    }

    assert payload["gate_ids"] == [f"NEW-MODEL-HG{index}" for index in range(1, 21)]
    assert list(gates) == payload["gate_ids"]
    for gate_id, row in gates.items():
        assert set(row) == required_fields
        assert row["required_candidate_pointer"] == f"$.hardgate_instances.{gate_id}"
        assert row["required_evidence_pointer"] == f"$.hardgate_instances.{gate_id}.evidence_pointer"
        assert row["not_claimed_pointer"] == f"$.hardgate_instances.{gate_id}.not_claimed_pointer"
    hg20_text = gates["NEW-MODEL-HG20"]["requirement"].lower()
    for phrase in ("universal architecture", "production", "full closure"):
        assert phrase in hg20_text


def test_new_model_hardgates_pointer_only_forbidden_body_fields():
    payload = canonical._build_new_model_hardgates_payload(generated_at="2030-01-01T00:00:00+00:00")
    section = canonical._new_model_hardgates_index_section(generated_at="2030-01-01T00:00:00+00:00")

    for mutate in (
        lambda item: item.update({"terminal_verdict": "pass"}),
        lambda item: item["gates"]["NEW-MODEL-HG11"].update({"candidate_evidence_body": {"rows": []}}),
        lambda item: item["gates"]["NEW-MODEL-HG7"].update({"measured_baseline": {"loss": 0.2}}),
        lambda item: item.__setitem__("leak", ".refactor-loop/host.env"),
    ):
        mutated = json.loads(json.dumps(payload))
        mutate(mutated)
        with pytest.raises(ValueError):
            canonical._validate_new_model_hardgates_payload(mutated)
    lowered_index = json.dumps(section).lower()
    for forbidden in ("terminal_verdict", "raw_metrics", "candidate_evidence_body", ".refactor-loop"):
        assert forbidden not in lowered_index


def test_discovery_gated_transformer_owner_schema_and_model_id():
    payload = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )

    assert set(payload) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "projector",
        "model_id",
        "source_artifacts",
        "component_refs",
        "architecture_spec",
        "hardgate",
        "hardgate_ref",
        "tool_route_evidence",
        "family_definition",
        "component_ablation",
        "neural_ablation_ref",
        "operational_robustness",
        "discovery_map_signal",
        "discovery_map_signal_ref",
        "d4_projection_ref",
        "d4_projection",
        "d5_o_projection",
        "d5_m_projection",
        "scaling_ladder",
        "claim_capsule_ref",
        "evidence_envelope_ref",
        "mechanism_namecert_ref",
        "jet_certificate_ref",
        "forbidden_claim_term_audit",
        "revocation_rows",
        "not_claimed",
    }
    assert payload["schema_id"] == canonical.DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID
    assert payload["artifact_id"] == canonical.DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID
    assert payload["producer"] == "scripts/run_discovery_gated_transformer.py"
    assert payload["model_id"] == "discovery-gated-transformer"
    assert payload["source_artifacts"]["construct_suspension_ref"] == {
        "artifact": canonical.DGT_L0_CONTROLS_JSON_ARTIFACT,
        "pointer": "$.construct_suspension",
    }
    assert payload["source_artifacts"]["interpretation_boundary_ref"] == {
        "artifact": canonical.DGT_L1_CONTROLS_JSON_ARTIFACT,
        "pointer": "$.l1_tiny_sequence_projection",
    }
    assert payload["source_artifacts"]["negative_witness_sweep_ref"] == {
        "artifact": canonical.DGT_L1_CONTROLS_JSON_ARTIFACT,
        "pointer": "$.negative_witness_sweep",
    }
    assert payload["architecture_spec"]["architecture_id"] == "discovery-gated-transformer"
    assert payload["tool_route_evidence"]["schema_id"] == "bedc-quality-lab:discovery-gated-transformer.tool-route-evidence"
    assert payload["tool_route_evidence"]["hardgate"]["status"] == "pass"
    assert payload["family_definition"]["schema_id"] == "bedc-quality-lab:discovery-gated-transformer.family-definition"
    assert payload["family_definition"]["owner_ref"] == (
        "reports/canonical/discovery-gated-transformer.json:$"
    )
    assert set(payload["family_definition"]["invariant_groups"]) == {"architecture", "objective", "certificate"}
    assert payload["family_definition"]["hardgate"]["status"] == "pass"
    assert payload["family_definition"]["model_family_claim_status"]["claim_allowed"] is False
    assert payload["component_ablation"]["owner_ref"] == (
        "reports/canonical/discovery-gated-transformer.json:$.component_ablation"
    )
    assert payload["component_ablation"]["arm_count"] == 11
    assert payload["component_ablation"]["hardgate"]["status"] == "pass"
    assert payload["neural_ablation_ref"] == {
        "artifact": canonical.DGT_NEURAL_ABLATION_JSON_ARTIFACT,
        "pointer": "$.nabl_hardgates.status",
    }
    assert payload["d5_m_projection"]["component_ablation_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.neural_ablation_ref"
    )
    assert payload["d5_m_projection"]["neural_ablation_pointer"] == (
        "reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status"
    )
    assert all(
        row["causal_claim_allowed"] is False
        for row in payload["component_ablation"]["arms"]
        if row["effect_status"] == "zero-effect-fail-closed"
    )
    assert payload["d4_projection"]["discovery_level"] == "D4"
    assert payload["d4_projection"]["readiness"] == "ready"
    assert set(payload["d4_projection"]["gates"]) == {f"PROJ-HG{index}" for index in range(1, 11)}
    assert set(payload["d5_o_projection"]["gates"]) == {f"D5O-HG{index}" for index in range(1, 9)}
    assert payload["d5_o_projection"]["discovery_level"] in {"D4", "D5-O"}
    assert [row["level_id"] for row in payload["scaling_ladder"]["levels"]] == [
        "L0_toy",
        "L1_tiny_sequence",
        "L2_char_lm",
        "L3_byte_lm",
        "L4_tool_use_toy",
        "L5_small_world_model",
    ]
    assert set(payload["scaling_ladder"]["hardgate"]["gates"]) == {f"SCALE-HG{index}" for index in range(1, 7)}
    assert payload["scaling_ladder"]["evidence_scope"] == "bounded-model-prototype-scaling"
    for pointer in (
        payload["scaling_ladder"]["source_projection"]["status_pointer"],
        payload["scaling_ladder"]["source_projection"]["discovery_level_pointer"],
        payload["scaling_ladder"]["source_projection"]["mechanism_closure_pointer"],
    ):
        artifact, local_pointer = pointer.split(":", 1)
        assert artifact == canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT
        assert pointer_value(payload, local_pointer) is not None
    assert set(payload["component_refs"]) == {
        "hardgate_contract",
        "mechanism_dna",
        "mechanism_namecert",
        "discovery_map",
        "training_replay",
    }
    assert payload["claim_capsule_ref"]["artifact"] == "reports/runs/discovery-gated-transformer/claim_capsule.json"
    assert payload["evidence_envelope_ref"]["artifact"] == "reports/runs/discovery-gated-transformer/evidence_envelope.json"
    assert payload["mechanism_namecert_ref"]["artifact"] == "reports/runs/discovery-gated-transformer/mechanism_namecert.json"
    assert payload["jet_certificate_ref"]["artifact"] == "reports/runs/discovery-gated-transformer/jet_certificate.json"


def test_discovery_map_rejects_dgt_scaling_ladder_without_open_l0_owner_consumption():
    from bedc_quality_lab.backends.current_lab import projection

    payload = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    mutated = json.loads(json.dumps(payload))
    ladder = mutated["scaling_ladder"]
    ladder["status"] = "ready"
    ladder["hardgate"]["status"] = "pass"
    for gate in ladder["hardgate"]["gates"].values():
        gate["status"] = "pass"
    ladder["levels"][0]["claim_capsule"]["ladder_consumption_status"] = "scoped-boundary"

    ready, reason, pointer = projection._dgt_scaling_ladder_projection_status(mutated)

    assert ready is False
    assert reason == "dgt_scaling_ladder_owner-l0-ladder-consumption-not-open"
    assert pointer == "$.scaling_ladder.levels[0].claim_capsule.ladder_consumption_status"


def test_dgt_neural_ablation_canonical_spec_is_single_auxiliary_owner():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "dgt-neural-ablation"]

    assert len(specs) == 1
    spec = specs[0]
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_neural_ablation.py")
    assert spec.json_artifact == canonical.DGT_NEURAL_ABLATION_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.DGT_NEURAL_ABLATION_MARKDOWN_ARTIFACT
    assert spec.required_json_keys == (
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "run_artifacts",
        "module_registry",
        "run_spec",
        "training_protocol",
        "metric_protocol",
        "scope_pressure_protocol",
        "scope_seal_mechanism",
        "records",
        "arm_summaries",
        "metric_delta_matrix",
        "paired_delta_matrix",
        "robustness_by_steps",
        "stable_causal_attribution",
        "stable_component_causal_claims",
        "stable_boundary_ledger",
        "compute_ledger",
        "pure_hardgates",
        "nabl_hardgates",
        "nabl2_hardgates",
        "component_causal_claims",
        "boundary_ledger",
        "evidence_scope",
        "claim_capsule_ref",
        "not_claimed",
        "forbidden_claim_term_audit",
        "negative_witness_sweep",
        "reproducibility_contract",
    )
    assert spec.positive_claim_pointer == "$.component_causal_claims"
    assert spec.claim_capsule_pointer == "$.claim_capsule_ref"


def test_dgt_ablation_null_decomposition_canonical_spec_is_read_only_auxiliary_owner():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "dgt-ablation-null-decomposition"]

    assert len(specs) == 1
    spec = specs[0]
    neural_index = [item.name for item in canonical.CANONICAL_REPORTS].index("dgt-neural-ablation")
    null_index = [item.name for item in canonical.CANONICAL_REPORTS].index("dgt-ablation-null-decomposition")
    assert neural_index < null_index
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_ablation_null_decomposition.py")
    assert spec.json_artifact == canonical.DGT_ABLATION_NULL_DECOMPOSITION_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.DGT_ABLATION_NULL_DECOMPOSITION_MARKDOWN_ARTIFACT
    assert spec.required_json_keys == (
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifact",
        "threshold_schema",
        "decision_table",
        "null_decomposition",
        "hardgates",
        "not_claimed",
    )
    assert spec.cost_pointer == "$.source_artifact"
    assert spec.control_pointer == "$.source_artifact"
    assert spec.positive_claim_pointer == "$.null_decomposition.verdict"


def test_dgt_component_redundancy_audit_canonical_spec_follows_null_decomposition():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "dgt-component-redundancy-audit"]

    assert len(specs) == 1
    spec = specs[0]
    names = [item.name for item in canonical.CANONICAL_REPORTS]
    assert names.index("dgt-ablation-null-decomposition") < names.index("dgt-component-redundancy-audit")
    assert names.index("dgt-component-redundancy-audit") < names.index("order-k-benchmark")
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_component_redundancy_audit.py")
    assert spec.json_artifact == canonical.DGT_COMPONENT_REDUNDANCY_AUDIT_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.DGT_COMPONENT_REDUNDANCY_AUDIT_MARKDOWN_ARTIFACT
    assert spec.required_json_keys == ("component_redundancy_audit",)
    assert spec.scope_pointer == "$.component_redundancy_audit.scope"
    assert spec.cost_pointer == "$.component_redundancy_audit.source_artifacts"
    assert spec.not_claimed_pointer == "$.component_redundancy_audit.not_claimed"
    assert spec.positive_claim_pointer == "$.component_redundancy_audit.global_recommendation"


def test_dgt_base_undertraining_audit_canonical_spec_follows_l1_controls():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "dgt-base-undertraining-audit"]

    assert len(specs) == 1
    spec = specs[0]
    names = [item.name for item in canonical.CANONICAL_REPORTS]
    assert names.index("dgt-l1-controls") < names.index("dgt-base-undertraining-audit")
    assert names.index("dgt-base-undertraining-audit") < names.index("discovery-gated-transformer")
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_dgt_base_undertraining_audit.py")
    assert spec.json_artifact == canonical.DGT_BASE_UNDERTRAINING_AUDIT_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.DGT_BASE_UNDERTRAINING_AUDIT_MARKDOWN_ARTIFACT
    assert spec.required_json_keys == ("base_undertraining_audit",)
    assert spec.scope_pointer == "$.base_undertraining_audit.not_claimed"
    assert spec.cost_pointer == "$.base_undertraining_audit.source_contract"
    assert spec.not_claimed_pointer == "$.base_undertraining_audit.not_claimed"
    assert spec.positive_claim_pointer == "$.base_undertraining_audit.verdict"
    assert spec.discovery_level_pointer == (
        "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.verdict"
    )


def test_fair_l1_decision_canonical_spec_projects_ladder_state():
    spec = canonical._specs_by_name()["fair-l1-decision"]
    names = [item.name for item in canonical.CANONICAL_REPORTS]
    payload = _payload_for_spec(spec)

    assert names.index("dgt-l1-controls") < names.index("fair-l1-decision")
    assert names.index("dgt-base-undertraining-audit") < names.index("fair-l1-decision")
    assert names.index("input-accessibility") < names.index("fair-l1-decision")
    assert names.index("fair-l1-decision") < names.index("discovery-gated-transformer")
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_fair_l1_decision.py")
    assert spec.json_artifact == canonical.FAIR_L1_DECISION_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.FAIR_L1_DECISION_MARKDOWN_ARTIFACT
    assert spec.positive_claim_pointer == "$.decision.status"
    assert spec.claim_capsule_pointer == "$.decision.claim_capsule"
    assert spec.construct_validity_pointer == (
        "reports/canonical/fair-l1-decision.json:$.construct_validity_projection"
    )
    assert payload["decision"]["status"] in {"blocked", "bounded-negative", "scaling-evidence-eligible"}
    assert payload["ladder_state_projection"]["state"] in {
        "l1-scaling-blocked",
        "l1-bounded-negative",
        "l1-scaling-evidence-eligible",
    }


def test_fair_l1_changed_run_allows_nonpass_when_committed_status_is_bounded_negative(monkeypatch):
    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", lambda _root, _pointer: "bounded-negative")

    assert canonical._result_blocks_changed_run({"name": "fair-l1-decision", "status": "fail"}) is False


def test_fair_l1_changed_run_blocks_nonpass_when_committed_status_is_not_bounded_negative(monkeypatch):
    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", lambda _root, _pointer: "blocked")

    assert canonical._result_blocks_changed_run({"name": "fair-l1-decision", "status": "fail"}) is True


def test_changed_run_blocks_non_fair_nonpass_without_committed_decision_lookup(monkeypatch):
    def unexpected_lookup(_root, _pointer):
        raise AssertionError("non-fair changed result must not read the fair L1 decision")

    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", unexpected_lookup)

    assert canonical._result_blocks_changed_run({"name": "dgt-l1-controls", "status": "fail"}) is True


def test_changed_run_allows_dgt_l0_cv_hg4_boundary_without_committed_lookup(monkeypatch):
    def unexpected_lookup(_root, _pointer):
        raise AssertionError("DGT L0 boundary result must not read the fair L1 decision")

    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", unexpected_lookup)

    assert (
        canonical._result_blocks_changed_run(
            {
                "name": "dgt-l0-controls",
                "status": "fail",
                "construct_validity": {"status": "fail", "failed_gates": ["CV-HG4"]},
            }
        )
        is False
    )


def test_changed_run_blocks_dgt_l0_construct_validity_failure_drift(monkeypatch):
    def unexpected_lookup(_root, _pointer):
        raise AssertionError("DGT L0 boundary result must not read the fair L1 decision")

    monkeypatch.setattr(canonical, "_resolve_committed_artifact_pointer", unexpected_lookup)

    assert (
        canonical._result_blocks_changed_run(
            {
                "name": "dgt-l0-controls",
                "status": "fail",
                "construct_validity": {"status": "fail", "failed_gates": ["CV-HG3"]},
            }
        )
        is True
    )


def test_dgt_base_undertraining_changed_mode_reruns_when_input_accessibility_changes(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["dgt-base-undertraining-audit"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    input_accessibility = tmp_path / canonical.INPUT_ACCESSIBILITY_JSON_ARTIFACT
    input_accessibility.write_text('{"rows":[{"missing_variables":["changed"]}]}\n', encoding="utf-8")
    calls = []

    def fake_run_producer(called):
        calls.append(called.name)
        _write_fingerprint_fixture(canonical, tmp_path, called)

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    result = canonical._run_spec(spec, mode="changed", generated_at="fixture")

    assert calls == ["dgt-base-undertraining-audit"]
    assert result["producer_status"] == "completed"
    assert result["fingerprint_status"] == "written"
    assert result["fingerprint_reason"] == "input-fingerprint"


def test_discovery_gated_transformer_hardgate_instances_are_candidate_local():
    payload = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    hardgates = payload["hardgate"]["gates"]

    assert list(hardgates) == [f"DGT-HG{index}" for index in range(1, 21)]
    assert payload["hardgate"]["status"] == "pass"
    for gate_id, row in hardgates.items():
        assert set(row) == {"status", "evidence", "not_claimed"}
        assert row["status"] == "pass"
        assert set(row["evidence"]) == {"artifact", "pointer"}
        assert set(row["not_claimed"]) == {"artifact", "pointer"}
        assert row["not_claimed"] == {
            "artifact": canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
            "pointer": "$.not_claimed",
        }


def test_discovery_gated_transformer_index_is_pointer_only():
    owner = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    section = canonical._discovery_gated_transformer_index_section(owner)

    assert set(section) == {
        "status",
        "artifact_id",
        "schema_id",
        "json_artifact",
        "markdown_artifact",
        "fingerprint_artifact",
        "model_id_pointer",
        "architecture_spec_pointer",
        "component_refs_pointer",
        "hardgate_pointer",
        "hardgate_ref_pointer",
        "tool_route_evidence_pointer",
        "tool_route_hardgate_pointer",
        "family_definition_pointer",
        "family_definition_hardgate_pointer",
        "model_family_claim_status_pointer",
        "component_ablation_pointer",
        "component_ablation_hardgate_pointer",
        "component_ablation_arm_catalog_pointer",
        "neural_ablation_hardgate_pointer",
        "neural_ablation_component_claim_pointer",
        "neural_ablation_claim_capsule_pointer",
        "neural_ablation_hg7_boundary_pointer",
        "robustness_pointer",
        "robustness_readiness_pointer",
        "robustness_hardgate_pointer",
        "discovery_map_signal_pointer",
        "discovery_map_signal_ref_pointer",
        "d4_projection_ref_pointer",
        "d4_projection_pointer",
        "d4_projection_discovery_level_pointer",
        "d5_o_projection_pointer",
        "d5_o_projection_discovery_level_pointer",
        "d5_o_projection_hardgate_pointer",
        "d5_m_projection_pointer",
        "d5_m_projection_discovery_level_pointer",
        "d5_m_projection_hardgate_pointer",
        "scaling_ladder_pointer",
        "scaling_ladder_discovery_level_pointer",
        "scaling_ladder_status_pointer",
        "scaling_ladder_hardgate_pointer",
        "scaling_ladder_source_projection_pointer",
        "l0_control_projection_pointer",
        "construct_suspension_ref_pointer",
        "l0_control_ledger_pointer",
        "l0_control_negative_witness_pointer",
        "l1_control_projection_pointer",
        "fair_l1_decision_projection_pointer",
        "fair_l1_decision_status_pointer",
        "interpretation_boundary_ref_pointer",
        "negative_witness_sweep_ref_pointer",
        "l1_control_step_ladder_pointer",
        "l1_control_step_ladder_verdict_pointer",
        "l1_control_step_ladder_crossover_pointer",
        "l1_control_review_status_pointer",
        "l1_control_promotion_readiness_pointer",
        "claim_capsule_ref_pointer",
        "evidence_envelope_ref_pointer",
        "mechanism_namecert_ref_pointer",
        "jet_certificate_ref_pointer",
        "jet_certificate_pointer",
        "jet_hardgate_pointer",
        "forbidden_claim_term_audit_pointer",
        "revocation_rows_pointer",
        "not_claimed_pointer",
        "hardgate_instance_pointers",
    }
    assert section["status"] == "pass"
    assert section["json_artifact"] == "reports/canonical/discovery-gated-transformer.json"
    assert section["markdown_artifact"] == "reports/canonical/discovery-gated-transformer.md"
    assert section["hardgate_instance_pointers"] == {
        f"DGT-HG{index}": (
            f"reports/canonical/discovery-gated-transformer.json:$.hardgate.gates.DGT-HG{index}"
        )
        for index in range(1, 21)
    }
    assert section["tool_route_evidence_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence"
    )
    assert section["tool_route_hardgate_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence.hardgate"
    )
    assert section["family_definition_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.family_definition"
    )
    assert section["family_definition_hardgate_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.family_definition.hardgate"
    )
    assert section["model_family_claim_status_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.family_definition.model_family_claim_status"
    )
    assert section["component_ablation_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.component_ablation"
    )
    assert section["component_ablation_hardgate_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.component_ablation.hardgate"
    )
    assert section["component_ablation_arm_catalog_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.component_ablation.arms"
    )
    assert section["neural_ablation_hardgate_pointer"] == (
        "reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status"
    )
    assert section["neural_ablation_component_claim_pointer"] == (
        "reports/canonical/dgt-neural-ablation.json:$.component_causal_claims"
    )
    assert section["neural_ablation_claim_capsule_pointer"] == (
        "reports/canonical/dgt-neural-ablation.json:$.claim_capsule_ref"
    )
    assert section["neural_ablation_hg7_boundary_pointer"] == (
        "reports/canonical/dgt-neural-ablation.json:$.boundary_ledger"
    )
    assert section["d4_projection_discovery_level_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.d4_projection.discovery_level"
    )
    assert section["robustness_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.operational_robustness"
    )
    assert section["d5_o_projection_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.d5_o_projection"
    )
    assert section["d5_o_projection_discovery_level_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.d5_o_projection.discovery_level"
    )
    assert section["scaling_ladder_pointer"] == (
        "reports/canonical/scaling-ladder.json:$.levels"
    )
    assert section["scaling_ladder_discovery_level_pointer"] == (
        "reports/canonical/scaling-ladder.json:$.levels"
    )
    assert section["scaling_ladder_status_pointer"] == "reports/canonical/scaling-ladder.json:$.levels"
    assert section["scaling_ladder_hardgate_pointer"] == "reports/canonical/scaling-ladder.json:$.hardgates"
    assert section["scaling_ladder_source_projection_pointer"] == (
        "reports/canonical/scaling-ladder.json:$.source_artifacts"
    )
    assert section["fair_l1_decision_projection_pointer"] == (
        "reports/canonical/fair-l1-decision.json:$.ladder_state_projection"
    )
    assert section["fair_l1_decision_status_pointer"] == (
        "reports/canonical/fair-l1-decision.json:$.decision.status"
    )
    lowered = json.dumps(section, sort_keys=True).lower()
    for forbidden in (
        "accuracy",
        "loss",
        "records",
        "raw_metrics",
        '"terminal_verdict":',
        "schema_id\": \"bedc-quality-lab:dgt-claim-capsule",
        "schema_id\": \"bedc-quality-lab:dgt-evidence-envelope",
        "schema_id\": \"bedc-quality-lab:dgt-mechanism-namecert",
        "schema_id\": \"bedc-quality-lab:dgt-jet-certificate",
    ):
        assert forbidden not in lowered


def test_scaling_ladder_index_section_is_pointer_only():
    section = canonical._scaling_ladder_index_section()

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:scaling-ladder",
        "schema_id": "bedc-quality-lab:scaling-ladder",
        "json_artifact": "reports/canonical/scaling-ladder.json",
        "markdown_artifact": "reports/canonical/scaling-ladder.md",
        "fingerprint_artifact": "reports/canonical/scaling-ladder.fingerprint.json",
        "levels_pointer": "reports/canonical/scaling-ladder.json:$.levels",
        "boundary_ledger_pointer": "reports/canonical/scaling-ladder.json:$.boundary_ledger",
        "hardgates_pointer": "reports/canonical/scaling-ladder.json:$.hardgates",
        "source_artifacts_pointer": "reports/canonical/scaling-ladder.json:$.source_artifacts",
        "not_claimed_pointer": "reports/canonical/scaling-ladder.json:$.not_claimed",
    }


def test_discovery_gated_transformer_forbidden_surfaces_absent():
    payload = canonical._build_discovery_gated_transformer_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    section = canonical._discovery_gated_transformer_index_section(payload)
    markdown = canonical._render_discovery_gated_transformer_markdown(payload)
    serialized = json.dumps({"owner": payload, "index": section}, sort_keys=True)

    for forbidden in (
        ".refactor-loop",
        "host.env",
        '"terminal_verdict":',
        "raw positive claim",
        "dgt-family-definition",
        "run_dgt_family_definition",
        "model_family.py",
    ):
        assert forbidden.lower() not in serialized.lower()
        assert forbidden.lower() not in markdown.lower()

    mutated = json.loads(json.dumps(payload))
    mutated["hardgate"]["gates"]["DGT-HG1"]["status"] = "fail"
    mutated["hardgate"]["status"] = "pass"
    with pytest.raises(ValueError, match="hardgate status"):
        canonical._validate_discovery_gated_transformer_payload(mutated)


def test_discovery_gated_transformer_public_pointers_resolve(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    real_index = canonical._index
    real_render_index_markdown = canonical._render_index_markdown
    _patch_lightweight_run_reports(monkeypatch)
    monkeypatch.setattr(canonical, "_index", real_index)
    monkeypatch.setattr(canonical, "_render_index_markdown", real_render_index_markdown)
    monkeypatch.setattr(
        canonical,
        "_build_claim_capsule",
        lambda generated_at: {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "DN",
            "terminal_verdict": "negative_discovery",
        },
    )
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)
    _patch_scaling_ladder_pass_run_spec(monkeypatch)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    owner = json.loads((tmp_path / canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT).read_text(encoding="utf-8"))
    section = payload["discovery-gated-transformer"]

    assert "discovery-gated-transformer" in {spec.name for spec in canonical.CANONICAL_REPORTS}
    assert "discovery_gated_transformer" not in payload
    assert owner["hardgate"]["status"] == "pass"
    assert owner["tool_route_evidence"]["hardgate"]["status"] == "pass"
    assert owner["family_definition"]["hardgate"]["status"] == "pass"
    assert (tmp_path / "reports/canonical/discovery-gated-transformer.fingerprint.json").exists()
    pointers = [
        section["model_id_pointer"],
        section["architecture_spec_pointer"],
        section["component_refs_pointer"],
        section["hardgate_pointer"],
        section["tool_route_evidence_pointer"],
        section["tool_route_hardgate_pointer"],
        section["family_definition_pointer"],
        section["family_definition_hardgate_pointer"],
        section["model_family_claim_status_pointer"],
        section["discovery_map_signal_pointer"],
        section["claim_capsule_ref_pointer"],
        section["evidence_envelope_ref_pointer"],
        section["mechanism_namecert_ref_pointer"],
        section["jet_certificate_ref_pointer"],
        section["not_claimed_pointer"],
        *section["hardgate_instance_pointers"].values(),
    ]
    for artifact_pointer in pointers:
        assert artifact_pointer.startswith(canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT + ":")
        assert _resolve_artifact_pointer(tmp_path, artifact_pointer) is not None
    for sidecar in (
        owner["claim_capsule_ref"],
        owner["evidence_envelope_ref"],
        owner["mechanism_namecert_ref"],
        owner["jet_certificate_ref"],
    ):
        assert _resolve_artifact_pointer(tmp_path, f"{sidecar['artifact']}:{sidecar['pointer']}") is not None


def test_discovery_gated_transformer_written_json_round_trips_validator(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    real_index = canonical._index
    real_render_index_markdown = canonical._render_index_markdown
    _patch_lightweight_run_reports(monkeypatch)
    monkeypatch.setattr(canonical, "_index", real_index)
    monkeypatch.setattr(canonical, "_render_index_markdown", real_render_index_markdown)
    monkeypatch.setattr(
        canonical,
        "_build_claim_capsule",
        lambda generated_at: {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "DN",
            "terminal_verdict": "negative_discovery",
        },
    )
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)
    _patch_scaling_ladder_pass_run_spec(monkeypatch)

    canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    owner = json.loads((tmp_path / canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT).read_text(encoding="utf-8"))

    canonical._validate_discovery_gated_transformer_payload(owner)


def test_dgt_regen_is_idempotent(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_payloads_for_all_specs(canonical, tmp_path)
    real_index = canonical._index
    real_render_index_markdown = canonical._render_index_markdown
    _patch_lightweight_run_reports(monkeypatch)
    monkeypatch.setattr(canonical, "_index", real_index)
    monkeypatch.setattr(canonical, "_render_index_markdown", real_render_index_markdown)
    monkeypatch.setattr(
        canonical,
        "_build_claim_capsule",
        lambda generated_at: {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "DN",
            "terminal_verdict": "negative_discovery",
        },
    )
    monkeypatch.setattr(
        canonical,
        "_build_formal_hardening_payload",
        lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0},
    )
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)
    _patch_scaling_ladder_pass_run_spec(monkeypatch)

    canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    first_owner = json.loads((tmp_path / canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT).read_text(encoding="utf-8"))
    first_index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    second_owner = json.loads((tmp_path / canonical.DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT).read_text(encoding="utf-8"))
    second_index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))

    assert first_owner == second_owner
    assert first_index["discovery-gated-transformer"] == second_index["discovery-gated-transformer"]



def test_discovery_regularized_training_quality_boundary_schema_and_semantics():
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])
    payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)

    canonical._validate_discovery_regularized_training_payload(payload)
    boundary = payload["quality_promotion_boundary"]
    hardgate = boundary["hardgate"]

    assert set(boundary) == {
        "slot_state",
        "owner_pointer",
        "source_artifact",
        "quality_metric",
        "replay_dimension_pointers",
        "task_only_quality_q_pointer",
        "hardgate",
        "arm_quality_order",
        "arm_comparisons",
    }
    assert boundary["slot_state"] == "present-but-fail-closed"
    assert set(boundary["replay_dimension_pointers"]) == {"steps", "seeds", "mixings", "rho", "lambda"}
    assert set(boundary["arm_comparisons"]) == set(canonical.DRT_QUALITY_PROMOTION_ARMS)
    assert boundary["arm_quality_order"] == list(canonical.DRT_QUALITY_PROMOTION_ARMS)
    assert hardgate["gate_id"] == "DRT-HG2"
    assert hardgate["slot_state"] == "present-but-fail-closed"
    assert hardgate["fail_closed_when"] == "drt_quality_q_ci_low <= task_only_quality_q"
    assert hardgate["promotion_gate"] == "clears-boundary"
    assert hardgate["drt_quality_q_ci_low"] > hardgate["task_only_quality_q"]
    assert boundary["arm_comparisons"]["DGT_full"]["promotion_gate"] == hardgate["promotion_gate"]
    assert boundary["arm_comparisons"]["old_certificate_guided"]["promotion_gate"] == "fail-closed"


def test_discovery_regularized_training_quality_boundary_fails_closed_when_drt_ci_low_not_above_task_only():
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])
    payload["lambda_summary"]["best_positive"]["delta_quality_ci_low_mean"] = 0.0
    payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)

    canonical._validate_discovery_regularized_training_payload(payload)
    hardgate = payload["quality_promotion_boundary"]["hardgate"]

    assert hardgate["drt_quality_q_ci_low"] == hardgate["task_only_quality_q"]
    assert hardgate["promotion_gate"] == "fail-closed"
    assert payload["quality_promotion_boundary"]["arm_comparisons"]["DGT_full"]["comparison_to_task_only"] == (
        "not-above-task-only-fail-closed"
    )


def test_discovery_regularized_training_quality_boundary_rejects_forbidden_body_fields():
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])
    payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)

    for mutate in (
        lambda item: item["quality_promotion_boundary"].update({"terminal_verdict": "accepted"}),
        lambda item: item["quality_promotion_boundary"]["arm_comparisons"]["DGT_full"].update(
            {"metrics": {"quality_q": 1.0}}
        ),
        lambda item: item["quality_promotion_boundary"]["arm_comparisons"]["DGT_full"].update({"host.env": {}}),
        lambda item: item["quality_promotion_boundary"]["hardgate"].update(
            {"candidate_evidence_body": {"rows": []}}
        ),
    ):
        mutated = json.loads(json.dumps(payload))
        mutate(mutated)
        with pytest.raises(ValueError):
            canonical._validate_discovery_regularized_training_payload(mutated)


def test_discovery_regularized_training_quality_boundary_pointers_resolve_when_present():
    root = Path(__file__).resolve().parents[1]
    owner_path = root / canonical.DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT
    owner = json.loads(owner_path.read_text(encoding="utf-8"))
    canonical._validate_discovery_regularized_training_payload(owner)
    boundary = owner["quality_promotion_boundary"]
    pointers = [
        boundary["owner_pointer"],
        boundary["task_only_quality_q_pointer"],
        boundary["hardgate"]["evidence_pointer"],
        *boundary["replay_dimension_pointers"].values(),
    ]
    for row in boundary["arm_comparisons"].values():
        pointers.extend([row["evidence_pointer"], row["quality_q_pointer"], row["quality_q_ci_low_pointer"]])

    unresolved = [pointer for pointer in pointers if _resolve_artifact_pointer(root, pointer) is None]

    assert unresolved == []


def test_discovery_regularized_training_quality_boundary_index_is_pointer_only():
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])
    payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)
    section = canonical._discovery_regularized_training_quality_boundary_index_section(payload)

    assert set(section) == {
        "status",
        "json_artifact",
        "markdown_artifact",
        "owner_pointer",
        "hardgate_pointer",
        "arm_comparisons_pointer",
        "compute_ledger_pointer",
        "replay_dimension_pointers",
        "ordered_arm_comparison_pointers",
    }
    assert section["status"] == "present-but-fail-closed"
    assert section["owner_pointer"] == (
        "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary"
    )
    assert section["compute_ledger_pointer"] == (
        "reports/canonical/discovery-regularized-training.json:$.compute_ledger"
    )
    assert [row["arm"] for row in section["ordered_arm_comparison_pointers"]] == list(
        canonical.DRT_QUALITY_PROMOTION_ARMS
    )
    lowered = json.dumps(section, sort_keys=True).lower()
    for forbidden in ("terminal_verdict", "metrics", "candidate_evidence_body", "host.env"):
        assert forbidden not in lowered


def test_discovery_regularized_training_quality_boundary_index_disk_invalid_payload_falls_back(monkeypatch, tmp_path):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])
    payload["quality_promotion_boundary"] = runner.quality_promotion_boundary(payload)
    payload["quality_promotion_boundary"]["hardgate"]["candidate_evidence_body"] = {"rows": []}

    with pytest.raises(ValueError):
        canonical._discovery_regularized_training_quality_boundary_index_section(payload)

    json_path = canonical._artifact_path(canonical.DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    section = canonical._discovery_regularized_training_quality_boundary_index_section()

    assert section["status"] == "present-but-fail-closed"
    assert section["owner_pointer"] == (
        "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary"
    )
    assert section["hardgate_pointer"] == (
        "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.hardgate"
    )
    assert section["arm_comparisons_pointer"] == (
        "reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.arm_comparisons"
    )
    assert [row["arm"] for row in section["ordered_arm_comparison_pointers"]] == list(
        canonical.DRT_QUALITY_PROMOTION_ARMS
    )


def test_drt_canonical_spec_has_no_companion_artifacts():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    drt_names = [name for name in names if "discovery-regularized-training" in name]

    assert drt_names == ["discovery-regularized-training"]
    forbidden_names = {
        "discovery-regularized-training-loss-ablation",
        "discovery-regularized-training-component-ablation",
        "discovery-regularized-training-method-comparison",
    }
    assert forbidden_names.isdisjoint(names)
    assert all(re.search(r"\bdrt[-_]?v\d+\b", name) is None for name in names)


def test_drt_jet_sidecar_artifacts_stay_under_single_canonical_owner():
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    markdown_artifacts = {spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS}
    payload = _payload_for_spec(canonical._specs_by_name()["discovery-regularized-training"])

    assert "discovery-regularized-training-jet" not in names
    assert payload["jet_sidecar_artifacts"]["jet_loss_surface"] not in json_artifacts
    assert payload["jet_sidecar_artifacts"]["jet_loss_frontier"] not in json_artifacts
    assert payload["jet_sidecar_artifacts"]["jet_ablation"] not in markdown_artifacts
    assert payload["jet_sidecar_artifacts"]["owner_artifact_id"] == payload["artifact_id"]
    assert payload["jet_sidecar_artifacts"]["owner_pointer"].endswith("$.jet_loss_surface")


def test_discovery_regularized_training_regen_idempotent_with_extension_sections(tmp_path):
    first_projection = runner.build_projection(generated_at="fixture-time")
    runner.write_artifacts(first_projection, root=tmp_path)
    first_json = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    second_projection = runner.build_projection(generated_at="fixture-time")
    runner.write_artifacts(second_projection, root=tmp_path)
    second_json = (tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8")
    second_md = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")
    payload = json.loads(second_json)

    assert first_json == second_json
    assert first_md == second_md
    assert payload["loss_family"]["status"] == "pointer-only"
    assert payload["component_ablation"]["status"] == "pointer-only"
    assert payload["training_method_comparison"]["status"] == "pointer-only"
    assert payload["drt_extension_hardgates"]["status"] == "pass"


def test_discovery_regularized_training_producer_json_round_trips_validator(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["discovery-regularized-training"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    projection = runner.build_projection(generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path)
    owner = json.loads(json_path.read_text(encoding="utf-8"))

    canonical._validate_discovery_regularized_training_payload(owner)
    assert "Quality Promotion Boundary" in md_path.read_text(encoding="utf-8")


def test_hg_p_forbidden_claim_terms_are_absent_from_positive_claim_cells():
    reports = [
        {
            "name": spec.name,
            "bundle_role": spec.bundle_role,
            "discipline": {
                "claim_promotion_eligible": spec.claim_promotion_eligible,
                "positive_claim_pointer": spec.positive_claim_pointer,
                "control_pointer": spec.control_pointer,
                "no_control_rationale_pointer": spec.no_control_rationale_pointer,
            },
        }
        for spec in canonical.CANONICAL_REPORTS
    ]
    cells = canonical._claims_nonclaims(reports)["positive_claim_cells"]
    forbidden = set(canonical.FORBIDDEN_POSITIVE_CLAIM_TERMS)

    for cell in cells:
        text = " ".join(str(value).lower() for value in cell.values())
        for term in forbidden:
            assert term not in text


def test_forbidden_term_at_positive_claim_pointer_is_caught(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    payload = _payload_for_spec(spec)
    payload["coverage_item"] = {
        "status": "positive",
        "claim": "full-lejepa certification",
    }
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)

    result = canonical._run_spec(spec)

    assert result["status"] == "fail"
    assert result["producer_status"] == "completed"
    assert result["validation"]["status"] == "pass"
    assert result["discipline"]["positive_claim_pointer"] == "$.coverage_item"
    assert result["discipline"]["forbidden_claim_terms_status"] == "fail"
    assert result["discipline"]["forbidden_claim_term_hits"] == ["full-lejepa"]


def test_run_spec_can_reuse_existing_artifacts_without_producer(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    def unexpected_producer(_spec):
        raise AssertionError("producer should not run")

    monkeypatch.setattr(canonical, "_run_producer", unexpected_producer)

    result = canonical._run_spec(spec, reuse_existing=True)

    assert result["status"] == "pass"
    assert result["producer_status"] == "skipped"
    assert result["validation"]["status"] == "pass"


def test_matching_fingerprint_skips_producer_but_validates(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    calls = {"producer": 0, "validation": 0, "discipline": 0}
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: calls.__setitem__("producer", calls["producer"] + 1))
    monkeypatch.setattr(canonical, "_artifact_validation", lambda _spec: calls.__setitem__("validation", calls["validation"] + 1) or {"status": "pass"})
    monkeypatch.setattr(canonical, "_discipline", lambda _spec: calls.__setitem__("discipline", calls["discipline"] + 1) or {"forbidden_claim_terms_status": "pass"})

    result = canonical._run_spec(spec, mode="verify")

    assert result["producer_status"] == "skipped"
    assert result["fingerprint_status"] == "match"
    assert calls == {"producer": 0, "validation": 1, "discipline": 1}


def test_fingerprint_staleness_fail_closed_and_cold_digest(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    (tmp_path / spec.command[1]).write_text("SEED = 8\n\ndef main(argv=None):\n    return None\n", encoding="utf-8")

    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")
    assert "fingerprint sidecar mismatch" in canonical._run_spec(spec, mode="verify")["error"]

    monkeypatch.setattr(canonical, "_run_producer", lambda target: _write_fingerprint_fixture(canonical, tmp_path, target))
    result = canonical._run_spec(spec, mode="cold", generated_at="fixture")
    sidecar = json.loads(canonical._fingerprint_path(spec).read_text(encoding="utf-8"))
    assert result["producer_status"] == "completed"
    assert "output_digest" not in sidecar
    assert sidecar["reproducibility_mode"] == "exact_fixture"
    assert len(sidecar["reproducibility_contract_digest"]) == 64


def test_output_byte_change_inside_contract_still_matches_fingerprint(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["lejepa-theorem-ledger"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)

    canonical._artifact_path(spec.markdown_artifact).write_text("# changed fixture bytes\n", encoding="utf-8")

    assert canonical._fingerprint_matches(spec) == (True, "match")


def test_true_training_fingerprint_uses_owner_pointer_contract_not_embedded_contract(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["dgt-neural-ablation"]
    script = tmp_path / spec.command[1]
    script.parent.mkdir(parents=True, exist_ok=True)
    script.write_text("SEED = 7\n\ndef main(argv=None):\n    return None\n", encoding="utf-8")
    run_policy = {
        "requested_device": "auto",
        "resolved_device": "cpu",
        "resolution_status": "fallback",
        "resolution_reason": "auto-cpu-fallback-no-accelerator",
        "backend_details": {"torch": "fixture", "cuda_available": False, "mps_available": False},
    }
    payload = {
        "schema_id": "fixture:dgt-neural-ablation",
        "artifact_id": "fixture:dgt-neural-ablation",
        "source_artifacts": {},
        "run_spec": {"seed_list": [1, 2], "device_policy": run_policy},
        "nabl_hardgates": {"status": "pass"},
        "paired_delta_matrix": {"status": "fixture"},
    }
    stale_contract = canonical._training_reproducibility_contract_payload(spec, payload)
    stale_contract["device_policy"] = {
        "requested_device": "auto",
        "resolved_device": "mps",
        "resolution_status": "available",
        "resolution_reason": "recorded-device-policy",
        "backend_details": {},
    }
    payload["reproducibility_contract"] = stale_contract
    stale_digest = canonical.contract_from_payload(payload).digest()
    json_path = canonical._artifact_path(spec.json_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    canonical._artifact_path(spec.markdown_artifact).write_text("# fixture\n", encoding="utf-8")
    input_fingerprint, inputs = canonical._input_fingerprint(spec)
    canonical._fingerprint_path(spec).write_text(
        json.dumps(
            {
                "schema_id": canonical.FINGERPRINT_SCHEMA_ID,
                "report_name": spec.name,
                "json_artifact": spec.json_artifact,
                "markdown_artifact": spec.markdown_artifact,
                "producer_command": list(spec.command),
                "input_fingerprint": input_fingerprint,
                "reproducibility_mode": "true_training",
                "reproducibility_contract_digest": stale_digest,
                "reproducibility_contract": canonical.contract_from_payload(payload).to_payload(),
                "inputs": inputs,
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    assert canonical._fingerprint_matches(spec) == (False, "reproducibility-contract-digest")


def test_relative_lab_helper_imports_enter_fingerprint_closure(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_lab_report_import_fixture(tmp_path, spec)

    paths = canonical._import_closure(spec.command)

    assert paths == sorted(paths)
    assert "bedc_quality_lab/report.py" in paths
    assert "bedc_quality_lab/cost_protocol.py" in paths
    assert "bedc_quality_lab/schema.py" in paths
    assert "bedc_quality_lab/tensor_namecert_candidate.py" in paths


@pytest.mark.parametrize(
    ("label", "mutate"),
    [
        ("producer-source", lambda root, spec: (root / spec.command[1]).write_text("SEED = 8\n", encoding="utf-8")),
        ("seed-cell", lambda root, spec: (root / spec.command[1]).write_text("SEED = 9\n", encoding="utf-8")),
        ("source-artifact", lambda root, spec: (root / "reports" / "canonical" / "upstream.json").write_text('{"cell": 2}\n', encoding="utf-8")),
    ],
)
def test_fingerprint_staleness_inputs_cause_miss(tmp_path, monkeypatch, label, mutate):
    del label
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    config_path = tmp_path / "configs" / "default_cost_protocol.yaml"
    config_path.parent.mkdir(parents=True, exist_ok=True)
    config_path.write_text("unit_cost: 1\n", encoding="utf-8")
    json_path = canonical._artifact_path(spec.json_artifact)
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    upstream_path = tmp_path / "reports" / "canonical" / "upstream.json"
    upstream_path.write_text('{"cell": 1}\n', encoding="utf-8")
    payload["source_artifacts"] = {"upstream": "reports/canonical/upstream.json"}
    json_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    canonical._write_fingerprint_sidecar(spec, generated_at="fixture")

    mutate(tmp_path, spec)

    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")


def test_relative_lab_helper_edit_causes_fingerprint_miss(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_lab_report_import_fixture(tmp_path, spec)
    _write_fingerprint_fixture(canonical, tmp_path, spec, script_text=(tmp_path / spec.command[1]).read_text(encoding="utf-8"))

    (tmp_path / "bedc_quality_lab" / "cost_protocol.py").write_text("COST_PROTOCOL = 'changed'\n", encoding="utf-8")

    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")


def test_dependency_abi_change_causes_fingerprint_miss(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "_dependency_abi", lambda: {"python": "fixture-a"})
    _write_fingerprint_fixture(canonical, tmp_path, spec)

    monkeypatch.setattr(canonical, "_dependency_abi", lambda: {"python": "fixture-b"})

    assert canonical._fingerprint_matches(spec) == (False, "input-fingerprint")


def test_verify_mode_fails_closed_for_missing_or_corrupt_sidecar(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    canonical._fingerprint_path(spec).unlink()

    missing = canonical._run_spec(spec, mode="verify")
    assert missing["status"] == "error"
    assert "missing fingerprint sidecar" in missing["error"]

    canonical._fingerprint_path(spec).write_text("{not-json}\n", encoding="utf-8")
    corrupt = canonical._run_spec(spec, mode="verify")
    assert corrupt["status"] == "error"
    assert "corrupt fingerprint sidecar" in corrupt["error"]


def test_run_spec_force_path_runs_producer_for_existing_artifacts(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")
    calls = []

    monkeypatch.setattr(canonical, "_run_producer", lambda called: calls.append(called.name))

    result = canonical._run_spec(spec, reuse_existing=False)

    assert calls == ["mixing-family-sweep"]
    assert result["producer_status"] == "completed"
    assert result["duration_seconds"] == 0.0


def test_run_spec_completed_fingerprint_miss_reports_zero_duration(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    calls = []

    def producer(called):
        calls.append(called.name)
        json_path = canonical._artifact_path(called.json_artifact)
        md_path = canonical._artifact_path(called.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(called)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_fingerprint_matches", lambda _spec: (False, "input-fingerprint"))
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", lambda _spec, generated_at=None: {})
    monkeypatch.setattr(canonical, "_run_producer", producer)

    result = canonical._run_spec(spec)

    assert calls == ["mixing-family-sweep"]
    assert result["producer_status"] == "completed"
    assert result["fingerprint_status"] == "written"
    assert result["fingerprint_reason"] == "input-fingerprint"
    assert result["duration_seconds"] == 0.0


def test_literature_ledger_status_follows_validator_not_path_existence(tmp_path, monkeypatch):
    ledger = tmp_path / "docs" / "lit" / "literature_ledger.yaml"
    ledger.parent.mkdir(parents=True)
    ledger.write_text("{}\n", encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)

    payload = canonical._literature_ledger()

    assert payload["status"] == "not-ready"
    assert payload["pointer"] == "docs/lit/literature_ledger.yaml"
    assert payload["record_count"] == 0
    assert "failures" in payload
    assert "records" not in payload


def test_artifact_path_rejects_non_canonical_paths():
    with pytest.raises(ValueError):
        canonical._artifact_path("reports/not-canonical.json")


def test_only_selects_one_manifest_row_and_rejects_unknown():
    selected = canonical._select_specs("gap-head-discovery")

    assert [spec.name for spec in selected] == ["gap-head-discovery"]
    with pytest.raises(ValueError):
        canonical._select_specs("missing")


def test_run_reports_only_writes_index_and_summary_from_producer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    old_runner = canonical._run_producer
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    canonical.INDEX_ARTIFACT = tmp_path / "reports" / "canonical" / "index.json"
    _write_release_pointer_fixture(tmp_path)
    canonical_dir = canonical.CANONICAL_DIR
    index_path = canonical.INDEX_ARTIFACT
    summary_path = tmp_path / "summary.json"
    calls = []

    def fake_run_producer(spec):
        calls.append(spec.name)
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(
            json.dumps(_payload_for_spec(spec)) + "\n",
            encoding="utf-8",
        )
        md_path.write_text("# fixture\n", encoding="utf-8")

    canonical._run_producer = fake_run_producer

    try:
        payload = canonical.run_reports(
            only="gap-head-on-h",
            json_summary=str(summary_path),
        )
        index_markdown = (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
        canonical._run_producer = old_runner

    assert calls == ["gap-head-on-h", "gap-head-discovery"]
    assert payload["schema_id"] == canonical.INDEX_SCHEMA_ID
    assert len(payload["reports"]) == 2
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert json.loads(index_path.read_text(encoding="utf-8")) == payload
    assert json.loads(summary_path.read_text(encoding="utf-8")) == payload
    assert "gap-head-on-h" in index_markdown
    assert (canonical_dir / "quality-scorecard.json").exists()
    assert (canonical_dir / "quality-scorecard.md").exists()


def test_run_reports_verify_fingerprints_skips_matching_artifact(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    calls = []
    monkeypatch.setattr(canonical, "_run_producer", lambda called: calls.append(called.name))

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert calls == []
    assert payload["reports"][0]["fingerprint_status"] == "match"
    assert payload["reports"][0]["producer_status"] == "skipped"


def test_run_reports_preflight_runs_before_fingerprint_acceptance(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    calls = []

    def fake_preflight(report_artifacts=None):
        calls.append(("preflight", tuple(report_artifacts or ())))
        return {"status": "pass"}

    def fake_run_producer(called):
        calls.append(f"producer:{called.name}")

    monkeypatch.setattr(canonical, "_run_metric_purity_preflight", fake_preflight)
    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert calls == [("preflight", (spec.json_artifact,))]
    assert payload["reports"][0]["fingerprint_status"] == "match"


def test_run_reports_verify_fingerprints_rejects_mutated_sidecar_inputs(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    sidecar = _write_fingerprint_fixture(canonical, tmp_path, spec)
    sidecar["inputs"]["producer_sources"][0]["sha256"] = "0" * 64
    canonical._fingerprint_path(spec).write_text(json.dumps(sidecar, sort_keys=True) + "\n", encoding="utf-8")
    calls = []
    monkeypatch.setattr(canonical, "_run_producer", lambda called: calls.append(called.name))
    summary_path = tmp_path / "summary.json"

    with pytest.raises(SystemExit) as excinfo:
        canonical.run_reports(
            verify_fingerprints=True,
            generated_at="2030-01-01T00:00:00+00:00",
            json_summary=str(summary_path),
        )

    assert excinfo.value.code == 1
    assert calls == []
    payload = json.loads(summary_path.read_text(encoding="utf-8"))
    assert payload["reports"][0]["status"] == "error"
    assert payload["reports"][0]["fingerprint_status"] == "miss"
    assert payload["reports"][0]["fingerprint_reason"] == "inputs"


def test_run_reports_verify_fingerprints_does_not_rewrite_derived_outputs(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    index_path = canonical.INDEX_ARTIFACT
    index_path.parent.mkdir(parents=True, exist_ok=True)
    index_path.write_text('{"sentinel": true}\n', encoding="utf-8")

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["reports"][0]["fingerprint_status"] == "match"
    assert json.loads(index_path.read_text(encoding="utf-8")) == {"sentinel": True}


def test_run_reports_verify_fingerprints_allows_matching_fail_closed_auxiliary(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["dgt-l0-controls"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    payload = json.loads(canonical._artifact_path(spec.json_artifact).read_text(encoding="utf-8"))
    payload["construct_validity_hardgates"]["status"] = "fail"
    payload["construct_validity_hardgates"]["failed_gates"] = ["CV-HG4"]
    payload["construct_validity_hardgates"]["gates"]["CV-HG4"]["status"] = "fail"
    canonical._artifact_path(spec.json_artifact).write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    canonical._write_fingerprint_sidecar(spec, generated_at="fixture")

    result = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert result["reports"][0]["status"] == "fail"
    assert result["reports"][0]["fingerprint_status"] == "match"
    assert result["reports"][0]["producer_status"] == "skipped"


def test_verify_fingerprints_allows_fail_closed_report_status(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)

    def fake_run_spec(called, mode="changed", generated_at=None):
        row = _index_row_for_spec(called)
        row["status"] = "fail"
        row["fingerprint_status"] = "match"
        row["fingerprint_reason"] = "match"
        return row

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["reports"][0]["status"] == "fail"
    assert payload["reports"][0]["fingerprint_status"] == "match"


def test_changed_run_allows_fail_closed_report_status(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))

    def fake_run_spec(called, mode="changed", generated_at=None):
        row = _index_row_for_spec(called)
        row["status"] = "fail"
        row["fingerprint_status"] = "match"
        row["fingerprint_reason"] = "match"
        return row

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")

    assert payload["reports"][0]["status"] == "fail"
    assert payload["reports"][0]["fingerprint_status"] == "match"


def test_experiment_stack_cards_run_after_release_sidecar_inputs(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    reports = canonical._specs_by_name()
    pre_spec = reports["mixing-family-sweep"]
    stack_spec = reports["experiment-stack-cards"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (pre_spec, stack_spec))
    calls = []

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name))
        return _index_row_for_spec(spec)

    def fake_release(*, root, generated_at=None):
        calls.append(("write-release", None))
        path = root / canonical.RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "schema_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                    "artifact_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                    "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
                    "generated_at": generated_at,
                    "version": "0.0.1",
                    "tag_ref": None,
                    "release_bundle_status": "ready",
                    "tag_status": "absent",
                    "source_pointers": {},
                    "required_pointers": [
                        {
                            "id": "fixture-pointer",
                            "path": "reports/canonical/index.json",
                            "pointer": "$.schema_id",
                            "status": "resolved",
                            "failure": None,
                        }
                    ],
                    "not_claimed": ["fixture boundary"],
                    "revoke_if": "Revoke if fixture pointer stops resolving.",
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        return {}

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setitem(
        sys.modules,
        "scripts.release_manifest_sidecar",
        types.SimpleNamespace(write_release_manifest_sidecar=fake_release),
    )

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")

    assert "experiment-stack-cards" in canonical.RELEASE_INPUT_REPORTS
    assert calls.index(("write-release", None)) < calls.index(("run-spec", "experiment-stack-cards"))
    assert [report["name"] for report in payload["reports"]] == ["mixing-family-sweep", "experiment-stack-cards"]


def test_run_reports_verify_fingerprints_does_not_cold_write_claim_graph_prerequisites(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["model-comparison"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    calls = []

    def fake_run_producer(called):
        calls.append(("producer", called.name))

    def fake_write_fingerprint(called, *, generated_at=None):
        calls.append(("fingerprint", called.name))
        return {}

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", fake_write_fingerprint)

    payload = canonical.run_reports(verify_fingerprints=True, generated_at="2030-01-01T00:00:00+00:00")

    assert calls == []
    assert payload["reports"][0]["fingerprint_status"] == "match"
    assert payload["reports"][0]["producer_status"] == "skipped"


def test_run_reports_cold_runs_selected_report(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    calls = []

    def fake_run_producer(called):
        calls.append(called.name)
        _write_fingerprint_fixture(canonical, tmp_path, called)

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(cold=True, generated_at="2030-01-01T00:00:00+00:00")

    assert calls == ["mixing-family-sweep"]
    assert payload["reports"][0]["fingerprint_status"] == "written"
    sidecar = json.loads(canonical._fingerprint_path(spec).read_text(encoding="utf-8"))
    assert "output_digest" not in sidecar
    assert len(sidecar["reproducibility_contract_digest"]) == 64


def test_configure_producer_does_not_disable_true_training_torch():
    spec = canonical._specs_by_name()["certificate-guided-training"]

    class StubTrainingProducer:
        USE_TORCH = True

    canonical._configure_producer(StubTrainingProducer, spec)

    assert StubTrainingProducer.USE_TORCH is True


def test_run_reports_force_runs_selected_report(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    calls = []

    def fake_run_producer(called):
        calls.append(called.name)
        _write_fingerprint_fixture(canonical, tmp_path, called)

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(force=True, generated_at="2030-01-01T00:00:00+00:00")

    assert calls == ["mixing-family-sweep"]
    assert payload["reports"][0]["producer_status"] == "completed"


def test_run_reports_scaling_ladder_only_updates_pointer_index(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    calls = []
    existing_index = {
        "schema_id": canonical.INDEX_SCHEMA_ID,
        "generated_at": "old-time",
        "root": canonical.INDEX_ROOT,
        "reports": [_index_row_for_spec(canonical._specs_by_name()["mixing-family-sweep"])],
        "paper_outline": {"status": "fixture", "core_reports": [], "auxiliary_reports": [], "sections": []},
    }
    canonical.INDEX_ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    canonical.INDEX_ARTIFACT.write_text(json.dumps(existing_index) + "\n", encoding="utf-8")

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append((spec.name, mode, generated_at))
        return _index_row_for_spec(spec)

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)

    payload = canonical.run_reports(only="scaling-ladder", generated_at="2030-01-01T00:00:00+00:00")

    assert calls == [("scaling-ladder", "cold", "2030-01-01T00:00:00+00:00")]
    assert [report["name"] for report in payload["reports"]] == ["mixing-family-sweep", "scaling-ladder"]
    assert payload["scaling_ladder"]["levels_pointer"] == "reports/canonical/scaling-ladder.json:$.levels"
    assert "discovery-gated-transformer" not in payload
    assert json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8")) == payload
    assert "reports/canonical/scaling-ladder.json:$.levels" in (
        canonical.CANONICAL_DIR / "index.md"
    ).read_text(encoding="utf-8")


def test_scaling_ladder_artifact_validation_rejects_hand_edited_level_rows(tmp_path, monkeypatch):
    from bedc_quality_lab.scaling_ladder import build_scaling_ladder_payload, render_scaling_ladder_markdown
    from tests.test_scaling_ladder import _write_json, _write_owner_inputs

    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/discovery-gated-transformer.json",
        {"scaling_ladder": {"opened_levels": ["L0_toy"]}},
    )
    spec = canonical._specs_by_name()["scaling-ladder"]
    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")
    payload["levels"][0]["state"] = "open"
    payload["levels"][0]["reason"] = "eligible"
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_scaling_ladder_markdown(build_scaling_ladder_payload(root=tmp_path)), encoding="utf-8")

    validation = canonical._artifact_validation(spec)

    assert validation["status"] == "fail"
    assert validation["required_key_validation"]["status"] == "pass"
    assert validation["semantic_errors"] == ["scaling ladder level owner projection mismatch"]


def test_scaling_ladder_owner_boundary_forces_claim_verdict_downgrade(tmp_path, monkeypatch):
    from bedc_quality_lab.scaling_ladder import build_scaling_ladder_payload
    from tests.test_discovery_map import _ready_dgt_scaling_level
    from tests.test_scaling_ladder import _write_json, _write_owner_inputs
    from scripts import run_discovery_gated_transformer as dgt_runner
    from scripts import run_claim_verdict_demo as claim_verdict_demo
    from bedc_quality_lab.discovery_gated_transformer import L0_LADDER_CONSUMPTION_REF

    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _write_release_pointer_fixture(tmp_path)
    _write_owner_inputs(tmp_path)
    dgt_payload = dgt_runner.build_payload(generated_at="fixture-time")
    dgt_payload["source_artifacts"]["ladder_consumption_ref"] = dict(L0_LADDER_CONSUMPTION_REF)
    levels = [
        {"level_id": level_id, "claim_capsule": _ready_dgt_scaling_level(level_id, index)}
        for index, level_id in enumerate(dgt_runner.SCALING_LADDER_LEVEL_IDS)
    ]
    levels[0]["claim_capsule"]["ladder_consumption_ref"] = dict(L0_LADDER_CONSUMPTION_REF)
    levels[0]["claim_capsule"]["ladder_consumption_status"] = "open"
    dgt_payload["scaling_ladder"] = {"levels": levels}
    dgt_payload["scaling_ladder"] = dgt_runner.build_scaling_ladder_projection(dgt_payload)
    _write_json(tmp_path, "reports/canonical/discovery-gated-transformer.json", dgt_payload)
    scaling_payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")
    _write_json(tmp_path, "reports/canonical/scaling-ladder.json", scaling_payload)
    scorecard = {
        "artifact_id": canonical.QUALITY_SCORECARD_ARTIFACT_ID,
        "rows": [
            {"metric": metric, "status": "ready", "value": index}
            for index, metric in enumerate(canonical.QUALITY_SCORECARD_METRICS)
        ],
    }
    _write_json(tmp_path, "reports/canonical/quality-scorecard.json", scorecard)
    _write_json(tmp_path, "reports/canonical/formal_hardening.json", {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    specs = (canonical._specs_by_name()["discovery-gated-transformer"],)
    discovery_payload = discovery_map.build_discovery_map(
        generated_at="fixture-time",
        root=tmp_path,
        canonical_reports=specs,
    )
    _write_json(tmp_path, "reports/canonical/discovery_map.json", discovery_payload)
    index_path = tmp_path / "reports/canonical/index.json"
    index_payload = json.loads(index_path.read_text(encoding="utf-8"))
    index_payload["evidence_provenance"] = canonical._evidence_provenance_index_section(
        "fixture-time",
        canonical_reports=specs,
    )
    index_path.write_text(json.dumps(index_payload, sort_keys=True) + "\n", encoding="utf-8")

    row = next(row for row in discovery_payload["rows"] if row["report"] == "discovery-gated-transformer")
    verdict = claim_verdict_demo.compile_claim_verdicts(tmp_path, generated_at="fixture-time")[0]

    assert row["discovery_level"] == "D0"
    assert row["scaling_ladder_pointer"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert row["evidence_pointer"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert row["failed_gate"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert verdict["claim_id"] == "claim:discovery-gated-transformer"
    assert verdict["claim_verdict"] == "projected_discovery_required"
    assert verdict["reason"] == "model-comparison-not-ready"
    assert verdict["source"] == "reports/canonical/scaling-ladder.json:$.levels[0]"
    assert verdict["ledger_pointer"] == "reports/canonical/discovery_map.json:$.rows[0].discovery_level"


def test_run_reports_runs_dgt_l0_controls_before_dgt_owner_generation(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    calls = []
    reports = canonical._specs_by_name()
    l0_spec = reports["dgt-l0-controls"]
    dgt_spec = reports["discovery-gated-transformer"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (l0_spec, dgt_spec))
    _patch_dgt_owner_fixture(monkeypatch, calls)

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name))
        return _index_row_for_spec(spec)

    def fake_write_fingerprint(spec, *, generated_at=None):
        calls.append(("fingerprint", spec.name))
        return {}

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", fake_write_fingerprint)

    canonical.run_reports(only="discovery-gated-transformer", generated_at="2030-01-01T00:00:00+00:00")

    assert calls.index(("run-spec", "discovery-gated-transformer")) < calls.index(("build-dgt", "discovery-gated-transformer"))
    assert calls.index(("run-spec", "dgt-l0-controls")) < calls.index(("build-dgt", "discovery-gated-transformer"))
    assert calls.index(("fingerprint", "dgt-l0-controls")) < calls.index(("build-dgt", "discovery-gated-transformer"))


def test_run_reports_refreshes_dgt_l1_controls_after_dgt_owner_generation(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    calls = []
    reports = canonical._specs_by_name()
    l1_spec = reports["dgt-l1-controls"]
    dgt_spec = reports["discovery-gated-transformer"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (l1_spec, dgt_spec))
    _patch_dgt_owner_fixture(monkeypatch, calls)

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name, mode))
        return _index_row_for_spec(spec) | {"fingerprint_status": "match", "fingerprint_reason": "match"}

    def fake_write_fingerprint(spec, *, generated_at=None):
        calls.append(("fingerprint", spec.name))
        return {}

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", fake_write_fingerprint)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")

    assert calls.index(("fingerprint", "dgt-l1-controls")) > calls.index(("build-dgt", "discovery-gated-transformer"))
    assert ("run-spec", "dgt-l1-controls", "verify") in calls
    assert [row for row in payload["reports"] if row["name"] == "dgt-l1-controls"][0]["fingerprint_status"] == "match"


def test_run_reports_does_not_run_dgt_l0_controls_twice_when_selected(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    calls = []
    reports = canonical._specs_by_name()
    l0_spec = reports["dgt-l0-controls"]
    dgt_spec = reports["discovery-gated-transformer"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (l0_spec, dgt_spec))
    _patch_dgt_owner_fixture(monkeypatch, calls)

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name))
        return _index_row_for_spec(spec)

    def fake_write_fingerprint(spec, *, generated_at=None):
        calls.append(("fingerprint", spec.name))
        return {}

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setattr(canonical, "_write_fingerprint_sidecar", fake_write_fingerprint)

    canonical.run_reports(only="dgt-l0-controls", generated_at="2030-01-01T00:00:00+00:00")

    assert calls.count(("run-spec", "dgt-l0-controls")) == 1
    assert ("fingerprint", "dgt-l0-controls") not in calls


def test_run_reports_cold_only_matches_normalized_committed_artifact(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    committed_payload = _payload_for_spec(spec)

    def fake_run_producer(called):
        json_path = canonical._artifact_path(called.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(committed_payload, sort_keys=True) + "\n", encoding="utf-8")
        canonical._artifact_path(called.markdown_artifact).write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    canonical.run_reports(cold=True, only=spec.name, generated_at="2030-01-01T00:00:00+00:00")

    assert json.loads(canonical._artifact_path(spec.json_artifact).read_text(encoding="utf-8")) == committed_payload


def test_changed_only_runs_stale_report_and_declared_dependent(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    unrelated = canonical._specs_by_name()["mixing-family-sweep"]
    source = canonical._specs_by_name()["gap-head-on-h"]
    dependent = canonical._specs_by_name()["gap-head-discovery"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (unrelated, source, dependent))
    monkeypatch.setattr(canonical, "_selected_specs_with_dependents", lambda only, include_dependents=True: (unrelated, source, dependent))
    for spec in (unrelated, source, dependent):
        _write_fingerprint_fixture(canonical, tmp_path, spec)
    (tmp_path / source.command[1]).write_text("SEED = 18\n", encoding="utf-8")
    calls = []

    def fake_run_producer(called):
        calls.append(called.name)
        json_path = canonical._artifact_path(called.json_artifact)
        payload = _payload_for_spec(called)
        if called.name == "gap-head-on-h":
            payload["producer_cell"] = "changed"
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
        canonical._artifact_path(called.markdown_artifact).write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")

    assert calls == ["gap-head-on-h", "gap-head-discovery"]
    by_name = {row["name"]: row for row in payload["reports"]}
    assert by_name["mixing-family-sweep"]["producer_status"] == "skipped"
    assert by_name["mixing-family-sweep"]["validation"]["status"] == "pass"
    assert by_name["gap-head-on-h"]["producer_status"] == "completed"
    assert by_name["gap-head-discovery"]["producer_status"] == "completed"


def test_matching_changed_only_run_is_idempotent(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    _write_fingerprint_fixture(canonical, tmp_path, spec)
    monkeypatch.setattr(canonical, "_run_producer", lambda called: (_ for _ in ()).throw(AssertionError(called.name)))

    canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    first = _file_digest_map(tmp_path)
    canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    second = _file_digest_map(tmp_path)

    assert first == second


def test_same_seed_produces_same_payload(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (spec,))
    calls = []

    def fake_run_producer(called):
        calls.append(called.name)
        seed = 314
        json_path = canonical._artifact_path(called.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        payload = _payload_for_spec(called)
        payload["seeded_value"] = seed * 17
        json_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
        canonical._artifact_path(called.markdown_artifact).write_text(f"# seed {seed}\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    canonical.run_reports(cold=True, generated_at="2030-01-01T00:00:00+00:00")
    first = json.loads(canonical._artifact_path(spec.json_artifact).read_text(encoding="utf-8"))
    canonical.run_reports(cold=True, generated_at="2030-01-01T00:00:00+00:00")
    second = json.loads(canonical._artifact_path(spec.json_artifact).read_text(encoding="utf-8"))

    assert calls == ["mixing-family-sweep", "mixing-family-sweep"]
    assert first == second


def test_targeted_selection_includes_declared_dependents():
    assert [spec.name for spec in canonical._selected_specs_with_dependents("certificate-guided-training")] == [
        "certificate-guided-training",
        "certificate-guided-discovery",
    ]


def test_quality_scorecard_has_exactly_twelve_metric_rows(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        rows = canonical._build_quality_scorecard([], generated_at="fixture-time")["rows"]
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert [row["metric"] for row in rows] == list(canonical.QUALITY_SCORECARD_METRICS)
    assert {row["metric"] for row in rows} == QUALITY_SCORECARD_METRICS
    assert len(rows) == 12


def test_quality_scorecard_is_generated_by_canonical_runner(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)
    _write_dimension_mismatch_gap_witness_fixture(tmp_path)

    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    canonical.INDEX_ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    canonical.INDEX_ARTIFACT.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    (canonical.CANONICAL_DIR / "index.md").write_text(canonical._render_index_markdown(payload), encoding="utf-8")
    scorecard_json = canonical.CANONICAL_DIR / "quality-scorecard.json"
    scorecard_md = canonical.CANONICAL_DIR / "quality-scorecard.md"

    assert scorecard_json.exists()
    assert scorecard_md.exists()
    assert payload["quality_scorecard"]["json_artifact"] == "reports/canonical/quality-scorecard.json"
    assert payload["quality_scorecard"]["markdown_artifact"] == "reports/canonical/quality-scorecard.md"
    assert "Quality scorecard" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    assert "run_quality_scorecard.py" not in json.dumps(payload)


def test_discovery_map_is_registered_by_canonical_runner(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    canonical.INDEX_ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    canonical.INDEX_ARTIFACT.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    (canonical.CANONICAL_DIR / "index.md").write_text(canonical._render_index_markdown(payload), encoding="utf-8")

    assert payload["discovery_map"]["artifact_id"] == "bedc-quality-lab:discovery-map"
    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert "Discovery map" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")


def test_canonical_index_points_to_discovery_map_coverage_matrix(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["coverage_matrix_pointer"] == "reports/canonical/discovery_map.json:$.coverage_matrix"
    assert "discovery_coverage" not in payload
    assert "coverage_matrix" not in payload["discovery_map"]
    assert "cells" not in payload["discovery_map"]
    assert "hardgates" not in payload["discovery_map"]
    assert "models" not in payload["discovery_map"]
    assert "surfaces" not in payload["discovery_map"]
    assert not (canonical.CANONICAL_DIR / "discovery_coverage.json").exists()
    assert all(report["name"] != "discovery_coverage" for report in payload["reports"])


def test_canonical_index_exposes_experiment_proposals_as_pointer_sidecar(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["experiment_proposals"]["canonical_role"] == "pointer_sidecar_not_CANONICAL_REPORTS"
    assert payload["experiment_proposals"]["proposal_rows_pointer"] == "reports/canonical/experiment_proposals.json:$.rows"
    assert payload["experiment_proposals"]["source_artifacts_pointer"] == (
        "reports/canonical/experiment_proposals.json:$.source_artifacts"
    )
    assert payload["experiment_proposals"]["proposal_count"] > 0
    assert (canonical.CANONICAL_DIR / "experiment_proposals.json").exists()
    assert "experiment_proposals_pointer" not in payload["discovery_map"]
    assert "experiment_proposal_count" not in payload["discovery_map"]
    assert "experiment_plan" not in payload
    assert "experiment_planner" not in payload
    assert "experiment_proposals" not in [report["name"] for report in payload["reports"]]
    assert "next_hypothesis" not in json.dumps(payload["discovery_map"], sort_keys=True)


def test_gap_head_transfer_atlas_index_matches_discovery_map_row(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        payload = _payload_for_spec(spec)
        if spec.name == "gap-head-transfer-atlas":
            payload["multi_surface_d5_o"] = {
                "decision": "pass",
                "discovery_level": "D5-O",
                "pass_surface_count": 3,
            }
        json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    discovery_payload = json.loads(
        (canonical.CANONICAL_DIR / "discovery_map.json").read_text(encoding="utf-8")
    )
    atlas_row = next(row for row in discovery_payload["rows"] if row["report"] == "gap-head-transfer-atlas")
    negative_reports = json.loads(
        (canonical.CANONICAL_DIR / "negative_discovery_reports.json").read_text(encoding="utf-8")
    )
    owner_index = int(
        atlas_row["negative_report_pointer"]
        .removeprefix("reports/canonical/negative_discovery_reports.json:$.rows[")
        .removesuffix("]")
    )
    atlas_owner = negative_reports["rows"][owner_index]
    verdicts = [
        json.loads(line)
        for line in (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    claim = next(row for row in verdicts if row["claim_id"] == "claim:gap-head-transfer-atlas")

    assert payload["gap_head_transfer_atlas"]["decision"] == "pass"
    assert payload["gap_head_transfer_atlas"]["discovery_level"] == atlas_row["discovery_level"]
    assert atlas_owner["terminal_verdict"] == "rejected"
    assert claim["claim_verdict"] == "negative_discovery"
    assert claim["negative_report_pointer"] == atlas_row["negative_report_pointer"]


def test_claim_verdicts_are_pointer_only_and_not_canonical_report_artifacts(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert payload["claim_verdicts"]["status"] == "pointer-only"
    assert payload["claim_verdicts"]["artifact_id"] == "bedc-quality-lab:claim-verdicts"
    assert payload["claim_verdicts"]["jsonl_artifact"] == "reports/canonical/claim_verdicts.jsonl"
    assert payload["claim_verdicts"]["jsonl_artifact"] not in json_artifacts
    assert (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").exists()
    assert "claim_verdicts.jsonl" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    assert payload["claim_graph"]["status"] == "pointer-only"
    assert payload["claim_graph"]["hardgate_status"]["CG-HG6"] == "pass"
    assert not (canonical.CANONICAL_DIR / "github-check.json").exists()
    assert not (canonical.CANONICAL_DIR / "github-check.md").exists()


def test_claim_verdict_writer_observes_current_scorecard_after_upstream_inputs(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    calls = []

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    def fake_formal_hardening(*, root, generated_at=None):
        calls.append("formal-hardening")
        path = root / canonical.FORMAL_HARDENING_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"ready": True, "recorded": 1, "required": 1, "gap_count": 0}, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (root / canonical.FORMAL_HARDENING_MARKDOWN_ARTIFACT).write_text("# formal\n", encoding="utf-8")
        return {"ready": True, "recorded": 1, "required": 1, "gap_count": 0}

    def fake_compile_discovery(*, root, generated_at=None, adapter=None):
        calls.append("discovery")
        path = root / canonical.DISCOVERY_MAP_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "generated_at": generated_at,
                    "row_count": 1,
                    "level_counts": {"D0": 1},
                    "rows": [
                        {
                            "report": "gap-head-discovery",
                            "json_artifact": "reports/canonical/gap-head-discovery.json",
                            "markdown_artifact": "reports/canonical/gap-head-discovery.md",
                            "discovery_level": "D0",
                            "terminal_verdict": "",
                            "classifier_reasons": [],
                            "projection_status": "projected",
                            "evidence_pointer": "$.positive_discovery",
                            "audit_status": "valid",
                            "audit_reason": "",
                            "evidence_type": "deterministic_projection",
                            "evidence_provenance_pointer": evidence_provenance_pointer_for_report("gap-head-discovery"),
                        }
                    ],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        (root / canonical.DISCOVERY_MAP_MARKDOWN_ARTIFACT).write_text("# discovery\n", encoding="utf-8")
        return {"discovery_map": {"row_count": 1}}

    def fake_transfer(*, root, generated_at=None, require_anti_triviality=False):
        calls.append("dimension-transfer")
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "dimension_mismatch_debt_transfer": {
                        "status": "pass",
                        "base_level": "D4",
                        "effective_level": "D4",
                        "discovery_level": "D4",
                        "terminal_verdict": "projected_discovery_required",
                        "scope": "fixture",
                    },
                    "control_protocol": {},
                    "not_claimed": [],
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        (root / canonical.DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT).write_text("# transfer\n", encoding="utf-8")
        return {}

    def fake_sidecar(*, root, generated_at=None):
        calls.append("dimension-sidecar")
        return {}

    def fake_claim_capsule(generated_at):
        return {
            "claim_id": "claim:dimension-mismatch-debt-transfer",
            "status": "complete",
            "effective_level": "D4",
            "terminal_verdict": "projected_discovery_required",
        }

    def fake_robustness(*, root, generated_at=None):
        calls.append("dimension-robustness")
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"status": "pass", "audit_status": "pass"}) + "\n", encoding="utf-8")
        (root / canonical.DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT).write_text("# robust\n", encoding="utf-8")
        return {}

    def fake_witness_summary(*, root, generated_at=None):
        calls.append("witness-summary")
        path = root / canonical.NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps({"status": "pointer-only", "row_count": 0, "audit_status": "pass", "rows": []}) + "\n",
            encoding="utf-8",
        )
        (root / canonical.NEGATIVE_WITNESS_SUMMARY_MARKDOWN_ARTIFACT).write_text("# witness\n", encoding="utf-8")
        return {"status": "pointer-only", "row_count": 0, "audit_status": "pass"}

    def fake_build_witness_summary(*, root, generated_at=None):
        return {"status": "pointer-only", "row_count": 0, "audit_status": "pass"}

    def fake_mutation_ledger(*, root, generated_at=None):
        calls.append("mutation-ledger")
        payload = {
            "schema_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID,
            "artifact_id": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID,
            "producer": "scripts/run_negative_witness_mutation_ledger.py",
            "generated_at": generated_at,
            "status": "ready",
            "entry_count": 0,
            "entries": [],
            "hardgates": {f"MUT-HG{index}": {"status": "pass"} for index in range(1, 6)},
            "forbidden_keys": [],
        }
        path = root / canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
        (root / canonical.MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT).write_text("# mutation graph\n", encoding="utf-8")
        (root / canonical.DGT_MUTATION_REPORT_ARTIFACT).write_text(
            json.dumps(
                {
                    "schema_id": "bedc-quality-lab:dgt-mutation-report",
                    "ledger": {"artifact": canonical.NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT, "pointer": "$.entries"},
                    "graph": {"artifact": canonical.MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT, "pointer": "$"},
                    "status": "ready",
                    "entry_count": 0,
                    "blocked_count": 0,
                    "mut_hg_summary": {f"MUT-HG{index}": "pass" for index in range(1, 6)},
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        return payload

    def fake_release(*, root, generated_at=None):
        path = root / canonical.RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {
                    "schema_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                    "artifact_id": canonical.RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID,
                    "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
                    "generated_at": generated_at,
                    "version": "0.0.1",
                    "tag_ref": None,
                    "release_bundle_status": "ready",
                    "tag_status": "absent",
                    "source_pointers": {},
                    "required_pointers": [
                        {
                            "id": "fixture-pointer",
                            "path": "reports/canonical/index.json",
                            "pointer": "$.schema_id",
                            "status": "resolved",
                            "failure": None,
                        }
                    ],
                    "not_claimed": ["fixture boundary"],
                    "revoke_if": "Revoke if fixture pointer stops resolving.",
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        (root / canonical.RELEASE_MANIFEST_SIDECAR_MARKDOWN_ARTIFACT).write_text("# release sidecar\n", encoding="utf-8")
        return {}

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: {"ready": True, "recorded": 1, "required": 1, "gap_count": 0})
    monkeypatch.setattr(canonical, "_build_claim_capsule", fake_claim_capsule)
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_formal_hardening_report",
        types.SimpleNamespace(write_formal_hardening_report=fake_formal_hardening),
    )
    monkeypatch.setitem(
        sys.modules,
        "bedc_quality_lab.discovery_compiler.compiler",
        types.SimpleNamespace(compile_discovery=fake_compile_discovery),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_debt_transfer",
        types.SimpleNamespace(write_dimension_mismatch_debt_transfer=fake_transfer),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_anti_triviality",
        types.SimpleNamespace(write_dimension_mismatch_anti_triviality=fake_sidecar),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_transfer_robustness",
        types.SimpleNamespace(write_dimension_mismatch_transfer_robustness=fake_robustness),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_discovery_negative_witness_summary",
        types.SimpleNamespace(
            write_discovery_negative_witness_summary=fake_witness_summary,
            build_discovery_negative_witness_summary=fake_build_witness_summary,
        ),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_negative_witness_mutation_ledger",
        types.SimpleNamespace(write_negative_witness_mutation_ledger=fake_mutation_ledger),
    )
    monkeypatch.setitem(
        sys.modules,
        "scripts.release_manifest_sidecar",
        types.SimpleNamespace(write_release_manifest_sidecar=fake_release),
    )

    payload = canonical.run_reports(only="gap-head-discovery", generated_at="2030-01-01T00:00:00+00:00")
    rows = [
        json.loads(line)
        for line in (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line
    ]
    scorecard_hash = claim_verdict_demo.load_scorecard_snapshot(tmp_path).scorecard_hash

    assert calls.index("formal-hardening") < calls.index("discovery") < calls.index("witness-summary")
    assert rows
    assert all(row["scorecard_hash"] == scorecard_hash for row in rows)
    assert all(row["formal_hardening_ready"] is True for row in rows)
    assert payload["claim_verdicts"]["row_count"] == len(rows)


def test_committed_canonical_bundle_matches_registered_reports():
    from scripts import run_claim_verdict_demo as claim_verdicts
    from scripts import run_discovery_map as discovery_map

    canonical_dir = canonical.ROOT / "reports" / "canonical"
    discovery_payload = json.loads((canonical_dir / "discovery_map.json").read_text(encoding="utf-8"))
    claim_rows = [
        json.loads(line)
        for line in (canonical_dir / "claim_verdicts.jsonl").read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    index_payload = json.loads((canonical_dir / "index.json").read_text(encoding="utf-8"))
    spec_names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    discovery_spec_names = {spec.name for spec in canonical._discovery_map_reports()}

    assert {row["report"] for row in discovery_payload["rows"]}.issuperset(discovery_spec_names)
    assert {row["claim_id"].removeprefix("claim:") for row in claim_rows if row["claim_id"].startswith("claim:")}.issuperset(discovery_spec_names)
    assert {row["name"] for row in index_payload["reports"]} == spec_names

    regenerated_discovery = discovery_map.build_discovery_map(
        generated_at=discovery_payload["generated_at"],
        root=canonical.ROOT,
        canonical_reports=canonical._discovery_map_reports(),
    )
    regenerated_claim_rows = claim_verdicts.compile_claim_verdicts(
        canonical.ROOT,
        generated_at=discovery_payload["generated_at"],
    )
    regenerated_index = canonical._index(
        index_payload["reports"],
        generated_at=index_payload["generated_at"],
        claim_verdict_rows=regenerated_claim_rows,
    )

    assert discovery_payload == regenerated_discovery
    _assert_dgt_discovery_map_row_uses_l0_consumption(
        next(row for row in discovery_payload["rows"] if row["report"] == "discovery-gated-transformer")
    )
    assert claim_rows == regenerated_claim_rows
    assert index_payload == regenerated_index


def test_canonical_dgt_report_exposes_jet_certificate_pointer_only():
    spec = canonical._specs_by_name()["discovery-gated-transformer"]
    payload = _payload_for_spec(spec)

    assert "dgt-boundary-causal-jet" not in {item.name for item in canonical.CANONICAL_REPORTS}
    for key in (
        "schema_id",
        "artifact_id",
        "source_artifacts",
        "jet_certificate_ref",
        "hardgate_ref",
        "not_claimed",
        "forbidden_claim_term_audit",
        "revocation_rows",
        "discovery_map_signal_ref",
        "d4_projection",
    ):
        assert key in payload
    assert payload["jet_certificate_ref"] == {
        "artifact": "reports/runs/discovery-gated-transformer/jet_certificate.json",
        "pointer": "$",
    }
    serialized = json.dumps(payload, sort_keys=True)
    assert "surface_rows" not in serialized
    assert "matched_random_gain" not in serialized


def test_dgt_canonical_index_uses_artifact_qualified_jet_pointers():
    payload = canonical._index([], generated_at="fixture-generated-at")
    section = payload["discovery-gated-transformer"]

    assert section["jet_certificate_pointer"] == "reports/runs/discovery-gated-transformer/jet_certificate.json:$"
    assert section["jet_hardgate_pointer"] == "reports/runs/discovery-gated-transformer/jet_certificate.json:$.hardgate"
    assert section["hardgate_pointer"] == "reports/canonical/discovery-gated-transformer.json:$.hardgate"
    assert section["discovery_map_signal_ref_pointer"] == (
        "reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal_ref"
    )
    assert section["d4_projection_pointer"] == "reports/canonical/discovery-gated-transformer.json:$.d4_projection"
    serialized = json.dumps(section, sort_keys=True)
    assert "surface_rows" not in serialized
    assert "matched_random_gain" not in serialized
    assert "dgt-boundary-causal-jet" not in serialized


def test_claim_capsule_is_generated_and_not_canonical_report_artifact(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)
    _write_dimension_mismatch_gap_witness_fixture(tmp_path)

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    def write_transfer(*, root, generated_at=None, require_anti_triviality=True):
        path = root / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {
            "control_protocol": {"control_arm": "matched_random_gap_head"},
            "dimension_mismatch_debt_transfer": {
                "status": "pass",
                "base_level": "D4",
                "anti_triviality_status": "scale_leakage_detected" if require_anti_triviality else None,
                "effective_level": "DN" if require_anti_triviality else "D4",
                "downgrade_reason": "scale_only_or_metadata_proxy_sufficient" if require_anti_triviality else None,
                "terminal_verdict": "negative_discovery" if require_anti_triviality else "source_pass",
                "hypothesis": "fixture hypothesis",
                "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status" if require_anti_triviality else None,
                "what_was_learned": "fixture learned",
            },
            "hardgate_evidence": {
                "HG-B3": {
                    "learned_auroc": {
                        "ci95_half_width": 0.01,
                        "ci95_high": 0.83,
                        "ci95_low": 0.81,
                        "mean": 0.82,
                        "n": 10,
                        "std": 0.01,
                    },
                    "matched_random_auroc": {
                        "ci95_half_width": 0.01,
                        "ci95_high": 0.49,
                        "ci95_low": 0.42,
                        "mean": 0.46,
                        "n": 10,
                        "std": 0.01,
                    },
                    "matched_random_positive": False,
                    "status": "pass",
                }
            },
            "not_claimed": ["fixture boundary"],
        }
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return payload

    def write_sidecar(*, root, generated_at=None):
        path = root / "reports/dimension_mismatch_anti_triviality.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {"status": "scale_leakage_detected", "recommended_projection": "demote_to_DN_or_D1"}
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return payload

    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_debt_transfer",
            types.SimpleNamespace(
                JSON_ARTIFACT=canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
                REPORT_ARTIFACT=canonical.DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT,
                SCALE_LEAKAGE_WITNESS_POINTER=(
                    "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:"
                    "$.run_local.negative_witness[0]"
                ),
                NEGATIVE_WITNESS_TEST_POINTER="$.run_local.test_artifact.regression_tests.scale_leakage_witness",
                scale_leakage_bedc_gap_mapping=lambda root: {
                    "witness_pointer": (
                        "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:"
                        "$.run_local.negative_witness[0]"
                    ),
                    "bedc_gap_field": "representation_scale_leakage",
                    "demotion_rule": "demote_to_DN_or_D1",
                    "regression_test": "$.run_local.test_artifact.regression_tests.scale_leakage_witness",
                },
                write_dimension_mismatch_debt_transfer=write_transfer,
            ),
        )
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_dimension_mismatch_anti_triviality",
        types.SimpleNamespace(write_dimension_mismatch_anti_triviality=write_sidecar),
    )

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    capsule_path = canonical.CANONICAL_DIR / "claim_capsule.json"
    capsule = json.loads(capsule_path.read_text(encoding="utf-8"))
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert payload["claim_capsule"]["json_artifact"] == "reports/canonical/claim_capsule.json"
    assert payload["claim_capsule"]["capsule_status"] == "complete"
    assert "reports/canonical/claim_capsule.json" not in json_artifacts
    assert capsule["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule["status"] == "complete"
    assert capsule["effective_level"] == "DN"
    assert capsule["downgrade_reason"] == "scale_only_or_metadata_proxy_sufficient"
    assert {
        "global dimension theory",
        "representation-geometric debt transfer",
        "D5 promotion",
        "global model quality",
        "full LeJEPA",
        "full TensorNameCert",
        "LLM behavior",
        "mechanism closure unless D5-M",
    }.issubset(set(capsule["not_claimed"]))


def test_claim_capsule_missing_source_node_is_incomplete_not_synthetic_dn(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    capsule = canonical._build_claim_capsule("fixture-time")

    assert capsule["status"] == "incomplete"
    assert capsule["reason"] == "source claim node is missing"
    assert "effective_level" not in capsule
    assert "terminal_verdict" not in capsule


def test_claim_capsule_missing_required_cells_is_incomplete_not_synthetic_dn(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    path = tmp_path / canonical.DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"dimension_mismatch_debt_transfer": {"base_level": "D4"}}) + "\n", encoding="utf-8")

    capsule = canonical._build_claim_capsule("fixture-time")

    assert capsule["status"] == "incomplete"
    assert "effective_level" in capsule["missing_cells"]
    assert "terminal_verdict" in capsule["missing_cells"]


def test_canonical_claim_capsule_includes_dimension_mismatch_run_local_contract():
    capsule = canonical._build_claim_capsule("fixture-time")
    run_local = capsule["run_local"]

    assert capsule["json_artifact"] == "reports/canonical/claim_capsule.json"
    assert run_local["owner"] == "claim:dimension-mismatch-debt-transfer"
    assert run_local["artifact_bundle"] == {
        "claim_capsule": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json",
        "raw_metrics": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/raw_metrics.jsonl",
        "summary": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/summary.json",
        "report": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/report.md",
    }
    b2_refs = [row for row in run_local["evidence_refs"] if str(row.get("evidence_id", "")).startswith("B2-HG")]
    sidecar = json.loads((canonical.ROOT / "reports/dimension_mismatch_anti_triviality.json").read_text(encoding="utf-8"))
    assert [row["evidence_id"] for row in b2_refs] == list(sidecar["controlled_geometry_hardgates"])
    for row in b2_refs:
        source = json.loads((canonical.ROOT / row["source_artifact"]).read_text(encoding="utf-8"))
        assert pointer_value(source, row["source_pointer"]) is not None


def test_canonical_claim_capsule_points_to_negative_witness_owner():
    capsule = canonical._build_claim_capsule("fixture-time")
    run_local = capsule["run_local"]
    owner_ref = {
        "artifact": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json",
        "pointer": "$.run_local.negative_witness",
    }
    hardgate_ref = {
        "artifact": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json",
        "pointer": "$.run_local.negative_witness_hardgates",
    }
    owner = json.loads((canonical.ROOT / owner_ref["artifact"]).read_text(encoding="utf-8"))

    assert run_local["negative_witness"] == owner_ref
    assert run_local["negative_witness_hardgates"] == hardgate_ref
    assert pointer_value(owner, owner_ref["pointer"]) is not None
    assert pointer_value(owner, hardgate_ref["pointer"]) is not None
    assert isinstance(pointer_value(owner, owner_ref["pointer"]), list)
    assert isinstance(pointer_value(owner, hardgate_ref["pointer"]), dict)


def test_quality_scorecard_projects_only_explicit_cells(tmp_path, monkeypatch):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        monkeypatch.setattr(
            canonical,
            "_build_formal_hardening_payload",
            lambda generated_at=None: formal_hardening.build_formal_hardening_report(
                root=formal_hardening.ROOT,
                generated_at=generated_at,
            ),
        )
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    expected = {
        "CertCov": {
            "value": pytest.approx(2 / 3),
            "source": {
                "report": "mixing-family-sweep",
                "artifact": "reports/canonical/mixing-family-sweep.json",
                "pointer": "$.coverage_item",
            },
            "numerator": 2,
            "denominator": 3,
        },
        "DebtQ": {
            "value": pytest.approx(0.125),
            "source": {
                "report": "mixing-family-sweep",
                "artifact": "reports/canonical/mixing-family-sweep.json",
                "pointer": "$.coverage_item.debt_item.score",
            },
        },
        "CriticalDebt": {
            "value": 0.25,
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.debt_terms",
            },
        },
        "LedgerCompleteness": {
            "value": pytest.approx(3 / 4),
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.classifier_state",
            },
            "numerator": 3,
            "denominator": 4,
        },
        "ClassifierShiftCount": {
            "value": 2,
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.surface_delta_count",
            },
        },
        "PositiveDiscoveryCount": {
            "value": 1,
            "source": [
                {
                    "report": "gap-head-discovery",
                    "artifact": "reports/canonical/gap-head-discovery.json",
                    "pointer": "$.positive_discovery",
                },
                {
                    "report": "certificate-guided-discovery",
                    "artifact": "reports/canonical/certificate-guided-discovery.json",
                    "pointer": "$.positive_discovery",
                },
            ],
            "numerator": 1,
            "denominator": 2,
        },
        "AuditImprovementCount": {
            "value": 1,
            "source": {
                "report": "certificate-guided-training",
                "artifact": "reports/canonical/certificate-guided-training.json",
                "pointer": "$.claim_gate.audit_improvement_tradeoff",
            },
            "numerator": 1,
            "denominator": 1,
        },
        "NegativeResultCount": {
            "value": 5,
            "source": [
                {
                    "report": "mixing-family-sweep",
                    "artifact": "reports/canonical/mixing-family-sweep.json",
                    "pointer": "$.negative_result_summary.cells",
                },
                {
                    "report": "anisotropic-ou-sweep",
                    "artifact": "reports/canonical/anisotropic-ou-sweep.json",
                    "pointer": "$.negative_result_summary.cells",
                },
                {
                    "report": "nongaussian-distribution-sweep",
                    "artifact": "reports/canonical/nongaussian-distribution-sweep.json",
                    "pointer": "$.negative_result_ledger",
                },
            ],
        },
        "ScopeCompleteness": {
            "value": 1.0,
            "source": [
                {
                    "report": spec.name,
                    "artifact": spec.json_artifact,
                    "pointer": spec.scope_pointer,
                }
                for spec in canonical._scorecard_report_specs()
            ],
            "numerator": len(canonical._scorecard_report_specs()),
            "denominator": len(canonical._scorecard_report_specs()),
        },
        "CostProtocolCompleteness": {
            "value": 1.0,
            "source": [
                {
                    "report": spec.name,
                    "artifact": spec.json_artifact,
                    "pointer": spec.cost_pointer,
                }
                for spec in canonical._scorecard_report_specs()
            ],
            "numerator": len(canonical._scorecard_report_specs()),
            "denominator": len(canonical._scorecard_report_specs()),
        },
        "HardeningCoverage": {
            "value": 1.0,
            "source": {
                "report": "formal_hardening",
                "artifact": "reports/canonical/formal_hardening.json",
                "pointer": "$.coverage",
            },
            "numerator": 4,
            "denominator": 4,
        },
        "OverclaimRate": {
            "value": pytest.approx(0.4),
            "source": {
                "report": "certificate-guided-discovery",
                "artifact": "reports/canonical/certificate-guided-discovery.json",
                "pointer": "$.audit_decision.overclaim_rate",
            },
        },
    }

    by_metric = {row["metric"]: row for row in payload["rows"]}
    for metric, fields in expected.items():
        row = by_metric[metric]
        assert row["status"] == fields.get("status", "ready")
        if row["status"] == "not-ready":
            assert row["dependency"] == fields["dependency"]
            assert row["reason"] == fields["reason"]
            continue
        assert row["value"] == fields["value"]
        assert row["source"] == fields["source"]
        if "numerator" in fields:
            assert row["numerator"] == fields["numerator"]
        if "denominator" in fields:
            assert row["denominator"] == fields["denominator"]


def test_positive_discovery_count_is_limited_to_discovery_producers(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["PositiveDiscoveryCount"]
    assert row["status"] == "ready"
    assert row["denominator"] == 2
    assert row["source"] == [
        {
            "report": "gap-head-discovery",
            "artifact": "reports/canonical/gap-head-discovery.json",
            "pointer": "$.positive_discovery",
        },
        {
            "report": "certificate-guided-discovery",
            "artifact": "reports/canonical/certificate-guided-discovery.json",
            "pointer": "$.positive_discovery",
        },
    ]


def test_attribution_capsule_d5_cells_project_minimal_two_axis_discovery_map_row(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        spec = canonical._specs_by_name()["gap-head-attribution-capsule"]
        _mutate_payload(
            canonical,
            "gap-head-attribution-capsule",
            lambda payload: payload.update(
                {
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
                    "ledger_debt": [{"debt_id": "gap-head-mechanism-evidence-closure", "status": "open"}],
                    "not_implemented": ["nonlinear_residualization", "full_causal_replacement_scope"],
                    "source_issues": [692, 747],
                    "a4_hardgates": {"gates": {"A4-HG2": {"status": "pass"}, "A4-HG3": {"status": "pass"}, "A4-HG5": {"status": "fail"}}},
                    "residualized_attribution": {"status": "pass"},
                    "score_margin_causal_evidence": {"channel_classification": "score_margin_sufficient"},
                }
            ),
        )

        payload = discovery_map.build_discovery_map(
            generated_at="fixture-time",
            root=tmp_path,
            canonical_reports=canonical.CANONICAL_REPORTS,
        )
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
    row = {item["report"]: item for item in payload["rows"]}[spec.name]

    assert row["discovery_level"] == "D1"
    assert row["classifier_reasons"]
    assert row["projection_status"] == "two-axis-recorded"
    assert row["evidence_pointer"] == "$.mechanism_evidence"
    assert row["base_level"] == "D5-O"
    assert row["base_status"] == "ready"
    assert row["mechanism_level"] == "blocked"
    assert row["mechanism_status"] == "blocked"
    assert row["mechanism_channel"] == "probe-margin-channel"
    assert row["mechanism_failed_gate"] == "A1-HG3"
    assert row["operational_pointer"] == "$.d5_o"
    assert row["mechanism_pointer"] == "$.mechanism_evidence"
    assert row["mechanism_case_pointer"] == "$.mechanism_evidence.candidate_mechanism"
    assert row["mechanism_namecert_pointer"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert row["mechanism_ledger_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status"
    assert row["mechanism_closure_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence.mechanism_status"
    assert row["audit_status"] == "invalid"


def test_attribution_capsule_sidecar_and_discovery_map_levels_are_consistent():
    capsule = json.loads((canonical.ROOT / "reports/canonical/gap_head_attribution_capsule.json").read_text(encoding="utf-8"))
    discovery = json.loads((canonical.ROOT / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    index = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()

    row = {item["report"]: item for item in discovery["rows"]}["gap-head-attribution-capsule"]
    index_row = {item["name"]: item for item in index["reports"]}["gap-head-attribution-capsule"]
    claim_row = {item["claim_id"]: item for item in claim_rows}["claim:gap-head-attribution-capsule"]
    row_index = next(
        index
        for index, item in enumerate(discovery["rows"])
        if item["report"] == "gap-head-attribution-capsule"
    )

    assert index_row["json_artifact"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert row["json_artifact"] == index_row["json_artifact"]
    assert claim_row["ledger_pointer"] == f"reports/canonical/discovery_map.json:$.rows[{row_index}].discovery_level"
    assert claim_row["source"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence"
    assert capsule["d5_o"]["status"] == "blocked"
    assert capsule["d5_o"]["failed_checks"] == ["ablation"]
    assert "base_status" not in row
    assert "base_level" not in row
    assert capsule["mechanism_evidence"]["base_status"] == "blocked"
    assert capsule["mechanism_evidence"]["base_level"] == "blocked"
    assert capsule["ledger_debt"][0]["status"] == "open"
    assert index["gap_head_attribution_capsule"]["mechanism_evidence_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence"
    assert index["gap_head_attribution_capsule"]["mechanism_ledger_debt_pointer"] == "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status"
    assert "gap_head_mechanism_namecert" not in index
    assert "mechanism_status" not in row
    assert "mechanism_level" not in row
    assert capsule["mechanism_evidence"]["failed_gate"]
    assert "$.a4_hardgates.gates.A4-HG5.status" in capsule["mechanism_evidence"]["required_gate_pointers"]
    assert capsule["mechanism_evidence"]["mechanism_status"] == "blocked"
    assert capsule["mechanism_evidence"]["candidate_mechanism"]
    assert "mechanism_channel" not in row
    assert "mechanism_ledger_pointer" not in row
    assert "mechanism_closure_pointer" not in row


def test_gap_head_mechanism_blockage_negative_owner_absent_when_base_readiness_blocked():
    negative_reports = json.loads((canonical.ROOT / "reports/canonical/negative_discovery_reports.json").read_text(encoding="utf-8"))
    discovery = json.loads((canonical.ROOT / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    claim_rows = _read_committed_claim_verdicts()
    claim_graph = json.loads((canonical.ROOT / "reports/canonical/claim_graph.json").read_text(encoding="utf-8"))
    capsule = json.loads((canonical.ROOT / "reports/canonical/gap_head_attribution_capsule.json").read_text(encoding="utf-8"))

    assert capsule["d5_o"]["status"] == "blocked"
    assert "gap-head-mechanism-blockage" not in {row["report_id"] for row in negative_reports["rows"]}
    assert "gap-head-mechanism-blockage" not in {row["report"] for row in discovery["rows"]}
    assert "claim:gap-head-mechanism-blockage" not in {row["claim_id"] for row in claim_rows}
    assert not any("gap-head-mechanism-blockage" in row["node_id"] for row in claim_graph["nodes"])


def test_attribution_capsule_remains_non_terminal_verdict_producer():
    capsule = json.loads((canonical.ROOT / "reports/canonical/gap_head_attribution_capsule.json").read_text(encoding="utf-8"))
    discovery = json.loads((canonical.ROOT / "reports/canonical/discovery_map.json").read_text(encoding="utf-8"))
    rows = {row["report"]: row for row in discovery["rows"]}

    assert "terminal_verdict" not in capsule
    assert rows["gap-head-attribution-capsule"]["discovery_level"] == "D0"
    assert rows["gap-head-attribution-capsule"]["terminal_verdict"] == ""
    assert "gap-head-mechanism-blockage" not in rows


def test_quality_scorecard_fails_closed_without_source_or_denominator(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    cases = [
        (
            "CertCov",
            "mixing-family-sweep:$.coverage_item",
            lambda: _mutate_payload(
                canonical,
                "mixing-family-sweep",
                lambda payload: payload["coverage_item"].pop("canonical_families"),
            ),
        ),
        (
            "PositiveDiscoveryCount",
            "canonical discovery positive flags",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-discovery",
                lambda payload: payload.update({"positive_discovery": "yes"}),
            ),
        ),
        (
            "NegativeResultCount",
            "canonical negative-result cells",
            lambda: _mutate_payload(
                canonical,
                "anisotropic-ou-sweep",
                lambda payload: payload.update({"negative_result_summary": {"cells": "none"}}),
            ),
        ),
        (
            "ScopeCompleteness",
            "certificate-guided-training:$.objective.required_rows",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-training",
                lambda payload: payload["objective"].pop("required_rows"),
            ),
        ),
        (
            "OverclaimRate",
            "certificate-guided-discovery:$.audit_decision.overclaim_rate",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-discovery",
                lambda payload: payload["audit_decision"].pop("overclaim_rate"),
            ),
        ),
    ]

    try:
        for metric, dependency, break_payload in cases:
            _write_payloads_for_all_specs(canonical, tmp_path)
            break_payload()
            scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
            row = {item["metric"]: item for item in scorecard["rows"]}[metric]
            assert row["status"] == "not-ready"
            assert row["dependency"] == dependency
            assert "value" not in row
            assert "numerator" not in row
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index


def test_quality_scorecard_hardening_coverage_uses_current_formal_payload(tmp_path, monkeypatch):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        monkeypatch.setattr(
            canonical,
            "_build_formal_hardening_payload",
            lambda generated_at=None: formal_hardening.build_formal_hardening_report(
                root=formal_hardening.ROOT,
                generated_at=generated_at,
            ),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["HardeningCoverage"]
    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == 4
    assert row["denominator"] == 4
    assert row["source"] == {
        "report": "formal_hardening",
        "artifact": "reports/canonical/formal_hardening.json",
        "pointer": "$.coverage",
    }


def test_quality_scorecard_hardening_coverage_ready_iff_all_rows_verified(monkeypatch):
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded"
    verified_rows = []
    for row in payload["verification_ledger"]:
        ready_row = dict(row)
        ready_row["status"] = "verified"
        ready_row["recorded"] = True
        ready_row["evidence_resolved"] = True
        ready_row["evidence_pointer"] = ready_row["evidence_pointer"] or evidence_pointer
        ready_row["gap"] = None
        verified_rows.append(ready_row)
    payload.update(
        {
            "ready": True,
            "status": "ready",
            "recorded": len(verified_rows),
            "required": len(verified_rows),
            "gap_count": 0,
            "verification_ledger": verified_rows,
            "coverage": {
                "ready": True,
                "recorded": len(verified_rows),
                "required": len(verified_rows),
                "gap_count": 0,
                "gap_rows": [],
            },
        }
    )
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == len(verified_rows)
    assert row["denominator"] == len(verified_rows)
    assert row["source"] == {
        "report": "formal_hardening",
        "artifact": "reports/canonical/formal_hardening.json",
        "pointer": "$.coverage",
    }


def test_quality_scorecard_hardening_coverage_reads_payload_not_lean_file(monkeypatch, tmp_path):
    payload = {
        "ready": True,
        "status": "ready",
        "recorded": 1,
        "required": 1,
        "verification_ledger": [
            {
                "status": "verified",
                "recorded": True,
                "evidence_resolved": True,
            }
        ],
        "coverage": {"ready": True, "recorded": 1, "required": 1, "gap_count": 0, "gap_rows": []},
    }
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == 1
    assert row["denominator"] == 1


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"ready": False}),
        lambda payload: payload["verification_ledger"][0].update({"status": "missing"}),
        lambda payload: payload["verification_ledger"][0].update({"recorded": False}),
        lambda payload: payload["verification_ledger"][0].update({"evidence_resolved": False}),
        lambda payload: payload["coverage"].update({"recorded": payload["coverage"]["required"] - 1}),
    ],
)
def test_quality_scorecard_hardening_coverage_fails_closed_for_any_unverified_cell(monkeypatch, mutate):
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded"
    rows = []
    for row in payload["verification_ledger"]:
        ready_row = dict(row)
        ready_row["status"] = "verified"
        ready_row["recorded"] = True
        ready_row["evidence_resolved"] = True
        ready_row["evidence_pointer"] = ready_row["evidence_pointer"] or evidence_pointer
        rows.append(ready_row)
    payload.update(
        {
            "ready": True,
            "recorded": len(rows),
            "required": len(rows),
            "verification_ledger": rows,
            "coverage": {"recorded": len(rows), "required": len(rows), "ready": True, "gap_count": 0},
        }
    )
    mutate(payload)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "not-ready"
    assert row["dependency"] == "formal_hardening:$.coverage"


@pytest.mark.parametrize(
    "evidence_pointer",
    [
        "reports/canonical/spectral-ablation-hinge.json:$.does_not_exist",
        "reports/canonical/formal_hardening.json:$.verification_ledger",
        "reports/canonical/missing-artifact.json:$.recorded",
    ],
)
def test_quality_scorecard_hardening_coverage_fails_closed_for_unresolved_pointer(monkeypatch, evidence_pointer):
    item = formal_hardening._HardeningItem(
        item_id="unresolved-pointer",
        name="unresolved pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "unresolved-pointer"),
        source_pointer=evidence_pointer,
        evidence_pointer=evidence_pointer,
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    scorecard_row = canonical._scorecard_hardening_coverage({})
    ledger_row = payload["verification_ledger"][0]

    assert ledger_row["status"] == "missing"
    assert ledger_row["recorded"] is False
    assert ledger_row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert scorecard_row["status"] == "not-ready"
    assert scorecard_row["dependency"] == "formal_hardening:$.coverage"


def test_quality_scorecard_hardening_coverage_falsy_resolved_value_stays_not_ready(monkeypatch):
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2].recorded"
    item = formal_hardening._HardeningItem(
        item_id="falsy-pointer",
        name="falsy pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "falsy-pointer"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2]",
        evidence_pointer=evidence_pointer,
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    scorecard_row = canonical._scorecard_hardening_coverage({})
    ledger_row = payload["verification_ledger"][0]

    assert ledger_row["status"] == "missing"
    assert ledger_row["recorded"] is False
    assert ledger_row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert scorecard_row["status"] == "not-ready"
    assert scorecard_row["dependency"] == "formal_hardening:$.coverage"


def test_quality_scorecard_cost_protocol_completeness_fails_closed_without_manifest_pointer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        _mutate_payload(
            canonical,
            "gap-head-discovery",
            lambda payload: payload.pop("score_terms"),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["CostProtocolCompleteness"]
    assert row["status"] == "not-ready"
    assert row["dependency"] == "gap-head-discovery:$.score_terms"
    assert "value" not in row
    assert "numerator" not in row


def test_quality_scorecard_cost_protocol_completeness_fails_closed_for_dangling_indirect_pointer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        _mutate_payload(
            canonical,
            "gap-head-attribution-capsule",
            lambda payload: payload.update({"cost_protocol_pointer": "$.source_artifacts.missing_cost_protocol"}),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["CostProtocolCompleteness"]
    assert row["status"] == "not-ready"
    assert row["dependency"] == "gap-head-attribution-capsule:$.cost_protocol_pointer"
    assert "value" not in row
    assert "numerator" not in row


def test_quality_scorecard_excludes_report_schema_fields(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert "report_schema_id" not in set(_walk_keys(payload))
    assert "report_kind" not in set(_walk_keys(payload))


def test_quality_scorecard_uses_caller_timestamp(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _drop_dgt_l0_from_manifest(monkeypatch)
    _write_release_pointer_fixture(tmp_path)

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    scorecard = json.loads((canonical.CANONICAL_DIR / "quality-scorecard.json").read_text(encoding="utf-8"))

    assert payload["generated_at"] == "2030-01-01T00:00:00+00:00"
    assert scorecard["generated_at"] == "2030-01-01T00:00:00+00:00"


def test_quality_scorecard_has_no_weighted_total(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
        markdown = canonical._render_quality_scorecard_markdown(payload)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    keys = set(_walk_keys(payload))
    assert "weighted_total" not in keys
    assert "total_score" not in keys
    assert "grade" not in keys
    assert "weight" not in keys
    assert "weighted" not in json.dumps(payload).lower()
    assert "weighted" not in markdown.lower()


def test_quality_scorecard_markdown_contains_baseline_pointers(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
        markdown = canonical._render_quality_scorecard_markdown(payload)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert "Quality baseline pointers" in markdown
    assert "docs/bedc_quality_lab_alpha_milestone.md" in markdown
    assert "reports/canonical/discovery_map.json:$.rows[*].discovery_level" in markdown


def test_run_spec_producer_exception_fails_closed_even_with_valid_stale_artifact(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["gap-head-on-h"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    def broken_producer(_spec):
        raise RuntimeError("producer stopped")

    monkeypatch.setattr(canonical, "_run_producer", broken_producer)

    result = canonical._run_spec(spec)

    assert result["status"] == "error"
    assert result["status"] != "pass"
    assert result["producer_status"] == "error"
    assert result["validation"]["status"] == "pass"
    assert result["validation"]["required_key_validation"]["status"] == "pass"
    assert result["error"] == "producer stopped"


def test_run_reports_certificate_guided_discovery_uses_canonical_training_source(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    source_json = canonical.CANONICAL_DIR / "certificate-guided-training.json"
    source_report = canonical.CANONICAL_DIR / "certificate-guided-training.md"
    source_json.parent.mkdir(parents=True, exist_ok=True)
    source_json.write_text(json.dumps({"training_marker": "canonical-source"}), encoding="utf-8")
    source_report.write_text("# canonical training\n", encoding="utf-8")
    observed = []

    class StubDiscoveryProducer:
        REPORT_JSON = None
        REPORT_MD = None
        JSON_ARTIFACT = "reports/certificate_guided_discovery.json"
        REPORT_ARTIFACT = "reports/certificate_guided_discovery.md"
        SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
        SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
        USE_TORCH = True

        @classmethod
        def main(cls):
            assert cls.JSON_ARTIFACT == "reports/canonical/certificate-guided-discovery.json"
            assert cls.REPORT_ARTIFACT == "reports/canonical/certificate-guided-discovery.md"
            assert cls.SOURCE_JSON_ARTIFACT == "reports/canonical/certificate-guided-training.json"
            assert cls.SOURCE_REPORT_ARTIFACT == "reports/canonical/certificate-guided-training.md"
            assert cls.USE_TORCH is False
            source_payload = json.loads((canonical.ROOT / cls.SOURCE_JSON_ARTIFACT).read_text(encoding="utf-8"))
            observed.append(source_payload["training_marker"])
            payload = {
                "generated_at": "fixture",
                "source_artifacts": {
                    "source_json_artifact": cls.SOURCE_JSON_ARTIFACT,
                    "source_report_artifact": cls.SOURCE_REPORT_ARTIFACT,
                },
                "verdicts": [{"verdict": "positive"}],
                "positive_discovery": True,
                "net_information": 1.25,
                    "matched_random_baseline": {"verdict": "negative"},
                    "claim_gate": {"positive_discovery_four_gate": True},
                    "hardgate": {"status": "pass"},
                    "failed_gate": None,
                    "verdict": "positive-discovery",
                    "discovery_level": "D4",
                    "revocation_decision": {"downgraded": False},
                "revocation_ledger": [],
                "not_claimed": ["fixture boundary"],
                "main_claim_status": "positive",
            }
            cls.REPORT_JSON.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
            cls.REPORT_MD.write_text("# stub discovery\n", encoding="utf-8")

    real_import_module = canonical.importlib.import_module

    def fake_import_module(module_name):
        if module_name == "scripts.run_certificate_guided_discovery":
            return StubDiscoveryProducer
        return real_import_module(module_name)

    monkeypatch.setattr(canonical.importlib, "import_module", fake_import_module)

    payload = canonical.run_reports(only="certificate-guided-discovery")
    report_payload = json.loads((canonical.CANONICAL_DIR / "certificate-guided-discovery.json").read_text(encoding="utf-8"))
    report_markdown = (canonical.CANONICAL_DIR / "certificate-guided-discovery.md").read_text(encoding="utf-8")

    assert observed == ["canonical-source"]
    assert payload["reports"][0]["name"] == "certificate-guided-discovery"
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert report_payload["source_artifacts"]["source_json_artifact"] == "reports/canonical/certificate-guided-training.json"
    assert report_payload["source_artifacts"]["source_report_artifact"] == "reports/canonical/certificate-guided-training.md"
    assert report_payload["positive_discovery"] is True
    assert report_payload["net_information"] == pytest.approx(1.25)
    assert report_payload["matched_random_baseline"] == {"verdict": "negative"}
    assert report_payload["claim_gate"] == {"positive_discovery_four_gate": True}
    assert report_payload["revocation_decision"] == {"downgraded": False}
    assert report_payload["revocation_ledger"] == []
    assert report_payload["not_claimed"] == ["fixture boundary"]
    assert report_payload["main_claim_status"] == "positive"
    assert report_markdown == "# stub discovery\n"


def test_certificate_guided_discovery_missing_control_commits_skipped_not_error(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    source_json = canonical.CANONICAL_DIR / "certificate-guided-training.json"
    source_report = canonical.CANONICAL_DIR / "certificate-guided-training.md"
    source_json.parent.mkdir(parents=True, exist_ok=True)
    source_json.write_text(
        json.dumps(
            {
                "generated_at": "fixture",
                "source_artifacts": {"generation_script": "scripts/run_certificate_guided_training.py"},
                "hardgate": {"status": "fail", "failed_gate": "fixture-missing-control"},
                "failed_gate": "fixture-missing-control",
                "scope_seal": {"not_claimed": ["fixture"]},
                "not_claimed": ["fixture"],
                "records": [{"role": "before", "candidate_id": "before"}],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    source_report.write_text("# canonical training\n", encoding="utf-8")

    payload = canonical.run_reports(only="certificate-guided-discovery")
    report = payload["reports"][0]
    report_payload = json.loads((canonical.CANONICAL_DIR / "certificate-guided-discovery.json").read_text(encoding="utf-8"))
    scorecard = json.loads((canonical.CANONICAL_DIR / "quality-scorecard.json").read_text(encoding="utf-8"))
    scorecard_row = next(row for row in scorecard["input_reports"] if row["name"] == "certificate-guided-discovery")

    assert report["status"] == "pass"
    assert report["producer_status"] == "completed"
    assert "error" not in report
    assert scorecard_row["status"] == "pass"
    assert report_payload["producer_status"] == "skipped"
    assert report_payload["positive_discovery"] is None
    assert report_payload["matched_random_baseline"] is None
    assert report_payload["discovery_level"] == "D0"
    assert report_payload["claim_gate"]["status"] == "skipped"
    assert report_payload["main_claim_status"]["status"] == "skipped"


def test_certificate_guided_discovery_validation_accepts_empty_revocation_ledger(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps({key: [] if key == "revocation_ledger" else {"downgraded": False} if key == "revocation_decision" else "fixture" for key in spec.required_json_keys}) + "\n",
        encoding="utf-8",
    )
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "pass"
    assert validation["required_key_validation"]["missing_keys"] == []


def test_certificate_guided_discovery_validation_fails_closed_on_missing_revocation_fields(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {key: "fixture" for key in spec.required_json_keys if key not in {"revocation_decision", "revocation_ledger"}}
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["required_key_validation"]["status"] == "fail"
    assert set(validation["required_key_validation"]["missing_keys"]) == {"revocation_decision", "revocation_ledger"}


def test_index_root_is_relative_and_host_path_free(tmp_path):
    payload = canonical._index([])
    index_path = tmp_path / "index.json"
    index_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    json_text = index_path.read_text(encoding="utf-8")
    root = payload.get("root")

    assert root is None or not os.path.isabs(root)
    assert "/Users/" not in json_text
    assert ".worktrees" not in json_text


def test_missing_artifact_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert spec.json_artifact in validation["missing_artifacts"]
    assert spec.markdown_artifact in validation["missing_artifacts"]
    assert validation["required_key_validation"]["status"] == "fail"


def test_required_key_failure_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text('{"generated_at": "fixture"}\n', encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["missing_artifacts"] == []
    assert validation["required_key_validation"]["status"] == "fail"
    assert "source_artifacts" in validation["required_key_validation"]["missing_keys"]


def test_index_markdown_lists_gap_head_reports():
    payload = canonical._index(
        [
            _index_row_for_spec(canonical._specs_by_name()["gap-head-on-h"]),
            _index_row_for_spec(canonical._specs_by_name()["nongaussian-distribution-sweep"]),
            _index_row_for_spec(canonical._specs_by_name()["gap-head-discovery"]),
            _index_row_for_spec(canonical._specs_by_name()["certificate-guided-discovery"]),
        ]
    )
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-on-h" in markdown
    assert "gap-head-discovery" in markdown
    assert "nongaussian-distribution-sweep" in markdown
    assert "certificate-guided-discovery" in markdown


def test_release_manifest_sidecar_index_summary_is_pointer_only(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    (tmp_path / "reports").mkdir(parents=True, exist_ok=True)
    (tmp_path / "reports" / "release_manifest_sidecar.json").write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:release-manifest-sidecar",
                "artifact_id": "bedc-quality-lab:release-manifest-sidecar",
                "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
                "release_bundle_status": "ready",
                "tag_status": "absent",
                "version": "0.0.1",
                "required_pointers": [{"id": "canonical-index"}],
            }
        )
        + "\n",
        encoding="utf-8",
    )

    section = canonical._release_manifest_sidecar_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:release-manifest-sidecar",
        "json_artifact": "reports/release_manifest_sidecar.json",
        "markdown_artifact": "reports/release_manifest_sidecar.md",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "release_bundle_status": "ready",
        "tag_status": "absent",
        "version": "0.0.1",
    }
    assert payload["release_manifest_sidecar"] == section
    assert set(section) == {
        "status",
        "artifact_id",
        "json_artifact",
        "markdown_artifact",
        "canonical_role",
        "release_bundle_status",
        "tag_status",
        "version",
    }
    assert "release_manifest_sidecar" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "required_pointers" not in json.dumps(payload["release_manifest_sidecar"])
    assert "release_manifest_sidecar" not in json.dumps(payload["discovery_map"])
    assert "Release manifest sidecar" in markdown


def test_release_readiness_index_section_is_pointer_only():
    section = canonical._release_readiness_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert section == {
        "status": "pointer-only",
        "canonical_role": "index_projection_not_fact_source",
        "freshness_hardgate": "scripts/run_canonical_reports.py --verify-fingerprints",
        "source_count": len(canonical.RELEASE_READINESS_POINTERS),
        "sources": [dict(row) for row in canonical.RELEASE_READINESS_POINTERS],
        "not_claimed": (
            "This section does not copy scorecard, discovery, formal, claim, or release facts; "
            "read the listed owner pointers and use --verify-fingerprints for stale-hash failure."
        ),
    }
    assert payload["release_readiness"] == section
    assert "Release readiness" in markdown
    assert "scripts/run_canonical_reports.py --verify-fingerprints" in markdown
    assert "release_readiness" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "release_readiness_board" not in json.dumps(payload["release_readiness"])
    assert "release_bundle_status" not in section
    assert "ready" not in section
    assert "metrics" not in section
    assert "coverage_matrix" not in section
    assert "rows" not in section
    assert all(set(row) == {"id", "label", "artifact", "pointer", "owner_pointer"} for row in section["sources"])


def test_cache_equivalence_index_section_is_pointer_only():
    section = canonical._cache_equivalence_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:canonical-cache-equivalence",
        "schema_id": "bedc-quality-lab:canonical-cache-equivalence",
        "json_artifact": "reports/canonical/cache-equivalence.json",
        "canonical_role": "index_projection_not_fact_source",
        "owner_pointer": "reports/canonical/cache-equivalence.json:$",
        "targets_pointer": "reports/canonical/cache-equivalence.json:$.targets",
        "hardgates_pointer": "reports/canonical/cache-equivalence.json:$.hardgates",
        "freshness_hardgate": "scripts/run_canonical_cache_equivalence.py --check",
    }
    assert payload["cache_equivalence"] == section
    assert "Cache equivalence" in markdown
    assert "cache_equivalence" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "pass_count" not in json.dumps(section)
    assert "targets" not in section
    assert "hardgates" not in section


def test_canonical_consistency_makefile_runs_fingerprints_before_cache_equivalence():
    makefile = (canonical.ROOT / "Makefile").read_text(encoding="utf-8")
    lines = makefile.splitlines()
    target_index = lines.index("canonical-consistency:")
    commands = []
    for line in lines[target_index + 1:]:
        if line and not line.startswith("\t"):
            break
        if line.startswith("\t"):
            commands.append(line.strip())

    assert commands == [
        "python3 scripts/run_canonical_reports.py --verify-fingerprints",
        "python3 scripts/run_canonical_cache_equivalence.py --check",
    ]
    assert "canonical-cache-equivalence:" in lines


def test_release_readiness_forbidden_files_do_not_exist():
    forbidden = [
        "bedc_quality_lab/release_readiness.py",
        "bedc_quality_lab/release_readiness_board.py",
        "scripts/run_release_readiness_board.py",
        "reports/canonical/release_readiness_board.json",
        "reports/canonical/release_readiness_board.md",
    ]

    assert all(not (canonical.ROOT / path).exists() for path in forbidden)


def test_toy_latent_planning_bedc_sidecar_index_is_pointer_only(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_release_pointer_fixture(tmp_path)
    section = canonical._toy_latent_planning_bedc_index_section()
    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert section == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:toy-latent-planning-bedc",
        "json_artifact": "reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_package": "experiments/toy_latent_planning_bedc",
        "sidecar_ref": {"artifact": "reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json", "pointer": "$"},
        "claim_capsule_ref": {"artifact": "reports/toy_latent_planning_bedc/claim_capsule.json", "pointer": "$"},
        "summary_ref": {"artifact": "reports/toy_latent_planning_bedc/summary.json", "pointer": "$"},
        "hardgate_status_pointer": "reports/toy_latent_planning_bedc/claim_capsule.json:$.u_hardgates.status",
        "present_but_fail_closed": True,
    }
    assert payload["toy_latent_planning_bedc"] == section
    assert "toy_latent_planning_bedc" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "terminal_verdict" not in json.dumps(section)
    assert "positive_claim" not in json.dumps(section)
    assert "arm_summary" not in json.dumps(section)
    assert "Toy latent planning BEDC" in markdown


def test_derivative_debt_ledger_artifacts_stay_absent_from_canonical_surfaces():
    forbidden_artifacts = {
        "reports/canonical/derivative_debt_ledger.json",
        "reports/canonical/derivative_debt_ledger.md",
        "reports/canonical/jet_negative_witnesses.json",
    }
    forbidden_names = {
        "derivative-debt-ledger",
        "jet-negative-witnesses",
    }
    specs = canonical.CANONICAL_REPORTS
    index_text = (canonical.ROOT / "reports" / "canonical" / "index.json").read_text(encoding="utf-8")

    assert forbidden_names.isdisjoint({spec.name for spec in specs})
    assert forbidden_artifacts.isdisjoint({spec.json_artifact for spec in specs})
    assert forbidden_artifacts.isdisjoint({spec.markdown_artifact for spec in specs})
    for artifact in forbidden_artifacts:
        assert artifact not in index_text


def test_high_impact_claim_review_stays_absent_from_canonical_surfaces():
    forbidden_artifacts = {
        "reports/canonical/high-impact-claim-review.json",
        "reports/canonical/high-impact-claim-review.md",
    }
    forbidden_names = {"high-impact-claim-review"}
    specs = canonical.CANONICAL_REPORTS
    index_text = (canonical.ROOT / "reports/canonical/index.json").read_text(encoding="utf-8")

    assert forbidden_names.isdisjoint({spec.name for spec in specs})
    assert forbidden_artifacts.isdisjoint({spec.json_artifact for spec in specs})
    assert forbidden_artifacts.isdisjoint({spec.markdown_artifact for spec in specs})
    for artifact in forbidden_artifacts:
        assert artifact not in index_text


def test_high_impact_review_canonical_spec_uses_hyphen_path_and_core_role():
    spec = canonical._specs_by_name()["high-impact-review"]

    assert spec.json_artifact == "reports/canonical/high-impact-review.json"
    assert spec.markdown_artifact == "reports/canonical/high-impact-review.md"
    assert spec.bundle_role == "hg_p_core"
    assert "not_claimed" in spec.required_json_keys
    assert {"schema_id", "artifact_id", "generated_at", "source_artifacts", "review_rows", "hardgates", "not_claimed"} <= set(spec.required_json_keys)
    assert "reports/canonical/high_impact_review.json" not in {
        item
        for report in canonical.CANONICAL_REPORTS
        for item in (report.json_artifact, report.markdown_artifact)
    }


def test_high_impact_review_required_keys_include_not_claimed():
    spec = canonical._specs_by_name()["high-impact-review"]

    assert "not_claimed" in spec.required_json_keys
    assert spec.not_claimed_pointer == "$.not_claimed"


def test_high_impact_review_existing_artifact_regen_is_idempotent(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["high-impact-review"]
    payload = {
        "schema_id": "bedc-quality-lab:high-impact-review",
        "artifact_id": "bedc-quality-lab:high-impact-review",
            "generated_at": "2030-01-01T00:00:00+00:00",
            "seed": 1131,
            "source_artifacts": {
                "dgt": "reports/canonical/discovery-gated-transformer.json",
                "model_comparison": "reports/canonical/model-comparison.json",
                "claim_graph": "reports/canonical/claim_graph.json",
            },
            "review_rows": [
            {
                "claim_id": "claim:discovery-gated-transformer",
                "status": "fail",
                "review_level": "bounded-D4-terminal-gate",
                "review_scope": "DGT bounded deterministic toy D4 positive-discovery terminal promotion only",
                "ledger_pointer": "reports/canonical/high-impact-review.json:$.review_rows[0]",
                "claim_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
                "hardgate_pointer": "reports/canonical/high-impact-review.json:$.hardgates",
                "not_claimed_pointer": "reports/canonical/high-impact-review.json:$.not_claimed",
                "reason": "high-impact-review-required",
            }
        ],
        "hardgates": {
            f"HIR-HG{index}": {
                "status": "fail",
                "reason": "fixture; fail-closed",
                "evidence_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
            }
            for index in range(1, 11)
        },
        "not_claimed": [
            "Bounded D4 prototype only.",
            "No production deployment authority is claimed.",
            "No global model superiority claim is made.",
            "No LLM replacement claim is made.",
            "No universal training recipe is claimed.",
            "No full BEDC closure is claimed.",
        ],
    }
    json_path = tmp_path / spec.json_artifact
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    (tmp_path / spec.markdown_artifact).write_text("# High Impact Review\n", encoding="utf-8")

    first = canonical._run_spec(spec, mode="verify", reuse_existing=True, generated_at="2030-01-01T00:00:00+00:00")
    second = canonical._run_spec(spec, mode="verify", reuse_existing=True, generated_at="2030-01-01T00:00:00+00:00")

    assert first == second
    assert first["validation"]["required_key_validation"]["status"] == "pass"


def _reporting_spec(**overrides):
    fields = {
        "name": "fixture-report",
        "command": ("python3", "scripts/run_fixture.py"),
        "json_artifact": "reports/canonical/fixture-report.json",
        "markdown_artifact": "reports/canonical/fixture-report.md",
        "required_json_keys": ("source_artifacts", "applicability_boundary", "positive_claim"),
        "estimated_seconds": 1,
        "bundle_role": "hg_p_core",
        "scope_pointer": "$.applicability_boundary",
        "cost_pointer": "$.source_artifacts.cost_protocol",
        "not_claimed_pointer": "$.applicability_boundary.not_claimed",
        "positive_claim_pointer": "$.positive_claim",
        "control_pointer": "$.control",
        "no_control_rationale_pointer": None,
        "claim_capsule_pointer": "$.claim_capsule_ref",
    }
    fields.update(overrides)
    return canonical.CanonicalReportSpec(**fields)


def _write_reporting_fixture(root: Path, spec, *, claim_capsule=True, cost_protocol=True, not_claimed=True):
    payload = {
        "source_artifacts": {},
        "applicability_boundary": {"claimed_scope": "fixture"},
        "positive_claim": {"status": "bounded-positive"},
        "control": {"status": "pass"},
    }
    if claim_capsule:
        payload["claim_capsule_ref"] = {"claim_id": "claim:fixture"}
    if cost_protocol:
        payload["source_artifacts"]["cost_protocol"] = "configs/default_cost_protocol.yaml"
    if not_claimed:
        payload["applicability_boundary"]["not_claimed"] = ["fixture boundary"]
    path = root / spec.json_artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    md = root / spec.markdown_artifact
    md.parent.mkdir(parents=True, exist_ok=True)
    md.write_text("# Fixture\n", encoding="utf-8")
    return payload


def test_index_discipline_owns_reporting_hardgate_nested_object():
    forbidden = {
        "papers/bedc-quality-lab/bedc_quality_lab/reporting_guideline.py",
        "papers/bedc-quality-lab/bedc_quality_lab/report_claim_manifest.py",
        "papers/bedc-quality-lab/scripts/run_reporting_guideline.py",
        "papers/bedc-quality-lab/reports/canonical/reporting-guideline.json",
        "papers/bedc-quality-lab/reports/canonical/reporting-guideline.md",
        "papers/bedc-quality-lab/reports/canonical/report_claim_manifest.json",
        "papers/bedc-quality-lab/reports/canonical/report_claim_manifest.md",
    }
    payload = json.loads((canonical.ROOT / "reports/canonical/index.json").read_text(encoding="utf-8"))

    assert payload["reports"]
    for report in payload["reports"]:
        gate = report["discipline"]["reporting_hardgate"]
        assert gate["hardgate_id"] == canonical.REPORTING_HARDGATE_ID
        assert set(gate) == {
            "hardgate_id",
            "status",
            "promotion_eligible",
            "applicability",
            "required_cells",
            "missing_required_cells",
            "cells",
        }
        assert "construct_validity_pointer" in report["discipline"]
        assert "construct_validity_status" in report["discipline"]
        assert "construct_validity" not in gate
    assert all(not Path(path).exists() for path in forbidden)
    assert "reporting_guideline" not in {spec.name for spec in canonical.CANONICAL_REPORTS}


def test_missing_claim_capsule_blocks_positive_promotion(tmp_path, monkeypatch):
    spec = _reporting_spec(claim_capsule_pointer="$.missing_claim_capsule")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    discipline = canonical._discipline(spec)
    result = canonical._run_spec(spec, reuse_existing=True)

    gate = discipline["reporting_hardgate"]
    assert gate["status"] == "fail"
    assert gate["promotion_eligible"] is False
    assert gate["missing_required_cells"] == ["claim_capsule"]
    assert gate["cells"]["claim_capsule"] == {
        "pointer": "$.missing_claim_capsule",
        "source_artifact": "reports/canonical/fixture-report.json",
        "status": "missing",
    }
    assert result["status"] == "fail"


def test_missing_cost_protocol_blocks_positive_promotion(tmp_path, monkeypatch):
    spec = _reporting_spec()
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec, cost_protocol=False)

    gate = canonical._discipline(spec)["reporting_hardgate"]

    assert gate["status"] == "fail"
    assert gate["promotion_eligible"] is False
    assert gate["missing_required_cells"] == ["cost_protocol"]
    assert gate["cells"]["cost_protocol"] == {
        "pointer": "$.source_artifacts.cost_protocol",
        "source_artifact": "reports/canonical/fixture-report.json",
        "status": "missing",
    }


def test_missing_not_claimed_blocks_positive_promotion(tmp_path, monkeypatch):
    spec = _reporting_spec()
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec, not_claimed=False)

    gate = canonical._discipline(spec)["reporting_hardgate"]

    assert gate["status"] == "fail"
    assert gate["promotion_eligible"] is False
    assert gate["missing_required_cells"] == ["not_claimed"]
    assert gate["cells"]["not_claimed"] == {
        "pointer": "$.applicability_boundary.not_claimed",
        "source_artifact": "reports/canonical/fixture-report.json",
        "status": "missing",
    }


def test_complete_reporting_hardgate_allows_positive_promotion(tmp_path, monkeypatch):
    spec = _reporting_spec()
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    result = canonical._run_spec(spec, reuse_existing=True)
    gate = result["discipline"]["reporting_hardgate"]

    assert gate["status"] == "pass"
    assert gate["promotion_eligible"] is True
    assert gate["missing_required_cells"] == []
    assert gate["cells"]["claim_capsule"]["status"] == "present"
    assert gate["cells"]["cost_protocol"]["status"] == "present"
    assert gate["cells"]["not_claimed"]["status"] == "present"
    assert result["status"] == "pass"


def test_auxiliary_reporting_hardgate_is_not_applicable(tmp_path, monkeypatch):
    spec = _reporting_spec(bundle_role="auxiliary")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec, claim_capsule=False, cost_protocol=False, not_claimed=False)

    gate = canonical._discipline(spec)["reporting_hardgate"]

    assert gate["status"] == "not-applicable"
    assert gate["promotion_eligible"] is False
    assert gate["missing_required_cells"] == []


def test_reporting_hardgate_cells_are_pointer_only(tmp_path, monkeypatch):
    spec = _reporting_spec()
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    gate = canonical._discipline(spec)["reporting_hardgate"]

    assert set(gate["cells"]) == {
        "scope_seal",
        "claim_capsule",
        "evidence_envelope",
        "cost_protocol",
        "backend",
        "discovery_level",
        "claim_graph_path",
        "not_claimed",
        "negative_witness",
        "formal_status",
    }
    for cell in gate["cells"].values():
        assert set(cell) == {"pointer", "source_artifact", "status"}
    serialized = json.dumps(gate)
    assert "ClaimCapsule body" not in serialized
    assert "CostProtocol rows" not in serialized
    assert "ClaimGraph topology" not in serialized
    assert "negative witness prose" not in serialized
    assert "\\formalstatus" not in serialized
    assert "theorem proof" not in serialized


def test_run_spec_consumes_reporting_hardgate_failure(tmp_path, monkeypatch):
    spec = _reporting_spec(claim_capsule_pointer="$.missing_claim_capsule")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    result = canonical._run_spec(spec, reuse_existing=True)

    assert result["validation"]["status"] == "pass"
    assert result["discipline"]["reporting_hardgate"]["status"] == "fail"
    assert result["status"] == "fail"


def test_run_spec_consumes_construct_validity_failure(tmp_path, monkeypatch):
    spec = _reporting_spec(
        required_json_keys=(
            "source_artifacts",
            "applicability_boundary",
            "positive_claim",
            "construct_validity_hardgates",
        ),
        construct_validity_pointer="reports/canonical/fixture-report.json:$.construct_validity_hardgates",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    payload = _write_reporting_fixture(tmp_path, spec)
    payload["construct_validity_hardgates"] = {
        "schema_id": "bedc.quality.construct_validity_hardgates",
        "status": "fail",
        "failed_gates": ["CV-HG2"],
    }
    (tmp_path / spec.json_artifact).write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    result = canonical._run_spec(spec, reuse_existing=True)

    assert result["validation"]["status"] == "pass"
    assert result["discipline"]["reporting_hardgate"]["status"] == "pass"
    assert result["construct_validity"]["status"] == "fail"
    assert result["construct_validity"]["failed_gates"] == ["CV-HG2"]
    assert result["status"] == "fail"


def test_run_spec_treats_missing_construct_validity_pointer_as_failure(tmp_path, monkeypatch):
    spec = _reporting_spec(
        required_json_keys=("source_artifacts", "applicability_boundary", "positive_claim"),
        construct_validity_pointer="reports/canonical/fixture-report.json:$.missing_construct_validity",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    result = canonical._run_spec(spec, reuse_existing=True)

    assert result["validation"]["status"] == "pass"
    assert result["construct_validity"]["status"] == "missing"
    assert result["status"] == "fail"


def test_host_env_is_ignored_by_reporting_hardgate(tmp_path, monkeypatch):
    spec = _reporting_spec()
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    _write_reporting_fixture(tmp_path, spec)

    before = canonical._discipline(spec)["reporting_hardgate"]
    host_env = tmp_path / ".refactor-loop" / "host.env"
    host_env.parent.mkdir(parents=True, exist_ok=True)
    host_env.write_text("BRANCH=other\nSTATUS=pass\nPATH=/tmp/other\n", encoding="utf-8")
    after = canonical._discipline(spec)["reporting_hardgate"]

    assert after == before


def test_claim_complexity_is_registered_as_post_verdict_auxiliary_report():
    specs = {spec.name: spec for spec in canonical.CANONICAL_REPORTS}
    spec_names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    claim_verdict_index = spec_names.index("claim-complexity")

    spec = specs["claim-complexity"]
    assert spec.command == ("python3", "scripts/run_claim_complexity_score.py")
    assert spec.json_artifact == canonical.CLAIM_COMPLEXITY_JSON_ARTIFACT
    assert spec.markdown_artifact == canonical.CLAIM_COMPLEXITY_MARKDOWN_ARTIFACT
    assert spec.bundle_role == "auxiliary"
    assert "claim-complexity" in canonical.POST_VERDICT_REPORTS
    assert "claim-complexity" in canonical.DISCOVERY_MAP_EXCLUDED_REPORTS
    assert claim_verdict_index > spec_names.index("causal-patch-suite")


def test_run_reports_runs_claim_complexity_after_claim_verdicts_are_written(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    _patch_lightweight_run_reports(monkeypatch)
    calls = []
    reports = {spec.name: spec for spec in canonical.CANONICAL_REPORTS}
    pre_verdict_spec = reports["mixing-family-sweep"]
    claim_complexity_spec = reports["claim-complexity"]
    verdict_path = tmp_path / canonical.CLAIM_VERDICTS_JSONL_ARTIFACT

    monkeypatch.setattr(canonical, "CANONICAL_REPORTS", (pre_verdict_spec, claim_complexity_spec))

    def fake_run_spec(spec, mode="changed", generated_at=None):
        calls.append(("run-spec", spec.name, verdict_path.exists()))
        if spec.name == "claim-complexity":
            assert verdict_path.exists()
            rows = [json.loads(line) for line in verdict_path.read_text(encoding="utf-8").splitlines() if line]
            assert rows == [{"claim_id": "claim:fixture", "claim_verdict": "negative_discovery"}]
        return _index_row_for_spec(spec)

    def fake_write_claim_verdicts(*, root, generated_at=None):
        calls.append(("write-claim-verdicts", None, verdict_path.exists()))
        verdict_path.parent.mkdir(parents=True, exist_ok=True)
        row = {"claim_id": "claim:fixture", "claim_verdict": "negative_discovery"}
        verdict_path.write_text(json.dumps(row, sort_keys=True) + "\n", encoding="utf-8")
        return [row]

    monkeypatch.setattr(canonical, "_run_spec", fake_run_spec)
    monkeypatch.setitem(
        sys.modules,
        "scripts.run_claim_verdict_demo",
        types.SimpleNamespace(write_claim_verdicts=fake_write_claim_verdicts),
    )

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")

    assert "claim-complexity" in canonical.POST_VERDICT_REPORTS
    assert calls.index(("write-claim-verdicts", None, False)) < calls.index(("run-spec", "claim-complexity", True))
    assert ("run-spec", "mixing-family-sweep", False) in calls
    assert ("run-spec", "claim-complexity", False) not in calls
    assert [report["name"] for report in payload["reports"]] == ["mixing-family-sweep", "claim-complexity"]


def test_claim_complexity_is_not_discovery_map_manifest_source():
    from bedc_quality_lab.backends.current_lab import projection

    assert (
        canonical.CLAIM_COMPLEXITY_JSON_ARTIFACT
        not in projection._manifest_audit(root=canonical.ROOT, canonical_reports=canonical._discovery_map_reports())[
            "unregistered_json_artifacts"
        ]
    )


def test_dgt_l0_canonical_spec_requires_honest_owner_keys():
    spec = canonical._specs_by_name()["dgt-l0-controls"]
    required = set(spec.required_json_keys)

    assert {
        "construct_suspension",
        "honest_metric_review",
        "feature_audit",
        "boundary_ledger",
        "negative_evidence",
        "ladder_consumption",
    }.issubset(required)


def test_claim_complexity_fingerprint_sidecar_path_is_canonical():
    spec = canonical._specs_by_name()["claim-complexity"]

    assert canonical._relative(canonical._fingerprint_path(spec)) == "reports/canonical/claim_complexity.fingerprint.json"


def test_claim_complexity_index_section_is_artifact_only(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    (tmp_path / "reports/canonical").mkdir(parents=True)
    (tmp_path / "reports/canonical/discovery_map.json").write_text(
        json.dumps(
            {
                "rows": [
                        {
                            "report": "demo",
                            "json_artifact": "reports/canonical/demo.json",
                            "markdown_artifact": "reports/canonical/demo.md",
                            "discovery_level": "D4",
                            "projection_status": "projected",
                            "classifier_reasons": ["fixture"],
                            "evidence_pointer": "$.positive_claim",
                            "audit_status": "valid",
                            "audit_reason": "",
                            "evidence_type": "deterministic_projection",
                            "evidence_provenance_pointer": evidence_provenance_pointer_for_report("demo"),
                            "control_pointer": "$.control",
                        }
                    ]
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (tmp_path / "reports/canonical/demo.json").write_text(
        json.dumps(
            {
                "positive_claim": True,
                "control": {"status": "pass"},
                "anti_triviality_status": "pass",
                "owner_contract": {
                    "scale_only": {"status": "present"},
                    "metadata_only": {"status": "present"},
                    "matched_random": {"status": "present"},
                    "forbidden_column": {"status": "present"},
                },
            }
            | owner_local_anti_triviality_contract(
                recommended_level="D4",
                scale_only_pointer="$.owner_contract.scale_only",
                metadata_only_pointer="$.owner_contract.metadata_only",
                matched_random_pointer="$.owner_contract.matched_random",
                forbidden_column_pointer="$.owner_contract.forbidden_column",
            ),
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (tmp_path / "reports/canonical/index.json").write_text(
        json.dumps(
            {
                "evidence_provenance": {
                    "schema_id": "bedc-quality-lab:evidence-provenance",
                    "owner": "bedc_quality_lab.evidence_provenance",
                    "generated_at": "fixture-time",
                    "producer_audits": [
                        {
                            "report": "demo",
                            "producer_command": ["python3", "scripts/run_demo.py"],
                            "producer_source_pointer": None,
                            "backward_pointers": [],
                            "optimizer_step_pointers": [],
                            "parameter_update_pointers": [],
                            "training_evidence_status": "training_evidence_absent",
                            "not_claimed": ["fixture"],
                        }
                    ],
                    "metric_rows": [
                        {
                            "report": "demo",
                            "metric_name": "headline",
                            "source_type": "deterministic_projection",
                            "source_code_pointer": None,
                            "source_artifact_pointer": "reports/canonical/demo.json:$.positive_claim",
                            "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                            "allowed_for_empirical_claim": False,
                            "value": True,
                            "not_claimed": ["fixture"],
                            "not_measurable_reason": None,
                        }
                    ],
                    "discovery_rows": [
                        {
                            "report": "demo",
                            "evidence_type": "deterministic_projection",
                            "discovery_map_pointer": "reports/canonical/discovery_map.json:$.rows[0]",
                            "metric_provenance_pointers": ["reports/canonical/index.json:$.evidence_provenance.metric_rows[0]"],
                            "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                            "allowed_claim_kinds": ["projection_only"],
                            "not_claimed": ["fixture"],
                        }
                    ],
                    "discovery_rows_by_report": {
                        "demo": {
                            "report": "demo",
                            "evidence_type": "deterministic_projection",
                            "discovery_map_pointer": "reports/canonical/discovery_map.json:$.rows[0]",
                            "metric_provenance_pointers": ["reports/canonical/index.json:$.evidence_provenance.metric_rows[0]"],
                            "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                            "allowed_claim_kinds": ["projection_only"],
                            "not_claimed": ["fixture"],
                        }
                    },
                    "hardgate_status": {},
                    "artifact_pointers": {
                        "owner_pointer": "reports/canonical/index.json:$.evidence_provenance",
                        "discovery_map_rows": "reports/canonical/discovery_map.json:$.rows",
                    },
                }
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (tmp_path / "reports/canonical/claim_verdicts.jsonl").write_text(
        json.dumps({"claim_id": "claim:demo", "claim_verdict": "accepted_positive_discovery"}, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    from scripts.run_claim_complexity_score import write_claim_complexity_score

    write_claim_complexity_score(root=tmp_path, generated_at="fixture-time")

    section = canonical._claim_complexity_index_section()

    assert section["canonical_role"] == "artifact_only_evidence"
    assert section["status"] == "pass"
    assert section["rows_pointer"] == "reports/canonical/claim_complexity.json:$.rows"
    assert section["verdict_refs_pointer"] == "reports/canonical/claim_complexity.json:$.rows[*].pointer_only_verdict_ref"
    assert section["terminal_verdict_owner"] == canonical.CLAIM_VERDICTS_ARTIFACT_ID


def test_claim_complexity_index_section_fails_on_unresolved_pointer(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    (tmp_path / "reports/canonical").mkdir(parents=True)
    payload = {
        "schema_id": canonical.CLAIM_COMPLEXITY_SCHEMA_ID,
        "artifact_id": canonical.CLAIM_COMPLEXITY_ARTIFACT_ID,
        "generated_at": "fixture-time",
        "source_artifacts": {
            "discovery_map": "reports/canonical/discovery_map.json",
            "claim_verdicts": "reports/canonical/claim_verdicts.jsonl",
        },
        "rows": [
            {
                "claim_id": "claim:demo",
                "complexity_score": 1,
                "scoring_dimensions": [
                    {"name": name, "weight": 1 if index == 0 else 0, "evidence_pointer": "reports/canonical/missing.json:$"}
                    for index, name in enumerate(DIMENSION_NAMES)
                ],
                "pointer_only_verdict_ref": "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
                "not_claimed": "fixture",
            }
        ],
        "hardgates": {
            "CC-HG1": {"gate_id": "CC-HG1", "status": "fail", "reason": "fixture", "evidence_pointer": None},
            "CC-HG2": {"gate_id": "CC-HG2", "status": "pass", "reason": "fixture", "evidence_pointer": None},
            "CC-HG3": {"gate_id": "CC-HG3", "status": "pass", "reason": "fixture", "evidence_pointer": None},
        },
        "not_claimed": ["fixture"],
    }
    (tmp_path / "reports/canonical/claim_complexity.json").write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    section = canonical._claim_complexity_index_section()

    assert section["status"] == "fail"
    assert section["validation_errors"]


def test_evidence_provenance_index_section_uses_current_report_manifest(tmp_path, monkeypatch):
    spec = canonical.CanonicalReportSpec(
        name="provenance-fixture",
        command=("python3", "scripts/run_fixture.py"),
        json_artifact="reports/canonical/provenance-fixture.json",
        markdown_artifact="reports/canonical/provenance-fixture.md",
        required_json_keys=("positive",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts/run_fixture.py").write_text("def main():\n    return None\n", encoding="utf-8")
    (tmp_path / "reports/canonical").mkdir(parents=True)
    (tmp_path / "reports/canonical/provenance-fixture.json").write_text(
        json.dumps(
            {
                "positive": True,
                "scope": {"status": "present"},
                "cost": {"status": "present"},
                "not_claimed": ["fixture"],
                "control": {"status": "present"},
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (tmp_path / "reports/canonical/discovery_map.json").write_text(
        json.dumps(
            {
                "rows": [
                    _committed_discovery_map_row("provenance-fixture")
                    | {
                        "json_artifact": "reports/canonical/provenance-fixture.json",
                        "markdown_artifact": "reports/canonical/provenance-fixture.md",
                    }
                ]
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    section = canonical._evidence_provenance_index_section("fixture-time", canonical_reports=(spec,))

    assert section["schema_id"] == "bedc-quality-lab:evidence-provenance"
    assert section["owner"] == "bedc_quality_lab.evidence_provenance"
    assert [row["report"] for row in section["producer_audits"]] == ["provenance-fixture"]
    assert [row["report"] for row in section["metric_rows"]] == ["provenance-fixture"]
    assert [row["report"] for row in section["discovery_rows"]] == ["provenance-fixture"]
    assert section["artifact_pointers"]["owner_pointer"] == "reports/canonical/index.json:$.evidence_provenance"


def test_index_evidence_provenance_owner_ignores_subset_manifest_argument():
    payload = canonical._index(
        [],
        generated_at="2030-01-01T00:00:00+00:00",
        canonical_reports=(canonical.CANONICAL_REPORTS[0],),
    )
    section = payload["evidence_provenance"]
    manifest_names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    assert [row["report"] for row in section["producer_audits"]] == manifest_names
    assert section["hardgate_status"]["EVCLASS-HG1"]["status"] == "pass"


def test_structural_generalization_splits_canonical_spec_required_keys():
    spec = canonical._specs_by_name()["structural-generalization-splits"]

    assert spec.json_artifact == "reports/canonical/structural-generalization-splits.json"
    assert spec.markdown_artifact == "reports/canonical/structural-generalization-splits.md"
    assert set(spec.required_json_keys) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "split_registry",
        "split_rows",
        "classifier_rows",
        "hardgates",
        "boundary_ledger",
        "consumer_pointers",
        "not_claimed",
    }


def test_structural_generalization_splits_index_pointer_shape():
    section = canonical._structural_generalization_splits_index_section()

    assert section["splits_pointer"] == "reports/canonical/structural-generalization-splits.json:$.split_rows"
    assert section["classifier_pointer"] == "reports/canonical/structural-generalization-splits.json:$.classifier_rows"
    assert section["hardgates_pointer"] == "reports/canonical/structural-generalization-splits.json:$.hardgates"
    assert section["boundary_pointer"] == "reports/canonical/structural-generalization-splits.json:$.boundary_ledger"


def test_structural_generalization_splits_fingerprint_path_is_canonical():
    spec = canonical._specs_by_name()["structural-generalization-splits"]

    assert canonical._relative(canonical._fingerprint_path(spec)) == (
        "reports/canonical/structural-generalization-splits.fingerprint.json"
    )


def test_structural_generalization_splits_nested_source_artifacts_enter_fingerprint(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["structural-generalization-splits"]
    for artifact, payload in {
        "reports/canonical/input-accessibility.json": {"schema_id": "bedc-quality-lab:input-accessibility", "rows": []},
        "reports/canonical/winnability-certificates.json": {
            "schema_id": "bedc-quality-lab:winnability-certificates",
            "certificates": [],
        },
        spec.json_artifact: {
            "schema_id": "bedc-quality-lab:structural-generalization-splits",
            "source_artifacts": {
                "input_accessibility": {
                    "artifact": "reports/canonical/input-accessibility.json",
                    "owner_pointer": "reports/canonical/input-accessibility.json:$",
                },
                "winnability_certificates": {
                    "artifact": "reports/canonical/winnability-certificates.json",
                    "owner_pointer": "reports/canonical/winnability-certificates.json:$",
                },
            },
        },
    }.items():
        path = tmp_path / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    paths = {row["path"] for row in canonical._source_artifact_inputs(spec)}

    assert paths == {
        "reports/canonical/input-accessibility.json",
        "reports/canonical/winnability-certificates.json",
    }


def test_structural_generalization_splits_gate_pointer_targets_enter_fingerprint(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    spec = canonical._specs_by_name()["structural-generalization-splits"]
    for artifact, payload in {
        "reports/canonical/input-accessibility.json": {"schema_id": "bedc-quality-lab:input-accessibility", "rows": []},
        "reports/canonical/winnability-certificates.json": {
            "schema_id": "bedc-quality-lab:winnability-certificates",
            "certificates": [],
        },
        "reports/canonical/performance.json": {"rows": [{"score": 1.0}]},
        spec.json_artifact: {
            "schema_id": "bedc-quality-lab:structural-generalization-splits",
            "classifier_rows": [
                {
                    "row_id": "symbol",
                    "visibility_pointer": "reports/canonical/input-accessibility.json:$.rows[0]",
                    "winnability_pointer": "reports/canonical/winnability-certificates.json:$.certificates[0]",
                    "performance_pointer": "reports/canonical/performance.json:$.rows[0]",
                }
            ],
            "split_rows": [],
            "source_artifacts": {},
        },
    }.items():
        path = tmp_path / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    paths = {row["path"] for row in canonical._source_artifact_inputs(spec)}

    assert paths == {
        "reports/canonical/input-accessibility.json",
        "reports/canonical/winnability-certificates.json",
        "reports/canonical/performance.json",
    }


def test_structural_generalization_splits_changed_mode_reruns_when_gate_pointer_target_is_deleted(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)
    canonical_dir = tmp_path / "reports" / "canonical"
    canonical_dir.mkdir(parents=True, exist_ok=True)
    (canonical_dir / "input-accessibility.json").write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:input-accessibility",
                "rows": [
                    {
                        "row_id": "symbol",
                        "family": "symbol_remapping",
                        "target_variable": "symbol",
                        "candidate_id": "candidate",
                        "fair_arm_id": "fair-arm",
                        "target_visible": True,
                        "candidate_visible": True,
                        "fair_arm_visible": True,
                        "finite_remap": {"x": "u"},
                        "performance_pointer": "reports/canonical/performance.json:$.rows[0]",
                    }
                ],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "winnability-certificates.json").write_text(
        json.dumps(
            {
                "schema_id": "bedc-quality-lab:winnability-certificates",
                "certificates": [
                    {
                        "split_id": "symbol",
                        "certificate_id": "win-symbol",
                        "winnable": True,
                        "status": "pass",
                    }
                ],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical_dir / "performance.json").write_text(json.dumps({"rows": [{"score": 1.0}]}, sort_keys=True) + "\n", encoding="utf-8")

    first = canonical.run_reports(only="structural-generalization-splits", cold=True, generated_at="fixture")
    first_payload = json.loads((canonical_dir / "structural-generalization-splits.json").read_text(encoding="utf-8"))

    assert first["reports"][0]["producer_status"] == "completed"
    assert len(first_payload["split_rows"]) == 1

    (canonical_dir / "performance.json").unlink()
    second = canonical.run_reports(only="structural-generalization-splits", generated_at="fixture")
    second_payload = json.loads((canonical_dir / "structural-generalization-splits.json").read_text(encoding="utf-8"))

    assert second["reports"][0]["producer_status"] == "completed"
    assert second["reports"][0]["fingerprint_status"] == "written"
    assert second_payload["split_rows"] == []
    assert second_payload["classifier_rows"][0]["classification"] == "excluded"
    assert second_payload["classifier_rows"][0]["failed_hardgates"] == ["SYM-HG4"]


def test_structural_generalization_splits_only_regen_is_idempotent(tmp_path, monkeypatch):
    _set_canonical_tmp_root(monkeypatch, tmp_path)

    first_payload = canonical.run_reports(
        only="structural-generalization-splits",
        generated_at="2030-01-01T00:00:00+00:00",
        cold=True,
    )
    first = {
        relative: (tmp_path / relative).read_bytes()
        for relative in (
            "reports/canonical/structural-generalization-splits.json",
            "reports/canonical/structural-generalization-splits.md",
            "reports/canonical/structural-generalization-splits.fingerprint.json",
        )
    }
    second_payload = canonical.run_reports(
        only="structural-generalization-splits",
        generated_at="2030-01-01T00:00:00+00:00",
        cold=True,
    )
    second = {
        relative: (tmp_path / relative).read_bytes()
        for relative in first
    }

    assert first == second
    assert first_payload["reports"][0]["name"] == "structural-generalization-splits"
    assert second_payload["reports"][0]["name"] == "structural-generalization-splits"

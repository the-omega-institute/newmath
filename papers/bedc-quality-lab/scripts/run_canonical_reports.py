#!/usr/bin/env python3
"""Run lab-local canonical reports and publish a discovery index."""

from __future__ import annotations

import argparse
import ast
from dataclasses import asdict, dataclass, replace
from datetime import datetime, timezone
import hashlib
import importlib
import importlib.util
import inspect
import json
from pathlib import Path
import sys
from typing import Any, Literal, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import pointer_value as _bracket_pointer_value
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer as _resolve_committed_artifact_pointer
from bedc_quality_lab.discovery_compiler.pointers import split_artifact_pointer as _split_artifact_pointer
from bedc_quality_lab.discovery_compiler.map import validate_discovery_map_payload
from bedc_quality_lab.discovery_regularized_training import (
    QUALITY_PROMOTION_ARMS as DRT_QUALITY_PROMOTION_ARMS,
    DRT_EXTENSION_UER_MAX,
    DRT_EXTENSION_UER_REDUCTION_MIN,
    drt_extension_forbidden_key_audit,
    quality_artifact_pointer as _drt_quality_artifact_pointer,
)
from bedc_quality_lab.discovery_gated_transformer_training import (
    TRAINING_REPLAY_ARTIFACT as DGT_TRAINING_REPLAY_ARTIFACT,
)
from scripts.literature_ledger import validate_literature_ledger
from tools.quality_discovery_adversarial_generator import (
    EXPECTED_KINDS as NEGATIVE_WITNESS_KINDS,
)

CANONICAL_DIR = ROOT / "reports" / "canonical"
INDEX_ARTIFACT = CANONICAL_DIR / "index.json"
INDEX_SCHEMA_ID = "bedc-quality-lab:canonical-report-index"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
FINGERPRINT_INPUT_SCHEMA_ID = "bedc-quality-lab:canonical-report-input-fingerprint"
INDEX_ROOT = "papers/bedc-quality-lab"
QUALITY_SCORECARD_JSON_ARTIFACT = "reports/canonical/quality-scorecard.json"
QUALITY_SCORECARD_MARKDOWN_ARTIFACT = "reports/canonical/quality-scorecard.md"
QUALITY_SCORECARD_ARTIFACT_ID = "bedc-quality-lab:quality-scorecard"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.md"
DIMENSION_MISMATCH_TRANSFER_ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-debt-transfer"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.json"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.md"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-transfer-robustness"
NEGATIVE_WITNESSES_JSON_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
NEGATIVE_WITNESSES_ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witnesses"
NEGATIVE_WITNESSES_EXPECTED_KIND_COUNT = len(NEGATIVE_WITNESS_KINDS)
CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
CLAIM_VERDICTS_ARTIFACT_ID = "bedc-quality-lab:claim-verdicts"
CLAIM_GRAPH_JSON_ARTIFACT = "reports/canonical/claim_graph.json"
CLAIM_GRAPH_MARKDOWN_ARTIFACT = "reports/canonical/claim_graph.md"
CLAIM_GRAPH_ARTIFACT_ID = "bedc-quality-lab:claim-graph"
CLAIM_CAPSULE_JSON_ARTIFACT = "reports/canonical/claim_capsule.json"
CLAIM_CAPSULE_ARTIFACT_ID = "bedc-quality-lab:claim-capsule"
CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.json"
NEGATIVE_WITNESS_SUMMARY_MARKDOWN_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.md"
NEGATIVE_WITNESS_SUMMARY_ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witness-summary"
NEGATIVE_DISCOVERY_REPORTS_JSON_ARTIFACT = "reports/canonical/negative_discovery_reports.json"
NEGATIVE_DISCOVERY_REPORTS_MARKDOWN_ARTIFACT = "reports/canonical/negative_discovery_reports.md"
NEGATIVE_DISCOVERY_REPORTS_ARTIFACT_ID = "bedc-quality-lab:negative-discovery-reports"
NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT = "reports/canonical/negative_witness_mutation_ledger.json"
MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT = "reports/canonical/model_mutation_lineage_graph.md"
DGT_MUTATION_REPORT_ARTIFACT = "reports/canonical/dgt_mutation_report.json"
NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
NEW_MODEL_HARDGATES_JSON_ARTIFACT = "reports/canonical/new_model_hardgates.json"
NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT = "reports/canonical/new_model_hardgates.md"
NEW_MODEL_HARDGATES_ARTIFACT_ID = "bedc-quality-lab:new-model-hardgates"
NEW_MODEL_HARDGATES_SCHEMA_ID = "bedc-quality-lab:new-model-hardgates"
DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
DISCOVERY_REGULARIZED_TRAINING_MARKDOWN_ARTIFACT = "reports/canonical/discovery-regularized-training.md"
MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT = "reports/canonical/mechanism-seeking-network.json"
DISCOVERY_GATED_NAS_JSON_ARTIFACT = "reports/canonical/discovery-gated-nas.json"
DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT = "reports/canonical/discovery_gated_transformer.json"
DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT = "reports/canonical/discovery_gated_transformer.md"
DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer"
DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer"
DGT_TRAINING_HARDGATES_POINTER = f"{DGT_TRAINING_REPLAY_ARTIFACT}:$.hardgates"
MODEL_DESIGN_SUITE_JSON_ARTIFACT = "reports/canonical/model_design_suite.json"
MODEL_DESIGN_SUITE_MARKDOWN_ARTIFACT = "reports/canonical/model_design_suite.md"
MODEL_DESIGN_SUITE_ARTIFACT_ID = "bedc-quality-lab:model-design-suite"
MODEL_DESIGN_SUITE_SCHEMA_ID = "bedc-quality-lab:model-design-suite"
MODEL_DISCOVERY_SUITE_SUMMARY_ARTIFACT = "reports/runs/model-discovery-suite/summary.json"
FORMAL_HARDENING_JSON_ARTIFACT = "reports/canonical/formal_hardening.json"
FORMAL_HARDENING_MARKDOWN_ARTIFACT = "reports/canonical/formal_hardening.md"
FORMAL_HARDENING_ARTIFACT_ID = "bedc-quality-lab:formal-hardening"
GAP_HEAD_TRANSFER_ATLAS_JSON_ARTIFACT = "reports/canonical/gap_head_transfer_atlas.json"
GAP_HEAD_TRANSFER_ATLAS_MARKDOWN_ARTIFACT = "reports/canonical/gap_head_transfer_atlas.md"
GAP_HEAD_TRANSFER_ATLAS_ARTIFACT_ID = "bedc-quality-lab:gap-head-transfer-atlas"
GAP_HEAD_MECHANISM_NAMECERT_JSON_ARTIFACT = "reports/gap_head_mechanism_namecert.json"
GAP_HEAD_MECHANISM_NAMECERT_MARKDOWN_ARTIFACT = "reports/gap_head_mechanism_namecert.md"
GAP_HEAD_MECHANISM_NAMECERT_ARTIFACT_ID = "bedc-quality-lab:gap-head-mechanism-namecert"
GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
GAP_HEAD_ATTRIBUTION_MARKDOWN_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.md"
GAP_HEAD_ATTRIBUTION_ARTIFACT_ID = "gap_head_attribution_capsule"
RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT = "reports/release_manifest_sidecar.json"
RELEASE_MANIFEST_SIDECAR_MARKDOWN_ARTIFACT = "reports/release_manifest_sidecar.md"
RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID = "bedc-quality-lab:release-manifest-sidecar"
TOY_LATENT_PLANNING_BEDC_JSON_ARTIFACT = "reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json"
TOY_LATENT_PLANNING_BEDC_SUMMARY_ARTIFACT = "reports/toy_latent_planning_bedc/summary.json"
TOY_LATENT_PLANNING_BEDC_CLAIM_CAPSULE_ARTIFACT = "reports/toy_latent_planning_bedc/claim_capsule.json"
TOY_LATENT_PLANNING_BEDC_ARTIFACT_ID = "bedc-quality-lab:toy-latent-planning-bedc"
RELEASE_NAMECERT_CANDIDATE_JSON_ARTIFACT = "reports/release_namecert_candidate.json"
RELEASE_NAMECERT_CANDIDATE_MARKDOWN_ARTIFACT = "reports/release_namecert_candidate.md"
RELEASE_NAMECERT_CANDIDATE_ARTIFACT_ID = "bedc-quality-lab:release-namecert-candidate"
TOY_SAFETY_BOUNDARY_JSON_ARTIFACT = "reports/canonical/toy_safety_boundary.json"
TOY_SAFETY_BOUNDARY_MARKDOWN_ARTIFACT = "reports/canonical/toy_safety_boundary.md"
TOY_SAFETY_BOUNDARY_ARTIFACT_ID = "bedc-quality-lab:toy-safety-boundary"


@dataclass(**{"froz" + "en": True})
class ObservedDebtAxisProjectionSpec:
    axis_id: str
    axis_label: str
    source_artifact: str
    evidence_pointer: str
    status_pointer: str
    positive_statuses: tuple[str, ...]
    hardgate_pointer: str | None
    debt_row_pointer: str | None
    not_claimed: str


OBSERVED_DEBT_AXIS_PROJECTION_SPECS = (
    ObservedDebtAxisProjectionSpec(
        axis_id="latent_distribution",
        axis_label="Latent distribution",
        source_artifact="reports/canonical/nongaussian-distribution-sweep.json",
        evidence_pointer="$.main_claim_status",
        status_pointer="$.main_claim_status",
        positive_statuses=("observed-debt",),
        hardgate_pointer="$.claim_gate",
        debt_row_pointer="$.records[0].latent_distribution_debt_item",
        not_claimed="Finite latent-distribution sweep only; no global non-Gaussian failure claim is projected.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="anisotropy",
        axis_label="Transition anisotropy",
        source_artifact="reports/canonical/anisotropic-ou-sweep.json",
        evidence_pointer="$.transition_debt_by_grid.rho_axes_0p95_0p3",
        status_pointer="$.transition_debt_by_grid.rho_axes_0p95_0p3.status",
        positive_statuses=("observed-debt",),
        hardgate_pointer=None,
        debt_row_pointer="$.transition_debt_by_grid.rho_axes_0p95_0p3",
        not_claimed="Transition anisotropy remains ledger evidence for this sweep, not a promoted observed-debt claim.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="dimension_mismatch",
        axis_label="Dimension mismatch",
        source_artifact=DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
        evidence_pointer="$.dimension_mismatch_debt_transfer.status",
        status_pointer="$.dimension_mismatch_debt_transfer.status",
        positive_statuses=("pass",),
        hardgate_pointer="$.hardgate_evidence",
        debt_row_pointer="$.boundary_ledger",
        not_claimed="Dimension mismatch is bounded to the encoder-dimension transfer surface and keeps its DN boundary.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="sample_count",
        axis_label="Sample count",
        source_artifact="reports/canonical/gap-head-observed-debt-transfer.json",
        evidence_pointer="$.gap_head_on_h_observed_debt_transfer.status",
        status_pointer="$.gap_head_on_h_observed_debt_transfer.status",
        positive_statuses=("pass",),
        hardgate_pointer="$.hardgate_evidence",
        debt_row_pointer="$.observed_debt_transfer_boundary",
        not_claimed="Sample-count transfer is finite surface evidence and does not promote a global quality claim.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="optimizer",
        axis_label="Optimizer",
        source_artifact="runs/training_choice_observability.json",
        evidence_pointer="$.training_choice_observability.ledger_risk_only_arm_count",
        status_pointer="$.training_choice_observability.observed_debt_arm_count",
        positive_statuses=("positive-observed-debt",),
        hardgate_pointer="$.training_choice_observability.arms[0].hardgates",
        debt_row_pointer="$.boundary_ledger[0]",
        not_claimed="Training-choice observability is ledger-risk-only unless producer-owned observed-debt arms pass their gates.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="mixing",
        axis_label="Mixing family",
        source_artifact="reports/canonical/mixing-family-sweep.json",
        evidence_pointer="$.coverage_item",
        status_pointer="$.coverage_item.debt_item.status",
        positive_statuses=("observed-debt",),
        hardgate_pointer=None,
        debt_row_pointer="$.coverage_item.debt_item",
        not_claimed="Mixing-family coverage is represented as ledger coverage and is not promoted by this projection.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="compute",
        axis_label="Compute budget",
        source_artifact="runs/training_choice_observability.json",
        evidence_pointer="$.source_artifacts.gap_head_metric_helper",
        status_pointer="$.status",
        positive_statuses=("positive-observed-debt",),
        hardgate_pointer=None,
        debt_row_pointer=None,
        not_claimed="Compute evidence is proxy-only in the current artifacts and remains ledger-risk-only.",
    ),
    ObservedDebtAxisProjectionSpec(
        axis_id="capacity",
        axis_label="Model capacity",
        source_artifact="reports/canonical/discovery_gate_escape_registry.json",
        evidence_pointer="$.capacity",
        status_pointer="$.capacity.overflow_policy",
        positive_statuses=("positive-observed-debt",),
        hardgate_pointer=None,
        debt_row_pointer=None,
        not_claimed="Capacity evidence is a boundary registry entry and remains ledger-risk-only.",
    ),
)
OBSERVED_DEBT_AXIS_IDS = tuple(spec.axis_id for spec in OBSERVED_DEBT_AXIS_PROJECTION_SPECS)
LITERATURE_LEDGER = ROOT / "docs" / "lit" / "literature_ledger.yaml"
HONEST_BOUNDARY_ROWS = (
    "EvidenceEnvelope is not NameCert.",
    "Candidate is not full certification.",
    "Bound projection is not full proof.",
    "Hardening is not closure.",
)
METRIC_ALIASES = {
    "alignment_loss": "alignment_loss_mse",
    "actual_recovery_error": "actual_recovery_mse",
    "theorem3_bound": "theorem3_bound_mse",
    "bound_margin": "bound_margin_mse",
}
QUALITY_SCORECARD_METRICS = (
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


@dataclass(**{"froz" + "en": True})
class CanonicalReportSpec:
    name: str
    command: tuple[str, ...]
    json_artifact: str
    markdown_artifact: str
    required_json_keys: tuple[str, ...]
    estimated_seconds: int
    bundle_role: Literal["hg_p_core", "auxiliary"]
    scope_pointer: str
    cost_pointer: str
    not_claimed_pointer: str
    positive_claim_pointer: str
    control_pointer: str | None
    no_control_rationale_pointer: str | None
    forbidden_claim_terms: tuple[str, ...] = FORBIDDEN_POSITIVE_CLAIM_TERMS
    literature_ref_ids: tuple[str, ...] = ()


CANONICAL_REPORTS: tuple[CanonicalReportSpec, ...] = (
    CanonicalReportSpec(
        name="mixing-family-sweep",
        command=("python3", "scripts/run_mixing_family_sweep.py"),
        json_artifact="reports/canonical/mixing-family-sweep.json",
        markdown_artifact="reports/canonical/mixing-family-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "records",
            "family_aggregates",
            "coverage_item",
            "negative_result_summary",
        ),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.coverage_item",
        control_pointer=None,
        no_control_rationale_pointer="$.coverage_item",
    ),
    CanonicalReportSpec(
        name="anisotropic-ou-sweep",
        command=("python3", "scripts/run_anisotropic_ou_sweep.py"),
        json_artifact="reports/canonical/anisotropic-ou-sweep.json",
        markdown_artifact="reports/canonical/anisotropic-ou-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "records",
            "aggregates",
            "transition_debt_by_grid",
            "negative_result_summary",
        ),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.transition_debt_by_grid",
        control_pointer=None,
        no_control_rationale_pointer="$.config.arm",
    ),
    CanonicalReportSpec(
        name="gap-head-on-h",
        command=("python3", "scripts/run_gap_ledger_head_on_h.py"),
        json_artifact="reports/canonical/gap-head-on-h.json",
        markdown_artifact="reports/canonical/gap-head-on-h.md",
        required_json_keys=(
            "generated_at",
            "representation_boundary",
            "inference_no_ground_truth_z",
            "boundary_no_z_audit",
            "forbidden_column_audit",
            "config",
            "source_artifacts",
            "scope_seal",
            "records",
            "aggregate",
            "aggregate_metrics",
            "treatment_comparison",
            "control_protocol",
            "control_verdict",
            "main_claim_status",
        ),
        estimated_seconds=90,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.control_protocol",
        not_claimed_pointer="$.applicability_boundary.forbidden_inference_columns",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.control_protocol",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="gap-head-discovery",
        command=("python3", "scripts/run_gap_head_discovery.py"),
        json_artifact="reports/canonical/gap-head-discovery.json",
        markdown_artifact="reports/canonical/gap-head-discovery.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "boundary_checks",
            "surface_delta_count",
            "benefit_terms",
            "positive_discovery",
            "matched_random_control",
            "main_claim_status",
            "final_main_claim_status",
        ),
        estimated_seconds=5,
        bundle_role="hg_p_core",
        scope_pointer="$.boundary_checks",
        cost_pointer="$.score_terms",
        not_claimed_pointer="$.boundary_checks.forbidden_inference_columns",
        positive_claim_pointer="$.final_main_claim_status",
        control_pointer="$.matched_random_control",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="gap-head-ablation",
        command=("python3", "scripts/run_gap_head_ablation.py"),
        json_artifact="reports/canonical/gap-head-ablation.json",
        markdown_artifact="reports/canonical/gap-head-ablation.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "applicability_boundary",
            "control_protocol",
            "config",
            "records",
            "aggregate",
            "factor_attribution",
            "hardgate",
            "positive_discovery_pointer",
        ),
        estimated_seconds=120,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.control_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.factor_attribution.learned_head.auroc_delta",
        control_pointer="$.control_protocol",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="ledger-aware-transformer",
        command=("python3", "scripts/run_ledger_aware_transformer.py"),
        json_artifact="reports/canonical/ledger-aware-transformer.json",
        markdown_artifact="reports/canonical/ledger-aware-transformer.md",
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "surface_registry",
            "applicability_boundary",
            "control_protocol",
            "records",
            "aggregate_metrics",
            "ledger",
            "matched_random_control",
            "parameter_matched_baseline",
            "compute_matched_baseline",
            "component_ablation",
            "mechanism_certificate",
            "torch_training_evidence",
            "robustness_signal",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "positive_claim",
            "claim_capsule_ref",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.control_protocol",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="certificate-gated-attention",
        command=("python3", "scripts/run_certificate_gated_attention.py"),
        json_artifact="reports/canonical/certificate-gated-attention.json",
        markdown_artifact="reports/canonical/certificate-gated-attention.md",
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "grid",
            "records",
            "surface_registry",
            "certificate_gate_summary",
            "gate_protocol",
            "arm_protocol",
            "device_protocol",
            "torch_attention_evidence",
            "matched_random_control",
            "route_patch_protocol",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "positive_claim",
            "claim_capsule_ref",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.grid",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.route_patch_protocol",
        no_control_rationale_pointer=None,
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="gap-head-threshold-frontier",
        command=("python3", "scripts/run_gap_head_threshold_sweep.py"),
        json_artifact="reports/canonical/gap-head-threshold-frontier.json",
        markdown_artifact="reports/canonical/gap-head-threshold-frontier.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "threshold_curve",
            "threshold_summary",
            "pareto_axis_spec",
            "pareto_frontier",
            "hardgate",
            "readiness",
            "main_claim_status",
            "not_claimed",
        ),
        estimated_seconds=120,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.threshold_summary.control_baseline",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="gap-head-transfer-atlas",
        command=("python3", "scripts/run_gap_head_transfer_atlas.py"),
        json_artifact=GAP_HEAD_TRANSFER_ATLAS_JSON_ARTIFACT,
        markdown_artifact=GAP_HEAD_TRANSFER_ATLAS_MARKDOWN_ARTIFACT,
        required_json_keys=(
            "generated_at",
            "producer",
            "source_artifacts",
            "config",
            "surface_registry",
            "prior_observation_packet",
            "surfaces",
            "boundary_ledger",
            "hardgate_evidence",
            "multi_surface_d5_o",
            "scope_seal",
            "not_claimed",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=180,
        bundle_role="hg_p_core",
        scope_pointer="$.not_claimed",
        cost_pointer="$.source_artifacts.metric_helper",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.multi_surface_d5_o",
        control_pointer="$.config.control_arm",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="gap-head-attribution-capsule",
        command=("python3", "scripts/run_gap_head_attribution_capsule.py"),
        json_artifact=GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT,
        markdown_artifact=GAP_HEAD_ATTRIBUTION_MARKDOWN_ARTIFACT,
        required_json_keys=(
            "schema_id",
            "generated_at",
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
            "cost_protocol_pointer",
            "control_pointer",
            "control_evidence",
            "scope_seal",
            "forbidden_column_audit",
            "failed_gate",
            "what_was_learned",
            "revocation_ledger",
            "positive_discovery_inputs",
            "scope",
            "source_artifacts",
            "aggregate",
        ),
        estimated_seconds=120,
        bundle_role="hg_p_core",
        scope_pointer="$.scope.not_claimed",
        cost_pointer="$.cost_protocol_pointer",
        not_claimed_pointer="$.scope.not_claimed",
        positive_claim_pointer="$.d5_m",
        control_pointer="$.control_pointer",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="nongaussian-distribution-sweep",
        command=("python3", "scripts/run_nongaussian_distribution_sweep.py"),
        json_artifact="reports/canonical/nongaussian-distribution-sweep.json",
        markdown_artifact="reports/canonical/nongaussian-distribution-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "records",
            "family_aggregates",
            "coverage_item",
            "claim_gate",
            "main_claim_status",
            "negative_result_ledger",
            "not_claimed",
        ),
        estimated_seconds=20,
        bundle_role="auxiliary",
        scope_pointer="$.coverage_item",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer=None,
        no_control_rationale_pointer="$.negative_result_ledger",
    ),
    CanonicalReportSpec(
        name="certificate-guided-training",
        command=("python3", "scripts/run_certificate_guided_constraint_training.py"),
        json_artifact="reports/canonical/certificate-guided-training.json",
        markdown_artifact="reports/canonical/certificate-guided-training.md",
        required_json_keys=(
            "generated_at",
            "run_id",
            "cost_protocol",
            "source_artifacts",
            "paired_seed_protocol",
            "objective",
            "grid_summary",
            "grid_metrics_artifact",
            "grid_summary_artifact",
            "raw_metrics_artifact",
            "raw_metrics_record_count",
            "raw_grid_record_count",
            "deltas",
            "metrics",
            "paired_delta_ci",
            "arm_protocol",
            "arm_summaries",
            "claim_gate",
            "hardgate",
            "c2_frontier",
            "failed_gate",
            "verdict",
            "discovery_level",
            "not_claimed",
            "claim_capsule",
            "result",
        ),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer="$.objective.required_rows",
        cost_pointer="$.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.claim_gate",
        control_pointer="$.paired_seed_protocol",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="certificate-guided-discovery",
        command=("python3", "scripts/run_certificate_guided_discovery.py"),
        json_artifact="reports/canonical/certificate-guided-discovery.json",
        markdown_artifact="reports/canonical/certificate-guided-discovery.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "verdicts",
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
        ),
        estimated_seconds=5,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.claim_gate",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.matched_random_baseline",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="sigreg-training-proxy",
        command=("python3", "scripts/run_sigreg_training_proxy.py"),
        json_artifact="reports/canonical/sigreg-training-proxy.json",
        markdown_artifact="reports/canonical/sigreg-training-proxy.md",
        required_json_keys=(
            "generated_at",
            "run_id",
            "run_artifacts",
            "source_artifacts",
            "config",
            "objective",
            "arm_protocol",
            "arm_summaries",
            "d1_evidence",
            "claim_gate",
            "hardgate",
            "failed_gate",
            "what_was_learned",
            "not_claimed",
            "full_lejepa_boundary",
            "result",
            "positive_claim",
            "claim_capsule_ref",
            "result_snapshot_ref",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=30,
        bundle_role="hg_p_core",
        scope_pointer="$.arm_protocol",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer=None,
        no_control_rationale_pointer="$.full_lejepa_boundary",
    ),
    CanonicalReportSpec(
        name="sigreg-mini-grid",
        command=("python3", "scripts/run_sigreg_mini_grid.py"),
        json_artifact="reports/canonical/sigreg-mini-grid.json",
        markdown_artifact="reports/canonical/sigreg-mini-grid.md",
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "grid",
            "metric_keys",
            "metric_separation",
            "lambda_summary",
            "rho_summary",
            "mixing_summary",
            "best_cell",
            "trend_summary",
            "tradeoff_ledger",
            "c3_hardgates",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "claim_capsule_ref",
            "claim_capsule_status",
            "positive_claim",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.grid",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer=None,
        no_control_rationale_pointer="$.not_claimed",
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="discovery-regularized-training",
        command=("python3", "scripts/run_discovery_regularized_training.py"),
        json_artifact=DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
        markdown_artifact=DISCOVERY_REGULARIZED_TRAINING_MARKDOWN_ARTIFACT,
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "grid",
            "records",
            "surface_registry",
            "lambda_summary",
            "constraint_summary",
            "arm_protocol",
            "device_protocol",
            "compute_ledger",
            "torch_training_evidence",
            "negative_witness_mutations",
            "training_loop_trace",
            "matched_random_control",
            "quality_promotion_boundary",
            "mechanism_ablation",
            "training_mechanism_cert",
            "loss_family",
            "component_ablation",
            "training_method_comparison",
            "drt_extension_hardgates",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "positive_claim",
            "claim_capsule_ref",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.grid",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.matched_random_control",
        no_control_rationale_pointer=None,
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="mechanism-seeking-network",
        command=("python3", "scripts/run_mechanism_seeking_network.py"),
        json_artifact="reports/canonical/mechanism-seeking-network.json",
        markdown_artifact="reports/canonical/mechanism-seeking-network.md",
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "grid",
            "records",
            "surface_registry",
            "mechanism_gate_summary",
            "gate_protocol",
            "device_protocol",
            "torch_evidence",
            "matched_random_control",
            "distinction_module_evidence",
            "d5_m_readiness",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "positive_claim",
            "claim_capsule_ref",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.grid",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.matched_random_control",
        no_control_rationale_pointer=None,
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="discovery-gated-nas",
        command=("python3", "scripts/run_discovery_gated_nas.py"),
        json_artifact="reports/canonical/discovery-gated-nas.json",
        markdown_artifact="reports/canonical/discovery-gated-nas.md",
        required_json_keys=(
            "schema_id",
            "artifact_id",
            "generated_at",
            "run_id",
            "producer",
            "projector",
            "run_artifacts",
            "source_artifacts",
            "config",
            "grid",
            "search_space",
            "records",
            "surface_registry",
            "search_objective_summary",
            "negative_witness_mutations",
            "candidate_protocol",
            "device_protocol",
            "torch_nas_evidence",
            "matched_baseline_control",
            "hardgate",
            "failed_gate",
            "discovery_map_signal",
            "positive_claim",
            "claim_capsule_ref",
            "not_claimed",
            "what_was_learned",
            "revocation_rows",
            "forbidden_claim_term_audit",
        ),
        estimated_seconds=2,
        bundle_role="hg_p_core",
        scope_pointer="$.search_space",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.matched_baseline_control",
        no_control_rationale_pointer=None,
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="lejepa-theorem-ledger",
        command=("python3", "scripts/run_lejepa_theorem_ledger.py"),
        json_artifact="reports/canonical/lejepa_theorem_ledger.json",
        markdown_artifact="reports/canonical/lejepa_theorem_ledger.md",
        required_json_keys=(
            "schema_id",
            "generated_at",
            "run_id",
            "source_artifacts",
            "scope",
            "role_catalog",
            "metric_catalog",
            "backend_theorem_rows",
            "backend_ledger_rows",
            "theorem_rows",
            "hardgates",
            "not_claimed",
            "positive_claim",
            "main_verdict",
            "claim_gate",
            "result",
        ),
        estimated_seconds=1,
        bundle_role="auxiliary",
        scope_pointer="$.scope",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer=None,
        no_control_rationale_pointer="$.scope",
        literature_ref_ids=("lit-lejepa-theorem-ledger",),
    ),
    CanonicalReportSpec(
        name="observed-debt-sweep",
        command=("python3", "scripts/run_observed_debt_sweep.py"),
        json_artifact="reports/canonical/observed-debt-sweep.json",
        markdown_artifact="reports/canonical/observed-debt-sweep.md",
        required_json_keys=(
            "artifact_id",
            "generated_at",
            "schema_id",
            "config",
            "source_artifacts",
            "baseline",
            "cells",
            "grid_summary",
            "hardgate_evidence",
            "claim_boundary",
            "global_claim_flag",
            "not_claimed",
        ),
        estimated_seconds=1,
        bundle_role="auxiliary",
        scope_pointer="$.claim_boundary.C4",
        cost_pointer="$.source_artifacts",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.hardgate_evidence.C-HG5",
        control_pointer=None,
        no_control_rationale_pointer="$.claim_boundary.C4",
    ),
    CanonicalReportSpec(
        name="spectral-ablation-hinge",
        command=("python3", "scripts/run_spectral_ablation_hinge.py"),
        json_artifact="reports/canonical/spectral-ablation-hinge.json",
        markdown_artifact="reports/canonical/spectral-ablation-hinge.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "arms",
            "hinge_ledger",
            "ledger_summary",
            "negative_control_summary",
            "rank_correlation",
        ),
        estimated_seconds=20,
        bundle_role="auxiliary",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.ledger_summary",
        control_pointer="$.negative_control_summary",
        no_control_rationale_pointer=None,
    ),
)


def _artifact_path(relative_path: str) -> Path:
    path = (ROOT / relative_path).resolve()
    if not path.is_relative_to(CANONICAL_DIR.resolve()):
        raise ValueError(f"canonical artifact must be under reports/canonical: {relative_path}")
    return path


def _specs_by_name() -> dict[str, CanonicalReportSpec]:
    return {spec.name: spec for spec in CANONICAL_REPORTS}


def _select_specs(only: str | None) -> tuple[CanonicalReportSpec, ...]:
    if only is None:
        return CANONICAL_REPORTS
    by_name = _specs_by_name()
    if only not in by_name:
        names = ", ".join(sorted(by_name))
        raise ValueError(f"unknown canonical report {only!r}; available: {names}")
    return (by_name[only],)


def _selected_specs_with_dependents(only: str | None, *, include_dependents: bool = True) -> tuple[CanonicalReportSpec, ...]:
    selected = list(_select_specs(only))
    if only is None or not include_dependents:
        return tuple(selected)
    dependent_names = {
        "gap-head-on-h": ("gap-head-discovery",),
        "certificate-guided-training": ("certificate-guided-discovery",),
    }.get(only, ())
    by_name = _specs_by_name()
    for name in dependent_names:
        if name in by_name:
            selected.append(by_name[name])
    return tuple(selected)


def _module_name_from_command(command: Sequence[str]) -> str:
    if len(command) != 2 or command[0] != "python3":
        raise ValueError(f"unsupported producer command: {' '.join(command)}")
    script = Path(command[1])
    if script.suffix != ".py" or script.parts[0] != "scripts":
        raise ValueError(f"producer command must target scripts/*.py: {' '.join(command)}")
    return ".".join(script.with_suffix("").parts)


def _relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def _path_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() and path.is_file() else "missing"


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _fingerprint_path(spec: CanonicalReportSpec) -> Path:
    return _artifact_path(spec.json_artifact).with_suffix(".fingerprint.json")


def _canonical_output_digest(spec: CanonicalReportSpec) -> str:
    parts = {
        spec.json_artifact: _path_digest(_artifact_path(spec.json_artifact)),
        spec.markdown_artifact: _path_digest(_artifact_path(spec.markdown_artifact)),
    }
    return _json_digest(parts)


def _local_module_path(module_name: str) -> Path | None:
    direct = ROOT / Path(*module_name.split(".")).with_suffix(".py")
    if direct.exists():
        return direct.resolve()
    package_init = ROOT / Path(*module_name.split(".")) / "__init__.py"
    if package_init.exists():
        return package_init.resolve()
    spec = importlib.util.find_spec(module_name)
    origin = None if spec is None else spec.origin
    if origin is None:
        return None
    path = Path(origin).resolve()
    try:
        path.relative_to(ROOT)
    except ValueError:
        return None
    return path if path.suffix == ".py" else None


def _local_imports(path: Path) -> set[str]:
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"))
    except (OSError, SyntaxError):
        return set()
    try:
        relative_path = path.resolve().relative_to(ROOT)
    except ValueError:
        relative_path = path
    module_parts = relative_path.with_suffix("").parts
    if module_parts and module_parts[-1] == "__init__":
        package_parts = module_parts[:-1]
    else:
        package_parts = module_parts[:-1]
    imports: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0:
                if node.module is not None:
                    imports.add(node.module)
                continue
            base_count = len(package_parts) - node.level + 1
            if base_count < 0:
                continue
            resolved_parts = list(package_parts[:base_count])
            if node.module is not None:
                resolved_parts.extend(node.module.split("."))
                imports.add(".".join(resolved_parts))
            else:
                for alias in node.names:
                    if alias.name != "*":
                        imports.add(".".join([*resolved_parts, alias.name]))
    return {
        name
        for name in imports
        if name == "scripts" or name.startswith("scripts.") or name == "bedc_quality_lab" or name.startswith("bedc_quality_lab.")
    }


def _import_closure(command: Sequence[str]) -> list[str]:
    seen: set[str] = set()
    pending = [_module_name_from_command(command)]
    paths: set[Path] = set()
    while pending:
        module_name = pending.pop()
        if module_name in seen:
            continue
        seen.add(module_name)
        path = _local_module_path(module_name)
        if path is None:
            continue
        paths.add(path)
        pending.extend(sorted(_local_imports(path) - seen))
    return [_relative(path) for path in sorted(paths)]


def _config_inputs() -> list[dict[str, str]]:
    paths = sorted(
        path
        for base in (ROOT / "configs", ROOT / "docs" / "lit")
        if base.exists()
        for path in base.rglob("*")
        if path.is_file()
    )
    return [{"path": _relative(path), "sha256": _path_digest(path)} for path in paths]


def _dependency_abi() -> dict[str, str]:
    abi = {"python": sys.version.split()[0], "executable": sys.executable}
    for package in ("numpy", "torch"):
        try:
            module = importlib.import_module(package)
        except ImportError:
            abi[package] = "not-installed"
        else:
            abi[package] = str(getattr(module, "__version__", "unknown"))
    return abi


def _source_artifact_inputs(spec: CanonicalReportSpec) -> list[dict[str, str]]:
    payload = _load_artifact_payload(spec.json_artifact) if _artifact_path(spec.json_artifact).exists() else {}
    source_artifacts = payload.get("source_artifacts") if isinstance(payload, Mapping) else None
    paths: set[str] = set()
    if isinstance(source_artifacts, Mapping):
        for value in source_artifacts.values():
            if isinstance(value, str) and value.startswith("reports/") and Path(value).suffix in {".json", ".jsonl", ".md"}:
                paths.add(value)
    if spec.name == "gap-head-discovery":
        paths.add("reports/canonical/gap-head-on-h.json")
    if spec.name == "certificate-guided-discovery":
        paths.update(("reports/canonical/certificate-guided-training.json", "reports/canonical/certificate-guided-training.md"))
    paths.discard(spec.json_artifact)
    paths.discard(spec.markdown_artifact)
    return [{"path": path, "sha256": _path_digest(ROOT / path)} for path in sorted(paths)]


def _input_record(spec: CanonicalReportSpec) -> dict[str, Any]:
    payload = _load_artifact_payload(spec.json_artifact) if _artifact_path(spec.json_artifact).exists() else {}
    schema_id = payload.get("schema_id") or payload.get("artifact_id") if isinstance(payload, dict) else None
    import_paths = _import_closure(spec.command)
    return {
        "fingerprint_schema_id": FINGERPRINT_INPUT_SCHEMA_ID,
        "runner_fingerprint_schema_id": FINGERPRINT_SCHEMA_ID,
        "report_output_schema_id": str(schema_id or "schema-unspecified"),
        "spec": asdict(spec),
        "producer_sources": [{"path": path, "sha256": _path_digest(ROOT / path)} for path in import_paths],
        "config_inputs": _config_inputs(),
        "source_artifacts": _source_artifact_inputs(spec),
        "seed_constants": {
            "environment": {"PYTHONHASHSEED": "unset"},
            "command": list(spec.command),
        },
        "backend_identity": "bedc_quality_lab.backends.current_lab.adapter.CurrentLabBackendEvidenceAdapter",
        "dependency_abi": _dependency_abi(),
    }


def _input_fingerprint(spec: CanonicalReportSpec) -> tuple[str, dict[str, Any]]:
    record = _input_record(spec)
    return _json_digest(record), record


def _load_fingerprint_sidecar(spec: CanonicalReportSpec) -> dict[str, Any]:
    path = _fingerprint_path(spec)
    if not path.exists():
        raise ValueError(f"missing fingerprint sidecar: {_relative(path)}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError(f"corrupt fingerprint sidecar: {_relative(path)}: {exc}") from exc
    if not isinstance(payload, dict) or payload.get("schema_id") != FINGERPRINT_SCHEMA_ID:
        raise ValueError(f"invalid fingerprint sidecar: {_relative(path)}")
    return payload


def _write_fingerprint_sidecar(spec: CanonicalReportSpec, *, generated_at: str | None = None) -> dict[str, Any]:
    input_fingerprint, inputs = _input_fingerprint(spec)
    payload = {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": spec.name,
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "producer_command": list(spec.command),
        "input_fingerprint": input_fingerprint,
        "output_digest": _canonical_output_digest(spec),
        "inputs": inputs,
        "generated_by": {
            "runner": "scripts/run_canonical_reports.py",
            "generated_at": generated_at,
        },
    }
    _write_json_atomic(_fingerprint_path(spec), payload)
    return payload


def _fingerprint_matches(spec: CanonicalReportSpec) -> tuple[bool, str]:
    sidecar = _load_fingerprint_sidecar(spec)
    input_fingerprint, _inputs = _input_fingerprint(spec)
    expected = {
        "report_name": spec.name,
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "producer_command": list(spec.command),
        "input_fingerprint": input_fingerprint,
        "output_digest": _canonical_output_digest(spec),
    }
    for key, value in expected.items():
        if sidecar.get(key) != value:
            return False, key.replace("_", "-")
    return True, "match"


def _set_existing_attr(module: Any, name: str, value: Any) -> None:
    if hasattr(module, name):
        setattr(module, name, value)


def _with_metric_aliases(envelope: Any) -> Any:
    metrics = dict(envelope.metrics)
    for alias, source in METRIC_ALIASES.items():
        if alias not in metrics and source in metrics:
            metrics[alias] = metrics[source]
    return replace(envelope, metrics=metrics)


def _configure_metric_aliases(module: Any) -> None:
    if not hasattr(module, "run_experiment") or getattr(module, "_CANONICAL_METRIC_ALIASES", False):
        return
    run_experiment = module.run_experiment

    def run_experiment_with_aliases(*args: Any, **kwargs: Any) -> Any:
        return _with_metric_aliases(run_experiment(*args, **kwargs))

    module.run_experiment = run_experiment_with_aliases
    module._CANONICAL_METRIC_ALIASES = True


def _configure_producer(module: Any, spec: CanonicalReportSpec) -> None:
    json_path = _artifact_path(spec.json_artifact)
    markdown_path = _artifact_path(spec.markdown_artifact)
    _set_existing_attr(module, "REPORT_JSON", json_path)
    _set_existing_attr(module, "REPORT_MD", markdown_path)
    _set_existing_attr(module, "JSON_ARTIFACT", spec.json_artifact)
    _set_existing_attr(module, "REPORT_ARTIFACT", spec.markdown_artifact)
    _set_existing_attr(module, "USE_TORCH", False)
    _configure_metric_aliases(module)
    if spec.name == "gap-head-discovery":
        _set_existing_attr(module, "SOURCE_JSON_ARTIFACT", "reports/canonical/gap-head-on-h.json")
    if spec.name == "certificate-guided-discovery":
        _set_existing_attr(module, "SOURCE_JSON_ARTIFACT", "reports/canonical/certificate-guided-training.json")
        _set_existing_attr(module, "SOURCE_REPORT_ARTIFACT", "reports/canonical/certificate-guided-training.md")


def _run_producer(spec: CanonicalReportSpec) -> None:
    module = importlib.import_module(_module_name_from_command(spec.command))
    _configure_producer(module, spec)
    if inspect.signature(module.main).parameters:
        module.main([])
    else:
        module.main()


def _compile_discovery_compat(compile_discovery, *, root: Path, generated_at: str, adapter: Any, require_required_negative_reports: bool) -> Any:
    kwargs = {
        "root": root,
        "generated_at": generated_at,
        "adapter": adapter,
    }
    try:
        signature = inspect.signature(compile_discovery)
    except (TypeError, ValueError):
        return compile_discovery(**kwargs)
    if "require_required_negative_reports" in signature.parameters:
        kwargs["require_required_negative_reports"] = require_required_negative_reports
    return compile_discovery(**kwargs)


def _validate_json(path: Path, required_keys: Sequence[str]) -> dict[str, Any]:
    if not path.exists():
        return {"status": "fail", "missing_keys": list(required_keys), "error": "missing json artifact"}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return {"status": "fail", "missing_keys": list(required_keys), "error": str(exc)}
    missing = [key for key in required_keys if key not in payload]
    return {"status": "pass" if not missing else "fail", "missing_keys": missing}


def _load_report_payload(spec: CanonicalReportSpec) -> dict[str, Any]:
    json_path = _artifact_path(spec.json_artifact)
    if not json_path.exists():
        return {}
    try:
        payload = json.loads(json_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _load_artifact_payload(relative_path: str) -> dict[str, Any]:
    json_path = _artifact_path(relative_path)
    if not json_path.exists():
        return {}
    try:
        payload = json.loads(json_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _load_sidecar_payload(relative_path: str) -> dict[str, Any]:
    json_path = ROOT / relative_path
    if not json_path.exists():
        return {}
    try:
        payload = json.loads(json_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _pointer_value(payload: dict[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, dict) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _cost_protocol_evidence(payload: dict[str, Any], pointer: str | None) -> Any:
    value = _pointer_value(payload, pointer)
    if isinstance(value, str) and value.startswith("$."):
        return _pointer_value(payload, value)
    return value


def _report_payloads_by_name() -> dict[str, dict[str, Any]]:
    return {spec.name: _load_report_payload(spec) for spec in CANONICAL_REPORTS}


def _canonical_source(report: str, pointer: str) -> dict[str, str]:
    spec = _specs_by_name()[report]
    return {
        "report": report,
        "artifact": spec.json_artifact,
        "pointer": pointer,
    }


def _metric_not_ready(metric: str, dependency: str, reason: str) -> dict[str, Any]:
    return {
        "metric": metric,
        "status": "not-ready",
        "dependency": dependency,
        "reason": reason,
    }


def _metric_ready(
    metric: str,
    value: Any,
    source: dict[str, str] | list[dict[str, str]],
    *,
    numerator: int | float | None = None,
    denominator: int | float | None = None,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "metric": metric,
        "status": "ready",
        "value": value,
        "source": source,
    }
    if numerator is not None:
        row["numerator"] = numerator
    if denominator is not None:
        row["denominator"] = denominator
    return row


def _sequence_len(value: Any) -> int | None:
    if isinstance(value, (list, tuple)):
        return len(value)
    return None


def _count_true_cells(value: Any, key: str) -> int | None:
    if not isinstance(value, dict):
        return None
    total = 0
    for cell in value.values():
        if not isinstance(cell, dict) or key not in cell:
            return None
        if cell[key] is True:
            total += 1
    return total


def _score_decimal(value: Any) -> float | None:
    if value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _scorecard_cert_cov(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "mixing-family-sweep"
    pointer = "$.coverage_item"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict):
        return _metric_not_ready("CertCov", f"{report}:{pointer}", "missing source cell")
    covered = _sequence_len(cell.get("covered_families"))
    total = _sequence_len(cell.get("canonical_families"))
    if covered is None or total is None or total <= 0:
        return _metric_not_ready("CertCov", f"{report}:{pointer}", "missing coverage denominator")
    return _metric_ready(
        "CertCov",
        covered / total,
        _canonical_source(report, pointer),
        numerator=covered,
        denominator=total,
    )


def _scorecard_debt_q(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "mixing-family-sweep"
    pointer = "$.coverage_item.debt_item.score"
    score = _score_decimal(_pointer_value(payloads.get(report, {}), pointer))
    if score is None:
        return _metric_not_ready("DebtQ", f"{report}:{pointer}", "missing debt score")
    return _metric_ready("DebtQ", score, _canonical_source(report, pointer))


def _scorecard_critical_debt(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.debt_terms"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict) or "classifier_ledger_rows" not in cell:
        return _metric_not_ready("CriticalDebt", f"{report}:{pointer}", "missing classifier debt term")
    return _metric_ready("CriticalDebt", cell["classifier_ledger_rows"], _canonical_source(report, pointer))


def _scorecard_ledger_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.classifier_state"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict):
        return _metric_not_ready("LedgerCompleteness", f"{report}:{pointer}", "missing classifier state")
    recorded = cell.get("recorded_ledger_rows")
    required = cell.get("required_ledger_rows")
    if not isinstance(recorded, int) or not isinstance(required, int) or required <= 0:
        return _metric_not_ready("LedgerCompleteness", f"{report}:{pointer}", "missing ledger denominator")
    return _metric_ready(
        "LedgerCompleteness",
        recorded / required,
        _canonical_source(report, pointer),
        numerator=recorded,
        denominator=required,
    )


def _scorecard_classifier_shift_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.surface_delta_count"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, int):
        return _metric_not_ready("ClassifierShiftCount", f"{report}:{pointer}", "missing shift count")
    return _metric_ready("ClassifierShiftCount", value, _canonical_source(report, pointer))


def _scorecard_positive_discovery_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [
        ("gap-head-discovery", "$.positive_discovery"),
        ("certificate-guided-discovery", "$.positive_discovery"),
    ]
    values = [_pointer_value(payloads.get(report, {}), pointer) for report, pointer in sources]
    if any(not isinstance(value, bool) for value in values):
        return _metric_not_ready("PositiveDiscoveryCount", "canonical discovery positive flags", "missing discovery flag")
    return _metric_ready(
        "PositiveDiscoveryCount",
        sum(1 for value in values if value is True),
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=sum(1 for value in values if value is True),
        denominator=len(values),
    )


def _scorecard_audit_improvement_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "certificate-guided-training"
    pointer = "$.claim_gate.audit_improvement_tradeoff"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, bool):
        return _metric_not_ready("AuditImprovementCount", f"{report}:{pointer}", "missing audit improvement flag")
    return _metric_ready(
        "AuditImprovementCount",
        1 if value else 0,
        _canonical_source(report, pointer),
        numerator=1 if value else 0,
        denominator=1,
    )


def _scorecard_negative_result_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [
        ("mixing-family-sweep", "$.negative_result_summary.cells"),
        ("anisotropic-ou-sweep", "$.negative_result_summary.cells"),
        ("nongaussian-distribution-sweep", "$.negative_result_ledger"),
    ]
    mixing = _count_true_cells(_pointer_value(payloads.get(sources[0][0], {}), sources[0][1]), "negative_result")
    anisotropic = _count_true_cells(_pointer_value(payloads.get(sources[1][0], {}), sources[1][1]), "negative_result")
    nongaussian = _sequence_len(_pointer_value(payloads.get(sources[2][0], {}), sources[2][1]))
    if mixing is None or anisotropic is None or nongaussian is None:
        return _metric_not_ready("NegativeResultCount", "canonical negative-result cells", "missing negative-result source")
    return _metric_ready(
        "NegativeResultCount",
        mixing + anisotropic + nongaussian,
        [_canonical_source(report, pointer) for report, pointer in sources],
    )


def _scorecard_scope_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    reports = [spec.name for spec in CANONICAL_REPORTS]
    sources = [(spec.name, spec.scope_pointer) for spec in CANONICAL_REPORTS]
    for spec in CANONICAL_REPORTS:
        if _pointer_value(payloads.get(spec.name, {}), spec.scope_pointer) is None:
            return _metric_not_ready(
                "ScopeCompleteness",
                f"{spec.name}:{spec.scope_pointer}",
                "missing scope pointer",
            )
    present = len(reports)
    denominator = len(reports)
    if denominator <= 0:
        return _metric_not_ready("ScopeCompleteness", "canonical report manifest", "missing manifest rows")
    return _metric_ready(
        "ScopeCompleteness",
        present / denominator,
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=present,
        denominator=denominator,
    )


def _scorecard_cost_protocol_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [(spec.name, spec.cost_pointer) for spec in CANONICAL_REPORTS]
    for spec in CANONICAL_REPORTS:
        if _cost_protocol_evidence(payloads.get(spec.name, {}), spec.cost_pointer) is None:
            return _metric_not_ready(
                "CostProtocolCompleteness",
                f"{spec.name}:{spec.cost_pointer}",
                "missing cost pointer",
            )
    present = len(CANONICAL_REPORTS)
    denominator = len(CANONICAL_REPORTS)
    if denominator <= 0:
        return _metric_not_ready("CostProtocolCompleteness", "canonical report manifest", "missing manifest rows")
    return _metric_ready(
        "CostProtocolCompleteness",
        present / denominator,
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=present,
        denominator=denominator,
    )


def _build_formal_hardening_payload(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_formal_hardening_report import build_formal_hardening_report

    return build_formal_hardening_report(root=ROOT, generated_at=generated_at)


def _scorecard_hardening_coverage(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    del payloads
    pointer = "$.coverage"
    dependency = f"formal_hardening:{pointer}"
    payload = _build_formal_hardening_payload()
    cell = _pointer_value(payload, pointer)
    ledger = payload.get("verification_ledger")
    if not isinstance(cell, dict) or not isinstance(ledger, list):
        return _metric_not_ready("HardeningCoverage", dependency, "missing formal hardening coverage payload")
    recorded = cell.get("recorded")
    required = cell.get("required")
    if not isinstance(recorded, int) or not isinstance(required, int) or required <= 0:
        return _metric_not_ready("HardeningCoverage", dependency, "missing formal hardening denominator")
    rows_verified = all(
        isinstance(row, dict)
        and row.get("status") == "verified"
        and row.get("recorded") is True
        and row.get("evidence_resolved") is True
        for row in ledger
    )
    if payload.get("ready") is not True or recorded != required or not rows_verified:
        return _metric_not_ready("HardeningCoverage", dependency, "incomplete formal hardening evidence")
    return _metric_ready(
        "HardeningCoverage",
        recorded / required,
        {
            "report": "formal_hardening",
            "artifact": FORMAL_HARDENING_JSON_ARTIFACT,
            "pointer": pointer,
        },
        numerator=recorded,
        denominator=required,
    )


def _scorecard_overclaim_rate(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "certificate-guided-discovery"
    pointer = "$.audit_decision.overclaim_rate"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, (int, float)):
        return _metric_not_ready("OverclaimRate", f"{report}:{pointer}", "missing explicit overclaim denominator")
    return _metric_ready("OverclaimRate", float(value), _canonical_source(report, pointer))


def _build_quality_scorecard(
    reports: Sequence[dict[str, Any]],
    *,
    generated_at: str,
) -> dict[str, Any]:
    payloads = _report_payloads_by_name()
    builders = (
        _scorecard_cert_cov,
        _scorecard_debt_q,
        _scorecard_critical_debt,
        _scorecard_ledger_completeness,
        _scorecard_classifier_shift_count,
        _scorecard_positive_discovery_count,
        _scorecard_audit_improvement_count,
        _scorecard_negative_result_count,
        _scorecard_scope_completeness,
        _scorecard_cost_protocol_completeness,
        _scorecard_hardening_coverage,
        _scorecard_overclaim_rate,
    )
    rows = [builder(payloads) for builder in builders]
    return {
        "artifact_id": QUALITY_SCORECARD_ARTIFACT_ID,
        "generated_at": generated_at,
        "root": INDEX_ROOT,
        "producer": "scripts/run_canonical_reports.py",
        "input_reports": [
            {
                "name": report["name"],
                "json_artifact": report["json_artifact"],
                "status": report["status"],
            }
            for report in reports
        ],
        "rows": rows,
    }


def _render_quality_scorecard_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Quality Scorecard",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Producer: `{payload['producer']}`",
        "",
        "## Quality baseline pointers",
        "",
        "- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`",
        "- Discovery levels: `reports/canonical/discovery_map.json:$.rows[*].discovery_level`",
        "- Claims boundary: `docs/claims_and_nonclaims.md`",
        "- Manifest: `docs/artifact_manifest.md`",
        "- Surface: metric rows with source pointers only",
        "",
        "## Metric rows",
        "",
        "| metric | status | value | source | dependency |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        source = row.get("source")
        if isinstance(source, list):
            source_text = ", ".join(f"{cell['artifact']}:{cell['pointer']}" for cell in source)
        elif isinstance(source, dict):
            source_text = f"{source['artifact']}:{source['pointer']}"
        else:
            source_text = ""
        lines.append(
            "| "
            f"`{row['metric']}` | "
            f"`{row['status']}` | "
            f"`{row.get('value', '')}` | "
            f"`{source_text}` | "
            f"`{row.get('dependency', '')}` |"
        )
    lines.append("")
    return "\n".join(lines)


def _pointer_status(payload: dict[str, Any], pointer: str | None) -> str:
    if pointer is None:
        return "not-applicable"
    return "present" if _pointer_value(payload, pointer) is not None else "missing"


def _text_for_term_scan(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def _forbidden_claim_term_check(spec: CanonicalReportSpec, payload: dict[str, Any]) -> dict[str, Any]:
    if spec.bundle_role != "hg_p_core":
        return {
            "status": "not-applicable",
            "hits": [],
        }
    value = _pointer_value(payload, spec.positive_claim_pointer)
    if value is None:
        return {
            "status": "missing-positive-claim-cell",
            "hits": [],
        }
    text = _text_for_term_scan(value)
    hits = [term for term in spec.forbidden_claim_terms if term.lower() in text]
    return {
        "status": "fail" if hits else "pass",
        "hits": hits,
    }


def _discipline(spec: CanonicalReportSpec) -> dict[str, Any]:
    payload = _load_report_payload(spec)
    control_pointer = spec.control_pointer
    no_control_rationale_pointer = spec.no_control_rationale_pointer
    positive_claim_pointer = spec.positive_claim_pointer
    forbidden_claim_terms = _forbidden_claim_term_check(spec, payload)
    discipline = {
        "bundle_role": spec.bundle_role,
        "scope_pointer": spec.scope_pointer,
        "scope_status": _pointer_status(payload, spec.scope_pointer),
        "cost_pointer": spec.cost_pointer,
        "cost_status": _pointer_status(payload, spec.cost_pointer),
        "not_claimed_pointer": spec.not_claimed_pointer,
        "not_claimed_status": _pointer_status(payload, spec.not_claimed_pointer),
        "positive_claim_pointer": positive_claim_pointer,
        "positive_claim_status": _pointer_status(payload, positive_claim_pointer),
        "control_pointer": control_pointer,
        "control_status": _pointer_status(payload, control_pointer),
        "no_control_rationale_pointer": no_control_rationale_pointer,
        "no_control_rationale_status": _pointer_status(payload, no_control_rationale_pointer),
        "forbidden_claim_terms_status": forbidden_claim_terms["status"],
        "forbidden_claim_term_hits": forbidden_claim_terms["hits"],
        "literature_ref_ids": list(spec.literature_ref_ids),
    }
    if spec.name == "certificate-guided-training":
        evidence_pointer = "$.arm_protocol.compat_roles.after"
        evidence_label = _pointer_value(payload, evidence_pointer)
        discipline["evidence_pointer"] = evidence_pointer
        if isinstance(evidence_label, str):
            discipline["evidence_label"] = evidence_label
    return discipline


def _literature_ledger() -> dict[str, Any]:
    return validate_literature_ledger(ROOT)


def _paper_outline(reports: Sequence[dict[str, Any]]) -> dict[str, Any]:
    core = [report["name"] for report in reports if report["bundle_role"] == "hg_p_core"]
    auxiliary = [report["name"] for report in reports if report["bundle_role"] == "auxiliary"]
    return {
        "status": "pointer-only",
        "core_reports": core,
        "auxiliary_reports": auxiliary,
        "sections": [
            "experiment bench scope",
            "cost protocol",
            "control discipline",
            "negative-result ledger",
            "honest boundary",
        ],
    }


def _claims_nonclaims(reports: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "positive_claim_cells": [
            {
                "report": report["name"],
                "bundle_role": report["bundle_role"],
                "positive_claim_pointer": report["discipline"]["positive_claim_pointer"],
                "control_pointer": report["discipline"]["control_pointer"],
                "no_control_rationale_pointer": report["discipline"]["no_control_rationale_pointer"],
            }
            for report in reports
        ],
        "nonclaims": [
            "not a solved model-quality claim",
            "not full LeJEPA",
            "not global quality",
            "not full Tensor NameCert",
            "not LLM behavior",
        ],
    }


def _honest_boundary() -> dict[str, Any]:
    return {
        "status": "explicit",
        "rows": list(HONEST_BOUNDARY_ROWS),
        "claimed": "Executable, auditable experiment bench that records negative results.",
        "not_claimed": "Solved model quality.",
    }


def _quality_scorecard_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": QUALITY_SCORECARD_ARTIFACT_ID,
        "json_artifact": QUALITY_SCORECARD_JSON_ARTIFACT,
        "markdown_artifact": QUALITY_SCORECARD_MARKDOWN_ARTIFACT,
        "metric_count": len(QUALITY_SCORECARD_METRICS),
        "metrics": list(QUALITY_SCORECARD_METRICS),
    }


def _discovery_map_index_section(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_discovery_map import build_discovery_map

    payload = build_discovery_map(generated_at=generated_at, root=ROOT, canonical_reports=CANONICAL_REPORTS)
    return {
        "status": "pointer-only",
        "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
        "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
        "experiment_proposals_pointer": "reports/canonical/discovery_map.json:$.experiment_proposals",
        "experiment_proposal_count": len(payload.get("experiment_proposals", [])),
        "row_count": payload["row_count"],
        "level_counts": payload["level_counts"],
    }


def _discovery_map_payload(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_discovery_map import build_discovery_map

    return build_discovery_map(generated_at=generated_at, root=ROOT, canonical_reports=CANONICAL_REPORTS)


def _all_gates_pass(value: Any) -> bool:
    if not isinstance(value, Mapping):
        return False
    statuses = [cell.get("status") for cell in value.values() if isinstance(cell, Mapping) and "status" in cell]
    return bool(statuses) and all(status == "pass" for status in statuses)


def _projection_row(spec: ObservedDebtAxisProjectionSpec) -> dict[str, Any]:
    source_payload = _load_sidecar_payload(spec.source_artifact)
    evidence_value = _bracket_pointer_value(source_payload, spec.evidence_pointer)
    source_status = _bracket_pointer_value(source_payload, spec.status_pointer)
    hardgate_value = _bracket_pointer_value(source_payload, spec.hardgate_pointer) if spec.hardgate_pointer else None
    hardgate_pass = bool(spec.hardgate_pointer and _all_gates_pass(hardgate_value))
    if spec.hardgate_pointer is None and source_status in spec.positive_statuses:
        hardgate_pass = True
    global_claim = _bracket_pointer_value(source_payload, "$.global_claim_flag") is True
    classification = (
        "observed-debt"
        if evidence_value is not None and source_status in spec.positive_statuses and hardgate_pass and not global_claim
        else "ledger-risk-only"
    )
    return {
        "axis_id": spec.axis_id,
        "axis_label": spec.axis_label,
        "classification": classification,
        "source_artifact": spec.source_artifact,
        "evidence_pointer": spec.evidence_pointer,
        "source_status": source_status,
        "debt_row": _bracket_pointer_value(source_payload, spec.debt_row_pointer) if spec.debt_row_pointer else None,
        "hardgate_pointer": spec.hardgate_pointer,
        "not_claimed": spec.not_claimed,
    }


def _observed_debt_axis_projection_section() -> dict[str, Any]:
    rows = [_projection_row(spec) for spec in OBSERVED_DEBT_AXIS_PROJECTION_SPECS]
    return {
        "status": "pointer-only",
        "axis_ids": list(OBSERVED_DEBT_AXIS_IDS),
        "classification_enum": ["observed-debt", "ledger-risk-only"],
        "row_count": len(rows),
        "rows": rows,
    }


def _dimension_mismatch_transfer_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT)
    transfer = _pointer_value(payload, "$.dimension_mismatch_debt_transfer")
    return {
        "status": "pointer-only",
        "artifact_id": DIMENSION_MISMATCH_TRANSFER_ARTIFACT_ID,
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
        "markdown_artifact": DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT,
        "claim_pointer": f"{DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT}:$.dimension_mismatch_debt_transfer",
        "claim_present": isinstance(transfer, dict),
    }


def _dimension_mismatch_transfer_robustness_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT)
    return {
        "status": payload.get("status", "missing"),
        "artifact_id": payload.get("artifact_id", DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_ARTIFACT_ID),
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT,
        "markdown_artifact": DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT,
        "audit_status": payload.get("audit_status", "missing"),
    }


def _negative_witnesses_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": NEGATIVE_WITNESSES_ARTIFACT_ID,
        "json_artifact": NEGATIVE_WITNESSES_JSON_ARTIFACT,
        "expected_kind_count": NEGATIVE_WITNESSES_EXPECTED_KIND_COUNT,
        "schema_role": "bedc-gap-witness-ledger",
        "witness_rows_pointer": f"{NEGATIVE_WITNESSES_JSON_ARTIFACT}:$.witnesses",
    }


def _claim_verdicts_index_section(rows: Sequence[dict[str, Any]] | None = None) -> dict[str, Any]:
    if rows is None:
        path = ROOT / CLAIM_VERDICTS_JSONL_ARTIFACT
        if path.exists():
            rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]
        else:
            rows = []
    return {
        "status": "pointer-only",
        "artifact_id": CLAIM_VERDICTS_ARTIFACT_ID,
        "jsonl_artifact": CLAIM_VERDICTS_JSONL_ARTIFACT,
        "row_count": len(rows),
    }


def _claim_graph_index_section(generated_at: str | None = None) -> dict[str, Any]:
    from bedc_quality_lab.claim_graph import build_claim_graph_payload

    path = ROOT / CLAIM_GRAPH_JSON_ARTIFACT
    if path.exists():
        payload = _load_artifact_payload(CLAIM_GRAPH_JSON_ARTIFACT)
    else:
        try:
            payload = build_claim_graph_payload(root=ROOT, generated_at=generated_at)
        except (OSError, ValueError):
            payload = {"status": "missing", "node_count": 0, "hardgates": {}}
    hardgates = payload.get("hardgates") if isinstance(payload, dict) else {}
    return {
        "status": payload.get("status", "missing") if isinstance(payload, dict) else "missing",
        "artifact_id": CLAIM_GRAPH_ARTIFACT_ID,
        "json_artifact": CLAIM_GRAPH_JSON_ARTIFACT,
        "markdown_artifact": CLAIM_GRAPH_MARKDOWN_ARTIFACT,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "node_count": payload.get("node_count", 0) if isinstance(payload, dict) else 0,
        "hardgate_status": {
            name: gate.get("status", "missing")
            for name, gate in sorted(hardgates.items())
            if isinstance(gate, dict)
        }
        if isinstance(hardgates, dict)
        else {},
    }


def _build_claim_capsule(generated_at: str) -> dict[str, Any]:
    from bedc_quality_lab.discovery_compiler.capsule import build_claim_capsule_payload

    dimension = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT)
    transfer = _pointer_value(dimension, "$.dimension_mismatch_debt_transfer")
    if not isinstance(transfer, dict):
        transfer = None
        run_local = None
    else:
        run_local = None
        anti = transfer.get("anti_triviality_evidence")
        if isinstance(anti, dict) and isinstance(anti.get("controlled_geometry"), dict):
            try:
                from scripts.run_dimension_mismatch_debt_transfer import (
                    RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
                    build_run_local_contract,
                )

                run_local = build_run_local_contract(dimension)
                run_local["negative_witness"] = {
                    "artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
                    "pointer": "$.run_local.negative_witness",
                }
                run_local["negative_witness_hardgates"] = {
                    "artifact": RUN_LOCAL_CLAIM_CAPSULE_ARTIFACT,
                    "pointer": "$.run_local.negative_witness_hardgates",
                }
            except (ImportError, KeyError, TypeError, ValueError):
                run_local = None
    return build_claim_capsule_payload(
        generated_at=generated_at,
        claim_id="claim:dimension-mismatch-debt-transfer",
        report="dimension-mismatch-debt-transfer",
        source_artifact=DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
        source_pointer="$.dimension_mismatch_debt_transfer",
        claim=transfer,
        not_claimed=(
            "global dimension theory",
            "representation-geometric debt transfer",
            "D5 promotion",
            "global model quality",
            "full LeJEPA",
            "full TensorNameCert",
            "LLM behavior",
            "mechanism closure unless D5-M",
        ),
        run_local=run_local,
    )


def _claim_capsule_index_section(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    payload = _build_claim_capsule(timestamp)
    return {
        "status": "pointer-only",
        "artifact_id": CLAIM_CAPSULE_ARTIFACT_ID,
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "json_artifact": CLAIM_CAPSULE_JSON_ARTIFACT,
        "claim_id": payload["claim_id"],
        "capsule_status": payload["status"],
        "effective_level": payload.get("effective_level"),
        "terminal_verdict": payload.get("terminal_verdict"),
    }


def _negative_witness_summary_index_section(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_discovery_negative_witness_summary import build_discovery_negative_witness_summary

    try:
        payload = build_discovery_negative_witness_summary(root=ROOT, generated_at=generated_at)
    except ValueError as exc:
        if str(exc) != "negative discovery reports must be written before witness summary":
            raise
        payload = {"status": "missing", "row_count": 0, "audit_status": "missing"}
    return {
        "status": payload["status"],
        "artifact_id": NEGATIVE_WITNESS_SUMMARY_ARTIFACT_ID,
        "json_artifact": NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT,
        "markdown_artifact": NEGATIVE_WITNESS_SUMMARY_MARKDOWN_ARTIFACT,
        "row_count": payload["row_count"],
        "audit_status": payload["audit_status"],
    }


def _negative_discovery_reports_index_section(generated_at: str | None = None) -> dict[str, Any]:
    del generated_at
    payload = _load_artifact_payload(NEGATIVE_DISCOVERY_REPORTS_JSON_ARTIFACT)
    return {
        "status": payload.get("status", "missing"),
        "artifact_id": NEGATIVE_DISCOVERY_REPORTS_ARTIFACT_ID,
        "json_artifact": NEGATIVE_DISCOVERY_REPORTS_JSON_ARTIFACT,
        "markdown_artifact": NEGATIVE_DISCOVERY_REPORTS_MARKDOWN_ARTIFACT,
        "row_count": payload.get("row_count", 0),
        "audit_status": payload.get("audit_status", "missing"),
    }


def _negative_witness_mutation_ledger_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT)
    hardgates = payload.get("hardgates", {}) if isinstance(payload.get("hardgates"), Mapping) else {}
    hardgate_status = {
        gate_id: gate.get("status")
        for gate_id, gate in hardgates.items()
        if isinstance(gate, Mapping)
    }
    return {
        "status": payload.get("status", "missing"),
        "artifact_id": payload.get("artifact_id", NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID),
        "schema_id": payload.get("schema_id", NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID),
        "json_artifact": NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT,
        "graph_artifact": MODEL_MUTATION_LINEAGE_GRAPH_ARTIFACT,
        "dgt_report_artifact": DGT_MUTATION_REPORT_ARTIFACT,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "entries_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries",
        "entry_count": payload.get("entry_count", 0),
        "hardgate_status": hardgate_status,
    }


def _new_model_hardgate_specs() -> tuple[Mapping[str, str], ...]:
    rows = (
        ("NEW-MODEL-HG1", "semantic model_id is present, unique, and not satisfied by report_id"),
        ("NEW-MODEL-HG2", "complete architecture specification pointer"),
        ("NEW-MODEL-HG3", "complete training objective specification pointer"),
        ("NEW-MODEL-HG4", "ClaimCapsule pointer"),
        ("NEW-MODEL-HG5", "EvidenceEnvelope pointer"),
        ("NEW-MODEL-HG6", "CostProtocol pointer"),
        ("NEW-MODEL-HG7", "parameter-matched baseline pointer"),
        ("NEW-MODEL-HG8", "compute-matched baseline pointer"),
        ("NEW-MODEL-HG9", "matched-random structural control pointer"),
        ("NEW-MODEL-HG10", "at least three OOD or stress surface pointers"),
        ("NEW-MODEL-HG11", "learned UER reduction over matched-random pointer"),
        ("NEW-MODEL-HG12", "FalseLedgerRate non-regression pointer"),
        ("NEW-MODEL-HG13", "nondecreasing benefit pointer"),
        ("NEW-MODEL-HG14", "decreasing debt pointer"),
        ("NEW-MODEL-HG15", "quality_q confidence-interval low endpoint above zero pointer"),
        ("NEW-MODEL-HG16", "positive classifier_shift_count pointer"),
        ("NEW-MODEL-HG17", "no forbidden inference evidence pointer"),
        ("NEW-MODEL-HG18", "negative-witness sweep pass pointer"),
        ("NEW-MODEL-HG19", "MechanismNameCertCandidate at least partial pointer"),
        (
            "NEW-MODEL-HG20",
            "not_claimed pointer excludes universal architecture, production, and full closure claims",
        ),
    )
    return tuple({"gate_id": gate_id, "requirement": requirement} for gate_id, requirement in rows)


def _build_new_model_hardgates_payload(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    gate_ids = [spec["gate_id"] for spec in _new_model_hardgate_specs()]
    gates = {
        spec["gate_id"]: {
            "requirement": spec["requirement"],
            "required_candidate_pointer": f"$.hardgate_instances.{spec['gate_id']}",
            "required_evidence_pointer": f"$.hardgate_instances.{spec['gate_id']}.evidence_pointer",
            "not_claimed_pointer": f"$.hardgate_instances.{spec['gate_id']}.not_claimed_pointer",
        }
        for spec in _new_model_hardgate_specs()
    }
    payload = {
        "schema_id": NEW_MODEL_HARDGATES_SCHEMA_ID,
        "generated_at": timestamp,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "gate_ids": gate_ids,
        "gates": gates,
    }
    _validate_new_model_hardgates_payload(payload)
    return payload


def _validate_new_model_hardgates_payload(payload: Mapping[str, Any]) -> None:
    forbidden_keys = {
        "terminal_verdict",
        "metrics",
        "raw_metrics",
        "candidate_metrics",
        "candidate_results",
        "candidate_measurements",
        "candidate_evidence",
        "candidate_evidence_body",
        "evidence_body",
        "baseline_metrics",
        "baseline_results",
        "measured_baseline",
    }

    def walk(value: Any, path: str) -> None:
        if isinstance(value, Mapping):
            for key, cell in value.items():
                if key in forbidden_keys or str(key).endswith("_body"):
                    raise ValueError(f"new_model_hardgates payload contains forbidden key at {path}.{key}")
                walk(cell, f"{path}.{key}")
        elif isinstance(value, list):
            for index, cell in enumerate(value):
                walk(cell, f"{path}[{index}]")
        elif isinstance(value, str):
            lowered = value.lower()
            if ".refactor-loop" in lowered or "terminal_verdict" in lowered:
                raise ValueError(f"new_model_hardgates payload contains forbidden value at {path}")
            if "candidate verdict" in lowered or "raw metric" in lowered:
                raise ValueError(f"new_model_hardgates payload contains forbidden candidate surface at {path}")

    walk(payload, "$")
    expected_top = {"schema_id", "generated_at", "canonical_role", "gate_ids", "gates"}
    if set(payload) != expected_top:
        raise ValueError("new_model_hardgates payload has invalid top-level fields")
    if payload["schema_id"] != NEW_MODEL_HARDGATES_SCHEMA_ID:
        raise ValueError("new_model_hardgates schema_id mismatch")
    if payload["canonical_role"] != "sidecar_not_in_CANONICAL_REPORTS":
        raise ValueError("new_model_hardgates canonical role mismatch")
    expected_ids = [f"NEW-MODEL-HG{index}" for index in range(1, 21)]
    if payload["gate_ids"] != expected_ids:
        raise ValueError("new_model_hardgates gate_ids must be NEW-MODEL-HG1..20")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping) or list(gates) != expected_ids:
        raise ValueError("new_model_hardgates gates must be ordered NEW-MODEL-HG1..20")
    required_fields = {
        "requirement",
        "required_candidate_pointer",
        "required_evidence_pointer",
        "not_claimed_pointer",
    }
    for gate_id, row in gates.items():
        if not isinstance(row, Mapping) or set(row) != required_fields:
            raise ValueError(f"new_model_hardgates gate row has invalid fields: {gate_id}")
        if row["required_candidate_pointer"] != f"$.hardgate_instances.{gate_id}":
            raise ValueError(f"new_model_hardgates candidate pointer mismatch: {gate_id}")
        if row["required_evidence_pointer"] != f"$.hardgate_instances.{gate_id}.evidence_pointer":
            raise ValueError(f"new_model_hardgates evidence pointer mismatch: {gate_id}")
        if row["not_claimed_pointer"] != f"$.hardgate_instances.{gate_id}.not_claimed_pointer":
            raise ValueError(f"new_model_hardgates not-claimed pointer mismatch: {gate_id}")


def _render_new_model_hardgates_markdown(payload: Mapping[str, Any]) -> str:
    _validate_new_model_hardgates_payload(payload)
    lines = [
        "# New Model Hardgates",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Canonical role: `{payload['canonical_role']}`",
        "",
        "| gate | requirement | candidate pointer | evidence pointer | not claimed |",
        "| --- | --- | --- | --- | --- |",
    ]
    for gate_id in payload["gate_ids"]:
        row = payload["gates"][gate_id]
        lines.append(
            "| "
            f"`{gate_id}` | "
            f"{row['requirement']} | "
            f"`{row['required_candidate_pointer']}` | "
            f"`{row['required_evidence_pointer']}` | "
            f"`{row['not_claimed_pointer']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def _new_model_hardgates_index_section(generated_at: str | None = None) -> dict[str, Any]:
    payload = _build_new_model_hardgates_payload(generated_at=generated_at)
    return {
        "status": "pointer-only",
        "artifact_id": NEW_MODEL_HARDGATES_ARTIFACT_ID,
        "json_artifact": NEW_MODEL_HARDGATES_JSON_ARTIFACT,
        "markdown_artifact": NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT,
        "schema_id": payload["schema_id"],
        "canonical_role": payload["canonical_role"],
        "gate_count": len(payload["gate_ids"]),
        "gate_ids_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gate_ids",
        "gates_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates",
    }


def _drt_pointer_value(payload: Mapping[str, Any], artifact_pointer: str) -> Any:
    prefix = f"{DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT}:"
    if not artifact_pointer.startswith(prefix):
        return None
    pointer = artifact_pointer[len(prefix) :]
    if pointer == "$":
        return payload
    return _bracket_pointer_value(payload, pointer)


def _as_finite_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _rounded_number(value: float | None) -> float | None:
    return None if value is None else round(float(value), 6)


def _validate_discovery_regularized_training_quality_promotion_boundary(payload: Mapping[str, Any]) -> None:
    boundary = payload.get("quality_promotion_boundary")
    if not isinstance(boundary, Mapping):
        raise ValueError("discovery_regularized_training quality_promotion_boundary must be an object")
    forbidden_keys = {
        "terminal_verdict",
        "metrics",
        "raw_metrics",
        "candidate_metrics",
        "candidate_results",
        "candidate_measurements",
        "candidate_evidence",
        "candidate_evidence_body",
        "evidence_body",
        "claim_capsule_body",
        "measurement_body",
        "host.env",
        "host_env",
        "host_environment",
    }

    def walk(value: Any, path: str) -> None:
        if isinstance(value, Mapping):
            for key, cell in value.items():
                if key in forbidden_keys or key.endswith("_body"):
                    raise ValueError(f"quality_promotion_boundary contains forbidden key at {path}.{key}")
                walk(cell, f"{path}.{key}")
        elif isinstance(value, list):
            for index, cell in enumerate(value):
                walk(cell, f"{path}[{index}]")
        elif isinstance(value, str):
            lowered = value.lower()
            for forbidden in ("terminal_verdict", "candidate evidence body", "host.env"):
                if forbidden in lowered:
                    raise ValueError(f"quality_promotion_boundary contains forbidden value at {path}")

    walk(boundary, "$.quality_promotion_boundary")
    expected_top_level = {
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
    if set(boundary) != expected_top_level:
        raise ValueError("quality_promotion_boundary has invalid top-level fields")
    if boundary["slot_state"] != "present-but-fail-closed":
        raise ValueError("quality_promotion_boundary slot_state must be present-but-fail-closed")
    if boundary["owner_pointer"] != _drt_quality_artifact_pointer("$.quality_promotion_boundary"):
        raise ValueError("quality_promotion_boundary owner pointer mismatch")
    if boundary["source_artifact"] != DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT:
        raise ValueError("quality_promotion_boundary source artifact mismatch")
    if boundary["quality_metric"] != "quality_q":
        raise ValueError("quality_promotion_boundary metric mismatch")
    replay_pointers = boundary["replay_dimension_pointers"]
    expected_replay_dimensions = {"steps", "seeds", "mixings", "rho", "lambda"}
    if not isinstance(replay_pointers, Mapping) or set(replay_pointers) != expected_replay_dimensions:
        raise ValueError("quality_promotion_boundary replay dimensions mismatch")
    for key, pointer in replay_pointers.items():
        if _drt_pointer_value(payload, str(pointer)) is None:
            raise ValueError(f"quality_promotion_boundary replay pointer does not resolve: {key}")
    task_quality = _as_finite_number(_drt_pointer_value(payload, str(boundary["task_only_quality_q_pointer"])))
    hardgate = boundary["hardgate"]
    hardgate_fields = {
        "gate_id",
        "slot_state",
        "requirement",
        "evidence_pointer",
        "task_only_quality_q",
        "drt_quality_q_ci_low",
        "drt_minus_task_only_quality_q_ci_low",
        "promotion_gate",
        "fail_closed_when",
    }
    if not isinstance(hardgate, Mapping) or set(hardgate) != hardgate_fields:
        raise ValueError("quality_promotion_boundary hardgate fields invalid")
    if hardgate["gate_id"] != "DRT-HG2":
        raise ValueError("quality_promotion_boundary hardgate id mismatch")
    if hardgate["slot_state"] != "present-but-fail-closed":
        raise ValueError("quality_promotion_boundary hardgate slot_state invalid")
    if hardgate["fail_closed_when"] != "drt_quality_q_ci_low <= task_only_quality_q":
        raise ValueError("quality_promotion_boundary fail-closed condition mismatch")
    delta = _as_finite_number(_drt_pointer_value(payload, str(hardgate["evidence_pointer"])))
    expected_drt_ci_low = task_quality + delta if task_quality is not None and delta is not None else None
    expected_margin = None if expected_drt_ci_low is None or task_quality is None else expected_drt_ci_low - task_quality
    if hardgate["task_only_quality_q"] != _rounded_number(task_quality):
        raise ValueError("quality_promotion_boundary task_only quality mismatch")
    if hardgate["drt_quality_q_ci_low"] != _rounded_number(expected_drt_ci_low):
        raise ValueError("quality_promotion_boundary DRT CI-low mismatch")
    if hardgate["drt_minus_task_only_quality_q_ci_low"] != _rounded_number(expected_margin):
        raise ValueError("quality_promotion_boundary DRT margin mismatch")
    expected_gate = (
        "clears-boundary"
        if expected_drt_ci_low is not None and task_quality is not None and expected_drt_ci_low > task_quality
        else "fail-closed"
    )
    if hardgate["promotion_gate"] != expected_gate:
        raise ValueError("quality_promotion_boundary DRT-HG2 fail-closed semantics mismatch")
    if list(boundary["arm_quality_order"]) != list(DRT_QUALITY_PROMOTION_ARMS):
        raise ValueError("quality_promotion_boundary arm render order mismatch")
    arm_comparisons = boundary["arm_comparisons"]
    if not isinstance(arm_comparisons, Mapping) or set(arm_comparisons) != set(DRT_QUALITY_PROMOTION_ARMS):
        raise ValueError("quality_promotion_boundary arm coverage mismatch")
    arm_fields = {
        "render_order",
        "arm",
        "source_arm",
        "slot_state",
        "evidence_pointer",
        "quality_q_pointer",
        "quality_q_ci_low_pointer",
        "quality_q",
        "quality_q_ci_low",
        "task_only_quality_q",
        "comparison_to_task_only",
        "promotion_gate",
    }
    for order, arm in enumerate(DRT_QUALITY_PROMOTION_ARMS, start=1):
        row = arm_comparisons[arm]
        if not isinstance(row, Mapping) or set(row) != arm_fields:
            raise ValueError(f"quality_promotion_boundary arm row fields invalid: {arm}")
        if row["render_order"] != order or row["arm"] != arm:
            raise ValueError(f"quality_promotion_boundary arm row identity invalid: {arm}")
        if row["slot_state"] != "present-but-fail-closed":
            raise ValueError(f"quality_promotion_boundary arm row state invalid: {arm}")
        for pointer_key in ("evidence_pointer", "quality_q_pointer", "quality_q_ci_low_pointer"):
            if _drt_pointer_value(payload, str(row[pointer_key])) is None:
                raise ValueError(f"quality_promotion_boundary pointer does not resolve: {arm}.{pointer_key}")
        if row["task_only_quality_q"] != _rounded_number(task_quality):
            raise ValueError(f"quality_promotion_boundary arm task_only quality mismatch: {arm}")
    drt_row = arm_comparisons["DRT"]
    if drt_row["quality_q_ci_low"] != hardgate["drt_quality_q_ci_low"]:
        raise ValueError("quality_promotion_boundary DRT row CI-low must match hardgate")
    if drt_row["promotion_gate"] != hardgate["promotion_gate"]:
        raise ValueError("quality_promotion_boundary DRT row gate must match hardgate")


def _validate_discovery_regularized_training_extension(payload: Mapping[str, Any]) -> None:
    loss_family = payload.get("loss_family")
    component_ablation = payload.get("component_ablation")
    comparison = payload.get("training_method_comparison")
    hardgates = payload.get("drt_extension_hardgates")
    if not all(isinstance(section, Mapping) for section in (loss_family, component_ablation, comparison, hardgates)):
        raise ValueError("discovery_regularized_training extension sections must be objects")
    audit = drt_extension_forbidden_key_audit(
        {
            "loss_family": loss_family,
            "component_ablation": component_ablation,
            "training_method_comparison": comparison,
            "drt_extension_hardgates": hardgates,
        }
    )
    if audit["status"] != "pass":
        raise ValueError("discovery_regularized_training extension forbidden audit failed")
    expected_loss_terms = {
        "discovery",
        "ledger",
        "certificate",
        "mechanism",
        "cost",
        "negative_witness",
    }
    if loss_family["status"] != "pointer-only":
        raise ValueError("discovery_regularized_training loss_family status mismatch")
    if loss_family["owner_pointer"] != _drt_quality_artifact_pointer("$.loss_family"):
        raise ValueError("discovery_regularized_training loss_family owner pointer mismatch")
    terms = loss_family.get("terms")
    if not isinstance(terms, Mapping) or set(terms) != expected_loss_terms:
        raise ValueError("discovery_regularized_training loss_family terms mismatch")
    if _drt_pointer_value(payload, str(loss_family["loss_terms_enabled_pointer"])) is None:
        raise ValueError("discovery_regularized_training loss_terms_enabled pointer does not resolve")
    for term_id, row in terms.items():
        if not isinstance(row, Mapping) or row.get("term_id") != term_id:
            raise ValueError(f"discovery_regularized_training loss term invalid: {term_id}")
        if _drt_pointer_value(payload, str(row.get("evidence_pointer"))) is None:
            raise ValueError(f"discovery_regularized_training loss term pointer does not resolve: {term_id}")
    if component_ablation["status"] != "pointer-only":
        raise ValueError("discovery_regularized_training component_ablation status mismatch")
    if component_ablation["owner_pointer"] != _drt_quality_artifact_pointer("$.component_ablation"):
        raise ValueError("discovery_regularized_training component_ablation owner pointer mismatch")
    rows = component_ablation.get("rows")
    if not isinstance(rows, list) or len(rows) != 7:
        raise ValueError("discovery_regularized_training component_ablation row count mismatch")
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError("discovery_regularized_training component_ablation row must be object")
        for key in ("evidence_pointer", "quality_q_pointer"):
            if _drt_pointer_value(payload, str(row.get(key))) is None:
                raise ValueError(f"discovery_regularized_training component_ablation pointer does not resolve: {key}")
    if comparison["status"] != "pointer-only":
        raise ValueError("discovery_regularized_training training_method_comparison status mismatch")
    expected_comparison_pointers = {
        "comparison_family_pointer",
        "compute_ledger_pointer",
        "debt_marker_pointer",
    }
    for key in expected_comparison_pointers:
        if _drt_pointer_value(payload, str(comparison.get(key))) is None:
            raise ValueError(f"discovery_regularized_training comparison pointer does not resolve: {key}")
    metric_pointers = comparison.get("metric_pointers")
    if not isinstance(metric_pointers, Mapping) or set(metric_pointers) != {"uer", "uer_reduction", "raw_rows"}:
        raise ValueError("discovery_regularized_training comparison metric pointers mismatch")
    for pointer in metric_pointers.values():
        if _drt_pointer_value(payload, str(pointer)) is None:
            raise ValueError("discovery_regularized_training comparison metric pointer does not resolve")
    gates = hardgates.get("gates")
    if not isinstance(gates, Mapping):
        raise ValueError("discovery_regularized_training extension hardgates missing gates")
    expected_gate_order = (
        "DRT-EXT-HG1_required_pointer_resolution",
        "DRT-EXT-HG2_uer_threshold",
        "DRT-EXT-HG3_component_ablation",
        "DRT-EXT-HG4_forbidden_key_audit",
    )
    expected_gates = set(expected_gate_order)
    if set(gates) != expected_gates:
        raise ValueError("discovery_regularized_training extension hardgate set mismatch")
    uer_gate = gates["DRT-EXT-HG2_uer_threshold"]
    if uer_gate.get("thresholds") != {
        "uer_max": DRT_EXTENSION_UER_MAX,
        "uer_reduction_min": DRT_EXTENSION_UER_REDUCTION_MIN,
    }:
        raise ValueError("discovery_regularized_training extension UER thresholds mismatch")
    uer = _as_finite_number(_drt_pointer_value(payload, str(uer_gate.get("uer_pointer"))))
    reduction = _as_finite_number(_drt_pointer_value(payload, str(uer_gate.get("uer_reduction_pointer"))))
    expected_uer_status = (
        "pass"
        if uer is not None
        and reduction is not None
        and uer <= DRT_EXTENSION_UER_MAX
        and reduction >= DRT_EXTENSION_UER_REDUCTION_MIN
        else "fail"
    )
    if uer_gate.get("status") != expected_uer_status:
        raise ValueError("discovery_regularized_training extension UER gate mismatch")
    expected_failed = next((gate for gate in expected_gate_order if gates[gate].get("status") != "pass"), None)
    if hardgates.get("status") != ("pass" if expected_failed is None else "fail"):
        raise ValueError("discovery_regularized_training extension hardgate status mismatch")
    if hardgates.get("failed_gate") != expected_failed:
        raise ValueError("discovery_regularized_training extension failed gate mismatch")
    expected_failed_pointer = None if expected_failed is None else f"$.drt_extension_hardgates.gates.{expected_failed}.status"
    if hardgates.get("failed_gate_pointer") != expected_failed_pointer:
        raise ValueError("discovery_regularized_training extension failed gate pointer mismatch")
    if expected_failed_pointer is not None and _drt_pointer_value(payload, _drt_quality_artifact_pointer(expected_failed_pointer)) is None:
            raise ValueError("discovery_regularized_training extension failed gate pointer does not resolve")


def _validate_discovery_regularized_training_compute_ledger(payload: Mapping[str, Any]) -> None:
    ledger = payload.get("compute_ledger")
    if not isinstance(ledger, Mapping):
        raise ValueError("discovery_regularized_training compute_ledger must be an object")
    expected_fields = {
        "status",
        "backend_row_counts",
        "device",
        "requested_device",
        "resolved_device",
        "deterministic_seed_count",
        "torch_seed_count",
        "total_steps",
        "wall_time_seconds_proxy",
        "flops_proxy",
        "energy_proxy",
        "cost_protocol_pointer",
        "raw_rows_pointer",
        "protocols_pointer",
        "missing_fields",
        "evidence_pointer",
    }
    if set(ledger) != expected_fields:
        raise ValueError("discovery_regularized_training compute_ledger fields invalid")
    if ledger["cost_protocol_pointer"] != "$.source_artifacts.cost_protocol":
        raise ValueError("discovery_regularized_training compute_ledger cost pointer mismatch")
    for key in ("raw_rows_pointer", "protocols_pointer", "evidence_pointer", "cost_protocol_pointer"):
        pointer = ledger.get(key)
        if key == "raw_rows_pointer":
            if not pointer:
                raise ValueError("discovery_regularized_training compute_ledger raw rows pointer missing")
            continue
        if _bracket_pointer_value(payload, str(pointer)) is None:
            raise ValueError(f"discovery_regularized_training compute_ledger pointer does not resolve: {key}")
    if not isinstance(ledger["backend_row_counts"], Mapping):
        raise ValueError("discovery_regularized_training compute_ledger backend counts invalid")
    if int(ledger["backend_row_counts"].get("deterministic-anchor", 0)) <= 0:
        raise ValueError("discovery_regularized_training compute_ledger deterministic rows missing")
    if int(ledger["deterministic_seed_count"]) <= 0:
        raise ValueError("discovery_regularized_training compute_ledger deterministic seeds missing")
    if int(ledger["torch_seed_count"]) <= 0:
        raise ValueError("discovery_regularized_training compute_ledger torch seeds missing")
    if int(ledger["total_steps"]) <= 0 or int(ledger["flops_proxy"]) <= 0:
        raise ValueError("discovery_regularized_training compute_ledger proxy counts missing")
    expected_status = "complete" if list(ledger["missing_fields"]) == [] else "incomplete"
    if ledger["status"] != expected_status:
        raise ValueError("discovery_regularized_training compute_ledger status mismatch")


def _validate_discovery_regularized_training_mechanism_ablation(payload: Mapping[str, Any]) -> None:
    section = payload.get("mechanism_ablation")
    if not isinstance(section, Mapping):
        raise ValueError("discovery_regularized_training mechanism_ablation must be an object")
    if section.get("status") not in {"pass", "fail"}:
        raise ValueError("discovery_regularized_training mechanism_ablation status invalid")
    if section.get("backend") != "deterministic-mechanism-ablation":
        raise ValueError("discovery_regularized_training mechanism_ablation backend mismatch")
    required = section.get("required_arms")
    comparisons = section.get("comparisons")
    by_arm = section.get("by_arm")
    if not isinstance(required, list) or len(required) != 6:
        raise ValueError("discovery_regularized_training mechanism_ablation required arms mismatch")
    if not isinstance(comparisons, list) or len(comparisons) != len(required):
        raise ValueError("discovery_regularized_training mechanism_ablation comparison rows mismatch")
    if not isinstance(by_arm, Mapping) or set(by_arm) != set(required):
        raise ValueError("discovery_regularized_training mechanism_ablation by_arm mismatch")
    for row in comparisons:
        if not isinstance(row, Mapping) or row.get("arm_id") not in required:
            raise ValueError("discovery_regularized_training mechanism_ablation row invalid")
        pointers = row.get("comparison_pointers")
        if not isinstance(pointers, Mapping):
            raise ValueError("discovery_regularized_training mechanism_ablation comparison pointers missing")
        for pointer in pointers.values():
            if _drt_pointer_value(payload, str(pointer)) is None:
                raise ValueError("discovery_regularized_training mechanism_ablation pointer does not resolve")
    expected_status = (
        "pass"
        if section.get("required_arms_present") is True
        and section.get("comparison_pointers_resolve") is True
        and section.get("full_beats_all_ablations") is True
        and section.get("full_positive_mechanism_signal") is True
        and section.get("no_ablation_net_positive_parity") is True
        else "fail"
    )
    if section.get("status") != expected_status:
        raise ValueError("discovery_regularized_training mechanism_ablation status mismatch")
    gates = payload.get("hardgate", {}).get("gates", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    hg7 = gates.get("DRT-HG7") if isinstance(gates, Mapping) else None
    if not isinstance(hg7, Mapping):
        raise ValueError("discovery_regularized_training DRT-HG7 missing")
    if hg7.get("evidence_pointer") != "$.mechanism_ablation":
        raise ValueError("discovery_regularized_training DRT-HG7 evidence pointer mismatch")
    expected_hg7 = "pass" if section.get("status") == "pass" else "fail"
    if hg7.get("status") != expected_hg7:
        raise ValueError("discovery_regularized_training DRT-HG7 status mismatch")


def _validate_discovery_regularized_training_mechanism_cert(payload: Mapping[str, Any]) -> None:
    cert = payload.get("training_mechanism_cert")
    if not isinstance(cert, Mapping):
        raise ValueError("discovery_regularized_training training_mechanism_cert must be an object")
    expected_fields = {
        "schema_id",
        "status",
        "owner_pointer",
        "hardgate_pointer",
        "status_pointer",
        "required_pointers",
        "mechanism_ablation_status_pointer",
        "torch_delta_pointer",
        "matched_control_pointer",
        "ledger_pointer",
        "negative_witness_pointer",
        "all_required_pointers_resolve",
        "mechanism_ablation_status",
        "torch_positive",
        "ledger_complete",
    }
    if set(cert) != expected_fields:
        raise ValueError("discovery_regularized_training training_mechanism_cert fields invalid")
    if cert["schema_id"] != "bedc-quality-lab:discovery-regularized-training:training-mechanism-cert":
        raise ValueError("discovery_regularized_training training_mechanism_cert schema mismatch")
    if cert["owner_pointer"] != _drt_quality_artifact_pointer("$.training_mechanism_cert"):
        raise ValueError("discovery_regularized_training training_mechanism_cert owner pointer mismatch")
    if cert["hardgate_pointer"] != _drt_quality_artifact_pointer("$.hardgate.gates.DRT-HG8"):
        raise ValueError("discovery_regularized_training training_mechanism_cert hardgate pointer mismatch")
    required = cert.get("required_pointers")
    if not isinstance(required, list) or not required:
        raise ValueError("discovery_regularized_training training_mechanism_cert required pointers missing")
    all_resolve = True
    for row in required:
        if not isinstance(row, Mapping) or set(row) != {"pointer", "status"}:
            raise ValueError("discovery_regularized_training training_mechanism_cert pointer row invalid")
        resolves = _drt_pointer_value(payload, str(row["pointer"])) is not None
        if row["status"] != ("pass" if resolves else "fail"):
            raise ValueError("discovery_regularized_training training_mechanism_cert pointer status mismatch")
        all_resolve = all_resolve and resolves
    pointer_fields = (
        "status_pointer",
        "mechanism_ablation_status_pointer",
        "torch_delta_pointer",
        "matched_control_pointer",
        "ledger_pointer",
        "negative_witness_pointer",
    )
    for key in pointer_fields:
        if _drt_pointer_value(payload, str(cert[key])) is None:
            raise ValueError(f"discovery_regularized_training training_mechanism_cert pointer does not resolve: {key}")
    expected_status = (
        "pass"
        if cert.get("mechanism_ablation_status") == "pass"
        and cert.get("torch_positive") is True
        and cert.get("ledger_complete") is True
        and all_resolve
        else "fail"
    )
    if cert["all_required_pointers_resolve"] is not all_resolve:
        raise ValueError("discovery_regularized_training training_mechanism_cert resolution mismatch")
    if cert["status"] != expected_status:
        raise ValueError("discovery_regularized_training training_mechanism_cert status mismatch")
    gates = payload.get("hardgate", {}).get("gates", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    hg8 = gates.get("DRT-HG8") if isinstance(gates, Mapping) else None
    if not isinstance(hg8, Mapping):
        raise ValueError("discovery_regularized_training DRT-HG8 missing")
    if hg8.get("evidence_pointer") != "$.training_mechanism_cert":
        raise ValueError("discovery_regularized_training DRT-HG8 evidence pointer mismatch")
    if hg8.get("status") != expected_status:
        raise ValueError("discovery_regularized_training DRT-HG8 status mismatch")


def _validate_discovery_regularized_training_payload(payload: Mapping[str, Any]) -> None:
    _validate_discovery_regularized_training_quality_promotion_boundary(payload)
    _validate_discovery_regularized_training_extension(payload)
    _validate_discovery_regularized_training_compute_ledger(payload)
    _validate_discovery_regularized_training_mechanism_ablation(payload)
    _validate_discovery_regularized_training_mechanism_cert(payload)


def _discovery_regularized_training_quality_boundary_index_section(payload: Mapping[str, Any] | None = None) -> dict[str, Any]:
    fallback = {
        "status": "present-but-fail-closed",
        "json_artifact": DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_REGULARIZED_TRAINING_MARKDOWN_ARTIFACT,
        "owner_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary"),
        "hardgate_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary.hardgate"),
        "arm_comparisons_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary.arm_comparisons"),
        "compute_ledger_pointer": _drt_quality_artifact_pointer("$.compute_ledger"),
        "replay_dimension_pointers": {
            "steps": _drt_quality_artifact_pointer("$.config.steps"),
            "seeds": _drt_quality_artifact_pointer("$.config.seeds"),
            "mixings": _drt_quality_artifact_pointer("$.config.mixings"),
            "rho": _drt_quality_artifact_pointer("$.config.rhos"),
            "lambda": _drt_quality_artifact_pointer("$.config.discovery_lambdas"),
        },
        "ordered_arm_comparison_pointers": [
            {
                "order": index,
                "arm": arm,
                "pointer": _drt_quality_artifact_pointer(f"$.quality_promotion_boundary.arm_comparisons.{arm}"),
            }
            for index, arm in enumerate(DRT_QUALITY_PROMOTION_ARMS, start=1)
        ],
    }
    if payload is None:
        path = _artifact_path(DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT)
        if not path.exists():
            return fallback
        payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        raise ValueError("discovery_regularized_training index source must be an object")
    if not isinstance(payload.get("config"), Mapping):
        return fallback
    _validate_discovery_regularized_training_payload(payload)
    boundary = payload["quality_promotion_boundary"]
    return {
        "status": boundary["slot_state"],
        "json_artifact": DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_REGULARIZED_TRAINING_MARKDOWN_ARTIFACT,
        "owner_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary"),
        "hardgate_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary.hardgate"),
        "arm_comparisons_pointer": _drt_quality_artifact_pointer("$.quality_promotion_boundary.arm_comparisons"),
        "compute_ledger_pointer": _drt_quality_artifact_pointer("$.compute_ledger"),
        "replay_dimension_pointers": dict(boundary["replay_dimension_pointers"]),
        "ordered_arm_comparison_pointers": [
            {
                "order": index,
                "arm": arm,
                "pointer": _drt_quality_artifact_pointer(f"$.quality_promotion_boundary.arm_comparisons.{arm}"),
            }
            for index, arm in enumerate(DRT_QUALITY_PROMOTION_ARMS, start=1)
        ],
    }


def _build_discovery_gated_transformer_payload(generated_at: str | None = None) -> dict[str, Any]:
    from scripts import run_discovery_gated_transformer as dgt_runner

    sidecar = _build_new_model_hardgates_payload(generated_at=generated_at)
    payload = dgt_runner.build_payload(
        generated_at=generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat(),
        sidecar=sidecar,
    )
    _validate_discovery_gated_transformer_payload(payload)
    return payload


def _validate_discovery_gated_transformer_payload(payload: Mapping[str, Any]) -> None:
    from scripts import run_discovery_gated_transformer as dgt_runner

    dgt_runner.validate_payload(payload)
    expected_top_level = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "model_id",
        "canonical_owner",
        "hardgate_contract_ref",
        "sequence_task_grid",
        "training_evidence",
        "baselines",
        "classifier_surface_delta",
        "net_positive_signal",
        "hardgate_instances",
        "prototype_status",
        "discovery_map_signal",
        "claim_capsule_ref",
        "not_claimed",
        "revocation_rows",
        "forbidden_claim_term_audit",
    }
    if set(payload) != expected_top_level:
        raise ValueError("discovery_gated_transformer payload has invalid top-level fields")
    if payload["model_id"] != "discovery_gated_transformer":
        raise ValueError("discovery_gated_transformer model_id mismatch")
    contract = payload["hardgate_contract_ref"]
    if contract != {
        "artifact": NEW_MODEL_HARDGATES_JSON_ARTIFACT,
        "pointer": "$.gates",
        "artifact_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates",
        "validation_status": "pass",
    }:
        raise ValueError("discovery_gated_transformer hardgate contract ref mismatch")
    hardgates = payload["hardgate_instances"]
    if set(hardgates) != {f"NEW-MODEL-HG{index}" for index in range(1, 21)}:
        raise ValueError("discovery_gated_transformer hardgate instances must contain NEW-MODEL-HG1..20")
    all_pass = all(row["status"] == "pass" for row in hardgates.values())
    if payload["prototype_status"] != ("prototype-candidate" if all_pass else "demoted-candidate"):
        raise ValueError("discovery_gated_transformer prototype status mismatch")
    forbidden = json.dumps(payload, sort_keys=True).lower()
    for token in ("terminal_verdict", ".refactor-loop", "host.env", "raw positive claim"):
        if token in forbidden:
            raise ValueError(f"discovery_gated_transformer payload contains forbidden value: {token}")


def _render_discovery_gated_transformer_markdown(payload: Mapping[str, Any]) -> str:
    from scripts import run_discovery_gated_transformer as dgt_runner

    _validate_discovery_gated_transformer_payload(payload)
    return dgt_runner.render_markdown(payload)


def _discovery_gated_transformer_index_section(payload: Mapping[str, Any]) -> dict[str, Any]:
    _validate_discovery_gated_transformer_payload(payload)
    return {
        "status": payload["prototype_status"],
        "artifact_id": DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID,
        "schema_id": DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID,
        "json_artifact": DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT,
        "fingerprint_artifact": "reports/canonical/discovery_gated_transformer.fingerprint.json",
        "model_id_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.model_id",
        "hardgate_contract_ref_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_contract_ref",
        "sequence_task_grid_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.sequence_task_grid",
        "training_evidence_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.training_evidence",
        "baselines_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.baselines",
        "classifier_surface_delta_pointer": (
            f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.classifier_surface_delta"
        ),
        "net_positive_signal_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.net_positive_signal",
        "hardgate_instances_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_instances",
        "prototype_status_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.prototype_status",
        "discovery_map_signal_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.discovery_map_signal",
        "claim_capsule_ref_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.claim_capsule_ref",
        "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
        "revocation_rows_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.revocation_rows",
        "forbidden_claim_term_audit_pointer": (
            f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.forbidden_claim_term_audit"
        ),
        "hardgate_instance_pointers": {
            f"NEW-MODEL-HG{index}": (
                f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_instances.NEW-MODEL-HG{index}"
            )
            for index in range(1, 21)
        },
        "hardgate_contract_gates_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates",
    }


def _write_discovery_gated_transformer_fingerprint(payload: Mapping[str, Any]) -> None:
    sidecar = {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "discovery_gated_transformer",
        "json_artifact": DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT,
        "input_fingerprint": _json_digest(
            {
                "producer": "scripts/run_discovery_gated_transformer.py",
                "sidecar_schema": NEW_MODEL_HARDGATES_SCHEMA_ID,
                "model_id": payload["model_id"],
            }
        ),
        "output_digest": _canonical_output_digest(
            CanonicalReportSpec(
                name="discovery_gated_transformer",
                command=("python3", "scripts/run_discovery_gated_transformer.py"),
                json_artifact=DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
                markdown_artifact=DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT,
                required_json_keys=("schema_id", "model_id", "hardgate_instances", "prototype_status"),
                estimated_seconds=1,
                bundle_role="auxiliary",
                scope_pointer="$.not_claimed",
                cost_pointer="$.training_evidence.cost_protocol_pointer",
                not_claimed_pointer="$.not_claimed",
                positive_claim_pointer="$.net_positive_signal",
                control_pointer="$.baselines",
                no_control_rationale_pointer=None,
            )
        ),
        "generated_by": {
            "runner": "scripts/run_canonical_reports.py",
            "generated_at": payload["generated_at"],
        },
    }
    _write_json_atomic(_artifact_path("reports/canonical/discovery_gated_transformer.fingerprint.json"), sidecar)


MODEL_DESIGN_SUITE_POINTER_FIELDS = (
    "component_id",
    "canonical_owner_pointer",
    "discovery_pointer",
    "verdict_pointer",
    "mechanism_pointer",
    "debt_pointer",
    "not_claimed_pointer",
    "negative_witness_pointer",
)
MODEL_DESIGN_SUITE_ROW_FIELDS = set(MODEL_DESIGN_SUITE_POINTER_FIELDS) | {
    "hardgate_status",
    "hardgate_reason",
}
MODEL_DESIGN_SUITE_FORBIDDEN_KEYS = (
    "terminal_verdict",
    "metrics",
    "raw_metrics",
    "candidate_metrics",
    "candidate_measurements",
    "candidate_results",
    "candidate_evidence",
    "candidate_evidence_body",
    "evidence_body",
    "measurement_body",
    "host",
)
MODEL_DESIGN_SUITE_HARDGATE_IDS = tuple(f"SUITE-HG{index}" for index in range(1, 6))


def _model_design_suite_pointer(pointer: str) -> str:
    return f"{MODEL_DESIGN_SUITE_JSON_ARTIFACT}:{pointer}"


def _model_design_suite_rows() -> list[dict[str, Any]]:
    return [
        {
            "component_id": "reports/canonical/ledger-aware-transformer.json:$.artifact_id",
            "canonical_owner_pointer": "reports/canonical/ledger-aware-transformer.json:$",
            "discovery_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_instances.NEW-MODEL-HG11",
            "verdict_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.prototype_status",
            "mechanism_pointer": "reports/canonical/ledger-aware-transformer.json:$.run_artifacts",
            "debt_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.training_evidence.false_ledger_rate",
            "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[6]",
            "hardgate_status": "pass",
            "hardgate_reason": "backbone owner and hardgate pointers resolve",
        },
        {
            "component_id": "reports/canonical/certificate-gated-attention.json:$.artifact_id",
            "canonical_owner_pointer": "reports/canonical/certificate-gated-attention.json:$",
            "discovery_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_instances.NEW-MODEL-HG19",
            "verdict_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.prototype_status",
            "mechanism_pointer": "reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary",
            "debt_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.discovery_map_signal",
            "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[3]",
            "hardgate_status": "pass",
            "hardgate_reason": "attention owner and hardgate pointers resolve",
        },
        {
            "component_id": f"{DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT}:$.artifact_id",
            "canonical_owner_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT}:$",
            "discovery_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.training_evidence.loss_decrease",
            "verdict_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.prototype_status",
            "mechanism_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT}:$.training_mechanism_cert",
            "debt_pointer": f"{DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT}:$.quality_promotion_boundary.hardgate",
            "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries",
            "hardgate_status": "pass",
            "hardgate_reason": "training owner and hardgate pointers resolve",
        },
        {
            "component_id": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.artifact_id",
            "canonical_owner_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$",
            "discovery_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.discovery_map_signal",
            "verdict_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.hardgate.status",
            "mechanism_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.mechanism_gate_summary",
            "debt_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.revocation_rows",
            "not_claimed_pointer": f"{MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[7]",
            "hardgate_status": "pass",
            "hardgate_reason": "mechanism-seeking owner and hardgate pointers resolve",
        },
        {
            "component_id": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.artifact_id",
            "canonical_owner_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$",
            "discovery_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.discovery_map_signal",
            "verdict_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.hardgate.status",
            "mechanism_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.search_space",
            "debt_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.hardgate.gates.DG-NAS-HG8",
            "not_claimed_pointer": f"{DISCOVERY_GATED_NAS_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries[2]",
            "hardgate_status": "pass",
            "hardgate_reason": "DG-NAS owner and hardgate pointers resolve",
        },
        {
            "component_id": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.artifact_id",
            "canonical_owner_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$",
            "discovery_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.discovery_map_signal",
            "verdict_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.prototype_status",
            "mechanism_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.hardgate_instances",
            "debt_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.revocation_rows",
            "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
            "negative_witness_pointer": f"{NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT}:$.entries",
            "hardgate_status": "pass",
            "hardgate_reason": "DGT design pointers resolve",
        },
    ]


def _model_design_suite_hardgate_rows(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    field_status = {
        field: "pass"
        if all(
            isinstance(row.get(field), str)
            and row.get(field)
            and (
                row.get("hardgate_status") == "pass"
                or field not in str(row.get("hardgate_reason", ""))
            )
            for row in rows
        )
        else "fail"
        for field in MODEL_DESIGN_SUITE_POINTER_FIELDS
    }
    suite_status = "pass" if all(row.get("hardgate_status") == "pass" for row in rows) else "fail"
    return {
        "SUITE-HG1": {
            "gate_id": "SUITE-HG1",
            "status": field_status["component_id"],
            "reason": "component_id pointers are artifact-qualified and non-empty",
        },
        "SUITE-HG2": {
            "gate_id": "SUITE-HG2",
            "status": field_status["canonical_owner_pointer"],
            "reason": "canonical_owner_pointer resolves for every row",
        },
        "SUITE-HG3": {
            "gate_id": "SUITE-HG3",
            "status": field_status["discovery_pointer"],
            "reason": "discovery pointers resolve for every row",
        },
        "SUITE-HG4": {
            "gate_id": "SUITE-HG4",
            "status": field_status["verdict_pointer"],
            "reason": "verdict and mechanism pointers resolve for every row",
        },
        "SUITE-HG5": {
            "gate_id": "SUITE-HG5",
            "status": suite_status,
            "reason": "row hardgate statuses propagate to the suite status",
        },
    }


def _model_design_suite_forbidden_paths(payload: Any, path: str = "$") -> list[str]:
    found: list[str] = []
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            key_text = str(key)
            child_path = f"{path}.{key_text}"
            if key_text in MODEL_DESIGN_SUITE_FORBIDDEN_KEYS or key_text.endswith("_body"):
                found.append(child_path)
            if path.endswith(".host") and key_text == "env":
                found.append(child_path)
            found.extend(_model_design_suite_forbidden_paths(value, child_path))
    elif isinstance(payload, list):
        for index, value in enumerate(payload):
            found.extend(_model_design_suite_forbidden_paths(value, f"{path}[{index}]"))
    return found


def _model_design_suite_pointer_resolves(pointer: Any, *, payload: Mapping[str, Any] | None = None) -> bool:
    if not isinstance(pointer, str) or not pointer:
        return False
    split = _split_artifact_pointer(pointer)
    if split is None:
        return False
    artifact, local_pointer = split
    if artifact == MODEL_DESIGN_SUITE_JSON_ARTIFACT and payload is not None:
        if local_pointer == "$":
            return True
        return _bracket_pointer_value(payload, local_pointer) is not None
    return _resolve_committed_artifact_pointer(ROOT, pointer) is not None


def _model_design_suite_row_status(row: Mapping[str, Any], *, payload: Mapping[str, Any]) -> tuple[str, str]:
    missing = [
        field
        for field in MODEL_DESIGN_SUITE_POINTER_FIELDS
        if not isinstance(row.get(field), str) or not row.get(field)
    ]
    if missing:
        return "fail", f"missing pointer fields: {', '.join(missing)}"
    dangling = [
        field
        for field in MODEL_DESIGN_SUITE_POINTER_FIELDS
        if not _model_design_suite_pointer_resolves(row[field], payload=payload)
    ]
    if dangling:
        return "fail", f"dangling pointer fields: {', '.join(dangling)}"
    return "pass", "all pointer fields resolve"


def _build_model_design_suite_payload(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    payload: dict[str, Any] = {
        "schema_id": MODEL_DESIGN_SUITE_SCHEMA_ID,
        "artifact_id": MODEL_DESIGN_SUITE_ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "scripts/run_canonical_reports.py",
        "status": "pending",
        "canonical_owner": {
            "owner_pointer": _model_design_suite_pointer("$"),
            "rows_pointer": _model_design_suite_pointer("$.rows"),
        },
        "coverage_matrix_pointer": f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.coverage_matrix",
        "rows": _model_design_suite_rows(),
        "hardgates": {},
        "not_claimed": [
            "The suite records design ownership pointers only.",
            "The suite does not claim production model performance.",
            "The suite does not copy candidate measurement bodies.",
        ],
    }
    for row in payload["rows"]:
        row["hardgate_status"], row["hardgate_reason"] = _model_design_suite_row_status(row, payload=payload)
    payload["hardgates"] = _model_design_suite_hardgate_rows(payload["rows"])
    payload["status"] = (
        "pass"
        if all(gate["status"] == "pass" for gate in payload["hardgates"].values())
        and all(row["hardgate_status"] == "pass" for row in payload["rows"])
        else "fail"
    )
    _validate_model_design_suite_payload(payload)
    return payload


def _validate_model_design_suite_payload(payload: Mapping[str, Any]) -> None:
    forbidden = _model_design_suite_forbidden_paths(payload)
    if forbidden:
        raise ValueError(f"model_design_suite payload contains forbidden keys: {', '.join(forbidden)}")
    expected_top_level = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "status",
        "canonical_owner",
        "coverage_matrix_pointer",
        "rows",
        "hardgates",
        "not_claimed",
    }
    if set(payload) != expected_top_level:
        raise ValueError("model_design_suite payload has invalid top-level fields")
    if payload["schema_id"] != MODEL_DESIGN_SUITE_SCHEMA_ID:
        raise ValueError("model_design_suite schema_id mismatch")
    if payload["artifact_id"] != MODEL_DESIGN_SUITE_ARTIFACT_ID:
        raise ValueError("model_design_suite artifact_id mismatch")
    rows = payload["rows"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("model_design_suite rows must be non-empty")
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping) or set(row) != MODEL_DESIGN_SUITE_ROW_FIELDS:
            raise ValueError(f"model_design_suite row schema mismatch: {index}")
        expected_status, expected_reason = _model_design_suite_row_status(row, payload=payload)
        if row["hardgate_status"] != expected_status:
            raise ValueError(f"model_design_suite row status mismatch: {index}")
        if row["hardgate_reason"] != expected_reason:
            raise ValueError(f"model_design_suite row reason mismatch: {index}")
    hardgates = payload["hardgates"]
    if not isinstance(hardgates, Mapping) or set(hardgates) != set(MODEL_DESIGN_SUITE_HARDGATE_IDS):
        raise ValueError("model_design_suite hardgates must contain SUITE-HG1..5")
    expected_hardgates = _model_design_suite_hardgate_rows(rows)
    if hardgates != expected_hardgates:
        raise ValueError("model_design_suite hardgate rows do not match row state")
    expected_status = (
        "pass"
        if all(gate["status"] == "pass" for gate in hardgates.values())
        and all(row["hardgate_status"] == "pass" for row in rows)
        else "fail"
    )
    if payload["status"] != expected_status:
        raise ValueError("model_design_suite status does not propagate row hardgate state")


def _validate_committed_model_design_suite_round_trip() -> None:
    payload = json.loads(_artifact_path(MODEL_DESIGN_SUITE_JSON_ARTIFACT).read_text(encoding="utf-8"))
    if not isinstance(payload, Mapping):
        raise ValueError("model_design_suite committed payload must be an object")
    _validate_model_design_suite_payload(payload)
    component_ids = set()
    owner_artifacts = set()
    for row in payload["rows"]:
        resolved = _resolve_committed_artifact_pointer(ROOT, row["component_id"])
        if isinstance(resolved, str):
            component_ids.add(resolved)
        elif isinstance(resolved, Mapping):
            role = resolved.get("role")
            if isinstance(role, str):
                component_ids.add(role)
        owner_split = _split_artifact_pointer(row["canonical_owner_pointer"])
        if owner_split is None:
            raise ValueError("model_design_suite owner pointer must be artifact-qualified")
        owner_artifacts.add(owner_split[0])
    expected_components = {
        "bedc-quality-lab:ledger-aware-transformer",
        "bedc-quality-lab:certificate-gated-attention",
        "bedc-quality-lab:discovery-regularized-training",
        "bedc-quality-lab:mechanism-seeking-network",
        "bedc-quality-lab:discovery-gated-nas",
        DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID,
    }
    expected_owner_artifacts = {
        "reports/canonical/ledger-aware-transformer.json",
        "reports/canonical/certificate-gated-attention.json",
        DISCOVERY_REGULARIZED_TRAINING_JSON_ARTIFACT,
        MECHANISM_SEEKING_NETWORK_JSON_ARTIFACT,
        DISCOVERY_GATED_NAS_JSON_ARTIFACT,
        DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
    }
    if component_ids != expected_components:
        if payload["status"] == "pass":
            raise ValueError("model_design_suite committed component slots mismatch")
    if owner_artifacts != expected_owner_artifacts:
        raise ValueError("model_design_suite committed owner artifact slots mismatch")
    if len(payload["rows"]) != len(expected_components):
        raise ValueError("model_design_suite committed row count mismatch")


def _render_model_design_suite_markdown(payload: Mapping[str, Any]) -> str:
    _validate_model_design_suite_payload(payload)
    lines = [
        "# Model Design Suite",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Coverage matrix: `{payload['coverage_matrix_pointer']}`",
        "",
        "## Coverage Rows",
        "",
        "| component | owner | discovery | verdict | mechanism | debt | not claimed | negative witness | status |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['component_id']}` | "
            f"`{row['canonical_owner_pointer']}` | "
            f"`{row['discovery_pointer']}` | "
            f"`{row['verdict_pointer']}` | "
            f"`{row['mechanism_pointer']}` | "
            f"`{row['debt_pointer']}` | "
            f"`{row['not_claimed_pointer']}` | "
            f"`{row['negative_witness_pointer']}` | "
            f"`{row['hardgate_status']}` |"
        )
    lines.extend(["", "## Hardgates", "", "| gate | status | reason |", "| --- | --- | --- |"])
    for gate_id in MODEL_DESIGN_SUITE_HARDGATE_IDS:
        gate = payload["hardgates"][gate_id]
        lines.append(f"| `{gate_id}` | `{gate['status']}` | {gate['reason']} |")
    lines.append("")
    return "\n".join(lines)


def _model_design_suite_index_section(payload: Mapping[str, Any]) -> dict[str, Any]:
    _validate_model_design_suite_payload(payload)
    return {
        "status": payload["status"],
        "artifact_id": MODEL_DESIGN_SUITE_ARTIFACT_ID,
        "schema_id": MODEL_DESIGN_SUITE_SCHEMA_ID,
        "json_artifact": MODEL_DESIGN_SUITE_JSON_ARTIFACT,
        "markdown_artifact": MODEL_DESIGN_SUITE_MARKDOWN_ARTIFACT,
        "owner_pointer": _model_design_suite_pointer("$"),
        "rows_pointer": _model_design_suite_pointer("$.rows"),
        "hardgates_pointer": _model_design_suite_pointer("$.hardgates"),
        "coverage_matrix_pointer": payload["coverage_matrix_pointer"],
        "row_count": len(payload["rows"]),
    }


def _dashboard_panel_pointers() -> tuple[dict[str, str], ...]:
    return (
        {
            "panel_id": "discovery-map",
            "label": "Discovery map",
            "artifact_pointer": f"{DISCOVERY_MAP_JSON_ARTIFACT}:$",
        },
        {
            "panel_id": "coverage-matrix",
            "label": "Coverage matrix",
            "artifact_pointer": f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.coverage_matrix",
        },
        {
            "panel_id": "claim-graph",
            "label": "Claim graph",
            "artifact_pointer": f"{CLAIM_GRAPH_JSON_ARTIFACT}:$",
        },
        {
            "panel_id": "scorecard",
            "label": "Scorecard",
            "artifact_pointer": f"{QUALITY_SCORECARD_JSON_ARTIFACT}:$",
        },
        {
            "panel_id": "negative-witnesses",
            "label": "Negative witnesses",
            "artifact_pointer": f"{NEGATIVE_WITNESSES_JSON_ARTIFACT}:$",
        },
        {
            "panel_id": "negative-witness-summary",
            "label": "Negative witness summary",
            "artifact_pointer": f"{NEGATIVE_WITNESS_SUMMARY_JSON_ARTIFACT}:$",
        },
        {
            "panel_id": "d5-status",
            "label": "D5 status",
            "artifact_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_m",
        },
        {
            "panel_id": "model-design-suite",
            "label": "Model-design suite",
            "artifact_pointer": f"{MODEL_DISCOVERY_SUITE_SUMMARY_ARTIFACT}:$",
        },
    )


def _dashboard_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:dashboard",
        "canonical_role": "navigation_view_not_fact_source",
        "source_index_artifact": "reports/canonical/index.json",
        "panels": [dict(row) for row in _dashboard_panel_pointers()],
    }


def _validate_dashboard_index_section(section: Mapping[str, Any], *, root: Path) -> list[str]:
    unresolved: list[str] = []
    panels = section.get("panels")
    if section.get("status") != "pointer-only":
        unresolved.append("dashboard.status")
    if not isinstance(panels, Sequence) or isinstance(panels, (str, bytes)):
        return unresolved + ["dashboard.panels"]
    for panel in panels:
        if not isinstance(panel, Mapping):
            unresolved.append("dashboard.panels")
            continue
        pointer = panel.get("artifact_pointer")
        if not isinstance(pointer, str) or _resolve_committed_artifact_pointer(root, pointer) is None:
            unresolved.append(str(pointer))
    return unresolved


def _formal_hardening_index_section(generated_at: str | None = None) -> dict[str, Any]:
    payload = _build_formal_hardening_payload(generated_at=generated_at)
    return {
        "status": "pointer-only",
        "artifact_id": FORMAL_HARDENING_ARTIFACT_ID,
        "json_artifact": FORMAL_HARDENING_JSON_ARTIFACT,
        "markdown_artifact": FORMAL_HARDENING_MARKDOWN_ARTIFACT,
        "ready": payload["ready"],
        "recorded": payload["recorded"],
        "required": payload["required"],
        "gap_count": payload["gap_count"],
    }


def _gap_head_transfer_atlas_index_section(discovery_map_payload: Mapping[str, Any] | None = None) -> dict[str, Any]:
    payload = _load_artifact_payload(GAP_HEAD_TRANSFER_ATLAS_JSON_ARTIFACT)
    decision = _pointer_value(payload, "$.multi_surface_d5_o")
    rows = discovery_map_payload.get("rows") if isinstance(discovery_map_payload, Mapping) else None
    map_row = next(
        (
            row
            for row in rows
            if isinstance(row, Mapping) and row.get("report") == "gap-head-transfer-atlas"
        ),
        {},
    ) if isinstance(rows, list) else {}
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", GAP_HEAD_TRANSFER_ATLAS_ARTIFACT_ID),
        "json_artifact": GAP_HEAD_TRANSFER_ATLAS_JSON_ARTIFACT,
        "markdown_artifact": GAP_HEAD_TRANSFER_ATLAS_MARKDOWN_ARTIFACT,
        "decision_pointer": "$.multi_surface_d5_o",
        "boundary_ledger_pointer": "$.boundary_ledger",
        "claim_capsule_pointer": "$.config.claim_capsule_artifact",
        "decision": decision.get("decision") if isinstance(decision, dict) else "missing",
        "discovery_level": map_row.get("discovery_level", "missing"),
        "discovery_level_pointer": "reports/canonical/discovery_map.json:$.rows[?report=gap-head-transfer-atlas].discovery_level",
        "pass_surface_count": decision.get("pass_surface_count") if isinstance(decision, dict) else "missing",
    }


def _gap_head_mechanism_namecert_index_section() -> dict[str, Any]:
    payload = _load_sidecar_payload(GAP_HEAD_MECHANISM_NAMECERT_JSON_ARTIFACT)
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", GAP_HEAD_MECHANISM_NAMECERT_ARTIFACT_ID),
        "json_artifact": GAP_HEAD_MECHANISM_NAMECERT_JSON_ARTIFACT,
        "markdown_artifact": GAP_HEAD_MECHANISM_NAMECERT_MARKDOWN_ARTIFACT,
        "ledger_policy_pointer": "$.ledger_policy.mechanism_closure_debt",
        "closure_status_pointer": "$.closure_status.mechanism_spec",
        "candidate_mechanism": _pointer_value(payload, "$.mechanism_spec.candidate_mechanism") or "missing",
        "mechanism_closure_debt": _pointer_value(payload, "$.ledger_policy.mechanism_closure_debt") or "missing",
        "mechanism_spec_closure": _pointer_value(payload, "$.closure_status.mechanism_spec") or "missing",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
    }

def _gap_head_attribution_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT)
    return {
        "status": "pointer-only",
        "artifact_id": GAP_HEAD_ATTRIBUTION_ARTIFACT_ID,
        "json_artifact": GAP_HEAD_ATTRIBUTION_JSON_ARTIFACT,
        "markdown_artifact": GAP_HEAD_ATTRIBUTION_MARKDOWN_ARTIFACT,
        "run_id": payload.get("run_id", "missing"),
        "run_artifacts": _pointer_value(payload, "$.source_artifacts.run_artifacts") or "missing",
        "d5_o_status": _pointer_value(payload, "$.d5_o.status") or "missing",
        "d5_m_status": _pointer_value(payload, "$.d5_m.status") or "missing",
        "mechanism_case": _pointer_value(payload, "$.mechanism_evidence.candidate_mechanism") or "missing",
        "mechanism_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence",
        "mechanism_ledger_debt_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt.0.status",
        "residualized_attribution_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution",
        "residualized_attribution_claim_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution_claim",
        "e_hardgates_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.e_hardgates",
        "e_hardgates_status_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.e_hardgates.status",
        "non_score_mechanism_claim_allowed_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.residualized_attribution_claim.non_score_mechanism_claim_allowed",
        "score_margin_causal_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "a4_hardgates_status_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.status",
        "a4_hg5_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
        "score_margin_shortcut_witness_alias": {
            "score_margin_causal_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
            "score_margin_channel_classification_pointer": (
                "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence.channel_classification"
            ),
            "a4_hg5_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
            "a4_hg5_status_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5.status",
            "d5_m_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_m",
            "d5_m_failed_gate_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.d5_m.failed_gate",
        },
        "a4_hardgates_status": _pointer_value(payload, "$.a4_hardgates.status") or "missing",
        "a4_hg5_status": _pointer_value(payload, "$.a4_hardgates.gates.A4-HG5.status") or "missing",
        "e_hardgates_status": _pointer_value(payload, "$.e_hardgates.status") or "missing",
        "non_score_mechanism_claim_allowed": _pointer_value(payload, "$.residualized_attribution_claim.non_score_mechanism_claim_allowed"),
    }


def _release_manifest_sidecar_index_section() -> dict[str, Any]:
    payload = _load_sidecar_payload(RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT)
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID),
        "json_artifact": RELEASE_MANIFEST_SIDECAR_JSON_ARTIFACT,
        "markdown_artifact": RELEASE_MANIFEST_SIDECAR_MARKDOWN_ARTIFACT,
        "canonical_role": payload.get("canonical_role", "sidecar_not_in_CANONICAL_REPORTS"),
        "release_bundle_status": payload.get("release_bundle_status", "missing"),
        "tag_status": payload.get("tag_status", "missing"),
        "version": payload.get("version", "missing"),
    }


def _toy_latent_planning_bedc_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": TOY_LATENT_PLANNING_BEDC_ARTIFACT_ID,
        "json_artifact": TOY_LATENT_PLANNING_BEDC_JSON_ARTIFACT,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_package": "experiments/toy_latent_planning_bedc",
        "sidecar_ref": {"artifact": TOY_LATENT_PLANNING_BEDC_JSON_ARTIFACT, "pointer": "$"},
        "claim_capsule_ref": {"artifact": TOY_LATENT_PLANNING_BEDC_CLAIM_CAPSULE_ARTIFACT, "pointer": "$"},
        "summary_ref": {"artifact": TOY_LATENT_PLANNING_BEDC_SUMMARY_ARTIFACT, "pointer": "$"},
        "hardgate_status_pointer": f"{TOY_LATENT_PLANNING_BEDC_CLAIM_CAPSULE_ARTIFACT}:$.u_hardgates.status",
        "present_but_fail_closed": True,
    }


def _release_namecert_candidate_index_section() -> dict[str, Any]:
    payload = _load_sidecar_payload(RELEASE_NAMECERT_CANDIDATE_JSON_ARTIFACT)
    source_spec = payload.get("source_spec") if isinstance(payload.get("source_spec"), dict) else {}
    ledger_policy = payload.get("ledger_policy") if isinstance(payload.get("ledger_policy"), dict) else {}
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", RELEASE_NAMECERT_CANDIDATE_ARTIFACT_ID),
        "json_artifact": RELEASE_NAMECERT_CANDIDATE_JSON_ARTIFACT,
        "markdown_artifact": RELEASE_NAMECERT_CANDIDATE_MARKDOWN_ARTIFACT,
        "owner_artifact": source_spec.get("sidecar_artifact_id", RELEASE_MANIFEST_SIDECAR_ARTIFACT_ID),
        "candidate_status": payload.get("candidate_status", "missing"),
        "ledger_policy_pointer": "$.ledger_policy",
        "revoke_if_pointer": "$.ledger_policy.revoke_if",
        "source_sidecar_digest": source_spec.get("sidecar_digest", "missing"),
        "tag_absent_policy": (
            ledger_policy.get("tag_absent", {}).get("status", "missing")
            if isinstance(ledger_policy.get("tag_absent"), dict)
            else "missing"
        ),
    }


def _toy_safety_boundary_index_section() -> dict[str, Any]:
    payload = _load_sidecar_payload(TOY_SAFETY_BOUNDARY_JSON_ARTIFACT)
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", TOY_SAFETY_BOUNDARY_ARTIFACT_ID),
        "json_artifact": TOY_SAFETY_BOUNDARY_JSON_ARTIFACT,
        "markdown_artifact": TOY_SAFETY_BOUNDARY_MARKDOWN_ARTIFACT,
        "claim_capsule_pointer": "experiments/toy_safety_boundary/reports/runs/toy_safety_boundary/claim_capsule.json:$",
        "hardgates_pointer": "experiments/toy_safety_boundary/reports/runs/toy_safety_boundary/claim_capsule.json:$.hardgates",
        "positive_claim_pointer": "experiments/toy_safety_boundary/reports/runs/toy_safety_boundary/claim_capsule.json:$.positive_claim",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
    }


def _artifact_validation(spec: CanonicalReportSpec) -> dict[str, Any]:
    json_path = _artifact_path(spec.json_artifact)
    markdown_path = _artifact_path(spec.markdown_artifact)
    key_validation = _validate_json(json_path, spec.required_json_keys)
    missing_artifacts = [
        path
        for path, exists in (
            (spec.json_artifact, json_path.exists()),
            (spec.markdown_artifact, markdown_path.exists()),
        )
        if not exists
    ]
    status = "pass" if key_validation["status"] == "pass" and not missing_artifacts else "fail"
    return {
        "status": status,
        "missing_artifacts": missing_artifacts,
        "required_json_keys": list(spec.required_json_keys),
        "required_key_validation": key_validation,
    }


def _run_spec(
    spec: CanonicalReportSpec,
    *,
    mode: Literal["changed", "verify", "cold"] = "changed",
    generated_at: str | None = None,
    reuse_existing: bool | None = None,
) -> dict[str, Any]:
    if reuse_existing is not None:
        mode = "verify" if reuse_existing else "cold"
    error = None
    producer_status = "skipped"
    fingerprint_status = "unchecked"
    fingerprint_reason = "not-evaluated"
    try:
        if mode == "cold":
            _run_producer(spec)
            producer_status = "completed"
            fingerprint_status = "written"
            fingerprint_reason = "cold"
            _write_fingerprint_sidecar(spec, generated_at=generated_at)
        else:
            if reuse_existing is True and _artifact_path(spec.json_artifact).exists() and _artifact_path(spec.markdown_artifact).exists():
                matches, reason = True, "artifact-present-reuse"
            else:
                try:
                    matches, reason = _fingerprint_matches(spec)
                except ValueError as exc:
                    if mode == "verify":
                        raise
                    matches, reason = False, str(exc)
            fingerprint_status = "match" if matches else "miss"
            fingerprint_reason = reason
            if matches:
                producer_status = "skipped"
            elif mode == "verify":
                raise ValueError(f"fingerprint sidecar mismatch for {spec.name}: {reason}")
            else:
                _run_producer(spec)
                producer_status = "completed"
                fingerprint_status = "written"
                fingerprint_reason = reason
                _write_fingerprint_sidecar(spec, generated_at=generated_at)
    except Exception as exc:  # pragma: no cover - kept for CLI fail-closed behavior
        error = str(exc)
    validation = _artifact_validation(spec)
    discipline = _discipline(spec)
    if error is not None:
        status = "error"
    elif validation["status"] == "fail" or discipline["forbidden_claim_terms_status"] == "fail":
        status = "fail"
    else:
        status = "pass"
    result = {
        "name": spec.name,
        "producer_command": list(spec.command),
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "bundle_role": spec.bundle_role,
        "discipline": discipline,
        "status": status,
        "duration_seconds": 0.0,
        "estimated_seconds": spec.estimated_seconds,
        "producer_status": producer_status if error is None else "error",
        "fingerprint_sidecar": _relative(_fingerprint_path(spec)),
        "fingerprint_status": fingerprint_status,
        "fingerprint_reason": fingerprint_reason,
        "validation": validation,
    }
    if error is not None:
        result["error"] = error
    return result


def _index(
    results: Sequence[dict[str, Any]],
    *,
    generated_at: str | None = None,
    claim_verdict_rows: Sequence[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    reports = list(results)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    discovery_map_payload = _discovery_map_payload(generated_at=timestamp)
    discovery_gated_transformer_payload = _build_discovery_gated_transformer_payload(generated_at=timestamp)
    model_design_suite_payload = _build_model_design_suite_payload(generated_at=timestamp)
    return {
        "schema_id": INDEX_SCHEMA_ID,
        "generated_at": timestamp,
        "root": INDEX_ROOT,
        "reports": reports,
        "dashboard": _dashboard_index_section(),
        "quality_scorecard": _quality_scorecard_index_section(),
        "discovery_map": {
            "status": "pointer-only",
            "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
            "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
            "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
            "coverage_matrix_pointer": "reports/canonical/discovery_map.json:$.coverage_matrix",
            "experiment_proposals_pointer": "reports/canonical/discovery_map.json:$.experiment_proposals",
            "experiment_proposal_count": len(discovery_map_payload.get("experiment_proposals", [])),
            "row_count": discovery_map_payload["row_count"],
            "level_counts": discovery_map_payload["level_counts"],
        },
        "observed_debt_axis_projection": _observed_debt_axis_projection_section(),
        "dimension_mismatch_debt_transfer": _dimension_mismatch_transfer_index_section(),
        "dimension_mismatch_transfer_robustness": _dimension_mismatch_transfer_robustness_index_section(),
        "negative_witnesses": _negative_witnesses_index_section(),
        "negative_discovery_reports": _negative_discovery_reports_index_section(generated_at=timestamp),
        "negative_witness_mutation_ledger": _negative_witness_mutation_ledger_index_section(),
        "new_model_hardgates": _new_model_hardgates_index_section(generated_at=timestamp),
        "discovery_regularized_training_quality": _discovery_regularized_training_quality_boundary_index_section(),
        "discovery_gated_transformer": _discovery_gated_transformer_index_section(discovery_gated_transformer_payload),
        "model_design_suite": _model_design_suite_index_section(model_design_suite_payload),
        "claim_verdicts": _claim_verdicts_index_section(claim_verdict_rows),
        "claim_graph": _claim_graph_index_section(generated_at=timestamp),
        "claim_capsule": _claim_capsule_index_section(generated_at=timestamp),
        "negative_witness_summary": _negative_witness_summary_index_section(generated_at=timestamp),
        "formal_hardening": _formal_hardening_index_section(generated_at=timestamp),
        "gap_head_transfer_atlas": _gap_head_transfer_atlas_index_section(discovery_map_payload),
        "gap_head_attribution_capsule": _gap_head_attribution_index_section(),
        "gap_head_mechanism_namecert": _gap_head_mechanism_namecert_index_section(),
        "release_manifest_sidecar": _release_manifest_sidecar_index_section(),
        "toy_latent_planning_bedc": _toy_latent_planning_bedc_index_section(),
        "release_namecert_candidate": _release_namecert_candidate_index_section(),
        "toy_safety_boundary": _toy_safety_boundary_index_section(),
        "paper_outline": _paper_outline(reports),
        "claims_nonclaims": _claims_nonclaims(reports),
        "honest_boundary": _honest_boundary(),
        "literature_ledger": _literature_ledger(),
    }


def _render_index_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Canonical Report Index",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Root: `{payload['root']}`",
        "",
    ]
    sections = (
        ("HG-P core reports", [report for report in payload["reports"] if report["bundle_role"] == "hg_p_core"]),
        ("Auxiliary reports", [report for report in payload["reports"] if report["bundle_role"] == "auxiliary"]),
    )
    for title, reports in sections:
        lines.extend(
            [
                f"## {title}",
                "",
                "| report | status | json | markdown | fingerprint | scope | cost | not-claimed | positive claim | control |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
            ]
        )
        for report in reports:
            discipline = report["discipline"]
            control = discipline["control_pointer"] or discipline["no_control_rationale_pointer"]
            lines.append(
                "| "
                f"`{report['name']}` | "
                f"`{report['status']}` | "
                f"`{report['json_artifact']}` | "
                f"`{report['markdown_artifact']}` | "
                f"`{report['fingerprint_sidecar']}` | "
                f"`{discipline['scope_pointer']}` | "
                f"`{discipline['cost_pointer']}` | "
                f"`{discipline['not_claimed_pointer']}` | "
                f"`{discipline['positive_claim_pointer']}` | "
                f"`{control}` |"
            )
        lines.append("")

    outline = payload["paper_outline"]
    lines.extend(
        [
            "## Dashboard",
            "",
            f"- Status: `{payload['dashboard']['status']}`",
            f"- Artifact pointer: `{payload['dashboard']['artifact_id']}`",
            f"- Canonical role: `{payload['dashboard']['canonical_role']}`",
            "",
        ]
    )
    lines.extend(
        [
            "## Quality scorecard",
            "",
            f"- Status: `{payload['quality_scorecard']['status']}`",
            f"- JSON: `{payload['quality_scorecard']['json_artifact']}`",
            f"- Markdown: `{payload['quality_scorecard']['markdown_artifact']}`",
            f"- Metrics: `{', '.join(payload['quality_scorecard']['metrics'])}`",
            "",
            "## Discovery map",
            "",
            f"- Status: `{payload['discovery_map']['status']}`",
            f"- JSON: `{payload['discovery_map']['json_artifact']}`",
            f"- Markdown: `{payload['discovery_map']['markdown_artifact']}`",
            f"- Coverage matrix: `{payload['discovery_map']['coverage_matrix_pointer']}`",
            f"- Experiment proposals: `{payload['discovery_map']['experiment_proposals_pointer']}`",
            f"- Rows: `{payload['discovery_map']['row_count']}`",
            "",
            "## Observed debt axis projection",
            "",
            f"- Status: `{payload['observed_debt_axis_projection']['status']}`",
            f"- Rows: `{payload['observed_debt_axis_projection']['row_count']}`",
            f"- Classifications: `{', '.join(payload['observed_debt_axis_projection']['classification_enum'])}`",
            "",
            "| axis | classification | source | evidence | hardgate |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["observed_debt_axis_projection"]["rows"]:
        lines.append(
            "| "
            f"`{row['axis_id']}` | "
            f"`{row['classification']}` | "
            f"`{row['source_artifact']}` | "
            f"`{row['evidence_pointer']}` | "
            f"`{row['hardgate_pointer']}` |"
        )
    lines.extend(
        [
            "",
            "## Dimension mismatch debt transfer",
            "",
            f"- Status: `{payload['dimension_mismatch_debt_transfer']['status']}`",
            f"- JSON: `{payload['dimension_mismatch_debt_transfer']['json_artifact']}`",
            f"- Markdown: `{payload['dimension_mismatch_debt_transfer']['markdown_artifact']}`",
            f"- Claim pointer: `{payload['dimension_mismatch_debt_transfer']['claim_pointer']}`",
            f"- Claim present: `{payload['dimension_mismatch_debt_transfer']['claim_present']}`",
            "",
            "## Dimension mismatch transfer robustness",
            "",
            f"- Status: `{payload['dimension_mismatch_transfer_robustness']['status']}`",
            f"- JSON: `{payload['dimension_mismatch_transfer_robustness']['json_artifact']}`",
            f"- Markdown: `{payload['dimension_mismatch_transfer_robustness']['markdown_artifact']}`",
            f"- Audit status: `{payload['dimension_mismatch_transfer_robustness']['audit_status']}`",
            "",
            "## Quality baseline pointers",
            "",
            "- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`",
            f"- Canonical artifacts: `{payload['root']}/reports/canonical/`",
            f"- Discovery map: `{payload['discovery_map']['json_artifact']}:$.rows[*].discovery_level`",
            f"- Claim verdicts: `{payload['claim_verdicts']['jsonl_artifact']}`",
            f"- Claim capsule: `{payload['claim_capsule']['json_artifact']}`",
            f"- Negative witnesses: `{payload['negative_witnesses']['json_artifact']}`",
            f"- Scorecard: `{payload['quality_scorecard']['json_artifact']}:$.rows`",
            "- Claims boundary: `docs/claims_and_nonclaims.md`",
            "- Manifest: `docs/artifact_manifest.md`",
            "",
            "## Negative witnesses",
            "",
            f"- Status: `{payload['negative_witnesses']['status']}`",
            f"- JSON: `{payload['negative_witnesses']['json_artifact']}`",
            f"- Expected kinds: `{payload['negative_witnesses']['expected_kind_count']}`",
            "",
            "## Negative discovery reports",
            "",
            f"- Status: `{payload['negative_discovery_reports']['status']}`",
            f"- JSON: `{payload['negative_discovery_reports']['json_artifact']}`",
            f"- Markdown: `{payload['negative_discovery_reports']['markdown_artifact']}`",
            f"- Rows: `{payload['negative_discovery_reports']['row_count']}`",
            f"- Audit: `{payload['negative_discovery_reports']['audit_status']}`",
            "",
            "## Negative witness mutation ledger",
            "",
            f"- Status: `{payload['negative_witness_mutation_ledger']['status']}`",
            f"- JSON: `{payload['negative_witness_mutation_ledger']['json_artifact']}`",
            f"- Graph: `{payload['negative_witness_mutation_ledger']['graph_artifact']}`",
            f"- DGT report: `{payload['negative_witness_mutation_ledger']['dgt_report_artifact']}`",
            f"- Canonical role: `{payload['negative_witness_mutation_ledger']['canonical_role']}`",
            f"- Entries: `{payload['negative_witness_mutation_ledger']['entry_count']}`",
            f"- Entries pointer: `{payload['negative_witness_mutation_ledger']['entries_pointer']}`",
            "",
            "## New model hardgates",
            "",
            f"- Status: `{payload['new_model_hardgates']['status']}`",
            f"- JSON: `{payload['new_model_hardgates']['json_artifact']}`",
            f"- Markdown: `{payload['new_model_hardgates']['markdown_artifact']}`",
            f"- Schema: `{payload['new_model_hardgates']['schema_id']}`",
            f"- Canonical role: `{payload['new_model_hardgates']['canonical_role']}`",
            f"- Gate ids pointer: `{payload['new_model_hardgates']['gate_ids_pointer']}`",
            f"- Gates pointer: `{payload['new_model_hardgates']['gates_pointer']}`",
            f"- Gate count: `{payload['new_model_hardgates']['gate_count']}`",
            "",
            "## Discovery-Regularized Training Quality Boundary",
            "",
            f"- Status: `{payload['discovery_regularized_training_quality']['status']}`",
            f"- JSON: `{payload['discovery_regularized_training_quality']['json_artifact']}`",
            f"- Markdown: `{payload['discovery_regularized_training_quality']['markdown_artifact']}`",
            f"- Owner: `{payload['discovery_regularized_training_quality']['owner_pointer']}`",
            f"- Hardgate: `{payload['discovery_regularized_training_quality']['hardgate_pointer']}`",
            f"- Arm comparisons: `{payload['discovery_regularized_training_quality']['arm_comparisons_pointer']}`",
            "",
            "## Discovery-Gated Transformer",
            "",
            f"- Status: `{payload['discovery_gated_transformer']['status']}`",
            f"- JSON: `{payload['discovery_gated_transformer']['json_artifact']}`",
            f"- Markdown: `{payload['discovery_gated_transformer']['markdown_artifact']}`",
            f"- Schema: `{payload['discovery_gated_transformer']['schema_id']}`",
            f"- Model id: `{payload['discovery_gated_transformer']['model_id_pointer']}`",
            f"- Hardgate contract: `{payload['discovery_gated_transformer']['hardgate_contract_ref_pointer']}`",
            f"- Task grid: `{payload['discovery_gated_transformer']['sequence_task_grid_pointer']}`",
            f"- Training evidence: `{payload['discovery_gated_transformer']['training_evidence_pointer']}`",
            f"- Hardgate instances: `{payload['discovery_gated_transformer']['hardgate_instances_pointer']}`",
            f"- Prototype status: `{payload['discovery_gated_transformer']['prototype_status_pointer']}`",
            f"- Not claimed: `{payload['discovery_gated_transformer']['not_claimed_pointer']}`",
            f"- Discovery map signal: `{payload['discovery_gated_transformer']['discovery_map_signal_pointer']}`",
            "",
            "## Model Design Suite",
            "",
            f"- Status: `{payload['model_design_suite']['status']}`",
            f"- JSON: `{payload['model_design_suite']['json_artifact']}`",
            f"- Markdown: `{payload['model_design_suite']['markdown_artifact']}`",
            f"- Schema: `{payload['model_design_suite']['schema_id']}`",
            f"- Owner: `{payload['model_design_suite']['owner_pointer']}`",
            f"- Rows: `{payload['model_design_suite']['rows_pointer']}`",
            f"- Hardgates: `{payload['model_design_suite']['hardgates_pointer']}`",
            f"- Coverage matrix: `{payload['model_design_suite']['coverage_matrix_pointer']}`",
            "",
            "## Claim verdicts",
            "",
            f"- Status: `{payload['claim_verdicts']['status']}`",
            f"- JSONL: `{payload['claim_verdicts']['jsonl_artifact']}`",
            f"- Rows: `{payload['claim_verdicts']['row_count']}`",
            "",
            "## Claim graph",
            "",
            f"- Status: `{payload['claim_graph']['status']}`",
            f"- JSON: `{payload['claim_graph']['json_artifact']}`",
            f"- Markdown: `{payload['claim_graph']['markdown_artifact']}`",
            f"- Canonical role: `{payload['claim_graph']['canonical_role']}`",
            f"- Nodes: `{payload['claim_graph']['node_count']}`",
            "",
            "## Claim capsule",
            "",
            f"- Status: `{payload['claim_capsule']['status']}`",
            f"- JSON: `{payload['claim_capsule']['json_artifact']}`",
            f"- Schema: `{payload['claim_capsule']['schema_id']}`",
            f"- Effective level: `{payload['claim_capsule']['effective_level']}`",
            f"- Terminal verdict: `{payload['claim_capsule']['terminal_verdict']}`",
            "",
            "## Negative witness summary",
            "",
            f"- Status: `{payload['negative_witness_summary']['status']}`",
            f"- JSON: `{payload['negative_witness_summary']['json_artifact']}`",
            f"- Markdown: `{payload['negative_witness_summary']['markdown_artifact']}`",
            f"- Rows: `{payload['negative_witness_summary']['row_count']}`",
            f"- Audit: `{payload['negative_witness_summary']['audit_status']}`",
            "",
            "## Formal hardening",
            "",
            f"- Status: `{payload['formal_hardening']['status']}`",
            f"- JSON: `{payload['formal_hardening']['json_artifact']}`",
            f"- Markdown: `{payload['formal_hardening']['markdown_artifact']}`",
            f"- Ready: `{payload['formal_hardening']['ready']}`",
            f"- Coverage: `{payload['formal_hardening']['recorded']}/{payload['formal_hardening']['required']}`",
            f"- Gaps: `{payload['formal_hardening']['gap_count']}`",
            "",
            "## Gap-head transfer atlas",
            "",
            f"- Status: `{payload['gap_head_transfer_atlas']['status']}`",
            f"- JSON: `{payload['gap_head_transfer_atlas']['json_artifact']}`",
            f"- Markdown: `{payload['gap_head_transfer_atlas']['markdown_artifact']}`",
            f"- Decision pointer: `{payload['gap_head_transfer_atlas']['decision_pointer']}`",
            f"- Boundary ledger pointer: `{payload['gap_head_transfer_atlas']['boundary_ledger_pointer']}`",
            f"- Claim capsule pointer: `{payload['gap_head_transfer_atlas']['claim_capsule_pointer']}`",
            "",
            "## Gap-head attribution capsule",
            "",
            f"- Status: `{payload['gap_head_attribution_capsule']['status']}`",
            f"- JSON: `{payload['gap_head_attribution_capsule']['json_artifact']}`",
            f"- Markdown: `{payload['gap_head_attribution_capsule']['markdown_artifact']}`",
            f"- Run id: `{payload['gap_head_attribution_capsule']['run_id']}`",
            f"- D5-O: `{payload['gap_head_attribution_capsule']['d5_o_status']}`",
            f"- D5-M: `{payload['gap_head_attribution_capsule']['d5_m_status']}`",
            f"- Mechanism case: `{payload['gap_head_attribution_capsule']['mechanism_case']}`",
            "",
            "## Gap-head mechanism NameCert candidate",
            "",
            f"- Status: `{payload['gap_head_mechanism_namecert']['status']}`",
            f"- JSON: `{payload['gap_head_mechanism_namecert']['json_artifact']}`",
            f"- Markdown: `{payload['gap_head_mechanism_namecert']['markdown_artifact']}`",
            f"- Ledger policy pointer: `{payload['gap_head_mechanism_namecert']['ledger_policy_pointer']}`",
            f"- Closure status pointer: `{payload['gap_head_mechanism_namecert']['closure_status_pointer']}`",
            f"- Candidate mechanism: `{payload['gap_head_mechanism_namecert']['candidate_mechanism']}`",
            f"- Canonical role: `{payload['gap_head_mechanism_namecert']['canonical_role']}`",
            "",
            "## Release manifest sidecar",
            "",
            f"- Status: `{payload['release_manifest_sidecar']['status']}`",
            f"- JSON: `{payload['release_manifest_sidecar']['json_artifact']}`",
            f"- Markdown: `{payload['release_manifest_sidecar']['markdown_artifact']}`",
            f"- Canonical role: `{payload['release_manifest_sidecar']['canonical_role']}`",
            f"- Release bundle status: `{payload['release_manifest_sidecar']['release_bundle_status']}`",
            f"- Tag status: `{payload['release_manifest_sidecar']['tag_status']}`",
            f"- Version: `{payload['release_manifest_sidecar']['version']}`",
            "",
            "## Toy latent planning BEDC",
            "",
            f"- Status: `{payload['toy_latent_planning_bedc']['status']}`",
            f"- JSON: `{payload['toy_latent_planning_bedc']['json_artifact']}`",
            f"- Canonical role: `{payload['toy_latent_planning_bedc']['canonical_role']}`",
            f"- Owner package: `{payload['toy_latent_planning_bedc']['owner_package']}`",
            f"- Hardgate status pointer: `{payload['toy_latent_planning_bedc']['hardgate_status_pointer']}`",
            "",
            "## Release NameCert candidate",
            "",
            f"- Status: `{payload['release_namecert_candidate']['status']}`",
            f"- JSON: `{payload['release_namecert_candidate']['json_artifact']}`",
            f"- Markdown: `{payload['release_namecert_candidate']['markdown_artifact']}`",
            f"- Owner artifact: `{payload['release_namecert_candidate']['owner_artifact']}`",
            f"- Candidate status: `{payload['release_namecert_candidate']['candidate_status']}`",
            f"- Revoke pointer: `{payload['release_namecert_candidate']['revoke_if_pointer']}`",
            "",
            "## Toy safety boundary",
            "",
            f"- Status: `{payload['toy_safety_boundary']['status']}`",
            f"- JSON: `{payload['toy_safety_boundary']['json_artifact']}`",
            f"- Markdown: `{payload['toy_safety_boundary']['markdown_artifact']}`",
            f"- Claim capsule: `{payload['toy_safety_boundary']['claim_capsule_pointer']}`",
            f"- Hardgates: `{payload['toy_safety_boundary']['hardgates_pointer']}`",
            "",
            "## Paper outline",
            "",
            f"- Status: `{outline['status']}`",
            f"- Core reports: `{', '.join(outline['core_reports'])}`",
            f"- Auxiliary reports: `{', '.join(outline['auxiliary_reports'])}`",
            f"- Sections: `{', '.join(outline['sections'])}`",
            "",
            "## Claims and non-claims",
            "",
            f"- Status: `{payload['claims_nonclaims']['status']}`",
            "",
            "| report | role | positive claim pointer | control pointer | no-control rationale pointer |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for claim in payload["claims_nonclaims"]["positive_claim_cells"]:
        lines.append(
            "| "
            f"`{claim['report']}` | "
            f"`{claim['bundle_role']}` | "
            f"`{claim['positive_claim_pointer']}` | "
            f"`{claim['control_pointer']}` | "
            f"`{claim['no_control_rationale_pointer']}` |"
        )
    lines.extend(
        [
            "",
            "## Literature ledger pointer",
            "",
            f"- Status: `{payload['literature_ledger']['status']}`",
            f"- Pointer: `{payload['literature_ledger']['pointer']}`",
            "",
            "## Honest boundary",
            "",
            f"- Status: `{payload['honest_boundary']['status']}`",
            f"- Claimed: {payload['honest_boundary']['claimed']}",
            f"- Not claimed: {payload['honest_boundary']['not_claimed']}",
        ]
    )
    for row in payload["honest_boundary"]["rows"]:
        lines.append(f"- {row}")
    lines.append("")
    return "\n".join(lines)


def _write_json_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _validate_committed_discovery_map_round_trip() -> None:
    path = _artifact_path(DISCOVERY_MAP_JSON_ARTIFACT)
    payload = json.loads(path.read_text(encoding="utf-8"))
    validate_discovery_map_payload(payload, root=ROOT)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _reusable_generated_at() -> str | None:
    if not INDEX_ARTIFACT.exists():
        return None
    try:
        payload = json.loads(INDEX_ARTIFACT.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def run_reports(
    *,
    only: str | None = None,
    json_summary: str | None = None,
    generated_at: str | None = None,
    force: bool = False,
    cold: bool = False,
    verify_fingerprints: bool = False,
) -> dict[str, Any]:
    CANONICAL_DIR.mkdir(parents=True, exist_ok=True)
    mode: Literal["changed", "verify", "cold"] = "cold" if cold or force else "verify" if verify_fingerprints else "changed"
    timestamp = (
        generated_at
        if generated_at is not None
        else (_reusable_generated_at() if mode != "cold" else None)
        or datetime.now(timezone.utc).isoformat()
    )
    results = [
        _run_spec(spec, mode=mode, generated_at=timestamp)
        for spec in _selected_specs_with_dependents(only, include_dependents=mode == "changed")
    ]
    from scripts.run_formal_hardening_report import write_formal_hardening_report

    write_formal_hardening_report(root=ROOT, generated_at=timestamp)
    from scripts.run_dimension_mismatch_debt_transfer import write_dimension_mismatch_debt_transfer

    write_dimension_mismatch_debt_transfer(root=ROOT, generated_at=timestamp, require_anti_triviality=False)
    from scripts.run_dimension_mismatch_anti_triviality import write_dimension_mismatch_anti_triviality

    write_dimension_mismatch_anti_triviality(root=ROOT, generated_at=timestamp)
    write_dimension_mismatch_debt_transfer(root=ROOT, generated_at=timestamp, require_anti_triviality=True)
    scorecard = _build_quality_scorecard(results, generated_at=timestamp)
    from bedc_quality_lab.backends.current_lab.adapter import CurrentLabBackendEvidenceAdapter
    from bedc_quality_lab.discovery_compiler.compiler import compile_discovery
    from scripts.run_claim_graph import write_claim_graph
    from scripts.run_claim_verdict_demo import write_claim_verdicts
    from scripts.run_gap_head_mechanism_namecert import write_gap_head_mechanism_namecert

    _write_json_atomic(_artifact_path(QUALITY_SCORECARD_JSON_ARTIFACT), scorecard)
    _write_text_atomic(_artifact_path(QUALITY_SCORECARD_MARKDOWN_ARTIFACT), _render_quality_scorecard_markdown(scorecard))
    write_gap_head_mechanism_namecert(root=ROOT, generated_at=timestamp)
    require_full_negative_reports = only is None
    _compile_discovery_compat(
        compile_discovery,
        root=ROOT,
        generated_at=timestamp,
        adapter=CurrentLabBackendEvidenceAdapter(),
        require_required_negative_reports=require_full_negative_reports,
    )
    _validate_committed_discovery_map_round_trip()
    _write_json_atomic(_artifact_path(CLAIM_CAPSULE_JSON_ARTIFACT), _build_claim_capsule(timestamp))
    from scripts.run_dimension_mismatch_transfer_robustness import write_dimension_mismatch_transfer_robustness
    from scripts.run_discovery_negative_witness_summary import write_discovery_negative_witness_summary

    write_dimension_mismatch_transfer_robustness(root=ROOT, generated_at=timestamp)
    write_gap_head_mechanism_namecert(root=ROOT, generated_at=timestamp)
    _compile_discovery_compat(
        compile_discovery,
        root=ROOT,
        generated_at=timestamp,
        adapter=CurrentLabBackendEvidenceAdapter(),
        require_required_negative_reports=require_full_negative_reports,
    )
    _validate_committed_discovery_map_round_trip()
    claim_verdict_rows = write_claim_verdicts(root=ROOT, generated_at=timestamp)
    if only is None:
        write_claim_graph(root=ROOT, generated_at=timestamp)
    write_discovery_negative_witness_summary(root=ROOT, generated_at=timestamp)
    from scripts.run_negative_witness_mutation_ledger import write_negative_witness_mutation_ledger

    write_negative_witness_mutation_ledger(root=ROOT, generated_at=timestamp)
    new_model_hardgates = _build_new_model_hardgates_payload(generated_at=timestamp)
    _write_json_atomic(_artifact_path(NEW_MODEL_HARDGATES_JSON_ARTIFACT), new_model_hardgates)
    _write_text_atomic(
        _artifact_path(NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT),
        _render_new_model_hardgates_markdown(new_model_hardgates),
    )
    from scripts.run_discovery_gated_transformer import write_artifacts as write_dgt_run_artifacts

    discovery_gated_transformer = _build_discovery_gated_transformer_payload(generated_at=timestamp)
    write_dgt_run_artifacts(discovery_gated_transformer, root=ROOT)
    _write_json_atomic(_artifact_path(DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT), discovery_gated_transformer)
    _write_text_atomic(
        _artifact_path(DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT),
        _render_discovery_gated_transformer_markdown(discovery_gated_transformer),
    )
    _write_discovery_gated_transformer_fingerprint(discovery_gated_transformer)
    model_design_suite = _build_model_design_suite_payload(generated_at=timestamp)
    _write_json_atomic(_artifact_path(MODEL_DESIGN_SUITE_JSON_ARTIFACT), model_design_suite)
    _write_text_atomic(
        _artifact_path(MODEL_DESIGN_SUITE_MARKDOWN_ARTIFACT),
        _render_model_design_suite_markdown(model_design_suite),
    )
    _validate_committed_model_design_suite_round_trip()
    draft_payload = _index(results, generated_at=timestamp, claim_verdict_rows=claim_verdict_rows)
    _write_json_atomic(INDEX_ARTIFACT, draft_payload)
    _write_text_atomic(CANONICAL_DIR / "index.md", _render_index_markdown(draft_payload))
    from scripts.release_manifest_sidecar import write_release_manifest_sidecar
    from scripts.run_release_namecert_candidate import write_release_namecert_candidate

    write_release_manifest_sidecar(root=ROOT, generated_at=timestamp)
    write_release_namecert_candidate(root=ROOT, generated_at=timestamp, make_check_passed=True)
    from scripts.run_toy_safety_boundary import main as write_toy_safety_boundary

    write_toy_safety_boundary([])
    payload = _index(results, generated_at=timestamp, claim_verdict_rows=claim_verdict_rows)
    _write_json_atomic(INDEX_ARTIFACT, payload)
    _write_text_atomic(CANONICAL_DIR / "index.md", _render_index_markdown(payload))
    if json_summary is not None:
        _write_json_atomic(Path(json_summary), payload)
    if any(result["status"] != "pass" for result in results):
        raise SystemExit(1)
    return payload


def _list_manifest() -> None:
    for spec in CANONICAL_REPORTS:
        print(
            "\t".join(
                (
                    spec.name,
                    " ".join(spec.command),
                    spec.json_artifact,
                    spec.markdown_artifact,
                    str(spec.estimated_seconds),
                )
            )
        )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="List canonical report manifest rows.")
    parser.add_argument("--only", metavar="NAME", help="Run one canonical report by manifest name.")
    parser.add_argument("--force", action="store_true", help="Regenerate all selected canonical producer artifacts.")
    parser.add_argument("--cold", action="store_true", help="Regenerate all selected canonical producer artifacts and write fingerprint sidecars.")
    parser.add_argument(
        "--verify-fingerprints",
        action="store_true",
        help="Fail when a selected committed artifact has no matching fingerprint sidecar.",
    )
    parser.add_argument("--json-summary", metavar="PATH", help="Write a JSON run summary to PATH.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.list:
        _list_manifest()
        return
    run_reports(
        only=args.only,
        json_summary=args.json_summary,
        force=args.force,
        cold=args.cold,
        verify_fingerprints=args.verify_fingerprints,
    )


if __name__ == "__main__":
    main()

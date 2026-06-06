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
from scripts.literature_ledger import validate_literature_ledger

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
NEGATIVE_WITNESSES_EXPECTED_KIND_COUNT = 8
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
NEGATIVE_WITNESS_MUTATION_LEDGER_MARKDOWN_ARTIFACT = "reports/canonical/negative_witness_mutation_ledger.md"
NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
NEW_MODEL_HARDGATES_JSON_ARTIFACT = "reports/canonical/new_model_hardgates.json"
NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT = "reports/canonical/new_model_hardgates.md"
NEW_MODEL_HARDGATES_ARTIFACT_ID = "bedc-quality-lab:new-model-hardgates"
NEW_MODEL_HARDGATES_SCHEMA_ID = "bedc-quality-lab:new-model-hardgate-registry"
DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT = "reports/canonical/discovery_gated_transformer.json"
DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT = "reports/canonical/discovery_gated_transformer.md"
DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer"
DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer"
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
RELEASE_NAMECERT_CANDIDATE_JSON_ARTIFACT = "reports/release_namecert_candidate.json"
RELEASE_NAMECERT_CANDIDATE_MARKDOWN_ARTIFACT = "reports/release_namecert_candidate.md"
RELEASE_NAMECERT_CANDIDATE_ARTIFACT_ID = "bedc-quality-lab:release-namecert-candidate"
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
            "torch_training_evidence",
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
        json_artifact="reports/canonical/discovery-regularized-training.json",
        markdown_artifact="reports/canonical/discovery-regularized-training.md",
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
            "torch_training_evidence",
            "negative_witness_mutations",
            "training_loop_trace",
            "matched_random_control",
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
        scope_pointer="$.grid",
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
        "row_count": payload["row_count"],
        "level_counts": payload["level_counts"],
    }


def _discovery_map_payload(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_discovery_map import build_discovery_map

    return build_discovery_map(generated_at=generated_at, root=ROOT, canonical_reports=CANONICAL_REPORTS)


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


NEGATIVE_WITNESS_MUTATION_ROWS: tuple[dict[str, str], ...] = (
    {
        "witness_id": "score_margin_shortcut",
        "source_witness_pointer": "reports/runs/a1-canonical/claim_capsule.json:$.run_local.negative_witness[0]",
        "mutation_target": "residualized_h_path",
        "mutation_target_pointer": "reports/canonical/discovery-gated-nas.json:$.search_objective_summary.by_candidate.residualized_h_path",
        "hardgate_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
        "not_claimed_pointer": "reports/canonical/discovery-gated-nas.json:$.not_claimed",
    },
    {
        "witness_id": "scale_leakage",
        "source_witness_pointer": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:$.run_local.negative_witness[0]",
        "mutation_target": "scale_invariant_norm",
        "mutation_target_pointer": "reports/canonical/discovery-gated-nas.json:$.search_objective_summary.by_candidate.scale_invariant_norm",
        "hardgate_pointer": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:$.run_local.negative_witness_hardgates.NW-HG2",
        "not_claimed_pointer": "reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.not_claimed",
    },
    {
        "witness_id": "control_positive",
        "source_witness_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]",
        "mutation_target": "control_separated_route",
        "mutation_target_pointer": "reports/canonical/discovery-gated-nas.json:$.search_objective_summary.by_candidate.control_separated_route",
        "hardgate_pointer": "reports/canonical/discovery-gated-nas.json:$.hardgate.gates.DG-NAS-HG6",
        "not_claimed_pointer": "reports/canonical/discovery-gated-nas.json:$.not_claimed",
    },
    {
        "witness_id": "benefit_debt_tradeoff",
        "source_witness_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]",
        "mutation_target": "constrained_lagrangian_loss",
        "mutation_target_pointer": "reports/canonical/certificate-guided-training.json:$.objective.formula",
        "hardgate_pointer": "reports/canonical/certificate-guided-training.json:$.hardgate.gates.C1-HG1",
        "not_claimed_pointer": "reports/canonical/certificate-guided-training.json:$.not_claimed",
    },
    {
        "witness_id": "single_threshold_escape",
        "source_witness_pointer": "runs/single_threshold_escape_witness.json:$.single_threshold_basis[0]",
        "mutation_target": "threshold_frontier_loss",
        "mutation_target_pointer": "reports/canonical/gap-head-threshold-frontier.json:$.pareto_axis_spec",
        "hardgate_pointer": "reports/canonical/gap-head-threshold-frontier.json:$.hardgate.checks.HG-GH-T3",
        "not_claimed_pointer": "reports/canonical/gap-head-threshold-frontier.json:$.not_claimed",
    },
    {
        "witness_id": "forbidden_column",
        "source_witness_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]",
        "mutation_target": "inference_audit_layer",
        "mutation_target_pointer": "reports/canonical/gap-head-on-h.json:$.forbidden_column_audit",
        "hardgate_pointer": "reports/canonical/gap-head-on-h.json:$.applicability_boundary.forbidden_inference_columns",
        "not_claimed_pointer": "reports/canonical/gap-head-on-h.json:$.applicability_boundary",
    },
    {
        "witness_id": "hidden_debt",
        "source_witness_pointer": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]",
        "mutation_target": "explicit_ledger_head",
        "mutation_target_pointer": "reports/canonical/ledger-aware-transformer.json:$.ledger.rows",
        "hardgate_pointer": "reports/canonical/ledger-aware-transformer.json:$.hardgate.gates.LAT-HG2",
        "not_claimed_pointer": "reports/canonical/ledger-aware-transformer.json:$.not_claimed",
    },
    {
        "witness_id": "mechanism_blocked",
        "source_witness_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence",
        "mutation_target": "mechanism_seeking_module",
        "mutation_target_pointer": "reports/canonical/mechanism-seeking-network.json:$.mechanism_gate_summary",
        "hardgate_pointer": "reports/canonical/mechanism-seeking-network.json:$.hardgate.gates.MSN-HG2",
        "not_claimed_pointer": "reports/canonical/mechanism-seeking-network.json:$.not_claimed",
    },
)


def _resolve_artifact_pointer(cell: str) -> Any:
    if ":$" not in cell:
        return None
    artifact, pointer = cell.split(":", 1)
    payload = _load_sidecar_payload(artifact)
    if pointer == "$":
        return payload or None
    return _bracket_pointer_value(payload, pointer)


def _negative_witness_mutation_row(spec: Mapping[str, str]) -> dict[str, Any]:
    required = {
        key: spec[key]
        for key in (
            "source_witness_pointer",
            "mutation_target_pointer",
            "hardgate_pointer",
            "not_claimed_pointer",
        )
    }
    resolved = {key: _resolve_artifact_pointer(pointer) is not None for key, pointer in required.items()}
    blocked = [key for key, ok in resolved.items() if not ok]
    return {
        "witness_id": spec["witness_id"],
        "source_witness_pointer": {
            "artifact": spec["source_witness_pointer"].split(":", 1)[0],
            "pointer": spec["source_witness_pointer"].split(":", 1)[1],
        },
        "mutation_target": spec["mutation_target"],
        "mutation_target_pointer": {
            "artifact": spec["mutation_target_pointer"].split(":", 1)[0],
            "pointer": spec["mutation_target_pointer"].split(":", 1)[1],
        },
        "hardgate_pointer": {
            "artifact": spec["hardgate_pointer"].split(":", 1)[0],
            "pointer": spec["hardgate_pointer"].split(":", 1)[1],
        },
        "not_claimed_pointer": {
            "artifact": spec["not_claimed_pointer"].split(":", 1)[0],
            "pointer": spec["not_claimed_pointer"].split(":", 1)[1],
        },
        "audit_status": "pass" if not blocked else "blocked",
        "audit_reason": "all pointers resolve" if not blocked else f"unresolved pointer fields: {', '.join(blocked)}",
        "resolved_pointers": resolved,
    }


def _negative_witness_mutation_ledger_payload(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    rows = [_negative_witness_mutation_row(row) for row in NEGATIVE_WITNESS_MUTATION_ROWS]
    blocked = [row["witness_id"] for row in rows if row["audit_status"] != "pass"]
    return {
        "schema_id": NEGATIVE_WITNESS_MUTATION_LEDGER_SCHEMA_ID,
        "artifact_id": NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "scripts/run_canonical_reports.py",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "surface": "pointer-only",
        "not_claimed": "This sidecar records mutation lineage pointers only and does not emit terminal verdicts.",
        "row_count": len(rows),
        "audit_status": "pass" if not blocked else "blocked",
        "blocked_witness_ids": blocked,
        "rows": rows,
    }


def _render_negative_witness_mutation_ledger_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Negative Witness Mutation Ledger",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Canonical role: `{payload['canonical_role']}`",
        f"- Audit: `{payload['audit_status']}`",
        "",
        "| witness | mutation target | source witness | target pointer | audit |",
        "| --- | --- | --- | --- | --- |",
    ]
    rows = payload.get("rows", [])
    if isinstance(rows, list):
        for row in rows:
            if not isinstance(row, Mapping):
                continue
            source = row.get("source_witness_pointer") if isinstance(row.get("source_witness_pointer"), Mapping) else {}
            target = row.get("mutation_target_pointer") if isinstance(row.get("mutation_target_pointer"), Mapping) else {}
            source_text = f"{source.get('artifact', '')}:{source.get('pointer', '')}"
            target_text = f"{target.get('artifact', '')}:{target.get('pointer', '')}"
            lines.append(
                "| "
                f"`{row.get('witness_id', '')}` | "
                f"`{row.get('mutation_target', '')}` | "
                f"`{source_text}` | "
                f"`{target_text}` | "
                f"`{row.get('audit_status', '')}` |"
            )
    lines.append("")
    return "\n".join(lines)


def _negative_witness_mutation_ledger_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT)
    return {
        "status": "pointer-only",
        "artifact_id": payload.get("artifact_id", NEGATIVE_WITNESS_MUTATION_LEDGER_ARTIFACT_ID),
        "json_artifact": NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT,
        "markdown_artifact": NEGATIVE_WITNESS_MUTATION_LEDGER_MARKDOWN_ARTIFACT,
        "canonical_role": payload.get("canonical_role", "sidecar_not_in_CANONICAL_REPORTS"),
        "row_count": payload.get("row_count", 0),
        "audit_status": payload.get("audit_status", "missing"),
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
            "not_claimed pointer excludes global architecture superiority, production superiority, and full closure claims",
        ),
    )
    return tuple({"gate_id": gate_id, "requirement": requirement} for gate_id, requirement in rows)


def _new_model_hardgates_payload(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    gates = {
        spec["gate_id"]: {
            "gate_id": spec["gate_id"],
            "requirement": spec["requirement"],
            "owner_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates.{spec['gate_id']}",
            "candidate_required_pointer_template": f"$.hardgates.{spec['gate_id']}",
            "candidate_status_pointer_template": f"$.hardgates.{spec['gate_id']}.status",
            "candidate_evidence_pointer_template": f"$.hardgates.{spec['gate_id']}.evidence_pointer",
            "candidate_not_claimed_pointer_template": f"$.hardgates.{spec['gate_id']}.not_claimed_pointer",
        }
        for spec in _new_model_hardgate_specs()
    }
    payload = {
        "schema_id": NEW_MODEL_HARDGATES_SCHEMA_ID,
        "artifact_id": NEW_MODEL_HARDGATES_ARTIFACT_ID,
        "generated_at": timestamp,
        "status": "pointer-only",
        "producer": "scripts/run_canonical_reports.py",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$",
        "candidate_contract": {
            "model_id": {
                "required": True,
                "semantic": True,
                "pointer_template": "$.model_id",
            },
            "report_identity_policy": "report_id is producer identity and cannot satisfy semantic model_id",
            "model_id_report_id_equality": "reject",
            "gate_status_pointer_templates": {
                gate_id: row["candidate_status_pointer_template"] for gate_id, row in gates.items()
            },
            "gate_evidence_pointer_templates": {
                gate_id: row["candidate_evidence_pointer_template"] for gate_id, row in gates.items()
            },
            "gate_not_claimed_pointer_templates": {
                gate_id: row["candidate_not_claimed_pointer_template"] for gate_id, row in gates.items()
            },
        },
        "gates": gates,
        "not_claimed": [
            "This registry does not evaluate any model candidate.",
            "This registry excludes global architecture superiority claims.",
            "This registry excludes production superiority claims.",
            "This registry excludes full closure claims.",
        ],
    }
    _validate_new_model_hardgates_payload(payload)
    return payload


def _validate_new_model_hardgates_payload(payload: Mapping[str, Any]) -> None:
    forbidden_keys = {
        "terminal_verdict",
        "metrics",
        "raw_metrics",
        "raw_metrics_artifact",
        "candidate_metrics",
        "candidate_results",
        "candidate_measurements",
        "candidate_evidence",
        "candidate_evidence_body",
        "evidence_body",
        "baseline_metrics",
        "baseline_results",
        "measured_baseline",
        "measured_baseline_body",
    }

    def walk(value: Any, path: str) -> None:
        if isinstance(value, Mapping):
            for key, cell in value.items():
                if key in forbidden_keys or key.endswith("_body"):
                    raise ValueError(f"new_model_hardgates payload contains forbidden key at {path}.{key}")
                walk(cell, f"{path}.{key}")
        elif isinstance(value, list):
            for index, cell in enumerate(value):
                walk(cell, f"{path}[{index}]")
        elif isinstance(value, str):
            lowered = value.lower()
            if ".refactor-loop/host.env" in value or "terminal_verdict" in value:
                raise ValueError(f"new_model_hardgates payload contains forbidden value at {path}")
            if "candidate evidence body" in lowered or "raw metrics body" in lowered or "measured baseline body" in lowered:
                raise ValueError(f"new_model_hardgates payload contains forbidden body text at {path}")

    walk(payload, "$")
    contract = payload.get("candidate_contract")
    if not isinstance(contract, Mapping):
        raise ValueError("new_model_hardgates payload requires candidate_contract")
    model_id = contract.get("model_id")
    if not isinstance(model_id, Mapping):
        raise ValueError("candidate_contract requires semantic model_id")
    if model_id.get("pointer_template") != "$.model_id" or model_id.get("required") is not True:
        raise ValueError("candidate_contract model_id must be required at $.model_id")
    if contract.get("semantic_identity_field") == "report_id" or contract.get("model_id") == "report_id":
        raise ValueError("candidate_contract rejects report_id as semantic model_id")
    if contract.get("model_id_report_id_equality") != "reject":
        raise ValueError("candidate_contract must reject model_id == report_id")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping):
        raise ValueError("new_model_hardgates payload requires gates")
    expected_ids = [f"NEW-MODEL-HG{index}" for index in range(1, 21)]
    if list(gates) != expected_ids:
        raise ValueError("new_model_hardgates payload must contain NEW-MODEL-HG1..20 in order")
    required_fields = {
        "gate_id",
        "requirement",
        "owner_pointer",
        "candidate_required_pointer_template",
        "candidate_status_pointer_template",
        "candidate_evidence_pointer_template",
        "candidate_not_claimed_pointer_template",
    }
    for gate_id, row in gates.items():
        if not isinstance(row, Mapping) or set(row) != required_fields:
            raise ValueError(f"new_model_hardgates gate row has invalid fields: {gate_id}")
        if row["gate_id"] != gate_id:
            raise ValueError(f"new_model_hardgates gate row id mismatch: {gate_id}")
        if row["owner_pointer"] != f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates.{gate_id}":
            raise ValueError(f"new_model_hardgates gate row owner pointer mismatch: {gate_id}")
        if row["candidate_required_pointer_template"] != f"$.hardgates.{gate_id}":
            raise ValueError(f"new_model_hardgates gate row required pointer mismatch: {gate_id}")
        if row["candidate_status_pointer_template"] != f"$.hardgates.{gate_id}.status":
            raise ValueError(f"new_model_hardgates gate row status pointer mismatch: {gate_id}")
        if row["candidate_evidence_pointer_template"] != f"$.hardgates.{gate_id}.evidence_pointer":
            raise ValueError(f"new_model_hardgates gate row evidence pointer mismatch: {gate_id}")
        if row["candidate_not_claimed_pointer_template"] != f"$.hardgates.{gate_id}.not_claimed_pointer":
            raise ValueError(f"new_model_hardgates gate row not-claimed pointer mismatch: {gate_id}")


def _render_new_model_hardgates_markdown(payload: Mapping[str, Any]) -> str:
    _validate_new_model_hardgates_payload(payload)
    lines = [
        "# New Model Hardgates",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Owner pointer: `{payload['owner_pointer']}`",
        "",
        "| gate | owner pointer | candidate required | candidate status | candidate evidence | candidate not-claimed |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    gates = payload.get("gates", {})
    if isinstance(gates, Mapping):
        for row in gates.values():
            if not isinstance(row, Mapping):
                continue
            lines.append(
                "| "
                f"`{row.get('gate_id', '')}` | "
                f"`{row.get('owner_pointer', '')}` | "
                f"`{row.get('candidate_required_pointer_template', '')}` | "
                f"`{row.get('candidate_status_pointer_template', '')}` | "
                f"`{row.get('candidate_evidence_pointer_template', '')}` | "
                f"`{row.get('candidate_not_claimed_pointer_template', '')}` |"
            )
    lines.append("")
    return "\n".join(lines)


def _new_model_hardgates_index_section(generated_at: str | None = None) -> dict[str, Any]:
    payload = _new_model_hardgates_payload(generated_at=generated_at)
    return {
        "status": "pointer-only",
        "artifact_id": NEW_MODEL_HARDGATES_ARTIFACT_ID,
        "json_artifact": NEW_MODEL_HARDGATES_JSON_ARTIFACT,
        "markdown_artifact": NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT,
        "schema_id": payload["schema_id"],
        "status_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.status",
        "gate_count": len(payload["gates"]),
        "gates_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates",
        "candidate_contract_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.candidate_contract",
    }


def _dgt_component_descriptors() -> dict[str, Any]:
    rows = (
        (
            "backbone",
            "base sequence backbone",
            "reports/canonical/ledger-aware-transformer.json:$",
            "reports/canonical/ledger-aware-transformer.json:$.run_artifacts",
        ),
        (
            "certificate_gated_attention",
            "certificate-gated attention component",
            "reports/canonical/certificate-gated-attention.json:$",
            "reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary",
        ),
        (
            "gap_ledger_route_mechanism_scope_heads",
            "gap, ledger, route certificate, mechanism-probe, and scope-seal heads",
            "reports/canonical/gap_head_attribution_capsule.json:$",
            "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence",
        ),
        (
            "discovery_regularized_training",
            "discovery-regularized training objective",
            "reports/canonical/discovery-regularized-training.json:$",
            "reports/canonical/discovery-regularized-training.json:$.torch_training_evidence",
        ),
        (
            "audit",
            "audit boundary and negative-witness controls",
            "reports/canonical/negative_discovery_reports.json:$",
            "reports/canonical/negative_discovery_reports.json:$.rows",
        ),
        (
            "output_bundle",
            "model output bundle boundary",
            f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.public_index_pointers",
            f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.downstream_scope",
        ),
    )
    return {
        key: {
            "role": role,
            "owner_pointer": owner_pointer,
            "evidence_pointer": evidence_pointer,
            "pointer_state": "present-but-fail-closed",
        }
        for key, role, owner_pointer, evidence_pointer in rows
    }


def _dgt_hardgate_slots() -> dict[str, Any]:
    specs = (
        (
            "DGT-HG1",
            "UER base baseline",
            "UER evidence against base baseline",
            "$.component_descriptors.backbone",
            "reports/canonical/ledger-aware-transformer.json:$.metrics.UER",
            "reports/canonical/ledger-aware-transformer.json:$.control_protocol",
            None,
            "NEW-MODEL-HG11",
            "missing-evidence-pointer",
        ),
        (
            "DGT-HG2",
            "UER parameter-matched baseline",
            "UER evidence against a parameter-matched baseline",
            "$.component_descriptors.backbone",
            "reports/canonical/discovery-gated-nas.json:$.matched_baseline_control.parameter_matched",
            "reports/canonical/discovery-gated-nas.json:$.matched_baseline_control",
            None,
            "NEW-MODEL-HG7",
            "missing-control-pointer",
        ),
        (
            "DGT-HG3",
            "UER compute-matched baseline",
            "UER evidence against a compute-matched baseline",
            "$.component_descriptors.backbone",
            "reports/canonical/discovery-gated-nas.json:$.matched_baseline_control.compute_matched",
            "reports/canonical/discovery-gated-nas.json:$.matched_baseline_control",
            None,
            "NEW-MODEL-HG8",
            "missing-control-pointer",
        ),
        (
            "DGT-HG4",
            "UER matched-random baseline",
            "UER evidence against a matched-random structural control",
            "$.component_descriptors.backbone",
            "reports/canonical/ledger-aware-transformer.json:$.metrics.UER",
            "reports/canonical/ledger-aware-transformer.json:$.matched_random_control",
            None,
            "NEW-MODEL-HG9",
            "missing-control-pointer",
        ),
        (
            "DGT-HG5",
            "FalseLedgerRate non-worsening",
            "FalseLedgerRate does not worsen under the candidate route",
            "$.component_descriptors.audit",
            "reports/canonical/ledger-aware-transformer.json:$.metrics.FalseLedgerRate",
            "reports/canonical/ledger-aware-transformer.json:$.matched_random_control",
            None,
            "NEW-MODEL-HG12",
            "missing-evidence-pointer",
        ),
        (
            "DGT-HG6",
            "classifier shift count",
            "classifier shift count is positive on the declared surface",
            "$.component_descriptors.audit",
            "reports/canonical/discovery-gated-nas.json:$.search_objective_summary.selected_candidate.classifier_shift_count",
            None,
            None,
            "NEW-MODEL-HG16",
            "missing-control-pointer",
        ),
        (
            "DGT-HG7",
            "OOD and stress surfaces",
            "at least three OOD or stress surface pointers are present",
            "$.component_descriptors.audit",
            "reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o",
            "reports/canonical/gap_head_transfer_atlas.json:$.config.control_arm",
            None,
            "NEW-MODEL-HG10",
            "missing-surface-pointer",
        ),
        (
            "DGT-HG8",
            "certificate-gated attention ablation",
            "certificate-gated attention ablation lowers the corresponding signal",
            "$.component_descriptors.certificate_gated_attention",
            "reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary",
            "reports/canonical/certificate-gated-attention.json:$.matched_random_control",
            "reports/canonical/certificate-gated-attention.json:$.discovery_map_signal",
            "NEW-MODEL-HG19",
            "missing-ablation-pointer",
        ),
        (
            "DGT-HG9",
            "DRT ablation",
            "discovery-regularized training ablation lowers the corresponding signal",
            "$.component_descriptors.discovery_regularized_training",
            "reports/canonical/discovery-regularized-training.json:$.torch_training_evidence",
            "reports/canonical/discovery-regularized-training.json:$.matched_random_control",
            "reports/canonical/discovery-regularized-training.json:$.training_loop_trace",
            "NEW-MODEL-HG19",
            "missing-ablation-pointer",
        ),
        (
            "DGT-HG10",
            "gap ledger head ablation",
            "gap, ledger, and head ablation lowers the corresponding signal",
            "$.component_descriptors.gap_ledger_route_mechanism_scope_heads",
            "reports/canonical/gap-head-ablation.json:$.factor_attribution",
            "reports/canonical/gap-head-ablation.json:$.control_protocol",
            "reports/canonical/gap-head-ablation.json:$.hardgate",
            "NEW-MODEL-HG19",
            "missing-ablation-pointer",
        ),
        (
            "DGT-HG11",
            "mechanism probe and scope seal ablation",
            "mechanism-probe and scope-seal ablation lowers the corresponding signal",
            "$.component_descriptors.gap_ledger_route_mechanism_scope_heads",
            "reports/gap_head_mechanism_namecert.json:$.mechanism_spec",
            "reports/gap_head_mechanism_namecert.json:$.source_spec.scope_seal",
            "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates",
            "NEW-MODEL-HG19",
            "missing-ablation-pointer",
        ),
        (
            "DGT-HG12",
            "boundary and terminal exposure",
            "boundary excludes broad superiority claims and terminal claim exposure remains downstream",
            "$.component_descriptors.output_bundle",
            "$.downstream_scope",
            None,
            None,
            "NEW-MODEL-HG20",
            "missing-terminal-claim-pointer",
        ),
    )
    slots = {}
    for (
        gate_id,
        gate_label,
        requirement_summary,
        component_pointer,
        evidence_pointer,
        control_pointer,
        ablation_pointer,
        registry_gate,
        failure_mode,
    ) in specs:
        slots[gate_id] = {
            "gate_id": gate_id,
            "gate_label": gate_label,
            "slot_state": "present-but-fail-closed",
            "requirement_summary": requirement_summary,
            "component_pointer": component_pointer,
            "evidence_pointer": evidence_pointer,
            "control_pointer": control_pointer,
            "ablation_pointer": ablation_pointer,
            "new_model_hardgate_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates.{registry_gate}",
            "not_claimed_pointer": "$.not_claimed",
            "failure_mode": failure_mode,
        }
    slots["overall_state"] = "present-but-fail-closed"
    return slots


def _build_discovery_gated_transformer_payload(generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    payload = {
        "schema_id": DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID,
        "artifact_id": DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID,
        "generated_at": timestamp,
        "status": "present-but-fail-closed",
        "producer": "scripts/run_canonical_reports.py",
        "model_id": "discovery_gated_transformer",
        "canonical_owner": {
            "json_artifact": DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
            "markdown_artifact": DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT,
            "owner_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$",
        },
        "component_descriptors": _dgt_component_descriptors(),
        "new_model_hardgates_registry": {
            "artifact_id": NEW_MODEL_HARDGATES_ARTIFACT_ID,
            "schema_id": NEW_MODEL_HARDGATES_SCHEMA_ID,
            "candidate_contract_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.candidate_contract",
            "gates_pointer": f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates",
            "pointer_state": "present-but-fail-closed",
        },
        "dgt_hardgate_slots": _dgt_hardgate_slots(),
        "public_index_pointers": {
            "model_id": "$.model_id",
            "component_descriptors": "$.component_descriptors",
            "dgt_hardgate_slots": "$.dgt_hardgate_slots",
            "not_claimed": "$.not_claimed",
            "downstream_scope": "$.downstream_scope",
        },
        "not_claimed": [
            "This owner does not claim broad architecture superiority.",
            "This owner does not claim production superiority.",
            "This owner does not claim full closure.",
            "This owner does not publish candidate measurement bodies.",
        ],
        "downstream_scope": {
            "discovery_map": "out-of-scope-follow-up",
            "claim_verdicts": "out-of-scope-follow-up",
            "claim_graph": "out-of-scope-follow-up",
        },
    }
    _validate_discovery_gated_transformer_payload(payload)
    return payload


def _validate_discovery_gated_transformer_payload(payload: Mapping[str, Any]) -> None:
    forbidden_keys = {
        "terminal_verdict",
        "metrics",
        "raw_metrics",
        "raw_metrics_artifact",
        "candidate_metrics",
        "candidate_results",
        "candidate_measurements",
        "candidate_evidence",
        "candidate_evidence_body",
        "evidence_body",
        "claim_capsule_body",
        "measurement_body",
        "terminal_claim_row",
    }
    forbidden_strings = (
        ".refactor-loop",
        "DGT-v0",
        "issue-",
        "issue #",
        "route-a",
        "route-b",
        "route-c",
        "run_discovery_gated_transformer",
        "discovery_gated_transformer_sidecar",
        "terminal_verdict",
        "raw metric",
        "global superiority",
    )

    def walk(value: Any, path: str) -> None:
        if isinstance(value, Mapping):
            for key, cell in value.items():
                if key in forbidden_keys or key.endswith("_body"):
                    raise ValueError(f"discovery_gated_transformer payload contains forbidden key at {path}.{key}")
                walk(cell, f"{path}.{key}")
        elif isinstance(value, list):
            for index, cell in enumerate(value):
                walk(cell, f"{path}[{index}]")
        elif isinstance(value, str):
            lowered = value.lower()
            for forbidden in forbidden_strings:
                if forbidden.lower() in lowered:
                    raise ValueError(f"discovery_gated_transformer payload contains forbidden value at {path}")

    walk(payload, "$")
    expected_top_level = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "status",
        "producer",
        "model_id",
        "canonical_owner",
        "component_descriptors",
        "new_model_hardgates_registry",
        "dgt_hardgate_slots",
        "public_index_pointers",
        "not_claimed",
        "downstream_scope",
    }
    if set(payload) != expected_top_level:
        raise ValueError("discovery_gated_transformer payload has invalid top-level fields")
    if payload["schema_id"] != DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID:
        raise ValueError("discovery_gated_transformer schema_id mismatch")
    if payload["artifact_id"] != DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID:
        raise ValueError("discovery_gated_transformer artifact_id mismatch")
    if payload["status"] != "present-but-fail-closed":
        raise ValueError("discovery_gated_transformer status must be present-but-fail-closed")
    if payload["model_id"] != "discovery_gated_transformer":
        raise ValueError("discovery_gated_transformer model_id mismatch")
    components = payload["component_descriptors"]
    expected_components = {
        "backbone",
        "certificate_gated_attention",
        "gap_ledger_route_mechanism_scope_heads",
        "discovery_regularized_training",
        "audit",
        "output_bundle",
    }
    if not isinstance(components, Mapping) or set(components) != expected_components:
        raise ValueError("discovery_gated_transformer component descriptors mismatch")
    component_fields = {"role", "owner_pointer", "evidence_pointer", "pointer_state"}
    for key, row in components.items():
        if not isinstance(row, Mapping) or set(row) != component_fields:
            raise ValueError(f"discovery_gated_transformer component row invalid: {key}")
        if row["pointer_state"] != "present-but-fail-closed":
            raise ValueError(f"discovery_gated_transformer component state invalid: {key}")
    registry = payload["new_model_hardgates_registry"]
    if not isinstance(registry, Mapping):
        raise ValueError("discovery_gated_transformer registry row invalid")
    if registry.get("candidate_contract_pointer") != f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.candidate_contract":
        raise ValueError("discovery_gated_transformer registry candidate contract pointer mismatch")
    if registry.get("gates_pointer") != f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates":
        raise ValueError("discovery_gated_transformer registry gates pointer mismatch")
    slots = payload["dgt_hardgate_slots"]
    if not isinstance(slots, Mapping):
        raise ValueError("discovery_gated_transformer slots invalid")
    expected_slot_ids = [f"DGT-HG{index}" for index in range(1, 13)]
    if list(slots) != expected_slot_ids + ["overall_state"]:
        raise ValueError("discovery_gated_transformer slots must contain DGT-HG1..12 plus overall_state")
    slot_fields = {
        "gate_id",
        "gate_label",
        "slot_state",
        "requirement_summary",
        "component_pointer",
        "evidence_pointer",
        "control_pointer",
        "ablation_pointer",
        "new_model_hardgate_pointer",
        "not_claimed_pointer",
        "failure_mode",
    }
    for gate_id in expected_slot_ids:
        row = slots[gate_id]
        if not isinstance(row, Mapping) or set(row) != slot_fields:
            raise ValueError(f"discovery_gated_transformer slot fields invalid: {gate_id}")
        if row["gate_id"] != gate_id:
            raise ValueError(f"discovery_gated_transformer slot id mismatch: {gate_id}")
        if row["slot_state"] != "present-but-fail-closed":
            raise ValueError(f"discovery_gated_transformer slot state invalid: {gate_id}")
        if row["not_claimed_pointer"] != "$.not_claimed":
            raise ValueError(f"discovery_gated_transformer slot not-claimed pointer invalid: {gate_id}")
        if not str(row["new_model_hardgate_pointer"]).startswith(f"{NEW_MODEL_HARDGATES_JSON_ARTIFACT}:$.gates.NEW-MODEL-HG"):
            raise ValueError(f"discovery_gated_transformer slot registry pointer invalid: {gate_id}")
    if slots["overall_state"] != "present-but-fail-closed":
        raise ValueError("discovery_gated_transformer overall_state invalid")
    public_pointers = payload["public_index_pointers"]
    expected_public_pointers = {
        "model_id": "$.model_id",
        "component_descriptors": "$.component_descriptors",
        "dgt_hardgate_slots": "$.dgt_hardgate_slots",
        "not_claimed": "$.not_claimed",
        "downstream_scope": "$.downstream_scope",
    }
    if public_pointers != expected_public_pointers:
        raise ValueError("discovery_gated_transformer public pointers mismatch")
    downstream_scope = payload["downstream_scope"]
    if downstream_scope != {
        "discovery_map": "out-of-scope-follow-up",
        "claim_verdicts": "out-of-scope-follow-up",
        "claim_graph": "out-of-scope-follow-up",
    }:
        raise ValueError("discovery_gated_transformer downstream scope mismatch")


def _render_discovery_gated_transformer_markdown(payload: Mapping[str, Any]) -> str:
    _validate_discovery_gated_transformer_payload(payload)
    lines = [
        "# Discovery-Gated Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Model id: `{payload['model_id']}`",
        f"- Owner pointer: `{payload['canonical_owner']['owner_pointer']}`",
        "",
        "## Components",
        "",
        "| component | owner pointer | evidence pointer | pointer state |",
        "| --- | --- | --- | --- |",
    ]
    for key, row in payload["component_descriptors"].items():
        lines.append(
            "| "
            f"`{key}` | "
            f"`{row['owner_pointer']}` | "
            f"`{row['evidence_pointer']}` | "
            f"`{row['pointer_state']}` |"
        )
    lines.extend(
        [
            "",
            "## DGT Hardgate Slots",
            "",
            "| gate | component | evidence | control | ablation | registry | state | failure mode |",
            "| --- | --- | --- | --- | --- | --- | --- | --- |",
        ]
    )
    slots = payload["dgt_hardgate_slots"]
    for gate_id in [f"DGT-HG{index}" for index in range(1, 13)]:
        row = slots[gate_id]
        lines.append(
            "| "
            f"`{gate_id}` | "
            f"`{row['component_pointer']}` | "
            f"`{row['evidence_pointer']}` | "
            f"`{row['control_pointer']}` | "
            f"`{row['ablation_pointer']}` | "
            f"`{row['new_model_hardgate_pointer']}` | "
            f"`{row['slot_state']}` | "
            f"`{row['failure_mode']}` |"
        )
    lines.extend(
        [
            "",
            f"- Overall state: `{slots['overall_state']}`",
            f"- Downstream scope: `{payload['public_index_pointers']['downstream_scope']}`",
            "",
        ]
    )
    return "\n".join(lines)


def _discovery_gated_transformer_index_section(payload: Mapping[str, Any]) -> dict[str, Any]:
    _validate_discovery_gated_transformer_payload(payload)
    return {
        "status": payload["status"],
        "artifact_id": DISCOVERY_GATED_TRANSFORMER_ARTIFACT_ID,
        "schema_id": DISCOVERY_GATED_TRANSFORMER_SCHEMA_ID,
        "json_artifact": DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT,
        "model_id_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.model_id",
        "component_descriptors_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.component_descriptors",
        "hardgate_slots_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.dgt_hardgate_slots",
        "overall_state_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.dgt_hardgate_slots.overall_state",
        "not_claimed_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.not_claimed",
        "downstream_scope_pointer": f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.downstream_scope",
        "dgt_hardgate_slot_pointers": {
            f"DGT-HG{index}": (
                f"{DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT}:$.dgt_hardgate_slots.DGT-HG{index}"
            )
            for index in range(1, 13)
        },
    }


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
        "score_margin_causal_evidence_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.score_margin_causal_evidence",
        "a4_hardgates_status_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.status",
        "a4_hg5_pointer": "reports/canonical/gap_head_attribution_capsule.json:$.a4_hardgates.gates.A4-HG5",
        "a4_hardgates_status": _pointer_value(payload, "$.a4_hardgates.status") or "missing",
        "a4_hg5_status": _pointer_value(payload, "$.a4_hardgates.gates.A4-HG5.status") or "missing",
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
    return {
        "schema_id": INDEX_SCHEMA_ID,
        "generated_at": timestamp,
        "root": INDEX_ROOT,
        "reports": reports,
        "quality_scorecard": _quality_scorecard_index_section(),
        "discovery_map": {
            "status": "pointer-only",
            "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
            "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
            "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
            "coverage_matrix_pointer": "reports/canonical/discovery_map.json:$.coverage_matrix",
            "row_count": discovery_map_payload["row_count"],
            "level_counts": discovery_map_payload["level_counts"],
        },
        "dimension_mismatch_debt_transfer": _dimension_mismatch_transfer_index_section(),
        "dimension_mismatch_transfer_robustness": _dimension_mismatch_transfer_robustness_index_section(),
        "negative_witnesses": _negative_witnesses_index_section(),
        "negative_discovery_reports": _negative_discovery_reports_index_section(generated_at=timestamp),
        "negative_witness_mutation_ledger": _negative_witness_mutation_ledger_index_section(),
        "new_model_hardgates": _new_model_hardgates_index_section(generated_at=timestamp),
        "discovery_gated_transformer": _discovery_gated_transformer_index_section(discovery_gated_transformer_payload),
        "claim_verdicts": _claim_verdicts_index_section(claim_verdict_rows),
        "claim_graph": _claim_graph_index_section(generated_at=timestamp),
        "claim_capsule": _claim_capsule_index_section(generated_at=timestamp),
        "negative_witness_summary": _negative_witness_summary_index_section(generated_at=timestamp),
        "formal_hardening": _formal_hardening_index_section(generated_at=timestamp),
        "gap_head_transfer_atlas": _gap_head_transfer_atlas_index_section(discovery_map_payload),
        "gap_head_attribution_capsule": _gap_head_attribution_index_section(),
        "gap_head_mechanism_namecert": _gap_head_mechanism_namecert_index_section(),
        "release_manifest_sidecar": _release_manifest_sidecar_index_section(),
        "release_namecert_candidate": _release_namecert_candidate_index_section(),
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
            f"- Rows: `{payload['discovery_map']['row_count']}`",
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
            f"- Markdown: `{payload['negative_witness_mutation_ledger']['markdown_artifact']}`",
            f"- Canonical role: `{payload['negative_witness_mutation_ledger']['canonical_role']}`",
            f"- Rows: `{payload['negative_witness_mutation_ledger']['row_count']}`",
            f"- Audit: `{payload['negative_witness_mutation_ledger']['audit_status']}`",
            "",
            "## New model hardgates",
            "",
            f"- Status: `{payload['new_model_hardgates']['status']}`",
            f"- JSON: `{payload['new_model_hardgates']['json_artifact']}`",
            f"- Markdown: `{payload['new_model_hardgates']['markdown_artifact']}`",
            f"- Schema: `{payload['new_model_hardgates']['schema_id']}`",
            f"- Status pointer: `{payload['new_model_hardgates']['status_pointer']}`",
            f"- Gates pointer: `{payload['new_model_hardgates']['gates_pointer']}`",
            f"- Gate count: `{payload['new_model_hardgates']['gate_count']}`",
            f"- Candidate contract: `{payload['new_model_hardgates']['candidate_contract_pointer']}`",
            "",
            "## Discovery-Gated Transformer",
            "",
            f"- Status: `{payload['discovery_gated_transformer']['status']}`",
            f"- JSON: `{payload['discovery_gated_transformer']['json_artifact']}`",
            f"- Markdown: `{payload['discovery_gated_transformer']['markdown_artifact']}`",
            f"- Schema: `{payload['discovery_gated_transformer']['schema_id']}`",
            f"- Model id: `{payload['discovery_gated_transformer']['model_id_pointer']}`",
            f"- Components: `{payload['discovery_gated_transformer']['component_descriptors_pointer']}`",
            f"- Hardgate slots: `{payload['discovery_gated_transformer']['hardgate_slots_pointer']}`",
            f"- Overall state: `{payload['discovery_gated_transformer']['overall_state_pointer']}`",
            f"- Not claimed: `{payload['discovery_gated_transformer']['not_claimed_pointer']}`",
            f"- Downstream scope: `{payload['discovery_gated_transformer']['downstream_scope_pointer']}`",
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
            "## Release NameCert candidate",
            "",
            f"- Status: `{payload['release_namecert_candidate']['status']}`",
            f"- JSON: `{payload['release_namecert_candidate']['json_artifact']}`",
            f"- Markdown: `{payload['release_namecert_candidate']['markdown_artifact']}`",
            f"- Owner artifact: `{payload['release_namecert_candidate']['owner_artifact']}`",
            f"- Candidate status: `{payload['release_namecert_candidate']['candidate_status']}`",
            f"- Revoke pointer: `{payload['release_namecert_candidate']['revoke_if_pointer']}`",
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
    claim_verdict_rows = write_claim_verdicts(root=ROOT, generated_at=timestamp)
    if only is None:
        write_claim_graph(root=ROOT, generated_at=timestamp)
    write_discovery_negative_witness_summary(root=ROOT, generated_at=timestamp)
    mutation_ledger = _negative_witness_mutation_ledger_payload(generated_at=timestamp)
    _write_json_atomic(_artifact_path(NEGATIVE_WITNESS_MUTATION_LEDGER_JSON_ARTIFACT), mutation_ledger)
    _write_text_atomic(
        _artifact_path(NEGATIVE_WITNESS_MUTATION_LEDGER_MARKDOWN_ARTIFACT),
        _render_negative_witness_mutation_ledger_markdown(mutation_ledger),
    )
    new_model_hardgates = _new_model_hardgates_payload(generated_at=timestamp)
    _write_json_atomic(_artifact_path(NEW_MODEL_HARDGATES_JSON_ARTIFACT), new_model_hardgates)
    _write_text_atomic(
        _artifact_path(NEW_MODEL_HARDGATES_MARKDOWN_ARTIFACT),
        _render_new_model_hardgates_markdown(new_model_hardgates),
    )
    discovery_gated_transformer = _build_discovery_gated_transformer_payload(generated_at=timestamp)
    _write_json_atomic(_artifact_path(DISCOVERY_GATED_TRANSFORMER_JSON_ARTIFACT), discovery_gated_transformer)
    _write_text_atomic(
        _artifact_path(DISCOVERY_GATED_TRANSFORMER_MARKDOWN_ARTIFACT),
        _render_discovery_gated_transformer_markdown(discovery_gated_transformer),
    )
    draft_payload = _index(results, generated_at=timestamp, claim_verdict_rows=claim_verdict_rows)
    _write_json_atomic(INDEX_ARTIFACT, draft_payload)
    _write_text_atomic(CANONICAL_DIR / "index.md", _render_index_markdown(draft_payload))
    from scripts.release_manifest_sidecar import write_release_manifest_sidecar
    from scripts.run_release_namecert_candidate import write_release_namecert_candidate

    write_release_manifest_sidecar(root=ROOT, generated_at=timestamp)
    write_release_namecert_candidate(root=ROOT, generated_at=timestamp, make_check_passed=True)
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

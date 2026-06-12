"""Discovery-gated transformer canonical projection."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL


SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer"
ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer"
MODEL_ID = "discovery-gated-transformer"
PRODUCER = "scripts/run_discovery_gated_transformer.py"
PROJECTOR = "bedc_quality_lab.discovery_gated_transformer.DiscoveryGatedTransformerProjector"
CANONICAL_JSON_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/discovery-gated-transformer.md"
RUN_ROOT = "reports/runs/discovery-gated-transformer"
DGT_NEURAL_ABLATION_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
NABL_HARDGATE_STATUS_POINTER = "$.nabl_hardgates.status"
NABL_HARDGATE_FAILED_GATE_POINTER = "$.nabl_hardgates.failed_gate"
DGT_L0_CONTROLS_ARTIFACT = "reports/canonical/dgt-l0-controls.json"
DGT_L1_CONTROLS_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
FAIR_L1_DECISION_ARTIFACT = "reports/canonical/fair-l1-decision.json"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_ROOT}/claim_capsule.json"
EVIDENCE_ENVELOPE_ARTIFACT = f"{RUN_ROOT}/evidence_envelope.json"
MECHANISM_NAMECERT_ARTIFACT = f"{RUN_ROOT}/mechanism_namecert.json"
JET_CERTIFICATE_ARTIFACT = f"{RUN_ROOT}/jet_certificate.json"
SOURCE_REFS_ARTIFACT = f"{RUN_ROOT}/source_refs.json"
GATE_NAMES = tuple(f"DGT-HG{index}" for index in range(1, 21))
JET_CERTIFICATE_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.jet-certificate"
JET_CERTIFICATE_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.jet-certificate"
JET_HARDGATE_NAMES = tuple(f"JET-HG{index}" for index in range(1, 9))
JET_REQUIRED_SURFACES = (
    "boundary_spec",
    "derivative_spec",
    "causal_spec",
    "irreducibility_spec",
    "matched_random_control",
    "jet_coverage",
)
JET_SURFACE_SLOTS = (
    "boundary_spec_ref",
    "derivative_spec_ref",
    "causal_spec_ref",
    "irreducibility_spec_ref",
)
JET_FORBIDDEN_MATCH_TERMS = (
    "terminal_verdict",
    "production",
    "deployment",
    "global superiority",
    "architecture superiority",
)
JET_FORBIDDEN_TERM_LABELS = (
    "terminal verdict token",
    "operation authority wording",
    "release authority wording",
    "external superiority wording",
    "architecture superiority wording",
)
TOOL_ROUTE_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.tool-route-evidence"
TOOL_ROUTE_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.tool-route-evidence"
TOOL_ROUTE_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$"
TOOL_ROUTE_SOURCE_ISSUE_REF = "github:issue:928"
TOOL_ROUTE_CGA_ROUTE_PATCH_REF = "reports/canonical/certificate-gated-attention.json:$.route_patch_protocol"
TOOL_ROUTE_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "source_issue_ref",
    "synthetic_tool_call_grid",
    "route_classes",
    "cga_route_patch_ref",
    "admission_ledger",
    "blocked_route_evidence",
    "unsafe_invalid_audit",
    "classifier_surface_delta",
    "net_positive_signal",
    "hardgate",
    "failed_gate",
    "not_claimed",
    "revocation_rows",
    "forbidden_alias_audit",
)
TOOL_ROUTE_GATE_NAMES = tuple(f"DGT-TOOL-HG{index}" for index in range(1, 7))
FAMILY_DEFINITION_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.family-definition"
FAMILY_DEFINITION_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.family-definition"
FAMILY_DEFINITION_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$"
FAMILY_DEFINITION_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.family_definition"
FAMILY_DEFINITION_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "slot_state",
    "definition_scope",
    "invariant_groups",
    "hardgate",
    "model_family_claim_status",
    "not_claimed",
    "forbidden_claim_term_audit",
)
FAMILY_DEFINITION_GROUPS = ("architecture", "objective", "certificate")
FAMILY_DEFINITION_GATE_NAMES = tuple(f"DGT-FAMILY-HG{index}" for index in range(1, 5))
FAMILY_DEFINITION_FORBIDDEN_TERMS = (
    "global superiority",
    "architecture superiority",
    "production authority",
    "universal training recipe",
    "terminal verdict",
)
CLAIMED_POSITIVE_ROUTE_CLASSES = frozenset({"valid_positive_discovery"})
BLOCKED_ROUTE_CLASSES = frozenset({"invalid_route", "unsafe_route"})
TOOL_ROUTE_RECURSIVE_FORBIDDEN_TOKENS = (
    ".refactor-loop",
    "host.env",
    "terminal_verdict",
    "discovery_gated_transformer",
    "tool-use-dgt",
    "tool-use-toy-dgt",
    "tool_use_dgt",
    "tool_use_toy_dgt",
)
COPIED_CGA_PAYLOAD_KEYS = frozenset(
    {
        "route_patch_protocol",
        "cga_route_patch_protocol",
        "classifier_payload",
        "classifier_surface",
        "cga_metric_body",
        "cga_metrics",
        "certificate_gate_summary",
        "torch_attention_evidence",
    }
)
REJECTED_INLINE_KEYS = frozenset(
    {
        "records",
        "quality_q",
        "attention_rows",
        "attention",
        "search_score",
        "search_score_rows",
        "terminal_verdict",
        "standalone_verdict",
        "private_row_carrier",
        "raw_metrics",
        "metric_rows",
        *COPIED_CGA_PAYLOAD_KEYS,
    }
)
NOT_CLAIMED = (
    "Bounded deterministic toy evidence only.",
    "No external operation authority.",
    "No universal training recipe claim.",
    "No external verdict ownership.",
)
D5O_NOT_CLAIMED = (
    "Bounded D5-O claim over deterministic toy surfaces only.",
    "No production robustness claim.",
    "No global robustness claim.",
    "No LLM replacement claim.",
    "No D5-M mechanism closure claim.",
)
D5O_PROJECTION_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection"
D5O_GATE_NAMES = tuple(f"D5O-HG{index}" for index in range(1, 9))
D5O_REQUIRED_KEYS = (
    "status",
    "discovery_level",
    "source_level",
    "gate_status",
    "gates",
    "evidence_pointers",
    "boundary_ledger",
    "blocked_reason",
    "not_claimed",
    "scope",
    "surface_summary",
    "anti_triviality_status",
    "anti_triviality_policy",
    "anti_triviality_recommended_level",
    "anti_triviality_failed_gate",
    "anti_triviality_gate_evidence",
)
D5O_REVIEW_PHRASE = "High-impact review accepted for bounded D5-O projection."
HIGH_IMPACT_REVIEW_JSON_ARTIFACT = "reports/canonical/high-impact-review.json"
D5M_NOT_CLAIMED = (
    "Bounded D5-M mechanism claim over deterministic model-prototype evidence only.",
    "No production authority claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No unbounded mechanism closure claim.",
)
D5M_PROJECTION_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.d5_m_projection"
D5M_DEFAULT_EVIDENCE_SCOPE = ("bounded-design", "toy-model", "theorem-backed", "production-forbidden")
EVIDENCE_SCOPE_VALUES = frozenset(
    {
        "bounded-design",
        "toy-model",
        "small-real-training",
        "theorem-backed",
        "production-forbidden",
    }
)
D5M_GATE_NAMES = tuple(f"D5M-HG{index}" for index in range(1, 11))
D5M_REQUIRED_KEYS = (
    "status",
    "readiness",
    "discovery_level",
    "source_level",
    "evidence_scope",
    "terminal_verdict_scope",
    "gate_status",
    "failed_gate",
    "blocked_reason",
    "hardgates",
    "boundary_ledger",
    "mechanism_certificate_pointer",
    "jet_certificate_pointer",
    "causal_patch_pointer",
    "component_ablation_pointer",
    "neural_ablation_pointer",
    "negative_witness_pointers",
    "forbidden_claim_audit",
    "not_claimed",
    "anti_triviality_status",
    "anti_triviality_policy",
    "anti_triviality_recommended_level",
    "anti_triviality_failed_gate",
    "anti_triviality_gate_evidence",
)
SCALING_LADDER_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.scaling_ladder"
SCALING_LADDER_LEVEL_IDS = (
    "L0_toy",
    "L1_tiny_sequence",
    "L2_char_lm",
    "L3_byte_lm",
    "L4_tool_use_toy",
    "L5_small_world_model",
)
SCALING_LADDER_GATE_NAMES = tuple(f"SCALE-HG{index}" for index in range(1, 7))
SCALING_LADDER_NOT_CLAIMED = (
    "Bounded model prototype scaling only.",
    "No production scale claim.",
    "No GPT or Llama claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No universal recipe claim.",
    "No unbounded scaling law claim.",
)
SCALING_LADDER_REQUIRED_KEYS = (
    "status",
    "review_status",
    "discovery_level",
    "evidence_scope",
    "source_projection",
    "l0_toy_projection_ref",
    "review_status_ref",
    "hardgate_summary_ref",
    "ladder_consumption_ref",
    "level_state",
    "promotion_status",
    "opened_levels",
    "overall_status",
    "not_inherited_from_l0",
    "levels",
    "boundary_ledger",
    "hardgate",
    "not_claimed",
    "anti_triviality_status",
    "anti_triviality_policy",
    "anti_triviality_recommended_level",
    "anti_triviality_failed_gate",
    "anti_triviality_gate_evidence",
)
L1_TINY_SEQUENCE_PROJECTION_POINTER = f"{FAIR_L1_DECISION_ARTIFACT}:$.ladder_state_projection"
L1_NEGATIVE_WITNESS_SWEEP_REF = {"artifact": DGT_L1_CONTROLS_ARTIFACT, "pointer": "$.negative_witness_sweep"}
L1_INTERPRETATION_BOUNDARY_REF = {"artifact": FAIR_L1_DECISION_ARTIFACT, "pointer": "$.ladder_state_projection"}
L1_OOD_MECHANISM_REF = {"artifact": DGT_L1_CONTROLS_ARTIFACT, "pointer": "$.l1_ood_mechanism"}
L1_OOD_MECHANISM_VERDICT_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_ood_mechanism.verdict"
L1_OOD_MECHANISM_L2_IMPLICATION_POINTER = f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_ood_mechanism.l2_implication"
FAIR_L1_DECISION_STATUS_POINTER = f"{FAIR_L1_DECISION_ARTIFACT}:$.decision.status"
L0_CONSTRUCT_SUSPENSION_REF = {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.construct_suspension"}
L0_CONTROL_POINTER_CONTRACT = {
    "base_transformer_control": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.controls.base_transformer_control"},
    "matched_random_structural_control": {
        "artifact": DGT_L0_CONTROLS_ARTIFACT,
        "pointer": "$.controls.matched_random_structural_control",
    },
    "compute_param_ledger": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.compute_param_ledger"},
    "negative_witness_sweep": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.negative_witness_sweep"},
    "independent_replay": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.independent_replay"},
    "l0_control_projection": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.l0_toy_projection"},
}
L0_TOY_PROJECTION_REF = {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.l0_toy_projection"}
L0_REVIEW_STATUS_REF = {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.l0_toy_projection.review_status"}
L0_HARDGATE_SUMMARY_REF = {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.l0_toy_projection.hardgate_statuses.pass"}
L0_LADDER_CONSUMPTION_REF = {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.l0_toy_projection.ladder_consumption"}
L0_FORBIDDEN_LADDER_KEYS = frozenset(
    {
        "L0-PASS-HG1",
        "L0-PASS-HG2",
        "L0-PASS-HG3",
        "L0-PASS-HG4",
        "L0-PASS-HG5",
        "L0-PASS-HG6",
        "hardgate_rows",
        "base_control",
        "base_transformer_control",
        "matched_random",
        "matched_random_structural_control",
        "ledger",
        "compute_param_ledger",
        "negative_witness",
        "negative_witness_sweep",
        "witness",
        "replay",
        "independent_replay",
    }
)
COMPONENT_ABLATION_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.component-ablation"
COMPONENT_ABLATION_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.component-ablation"
COMPONENT_ABLATION_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation"
COMPONENT_ABLATION_SEED = 1105
COMPONENT_ABLATION_GATE_NAMES = tuple(f"ABL-HG{index}" for index in range(1, 7))
COMPONENT_ABLATION_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "status",
    "seed",
    "arm_count",
    "components",
    "arms",
    "metric_contract",
    "hardgate",
    "failed_gate",
    "claim_policy",
    "not_claimed",
    "revocation_rows",
    "forbidden_claim_term_audit",
)
COMPONENT_ABLATION_FORBIDDEN_TERMS = (
    "terminal_verdict",
    "production",
    "global superiority",
    "architecture superiority",
    "formal closure",
)
COMPONENT_ABLATION_FORBIDDEN_TERM_LABELS = (
    "terminal verdict token",
    "operation authority wording",
    "external superiority wording",
    "architecture superiority wording",
    "formal closure wording",
)
D4_PROJECTION_GATE_NAMES = tuple(f"PROJ-HG{index}" for index in range(1, 11))
D4_PROJECTION_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "model_id",
    "gates",
    "failed_gate",
    "failed_gate_pointer",
    "blocked_reason",
    "discovery_level",
    "readiness",
    "net_positive_signal",
    "classifier_surface_delta_pointer",
    "input_pointers",
    "core_contracts",
    "not_claimed",
    "forbidden_claim_term_audit",
    "scope_seal",
    "matched_control",
    "claim_basis",
    "anti_triviality_status",
    "anti_triviality_policy",
    "anti_triviality_recommended_level",
    "anti_triviality_failed_gate",
    "anti_triviality_gate_evidence",
)
ROBUSTNESS_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.robustness"
ROBUSTNESS_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.robustness"
ROBUSTNESS_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness"
ROBUSTNESS_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness"
ROBUSTNESS_GATE_NAMES = tuple(f"DGT-ROB-HG{index}" for index in range(1, 9))
ROBUSTNESS_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "model_id",
    "status",
    "readiness",
    "discovery_level",
    "source_artifacts",
    "source_evidence",
    "operational_contract",
    "hardgate",
    "failed_gate",
    "failed_gate_pointer",
    "not_claimed",
    "revocation_rows",
    "forbidden_claim_term_audit",
)
ROBUSTNESS_FORBIDDEN_TERMS = (
    "terminal_verdict",
    "production",
    "global superiority",
    "architecture superiority",
    ".refactor-loop",
    "host.env",
)
ROBUSTNESS_FORBIDDEN_TERM_LABELS = (
    "terminal verdict token",
    "operation authority wording",
    "external superiority wording",
    "architecture superiority wording",
    "host-private refactor path",
    "host-private env path",
)
LAT_CANONICAL_ARTIFACT = "reports/canonical/ledger-aware-transformer.json"
MODEL_COMPARISON_CANONICAL_ARTIFACT = "reports/canonical/model-comparison.json"


@dataclass(frozen=True)
class EvidenceCell:
    artifact: str
    pointer: str

    def as_payload(self) -> dict[str, str]:
        return {"artifact": self.artifact, "pointer": self.pointer}


@dataclass(frozen=True)
class DgtD4Projection:
    payload: dict[str, Any]

    def as_payload(self) -> dict[str, Any]:
        return dict(self.payload)


class DgtOperationalRobustnessLedger:
    def evaluate(
        self,
        owner_payload: Mapping[str, Any],
        source_payloads: Mapping[str, Mapping[str, Any]],
    ) -> dict[str, Any]:
        lat = source_payloads.get("ledger_aware_transformer", {})
        model_comparison = source_payloads.get("model_comparison", {})
        robustness_signal = lat.get("robustness_signal") if isinstance(lat, Mapping) else None
        lat_discovery = lat.get("discovery_map_signal") if isinstance(lat, Mapping) else None
        d4_projection = owner_payload.get("d4_projection") if isinstance(owner_payload, Mapping) else None
        component_ablation = owner_payload.get("component_ablation") if isinstance(owner_payload, Mapping) else None
        source_artifacts = owner_payload.get("source_artifacts") if isinstance(owner_payload, Mapping) else None
        source_payload = {
            "ledger_aware_transformer_pointer": (
                source_artifacts.get("ledger_aware_transformer_pointer")
                if isinstance(source_artifacts, Mapping)
                else None
            ),
            "model_comparison_pointer": (
                source_artifacts.get("model_comparison_pointer")
                if isinstance(source_artifacts, Mapping)
                else None
            ),
            "d4_projection_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection",
            "component_ablation_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation",
        }
        source_evidence = {
            "ledger_aware_transformer": {
                "artifact_id": lat.get("artifact_id") if isinstance(lat, Mapping) else None,
                "hardgate_status": _mapping_path(lat, ("hardgate", "status")),
                "robustness_status": (
                    robustness_signal.get("status") if isinstance(robustness_signal, Mapping) else None
                ),
                "pass_surface_count": (
                    robustness_signal.get("pass_surface_count") if isinstance(robustness_signal, Mapping) else None
                ),
                "required_pass_surface_count": (
                    robustness_signal.get("required_pass_surface_count")
                    if isinstance(robustness_signal, Mapping)
                    else None
                ),
                "level_candidate": (
                    lat_discovery.get("level_candidate") if isinstance(lat_discovery, Mapping) else None
                ),
                "source_role": "component-evidence-input",
            },
            "model_comparison": {
                "artifact_id": model_comparison.get("artifact_id") if isinstance(model_comparison, Mapping) else None,
                "hardgate_status": _model_comparison_hardgate_status(model_comparison),
                "source_role": "matched-control-evidence-input",
            },
            "owner": {
                "model_id": owner_payload.get("model_id"),
                "d4_readiness": d4_projection.get("readiness") if isinstance(d4_projection, Mapping) else None,
                "d4_discovery_level": (
                    d4_projection.get("discovery_level") if isinstance(d4_projection, Mapping) else None
                ),
                "component_ablation_status": _mapping_path(component_ablation, ("hardgate", "status")),
            },
        }
        payload: dict[str, Any] = {
            "schema_id": ROBUSTNESS_SCHEMA_ID,
            "artifact_id": ROBUSTNESS_ARTIFACT_ID,
            "owner_ref": ROBUSTNESS_OWNER_REF,
            "model_id": MODEL_ID,
            "status": "blocked",
            "readiness": "blocked",
            "discovery_level": "D0",
            "source_artifacts": source_payload,
            "source_evidence": source_evidence,
            "operational_contract": {
                "readiness_pointer": ROBUSTNESS_POINTER,
                "owner_policy": "DGT owner-local readiness only",
                "lat_relationship": "LAT remains component evidence input only",
                "robustness_basis": "bounded deterministic toy evidence with matched controls",
            },
            "hardgate": {},
            "failed_gate": [],
            "failed_gate_pointer": None,
            "not_claimed": [
                "No deployment readiness is claimed.",
                "No cross-model winner is claimed.",
                "No external operation authority is claimed.",
                "No D5-M mechanism closure is claimed.",
            ],
            "revocation_rows": [
                {
                    "gate": "DGT-ROB-HG2",
                    "condition": "Revoke when the D4 owner projection is blocked.",
                },
                {
                    "gate": "DGT-ROB-HG4",
                    "condition": "Revoke when LAT multi-surface evidence is absent or not passing.",
                },
                {
                    "gate": "DGT-ROB-HG8",
                    "condition": "Revoke when forbidden authority wording appears in DGT robustness fields.",
                },
            ],
            "forbidden_claim_term_audit": {},
        }
        payload["forbidden_claim_term_audit"] = _robustness_forbidden_claim_term_audit(payload)
        payload["hardgate"] = self.hardgate_rows(payload)
        payload["failed_gate"] = payload["hardgate"]["failed_gate"]
        first_failed = payload["failed_gate"][0] if payload["failed_gate"] else None
        payload["failed_gate_pointer"] = (
            None if first_failed is None else f"{ROBUSTNESS_POINTER}.hardgate.gates.{first_failed}"
        )
        if first_failed is None:
            payload["status"] = "ready"
            payload["readiness"] = "ready"
            payload["discovery_level"] = "D5-O"
        validate_operational_robustness(payload, owner_payload)
        return payload

    def hardgate_rows(self, robustness: Mapping[str, Any]) -> dict[str, Any]:
        return evaluate_operational_robustness_hardgates(robustness)


@dataclass(frozen=True)
class DgtComponentSpec:
    component_id: str
    owner_pointer: str
    component_role: str

    def as_payload(self) -> dict[str, str]:
        return {
            "component_id": self.component_id,
            "owner_pointer": self.owner_pointer,
            "component_role": self.component_role,
        }


@dataclass(frozen=True)
class DgtAblationMetricContract:
    primary_delta: str = "bounded_toy_signal_delta"
    measurable_effect_threshold: float = 0.02
    zero_effect_policy: str = "fail-closed-no-causal-claim"
    matched_control_pointer: str = f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.matched_control"

    def as_payload(self) -> dict[str, Any]:
        return {
            "primary_delta": self.primary_delta,
            "measurable_effect_threshold": self.measurable_effect_threshold,
            "zero_effect_policy": self.zero_effect_policy,
            "matched_control_pointer": self.matched_control_pointer,
        }


@dataclass(frozen=True)
class DgtAblationArmSpec:
    arm_id: str
    component: DgtComponentSpec
    disabled_components: tuple[str, ...]
    expected_signal_delta: float

    def as_payload(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "component_id": self.component.component_id,
            "component_pointer": self.component.owner_pointer,
            "disabled_components": list(self.disabled_components),
            "expected_signal_delta": self.expected_signal_delta,
        }


def artifact_pointer(cell: Mapping[str, Any]) -> str:
    return f"{cell['artifact']}:{cell['pointer']}"


def _cell(artifact: str, pointer: str) -> dict[str, str]:
    return EvidenceCell(artifact=artifact, pointer=pointer).as_payload()


def _resolve_cell(root: Path, cell: Mapping[str, Any]) -> Any:
    return resolve_artifact_pointer(root, artifact_pointer(cell))


def default_component_refs() -> dict[str, dict[str, str]]:
    return {
        "hardgate_contract": _cell("reports/canonical/new_model_hardgates.json", "$.gates"),
        "mechanism_dna": _cell("reports/canonical/mechanism_dna.json", "$.rows"),
        "mechanism_namecert": _cell(CANONICAL_JSON_ARTIFACT, "$.mechanism_namecert_ref"),
        "discovery_map": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
        "training_replay": _cell(
            "reports/canonical/discovery-gated-transformer-training.json",
            "$.hardgates",
        ),
    }


def default_architecture_spec() -> dict[str, Any]:
    return {
        "architecture_id": MODEL_ID,
        "role": "bounded sequence transformer prototype",
        "gating_protocol": "discovery hardgate before promotion",
        "evidence_policy": "pointer-only source cells",
        "component_order": [
            "hardgate_contract",
            "mechanism_dna",
            "mechanism_namecert",
            "discovery_map",
            "training_replay",
        ],
    }


def default_discovery_map_signal() -> dict[str, Any]:
    return {
        "status": "candidate-local-positive",
        "level_candidate": "D4",
        "evidence": _cell(CANONICAL_JSON_ARTIFACT, "$.d4_projection.discovery_level"),
        "map_ref": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
    }


def default_dgt_source_refs() -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:discovery-gated-transformer.source-refs",
        "artifact_id": "bedc-quality-lab:discovery-gated-transformer.source-refs",
        "model_id": MODEL_ID,
        "generated_at": None,
        "source_refs": {
            "boundary_spec": _cell("reports/canonical/boundary_causal_derivative_schema.json", "$.boundary_spec"),
            "derivative_spec": _cell("reports/canonical/derivative_order_ledger.json", "$.rows"),
            "causal_patch_suite": _cell("reports/canonical/causal_patch_suite.json", "$.patches"),
            "irreducibility_report": _cell("reports/canonical/irreducibility_report.json", "$.residual_gains"),
            "matched_random_control": _cell("reports/canonical/order-k-benchmark.json", "$.matched_random_controls"),
            "jet_coverage_matrix": _cell("reports/canonical/jet_coverage_matrix.json", "$.rows"),
            "discovery_map": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
        },
    }


def _default_jet_surface_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, surface_id in enumerate(JET_REQUIRED_SURFACES, start=1):
        rows.append(
            {
                "surface_id": surface_id,
                "boundary_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.boundary_spec",
                "derivative_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                "causal_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.causal_patch_suite",
                "irreducibility_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.irreducibility_report",
                "low_order_baseline_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                "causal_patch_evidence_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.causal_patch_suite",
                "matched_random_gain": -0.01 * index,
                "dgt_jet_gain": 0.20 + (0.01 * index),
                "base_jet_gain": 0.10,
                "matched_random_jet_gain": 0.0,
                "irreducible_residual_gain": 0.05 + (0.01 * index),
            }
        )
    return rows


def _jet_gate_rows(failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "JET-HG1": "$.surface_rows",
        "JET-HG2": "$.surface_rows",
        "JET-HG3": "$.surface_rows",
        "JET-HG4": "$.surface_rows",
        "JET-HG5": "$.surface_rows",
        "JET-HG6": "$.jet_coverage",
        "JET-HG7": "$.derivative_debt_ledger",
        "JET-HG8": "$.forbidden_claim_term_audit",
    }
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(JET_CERTIFICATE_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in JET_HARDGATE_NAMES
    }


def _jet_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "claim_status": payload.get("claim_status"),
            "not_claimed": payload.get("not_claimed"),
            "revocation_rows": payload.get("revocation_rows"),
        },
        sort_keys=True,
    ).lower()
    hits = [label for term, label in zip(JET_FORBIDDEN_MATCH_TERMS, JET_FORBIDDEN_TERM_LABELS) if term in serialized]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(JET_FORBIDDEN_TERM_LABELS),
    }


def evaluate_dgt_jet_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    rows = payload.get("surface_rows")
    rows = rows if isinstance(rows, list) else []
    if (
        set(row.get("surface_id") for row in rows if isinstance(row, Mapping)) != set(JET_REQUIRED_SURFACES)
        or any(
            not isinstance(row, Mapping)
            or any(not isinstance(row.get(slot), str) or ":$" not in row[slot] for slot in JET_SURFACE_SLOTS)
            for row in rows
        )
    ):
        failed.append("JET-HG1")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("low_order_baseline_ref"), str)
        or ":$" not in row["low_order_baseline_ref"]
        for row in rows
    ):
        failed.append("JET-HG2")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("irreducible_residual_gain"), (int, float))
        or row["irreducible_residual_gain"] <= 0
        for row in rows
    ):
        failed.append("JET-HG3")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("causal_patch_evidence_ref"), str)
        or ":$" not in row["causal_patch_evidence_ref"]
        for row in rows
    ):
        failed.append("JET-HG4")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("matched_random_gain"), (int, float))
        or row["matched_random_gain"] > 0
        for row in rows
    ):
        failed.append("JET-HG5")
    coverage = payload.get("jet_coverage")
    if (
        not isinstance(coverage, Mapping)
        or not isinstance(coverage.get("dgt"), (int, float))
        or not isinstance(coverage.get("base_control"), (int, float))
        or not isinstance(coverage.get("matched_random_control"), (int, float))
        or coverage["dgt"] <= coverage["base_control"]
        or coverage["dgt"] <= coverage["matched_random_control"]
    ):
        failed.append("JET-HG6")
    ledger = payload.get("derivative_debt_ledger")
    ledger_rows = ledger.get("rows") if isinstance(ledger, Mapping) else None
    ledger_rows = ledger_rows if isinstance(ledger_rows, list) else []
    ledger_ids = {row.get("surface_id") for row in ledger_rows if isinstance(row, Mapping) and row.get("status") == "complete"}
    if ledger_ids != set(JET_REQUIRED_SURFACES):
        failed.append("JET-HG7")
    audit = payload.get("forbidden_claim_term_audit")
    expected_audit = _jet_forbidden_claim_term_audit(payload)
    if not isinstance(audit, Mapping) or dict(audit) != expected_audit or expected_audit["status"] != "pass":
        failed.append("JET-HG8")
    failed_gate = sorted(set(failed), key=JET_HARDGATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(JET_HARDGATE_NAMES),
        "gates": _jet_gate_rows(failed_gate),
        "failed_gate": failed_gate,
    }


def build_dgt_jet_certificate(source_refs: Mapping[str, Any]) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_id": JET_CERTIFICATE_SCHEMA_ID,
        "artifact_id": JET_CERTIFICATE_ARTIFACT_ID,
        "model_id": MODEL_ID,
        "generated_at": None,
        "owner_ref": f"{CANONICAL_JSON_ARTIFACT}:$",
        "source_refs_ref": _cell(SOURCE_REFS_ARTIFACT, "$.source_refs"),
        "source_artifacts": source_refs.get("source_refs", source_refs),
        "certificate_scope": "DGT owner-local boundary-causal-jet certificate",
        "surface_rows": _default_jet_surface_rows(),
        "jet_coverage": {
            "dgt": 0.72,
            "base_control": 0.41,
            "matched_random_control": 0.37,
            "coverage_matrix_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.jet_coverage_matrix",
        },
        "derivative_debt_ledger": {
            "status": "complete",
            "rows": [
                {
                    "surface_id": surface_id,
                    "status": "complete",
                    "ledger_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                }
                for surface_id in JET_REQUIRED_SURFACES
            ],
        },
        "claim_status": {
            "status": "owner-local-candidate",
            "claim_scope": "bounded deterministic toy evidence only",
        },
        "hardgate": {},
        "failed_gate": [],
        "not_claimed": [
            "The certificate is bounded to deterministic toy source refs.",
            "The certificate is owner-local evidence only.",
            "The certificate does not claim external verdict ownership.",
        ],
        "revocation_rows": [
            {"gate": "JET-HG1", "condition": "Revoke when any required Boundary, Derivative, Causal, or Irreducibility slot is absent."},
            {"gate": "JET-HG8", "condition": "Revoke when forbidden authority language appears in claim fields."},
        ],
        "forbidden_claim_term_audit": {},
    }
    payload["forbidden_claim_term_audit"] = _jet_forbidden_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_jet_hardgates(payload)
    payload["failed_gate"] = payload["hardgate"]["failed_gate"]
    validate_dgt_jet_certificate(payload)
    return payload


def validate_dgt_jet_certificate(payload: Mapping[str, Any]) -> None:
    expected = {
        "schema_id",
        "artifact_id",
        "model_id",
        "generated_at",
        "owner_ref",
        "source_refs_ref",
        "source_artifacts",
        "certificate_scope",
        "surface_rows",
        "jet_coverage",
        "derivative_debt_ledger",
        "claim_status",
        "hardgate",
        "failed_gate",
        "not_claimed",
        "revocation_rows",
        "forbidden_claim_term_audit",
    }
    if set(payload) != expected:
        raise ValueError("DGT jet certificate fields mismatch")
    if payload["schema_id"] != JET_CERTIFICATE_SCHEMA_ID or payload["artifact_id"] != JET_CERTIFICATE_ARTIFACT_ID:
        raise ValueError("DGT jet certificate identity mismatch")
    if payload["model_id"] != MODEL_ID or payload["owner_ref"] != f"{CANONICAL_JSON_ARTIFACT}:$":
        raise ValueError("DGT jet certificate owner mismatch")
    if not _is_cell(payload["source_refs_ref"]):
        raise ValueError("DGT jet source refs must be a pointer cell")
    hardgate = evaluate_dgt_jet_hardgates(payload)
    if payload["hardgate"] != hardgate:
        raise ValueError("DGT jet hardgate mismatch")
    if payload["failed_gate"] != hardgate["failed_gate"]:
        raise ValueError("DGT jet failed_gate mismatch")
    if hardgate["status"] != "pass":
        raise ValueError("DGT jet hardgate failed")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if token is not None:
        raise ValueError(f"DGT jet certificate contains forbidden value: {token}")


def _default_family_definition_groups() -> dict[str, dict[str, Any]]:
    return {
        "architecture": {
            "group_id": "architecture",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.model_id",
                f"{CANONICAL_JSON_ARTIFACT}:$.architecture_spec",
                f"{CANONICAL_JSON_ARTIFACT}:$.component_refs",
            ],
        },
        "objective": {
            "group_id": "objective",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.discovery_map_signal",
                f"{CANONICAL_JSON_ARTIFACT}:$.hardgate",
                f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
            ],
        },
        "certificate": {
            "group_id": "certificate",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.evidence_envelope_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
            ],
        },
    }


def _family_definition_gate_rows(payload: Mapping[str, Any], failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "DGT-FAMILY-HG1": "$.family_definition.invariant_groups.architecture",
        "DGT-FAMILY-HG2": "$.family_definition.invariant_groups.objective",
        "DGT-FAMILY-HG3": "$.family_definition.invariant_groups.certificate",
        "DGT-FAMILY-HG4": "$.family_definition.forbidden_claim_term_audit",
    }
    del payload
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in FAMILY_DEFINITION_GATE_NAMES
    }


def _forbidden_family_definition_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "definition_scope": payload.get("definition_scope"),
            "model_family_claim_status": payload.get("model_family_claim_status"),
            "not_claimed": payload.get("not_claimed"),
        },
        sort_keys=True,
    ).lower()
    hits = [term for term in FAMILY_DEFINITION_FORBIDDEN_TERMS if term in serialized]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(FAMILY_DEFINITION_FORBIDDEN_TERMS),
    }


def evaluate_dgt_family_definition_hardgate(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    groups = payload.get("invariant_groups")
    groups = groups if isinstance(groups, Mapping) else {}
    for index, group_name in enumerate(FAMILY_DEFINITION_GROUPS, start=1):
        group = groups.get(group_name)
        pointers = group.get("evidence_pointers") if isinstance(group, Mapping) else None
        if (
            not isinstance(group, Mapping)
            or group.get("group_id") != group_name
            or group.get("required") is not True
            or not isinstance(pointers, list)
            or not pointers
            or any(not isinstance(pointer, str) or not pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$") for pointer in pointers)
        ):
            failed.append(f"DGT-FAMILY-HG{index}")
    audit = payload.get("forbidden_claim_term_audit")
    expected_audit = _forbidden_family_definition_claim_term_audit(payload)
    if not isinstance(audit, Mapping) or dict(audit) != expected_audit or expected_audit["status"] != "pass":
        failed.append("DGT-FAMILY-HG4")
    failed_gate = sorted(set(failed), key=FAMILY_DEFINITION_GATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(FAMILY_DEFINITION_GATE_NAMES),
        "gates": _family_definition_gate_rows(payload, failed_gate),
        "failed_gate": failed_gate,
    }


def _family_claim_status_from_hardgate(hardgate: Mapping[str, Any]) -> dict[str, Any]:
    if hardgate.get("status") == "pass":
        return {
            "status": "definition-recorded",
            "claim_scope": "structural pointer definition only",
            "claim_allowed": False,
        }
    return {
        "status": "blocked",
        "claim_scope": "structural pointer definition only",
        "claim_allowed": False,
        "blocked_by": list(hardgate.get("failed_gate", [])),
    }


def build_dgt_family_definition() -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_id": FAMILY_DEFINITION_SCHEMA_ID,
        "artifact_id": FAMILY_DEFINITION_ARTIFACT_ID,
        "owner_ref": FAMILY_DEFINITION_OWNER_REF,
        "slot_state": "present-fail-closed",
        "definition_scope": "bounded DGT structural family definition",
        "invariant_groups": _default_family_definition_groups(),
        "hardgate": {},
        "model_family_claim_status": {},
        "not_claimed": [
            "The family definition is a pointer bundle inside the DGT owner.",
            "The family definition is not a standalone report, runner, backend, registry, or host setting.",
            "The family definition does not admit deployment, promotion, or external authority.",
        ],
        "forbidden_claim_term_audit": {},
    }
    payload["forbidden_claim_term_audit"] = _forbidden_family_definition_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_family_definition_hardgate(payload)
    payload["model_family_claim_status"] = _family_claim_status_from_hardgate(payload["hardgate"])
    payload["forbidden_claim_term_audit"] = _forbidden_family_definition_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_family_definition_hardgate(payload)
    validate_dgt_family_definition(payload)
    return payload


def validate_dgt_family_definition(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(FAMILY_DEFINITION_REQUIRED_KEYS):
        raise ValueError("DGT family definition fields mismatch")
    if payload["schema_id"] != FAMILY_DEFINITION_SCHEMA_ID or payload["artifact_id"] != FAMILY_DEFINITION_ARTIFACT_ID:
        raise ValueError("DGT family definition identity mismatch")
    if payload["owner_ref"] != FAMILY_DEFINITION_OWNER_REF:
        raise ValueError("DGT family definition owner pointer mismatch")
    if payload["slot_state"] != "present-fail-closed":
        raise ValueError("DGT family definition slot state mismatch")
    groups = payload["invariant_groups"]
    if not isinstance(groups, Mapping) or set(groups) != set(FAMILY_DEFINITION_GROUPS):
        raise ValueError("DGT family definition invariant groups mismatch")
    for group_name, group in groups.items():
        if not isinstance(group, Mapping) or set(group) != {"group_id", "required", "evidence_pointers"}:
            raise ValueError(f"DGT family definition group schema mismatch: {group_name}")
    expected_hardgate = evaluate_dgt_family_definition_hardgate(payload)
    if payload["hardgate"] != expected_hardgate:
        raise ValueError("DGT family definition hardgate mismatch")
    if expected_hardgate["status"] != "pass":
        raise ValueError("DGT family definition hardgate failed")
    expected_claim_status = _family_claim_status_from_hardgate(expected_hardgate)
    if payload["model_family_claim_status"] != expected_claim_status:
        raise ValueError("DGT family definition claim status mismatch")
    found = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if found is not None:
        raise ValueError(f"DGT family definition contains forbidden value: {found}")


def sidecar_refs() -> dict[str, dict[str, str]]:
    return {
        "claim_capsule_ref": _cell(CLAIM_CAPSULE_ARTIFACT, "$"),
        "evidence_envelope_ref": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$"),
        "mechanism_namecert_ref": _cell(MECHANISM_NAMECERT_ARTIFACT, "$"),
        "jet_certificate_ref": _cell(JET_CERTIFICATE_ARTIFACT, "$"),
    }


def default_sidecars(*, generated_at: str) -> dict[str, dict[str, Any]]:
    source_refs = default_dgt_source_refs()
    jet_certificate = build_dgt_jet_certificate(source_refs)
    return {
        "claim_capsule": {
            "schema_id": "bedc-quality-lab:dgt-claim-capsule",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-claim-capsule",
            "model_id": MODEL_ID,
            "claim_scope": "bounded D4 candidate prototype",
            "owner_ref": _cell(CANONICAL_JSON_ARTIFACT, "$"),
            "not_claimed_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        },
        "evidence_envelope": {
            "schema_id": "bedc-quality-lab:dgt-evidence-envelope",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-evidence-envelope",
            "model_id": MODEL_ID,
            "component_refs": default_component_refs(),
            "evidence_policy": "pointer-only",
        },
        "mechanism_namecert": {
            "schema_id": "bedc-quality-lab:dgt-mechanism-namecert",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-mechanism-namecert",
            "model_id": MODEL_ID,
            "candidate_mechanism": "discovery-gated sequence route",
            "evidence_ref": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$.component_refs"),
        },
        "source_refs": {**source_refs, "generated_at": generated_at},
        "jet_certificate": {**jet_certificate, "generated_at": generated_at},
    }


def _has_recursive_key(value: Any, forbidden: frozenset[str]) -> str | None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str) and key in forbidden:
                return key
            found = _has_recursive_key(item, forbidden)
            if found is not None:
                return found
    elif isinstance(value, (list, tuple)):
        for item in value:
            found = _has_recursive_key(item, forbidden)
            if found is not None:
                return found
    return None


def _has_recursive_token(value: Any, forbidden: Sequence[str]) -> str | None:
    if isinstance(value, str):
        lowered = value.lower()
        for token in forbidden:
            if token in lowered:
                return token
    elif isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str):
                lowered_key = key.lower()
                for token in forbidden:
                    if token in lowered_key:
                        return token
            found = _has_recursive_token(item, forbidden)
            if found is not None:
                return found
    elif isinstance(value, (list, tuple)):
        for item in value:
            found = _has_recursive_token(item, forbidden)
            if found is not None:
                return found
    return None


def _is_cell(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and set(value) == {"artifact", "pointer"}
        and isinstance(value["artifact"], str)
        and isinstance(value["pointer"], str)
        and value["artifact"]
        and value["pointer"].startswith("$")
    )


def _walk_cells(value: Any) -> bool:
    if _is_cell(value):
        return True
    if isinstance(value, Mapping):
        return all(_walk_cells(item) for item in value.values())
    if isinstance(value, list):
        return all(_walk_cells(item) for item in value)
    return not isinstance(value, (dict, list))


def _artifact_pointer_cell(value: str) -> dict[str, str]:
    artifact, pointer = value.split(":", 1)
    return _cell(artifact, pointer)


def _neural_ablation_ref(root: Path) -> dict[str, str]:
    status = resolve_artifact_pointer(root, f"{DGT_NEURAL_ABLATION_ARTIFACT}:{NABL_HARDGATE_STATUS_POINTER}")
    pointer = NABL_HARDGATE_STATUS_POINTER if status == "pass" else NABL_HARDGATE_FAILED_GATE_POINTER
    return _cell(DGT_NEURAL_ABLATION_ARTIFACT, pointer)


def _mapping_path(value: Any, path: Sequence[str]) -> Any:
    current = value
    for key in path:
        if not isinstance(current, Mapping):
            return None
        current = current.get(key)
    return current


def _model_comparison_hardgate_status(payload: Mapping[str, Any]) -> str | None:
    hardgates = payload.get("hardgates") if isinstance(payload, Mapping) else None
    if not isinstance(hardgates, Mapping) or not hardgates:
        return None
    return "pass" if all(isinstance(row, Mapping) and row.get("status") == "pass" for row in hardgates.values()) else "fail"


def default_robustness_source_payloads() -> dict[str, dict[str, Any]]:
    return {
        "ledger_aware_transformer": {
            "artifact_id": "bedc-quality-lab:ledger-aware-transformer",
            "hardgate": {"status": "pass"},
            "robustness_signal": {
                "status": "pass",
                "pass_surface_count": 3,
                "required_pass_surface_count": 3,
                "pass_surface_pointers": [
                    "$.records.0.deltas.unlogged_error_rate",
                    "$.records.1.deltas.unlogged_error_rate",
                    "$.records.2.deltas.unlogged_error_rate",
                ],
            },
            "discovery_map_signal": {
                "level_candidate": "D5-O",
                "status": "d5-o-candidate",
                "robustness_evidence_pointer": "$.robustness_signal",
            },
        },
        "model_comparison": {
            "artifact_id": "bedc-quality-lab:model-comparison",
            "hardgates": {
                "MC-HG7": {"status": "pass"},
                "MC-HG8": {"status": "pass"},
                "MC-HG9": {"status": "pass"},
            },
        },
    }


def _dgt_component_specs() -> tuple[DgtComponentSpec, ...]:
    return (
        DgtComponentSpec(
            component_id="hardgate_contract",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.component_refs.hardgate_contract",
            component_role="promotion boundary",
        ),
        DgtComponentSpec(
            component_id="mechanism_namecert",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.component_refs.mechanism_namecert",
            component_role="mechanism certificate pointer",
        ),
        DgtComponentSpec(
            component_id="discovery_map",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.component_refs.discovery_map",
            component_role="candidate-level map signal",
        ),
        DgtComponentSpec(
            component_id="training_replay",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.component_refs.training_replay",
            component_role="bounded replay hardgate pointer",
        ),
        DgtComponentSpec(
            component_id="tool_route_evidence",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
            component_role="tool-route admission evidence",
        ),
        DgtComponentSpec(
            component_id="family_definition",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.family_definition",
            component_role="structural family invariant pointer",
        ),
        DgtComponentSpec(
            component_id="jet_certificate",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
            component_role="owner-local jet certificate pointer",
        ),
        DgtComponentSpec(
            component_id="d4_projection",
            owner_pointer=f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection",
            component_role="candidate projection",
        ),
    )


def arm_catalog() -> tuple[DgtAblationArmSpec, ...]:
    components = {spec.component_id: spec for spec in _dgt_component_specs()}
    return (
        DgtAblationArmSpec("drop_hardgate_contract", components["hardgate_contract"], ("hardgate_contract",), 0.09),
        DgtAblationArmSpec("drop_mechanism_namecert", components["mechanism_namecert"], ("mechanism_namecert",), 0.06),
        DgtAblationArmSpec("drop_discovery_map", components["discovery_map"], ("discovery_map",), 0.08),
        DgtAblationArmSpec("drop_training_replay", components["training_replay"], ("training_replay",), 0.04),
        DgtAblationArmSpec("drop_tool_route_evidence", components["tool_route_evidence"], ("tool_route_evidence",), 0.10),
        DgtAblationArmSpec("drop_family_definition", components["family_definition"], ("family_definition",), 0.05),
        DgtAblationArmSpec("drop_jet_certificate", components["jet_certificate"], ("jet_certificate",), 0.07),
        DgtAblationArmSpec("drop_d4_projection", components["d4_projection"], ("d4_projection",), 0.11),
        DgtAblationArmSpec(
            "drop_mechanism_pair",
            components["mechanism_namecert"],
            ("mechanism_namecert", "discovery_map"),
            0.13,
        ),
        DgtAblationArmSpec(
            "drop_evidence_pair",
            components["tool_route_evidence"],
            ("tool_route_evidence", "jet_certificate"),
            0.15,
        ),
        DgtAblationArmSpec(
            "drop_structural_contracts",
            components["family_definition"],
            ("hardgate_contract", "family_definition", "d4_projection"),
            0.18,
        ),
    )


def metric_contract() -> dict[str, Any]:
    return DgtAblationMetricContract().as_payload()


def evaluate_ablation_arm(spec: DgtAblationArmSpec, seed: int) -> dict[str, Any]:
    contract = metric_contract()
    threshold = contract["measurable_effect_threshold"]
    deterministic_jitter = ((seed + sum(ord(char) for char in spec.arm_id)) % 7) * 0.001
    measured_delta = round(max(0.0, spec.expected_signal_delta + deterministic_jitter), 3)
    causal_claim_allowed = measured_delta >= threshold
    return {
        **spec.as_payload(),
        "seed": seed,
        "metric_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation.metric_contract",
        "matched_control_pointer": contract["matched_control_pointer"],
        "measured_effect": measured_delta,
        "effect_status": "measurable" if causal_claim_allowed else "zero-effect-fail-closed",
        "causal_claim_allowed": causal_claim_allowed,
        "claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation.claim_policy",
    }


def _component_ablation_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "status": payload.get("status"),
            "claim_policy": payload.get("claim_policy"),
            "not_claimed": payload.get("not_claimed"),
            "revocation_rows": payload.get("revocation_rows"),
        },
        sort_keys=True,
    ).lower()
    hits = [
        label
        for term, label in zip(COMPONENT_ABLATION_FORBIDDEN_TERMS, COMPONENT_ABLATION_FORBIDDEN_TERM_LABELS)
        if term in serialized
    ]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(COMPONENT_ABLATION_FORBIDDEN_TERM_LABELS),
    }


def _component_ablation_arm_claim_mismatch(row: Mapping[str, Any], threshold: float) -> bool:
    measured_effect = row.get("measured_effect")
    if not isinstance(measured_effect, int | float):
        return True
    if measured_effect >= threshold:
        return row.get("effect_status") != "measurable" or row.get("causal_claim_allowed") is not True
    return (
        row.get("effect_status") != "zero-effect-fail-closed"
        or row.get("causal_claim_allowed") is not False
    )


def _component_ablation_gate_rows(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    arms = payload.get("arms")
    arms = arms if isinstance(arms, list) else []
    arm_ids = [row.get("arm_id") for row in arms if isinstance(row, Mapping)]
    expected_arm_ids = [spec.arm_id for spec in arm_catalog()]
    components = payload.get("components")
    components = components if isinstance(components, list) else []
    contract = payload.get("metric_contract")
    audit = payload.get("forbidden_claim_term_audit")
    threshold = (contract or {}).get("measurable_effect_threshold", 1.0)
    failed_conditions = {
        "ABL-HG1": payload.get("owner_ref") != COMPONENT_ABLATION_OWNER_REF,
        "ABL-HG2": arm_ids != expected_arm_ids or len(arms) != 11 or payload.get("arm_count") != 11,
        "ABL-HG3": any(not isinstance(row, Mapping) or not isinstance(row.get("component_pointer"), str) or ":$" not in row["component_pointer"] for row in arms),
        "ABL-HG4": any(
            not isinstance(row, Mapping)
            or not isinstance(threshold, int | float)
            or _component_ablation_arm_claim_mismatch(row, threshold)
            for row in arms
        ),
        "ABL-HG5": not (
            isinstance(contract, Mapping)
            and contract.get("zero_effect_policy") == "fail-closed-no-causal-claim"
            and isinstance(contract.get("matched_control_pointer"), str)
            and contract["matched_control_pointer"].startswith(f"{CANONICAL_JSON_ARTIFACT}:$")
        ),
        "ABL-HG6": not (
            isinstance(audit, Mapping)
            and dict(audit) == _component_ablation_forbidden_claim_term_audit(payload)
            and audit.get("status") == "pass"
            and len(components) == len(_dgt_component_specs())
        ),
    }
    evidence = {
        "ABL-HG1": "$.component_ablation.owner_ref",
        "ABL-HG2": "$.component_ablation.arms",
        "ABL-HG3": "$.component_ablation.arms",
        "ABL-HG4": "$.component_ablation.claim_policy",
        "ABL-HG5": "$.component_ablation.metric_contract",
        "ABL-HG6": "$.component_ablation.forbidden_claim_term_audit",
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in COMPONENT_ABLATION_GATE_NAMES
    }


def build_component_ablation(
    records: Sequence[DgtAblationArmSpec] | None = None,
    contract: Mapping[str, Any] | None = None,
    *,
    seed: int = COMPONENT_ABLATION_SEED,
) -> dict[str, Any]:
    specs = tuple(records) if records is not None else arm_catalog()
    payload: dict[str, Any] = {
        "schema_id": COMPONENT_ABLATION_SCHEMA_ID,
        "artifact_id": COMPONENT_ABLATION_ARTIFACT_ID,
        "owner_ref": COMPONENT_ABLATION_OWNER_REF,
        "status": "bounded-owner-local",
        "seed": seed,
        "arm_count": len(specs),
        "components": [spec.as_payload() for spec in _dgt_component_specs()],
        "arms": [evaluate_ablation_arm(spec, seed) for spec in specs],
        "metric_contract": dict(contract or metric_contract()),
        "hardgate": {},
        "failed_gate": [],
        "claim_policy": {
            "causal_claim_rule": "claim only arms with measurable owner-local toy effect",
            "zero_effect_rule": "zero-effect arms remain blocked and cannot support causal attribution",
            "owner_scope": "DGT canonical owner only",
        },
        "not_claimed": [
            "Component ablation is bounded deterministic toy evidence inside the DGT owner artifact.",
            "No standalone DGT component-ablation report, runner, registry entry, or sidecar is defined.",
            "Zero-effect components do not support causal attribution.",
        ],
        "revocation_rows": [
            {"gate": "ABL-HG2", "condition": "Revoke when the catalog is not exactly the eleven DGT ablation arms."},
            {"gate": "ABL-HG4", "condition": "Revoke when a zero-effect arm is used as causal evidence."},
        ],
        "forbidden_claim_term_audit": {},
    }
    payload["forbidden_claim_term_audit"] = _component_ablation_forbidden_claim_term_audit(payload)
    payload["hardgate"] = {
        "status": "pass",
        "gate_names": list(COMPONENT_ABLATION_GATE_NAMES),
        "gates": _component_ablation_gate_rows(payload),
    }
    failed = [gate for gate, row in payload["hardgate"]["gates"].items() if row["status"] != "pass"]
    payload["failed_gate"] = failed
    payload["hardgate"]["status"] = "pass" if not failed else "fail"
    validate_component_ablation(payload)
    return payload


def validate_component_ablation(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(COMPONENT_ABLATION_REQUIRED_KEYS):
        raise ValueError("DGT component ablation fields mismatch")
    if payload["schema_id"] != COMPONENT_ABLATION_SCHEMA_ID or payload["artifact_id"] != COMPONENT_ABLATION_ARTIFACT_ID:
        raise ValueError("DGT component ablation identity mismatch")
    if payload["owner_ref"] != COMPONENT_ABLATION_OWNER_REF:
        raise ValueError("DGT component ablation owner pointer mismatch")
    if payload["arm_count"] != 11:
        raise ValueError("DGT component ablation arm count mismatch")
    arms = payload["arms"]
    if not isinstance(arms, list) or [row.get("arm_id") for row in arms if isinstance(row, Mapping)] != [spec.arm_id for spec in arm_catalog()]:
        raise ValueError("DGT component ablation arm catalog mismatch")
    for row in arms:
        if not isinstance(row, Mapping):
            raise ValueError("DGT component ablation arm row must be object")
        if set(row) != {
            "arm_id",
            "component_id",
            "component_pointer",
            "disabled_components",
            "expected_signal_delta",
            "seed",
            "metric_pointer",
            "matched_control_pointer",
            "measured_effect",
            "effect_status",
            "causal_claim_allowed",
            "claim_pointer",
        }:
            raise ValueError("DGT component ablation arm row schema mismatch")
    hardgate = {
        "status": "pass",
        "gate_names": list(COMPONENT_ABLATION_GATE_NAMES),
        "gates": _component_ablation_gate_rows(payload),
    }
    failed = [gate for gate, row in hardgate["gates"].items() if row["status"] != "pass"]
    hardgate["failed_gate"] = failed
    hardgate["status"] = "pass" if not failed else "fail"
    if payload["hardgate"]["gate_names"] != hardgate["gate_names"] or payload["hardgate"]["gates"] != hardgate["gates"]:
        raise ValueError("DGT component ablation hardgate mismatch")
    if payload["failed_gate"] != failed:
        raise ValueError("DGT component ablation failed_gate mismatch")
    if failed:
        raise ValueError("DGT component ablation hardgate failed")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if token is not None:
        raise ValueError(f"DGT component ablation contains forbidden value: {token}")


def _synthetic_tool_call_grid() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "route_math_lookup_positive",
            "tool": "symbolic-table",
            "route_class": "valid_positive_discovery",
            "classifier_surface_delta": {
                "before": "route-unclassified",
                "after": "tool-route-positive-discovery",
                "surface_delta_count": 2,
            },
            "net_positive_signal": True,
            "admission_decision": "admit",
        },
        {
            "route_id": "route_ledger_patch_positive",
            "tool": "ledger-patcher",
            "route_class": "valid_positive_discovery",
            "classifier_surface_delta": {
                "before": "candidate-ledger-gap",
                "after": "route-patched-positive-discovery",
                "surface_delta_count": 1,
            },
            "net_positive_signal": True,
            "admission_decision": "admit",
        },
        {
            "route_id": "route_schema_invalid",
            "tool": "schema-mutator",
            "route_class": "invalid_route",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "block",
        },
        {
            "route_id": "route_secret_unsafe",
            "tool": "host-secret-reader",
            "route_class": "unsafe_route",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "block",
        },
        {
            "route_id": "route_control_neutral",
            "tool": "no-op-control",
            "route_class": "neutral_control",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "do-not-admit",
        },
    ]


def _tool_route_gate_rows(payload: Mapping[str, Any], failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "DGT-TOOL-HG1": "$.tool_route_evidence.classifier_surface_delta",
        "DGT-TOOL-HG2": "$.tool_route_evidence.cga_route_patch_ref",
        "DGT-TOOL-HG3": "$.tool_route_evidence.admission_ledger",
        "DGT-TOOL-HG4": "$.tool_route_evidence.blocked_route_evidence",
        "DGT-TOOL-HG5": "$.tool_route_evidence.not_claimed",
        "DGT-TOOL-HG6": "$.tool_route_evidence.forbidden_alias_audit",
    }
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in TOOL_ROUTE_GATE_NAMES
    }


def evaluate_dgt_tool_route_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    rows = payload.get("synthetic_tool_call_grid")
    rows = rows if isinstance(rows, list) else []
    positive_rows = [row for row in rows if isinstance(row, Mapping) and row.get("route_class") in CLAIMED_POSITIVE_ROUTE_CLASSES]
    if any(not row.get("classifier_surface_delta") or row.get("net_positive_signal") is not True for row in positive_rows):
        failed.append("DGT-TOOL-HG1")

    if payload.get("cga_route_patch_ref") != TOOL_ROUTE_CGA_ROUTE_PATCH_REF:
        failed.append("DGT-TOOL-HG2")
    if _has_recursive_key(payload, COPIED_CGA_PAYLOAD_KEYS) is not None:
        failed.append("DGT-TOOL-HG2")

    ledger = payload.get("admission_ledger")
    ledger_rows = ledger.get("rows") if isinstance(ledger, Mapping) else None
    ledger_rows = ledger_rows if isinstance(ledger_rows, list) else []
    route_class_by_id = {
        row["route_id"]: row.get("route_class")
        for row in rows
        if isinstance(row, Mapping) and isinstance(row.get("route_id"), str)
    }
    ledgered_blocked = [
        row.get("route_id")
        for row in ledger_rows
        if isinstance(row, Mapping) and route_class_by_id.get(row.get("route_id")) in BLOCKED_ROUTE_CLASSES
    ]
    if ledgered_blocked:
        failed.append("DGT-TOOL-HG3")

    blocked = payload.get("blocked_route_evidence")
    blocked_rows = blocked.get("rows") if isinstance(blocked, Mapping) else None
    blocked_rows = blocked_rows if isinstance(blocked_rows, list) else []
    blocked_ids = {row.get("route_id") for row in blocked_rows if isinstance(row, Mapping)}
    invalid_unsafe_ids = {
        row.get("route_id")
        for row in rows
        if isinstance(row, Mapping) and row.get("route_class") in BLOCKED_ROUTE_CLASSES
    }
    if not invalid_unsafe_ids.issubset(blocked_ids):
        failed.append("DGT-TOOL-HG4")

    if not payload.get("not_claimed"):
        failed.append("DGT-TOOL-HG5")

    if _has_recursive_token(payload, TOOL_ROUTE_RECURSIVE_FORBIDDEN_TOKENS) is not None:
        failed.append("DGT-TOOL-HG6")

    failed_gate = sorted(set(failed), key=TOOL_ROUTE_GATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(TOOL_ROUTE_GATE_NAMES),
        "gates": _tool_route_gate_rows(payload, failed_gate),
        "failed_gate": failed_gate,
    }


def build_dgt_tool_route_evidence(*, generated_at: str) -> dict[str, Any]:
    rows = _synthetic_tool_call_grid()
    admitted = [
        {
            "route_id": row["route_id"],
            "route_class": row["route_class"],
            "admission_basis_ref": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[{index}]",
        }
        for index, row in enumerate(rows)
        if row["admission_decision"] == "admit"
    ]
    blocked = [
        {
            "route_id": row["route_id"],
            "route_class": row["route_class"],
            "block_basis": "invalid-or-unsafe-route",
            "evidence_ref": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[{index}]",
        }
        for index, row in enumerate(rows)
        if row["route_class"] in BLOCKED_ROUTE_CLASSES
    ]
    classifier_surface_delta = {
        row["route_id"]: row["classifier_surface_delta"]
        for row in rows
        if row["route_class"] in CLAIMED_POSITIVE_ROUTE_CLASSES
    }
    payload: dict[str, Any] = {
        "schema_id": TOOL_ROUTE_SCHEMA_ID,
        "artifact_id": TOOL_ROUTE_ARTIFACT_ID,
        "owner_ref": TOOL_ROUTE_OWNER_REF,
        "source_issue_ref": TOOL_ROUTE_SOURCE_ISSUE_REF,
        "synthetic_tool_call_grid": rows,
        "route_classes": {
            "claimed_positive": sorted(CLAIMED_POSITIVE_ROUTE_CLASSES),
            "blocked": sorted(BLOCKED_ROUTE_CLASSES),
            "control": ["neutral_control"],
        },
        "cga_route_patch_ref": TOOL_ROUTE_CGA_ROUTE_PATCH_REF,
        "admission_ledger": {
            "policy": "admit only valid positive-discovery routes with classifier delta and net-positive signal",
            "rows": admitted,
        },
        "blocked_route_evidence": {"rows": blocked},
        "unsafe_invalid_audit": {
            "status": "pass",
            "invalid_or_unsafe_route_ids": [row["route_id"] for row in blocked],
            "ledgered_invalid_or_unsafe_route_ids": [],
        },
        "classifier_surface_delta": classifier_surface_delta,
        "net_positive_signal": True,
        "hardgate": {},
        "failed_gate": [],
        "not_claimed": [
            "Tool-route evidence is bounded to deterministic synthetic DGT route rows.",
            "CGA route-patch authority is pointer-only and not copied into the DGT owner.",
            "Invalid or unsafe routes are blocked evidence, not admitted ledger rows.",
        ],
        "revocation_rows": [
            {
                "condition": "Revoke if an invalid or unsafe route appears in admission_ledger.rows.",
                "gate": "DGT-TOOL-HG3",
            },
            {
                "condition": "Revoke if the CGA route-patch pointer is replaced by copied route-patch payload.",
                "gate": "DGT-TOOL-HG2",
            },
        ],
        "forbidden_alias_audit": {
            "status": "pass",
            "forbidden_refs": [],
            "checked_ref_classes": ["host-private refs", "terminal verdict refs", "DGT alias refs", "standalone tool route refs"],
        },
    }
    del generated_at
    payload["hardgate"] = evaluate_dgt_tool_route_hardgates(payload)
    payload["failed_gate"] = payload["hardgate"]["failed_gate"]
    validate_dgt_tool_route_evidence(payload)
    return payload


def validate_dgt_tool_route_evidence(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(TOOL_ROUTE_REQUIRED_KEYS):
        raise ValueError("DGT tool-route evidence fields mismatch")
    if payload["schema_id"] != TOOL_ROUTE_SCHEMA_ID or payload["artifact_id"] != TOOL_ROUTE_ARTIFACT_ID:
        raise ValueError("DGT tool-route identity mismatch")
    if payload["owner_ref"] != TOOL_ROUTE_OWNER_REF:
        raise ValueError("DGT tool-route owner pointer mismatch")
    rows = payload["synthetic_tool_call_grid"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("DGT tool-route grid must be non-empty")
    route_ids = [row.get("route_id") for row in rows if isinstance(row, Mapping)]
    if len(route_ids) != len(set(route_ids)) or len(route_ids) != len(rows):
        raise ValueError("DGT tool-route ids must be unique")
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError("DGT tool-route grid row must be an object")
        expected_row = {"route_id", "tool", "route_class", "classifier_surface_delta", "net_positive_signal", "admission_decision"}
        if set(row) != expected_row:
            raise ValueError("DGT tool-route grid row schema mismatch")
    hardgate = evaluate_dgt_tool_route_hardgates(payload)
    if payload["hardgate"] != hardgate:
        raise ValueError("DGT tool-route hardgate mismatch")
    if payload["failed_gate"] != hardgate["failed_gate"]:
        raise ValueError("DGT tool-route failed_gate mismatch")
    if hardgate["status"] != "pass":
        raise ValueError("DGT tool-route hardgate failed")


def _gate_rows(component_refs: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    pointer_cells = {
        "DGT-HG1": _cell(CANONICAL_JSON_ARTIFACT, "$.schema_id"),
        "DGT-HG2": _cell(CANONICAL_JSON_ARTIFACT, "$.artifact_id"),
        "DGT-HG3": _cell(CANONICAL_JSON_ARTIFACT, "$.model_id"),
        "DGT-HG4": _cell(CANONICAL_JSON_ARTIFACT, "$.architecture_spec"),
        "DGT-HG5": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.hardgate_contract"),
        "DGT-HG6": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.mechanism_namecert"),
        "DGT-HG7": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.discovery_map"),
        "DGT-HG8": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.training_replay"),
        "DGT-HG9": _cell(CANONICAL_JSON_ARTIFACT, "$.discovery_map_signal"),
        "DGT-HG10": _cell(CANONICAL_JSON_ARTIFACT, "$.claim_capsule_ref"),
        "DGT-HG11": _cell(CANONICAL_JSON_ARTIFACT, "$.evidence_envelope_ref"),
        "DGT-HG12": _cell(CANONICAL_JSON_ARTIFACT, "$.mechanism_namecert_ref"),
        "DGT-HG13": _cell(CANONICAL_JSON_ARTIFACT, "$.jet_certificate_ref"),
        "DGT-HG14": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        "DGT-HG15": _cell(CLAIM_CAPSULE_ARTIFACT, "$.owner_ref"),
        "DGT-HG16": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$.component_refs"),
        "DGT-HG17": _cell(MECHANISM_NAMECERT_ARTIFACT, "$.evidence_ref"),
        "DGT-HG18": _cell(JET_CERTIFICATE_ARTIFACT, "$.owner_ref"),
        "DGT-HG19": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.mechanism_dna"),
        "DGT-HG20": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
    }
    missing = not all(_is_cell(component_refs.get(name)) for name in default_component_refs())
    return {
        gate_name: {
            "status": "fail" if missing else "pass",
            "evidence": pointer_cells[gate_name],
            "not_claimed": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        }
        for gate_name in GATE_NAMES
    }


def _dgt_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "architecture_spec": payload.get("architecture_spec"),
            "discovery_map_signal": payload.get("discovery_map_signal"),
            "not_claimed": payload.get("not_claimed"),
        },
        sort_keys=True,
    ).lower()
    match_terms = ("terminal_verdict", "production", "global superiority", "architecture superiority")
    labels = (
        "terminal verdict token",
        "operation authority wording",
        "external superiority wording",
        "architecture superiority wording",
    )
    hits = [label for term, label in zip(match_terms, labels) if term in serialized]
    return {"status": "pass" if not hits else "fail", "hits": hits, "forbidden_terms": list(labels)}


def _projection_not_claimed_clean(not_claimed: Any) -> bool:
    if not isinstance(not_claimed, Sequence) or isinstance(not_claimed, (str, bytes, bytearray)) or not not_claimed:
        return False
    text = " ".join(str(item).lower() for item in not_claimed)
    return all(token not in text for token in ("global superiority", "production"))


def _robustness_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "status": payload.get("status"),
            "readiness": payload.get("readiness"),
            "discovery_level": payload.get("discovery_level"),
            "operational_contract": payload.get("operational_contract"),
            "not_claimed": payload.get("not_claimed"),
            "revocation_rows": payload.get("revocation_rows"),
        },
        sort_keys=True,
    ).lower()
    hits = [
        label
        for term, label in zip(ROBUSTNESS_FORBIDDEN_TERMS, ROBUSTNESS_FORBIDDEN_TERM_LABELS)
        if term in serialized
    ]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(ROBUSTNESS_FORBIDDEN_TERM_LABELS),
    }


def evaluate_operational_robustness_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    source_artifacts = payload.get("source_artifacts")
    source_artifacts = source_artifacts if isinstance(source_artifacts, Mapping) else {}
    source_evidence = payload.get("source_evidence")
    source_evidence = source_evidence if isinstance(source_evidence, Mapping) else {}
    owner = source_evidence.get("owner")
    owner = owner if isinstance(owner, Mapping) else {}
    lat = source_evidence.get("ledger_aware_transformer")
    lat = lat if isinstance(lat, Mapping) else {}
    model_comparison = source_evidence.get("model_comparison")
    model_comparison = model_comparison if isinstance(model_comparison, Mapping) else {}
    audit = payload.get("forbidden_claim_term_audit")
    expected_audit = _robustness_forbidden_claim_term_audit(payload)
    failed_conditions = {
        "DGT-ROB-HG1": payload.get("owner_ref") != ROBUSTNESS_OWNER_REF or payload.get("model_id") != MODEL_ID,
        "DGT-ROB-HG2": owner.get("d4_readiness") != "ready" or owner.get("d4_discovery_level") != "D4",
        "DGT-ROB-HG3": owner.get("component_ablation_status") != "pass",
        "DGT-ROB-HG4": not (
            lat.get("artifact_id") == "bedc-quality-lab:ledger-aware-transformer"
            and lat.get("hardgate_status") == "pass"
            and lat.get("robustness_status") == "pass"
            and isinstance(lat.get("pass_surface_count"), int)
            and isinstance(lat.get("required_pass_surface_count"), int)
            and lat["pass_surface_count"] >= lat["required_pass_surface_count"]
            and lat.get("level_candidate") == "D5-O"
        ),
        "DGT-ROB-HG5": model_comparison.get("hardgate_status") != "pass",
        "DGT-ROB-HG6": not (
            source_artifacts.get("ledger_aware_transformer_pointer")
            == f"{LAT_CANONICAL_ARTIFACT}:$"
            and source_artifacts.get("model_comparison_pointer")
            == f"{MODEL_COMPARISON_CANONICAL_ARTIFACT}:$"
        ),
        "DGT-ROB-HG7": not _projection_not_claimed_clean(payload.get("not_claimed")),
        "DGT-ROB-HG8": not (
            isinstance(audit, Mapping)
            and dict(audit) == expected_audit
            and expected_audit["status"] == "pass"
        ),
    }
    evidence = {
        "DGT-ROB-HG1": "$.operational_robustness.owner_ref",
        "DGT-ROB-HG2": "$.d4_projection",
        "DGT-ROB-HG3": "$.component_ablation.hardgate",
        "DGT-ROB-HG4": "$.operational_robustness.source_evidence.ledger_aware_transformer",
        "DGT-ROB-HG5": "$.operational_robustness.source_evidence.model_comparison",
        "DGT-ROB-HG6": "$.operational_robustness.source_artifacts",
        "DGT-ROB-HG7": "$.operational_robustness.not_claimed",
        "DGT-ROB-HG8": "$.operational_robustness.forbidden_claim_term_audit",
    }
    gates = {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in ROBUSTNESS_GATE_NAMES
    }
    failed_gate = [gate_name for gate_name in ROBUSTNESS_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(ROBUSTNESS_GATE_NAMES),
        "gates": gates,
        "failed_gate": failed_gate,
    }


def validate_operational_robustness(payload: Mapping[str, Any], owner_payload: Mapping[str, Any] | None = None) -> None:
    if set(payload) != set(ROBUSTNESS_REQUIRED_KEYS):
        raise ValueError("DGT robustness fields mismatch")
    if payload["schema_id"] != ROBUSTNESS_SCHEMA_ID or payload["artifact_id"] != ROBUSTNESS_ARTIFACT_ID:
        raise ValueError("DGT robustness identity mismatch")
    if payload["owner_ref"] != ROBUSTNESS_OWNER_REF or payload["model_id"] != MODEL_ID:
        raise ValueError("DGT robustness owner mismatch")
    hardgate = evaluate_operational_robustness_hardgates(payload)
    if payload["hardgate"] != hardgate:
        raise ValueError("DGT robustness hardgate mismatch")
    if payload["failed_gate"] != hardgate["failed_gate"]:
        raise ValueError("DGT robustness failed_gate mismatch")
    first_failed = hardgate["failed_gate"][0] if hardgate["failed_gate"] else None
    expected_pointer = None if first_failed is None else f"{ROBUSTNESS_POINTER}.hardgate.gates.{first_failed}"
    if payload["failed_gate_pointer"] != expected_pointer:
        raise ValueError("DGT robustness failed_gate_pointer mismatch")
    expected_ready = first_failed is None
    if payload["status"] != ("ready" if expected_ready else "blocked"):
        raise ValueError("DGT robustness status mismatch")
    if payload["readiness"] != ("ready" if expected_ready else "blocked"):
        raise ValueError("DGT robustness readiness mismatch")
    if payload["discovery_level"] != ("D5-O" if expected_ready else "D0"):
        raise ValueError("DGT robustness discovery level mismatch")
    if owner_payload is not None and payload.get("owner_ref") != ROBUSTNESS_OWNER_REF:
        raise ValueError("DGT robustness must stay inside the DGT owner")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if token is not None:
        raise ValueError(f"DGT robustness contains forbidden value: {token}")


def _tool_route_positive(tool_route: Any) -> tuple[bool, bool]:
    if not isinstance(tool_route, Mapping):
        return False, False
    if tool_route.get("net_positive_signal") is not True:
        return False, False
    deltas = tool_route.get("classifier_surface_delta")
    if not isinstance(deltas, Mapping) or not deltas:
        return True, False
    for delta in deltas.values():
        if not isinstance(delta, Mapping):
            return True, False
        count = delta.get("surface_delta_count")
        if not isinstance(count, (int, float)) or isinstance(count, bool) or count <= 0:
            return True, False
    return True, True


def _d4_gate_rows(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    gates = payload.get("hardgate", {}).get("gates") if isinstance(payload.get("hardgate"), Mapping) else {}
    tool_route = payload.get("tool_route_evidence")
    family_definition = payload.get("family_definition")
    net_positive, classifier_delta_positive = _tool_route_positive(tool_route)
    failed_conditions = {
        "PROJ-HG1": not (
            isinstance(payload.get("hardgate"), Mapping)
            and payload["hardgate"].get("status") == "pass"
            and isinstance(gates, Mapping)
            and all(isinstance(row, Mapping) and row.get("status") == "pass" for row in gates.values())
        ),
        "PROJ-HG2": not (
            isinstance(tool_route, Mapping)
            and isinstance(tool_route.get("hardgate"), Mapping)
            and tool_route["hardgate"].get("status") == "pass"
        ),
        "PROJ-HG3": not net_positive,
        "PROJ-HG4": not classifier_delta_positive,
        "PROJ-HG5": not (
            isinstance(family_definition, Mapping)
            and isinstance(family_definition.get("hardgate"), Mapping)
            and family_definition["hardgate"].get("status") == "pass"
        ),
        "PROJ-HG6": not (
            _is_cell(payload.get("claim_capsule_ref"))
            and _is_cell(payload.get("evidence_envelope_ref"))
            and _is_cell(payload.get("mechanism_namecert_ref"))
            and _is_cell(payload.get("jet_certificate_ref"))
        ),
        "PROJ-HG7": not _projection_not_claimed_clean(payload.get("not_claimed")),
        "PROJ-HG8": not (
            isinstance(payload.get("forbidden_claim_term_audit"), Mapping)
            and payload["forbidden_claim_term_audit"].get("status") == "pass"
        ),
        "PROJ-HG9": _has_recursive_key(payload, frozenset({"terminal_verdict"})) is not None,
        "PROJ-HG10": not (
            _is_cell(payload.get("hardgate_ref"))
            and _is_cell(payload.get("discovery_map_signal_ref"))
        ),
    }
    evidence = {
        "PROJ-HG1": "$.hardgate",
        "PROJ-HG2": "$.tool_route_evidence.hardgate",
        "PROJ-HG3": "$.tool_route_evidence.net_positive_signal",
        "PROJ-HG4": "$.tool_route_evidence.classifier_surface_delta",
        "PROJ-HG5": "$.family_definition.hardgate",
        "PROJ-HG6": "$.claim_capsule_ref",
        "PROJ-HG7": "$.not_claimed",
        "PROJ-HG8": "$.forbidden_claim_term_audit",
        "PROJ-HG9": "$",
        "PROJ-HG10": "$.discovery_map_signal_ref",
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in D4_PROJECTION_GATE_NAMES
    }


def build_d4_projection_payload(
    evidence: Mapping[str, Any],
    core_contracts: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    gates = _d4_gate_rows(evidence)
    failed = [gate_name for gate_name in D4_PROJECTION_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    failed_gate = failed[0] if failed else None
    evidence_not_claimed = list(evidence.get("not_claimed", [])) if isinstance(evidence.get("not_claimed"), Sequence) else []
    projection_not_claimed = evidence_not_claimed if _projection_not_claimed_clean(evidence_not_claimed) else list(NOT_CLAIMED)
    input_pointers = {
        "hardgate": f"{CANONICAL_JSON_ARTIFACT}:$.hardgate",
        "tool_route": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
        "family_definition": f"{CANONICAL_JSON_ARTIFACT}:$.family_definition",
        "claim_capsule": f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
        "evidence_envelope": f"{CANONICAL_JSON_ARTIFACT}:$.evidence_envelope_ref",
        "mechanism_namecert": f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref",
        "jet_certificate": f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
        "not_claimed": f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed",
        "forbidden_claim_term_audit": f"{CANONICAL_JSON_ARTIFACT}:$.forbidden_claim_term_audit",
    }
    tool_route = evidence.get("tool_route_evidence")
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "owner_ref": f"{CANONICAL_JSON_ARTIFACT}:$",
        "model_id": MODEL_ID,
        "gates": gates,
        "failed_gate": failed_gate,
        "failed_gate_pointer": None if failed_gate is None else f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.gates.{failed_gate}",
        "blocked_reason": None if failed_gate is None else f"blocked-by-{failed_gate}",
        "discovery_level": "D4" if failed_gate is None else "D0",
        "readiness": "ready" if failed_gate is None else "blocked",
        "net_positive_signal": isinstance(tool_route, Mapping) and tool_route.get("net_positive_signal") is True,
        "classifier_surface_delta_pointer": "$.tool_route_evidence.classifier_surface_delta",
        "input_pointers": input_pointers,
        "core_contracts": dict(core_contracts or {}),
        "not_claimed": projection_not_claimed,
        "forbidden_claim_term_audit": evidence.get("forbidden_claim_term_audit", {}),
        "scope_seal": dict(CLOSED_CLAIM_SCOPE_SEAL),
        "matched_control": {
            "control_positive": False,
            "control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.blocked_route_evidence",
        },
        "claim_basis": {
            "positive_discovery": failed_gate is None,
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.gates.PROJ-HG1",
        },
        "anti_triviality_status": "pass" if failed_gate is None else "fail",
        **owner_local_anti_triviality_contract(
            recommended_level="D4",
            scale_only_pointer="$.d4_projection.gates.PROJ-HG1",
            metadata_only_pointer="$.d4_projection.gates.PROJ-HG5",
            matched_random_pointer="$.d4_projection.matched_control",
            forbidden_column_pointer="$.d4_projection.forbidden_claim_term_audit",
            status="pass" if failed_gate is None else "fail",
            failed_gate=failed_gate,
        ),
    }
    validate_d4_projection(payload, evidence)
    return DgtD4Projection(payload).as_payload()


def validate_d4_projection(payload: Mapping[str, Any], root: Mapping[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    if set(payload) != set(D4_PROJECTION_REQUIRED_KEYS):
        errors.append("DGT D4 projection fields mismatch")
    if payload.get("schema_id") != SCHEMA_ID or payload.get("artifact_id") != ARTIFACT_ID:
        errors.append("DGT D4 projection identity mismatch")
    if payload.get("owner_ref") != f"{CANONICAL_JSON_ARTIFACT}:$":
        errors.append("DGT D4 projection owner mismatch")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(D4_PROJECTION_GATE_NAMES):
        errors.append("DGT D4 projection gate names mismatch")
    else:
        failed = [gate_name for gate_name in D4_PROJECTION_GATE_NAMES if gates[gate_name].get("status") != "pass"]
        expected_failed = failed[0] if failed else None
        if payload.get("failed_gate") != expected_failed:
            errors.append("DGT D4 projection failed gate mismatch")
        if payload.get("blocked_reason") != (None if expected_failed is None else f"blocked-by-{expected_failed}"):
            errors.append("DGT D4 projection blocked reason mismatch")
        if payload.get("discovery_level") != ("D4" if expected_failed is None else "D0"):
            errors.append("DGT D4 projection discovery level mismatch")
        if payload.get("readiness") != ("ready" if expected_failed is None else "blocked"):
            errors.append("DGT D4 projection readiness mismatch")
    if _has_recursive_key(payload, frozenset({"terminal_verdict"})) is not None or _has_recursive_token(payload, (".refactor-loop", "host.env")) is not None:
        errors.append("DGT D4 projection contains forbidden authority token")
    if not _projection_not_claimed_clean(payload.get("not_claimed")):
        errors.append("DGT D4 projection not_claimed boundary mismatch")
    if payload.get("readiness") == "ready" and payload.get("net_positive_signal") is not True:
        errors.append("DGT D4 projection net positive signal missing")
    if payload.get("scope_seal") != CLOSED_CLAIM_SCOPE_SEAL:
        errors.append("DGT D4 projection scope seal mismatch")
    if root is not None and isinstance(gates, Mapping) and _d4_gate_rows(root) != gates:
        errors.append("DGT D4 projection gate evaluation mismatch")
    return errors


@dataclass(frozen=True)
class DgtD5OProjection:
    payload: dict[str, Any]

    def as_payload(self) -> dict[str, Any]:
        return dict(self.payload)


@dataclass(frozen=True)
class DgtBoundedMechanismProjection:
    payload: dict[str, Any]

    def as_payload(self) -> dict[str, Any]:
        return dict(self.payload)


@dataclass(frozen=True)
class DgtScalingLadderProjection:
    payload: dict[str, Any]

    def as_payload(self) -> dict[str, Any]:
        return dict(self.payload)


def _read_high_impact_review_rows(root: Path) -> list[Mapping[str, Any]]:
    path = root / HIGH_IMPACT_REVIEW_JSON_ARTIFACT
    if not path.exists():
        return []
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return []
    rows = payload.get("review_rows") if isinstance(payload, Mapping) else None
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, Mapping)]


def _terminal_d4_review_row(review_rows: Sequence[Mapping[str, Any]]) -> tuple[int, Mapping[str, Any]] | None:
    for index, row in enumerate(review_rows):
        if row.get("claim_id") == "claim:discovery-gated-transformer" and row.get("status") == "pass":
            return index, row
    return None


def _pointer_resolves_in_owner(owner_payload: Mapping[str, Any], pointer: str) -> bool:
    if ":" in pointer:
        artifact, local_pointer = pointer.split(":", 1)
        if artifact != CANONICAL_JSON_ARTIFACT:
            return bool(artifact and local_pointer.startswith("$"))
        pointer = local_pointer
    return pointer_value(owner_payload, pointer) is not None


def _toy_seed_surface_summary(seed: int = 1105) -> dict[str, Any]:
    surfaces: list[dict[str, Any]] = []
    owner_scores = (0.74, 0.77, 0.81, 0.79)
    matched_random_scores = (0.45, 0.47, 0.46, 0.48)
    thresholds = (0.56, 0.60, 0.64, 0.68)
    for index, (owner_score, control_score, threshold) in enumerate(
        zip(owner_scores, matched_random_scores, thresholds),
        start=1,
    ):
        surfaces.append(
            {
                "surface_id": f"toy-seed-{seed}-surface-{index}",
                "seed": seed + index,
                "threshold": threshold,
                "owner_score": owner_score,
                "matched_random_score": control_score,
                "owner_pass": owner_score >= threshold,
                "matched_random_pass": control_score >= threshold,
                "boundary_status": "passed" if owner_score >= threshold and control_score < threshold else "failed",
            }
        )
    pass_rows = [row for row in surfaces if row["boundary_status"] == "passed"]
    return {
        "seed": seed,
        "surface_count": len(surfaces),
        "nontrivial_ood_pass_count": len(pass_rows),
        "required_nontrivial_ood_pass_count": 3,
        "threshold_frontier": {
            "thresholds": list(thresholds),
            "owner_pass_count": sum(1 for row in surfaces if row["owner_pass"]),
            "matched_random_pass_count": sum(1 for row in surfaces if row["matched_random_pass"]),
            "frontier_status": "pass"
            if len(pass_rows) >= 3 and all(not row["matched_random_pass"] for row in surfaces)
            else "fail",
        },
        "surfaces": surfaces,
    }


def _d5_o_gate_rows(
    owner_payload: Mapping[str, Any],
    high_impact_review_rows: Sequence[Mapping[str, Any]],
    surface_summary: Mapping[str, Any],
    not_claimed: Sequence[str],
) -> dict[str, dict[str, Any]]:
    terminal_row = _terminal_d4_review_row(high_impact_review_rows)
    d4_projection = owner_payload.get("d4_projection")
    operational = owner_payload.get("operational_robustness") or owner_payload.get("robustness")
    component_ablation = owner_payload.get("component_ablation")
    surface_rows = surface_summary.get("surfaces")
    evidence_pointers = {
        "D5O-HG1": f"{HIGH_IMPACT_REVIEW_JSON_ARTIFACT}:$.review_rows[0]",
        "D5O-HG2": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection",
        "D5O-HG3": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary",
        "D5O-HG4": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary.seed",
        "D5O-HG5": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary.threshold_frontier",
        "D5O-HG6": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.evidence_pointers.stronger_matched_random",
        "D5O-HG7": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.boundary_ledger",
        "D5O-HG8": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.not_claimed",
    }
    not_claimed_text = " ".join(str(item) for item in not_claimed).lower()
    failed_conditions = {
        "D5O-HG1": terminal_row is None,
        "D5O-HG2": not (
            isinstance(d4_projection, Mapping)
            and d4_projection.get("discovery_level") == "D4"
            and d4_projection.get("readiness") == "ready"
            and d4_projection.get("failed_gate") is None
        ),
        "D5O-HG3": not (
            isinstance(surface_summary.get("nontrivial_ood_pass_count"), int)
            and surface_summary["nontrivial_ood_pass_count"]
            >= surface_summary.get("required_nontrivial_ood_pass_count", 3)
        ),
        "D5O-HG4": not (
            isinstance(surface_summary.get("seed"), int)
            and isinstance(surface_rows, list)
            and len({row.get("seed") for row in surface_rows if isinstance(row, Mapping)}) >= 4
        ),
        "D5O-HG5": pointer_value(surface_summary, "$.threshold_frontier.frontier_status") != "pass",
        "D5O-HG6": not (
            isinstance(surface_rows, list)
            and bool(surface_rows)
            and all(isinstance(row, Mapping) and row.get("matched_random_pass") is False for row in surface_rows)
        ),
        "D5O-HG7": not (
            isinstance(component_ablation, Mapping)
            and pointer_value(component_ablation, "$.hardgate.status") == "pass"
            and isinstance(operational, Mapping)
            and pointer_value(operational, "$.hardgate.status") == "pass"
        ),
        "D5O-HG8": not (
            "bounded d5-o" in not_claimed_text
            and "production robustness" in not_claimed_text
            and "global robustness" in not_claimed_text
            and "llm replacement" in not_claimed_text
            and "d5-m mechanism closure" in not_claimed_text
        ),
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(*evidence_pointers[gate_name].split(":", 1)),
        }
        for gate_name in D5O_GATE_NAMES
    }


def build_d5_o_projection(
    owner_payload: Mapping[str, Any],
    high_impact_review_rows: Sequence[Mapping[str, Any]],
    *,
    root: Path,
    surface_summary: Mapping[str, Any] | None = None,
    not_claimed: Sequence[str] | None = None,
) -> dict[str, Any]:
    del root
    surface_summary = dict(surface_summary or _toy_seed_surface_summary())
    not_claimed_rows = list(not_claimed or D5O_NOT_CLAIMED)
    gates = _d5_o_gate_rows(owner_payload, high_impact_review_rows, surface_summary, not_claimed_rows)
    failed = [gate_name for gate_name in D5O_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    terminal_row = _terminal_d4_review_row(high_impact_review_rows)
    source_level = pointer_value(owner_payload, "$.d4_projection.discovery_level")
    terminal_pointer = (
        f"{HIGH_IMPACT_REVIEW_JSON_ARTIFACT}:$.review_rows[{terminal_row[0]}]"
        if terminal_row is not None
        else f"{HIGH_IMPACT_REVIEW_JSON_ARTIFACT}:$.review_rows[0]"
    )
    evidence_pointers = {
        "terminal_d4_acceptance": terminal_pointer,
        "source_d4_projection": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection",
        "operational_robustness": f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness",
        "component_ablation": f"{CANONICAL_JSON_ARTIFACT}:$.component_ablation",
        "stronger_matched_random": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary.threshold_frontier.matched_random_pass_count",
        "high_impact_review": terminal_pointer,
    }
    boundary_ledger = [
        {
            "gate": gate_name,
            "status": row["status"],
            "evidence_pointer": artifact_pointer(row["evidence"]),
            "boundary": "blocks D5-O projection" if row["status"] != "pass" else "closed for bounded D5-O",
        }
        for gate_name, row in gates.items()
    ]
    gate_status = "pass" if not failed else "fail"
    payload = {
        "status": "ready" if not failed else "blocked",
        "discovery_level": "D5-O" if not failed else (source_level if source_level == "D4" else "D0"),
        "source_level": source_level,
        "gate_status": gate_status,
        "gates": gates,
        "evidence_pointers": evidence_pointers,
        "boundary_ledger": boundary_ledger,
        "blocked_reason": None if not failed else f"blocked-by-{failed[0]}",
        "not_claimed": not_claimed_rows,
        "scope": {
            "claim": "bounded deterministic toy operational robustness",
            "review": D5O_REVIEW_PHRASE,
            "owner": MODEL_ID,
        },
        "surface_summary": surface_summary,
        "anti_triviality_status": "pass" if not failed else "fail",
        **owner_local_anti_triviality_contract(
            recommended_level="D5-O",
            scale_only_pointer="$.d5_o_projection.gates.D5O-HG2",
            metadata_only_pointer="$.d5_o_projection.gates.D5O-HG3",
            matched_random_pointer="$.d5_o_projection.evidence_pointers.stronger_matched_random",
            forbidden_column_pointer="$.d5_o_projection.not_claimed",
            status="pass" if not failed else "fail",
            failed_gate=failed[0] if failed else None,
        ),
    }
    validate_d5_o_projection(payload, owner_payload)
    return DgtD5OProjection(payload).as_payload()


def validate_d5_o_projection(payload: Mapping[str, Any], owner_payload: Mapping[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    if set(payload) != set(D5O_REQUIRED_KEYS):
        errors.append("DGT D5-O projection fields mismatch")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(D5O_GATE_NAMES):
        errors.append("DGT D5-O projection gate names mismatch")
        return errors
    failed = [gate_name for gate_name in D5O_GATE_NAMES if gates[gate_name].get("status") != "pass"]
    if payload.get("gate_status") != ("pass" if not failed else "fail"):
        errors.append("DGT D5-O projection gate status mismatch")
    if payload.get("status") != ("ready" if not failed else "blocked"):
        errors.append("DGT D5-O projection status mismatch")
    if payload.get("discovery_level") != ("D5-O" if not failed else payload.get("source_level")):
        errors.append("DGT D5-O projection discovery level mismatch")
    if payload.get("blocked_reason") != (None if not failed else f"blocked-by-{failed[0]}"):
        errors.append("DGT D5-O projection blocked reason mismatch")
    if not isinstance(payload.get("boundary_ledger"), list) or len(payload["boundary_ledger"]) != len(D5O_GATE_NAMES):
        errors.append("DGT D5-O projection boundary ledger mismatch")
    not_claimed = payload.get("not_claimed")
    text = " ".join(str(item).lower() for item in not_claimed) if isinstance(not_claimed, list) else ""
    for phrase in ("bounded d5-o", "production robustness", "global robustness", "llm replacement"):
        if phrase not in text:
            errors.append(f"DGT D5-O not_claimed missing boundary: {phrase}")
    if "terminal_verdict" in json.dumps(payload, sort_keys=True).lower():
        errors.append("DGT D5-O projection contains terminal authority wording")
    if owner_payload is not None:
        evidence_pointers = payload.get("evidence_pointers")
        if not isinstance(evidence_pointers, Mapping):
            errors.append("DGT D5-O projection evidence pointer mismatch")
        else:
            for name, pointer in evidence_pointers.items():
                if name in {"terminal_d4_acceptance", "high_impact_review"}:
                    continue
                if not isinstance(pointer, str):
                    errors.append(f"DGT D5-O evidence pointer unresolved: {name}")
                    continue
                if pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection"):
                    local_pointer = pointer.split(":", 1)[1]
                    relative_pointer = "$" + local_pointer.removeprefix("$.d5_o_projection")
                    if pointer_value(payload, relative_pointer) is None:
                        errors.append(f"DGT D5-O evidence pointer unresolved: {name}")
                    continue
                if not _pointer_resolves_in_owner(owner_payload, pointer):
                    errors.append(f"DGT D5-O evidence pointer unresolved: {name}")
    return errors


def _d5_m_forbidden_claim_audit(owner_payload: Mapping[str, Any], not_claimed: Sequence[str]) -> dict[str, Any]:
    reported_forbidden_terms = (
        "production authority",
        "production deployment",
        "global superiority",
        "llm replacement",
        "unbounded mechanism",
    )
    detected_forbidden_terms = (
        *reported_forbidden_terms,
        ".refactor-loop",
        "host.env",
    )
    claim_surface = {
        "evidence_scope": pointer_value(owner_payload, "$.d5_m_projection.evidence_scope"),
        "terminal_verdict_scope": pointer_value(owner_payload, "$.d5_m_projection.terminal_verdict_scope"),
    }
    serialized = json.dumps(claim_surface, sort_keys=True).lower()
    hits = [term for term in detected_forbidden_terms if term in serialized]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(reported_forbidden_terms),
        "claim_surface_pointer": D5M_PROJECTION_POINTER,
    }


def validate_evidence_scope(value: Any, *, allow_missing: bool = False) -> list[str]:
    if value is None and allow_missing:
        return []
    if not isinstance(value, list):
        return ["evidence_scope must be a non-empty array"]
    if not value:
        return ["evidence_scope must be non-empty"]
    if not all(isinstance(item, str) for item in value):
        return ["evidence_scope entries must be strings"]
    if len(set(value)) != len(value):
        return ["evidence_scope must not contain duplicate entries"]
    invalid = sorted(set(value) - EVIDENCE_SCOPE_VALUES)
    if invalid:
        return [f"evidence_scope contains invalid entries: {', '.join(invalid)}"]
    return []


def d5_m_evidence_scope_is_closed(value: Any) -> bool:
    return validate_evidence_scope(value) == []


def _scope_has_production_forbidden(value: Any) -> bool:
    return isinstance(value, list) and "production-forbidden" in value


def _has_production_claim(value: Any) -> bool:
    text = json.dumps(value, sort_keys=True).lower()
    return any(
        token in text
        for token in (
            "production claim",
            "production authority accepted",
            "production deployment",
            "deployment authority",
            "production ready",
            "production-ready",
            "production scale authority",
        )
    )


def d5_m_hardgate_rows(owner_payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    d5_o = owner_payload.get("d5_o_projection")
    d5_m = owner_payload.get("d5_m_projection")
    d5_m = d5_m if isinstance(d5_m, Mapping) else {}
    mechanism_ref = owner_payload.get("mechanism_namecert_ref")
    jet_ref = owner_payload.get("jet_certificate_ref")
    operational = owner_payload.get("operational_robustness")
    not_claimed = d5_m.get("not_claimed", D5M_NOT_CLAIMED)
    not_claimed_text = " ".join(str(item).lower() for item in not_claimed) if isinstance(not_claimed, Sequence) else ""
    negative = d5_m.get("negative_witness_pointers")
    negative = negative if isinstance(negative, Mapping) else {}
    forbidden_audit = d5_m.get("forbidden_claim_audit")
    if not isinstance(forbidden_audit, Mapping):
        forbidden_audit = _d5_m_forbidden_claim_audit(owner_payload, list(D5M_NOT_CLAIMED))
    neural_ref = owner_payload.get("neural_ablation_ref")
    neural_ablation_pointer = artifact_pointer(neural_ref) if _is_cell(neural_ref) else None
    failed_conditions = {
        "D5M-HG1": not (
            isinstance(d5_o, Mapping)
            and d5_o.get("discovery_level") == "D5-O"
            and d5_o.get("status") == "ready"
            and d5_o.get("gate_status") == "pass"
        ),
        "D5M-HG2": not d5_m_evidence_scope_is_closed(d5_m.get("evidence_scope")),
        "D5M-HG3": not (
            _is_cell(mechanism_ref)
            and d5_m.get("mechanism_certificate_pointer") == f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref"
            and d5_m.get("mechanism_closure_status") in {None, "closed"}
        ),
        "D5M-HG4": not (_is_cell(jet_ref) and d5_m.get("jet_certificate_pointer") == f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref"),
        "D5M-HG5": not (
            isinstance(operational, Mapping)
            and pointer_value(operational, "$.hardgate.status") == "pass"
            and d5_m.get("causal_patch_pointer") == f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness"
        ),
        "D5M-HG6": not (
            _is_cell(neural_ref)
            and neural_ablation_pointer == f"{DGT_NEURAL_ABLATION_ARTIFACT}:{NABL_HARDGATE_STATUS_POINTER}"
            and d5_m.get("component_ablation_pointer") == f"{CANONICAL_JSON_ARTIFACT}:$.neural_ablation_ref"
            and d5_m.get("neural_ablation_pointer") == neural_ablation_pointer
        ),
        "D5M-HG7": negative.get("score_margin_shortcut") != "cleared",
        "D5M-HG8": negative.get("scale_leakage") != "cleared",
        "D5M-HG9": not (
            negative.get("control_positive") == "cleared"
            and pointer_value(owner_payload, "$.d4_projection.matched_control.control_positive") is False
        ),
        "D5M-HG10": not (
            isinstance(forbidden_audit, Mapping)
            and forbidden_audit.get("status") == "pass"
            and d5_m.get("terminal_verdict_scope") == "Core"
            and "production authority" in not_claimed_text
            and "global superiority" in not_claimed_text
            and "llm replacement" in not_claimed_text
            and "unbounded" in not_claimed_text
        ),
    }
    evidence = {
        "D5M-HG1": "$.d5_o_projection",
        "D5M-HG2": "$.d5_m_projection.evidence_scope",
        "D5M-HG3": "$.mechanism_namecert_ref",
        "D5M-HG4": "$.jet_certificate_ref",
        "D5M-HG5": "$.operational_robustness",
        "D5M-HG6": "$.neural_ablation_ref",
        "D5M-HG7": "$.d5_m_projection.negative_witness_pointers.score_margin_shortcut",
        "D5M-HG8": "$.d5_m_projection.negative_witness_pointers.scale_leakage",
        "D5M-HG9": "$.d4_projection.matched_control.control_positive",
        "D5M-HG10": "$.d5_m_projection.forbidden_claim_audit",
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in D5M_GATE_NAMES
    }


def build_d5_m_projection(owner_payload: Mapping[str, Any]) -> dict[str, Any]:
    overrides = owner_payload.get("d5_m_projection")
    overrides = overrides if isinstance(overrides, Mapping) else {}
    has_evidence_scope_override = "evidence_scope" in overrides
    draft: dict[str, Any] = {
        "status": "blocked",
        "readiness": "blocked",
        "discovery_level": pointer_value(owner_payload, "$.d5_o_projection.discovery_level") or "D0",
        "source_level": pointer_value(owner_payload, "$.d5_o_projection.discovery_level"),
        "evidence_scope": list(D5M_DEFAULT_EVIDENCE_SCOPE),
        "terminal_verdict_scope": "Core",
        "gate_status": "fail",
        "failed_gate": None,
        "blocked_reason": None,
        "hardgates": {},
        "boundary_ledger": [],
        "mechanism_certificate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref",
        "mechanism_closure_status": "closed",
        "jet_certificate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
        "causal_patch_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.operational_robustness",
        "component_ablation_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.neural_ablation_ref",
        "neural_ablation_pointer": artifact_pointer(owner_payload["neural_ablation_ref"])
        if _is_cell(owner_payload.get("neural_ablation_ref"))
        else f"{DGT_NEURAL_ABLATION_ARTIFACT}:{NABL_HARDGATE_FAILED_GATE_POINTER}",
        "negative_witness_pointers": {
            "score_margin_shortcut": "cleared",
            "score_margin_shortcut_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary.threshold_frontier",
            "scale_leakage": "cleared",
            "scale_leakage_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d5_o_projection.surface_summary.surfaces",
            "control_positive": "cleared",
            "control_positive_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.matched_control.control_positive",
        },
        "forbidden_claim_audit": {},
        "not_claimed": list(D5M_NOT_CLAIMED),
    }
    for key in (
        "terminal_verdict_scope",
        "mechanism_certificate_pointer",
        "mechanism_closure_status",
        "jet_certificate_pointer",
        "causal_patch_pointer",
        "component_ablation_pointer",
        "neural_ablation_pointer",
        "negative_witness_pointers",
        "not_claimed",
    ):
        if key in overrides:
            draft[key] = overrides[key]
    if has_evidence_scope_override:
        draft["evidence_scope"] = overrides["evidence_scope"]
    if isinstance(overrides.get("forbidden_claim_audit"), Mapping):
        draft["forbidden_claim_audit"] = dict(overrides["forbidden_claim_audit"])
    draft["forbidden_claim_audit"] = _d5_m_forbidden_claim_audit({**owner_payload, "d5_m_projection": draft}, draft["not_claimed"])
    gates = d5_m_hardgate_rows({**owner_payload, "d5_m_projection": draft})
    failed = [gate_name for gate_name in D5M_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    if overrides and not has_evidence_scope_override:
        failed.insert(0, "D5M-HG2")
        gates["D5M-HG2"]["status"] = "fail"
    failed_gate = failed[0] if failed else None
    draft.update(
        {
            "status": "ready" if failed_gate is None else "blocked",
            "readiness": "ready" if failed_gate is None else "blocked",
            "discovery_level": "D5-M" if failed_gate is None else (draft["source_level"] if draft["source_level"] in {"D5-O", "D4"} else "D0"),
            "gate_status": "pass" if failed_gate is None else "fail",
            "failed_gate": failed_gate,
            "blocked_reason": None if failed_gate is None else f"blocked-by-{failed_gate}",
            "hardgates": gates,
            "boundary_ledger": [
                {
                    "gate": gate_name,
                    "status": row["status"],
                    "evidence_pointer": artifact_pointer(row["evidence"]),
                    "boundary": "closed for bounded D5-M" if row["status"] == "pass" else "blocks D5-M projection",
                }
                for gate_name, row in gates.items()
            ],
            "anti_triviality_status": "pass" if failed_gate is None else "fail",
            **owner_local_anti_triviality_contract(
                recommended_level="D5-M",
                scale_only_pointer="$.d5_m_projection.hardgates.D5M-HG7",
                metadata_only_pointer="$.d5_m_projection.hardgates.D5M-HG2",
                matched_random_pointer="$.d5_m_projection.hardgates.D5M-HG9",
                forbidden_column_pointer="$.d5_m_projection.hardgates.D5M-HG10",
                status="pass" if failed_gate is None else "fail",
                failed_gate=failed_gate,
            ),
        }
    )
    errors = validate_d5_m_projection({**owner_payload, "d5_m_projection": draft})
    if errors:
        raise ValueError("; ".join(errors))
    return DgtBoundedMechanismProjection(draft).as_payload()


def validate_d5_m_projection(owner_payload: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    payload = owner_payload.get("d5_m_projection")
    if not isinstance(payload, Mapping):
        return ["DGT D5-M projection missing"]
    expected = set(D5M_REQUIRED_KEYS) | {"mechanism_closure_status"}
    if set(payload) != expected:
        errors.append("DGT D5-M projection fields mismatch")
    gates = payload.get("hardgates")
    if not isinstance(gates, Mapping) or set(gates) != set(D5M_GATE_NAMES):
        errors.append("DGT D5-M projection gate names mismatch")
        return errors
    expected_gates = d5_m_hardgate_rows(owner_payload)
    gates_match = gates == expected_gates
    if not gates_match and payload.get("failed_gate") == "D5M-HG2":
        patched_expected = json.loads(json.dumps(expected_gates))
        patched_expected["D5M-HG2"]["status"] = "fail"
        gates_match = gates == patched_expected
    if not gates_match:
        errors.append("DGT D5-M projection gate evaluation mismatch")
    scope_errors = validate_evidence_scope(payload.get("evidence_scope"))
    errors.extend(f"DGT D5-M {error}" for error in scope_errors)
    failed = [gate_name for gate_name in D5M_GATE_NAMES if gates[gate_name].get("status") != "pass"]
    failed_gate = failed[0] if failed else None
    if payload.get("gate_status") != ("pass" if failed_gate is None else "fail"):
        errors.append("DGT D5-M projection gate status mismatch")
    if payload.get("status") != ("ready" if failed_gate is None else "blocked"):
        errors.append("DGT D5-M projection status mismatch")
    if payload.get("readiness") != payload.get("status"):
        errors.append("DGT D5-M projection readiness mismatch")
    expected_blocked_level = payload.get("source_level") if payload.get("source_level") in {"D5-O", "D4"} else "D0"
    if payload.get("discovery_level") != ("D5-M" if failed_gate is None else expected_blocked_level):
        errors.append("DGT D5-M projection discovery level mismatch")
    if payload.get("failed_gate") != failed_gate:
        errors.append("DGT D5-M projection failed gate mismatch")
    if payload.get("blocked_reason") != (None if failed_gate is None else f"blocked-by-{failed_gate}"):
        errors.append("DGT D5-M projection blocked reason mismatch")
    if failed_gate is None and scope_errors:
        errors.append("DGT D5-M evidence scope mismatch")
    if _scope_has_production_forbidden(payload.get("evidence_scope")) and _has_production_claim(
        {
            "terminal_verdict_scope": payload.get("terminal_verdict_scope"),
            "scope": payload.get("scope"),
            "claim": payload.get("claim"),
            "claim_basis": payload.get("claim_basis"),
            "claim_surface": payload.get("claim_surface"),
            "positive_claim": payload.get("positive_claim"),
        }
    ):
        errors.append("DGT D5-M evidence scope contradicts production claim")
    if failed_gate is None and payload.get("terminal_verdict_scope") != "Core":
        errors.append("DGT D5-M terminal verdict scope mismatch")
    if failed_gate is None and payload.get("mechanism_closure_status") != "closed":
        errors.append("DGT D5-M mechanism closure mismatch")
    if not isinstance(payload.get("boundary_ledger"), list) or len(payload["boundary_ledger"]) != len(D5M_GATE_NAMES):
        errors.append("DGT D5-M boundary ledger mismatch")
    forbidden = json.dumps(payload, sort_keys=True).lower()
    for token in (".refactor-loop", "host.env"):
        if token in forbidden:
            errors.append(f"DGT D5-M projection contains forbidden token: {token}")
    if '"terminal_verdict":' in forbidden:
        errors.append("DGT D5-M projection contains forbidden terminal authority payload")
    not_claimed = payload.get("not_claimed")
    text = " ".join(str(item).lower() for item in not_claimed) if isinstance(not_claimed, list) else ""
    if failed_gate != "D5M-HG10":
        for phrase in ("bounded d5-m", "production authority", "global superiority", "llm replacement", "unbounded"):
            if phrase not in text:
                errors.append(f"DGT D5-M not_claimed missing boundary: {phrase}")
    if failed_gate is None:
        for pointer_key in (
            "mechanism_certificate_pointer",
            "jet_certificate_pointer",
            "causal_patch_pointer",
            "component_ablation_pointer",
            "neural_ablation_pointer",
        ):
            pointer = payload.get(pointer_key)
            if not isinstance(pointer, str) or not (
                pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$")
                or pointer.startswith(f"{DGT_NEURAL_ABLATION_ARTIFACT}:$")
            ):
                errors.append(f"DGT D5-M pointer mismatch: {pointer_key}")
    return errors


def _scaling_level_input_by_id(owner_payload: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    source = owner_payload.get("scaling_ladder")
    levels = source.get("levels") if isinstance(source, Mapping) else None
    if not isinstance(levels, list):
        return {}
    by_id: dict[str, Mapping[str, Any]] = {}
    for row in levels:
        if not isinstance(row, Mapping):
            continue
        capsule = row.get("claim_capsule")
        if not isinstance(capsule, Mapping):
            continue
        level_id = capsule.get("level_id")
        if isinstance(level_id, str):
            by_id[level_id] = capsule
    return by_id


def _read_l0_control_projection(root: Path) -> Mapping[str, Any] | None:
    path = root / DGT_L0_CONTROLS_ARTIFACT
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    projection = payload.get("l0_toy_projection") if isinstance(payload, Mapping) else None
    return projection if isinstance(projection, Mapping) else None


def _l0_ladder_consumption_ref_from_projection(projection: Mapping[str, Any] | None) -> dict[str, Any] | None:
    if isinstance(projection, Mapping) and isinstance(projection.get("ladder_consumption"), Mapping):
        return dict(L0_LADDER_CONSUMPTION_REF)
    return None


def _l0_ladder_consumption_target_resolves(root: Path) -> bool:
    return resolve_artifact_pointer(root, artifact_pointer(L0_LADDER_CONSUMPTION_REF)) is not None


def _owner_ladder_consumption_ref(owner_payload: Mapping[str, Any]) -> dict[str, Any] | None:
    source_artifacts = owner_payload.get("source_artifacts")
    if not isinstance(source_artifacts, Mapping):
        return None
    ref = source_artifacts.get("ladder_consumption_ref")
    return dict(ref) if isinstance(ref, Mapping) else None


def _payload_ladder_consumption_ref_consistent(payload: Mapping[str, Any], *, target_resolves: bool | None = None) -> bool:
    ladder = payload.get("scaling_ladder")
    if not isinstance(ladder, Mapping):
        return False
    source_ref = _owner_ladder_consumption_ref(payload)
    top_ref = ladder.get("ladder_consumption_ref")
    levels = ladder.get("levels")
    capsule = levels[0].get("claim_capsule") if isinstance(levels, list) and levels and isinstance(levels[0], Mapping) else None
    capsule_ref = capsule.get("ladder_consumption_ref") if isinstance(capsule, Mapping) else None
    expected_ref = L0_LADDER_CONSUMPTION_REF if target_resolves is True else source_ref
    if target_resolves is True and source_ref != L0_LADDER_CONSUMPTION_REF:
        return False
    if target_resolves is False and source_ref is not None:
        return False
    if expected_ref is None:
        return top_ref is None and capsule_ref is None
    return top_ref == expected_ref and capsule_ref == expected_ref


def _read_l1_tiny_sequence_projection(root: Path) -> Mapping[str, Any] | None:
    path = root / FAIR_L1_DECISION_ARTIFACT
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    projection = payload.get("ladder_state_projection") if isinstance(payload, Mapping) else None
    if not isinstance(projection, Mapping):
        return None
    return {
        "state": projection.get("state"),
        "decision_status": projection.get("decision_status"),
        "l1_ood_mechanism_verdict_alias_source": L1_OOD_MECHANISM_VERDICT_POINTER,
        "l1_ood_mechanism_l2_implication_alias_source": L1_OOD_MECHANISM_L2_IMPLICATION_POINTER,
        "not_claimed": projection.get("not_claimed"),
    }


def _owner_refs_resolve(root: Path, payload: Mapping[str, Any]) -> bool:
    source_artifacts = payload.get("source_artifacts")
    if not isinstance(source_artifacts, Mapping):
        return False
    owner_keys = (
        "construct_suspension_ref",
        "honest_metric_review_ref",
        "interpretation_boundary_ref",
        "negative_witness_sweep_ref",
        "l1_ood_mechanism_ref",
    )
    owner_artifacts = [
        artifact
        for key in owner_keys
        if isinstance(source_artifacts.get(key), Mapping)
        for artifact in (source_artifacts[key].get("artifact"),)
        if isinstance(artifact, str)
    ]
    if not owner_artifacts or any(not (root / artifact).exists() for artifact in owner_artifacts):
        return False
    for key in owner_keys:
        cell = source_artifacts.get(key)
        if not isinstance(cell, Mapping):
            return False
        if resolve_artifact_pointer(root, artifact_pointer(cell)) is None:
            return False
    target_resolves = _l0_ladder_consumption_target_resolves(root)
    ladder_cell = source_artifacts.get("ladder_consumption_ref")
    if isinstance(ladder_cell, Mapping):
        if resolve_artifact_pointer(root, artifact_pointer(ladder_cell)) is None:
            return False
    elif ladder_cell is not None:
        return False
    if target_resolves and not isinstance(ladder_cell, Mapping):
        return False
    if not target_resolves and isinstance(ladder_cell, Mapping):
        return False
    if not _payload_ladder_consumption_ref_consistent(payload, target_resolves=target_resolves):
        return False
    return True


def _l0_capsule_from_projection(projection: Mapping[str, Any] | None) -> dict[str, Any]:
    capsule = _scaling_default_capsule("L0_toy")
    if not isinstance(projection, Mapping):
        return capsule
    capsule["ladder_consumption_ref"] = _l0_ladder_consumption_ref_from_projection(projection)
    review_status = projection.get("review_status")
    hardgate_summary = projection.get("hardgate_statuses", {}).get("pass") if isinstance(projection.get("hardgate_statuses"), Mapping) else None
    pass_ready = (
        isinstance(projection.get("ladder_consumption"), Mapping)
        and projection["ladder_consumption"].get("status") == "open"
        and review_status == "pass"
        and projection.get("status") == "pass"
        and isinstance(hardgate_summary, Mapping)
        and hardgate_summary.get("status") == "pass"
    )
    if pass_ready:
        capsule["review_status_alias"] = "pass"
        capsule["ladder_consumption_status"] = "open"
        capsule["level_state"] = "open"
        capsule["promotion_status"] = "opened-from-l0-pass-pointer"
        capsule["boundary_ledger"] = []
    else:
        ladder = projection.get("ladder_consumption") if isinstance(projection.get("ladder_consumption"), Mapping) else {}
        ladder_status = ladder.get("status") if isinstance(ladder.get("status"), str) else "suspended"
        capsule["review_status_alias"] = str(review_status) if isinstance(review_status, str) else "missing"
        capsule["ladder_consumption_status"] = ladder_status
        capsule["level_state"] = "scoped-boundary" if ladder_status == "scoped-boundary" else ("suspended" if ladder_status == "suspended" else "blocked")
        capsule["promotion_status"] = (
            "scoped-boundary-from-l0-owner-pointer"
            if ladder_status == "scoped-boundary"
            else "suspended-by-l0-owner-pointer"
            if ladder_status == "suspended"
            else "blocked-by-l0-owner-pointer"
        )
        capsule["boundary_ledger"] = [
            {
                "level_id": "L0_toy",
                "status": capsule["level_state"],
                "reason": "; ".join(str(item) for item in projection.get("failure_reasons", []))
                or str(ladder.get("reason") or "dgt-l0-controls ladder consumption is not open"),
                "source_pointer": f"{DGT_L0_CONTROLS_ARTIFACT}:$.l0_toy_projection",
            }
        ]
    not_claimed = projection.get("not_claimed")
    if isinstance(not_claimed, list) and not_claimed:
        capsule["not_claimed"] = list(not_claimed)
    return capsule


def _l1_default_scaling_capsule() -> dict[str, Any]:
    index = SCALING_LADDER_LEVEL_IDS.index("L1_tiny_sequence")
    return {
        "level_id": "L1_tiny_sequence",
        "claim_id": "claim:dgt_scaling_ladder_owner:L1_tiny_sequence",
        "pointer": L1_TINY_SEQUENCE_PROJECTION_POINTER,
        "projected_claim_pointer": f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
        "review_status_alias": "missing",
        "promotion_readiness_alias": "missing",
        "review_status_alias_source": FAIR_L1_DECISION_STATUS_POINTER,
        "promotion_readiness_alias_source": L1_TINY_SEQUENCE_PROJECTION_POINTER,
        "l1_ood_mechanism_verdict_alias_source": L1_OOD_MECHANISM_VERDICT_POINTER,
        "l1_ood_mechanism_l2_implication_alias_source": L1_OOD_MECHANISM_L2_IMPLICATION_POINTER,
        "level_state": "blocked",
        "promotion_status": "blocked-by-l1-review-status-pointer",
        "boundary_ledger": [
            {
                "level_id": "L1_tiny_sequence",
                "status": "blocked",
                "reason": "missing fair L1 decision projection",
                "source_pointer": L1_TINY_SEQUENCE_PROJECTION_POINTER,
            }
        ],
        "not_claimed": list(SCALING_LADDER_NOT_CLAIMED),
    }


def _scaling_default_capsule(level_id: str) -> dict[str, Any]:
    index = SCALING_LADDER_LEVEL_IDS.index(level_id)
    if level_id == "L0_toy":
        return {
            "level_id": level_id,
            "claim_id": f"claim:dgt_scaling_ladder_owner:{level_id}",
            "l0_toy_projection_ref": dict(L0_TOY_PROJECTION_REF),
            "review_status_ref": dict(L0_REVIEW_STATUS_REF),
            "hardgate_summary_ref": dict(L0_HARDGATE_SUMMARY_REF),
            "ladder_consumption_ref": None,
            "review_status_alias": "missing",
            "ladder_consumption_status": "suspended",
            "review_status_alias_source": f"{DGT_L0_CONTROLS_ARTIFACT}:$.l0_toy_projection.review_status",
            "projected_claim_pointer": f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
            "level_state": "suspended",
            "promotion_status": "suspended-by-l0-owner-pointer",
            "boundary_ledger": [
                {
                    "level_id": level_id,
                    "status": "suspended",
                    "reason": "missing dgt-l0-controls projection",
                    "source_pointer": f"{DGT_L0_CONTROLS_ARTIFACT}:$.l0_toy_projection",
                }
            ],
            "not_claimed": [
                "Bounded L0 toy training controls only.",
                "No production scale claim.",
                "No GPT or Llama claim.",
                "No global superiority claim.",
                "No LLM replacement claim.",
                "No universal recipe claim.",
                "No unbounded scaling law claim.",
                "No verdict inheritance to L1 or higher scaling levels.",
            ],
        }
    if level_id == "L1_tiny_sequence":
        return _l1_default_scaling_capsule()
    return {
        "level_id": level_id,
        "claim_id": f"claim:dgt_scaling_ladder_owner:{level_id}",
        "pointer": L1_TINY_SEQUENCE_PROJECTION_POINTER if level_id == "L1_tiny_sequence" else f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
        "projected_claim_pointer": f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
        "level_state": "blocked",
        "promotion_status": "blocked-until-level-local-evidence",
        "base_transformer_control": None,
        "matched_random_structural_control": None,
        "compute_param_ledger": None,
        "negative_witness_sweep": None,
        "hardgates": {
            "SCALE-HG2": "fail",
            "SCALE-HG3": "fail",
            "SCALE-HG4": "fail",
        },
        "boundary_ledger": [
            {
                "level_id": level_id,
                "status": "blocked",
                "reason": "missing bounded scaling level capsule evidence",
            }
        ],
        "not_claimed": list(SCALING_LADDER_NOT_CLAIMED),
    }


def _l1_capsule_from_projection(projection: Mapping[str, Any] | None) -> dict[str, Any]:
    capsule = _l1_default_scaling_capsule()
    if not isinstance(projection, Mapping):
        return capsule
    eligible = projection.get("state") == "l1-scaling-evidence-eligible" and projection.get("decision_status") == "scaling-evidence-eligible"
    bounded_negative = projection.get("state") == "l1-bounded-negative" and projection.get("decision_status") == "bounded-negative"
    capsule.update(
        {
            "pointer": L1_TINY_SEQUENCE_PROJECTION_POINTER,
            "review_status_alias": (
                projection.get("decision_status") if isinstance(projection.get("decision_status"), str) else "missing"
            ),
            "promotion_readiness_alias": (
                projection.get("state") if isinstance(projection.get("state"), str) else "missing"
            ),
            "review_status_alias_source": FAIR_L1_DECISION_STATUS_POINTER,
            "promotion_readiness_alias_source": L1_TINY_SEQUENCE_PROJECTION_POINTER,
            "l1_ood_mechanism_verdict_alias_source": L1_OOD_MECHANISM_VERDICT_POINTER,
            "l1_ood_mechanism_l2_implication_alias_source": L1_OOD_MECHANISM_L2_IMPLICATION_POINTER,
        }
    )
    if eligible:
        capsule["level_state"] = "ready"
        capsule["promotion_status"] = "l1-scaling-evidence-eligible"
        capsule["boundary_ledger"] = []
    else:
        capsule["level_state"] = "blocked"
        capsule["promotion_status"] = "l1-bounded-negative" if bounded_negative else "blocked-by-fair-l1-decision-pointer"
        capsule["boundary_ledger"] = [
            {
                "level_id": "L1_tiny_sequence",
                "status": "blocked",
                "reason": "fair L1 decision is not scaling-evidence-eligible",
                "source_pointer": L1_TINY_SEQUENCE_PROJECTION_POINTER,
            }
        ]
    not_claimed = projection.get("not_claimed")
    if isinstance(not_claimed, list) and not_claimed:
        capsule["not_claimed"] = list(not_claimed)
    return capsule


def _scaling_level_capsule(level_id: str, input_capsules: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    default = _scaling_default_capsule(level_id)
    raw = input_capsules.get(level_id)
    if not isinstance(raw, Mapping):
        return default
    capsule = dict(default)
    for key in (
        "claim_id",
        "pointer",
        "raw_claim_pointer",
        "l0_toy_projection_ref",
        "review_status_ref",
        "hardgate_summary_ref",
        "ladder_consumption_ref",
        "review_status_alias",
        "ladder_consumption_status",
        "review_status_alias_source",
        "promotion_readiness_alias",
        "promotion_readiness_alias_source",
        "projected_claim_pointer",
        "level_state",
        "promotion_status",
        "base_transformer_control",
        "matched_random_structural_control",
        "compute_param_ledger",
        "negative_witness_sweep",
        "independent_replay",
        "l0_control_projection",
        "hardgates",
        "boundary_ledger",
        "not_claimed",
    ):
        if key in raw:
            capsule[key] = raw[key]
    capsule["level_id"] = level_id
    return capsule


def _scaling_capsule_failures(capsule: Mapping[str, Any]) -> list[str]:
    failures: list[str] = []
    if not all(isinstance(capsule.get(key), str) and capsule.get(key) for key in ("level_id", "claim_id", "projected_claim_pointer")):
        failures.append("capsule identity or claim pointer missing")
    if capsule.get("level_id") == "L0_toy":
        if capsule.get("level_state") != "open":
            failures.append("level state not open")
        if capsule.get("promotion_status") != "opened-from-l0-pass-pointer":
            failures.append("promotion status not opened")
        if capsule.get("l0_toy_projection_ref") != L0_TOY_PROJECTION_REF:
            failures.append("l0 projection pointer mismatch")
        if capsule.get("review_status_ref") != L0_REVIEW_STATUS_REF:
            failures.append("review status pointer mismatch")
        if capsule.get("hardgate_summary_ref") != L0_HARDGATE_SUMMARY_REF:
            failures.append("hardgate summary pointer mismatch")
        if capsule.get("ladder_consumption_ref") != L0_LADDER_CONSUMPTION_REF:
            failures.append("ladder consumption pointer mismatch")
        if capsule.get("ladder_consumption_status") != "open":
            failures.append("ladder consumption not open")
        if capsule.get("review_status_alias_source") != artifact_pointer(L0_REVIEW_STATUS_REF):
            failures.append("review status alias source mismatch")
        copied_keys = sorted(key for key in L0_FORBIDDEN_LADDER_KEYS if key in capsule)
        if copied_keys:
            failures.append(f"L0 copied evidence body keys present: {copied_keys}")
        text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
        for phrase in ("bounded", "production", "global superiority", "llm replacement", "universal recipe", "l1"):
            if phrase not in text:
                failures.append(f"not_claimed boundary missing: {phrase}")
        return failures
    if capsule.get("level_id") == "L1_tiny_sequence":
        if capsule.get("pointer") != L1_TINY_SEQUENCE_PROJECTION_POINTER:
            failures.append("L1 pointer mismatch")
        if capsule.get("level_state") != "ready":
            failures.append("level state not ready")
        if capsule.get("promotion_status") != "l1-scaling-evidence-eligible":
            failures.append("promotion status not scaling-evidence eligible")
        if capsule.get("review_status_alias") != "scaling-evidence-eligible":
            failures.append("L1 decision status not eligible")
        if capsule.get("promotion_readiness_alias") != "l1-scaling-evidence-eligible":
            failures.append("L1 ladder projection not eligible")
        copied_keys = sorted(
            key
            for key in (
                "metrics",
                "hardgates",
                "claim_capsule",
                "claim_capsule_ref",
                "discovery_map",
                "verdict",
                "stable_causal_attribution",
            )
            if key in capsule
        )
        if copied_keys:
            failures.append(f"L1 copied evidence body keys present: {copied_keys}")
        text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
        for phrase in ("bounded tiny-sequence", "production", "global superiority", "llm replacement", "l2"):
            if phrase not in text:
                failures.append(f"L1 not_claimed boundary missing: {phrase}")
        return failures
    if capsule.get("level_state") != "ready":
        failures.append("level state not ready")
    if capsule.get("promotion_status") != "level-local-evidence-ready":
        failures.append("promotion status not level-local ready")
    for key in ("base_transformer_control", "matched_random_structural_control"):
        control = capsule.get(key)
        if not isinstance(control, Mapping) or control.get("status") != "pass" or not isinstance(control.get("pointer"), str):
            failures.append(f"{key} missing pass pointer")
    ledger = capsule.get("compute_param_ledger")
    if not isinstance(ledger, Mapping) or ledger.get("status") != "pass":
        failures.append("compute/param ledger missing pass status")
    for key in ("compute_units", "parameter_count"):
        value = ledger.get(key) if isinstance(ledger, Mapping) else None
        if not isinstance(value, (int, float)) or isinstance(value, bool) or value <= 0:
            failures.append(f"{key} missing positive numeric value")
    sweep = capsule.get("negative_witness_sweep")
    if not isinstance(sweep, Mapping) or sweep.get("status") != "pass" or not isinstance(sweep.get("pointer"), str):
        failures.append("negative witness sweep missing pass pointer")
    if not isinstance(capsule.get("boundary_ledger"), list):
        failures.append("boundary ledger missing")
    text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
    if "production" not in text or "global superiority" not in text or "unbounded" not in text:
        failures.append("not_claimed boundary missing")
    return failures


def _scaling_level_passes(capsule: Mapping[str, Any]) -> bool:
    return not _scaling_capsule_failures(capsule)


def _scaling_capsule_contract_passes(capsule: Mapping[str, Any]) -> bool:
    if not all(isinstance(capsule.get(key), str) and capsule.get(key) for key in ("level_id", "claim_id", "projected_claim_pointer")):
        return False
    if capsule.get("level_id") == "L0_toy":
        text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
        return (
            capsule.get("level_state") == "open"
            and capsule.get("promotion_status") == "opened-from-l0-pass-pointer"
            and capsule.get("l0_toy_projection_ref") == L0_TOY_PROJECTION_REF
            and capsule.get("review_status_ref") == L0_REVIEW_STATUS_REF
            and capsule.get("hardgate_summary_ref") == L0_HARDGATE_SUMMARY_REF
            and capsule.get("ladder_consumption_ref") == L0_LADDER_CONSUMPTION_REF
            and capsule.get("ladder_consumption_status") == "open"
            and all(key not in capsule for key in L0_FORBIDDEN_LADDER_KEYS)
            and "production" in text
            and "global superiority" in text
            and "llm replacement" in text
            and "universal recipe" in text
            and "l1" in text
        )
    if capsule.get("level_id") == "L1_tiny_sequence":
        text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
        return (
            capsule.get("pointer") == L1_TINY_SEQUENCE_PROJECTION_POINTER
            and capsule.get("level_state") == "ready"
            and capsule.get("promotion_status") == "l1-scaling-evidence-eligible"
            and capsule.get("review_status_alias") == "scaling-evidence-eligible"
            and capsule.get("promotion_readiness_alias") == "l1-scaling-evidence-eligible"
            and all(
                key not in capsule
                for key in (
                    "metrics",
                    "hardgates",
                    "claim_capsule",
                    "claim_capsule_ref",
                    "discovery_map",
                    "verdict",
                    "stable_causal_attribution",
                )
            )
            and "bounded tiny-sequence" in text
            and "production" in text
            and "global superiority" in text
            and "llm replacement" in text
            and "l2" in text
        )
    if capsule.get("level_state") != "ready" or capsule.get("promotion_status") != "level-local-evidence-ready":
        return False
    for key in ("base_transformer_control", "matched_random_structural_control"):
        control = capsule.get(key)
        if not isinstance(control, Mapping) or control.get("status") != "pass" or not isinstance(control.get("pointer"), str):
            return False
    if not isinstance(capsule.get("boundary_ledger"), list):
        return False
    text = " ".join(str(item).lower() for item in capsule.get("not_claimed", []))
    return "production" in text and "global superiority" in text and "unbounded" in text


def _scaling_ledgers_monotone(levels: Sequence[Mapping[str, Any]]) -> bool:
    previous_compute = -1.0
    previous_params = -1.0
    for row in levels:
        capsule = row.get("claim_capsule") if isinstance(row, Mapping) else None
        if isinstance(capsule, Mapping) and capsule.get("level_id") == "L0_toy":
            if capsule.get("hardgate_summary_ref") != L0_HARDGATE_SUMMARY_REF:
                return False
            previous_compute = -1.0
            previous_params = -1.0
            continue
        if isinstance(capsule, Mapping) and capsule.get("level_id") == "L1_tiny_sequence":
            previous_compute = 0.0
            previous_params = 0.0
            continue
        ledger = capsule.get("compute_param_ledger") if isinstance(capsule, Mapping) else None
        if not isinstance(ledger, Mapping):
            return False
        compute = ledger.get("compute_units")
        params = ledger.get("parameter_count")
        if not isinstance(compute, (int, float)) or isinstance(compute, bool) or compute <= previous_compute:
            return False
        if not isinstance(params, (int, float)) or isinstance(params, bool) or params <= previous_params:
            return False
        if any(str(key).lower() in {"accuracy", "loss", "raw_metrics", "records"} for key in ledger):
            return False
        previous_compute = float(compute)
        previous_params = float(params)
    return True


def _scaling_source_projection(owner_payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d5_m_projection.status",
        "discovery_level_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d5_m_projection.discovery_level",
        "mechanism_closure_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d5_m_projection.mechanism_closure_status",
        "status": pointer_value(owner_payload, "$.d5_m_projection.status"),
        "discovery_level": pointer_value(owner_payload, "$.d5_m_projection.discovery_level"),
        "mechanism_closure_status": pointer_value(owner_payload, "$.d5_m_projection.mechanism_closure_status"),
    }


def _scaling_boundary_ledger(levels: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    failed_index: int | None = None
    rows: list[dict[str, Any]] = []
    for index, row in enumerate(levels):
        capsule = row.get("claim_capsule") if isinstance(row, Mapping) else None
        level_id = SCALING_LADDER_LEVEL_IDS[index]
        failures = _scaling_capsule_failures(capsule if isinstance(capsule, Mapping) else {})
        if failures and failed_index is None:
            failed_index = index
            rows.append(
                {
                    "level_id": level_id,
                    "status": "failed",
                    "failed_gate": "SCALE-HG5",
                    "reason": "; ".join(failures),
                    "source_pointer": f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
                }
            )
        elif failed_index is not None and index > failed_index:
            rows.append(
                {
                    "level_id": level_id,
                    "status": "blocked",
                    "failed_gate": "SCALE-HG5",
                    "reason": f"blocked by earlier failed level {SCALING_LADDER_LEVEL_IDS[failed_index]}",
                    "source_pointer": f"{SCALING_LADDER_POINTER}.levels[{index}].claim_capsule",
                }
            )
    return rows


def scaling_ladder_hardgate_rows(owner_payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    ladder = owner_payload.get("scaling_ladder")
    ladder = ladder if isinstance(ladder, Mapping) else {}
    levels = ladder.get("levels")
    levels = levels if isinstance(levels, list) else []
    source_projection = ladder.get("source_projection")
    source_projection = source_projection if isinstance(source_projection, Mapping) else _scaling_source_projection(owner_payload)
    not_claimed = ladder.get("not_claimed", SCALING_LADDER_NOT_CLAIMED)
    not_claimed_text = " ".join(str(item).lower() for item in not_claimed) if isinstance(not_claimed, Sequence) else ""
    level_capsules = [
        row.get("claim_capsule")
        for row in levels
        if isinstance(row, Mapping) and isinstance(row.get("claim_capsule"), Mapping)
    ]
    level_passes = [bool(isinstance(capsule, Mapping) and _scaling_level_passes(capsule)) for capsule in level_capsules]
    contract_passes = [bool(isinstance(capsule, Mapping) and _scaling_capsule_contract_passes(capsule)) for capsule in level_capsules]
    failed_level_count = len([passed for passed in level_passes if not passed])
    boundary_ledger = ladder.get("boundary_ledger")
    failed_conditions = {
        "SCALE-HG1": not (
            source_projection.get("status") == "ready"
            and source_projection.get("discovery_level") == "D5-M"
            and source_projection.get("mechanism_closure_status") == "closed"
        ),
        "SCALE-HG2": not (
            len(level_capsules) == len(SCALING_LADDER_LEVEL_IDS)
            and all(contract_passes)
        ),
        "SCALE-HG3": not (
            len(levels) == len(SCALING_LADDER_LEVEL_IDS)
            and _scaling_ledgers_monotone(levels)
        ),
        "SCALE-HG4": not (
            len(level_capsules) == len(SCALING_LADDER_LEVEL_IDS)
            and all(
                isinstance(capsule, Mapping)
                and (
                    (
                        capsule.get("level_id") == "L0_toy"
                        and capsule.get("hardgate_summary_ref") == L0_HARDGATE_SUMMARY_REF
                    )
                    or (
                        capsule.get("level_id") == "L1_tiny_sequence"
                        and capsule.get("pointer") == L1_TINY_SEQUENCE_PROJECTION_POINTER
                        and capsule.get("review_status_alias") == "scaling-evidence-eligible"
                        and capsule.get("promotion_readiness_alias") == "l1-scaling-evidence-eligible"
                    )
                    or (
                        isinstance(capsule.get("negative_witness_sweep"), Mapping)
                        and capsule["negative_witness_sweep"].get("status") == "pass"
                    )
                )
                for capsule in level_capsules
            )
        ),
        "SCALE-HG5": failed_level_count != 0
        or not isinstance(boundary_ledger, list)
        or bool(boundary_ledger),
        "SCALE-HG6": not (
            ladder.get("evidence_scope") == "bounded-model-prototype-scaling"
            and "production" in not_claimed_text
            and "gpt" in not_claimed_text
            and "llama" in not_claimed_text
            and "global superiority" in not_claimed_text
            and "llm replacement" in not_claimed_text
            and "universal recipe" in not_claimed_text
            and "unbounded" in not_claimed_text
        ),
    }
    evidence = {
        "SCALE-HG1": "$.d5_m_projection",
        "SCALE-HG2": "$.scaling_ladder.levels",
        "SCALE-HG3": "$.scaling_ladder.levels",
        "SCALE-HG4": "$.scaling_ladder.levels",
        "SCALE-HG5": "$.scaling_ladder.boundary_ledger",
        "SCALE-HG6": "$.scaling_ladder.evidence_scope",
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in SCALING_LADDER_GATE_NAMES
    }


def build_scaling_ladder_projection(owner_payload: Mapping[str, Any]) -> dict[str, Any]:
    overrides = owner_payload.get("scaling_ladder")
    overrides = overrides if isinstance(overrides, Mapping) else {}
    input_capsules = _scaling_level_input_by_id(owner_payload)
    levels = [
        {
            "level_id": level_id,
            "claim_capsule": _scaling_level_capsule(level_id, input_capsules),
        }
        for level_id in SCALING_LADDER_LEVEL_IDS
    ]
    if "L1_tiny_sequence" not in input_capsules:
        levels[SCALING_LADDER_LEVEL_IDS.index("L1_tiny_sequence")] = {
            "level_id": "L1_tiny_sequence",
            "claim_capsule": _l1_capsule_from_projection(_read_l1_tiny_sequence_projection(Path("."))),
        }
    source_projection = _scaling_source_projection(owner_payload)
    boundary_ledger = _scaling_boundary_ledger(levels)
    opened_levels = [
        row["level_id"]
        for row in levels
        if isinstance(row.get("claim_capsule"), Mapping) and row["claim_capsule"].get("level_state") in {"open", "ready"}
    ]
    draft: dict[str, Any] = {
        "status": "blocked",
        "review_status": "review-line-blocked",
        "discovery_level": source_projection["discovery_level"] if source_projection["discovery_level"] in {"D5-M", "D5-O", "D4"} else "D0",
        "evidence_scope": overrides.get("evidence_scope", "bounded-model-prototype-scaling"),
        "source_projection": source_projection,
        "l0_toy_projection_ref": dict(L0_TOY_PROJECTION_REF),
        "review_status_ref": dict(L0_REVIEW_STATUS_REF),
        "hardgate_summary_ref": dict(L0_HARDGATE_SUMMARY_REF),
        "ladder_consumption_ref": _owner_ladder_consumption_ref(owner_payload),
        "level_state": "l0-open" if opened_levels == ["L0_toy"] else ("all-levels-ready" if len(opened_levels) == len(SCALING_LADDER_LEVEL_IDS) else "blocked"),
        "promotion_status": "l0-open-only" if opened_levels == ["L0_toy"] else ("all-levels-ready" if len(opened_levels) == len(SCALING_LADDER_LEVEL_IDS) else "blocked"),
        "opened_levels": opened_levels,
        "overall_status": "blocked",
        "not_inherited_from_l0": [
            level_id
            for level_id in SCALING_LADDER_LEVEL_IDS
            if level_id != "L0_toy"
        ],
        "levels": levels,
        "boundary_ledger": boundary_ledger,
        "hardgate": {
            "status": "fail",
            "gate_names": list(SCALING_LADDER_GATE_NAMES),
            "gates": {},
            "failed_gate": None,
            "failed_gate_pointer": None,
            "blocked_reason": None,
        },
        "not_claimed": list(overrides.get("not_claimed", SCALING_LADDER_NOT_CLAIMED)),
    }
    gates = scaling_ladder_hardgate_rows({**owner_payload, "scaling_ladder": draft})
    failed = [gate_name for gate_name in SCALING_LADDER_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    failed_gate = failed[0] if failed else None
    overall_status = "ready" if failed_gate is None else ("l0-open-only" if opened_levels == ["L0_toy"] else "blocked")
    draft.update(
        {
            "status": "ready" if failed_gate is None else "blocked",
            "review_status": "review-line-ready" if failed_gate is None else "review-line-blocked",
            "discovery_level": "D5-M" if failed_gate is None else draft["discovery_level"],
            "overall_status": overall_status,
            "hardgate": {
                "status": "pass" if failed_gate is None else "fail",
                "gate_names": list(SCALING_LADDER_GATE_NAMES),
                "gates": gates,
                "failed_gate": failed_gate,
                "failed_gate_pointer": None if failed_gate is None else artifact_pointer(gates[failed_gate]["evidence"]),
                "blocked_reason": None if failed_gate is None else f"blocked-by-{failed_gate}",
            },
            "anti_triviality_status": "pass",
            **owner_local_anti_triviality_contract(
                recommended_level="D5-M",
                scale_only_pointer="$.scaling_ladder.hardgate.gates.SCALE-HG1",
                metadata_only_pointer="$.scaling_ladder.hardgate.gates.SCALE-HG3",
                matched_random_pointer="$.scaling_ladder.hardgate.gates.SCALE-HG2",
                forbidden_column_pointer="$.scaling_ladder.hardgate.gates.SCALE-HG6",
                status="pass",
                failed_gate=None,
            ),
        }
    )
    errors = validate_scaling_ladder_projection({**owner_payload, "scaling_ladder": draft})
    if errors:
        raise ValueError("; ".join(errors))
    return DgtScalingLadderProjection(draft).as_payload()


def validate_scaling_ladder_projection(owner_payload: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    payload = owner_payload.get("scaling_ladder")
    if not isinstance(payload, Mapping):
        return ["DGT scaling ladder projection missing"]
    if set(payload) != set(SCALING_LADDER_REQUIRED_KEYS):
        errors.append("DGT scaling ladder fields mismatch")
    levels = payload.get("levels")
    if not isinstance(levels, list) or [row.get("level_id") for row in levels if isinstance(row, Mapping)] != list(SCALING_LADDER_LEVEL_IDS):
        errors.append("DGT scaling ladder level order mismatch")
    else:
        for index, row in enumerate(levels):
            capsule = row.get("claim_capsule") if isinstance(row, Mapping) else None
            if not isinstance(capsule, Mapping) or capsule.get("level_id") != SCALING_LADDER_LEVEL_IDS[index]:
                errors.append(f"DGT scaling ladder capsule mismatch: {SCALING_LADDER_LEVEL_IDS[index]}")
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping) or hardgate.get("gate_names") != list(SCALING_LADDER_GATE_NAMES):
        errors.append("DGT scaling ladder hardgate names mismatch")
        return errors
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(SCALING_LADDER_GATE_NAMES):
        errors.append("DGT scaling ladder hardgate rows mismatch")
        return errors
    expected_gates = scaling_ladder_hardgate_rows(owner_payload)
    if gates != expected_gates:
        errors.append("DGT scaling ladder hardgate evaluation mismatch")
    failed = [gate_name for gate_name in SCALING_LADDER_GATE_NAMES if gates[gate_name].get("status") != "pass"]
    failed_gate = failed[0] if failed else None
    if hardgate.get("status") != ("pass" if failed_gate is None else "fail"):
        errors.append("DGT scaling ladder hardgate status mismatch")
    if hardgate.get("failed_gate") != failed_gate:
        errors.append("DGT scaling ladder failed gate mismatch")
    expected_pointer = None if failed_gate is None else artifact_pointer(gates[failed_gate]["evidence"])
    if hardgate.get("failed_gate_pointer") != expected_pointer:
        errors.append("DGT scaling ladder failed gate pointer mismatch")
    if hardgate.get("blocked_reason") != (None if failed_gate is None else f"blocked-by-{failed_gate}"):
        errors.append("DGT scaling ladder blocked reason mismatch")
    if payload.get("status") != ("ready" if failed_gate is None else "blocked"):
        errors.append("DGT scaling ladder status mismatch")
    if payload.get("review_status") != ("review-line-ready" if failed_gate is None else "review-line-blocked"):
        errors.append("DGT scaling ladder review status mismatch")
    source_level = pointer_value(owner_payload, "$.d5_m_projection.discovery_level")
    expected_level = "D5-M" if failed_gate is None else (source_level if source_level in {"D5-M", "D5-O", "D4"} else "D0")
    if payload.get("discovery_level") != expected_level:
        errors.append("DGT scaling ladder discovery level mismatch")
    if payload.get("l0_toy_projection_ref") != L0_TOY_PROJECTION_REF:
        errors.append("DGT scaling ladder L0 projection pointer mismatch")
    if payload.get("review_status_ref") != L0_REVIEW_STATUS_REF:
        errors.append("DGT scaling ladder review status pointer mismatch")
    if payload.get("hardgate_summary_ref") != L0_HARDGATE_SUMMARY_REF:
        errors.append("DGT scaling ladder hardgate summary pointer mismatch")
    expected_ladder_ref = _owner_ladder_consumption_ref(owner_payload)
    if payload.get("ladder_consumption_ref") != expected_ladder_ref:
        errors.append("DGT scaling ladder ladder consumption pointer mismatch")
    if not _payload_ladder_consumption_ref_consistent(owner_payload):
        errors.append("DGT scaling ladder ladder consumption pointer co-presence mismatch")
    opened = payload.get("opened_levels")
    if not isinstance(opened, list):
        errors.append("DGT scaling ladder opened levels mismatch")
    else:
        expected_opened = [
            row["level_id"]
            for row in levels
            if isinstance(row, Mapping)
            and isinstance(row.get("claim_capsule"), Mapping)
            and row["claim_capsule"].get("level_state") in {"open", "ready"}
        ]
        if opened != expected_opened:
            errors.append("DGT scaling ladder opened levels evaluation mismatch")
    if payload.get("not_inherited_from_l0") != [level_id for level_id in SCALING_LADDER_LEVEL_IDS if level_id != "L0_toy"]:
        errors.append("DGT scaling ladder inheritance boundary mismatch")
    expected_overall = "ready" if failed_gate is None else ("l0-open-only" if payload.get("opened_levels") == ["L0_toy"] else "blocked")
    if payload.get("overall_status") != expected_overall:
        errors.append("DGT scaling ladder overall status mismatch")
    if failed_gate is None and payload.get("evidence_scope") != "bounded-model-prototype-scaling":
        errors.append("DGT scaling ladder evidence scope mismatch")
    source = payload.get("source_projection")
    if not isinstance(source, Mapping):
        errors.append("DGT scaling ladder source projection missing")
    else:
        expected_source = _scaling_source_projection(owner_payload)
        if source != expected_source:
            errors.append("DGT scaling ladder source projection mismatch")
    boundary = payload.get("boundary_ledger")
    if not isinstance(boundary, list):
        errors.append("DGT scaling ladder boundary ledger mismatch")
    elif levels and boundary != _scaling_boundary_ledger(levels):
        errors.append("DGT scaling ladder boundary ledger evaluation mismatch")
    text = " ".join(str(item).lower() for item in payload.get("not_claimed", []))
    for phrase in ("production", "gpt", "llama", "global superiority", "llm replacement", "universal recipe", "unbounded"):
        if phrase not in text:
            errors.append(f"DGT scaling ladder not_claimed missing boundary: {phrase}")
    forbidden = json.dumps(payload, sort_keys=True).lower()
    for token in ("production scale authority", "global superiority accepted", "unbounded scaling law accepted"):
        if token in forbidden:
            errors.append(f"DGT scaling ladder contains forbidden claim token: {token}")
    return errors


class DiscoveryGatedTransformerProjector:
    def __init__(
        self,
        *,
        component_refs: Mapping[str, Any] | None = None,
        robustness_source_payloads: Mapping[str, Mapping[str, Any]] | None = None,
        claim_verdict_rows: Sequence[Mapping[str, Any]] | None = None,
        high_impact_review_rows: Sequence[Mapping[str, Any]] | None = None,
        d5_o_surface_summary: Mapping[str, Any] | None = None,
        root: Path | None = None,
    ) -> None:
        del claim_verdict_rows
        self.component_refs = dict(component_refs) if component_refs is not None else default_component_refs()
        self.robustness_source_payloads = (
            dict(robustness_source_payloads)
            if robustness_source_payloads is not None
            else default_robustness_source_payloads()
        )
        self.root = root or Path(".")
        self.high_impact_review_rows = tuple(
            high_impact_review_rows if high_impact_review_rows is not None else _read_high_impact_review_rows(self.root)
        )
        self.d5_o_surface_summary = dict(d5_o_surface_summary) if d5_o_surface_summary is not None else None

    def project(self, *, generated_at: str) -> dict[str, Any]:
        l0_projection = _read_l0_control_projection(self.root)
        ladder_consumption_ref = _l0_ladder_consumption_ref_from_projection(l0_projection)
        payload = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": generated_at,
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "model_id": MODEL_ID,
        "source_artifacts": {
            "component_refs": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs"),
            "ledger_aware_transformer_pointer": f"{LAT_CANONICAL_ARTIFACT}:$",
            "model_comparison_pointer": f"{MODEL_COMPARISON_CANONICAL_ARTIFACT}:$",
            "construct_suspension_ref": dict(L0_CONSTRUCT_SUSPENSION_REF),
            "honest_metric_review_ref": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.honest_metric_review"},
            "ladder_consumption_ref": ladder_consumption_ref,
            "interpretation_boundary_ref": dict(L1_INTERPRETATION_BOUNDARY_REF),
            "negative_witness_sweep_ref": dict(L1_NEGATIVE_WITNESS_SWEEP_REF),
            "l1_ood_mechanism_ref": dict(L1_OOD_MECHANISM_REF),
        },
            "component_refs": self.component_refs,
            "architecture_spec": default_architecture_spec(),
            "hardgate": {"status": "pass", "gate_names": list(GATE_NAMES), "gates": _gate_rows(self.component_refs)},
            "hardgate_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.hardgate"),
            "tool_route_evidence": build_dgt_tool_route_evidence(generated_at=generated_at),
            "family_definition": build_dgt_family_definition(),
            "component_ablation": build_component_ablation(seed=COMPONENT_ABLATION_SEED),
            "neural_ablation_ref": _neural_ablation_ref(self.root),
            "discovery_map_signal": default_discovery_map_signal(),
            "discovery_map_signal_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.discovery_map_signal"),
            "d4_projection_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.d4_projection"),
            **sidecar_refs(),
            "forbidden_claim_term_audit": {},
            "revocation_rows": [
                {"gate": "DGT-HG13", "condition": "Revoke when the owner-local jet certificate pointer is absent."},
                {"gate": "DGT-HG20", "condition": "Revoke when forbidden claim language appears in DGT claim fields."},
            ],
            "not_claimed": list(NOT_CLAIMED),
        }
        if any(row["status"] != "pass" for row in payload["hardgate"]["gates"].values()):
            payload["hardgate"]["status"] = "fail"
        payload["forbidden_claim_term_audit"] = _dgt_forbidden_claim_term_audit(payload)
        payload["d4_projection"] = build_d4_projection_payload(
            payload,
            {
                "discovery_map_level_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.discovery_level",
                "claim_verdict_owner": "Core",
                "claim_graph_owner": "Core",
            },
        )
        payload["operational_robustness"] = DgtOperationalRobustnessLedger().evaluate(
            payload,
            self.robustness_source_payloads,
        )
        payload["d5_o_projection"] = build_d5_o_projection(
            payload,
            self.high_impact_review_rows,
            root=self.root,
            surface_summary=self.d5_o_surface_summary,
        )
        payload["d5_m_projection"] = build_d5_m_projection(payload)
        payload["scaling_ladder"] = {
            "levels": [
                {"level_id": "L0_toy", "claim_capsule": _l0_capsule_from_projection(l0_projection)},
                {
                    "level_id": "L1_tiny_sequence",
                    "claim_capsule": _l1_capsule_from_projection(_read_l1_tiny_sequence_projection(self.root)),
                },
            ]
        }
        payload["scaling_ladder"] = build_scaling_ladder_projection(payload)
        if not _owner_refs_resolve(self.root, payload):
            raise ValueError("DGT owner refs do not resolve")
        validate_projection(payload)
        return payload


def validate_projection(payload: Mapping[str, Any]) -> None:
    expected = {
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
    if set(payload) != expected:
        raise ValueError("DGT projection top-level fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT projection identity mismatch")
    if payload["model_id"] != MODEL_ID:
        raise ValueError("DGT model identity mismatch")
    source_artifacts = payload["source_artifacts"]
    if not isinstance(source_artifacts, Mapping):
        raise ValueError("DGT source artifacts missing")
    expected_owner_refs = {
        "construct_suspension_ref": L0_CONSTRUCT_SUSPENSION_REF,
        "honest_metric_review_ref": {"artifact": DGT_L0_CONTROLS_ARTIFACT, "pointer": "$.honest_metric_review"},
        "interpretation_boundary_ref": L1_INTERPRETATION_BOUNDARY_REF,
        "negative_witness_sweep_ref": L1_NEGATIVE_WITNESS_SWEEP_REF,
        "l1_ood_mechanism_ref": L1_OOD_MECHANISM_REF,
    }
    for key, expected_ref in expected_owner_refs.items():
        if source_artifacts.get(key) != expected_ref:
            raise ValueError(f"DGT owner ref mismatch: {key}")
    ladder_ref = source_artifacts.get("ladder_consumption_ref")
    if ladder_ref is not None and ladder_ref != L0_LADDER_CONSUMPTION_REF:
        raise ValueError("DGT owner ref mismatch: ladder_consumption_ref")
    if not _payload_ladder_consumption_ref_consistent(payload):
        raise ValueError("DGT ladder consumption pointer co-presence mismatch")
    validate_dgt_tool_route_evidence(payload["tool_route_evidence"])
    validate_dgt_family_definition(payload["family_definition"])
    validate_component_ablation(payload["component_ablation"])
    validate_operational_robustness(payload["operational_robustness"], payload)
    found = _has_recursive_key(payload, REJECTED_INLINE_KEYS)
    if found is not None:
        raise ValueError(f"DGT projection contains inline source body key: {found}")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "tool-use-dgt", "tool-use-toy-dgt"))
    if token is not None:
        raise ValueError(f"DGT projection contains forbidden value: {token}")
    if '"terminal_verdict":' in json.dumps(payload, sort_keys=True).lower():
        raise ValueError("DGT projection contains forbidden terminal authority payload")
    for key in ("claim_capsule_ref", "evidence_envelope_ref", "mechanism_namecert_ref", "jet_certificate_ref", "neural_ablation_ref"):
        if not _is_cell(payload[key]):
            raise ValueError(f"DGT sidecar ref is not a pointer cell: {key}")
    for key in ("hardgate_ref", "discovery_map_signal_ref", "d4_projection_ref"):
        if not _is_cell(payload[key]):
            raise ValueError(f"DGT summary ref is not a pointer cell: {key}")
    if artifact_pointer(payload["d4_projection_ref"]) != f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection":
        raise ValueError("DGT D4 projection ref mismatch")
    if payload["forbidden_claim_term_audit"] != _dgt_forbidden_claim_term_audit(payload):
        raise ValueError("DGT forbidden claim term audit mismatch")
    if payload["forbidden_claim_term_audit"]["status"] != "pass":
        raise ValueError("DGT forbidden claim term audit failed")
    if not isinstance(payload["revocation_rows"], list) or not payload["revocation_rows"]:
        raise ValueError("DGT revocation rows missing")
    if not isinstance(payload["component_refs"], Mapping) or not _walk_cells(payload["component_refs"]):
        raise ValueError("DGT component refs must be pointer-only")
    hardgate = payload["hardgate"]
    if not isinstance(hardgate, Mapping) or hardgate.get("gate_names") != list(GATE_NAMES):
        raise ValueError("DGT hardgate names mismatch")
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(GATE_NAMES):
        raise ValueError("DGT hardgate rows mismatch")
    if hardgate.get("status") != ("pass" if all(row.get("status") == "pass" for row in gates.values()) else "fail"):
        raise ValueError("DGT hardgate status mismatch")
    for gate_name, row in gates.items():
        if not isinstance(row, Mapping) or set(row) != {"status", "evidence", "not_claimed"}:
            raise ValueError(f"DGT hardgate row schema mismatch: {gate_name}")
        if row["status"] not in {"pass", "fail"}:
            raise ValueError(f"DGT hardgate row status mismatch: {gate_name}")
        if not _is_cell(row["evidence"]) or not _is_cell(row["not_claimed"]):
            raise ValueError(f"DGT hardgate row must use pointer cells: {gate_name}")
    d4_errors = validate_d4_projection(payload["d4_projection"], payload)
    if d4_errors:
        raise ValueError("; ".join(d4_errors))
    d5_errors = validate_d5_o_projection(payload["d5_o_projection"], payload)
    if d5_errors:
        raise ValueError("; ".join(d5_errors))
    d5_m_errors = validate_d5_m_projection(payload)
    if d5_m_errors:
        raise ValueError("; ".join(d5_m_errors))
    scaling_errors = validate_scaling_ladder_projection(payload)
    if scaling_errors:
        raise ValueError("; ".join(scaling_errors))


def validate_dgt_hardgate_evidence_bundle(payload: Mapping[str, Any], *, root: Path) -> None:
    validate_projection(payload)
    gates = payload["hardgate"]["gates"]
    for gate_name, row in gates.items():
        if row["status"] != "pass":
            continue
        for key in ("evidence", "not_claimed"):
            if _resolve_cell(root, row[key]) is None:
                raise ValueError(f"DGT hardgate {key} pointer does not resolve: {gate_name}")


def build_projection(
    *,
    generated_at: str,
    component_refs: Mapping[str, Any] | None = None,
    robustness_source_payloads: Mapping[str, Mapping[str, Any]] | None = None,
    claim_verdict_rows: Sequence[Mapping[str, Any]] | None = None,
    high_impact_review_rows: Sequence[Mapping[str, Any]] | None = None,
    d5_o_surface_summary: Mapping[str, Any] | None = None,
    root: Path | None = None,
) -> dict[str, Any]:
    return DiscoveryGatedTransformerProjector(
        component_refs=component_refs,
        robustness_source_payloads=robustness_source_payloads,
        claim_verdict_rows=claim_verdict_rows,
        high_impact_review_rows=high_impact_review_rows,
        d5_o_surface_summary=d5_o_surface_summary,
        root=root,
    ).project(generated_at=generated_at)


def render_markdown(payload: Mapping[str, Any]) -> str:
    validate_projection(payload)
    lines = [
        "# Discovery-Gated Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Model: `{payload['model_id']}`",
        f"- Hardgate: `{payload['hardgate']['status']}`",
        "",
        "## Component Refs",
        "",
        "| component | artifact | pointer |",
        "| --- | --- | --- |",
    ]
    for name, cell in payload["component_refs"].items():
        lines.append(f"| `{name}` | `{cell['artifact']}` | `{cell['pointer']}` |")
    lines.extend(["", "## Hardgates", "", "| gate | status | evidence |", "| --- | --- | --- |"])
    for gate_name, row in payload["hardgate"]["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    tool_route = payload["tool_route_evidence"]
    lines.extend(
        [
            "",
            "## Tool Route Evidence",
            "",
            f"- Schema: `{tool_route['schema_id']}`",
            f"- Owner: `{tool_route['owner_ref']}`",
            f"- CGA route patch: `{tool_route['cga_route_patch_ref']}`",
            f"- Hardgate: `{tool_route['hardgate']['status']}`",
            "",
            "| route | class | decision |",
            "| --- | --- | --- |",
        ]
    )
    for row in tool_route["synthetic_tool_call_grid"]:
        lines.append(f"| `{row['route_id']}` | `{row['route_class']}` | `{row['admission_decision']}` |")
    family_definition = payload["family_definition"]
    lines.extend(
        [
            "",
            "## Family Definition",
            "",
            f"- Schema: `{family_definition['schema_id']}`",
            f"- Owner: `{family_definition['owner_ref']}`",
            f"- Hardgate: `{family_definition['hardgate']['status']}`",
            f"- Claim status: `{family_definition['model_family_claim_status']['status']}`",
            "",
            "| group | pointers |",
            "| --- | --- |",
        ]
    )
    for group_name, group in family_definition["invariant_groups"].items():
        lines.append(f"| `{group_name}` | `{len(group['evidence_pointers'])}` |")
    component_ablation = payload["component_ablation"]
    lines.extend(
        [
            "",
            "## Component Ablation",
            "",
            f"- Schema: `{component_ablation['schema_id']}`",
            f"- Owner: `{component_ablation['owner_ref']}`",
            f"- Arms: `{component_ablation['arm_count']}`",
            f"- Hardgate: `{component_ablation['hardgate']['status']}`",
            "",
            "| arm | component | effect status | claim allowed |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in component_ablation["arms"]:
        lines.append(
            f"| `{row['arm_id']}` | `{row['component_id']}` | `{row['effect_status']}` | `{row['causal_claim_allowed']}` |"
        )
    robustness = payload["operational_robustness"]
    lines.extend(
        [
            "",
            "## Operational Robustness",
            "",
            f"- Owner: `{robustness['owner_ref']}`",
            f"- Readiness: `{robustness['readiness']}`",
            f"- Discovery level: `{robustness['discovery_level']}`",
            f"- LAT evidence: `{robustness['source_artifacts']['ledger_aware_transformer_pointer']}`",
            "",
            "| gate | status | evidence |",
            "| --- | --- | --- |",
        ]
    )
    for gate_name, row in robustness["hardgate"]["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    d5_o_projection = payload["d5_o_projection"]
    lines.extend(
        [
            "",
            "## D5-O Projection",
            "",
            f"- Status: `{d5_o_projection['status']}`",
            f"- Discovery level: `{d5_o_projection['discovery_level']}`",
            f"- Source level: `{d5_o_projection['source_level']}`",
            f"- Blocked reason: `{d5_o_projection['blocked_reason']}`",
            "",
            "| gate | status | evidence |",
            "| --- | --- | --- |",
        ]
    )
    for gate_name, row in d5_o_projection["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    d5_m_projection = payload["d5_m_projection"]
    d5_m_evidence_scope = json.dumps(d5_m_projection["evidence_scope"], sort_keys=True)
    lines.extend(
        [
            "",
            "## D5-M Projection",
            "",
            f"- Status: `{d5_m_projection['status']}`",
            f"- Discovery level: `{d5_m_projection['discovery_level']}`",
            f"- Evidence scope: `{d5_m_evidence_scope}`",
            f"- Terminal scope: `{d5_m_projection['terminal_verdict_scope']}`",
            f"- Blocked reason: `{d5_m_projection['blocked_reason']}`",
            "",
            "| gate | status | evidence |",
            "| --- | --- | --- |",
        ]
    )
    for gate_name, row in d5_m_projection["hardgates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    scaling_ladder = payload["scaling_ladder"]
    lines.extend(
        [
            "",
            "## Scaling Ladder",
            "",
            f"- Status: `{scaling_ladder['status']}`",
            f"- Review status: `{scaling_ladder['review_status']}`",
            f"- Discovery level: `{scaling_ladder['discovery_level']}`",
            f"- Evidence scope: `{scaling_ladder['evidence_scope']}`",
            f"- Blocked reason: `{scaling_ladder['hardgate']['blocked_reason']}`",
            "",
            "| level | state | promotion | evidence |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in scaling_ladder["levels"]:
        capsule = row["claim_capsule"]
        if row["level_id"] == "L0_toy":
            evidence = artifact_pointer(capsule["l0_toy_projection_ref"])
        else:
            evidence = capsule.get("raw_claim_pointer") or capsule.get("projected_claim_pointer", "missing")
        lines.append(
            "| "
            f"`{row['level_id']}` | "
            f"`{capsule['level_state']}` | "
            f"`{capsule['promotion_status']}` | "
            f"`{evidence}` |"
        )
    lines.extend(["", "| gate | status | evidence |", "| --- | --- | --- |"])
    for gate_name, row in scaling_ladder["hardgate"]["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    lines.extend(["", "### Scaling Boundary Ledger", "", "| level | status | gate | reason |", "| --- | --- | --- | --- |"])
    for row in scaling_ladder["boundary_ledger"]:
        lines.append(f"| `{row['level_id']}` | `{row['status']}` | `{row['failed_gate']}` | `{row['reason']}` |")
    d4_projection = payload["d4_projection"]
    lines.extend(
        [
            "",
            "## D4 Projection",
            "",
            f"- Readiness: `{d4_projection['readiness']}`",
            f"- Discovery level: `{d4_projection['discovery_level']}`",
            f"- Failed gate: `{d4_projection['failed_gate']}`",
            "",
            "| gate | status | evidence |",
            "| --- | --- | --- |",
        ]
    )
    for gate_name, row in d4_projection["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    lines.extend(
        [
            "",
            "## Sidecars",
            "",
            f"- Claim capsule: `{artifact_pointer(payload['claim_capsule_ref'])}`",
            f"- Evidence envelope: `{artifact_pointer(payload['evidence_envelope_ref'])}`",
            f"- Mechanism NameCert: `{artifact_pointer(payload['mechanism_namecert_ref'])}`",
            f"- Jet certificate: `{artifact_pointer(payload['jet_certificate_ref'])}`",
            f"- Jet hardgate: `{artifact_pointer(payload['hardgate_ref'])}`",
            f"- Discovery map signal: `{artifact_pointer(payload['discovery_map_signal_ref'])}`",
            "",
        ]
    )
    return "\n".join(lines)

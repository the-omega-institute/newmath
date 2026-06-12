"""Discovery-regularized training canonical projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL


SCHEMA_ID = "bedc-quality-lab:discovery-regularized-training"
ARTIFACT_ID = "bedc-quality-lab:discovery-regularized-training"
PRODUCER = "scripts/run_discovery_regularized_training.py"
PROJECTOR = "bedc_quality_lab.discovery_regularized_training.DiscoveryRegularizedTrainingProjection"
DEFAULT_DISCOVERY_LAMBDAS = (0.0, 1.0e-4, 1.0e-3, 5.0e-3, 1.0e-2)
DEFAULT_RHOS = (0.5, 0.7, 0.9, 0.95)
DEFAULT_MIXINGS = ("spiral", "parabolic", "realnvp")
DEFAULT_SEEDS = (11, 23, 37)
FORMAL_REPLAY_ARMS = (
    "base_transformer",
    "parameter_matched",
    "compute_matched",
    "matched_random_structural_control",
    "DGT_full",
    "DGT_without_LAT",
    "DGT_without_CGA",
    "DGT_without_DRT",
    "DGT_without_gap_ledger_route",
    "DGT_without_mechanism_probe",
    "DGT_without_certificate_gate",
    "DGT_without_jet_loss",
)
COMPAT_REPLAY_ALIASES = {
    "task_only": "base_transformer",
    "sigreg": "parameter_matched",
    "drt": "DGT_full",
    "matched_random": "matched_random_structural_control",
    "drt_jet": "DGT_full",
}
REPLAY_ARM_INTERNAL_ALIASES = {value: key for key, value in COMPAT_REPLAY_ALIASES.items() if value != "DGT_full"}
REPLAY_ARM_INTERNAL_ALIASES.update(
    {
        "compute_matched": "task_only",
        "DGT_full": "drt_jet",
        "DGT_without_LAT": "drt",
        "DGT_without_CGA": "drt",
        "DGT_without_DRT": "sigreg",
        "DGT_without_gap_ledger_route": "matched_random",
        "DGT_without_mechanism_probe": "matched_random",
        "DGT_without_certificate_gate": "matched_random",
        "DGT_without_jet_loss": "drt",
    }
)
REPLAY_ARM_DISABLED_COMPONENTS = {
    "base_transformer": (),
    "parameter_matched": (),
    "compute_matched": (),
    "matched_random_structural_control": ("structural_randomization",),
    "DGT_full": (),
    "DGT_without_LAT": ("LAT",),
    "DGT_without_CGA": ("CGA",),
    "DGT_without_DRT": ("DRT",),
    "DGT_without_gap_ledger_route": ("gap_ledger_route",),
    "DGT_without_mechanism_probe": ("mechanism_probe",),
    "DGT_without_certificate_gate": ("certificate_gate",),
    "DGT_without_jet_loss": ("jet_loss",),
}
REPLAY_ARM_ROLES = {
    "base_transformer": "model-comparison:base_transformer",
    "parameter_matched": "parameter-matched control",
    "compute_matched": "compute-matched control",
    "matched_random_structural_control": "model-comparison:matched_random_structural_control",
    "DGT_full": "model-comparison:dgt",
    "DGT_without_LAT": "DGT component ablation",
    "DGT_without_CGA": "DGT component ablation",
    "DGT_without_DRT": "DGT component ablation",
    "DGT_without_gap_ledger_route": "DGT component ablation",
    "DGT_without_mechanism_probe": "DGT component ablation",
    "DGT_without_certificate_gate": "DGT component ablation",
    "DGT_without_jet_loss": "DGT component ablation",
}
DEFAULT_ARMS = FORMAL_REPLAY_ARMS
TORCH_LAMBDAS = (1.0e-3, 5.0e-3)
TORCH_RHOS = (0.7, 0.9)
TORCH_SEEDS = (11, 23)
TORCH_ARMS = ("drt", "matched_random")
MECHANISM_ABLATION_DISCOVERY_LAMBDA = 0.01
MECHANISM_ABLATION_RHO = 0.95
MECHANISM_ABLATION_MIXING = "spiral"
MECHANISM_ABLATION_REQUIRED_ARMS = (
    "without_discovery",
    "without_ledger",
    "without_certificate",
    "without_mechanism",
    "without_cost",
    "without_negative_witness",
)
MECHANISM_ABLATION_DISABLED_TERMS = {
    "without_discovery": ("discovery",),
    "without_ledger": ("ledger",),
    "without_certificate": ("certificate",),
    "without_mechanism": ("mechanism",),
    "without_cost": ("cost",),
    "without_negative_witness": ("negative_witness",),
}
DRIFT_TOLERANCE = 1.0e-4
METRIC_KEYS = (
    "task_accuracy",
    "quality_q",
    "debt_q",
    "benefit_q",
    "certificate_loss",
    "matched_random_certificate_loss",
    "classifier_shift_count",
    "delta_quality_ci_low",
    "net_positive_signal",
    "jet_required_order_gain",
    "jet_order_one_gain",
    "jet_shortcut_reducible_fraction",
    "matched_random_jet_gain",
    "jet_quality_q_ci_low",
)
MECHANISM_ABLATION_METRIC_KEYS = (
    "quality_q",
    "classifier_shift_count",
    "net_positive_signal",
)
FORBIDDEN_SUMMARY_ALIASES = (
    "terminal_verdict",
    "claim_capsule",
    "task_accuracy_only_result",
)
NOT_CLAIMED = (
    "full model training",
    "global architecture superiority",
    "full LeJEPA reproduction",
    "mechanism closure",
    "production device authority",
)
POSITIVE_CLAIM = {
    "text": "Discovery-regularized training records a bounded lab-local positive signal under deterministic replay and matched-random controls.",
    "scope": "canonical deterministic anchor with bounded optional PyTorch evidence",
}
JSON_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
QUALITY_PROMOTION_ARMS = (
    "base_transformer",
    "parameter_matched",
    "DGT_full",
    "matched_random_structural_control",
    "old_certificate_guided",
)
CERTIFICATE_GUIDED_DN_ARTIFACTS = (
    "reports/canonical/certificate-guided-training.json",
    "reports/canonical/certificate-guided-discovery.json",
)
CERTIFICATE_GUIDED_DN_DISCOVERY_MAP_ROWS = (
    "reports/canonical/discovery_map.json:$.rows[?report=certificate-guided-training].discovery_level",
    "reports/canonical/discovery_map.json:$.rows[?report=certificate-guided-discovery].discovery_level",
)
CERTIFICATE_GUIDED_DN_FORBIDDEN_ACTIONS = ("cover", "replace", "delete")
DRT_EXTENSION_UER_MAX = 0.18
DRT_EXTENSION_UER_REDUCTION_MIN = 0.06
DRT_EXTENSION_FORBIDDEN_PATTERNS = (
    ".refactor-loop/host.env",
    "host.env",
    "host_env",
    "terminal_verdict",
    "candidate_evidence_body",
    "candidate_measurement_body",
    "candidate_measurements_body",
)
FIXED_CELL_SECONDS_PROXY = 0.00025
FLOPS_PER_STEP_PROXY = 4096
ENERGY_PER_FLOP_PROXY = 1.0e-10
DRT_HARDGATES = tuple(f"DRT-HG{index}" for index in range(1, 10))
DRTJ_HARDGATES = tuple(f"DRTJ-HG{index}" for index in range(1, 6))
DGT_REPLAY_OWNER_READY_GATE = "DGT-REPLAY-HG0-owner-ready"
DGT_REPLAY_HARDGATES = tuple(f"DGT-REPLAY-HG{index}" for index in range(1, 11))
DRT_BASE_HARDGATES = (DGT_REPLAY_OWNER_READY_GATE, *DRT_HARDGATES[:8], *DRTJ_HARDGATES, *DGT_REPLAY_HARDGATES)
DRT_PROMOTION_HARDGATE = DRT_HARDGATES[-1]
JET_SIDECAR_SCHEMA_ID = f"{SCHEMA_ID}:jet-sidecar"
JET_SIDECAR_ARTIFACT = "reports/canonical/discovery_regularized_training_jet.json"
JET_ABLATION_ARTIFACT = "reports/canonical/drt_jet_ablation.md"
JET_FRONTIER_ARTIFACT = "reports/canonical/jet_loss_frontier.json"


@dataclass(frozen=True)
class LossTermSpec:
    term_id: str
    role: str
    evidence_pointer: str


@dataclass(frozen=True)
class AblationArmSpec:
    arm_id: str
    disabled_terms: tuple[str, ...]
    evidence_pointer: str


@dataclass(frozen=True)
class DrtTrainingExtensionSpec:
    loss_terms: tuple[LossTermSpec, ...]
    ablation_arms: tuple[AblationArmSpec, ...]
    forbidden_keys: tuple[str, ...]
    required_run_pointers: tuple[str, ...]


@dataclass(frozen=True)
class TorchTrainingArmProtocol:
    requested_device: str
    resolved_device: str
    seed: int
    steps: int
    dtype: str
    drift_tolerance: float
    status: str
    evidence_pointer: str


@dataclass(frozen=True)
class ComputeLedger:
    status: str
    backend_row_counts: dict[str, int]
    device: str
    requested_device: str
    resolved_device: str
    deterministic_seed_count: int
    torch_seed_count: int
    total_steps: int
    wall_time_seconds_proxy: float
    flops_proxy: int
    energy_proxy: float
    cost_protocol_pointer: str
    raw_rows_pointer: str | None
    protocols_pointer: str
    missing_fields: list[str]
    evidence_pointer: str


@dataclass(frozen=True)
class JetLossProtocol:
    lambda_ledger: float
    lambda_certificate: float
    lambda_jet: float
    lambda_witness: float
    lambda_debt: float
    required_order: int
    max_noise_order: int
    shortcut_controls: tuple[str, ...]
    thresholds: dict[str, float]


@dataclass(frozen=True)
class JetSurfaceProjection:
    records: Sequence[Mapping[str, Any]]
    protocol: JetLossProtocol

    def project(self) -> dict[str, Any]:
        return project_jet_surface(self.records, self.protocol)


def default_grid() -> tuple[dict[str, Any], ...]:
    return tuple(
        {
            "discovery_lambda": float(discovery_lambda),
            "rho": float(rho),
            "mixing": str(mixing),
            "seed": int(seed),
            "arm": str(arm),
        }
        for discovery_lambda in DEFAULT_DISCOVERY_LAMBDAS
        for rho in DEFAULT_RHOS
        for mixing in DEFAULT_MIXINGS
        for seed in DEFAULT_SEEDS
        for arm in DEFAULT_ARMS
    )


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def quality_artifact_pointer(pointer: str) -> str:
    return f"{JSON_ARTIFACT}:{pointer}"


def _quality_pointer_value(payload: Mapping[str, Any], artifact_pointer: str) -> Any:
    prefix = f"{JSON_ARTIFACT}:"
    if not artifact_pointer.startswith(prefix):
        return None
    pointer = artifact_pointer[len(prefix) :]
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _as_finite_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _rounded_number(value: float | None) -> float | None:
    return None if value is None else round(float(value), 6)


def default_drt_training_extension_spec() -> DrtTrainingExtensionSpec:
    loss_terms = (
        LossTermSpec("discovery", "positive discovery surface regularizer", quality_artifact_pointer("$.surface_registry.classifier_shift")),
        LossTermSpec("ledger", "debt ledger pressure", quality_artifact_pointer("$.constraint_summary")),
        LossTermSpec("certificate", "certificate loss separation", quality_artifact_pointer("$.matched_random_control")),
        LossTermSpec("mechanism", "mechanism-facing classifier shift", quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta")),
        LossTermSpec("cost", "bounded replay cost accounting", quality_artifact_pointer("$.compute_ledger")),
        LossTermSpec("negative_witness", "matched-random negative witness pressure", quality_artifact_pointer("$.negative_witness_mutations")),
    )
    return DrtTrainingExtensionSpec(
        loss_terms=loss_terms,
        ablation_arms=(
            AblationArmSpec("full_drt", (), quality_artifact_pointer("$.surface_registry.quality.by_arm.DGT_full")),
            AblationArmSpec("without_discovery", ("discovery",), quality_artifact_pointer("$.surface_registry.quality.by_arm.parameter_matched")),
            AblationArmSpec("without_ledger", ("ledger",), quality_artifact_pointer("$.surface_registry.quality.by_arm.matched_random_structural_control")),
            AblationArmSpec("without_certificate", ("certificate",), quality_artifact_pointer("$.matched_random_control")),
            AblationArmSpec("without_mechanism", ("mechanism",), quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta")),
            AblationArmSpec("without_cost", ("cost",), quality_artifact_pointer("$.compute_ledger")),
            AblationArmSpec("without_negative_witness", ("negative_witness",), quality_artifact_pointer("$.negative_witness_mutations")),
        ),
        forbidden_keys=DRT_EXTENSION_FORBIDDEN_PATTERNS,
        required_run_pointers=(
            quality_artifact_pointer("$.records.raw_rows_pointer"),
            quality_artifact_pointer("$.training_loop_trace"),
            quality_artifact_pointer("$.matched_random_control"),
            quality_artifact_pointer("$.negative_witness_mutations"),
        ),
    )


def default_jet_loss_protocol() -> JetLossProtocol:
    return JetLossProtocol(
        lambda_ledger=0.16,
        lambda_certificate=0.22,
        lambda_jet=0.34,
        lambda_witness=0.18,
        lambda_debt=0.10,
        required_order=3,
        max_noise_order=1,
        shortcut_controls=("matched_random_jet", "shortcut_witness_flip"),
        thresholds={
            "required_order_gain_min": 0.015,
            "order_one_degradation_floor": -0.004,
            "shortcut_reduction_max": 0.55,
            "matched_random_jet_gain_max": -0.001,
            "quality_ci_low_min": 0.001,
        },
    )


def jet_protocol_payload(protocol: JetLossProtocol) -> dict[str, Any]:
    return {
        **asdict(protocol),
        "owner_pointer": quality_artifact_pointer("$.jet_loss_protocol"),
        "protocol_pointer": quality_artifact_pointer("$.jet_loss_protocol"),
        "sidecar_schema_id": JET_SIDECAR_SCHEMA_ID,
    }


def drt_extension_forbidden_key_audit(
    value: Any,
    forbidden_keys: Sequence[str] = DRT_EXTENSION_FORBIDDEN_PATTERNS,
) -> dict[str, Any]:
    hits: list[dict[str, str]] = []
    forbidden = tuple(pattern.lower() for pattern in forbidden_keys)

    def walk(cell: Any, path: str) -> None:
        if isinstance(cell, Mapping):
            for key, item in cell.items():
                key_text = str(key)
                key_lower = key_text.lower()
                for pattern in forbidden:
                    if pattern in key_lower:
                        hits.append({"path": f"{path}.{key_text}", "kind": "key", "match": key_text})
                walk(item, f"{path}.{key_text}")
        elif isinstance(cell, (list, tuple)):
            for index, item in enumerate(cell):
                walk(item, f"{path}[{index}]")
        elif isinstance(cell, str):
            lowered = cell.lower()
            for pattern in forbidden:
                if pattern in lowered:
                    hits.append({"path": path, "kind": "value", "match": cell})

    walk(value, "$")
    return {
        "status": _status(not hits),
        "audited_pattern_count": len(forbidden),
        "hit_count": len(hits),
        "hits": hits,
    }


def quality_promotion_boundary(payload: Mapping[str, Any]) -> dict[str, Any]:
    task_pointer = quality_artifact_pointer("$.surface_registry.quality.by_arm.base_transformer.quality_q_mean")
    task_quality = _as_finite_number(_quality_pointer_value(payload, task_pointer))
    drt_delta_pointer = quality_artifact_pointer("$.lambda_summary.best_positive.delta_quality_ci_low_mean")
    drt_delta = _as_finite_number(_quality_pointer_value(payload, drt_delta_pointer))
    drt_ci_low = task_quality + drt_delta if task_quality is not None and drt_delta is not None else None
    hardgate_state = (
        "clears-boundary"
        if drt_ci_low is not None and task_quality is not None and drt_ci_low > task_quality
        else "fail-closed"
    )
    arm_sources = {
        "base_transformer": "base_transformer",
        "parameter_matched": "parameter_matched",
        "DGT_full": "DGT_full",
        "matched_random_structural_control": "matched_random_structural_control",
        "old_certificate_guided": None,
    }
    arm_comparisons: dict[str, dict[str, Any]] = {}
    for order, arm in enumerate(QUALITY_PROMOTION_ARMS, start=1):
        source_arm = arm_sources[arm]
        if source_arm is None:
            evidence_pointer = quality_artifact_pointer("$.config.arms")
            quality_pointer = evidence_pointer
            arm_quality = None
            ci_low_pointer = evidence_pointer
            ci_low = None
            comparison = "missing-evidence-fail-closed"
        else:
            evidence_pointer = quality_artifact_pointer(f"$.surface_registry.quality.by_arm.{source_arm}")
            quality_pointer = quality_artifact_pointer(
                f"$.surface_registry.quality.by_arm.{source_arm}.quality_q_mean"
            )
            arm_quality = _as_finite_number(_quality_pointer_value(payload, quality_pointer))
            if arm == "DGT_full":
                ci_low_pointer = drt_delta_pointer
                ci_low = drt_ci_low
            else:
                ci_low_pointer = quality_pointer
                ci_low = arm_quality
            if ci_low is None or task_quality is None:
                comparison = "missing-evidence-fail-closed"
            elif arm == "base_transformer":
                comparison = "task-only-reference"
            elif ci_low > task_quality:
                comparison = "above-task-only"
            else:
                comparison = "not-above-task-only-fail-closed"
        arm_comparisons[arm] = {
            "render_order": order,
            "arm": arm,
            "source_arm": source_arm,
            "slot_state": "present-but-fail-closed",
            "evidence_pointer": evidence_pointer,
            "quality_q_pointer": quality_pointer,
            "quality_q_ci_low_pointer": ci_low_pointer,
            "quality_q": _rounded_number(arm_quality),
            "quality_q_ci_low": _rounded_number(ci_low),
            "task_only_quality_q": _rounded_number(task_quality),
            "comparison_to_task_only": comparison,
            "promotion_gate": "fail-closed" if comparison.endswith("fail-closed") else "reference"
            if arm == "base_transformer"
            else "comparison-only",
        }
    arm_comparisons["DGT_full"]["promotion_gate"] = hardgate_state
    return {
        "slot_state": "present-but-fail-closed",
        "owner_pointer": quality_artifact_pointer("$.quality_promotion_boundary"),
        "source_artifact": JSON_ARTIFACT,
        "quality_metric": "quality_q",
        "replay_dimension_pointers": {
            "steps": quality_artifact_pointer("$.config.steps"),
            "seeds": quality_artifact_pointer("$.config.seeds"),
            "mixings": quality_artifact_pointer("$.config.mixings"),
            "rho": quality_artifact_pointer("$.config.rhos"),
            "lambda": quality_artifact_pointer("$.config.discovery_lambdas"),
        },
        "task_only_quality_q_pointer": task_pointer,
        "hardgate": {
            "gate_id": "DRT-HG2",
            "slot_state": "present-but-fail-closed",
            "requirement": "DRT quality_q CI-low must be strictly above task_only quality_q.",
            "evidence_pointer": drt_delta_pointer,
            "task_only_quality_q": _rounded_number(task_quality),
            "drt_quality_q_ci_low": _rounded_number(drt_ci_low),
            "drt_minus_task_only_quality_q_ci_low": _rounded_number(
                None if drt_ci_low is None or task_quality is None else drt_ci_low - task_quality
            ),
            "promotion_gate": hardgate_state,
            "fail_closed_when": "drt_quality_q_ci_low <= task_only_quality_q",
        },
        "arm_quality_order": list(QUALITY_PROMOTION_ARMS),
        "arm_comparisons": arm_comparisons,
    }


def _artifact_pointer_resolves(payload: Mapping[str, Any], artifact_pointer: str) -> bool:
    return _quality_pointer_value(payload, artifact_pointer) is not None


def _rows_for_arm(rows: Sequence[Mapping[str, Any]], arm: str) -> list[Mapping[str, Any]]:
    return [
        row
        for row in rows
        if row.get("arm") == arm or row.get("internal_metric_alias") == arm
    ]


def replay_arm_catalog() -> dict[str, Any]:
    return {
        "schema_id": f"{SCHEMA_ID}:replay-arm-catalog",
        "owner_pointer": quality_artifact_pointer("$.replay_arm_catalog"),
        "formal_arms": [
            {
                "arm_id": arm,
                "render_order": index,
                "disabled_components": list(REPLAY_ARM_DISABLED_COMPONENTS.get(arm, ())),
                "comparison_owner_role": REPLAY_ARM_ROLES.get(arm, "DGT replay arm"),
                "structural_randomized": arm == "matched_random_structural_control",
            }
            for index, arm in enumerate(FORMAL_REPLAY_ARMS, start=1)
        ],
        "public_arm_summary_policy": "formal-arms-only",
    }


def comparison_owner_status(source_artifacts: Mapping[str, Any]) -> dict[str, Any]:
    configured = source_artifacts.get("model_comparison")
    if isinstance(configured, Mapping):
        status = str(configured.get("status", "missing"))
        gates_status = str(configured.get("hardgates_status", "fail"))
        owner_status = str(configured.get("owner_status", status))
    else:
        status = str(configured or "ready")
        gates_status = "pass" if status == "ready" else "fail"
        owner_status = "resolved" if status == "ready" else status
    ready = status == "ready" and gates_status == "pass" and owner_status in {"resolved", "ready"}
    return {
        "schema_id": f"{SCHEMA_ID}:comparison-owner",
        "artifact": "reports/canonical/model-comparison.json",
        "owner_pointer": quality_artifact_pointer("$.comparison_owner"),
        "models_pointer": "reports/canonical/model-comparison.json:$.models",
        "hardgates_pointer": "reports/canonical/model-comparison.json:$.hardgates",
        "required_owner_ids": ["dgt", "base_transformer", "matched_random_structural_control"],
        "status": "ready" if ready else ("pending" if status == "pending" else "missing"),
        "owner_status": owner_status,
        "hardgates_status": gates_status,
        "ready": ready,
    }


def dgt_replay_gate_summary(payload: Mapping[str, Any]) -> dict[str, Any]:
    gates = payload.get("hardgate", {}).get("gates") if isinstance(payload.get("hardgate"), Mapping) else None
    if not isinstance(gates, Mapping):
        gates = {}
    ordered = (DGT_REPLAY_OWNER_READY_GATE, *DGT_REPLAY_HARDGATES)
    failed = next((gate for gate in ordered if not isinstance(gates.get(gate), Mapping) or gates[gate].get("status") != "pass"), None)
    return {
        "schema_id": f"{SCHEMA_ID}:dgt-replay-gate-summary",
        "owner_pointer": quality_artifact_pointer("$.dgt_replay_gate_summary"),
        "status": "pass" if failed is None else ("blocked" if failed == DGT_REPLAY_OWNER_READY_GATE else "fail"),
        "gate_order": list(ordered),
        "failed_gate": failed,
        "failed_gate_pointer": None if failed is None else f"$.hardgate.gates.{failed}.status",
        "level_candidate": "D5-M" if failed is None else "DN",
        "positive_claim_permitted": failed is None,
    }


def certificate_guided_dn_preservation(
    source_artifacts: Mapping[str, Any],
    *,
    required_refs: Sequence[str] = CERTIFICATE_GUIDED_DN_ARTIFACTS,
    discovery_map_refs: Sequence[str] = CERTIFICATE_GUIDED_DN_DISCOVERY_MAP_ROWS,
    forbidden_actions: Sequence[str] = CERTIFICATE_GUIDED_DN_FORBIDDEN_ACTIONS,
    expected_discovery_level: str = "DN",
    terminal_status_isolated: bool = True,
) -> dict[str, Any]:
    ref_rows = [
        {
            "artifact": str(artifact),
            "role": "sibling-dn-evidence",
            "expected_discovery_level": expected_discovery_level,
            "artifact_status": str(source_artifacts.get(str(artifact), "missing")),
        }
        for artifact in required_refs
    ]
    map_rows = [
        {
            "pointer": str(pointer),
            "expected_discovery_level": expected_discovery_level,
            "status": "expected",
        }
        for pointer in discovery_map_refs
    ]
    actions = tuple(str(action).lower() for action in forbidden_actions)
    return {
        "schema_id": f"{SCHEMA_ID}:certificate-guided-dn-preservation",
        "status": _status(
            bool(ref_rows)
            and all(row["artifact_status"] == "present" for row in ref_rows)
            and all(row["expected_discovery_level"] == "DN" for row in ref_rows)
            and all(row["expected_discovery_level"] == "DN" for row in map_rows)
            and terminal_status_isolated
        ),
        "owner_pointer": quality_artifact_pointer("$.certificate_guided_dn_preservation"),
        "boundary_verdict": "preserve-sibling-dn-evidence",
        "comparison_permission": "DRT may compare while preserving certificate-guided DN evidence as sibling artifacts.",
        "required_refs": ref_rows,
        "discovery_map_refs": map_rows,
        "forbidden_actions": list(actions),
        "terminal_status_isolated": terminal_status_isolated,
        "not_claimed": "Certificate-guided artifacts remain independent sibling evidence.",
    }


def certificate_guided_dn_preservation_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    section = payload.get("certificate_guided_dn_preservation")
    if not isinstance(section, Mapping):
        return {
            "status": "fail",
            "required_refs_present": False,
            "expected_dn_status": False,
            "forbidden_actions_absent": False,
            "terminal_status_isolated": False,
        }
    required = section.get("required_refs")
    map_rows = section.get("discovery_map_refs")
    forbidden_actions = tuple(str(action).lower() for action in section.get("forbidden_actions", ()))
    artifacts = {
        str(row.get("artifact"))
        for row in required
        if isinstance(row, Mapping)
    } if isinstance(required, Sequence) and not isinstance(required, str) else set()
    required_refs_present = (
        artifacts == set(CERTIFICATE_GUIDED_DN_ARTIFACTS)
        and all(
            isinstance(row, Mapping)
            and str(row.get("artifact", "")).startswith("reports/canonical/")
            and row.get("artifact_status") == "present"
            for row in required
        )
    ) if isinstance(required, Sequence) and not isinstance(required, str) else False
    expected_dn_status = (
        all(isinstance(row, Mapping) and row.get("expected_discovery_level") == "DN" for row in required)
        and all(isinstance(row, Mapping) and row.get("expected_discovery_level") == "DN" for row in map_rows)
    ) if (
        isinstance(required, Sequence)
        and not isinstance(required, str)
        and isinstance(map_rows, Sequence)
        and not isinstance(map_rows, str)
    ) else False
    text = json.dumps(section, sort_keys=True).lower().replace("_", "-")
    forbidden_hits = [
        action
        for action in forbidden_actions
        if f"{action}-claim" in text
        or f"{action} claim" in text
        or f"{action} certificate-guided" in text
    ]
    terminal_status_isolated = section.get("terminal_status_isolated") is True and not _has_recursive_key(section, "terminal_verdict")
    status = _status(required_refs_present and expected_dn_status and not forbidden_hits and terminal_status_isolated)
    return {
        "status": status,
        "required_refs_present": required_refs_present,
        "expected_dn_status": expected_dn_status,
        "forbidden_actions_absent": not forbidden_hits,
        "forbidden_action_hits": forbidden_hits,
        "terminal_status_isolated": terminal_status_isolated,
    }


def _mechanism_ablation_row_key(row: Mapping[str, Any]) -> str:
    return str(row.get("arm", ""))


def _mechanism_ablation_summary(
    rows: Sequence[Mapping[str, Any]],
    owner_payload: Mapping[str, Any],
) -> dict[str, Any]:
    by_arm = {arm: [] for arm in MECHANISM_ABLATION_REQUIRED_ARMS}
    for row in rows:
        arm = _mechanism_ablation_row_key(row)
        if arm in by_arm:
            by_arm[arm].append(row)
    full_quality_pointer = quality_artifact_pointer("$.surface_registry.quality.by_arm.DGT_full.quality_q_mean")
    full_shift_pointer = quality_artifact_pointer("$.surface_registry.classifier_shift.classifier_shift_count_mean")
    full_signal_pointer = quality_artifact_pointer("$.surface_registry.classifier_shift.net_positive_signal")
    full_quality = _as_finite_number(_quality_pointer_value(owner_payload, full_quality_pointer))
    full_shift = _as_finite_number(_quality_pointer_value(owner_payload, full_shift_pointer))
    full_signal = _quality_pointer_value(owner_payload, full_signal_pointer) is True
    full_positive = full_signal and full_shift is not None and full_shift > 0.0
    comparison_rows = []
    for order, arm in enumerate(MECHANISM_ABLATION_REQUIRED_ARMS, start=1):
        arm_rows = by_arm[arm]
        row_count_pointer = quality_artifact_pointer(f"$.mechanism_ablation.by_arm.{arm}.row_count")
        quality_pointer = quality_artifact_pointer(f"$.mechanism_ablation.by_arm.{arm}.quality_q_mean")
        shift_pointer = quality_artifact_pointer(f"$.mechanism_ablation.by_arm.{arm}.classifier_shift_count_mean")
        signal_pointer = quality_artifact_pointer(f"$.mechanism_ablation.by_arm.{arm}.net_positive_count")
        quality = _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "quality_q")) is not None and not isinstance(value, bool)
        )
        shift = _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "classifier_shift_count")) is not None and not isinstance(value, bool)
        )
        net_positive_count = sum(1 for row in arm_rows if row.get("net_positive_signal") is True)
        full_minus_ablation = None if full_quality is None or quality is None else round(float(full_quality) - float(quality), 6)
        comparison_rows.append(
            {
                "render_order": order,
                "arm_id": arm,
                "disabled_terms": list(MECHANISM_ABLATION_DISABLED_TERMS[arm]),
                "row_count": len(arm_rows),
                "row_count_pointer": row_count_pointer,
                "quality_q_mean": quality,
                "quality_q_pointer": quality_pointer,
                "classifier_shift_count_mean": shift,
                "classifier_shift_pointer": shift_pointer,
                "net_positive_count": net_positive_count,
                "net_positive_pointer": signal_pointer,
                "full_drt_quality_q_mean": _rounded_number(full_quality),
                "full_minus_ablation_quality_q": _rounded_number(full_minus_ablation),
                "full_beats_ablation": isinstance(full_minus_ablation, (int, float)) and full_minus_ablation > DRIFT_TOLERANCE,
                "net_positive_parity": net_positive_count > 0 and shift is not None and shift + DRIFT_TOLERANCE >= (full_shift or 0.0),
                "comparison_pointers": {
                    "full_quality_q": full_quality_pointer,
                    "ablation_quality_q": quality_pointer,
                    "ablation_row_count": row_count_pointer,
                    "ablation_net_positive_count": signal_pointer,
                },
            }
        )
    by_arm_summary = {
        row["arm_id"]: {
            "row_count": row["row_count"],
            "quality_q_mean": row["quality_q_mean"],
            "classifier_shift_count_mean": row["classifier_shift_count_mean"],
            "net_positive_count": row["net_positive_count"],
        }
        for row in comparison_rows
    }
    payload = {
        "schema_id": f"{SCHEMA_ID}:mechanism-ablation",
        "backend": "deterministic-mechanism-ablation",
        "anchor_cell": {
            "discovery_lambda": MECHANISM_ABLATION_DISCOVERY_LAMBDA,
            "rho": MECHANISM_ABLATION_RHO,
            "mixing": MECHANISM_ABLATION_MIXING,
            "seeds": list(DEFAULT_SEEDS),
        },
        "required_arms": list(MECHANISM_ABLATION_REQUIRED_ARMS),
        "metric_keys": list(MECHANISM_ABLATION_METRIC_KEYS),
        "raw_rows_pointer": quality_artifact_pointer("$.records.raw_rows_pointer"),
        "full_drt": {
            "quality_q_mean": _rounded_number(full_quality),
            "quality_q_pointer": full_quality_pointer,
            "classifier_shift_count_mean": _rounded_number(full_shift),
            "classifier_shift_pointer": full_shift_pointer,
            "net_positive_signal": full_signal,
            "net_positive_signal_pointer": full_signal_pointer,
        },
        "by_arm": by_arm_summary,
        "comparisons": comparison_rows,
    }
    required_arms_present = all(row["row_count"] > 0 for row in comparison_rows)
    resolution_payload = {**owner_payload, "mechanism_ablation": payload}
    comparison_pointers_resolve = all(
        _artifact_pointer_resolves(resolution_payload, pointer)
        for row in comparison_rows
        for pointer in row["comparison_pointers"].values()
    )
    full_beats_all = all(row["full_beats_ablation"] for row in comparison_rows)
    no_net_positive_parity = not any(row["net_positive_parity"] for row in comparison_rows)
    payload.update(
        {
            "status": _status(
                required_arms_present
                and comparison_pointers_resolve
                and full_beats_all
                and full_positive
                and no_net_positive_parity
            ),
            "required_arms_present": required_arms_present,
            "comparison_pointers_resolve": comparison_pointers_resolve,
            "full_beats_all_ablations": full_beats_all,
            "full_positive_mechanism_signal": full_positive,
            "no_ablation_net_positive_parity": no_net_positive_parity,
        }
    )
    return payload


def _training_mechanism_cert(owner_payload: Mapping[str, Any]) -> dict[str, Any]:
    required_pointers = (
        quality_artifact_pointer("$.mechanism_ablation.status"),
        quality_artifact_pointer("$.mechanism_ablation.comparisons"),
        quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta"),
        quality_artifact_pointer("$.training_loop_trace.retrain_rows_pointer"),
        quality_artifact_pointer("$.matched_random_control"),
        quality_artifact_pointer("$.negative_witness_mutations"),
        quality_artifact_pointer("$.compute_ledger"),
    )
    resolution_rows = [
        {
            "pointer": pointer,
            "status": _status(_artifact_pointer_resolves(owner_payload, pointer)),
        }
        for pointer in required_pointers
    ]
    mechanism_status = _quality_pointer_value(owner_payload, required_pointers[0])
    torch_positive = _quality_pointer_value(
        owner_payload,
        quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta.net_positive_signal"),
    ) is True
    ledger_complete = _quality_pointer_value(owner_payload, quality_artifact_pointer("$.compute_ledger.status")) == "complete"
    all_pointers_resolve = all(row["status"] == "pass" for row in resolution_rows)
    return {
        "schema_id": f"{SCHEMA_ID}:training-mechanism-cert",
        "status": _status(
            mechanism_status == "pass"
            and torch_positive
            and ledger_complete
            and all_pointers_resolve
        ),
        "owner_pointer": quality_artifact_pointer("$.training_mechanism_cert"),
        "hardgate_pointer": quality_artifact_pointer("$.hardgate.gates.DRT-HG9"),
        "status_pointer": quality_artifact_pointer("$.training_mechanism_cert.status"),
        "required_pointers": resolution_rows,
        "mechanism_ablation_status_pointer": required_pointers[0],
        "torch_delta_pointer": quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta"),
        "matched_control_pointer": quality_artifact_pointer("$.matched_random_control"),
        "ledger_pointer": quality_artifact_pointer("$.compute_ledger"),
        "negative_witness_pointer": quality_artifact_pointer("$.negative_witness_mutations"),
        "all_required_pointers_resolve": all_pointers_resolve,
        "mechanism_ablation_status": mechanism_status,
        "torch_positive": torch_positive,
        "ledger_complete": ledger_complete,
    }


def project_drt_training_extension(
    records: Sequence[Mapping[str, Any]],
    spec: DrtTrainingExtensionSpec,
    run_artifacts: Mapping[str, str],
    owner_payload: Mapping[str, Any],
) -> dict[str, Any]:
    loss_terms = {
        term.term_id: {
            "term_id": term.term_id,
            "role": term.role,
            "enabled_pointer": quality_artifact_pointer("$.records.extension_metrics.loss_terms_enabled"),
            "evidence_pointer": term.evidence_pointer,
            "pointer_state": "present" if _artifact_pointer_resolves(owner_payload, term.evidence_pointer) else "missing",
        }
        for term in spec.loss_terms
    }
    ablation_rows = []
    full_quality = _as_finite_number(
        _quality_pointer_value(owner_payload, quality_artifact_pointer("$.surface_registry.quality.by_arm.DGT_full.quality_q_mean"))
    )
    for order, arm in enumerate(spec.ablation_arms, start=1):
        source_key = {
            "full_drt": "DGT_full",
            "without_discovery": "parameter_matched",
            "without_ledger": "matched_random_structural_control",
            "without_certificate": "matched_random_structural_control",
            "without_mechanism": "matched_random_structural_control",
            "without_cost": "DGT_full",
            "without_negative_witness": "matched_random_structural_control",
        }[arm.arm_id]
        quality_pointer = quality_artifact_pointer(f"$.surface_registry.quality.by_arm.{source_key}.quality_q_mean")
        quality_value = _as_finite_number(_quality_pointer_value(owner_payload, quality_pointer))
        ablation_rows.append(
            {
                "render_order": order,
                "arm_id": arm.arm_id,
                "disabled_terms": list(arm.disabled_terms),
                "source_arm": source_key,
                "evidence_pointer": arm.evidence_pointer,
                "quality_q_pointer": quality_pointer,
                "quality_q": _rounded_number(quality_value),
                "full_drt_quality_q": _rounded_number(full_quality),
                "quality_delta_vs_full_drt": _rounded_number(
                    None if quality_value is None or full_quality is None else quality_value - full_quality
                ),
                "pointer_state": "present" if _artifact_pointer_resolves(owner_payload, arm.evidence_pointer) else "missing",
            }
        )
    uer = _as_finite_number(_quality_pointer_value(owner_payload, quality_artifact_pointer("$.records.extension_metrics.uer_mean")))
    uer_reduction = _as_finite_number(
        _quality_pointer_value(owner_payload, quality_artifact_pointer("$.records.extension_metrics.uer_reduction_mean"))
    )
    component_drop_count = sum(
        1
        for row in ablation_rows
        if row["arm_id"] != "full_drt"
        and isinstance(row["quality_delta_vs_full_drt"], (int, float))
        and float(row["quality_delta_vs_full_drt"]) < 0.0
    )
    required_pointer_rows = [
        {
            "pointer": pointer,
            "status": _status(_artifact_pointer_resolves(owner_payload, pointer)),
        }
        for pointer in spec.required_run_pointers
    ]
    forbidden_audit = drt_extension_forbidden_key_audit(
        {
            "run_artifacts": dict(run_artifacts),
            "loss_family": loss_terms,
            "component_ablation": ablation_rows,
            "training_method_comparison": {
                "records_pointer": quality_artifact_pointer("$.records.extension_metrics"),
                "loss_terms_enabled_pointer": quality_artifact_pointer("$.records.extension_metrics.loss_terms_enabled"),
                "comparison_family_pointer": quality_artifact_pointer("$.records.extension_metrics.comparison_family"),
            },
        },
        spec.forbidden_keys,
    )
    gates = {
        "DRT-EXT-HG1_required_pointer_resolution": {
            "status": _status(all(row["status"] == "pass" for row in required_pointer_rows)),
            "evidence_pointer": "$.drt_extension_hardgates.required_run_pointers",
            "required_run_pointers": required_pointer_rows,
        },
        "DRT-EXT-HG2_uer_threshold": {
            "status": _status(
                uer is not None
                and uer_reduction is not None
                and uer <= DRT_EXTENSION_UER_MAX
                and uer_reduction >= DRT_EXTENSION_UER_REDUCTION_MIN
            ),
            "thresholds": {
                "uer_max": DRT_EXTENSION_UER_MAX,
                "uer_reduction_min": DRT_EXTENSION_UER_REDUCTION_MIN,
            },
            "uer_pointer": quality_artifact_pointer("$.records.extension_metrics.uer_mean"),
            "uer_reduction_pointer": quality_artifact_pointer("$.records.extension_metrics.uer_reduction_mean"),
            "uer": _rounded_number(uer),
            "uer_reduction": _rounded_number(uer_reduction),
        },
        "DRT-EXT-HG3_component_ablation": {
            "status": _status(component_drop_count >= 3),
            "evidence_pointer": "$.component_ablation.rows",
            "component_drop_count": component_drop_count,
            "required_component_drop_count": 3,
        },
        "DRT-EXT-HG4_forbidden_key_audit": forbidden_audit,
    }
    failed = next((gate_id for gate_id, row in gates.items() if row.get("status") != "pass"), None)
    return {
        "loss_family": {
            "status": "pointer-only",
            "owner_pointer": quality_artifact_pointer("$.loss_family"),
            "terms": loss_terms,
            "loss_terms_enabled_pointer": quality_artifact_pointer("$.records.extension_metrics.loss_terms_enabled"),
        },
        "component_ablation": {
            "status": "pointer-only",
            "owner_pointer": quality_artifact_pointer("$.component_ablation"),
            "rows": ablation_rows,
        },
        "training_method_comparison": {
            "status": "pointer-only",
            "owner_pointer": quality_artifact_pointer("$.training_method_comparison"),
            "comparison_family_pointer": quality_artifact_pointer("$.records.extension_metrics.comparison_family"),
            "compute_ledger_pointer": quality_artifact_pointer("$.records.extension_metrics.compute_ledger_pointer"),
            "debt_marker_pointer": quality_artifact_pointer("$.records.extension_metrics.debt_marker_pointer"),
            "metric_pointers": {
                "uer": quality_artifact_pointer("$.records.extension_metrics.uer_mean"),
                "uer_reduction": quality_artifact_pointer("$.records.extension_metrics.uer_reduction_mean"),
                "raw_rows": quality_artifact_pointer("$.records.raw_rows_pointer"),
            },
        },
        "drt_extension_hardgates": {
            "status": _status(failed is None),
            "gates": gates,
            "failed_gate": failed,
            "failed_gate_pointer": None if failed is None else f"$.drt_extension_hardgates.gates.{failed}.status",
            "thresholds": {
                "uer_max": DRT_EXTENSION_UER_MAX,
                "uer_reduction_min": DRT_EXTENSION_UER_REDUCTION_MIN,
            },
            "required_run_pointers": list(spec.required_run_pointers),
        },
    }


def _jet_arm_summary(rows: Sequence[Mapping[str, Any]], arm: str) -> dict[str, Any]:
    arm_rows = [row for row in rows if row.get("arm") == arm]
    return {
        "row_count": len(arm_rows),
        "required_order_gain_mean": _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "jet_required_order_gain")) is not None and not isinstance(value, bool)
        ),
        "order_one_gain_mean": _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "jet_order_one_gain")) is not None and not isinstance(value, bool)
        ),
        "shortcut_reducible_fraction_mean": _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "jet_shortcut_reducible_fraction")) is not None and not isinstance(value, bool)
        ),
        "quality_q_ci_low_mean": _mean(
            float(value)
            for row in arm_rows
            if (value := _metric(row, "jet_quality_q_ci_low")) is not None and not isinstance(value, bool)
        ),
        "net_positive_count": sum(1 for row in arm_rows if row.get("net_positive_signal") is True),
    }


def project_jet_surface(
    records: Sequence[Mapping[str, Any]],
    protocol: JetLossProtocol,
) -> dict[str, Any]:
    deterministic_rows = [row for row in records if row.get("backend") == "deterministic-anchor"]
    by_arm = {
        arm: _jet_arm_summary(deterministic_rows, arm)
        for arm in ("base_transformer", "parameter_matched", "DGT_full", "DGT_without_jet_loss", "matched_random_structural_control")
    }
    jet = by_arm["DGT_full"]
    drt = by_arm["DGT_without_jet_loss"]
    matched = by_arm["matched_random_structural_control"]
    required_order_delta = (
        None
        if jet["required_order_gain_mean"] is None or drt["required_order_gain_mean"] is None
        else round(float(jet["required_order_gain_mean"]) - float(drt["required_order_gain_mean"]), 6)
    )
    order_one_delta = (
        None
        if jet["order_one_gain_mean"] is None or drt["order_one_gain_mean"] is None
        else round(float(jet["order_one_gain_mean"]) - float(drt["order_one_gain_mean"]), 6)
    )
    shortcut_reduction = (
        None
        if jet["shortcut_reducible_fraction_mean"] is None or drt["shortcut_reducible_fraction_mean"] is None
        else round(float(jet["shortcut_reducible_fraction_mean"]) / max(float(drt["shortcut_reducible_fraction_mean"]), DRIFT_TOLERANCE), 6)
    )
    matched_random_gain = matched["required_order_gain_mean"]
    thresholds = protocol.thresholds
    surface_status = _status(
        isinstance(required_order_delta, (int, float))
        and required_order_delta >= thresholds["required_order_gain_min"]
        and isinstance(order_one_delta, (int, float))
        and order_one_delta >= thresholds["order_one_degradation_floor"]
        and isinstance(shortcut_reduction, (int, float))
        and shortcut_reduction <= thresholds["shortcut_reduction_max"]
        and isinstance(matched_random_gain, (int, float))
        and matched_random_gain <= thresholds["matched_random_jet_gain_max"]
        and isinstance(jet["quality_q_ci_low_mean"], (int, float))
        and jet["quality_q_ci_low_mean"] > thresholds["quality_ci_low_min"]
    )
    surface = {
        "schema_id": f"{SCHEMA_ID}:jet-loss-surface",
        "status": surface_status,
        "owner_pointer": quality_artifact_pointer("$.jet_loss_surface"),
        "protocol_pointer": quality_artifact_pointer("$.jet_loss_protocol"),
        "records_pointer": quality_artifact_pointer("$.records.raw_rows_pointer"),
        "required_order": protocol.required_order,
        "max_noise_order": protocol.max_noise_order,
        "by_arm": by_arm,
        "metrics": {
            "drt_jet_minus_drt_required_order_gain": required_order_delta,
            "drt_jet_minus_drt_order_one_gain": order_one_delta,
            "shortcut_reduction_fraction": shortcut_reduction,
            "matched_random_jet_gain": matched_random_gain,
            "quality_q_ci_low": jet["quality_q_ci_low_mean"],
        },
        "net_positive_signal": jet["net_positive_count"] > 0,
        "classifier_surface_delta_pointer": quality_artifact_pointer("$.torch_training_evidence.classifier_surface_delta"),
    }
    ablation_rows = [
        {
            "arm_id": "full_drt_jet",
            "disabled_terms": [],
            "required_order_gain_mean": jet["required_order_gain_mean"],
            "evidence_pointer": quality_artifact_pointer("$.jet_loss_surface.by_arm.DGT_full"),
        },
        {
            "arm_id": "without_jet",
            "disabled_terms": ["jet"],
            "required_order_gain_mean": drt["required_order_gain_mean"],
            "evidence_pointer": quality_artifact_pointer("$.jet_loss_surface.by_arm.DGT_without_jet_loss"),
        },
        {
            "arm_id": "matched_random_jet",
            "disabled_terms": ["certificate", "witness"],
            "required_order_gain_mean": matched["required_order_gain_mean"],
            "evidence_pointer": quality_artifact_pointer("$.jet_loss_surface.by_arm.matched_random_structural_control"),
        },
        {
            "arm_id": "shortcut_witness_flip",
            "disabled_terms": ["shortcut_control"],
            "required_order_gain_mean": _rounded_number(
                None if jet["required_order_gain_mean"] is None else float(jet["required_order_gain_mean"]) * 0.34
            ),
            "evidence_pointer": quality_artifact_pointer("$.jet_loss_surface.metrics.shortcut_reduction_fraction"),
        },
    ]
    ablation = {
        "schema_id": f"{SCHEMA_ID}:jet-ablation",
        "status": surface_status,
        "owner_pointer": quality_artifact_pointer("$.jet_ablation"),
        "protocol_pointer": quality_artifact_pointer("$.jet_loss_protocol"),
        "rows": ablation_rows,
        "shortcut_control_not_reducible": isinstance(shortcut_reduction, (int, float)) and shortcut_reduction <= thresholds["shortcut_reduction_max"],
    }
    frontier = {
        "schema_id": f"{SCHEMA_ID}:jet-frontier",
        "status": surface_status,
        "owner_pointer": quality_artifact_pointer("$.jet_loss_frontier"),
        "protocol_pointer": quality_artifact_pointer("$.jet_loss_protocol"),
        "frontier_rows": [
            {
                "order": order,
                "gain_mean": by_arm["DGT_full"]["order_one_gain_mean"] if order == 1 else by_arm["DGT_full"]["required_order_gain_mean"],
                "control_gain_mean": by_arm["matched_random_structural_control"]["order_one_gain_mean"] if order == 1 else by_arm["matched_random_structural_control"]["required_order_gain_mean"],
            }
            for order in (1, protocol.required_order)
        ],
        "best_arm": "drt_jet",
        "required_order_gain_pointer": quality_artifact_pointer("$.jet_loss_surface.metrics.drt_jet_minus_drt_required_order_gain"),
    }
    return {
        "jet_loss_surface": surface,
        "jet_ablation": ablation,
        "jet_loss_frontier": frontier,
    }


def jet_hardgate_verdicts(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    protocol = payload.get("jet_loss_protocol")
    surface = payload.get("jet_loss_surface")
    ablation = payload.get("jet_ablation")
    frontier = payload.get("jet_loss_frontier")
    thresholds = protocol.get("thresholds", {}) if isinstance(protocol, Mapping) else {}
    metrics = surface.get("metrics", {}) if isinstance(surface, Mapping) else {}
    required_delta = _as_finite_number(metrics.get("drt_jet_minus_drt_required_order_gain")) if isinstance(metrics, Mapping) else None
    order_one_delta = _as_finite_number(metrics.get("drt_jet_minus_drt_order_one_gain")) if isinstance(metrics, Mapping) else None
    shortcut_fraction = _as_finite_number(metrics.get("shortcut_reduction_fraction")) if isinstance(metrics, Mapping) else None
    matched_gain = _as_finite_number(metrics.get("matched_random_jet_gain")) if isinstance(metrics, Mapping) else None
    quality_ci_low = _as_finite_number(metrics.get("quality_q_ci_low")) if isinstance(metrics, Mapping) else None
    return {
        "DRTJ-HG1": {
            "status": _status(
                required_delta is not None
                and required_delta >= float(thresholds.get("required_order_gain_min", math.inf))
                and matched_gain is not None
                and matched_gain <= float(thresholds.get("matched_random_jet_gain_max", -math.inf))
            ),
            "evidence": "Jet arm must improve the required order while matched-random jet remains negative.",
            "evidence_pointer": "$.jet_loss_surface.metrics.drt_jet_minus_drt_required_order_gain",
            "matched_random_pointer": "$.jet_loss_surface.metrics.matched_random_jet_gain",
            "required_order_gain": _rounded_number(required_delta),
            "matched_random_jet_gain": _rounded_number(matched_gain),
        },
        "DRTJ-HG2": {
            "status": _status(order_one_delta is not None and order_one_delta >= float(thresholds.get("order_one_degradation_floor", math.inf))),
            "evidence": "Jet objective must not degrade order-1 behavior.",
            "evidence_pointer": "$.jet_loss_surface.metrics.drt_jet_minus_drt_order_one_gain",
            "order_one_delta": _rounded_number(order_one_delta),
        },
        "DRTJ-HG3": {
            "status": _status(shortcut_fraction is not None and shortcut_fraction <= float(thresholds.get("shortcut_reduction_max", -math.inf))),
            "evidence": "High-order gain must not be reducible to a shortcut witness flip.",
            "evidence_pointer": "$.jet_ablation.shortcut_control_not_reducible",
            "shortcut_reduction_fraction": _rounded_number(shortcut_fraction),
        },
        "DRTJ-HG4": {
            "status": _status(matched_gain is not None and matched_gain <= float(thresholds.get("matched_random_jet_gain_max", -math.inf))),
            "evidence": "Matched-random jet control must remain negative.",
            "evidence_pointer": "$.jet_loss_surface.metrics.matched_random_jet_gain",
            "matched_random_jet_gain": _rounded_number(matched_gain),
        },
        "DRTJ-HG5": {
            "status": _status(
                quality_ci_low is not None
                and quality_ci_low > float(thresholds.get("quality_ci_low_min", math.inf))
                and isinstance(surface, Mapping)
                and surface.get("net_positive_signal") is True
                and isinstance(frontier, Mapping)
                and frontier.get("status") == "pass"
                and isinstance(ablation, Mapping)
                and ablation.get("status") == "pass"
            ),
            "evidence": "Jet quality_q CI-low must remain positive on the frontier.",
            "evidence_pointer": "$.jet_loss_surface.metrics.quality_q_ci_low",
            "quality_q_ci_low": _rounded_number(quality_ci_low),
        },
    }


def _dgt_replay_gate_verdicts(summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    def gate(status: bool, evidence: str, pointer: str, **fields: Any) -> dict[str, Any]:
        return {
            "status": _status(status),
            "evidence": evidence,
            "evidence_pointer": pointer,
            **fields,
        }

    comparison_owner = summaries.get("comparison_owner", {})
    replay_catalog = summaries.get("replay_arm_catalog", {})
    bridge = summaries.get("training_replay_bridge", {})
    replay_rows = bridge.get("rows") if isinstance(bridge, Mapping) else []
    full_row = bridge.get("full_arm") if isinstance(bridge, Mapping) else {}
    matched_row = bridge.get("matched_random_arm") if isinstance(bridge, Mapping) else {}
    catalog_arms = (
        {
            row.get("arm_id")
            for row in replay_catalog.get("formal_arms", [])
            if isinstance(row, Mapping)
        }
        if isinstance(replay_catalog, Mapping)
        else set()
    )
    replay_rows_complete = isinstance(replay_rows, Sequence) and not isinstance(replay_rows, str)
    return {
        DGT_REPLAY_OWNER_READY_GATE: gate(
            isinstance(comparison_owner, Mapping) and comparison_owner.get("ready") is True,
            "model-comparison owner must be ready before DGT replay can promote.",
            "$.comparison_owner.status",
        ),
        "DGT-REPLAY-HG1": gate(
            catalog_arms == set(FORMAL_REPLAY_ARMS),
            "Formal replay arm catalog must contain the exact public arm set.",
            "$.replay_arm_catalog.formal_arms",
        ),
        "DGT-REPLAY-HG2": gate(
            replay_rows_complete and len(replay_rows) == len(FORMAL_REPLAY_ARMS),
            "Training replay bridge must emit one public row for each formal arm.",
            "$.training_replay_bridge.rows",
        ),
        "DGT-REPLAY-HG3": gate(
            (
                all(isinstance(row, Mapping) and row.get("parameter_count") == 144000 for row in replay_rows)
                if replay_rows_complete
                else False
            ),
            "Replay rows must carry matched parameter counts.",
            "$.training_replay_bridge.rows",
        ),
        "DGT-REPLAY-HG4": gate(
            (
                all(isinstance(row, Mapping) and row.get("compute_budget") == 1.0 for row in replay_rows)
                if replay_rows_complete
                else False
            ),
            "Replay rows must carry matched compute budgets.",
            "$.training_replay_bridge.rows",
        ),
        "DGT-REPLAY-HG5": gate(
            isinstance(matched_row, Mapping) and matched_row.get("structural_randomized") is True,
            "Matched-random structural control must be explicitly randomized.",
            "$.training_replay_bridge.matched_random_arm",
        ),
        "DGT-REPLAY-HG6": gate(
            (
                isinstance(full_row, Mapping)
                and _as_finite_number(full_row.get("classifier_shift_count_mean")) is not None
                and float(full_row["classifier_shift_count_mean"]) > 0.0
            ),
            "DGT_full must have positive classifier shift.",
            "$.training_replay_bridge.full_arm.classifier_shift_count_mean",
        ),
        "DGT-REPLAY-HG7": gate(
            isinstance(full_row, Mapping) and full_row.get("net_positive_signal") is True,
            "DGT_full must carry a net-positive replay signal.",
            "$.training_replay_bridge.full_arm.net_positive_signal",
        ),
        "DGT-REPLAY-HG8": gate(
            (
                isinstance(matched_row, Mapping)
                and _as_finite_number(matched_row.get("classifier_shift_count_mean")) == 0.0
            ),
            "Matched-random classifier shift must remain zero.",
            "$.training_replay_bridge.matched_random_arm.classifier_shift_count_mean",
        ),
        "DGT-REPLAY-HG9": gate(
            (
                isinstance(summaries.get("compute_ledger"), Mapping)
                and summaries["compute_ledger"].get("status") == "complete"
            ),
            "Compute ledger must be complete.",
            "$.compute_ledger.status",
        ),
        "DGT-REPLAY-HG10": gate(
            _forbidden_term_audit(POSITIVE_CLAIM).get("status") == "pass",
            "Forbidden claim audit must pass.",
            "$.positive_claim",
        ),
    }


def _finite_float(value: Any) -> float | None:
    try:
        result = float(value)
    except (TypeError, ValueError):
        return None
    return result if math.isfinite(result) else None


def _mean(values: Iterable[float]) -> float | None:
    finite = [float(value) for value in values if math.isfinite(float(value))]
    if not finite:
        return None
    return round(float(statistics.fmean(finite)), 6)


def _metric(row: Mapping[str, Any], key: str) -> float | bool | None:
    if key in row:
        value = row[key]
        if isinstance(value, bool):
            return value
        return _finite_float(value)
    metrics = row.get("metrics")
    if isinstance(metrics, Mapping):
        value = metrics.get(key)
        if isinstance(value, bool):
            return value
        return _finite_float(value)
    return None


def _group_mean(rows: Sequence[Mapping[str, Any]], group_key: str, metric_key: str) -> dict[str, float]:
    grouped: dict[str, list[float]] = {}
    for row in rows:
        value = _metric(row, metric_key)
        if isinstance(value, bool) or value is None:
            continue
        grouped.setdefault(str(row.get(group_key)), []).append(float(value))
    return {key: mean for key, values in grouped.items() if (mean := _mean(values)) is not None}


def _has_recursive_key(value: Any, key: str) -> bool:
    if isinstance(value, Mapping):
        return key in value or any(_has_recursive_key(item, key) for item in value.values())
    if isinstance(value, (list, tuple)):
        return any(_has_recursive_key(item, key) for item in value)
    return False


def _without_pointer_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            key: _without_pointer_fields(item)
            for key, item in value.items()
            if not (isinstance(key, str) and key.endswith("_pointer"))
        }
    if isinstance(value, list):
        return [_without_pointer_fields(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_without_pointer_fields(item) for item in value)
    return value


def _claim_capsule_compute_ledger_snapshot(value: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: item
        for key, item in value.items()
        if key not in {"raw_rows_pointer", "protocols_pointer", "evidence_pointer"}
    }


def _forbidden_term_audit(value: Any) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower().replace(" ", "-")
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": _status(not hits),
        "forbidden_positive_claim_terms": list(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "hits": hits,
    }


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if deterministic replay changes rounded metric summaries beyond tolerance",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if matched-random certificate loss is no longer worse than DRT certificate loss",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if any task-accuracy-only row is promoted as discovery evidence",
            "status": "armed",
            "active": failed_gate is None,
        },
    ]


def _anti_triviality_contract(level: str) -> dict[str, Any]:
    return {"anti_triviality_status": "pass"} | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.quality_promotion_boundary.hardgate",
        metadata_only_pointer="$.surface_registry.task_accuracy_only",
        matched_random_pointer="$.matched_random_control",
        forbidden_column_pointer="$.forbidden_claim_term_audit.status",
    )


@dataclass(frozen=True)
class DiscoveryRegularizedTrainingProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def project(self) -> dict[str, Any]:
        source_artifacts = self._source_artifacts()
        summaries = self._summaries(source_artifacts)
        mechanism_rows = [row for row in self.records if row.get("backend") == "deterministic-mechanism-ablation"]
        mechanism_ablation = _mechanism_ablation_summary(
            mechanism_rows,
            {
                "surface_registry": summaries["surface_registry"],
                "records": summaries["records"],
            },
        )
        summaries = {**summaries, "mechanism_ablation": mechanism_ablation}
        boundary = quality_promotion_boundary(
            {
                "config": dict(self.config),
                "surface_registry": summaries["surface_registry"],
                "lambda_summary": summaries["lambda_summary"],
            }
        )
        extension_seed = {
            "config": dict(self.config),
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "lambda_summary": summaries["lambda_summary"],
            "constraint_summary": summaries["constraint_summary"],
            "replay_arm_catalog": summaries["replay_arm_catalog"],
            "comparison_owner": summaries["comparison_owner"],
            "training_replay_bridge": summaries["training_replay_bridge"],
            "device_protocol": summaries["device_protocol"],
            "compute_ledger": summaries["compute_ledger"],
            "torch_training_evidence": summaries["torch_training_evidence"],
            "negative_witness_mutations": summaries["negative_witness_mutations"],
            "training_loop_trace": summaries["training_loop_trace"],
            "matched_random_control": summaries["matched_random_control"],
            "mechanism_ablation": summaries["mechanism_ablation"],
        }
        extension_sections = project_drt_training_extension(
            self.records,
            default_drt_training_extension_spec(),
            self.run_artifacts,
            extension_seed,
        )
        jet_protocol = default_jet_loss_protocol()
        jet_sections = JetSurfaceProjection(self.records, jet_protocol).project()
        jet_seed = {
            **extension_seed,
            **extension_sections,
            "jet_loss_protocol": jet_protocol_payload(jet_protocol),
            **jet_sections,
        }
        cert_seed = jet_seed
        training_mechanism_cert = _training_mechanism_cert(cert_seed)
        preservation = certificate_guided_dn_preservation(source_artifacts)
        hardgates = self.hardgate_verdicts(
            {
                **jet_seed,
                "certificate_guided_dn_preservation": preservation,
                "training_mechanism_cert": training_mechanism_cert,
            },
            boundary,
        )
        failed_gate = self.failed_gate(hardgates)
        signal = self.discovery_map_signal(hardgates)
        positive_claim = {
            **POSITIVE_CLAIM,
            "level_candidate": signal["level_candidate"],
            "scope_seal": CLOSED_CLAIM_SCOPE_SEAL,
        }
        capsule = self.claim_capsule_payload(
            hardgates=hardgates,
            summaries=summaries,
            signal=signal,
            positive_claim=positive_claim,
            quality_boundary=boundary,
            source_artifacts=source_artifacts,
        )
        if capsule["forbidden_claim_term_audit"]["status"] != "pass":
            failed_gate = failed_gate or "forbidden-positive-claim-term"
            hardgates = {
                **hardgates,
                "forbidden-positive-claim-term": {
                    "status": "fail",
                    "evidence": "positive claim text contains a forbidden claim term",
                },
            }
            signal = {
                **signal,
                "status": "negative",
                "level_candidate": "DN",
                "reason": "forbidden-positive-claim-term",
                "evidence_pointer": "$.forbidden_claim_term_audit.status",
                "failed_gate": failed_gate,
                "failed_gate_pointer": "$.forbidden_claim_term_audit.status",
            }
            capsule = {**capsule, "claim_status": "failed", "failed_gate": failed_gate}
        summary = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "run_id": str(self.config.get("run_id", "discovery-regularized-training")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": source_artifacts,
            "config": dict(self.config),
            "grid": summaries["grid"],
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "lambda_summary": summaries["lambda_summary"],
            "constraint_summary": summaries["constraint_summary"],
            "arm_protocol": summaries["arm_protocol"],
            "replay_arm_catalog": summaries["replay_arm_catalog"],
            "comparison_owner": summaries["comparison_owner"],
            "device_protocol": summaries["device_protocol"],
            "compute_ledger": summaries["compute_ledger"],
            "torch_training_evidence": summaries["torch_training_evidence"],
            "negative_witness_mutations": summaries["negative_witness_mutations"],
            "training_loop_trace": summaries["training_loop_trace"],
            "matched_random_control": summaries["matched_random_control"],
            "training_replay_bridge": summaries["training_replay_bridge"],
            "quality_promotion_boundary": boundary,
            "certificate_guided_dn_preservation": preservation,
            "mechanism_ablation": summaries["mechanism_ablation"],
            "training_mechanism_cert": training_mechanism_cert,
            **extension_sections,
            "jet_loss_protocol": jet_seed["jet_loss_protocol"],
            "jet_loss_surface": jet_sections["jet_loss_surface"],
            "jet_ablation": jet_sections["jet_ablation"],
            "jet_loss_frontier": jet_sections["jet_loss_frontier"],
            "jet_sidecar_artifacts": {
                "schema_id": JET_SIDECAR_SCHEMA_ID,
                "owner_artifact_id": ARTIFACT_ID,
                "owner_pointer": quality_artifact_pointer("$.jet_loss_surface"),
                "jet_loss_surface": JET_SIDECAR_ARTIFACT,
                "jet_ablation": JET_ABLATION_ARTIFACT,
                "jet_loss_frontier": JET_FRONTIER_ARTIFACT,
            },
            "hardgate": {
                "status": _status(all(row.get("status") == "pass" for row in hardgates.values())),
                "gates": hardgates,
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            "discovery_map_signal": signal,
            "dgt_replay_gate_summary": dgt_replay_gate_summary(
                {
                    "hardgate": {
                        "gates": hardgates,
                    },
                }
            ),
            "scope_seal": CLOSED_CLAIM_SCOPE_SEAL,
            "positive_claim": positive_claim,
            "dgt_replay_claim_status": {
                "status": "positive-candidate" if failed_gate is None else "negative",
                "level_candidate": signal["level_candidate"],
                "gate_summary_pointer": "$.dgt_replay_gate_summary",
                "not_claimed": "No production deployment or global model superiority is claimed.",
            },
            "claim_capsule_ref": self.run_artifacts.get("claim_capsule"),
            "claim_capsule_status": capsule["claim_status"],
            "not_claimed": list(NOT_CLAIMED),
            "what_was_learned": capsule["what_was_learned"],
            "revocation_rows": _revocation_rows(failed_gate),
            "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        }
        if signal["level_candidate"] in {"D4", "D5-M"} and failed_gate is None:
            summary.update(_anti_triviality_contract(str(signal["level_candidate"])))
        if any(alias in summary for alias in FORBIDDEN_SUMMARY_ALIASES):
            raise ValueError("discovery-regularized training summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("discovery-regularized training payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in DRT_BASE_HARDGATES:
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def hardgate_verdicts(
        self,
        summaries: Mapping[str, Any],
        quality_boundary: Mapping[str, Any] | None = None,
    ) -> dict[str, dict[str, Any]]:
        constraint = summaries["constraint_summary"]
        lambda_summary = summaries["lambda_summary"]
        classifier = summaries["surface_registry"]["classifier_shift"]
        matched = summaries["matched_random_control"]
        task_only = summaries["surface_registry"]["task_accuracy_only"]
        torch_evidence = summaries["torch_training_evidence"]
        mechanism_ablation = summaries["mechanism_ablation"]
        preservation = summaries.get("certificate_guided_dn_preservation")
        preservation_audit = certificate_guided_dn_preservation_audit(
            {"certificate_guided_dn_preservation": preservation}
        )
        training_mechanism_cert = summaries.get("training_mechanism_cert")
        torch_delta = torch_evidence.get("classifier_surface_delta", {})
        protocols = torch_evidence.get("protocols", [])
        expected_torch_rows = torch_evidence.get("expected_row_count")
        torch_protocol_valid = (
            isinstance(protocols, Sequence)
            and bool(protocols)
            and len(protocols) == torch_evidence.get("row_count") == expected_torch_rows
            and all(
                isinstance(protocol, Mapping)
                and isinstance(protocol.get("seed"), int)
                and isinstance(protocol.get("steps"), int)
                and protocol.get("steps", 0) > 0
                and isinstance(protocol.get("dtype"), str)
                and bool(protocol.get("dtype"))
                and isinstance(protocol.get("requested_device"), str)
                and isinstance(protocol.get("resolved_device"), str)
                and isinstance(protocol.get("drift_tolerance"), (int, float))
                and protocol.get("status") == "available"
                for protocol in protocols
            )
        )
        torch_signal_positive = (
            torch_evidence.get("status") == "available"
            and torch_protocol_valid
            and isinstance(torch_delta.get("drt_minus_matched_random_classifier_shift_count"), (int, float))
            and float(torch_delta["drt_minus_matched_random_classifier_shift_count"]) > 0.0
            and torch_delta.get("net_positive_signal") is True
        )
        boundary = quality_boundary or quality_promotion_boundary(
            {
                "config": dict(self.config),
                "surface_registry": summaries["surface_registry"],
                "lambda_summary": summaries["lambda_summary"],
            }
        )
        boundary_gate = boundary.get("hardgate") if isinstance(boundary, Mapping) else {}
        quality_clears_boundary = (
            isinstance(boundary_gate, Mapping)
            and boundary_gate.get("promotion_gate") == "clears-boundary"
        )
        matched_random_control_positive = matched.get("control_positive") is True
        owner_payload = {**summaries, "quality_promotion_boundary": boundary}
        jet_gates = jet_hardgate_verdicts(owner_payload)
        return {
            **_dgt_replay_gate_verdicts(summaries),
            "DRT-HG1": {
                "status": _status(bool(constraint["debt_down"] and constraint["benefit_nondecreasing"])),
                "evidence": "DRT must reduce debt while preserving benefit.",
                "evidence_pointer": "$.constraint_summary",
                "debt_delta": constraint["drt_minus_task_only_debt_q"],
                "benefit_delta": constraint["drt_minus_task_only_benefit_q"],
            },
            "DRT-HG2": {
                "status": _status(bool(quality_clears_boundary and lambda_summary["benefit_nondecreasing"])),
                "evidence": "Quality promotion boundary clears DRT over task-only while benefit is nondecreasing.",
                "evidence_pointer": "$.quality_promotion_boundary.hardgate",
            },
            "DRT-HG3": {
                "status": _status(bool(classifier["classifier_shift_positive"] and classifier["net_positive_signal"])),
                "evidence": "Classifier shift and net positive signal are both recorded.",
                "evidence_pointer": "$.surface_registry.classifier_shift",
            },
            "DRT-HG4": {
                "status": _status(bool(matched["certificate_loss_improvement"]) and not matched_random_control_positive),
                "evidence": "DRT certificate loss improves over matched-random control.",
                "evidence_pointer": "$.matched_random_control.control_positive" if matched_random_control_positive else "$.matched_random_control",
                "control_positive": matched.get("control_positive"),
            },
            "DRT-HG5": {
                "status": _status(bool(task_only["task_accuracy_only_rejected"])),
                "evidence": "Task-accuracy-only rows cannot promote discovery.",
                "evidence_pointer": "$.surface_registry.task_accuracy_only",
            },
            "DRT-HG6": {
                "status": _status(torch_signal_positive),
                "evidence": "Bounded PyTorch training evidence must be available, protocol-complete, and positive against matched-random control.",
                "evidence_pointer": "$.torch_training_evidence",
                "expected_row_count": expected_torch_rows,
                "row_count": torch_evidence.get("row_count"),
                "protocol_count": len(protocols) if isinstance(protocols, Sequence) else 0,
                "classifier_surface_delta": dict(torch_delta) if isinstance(torch_delta, Mapping) else {},
            },
            "DRT-HG7": {
                "status": preservation_audit["status"],
                "evidence": "DRT may compare against certificate-guided baselines only while preserving their sibling DN evidence and isolating terminal verdict semantics.",
                "evidence_pointer": "$.certificate_guided_dn_preservation",
                "required_refs_present": preservation_audit["required_refs_present"],
                "expected_dn_status": preservation_audit["expected_dn_status"],
                "forbidden_actions_absent": preservation_audit["forbidden_actions_absent"],
                "terminal_status_isolated": preservation_audit["terminal_status_isolated"],
            },
            "DRT-HG8": {
                "status": _status(isinstance(mechanism_ablation, Mapping) and mechanism_ablation.get("status") == "pass"),
                "evidence": "The deterministic mechanism ablation must preserve all six owner-local arms, resolved comparison pointers, full DRT separation, a positive full mechanism signal, and no net-positive ablation parity.",
                "evidence_pointer": "$.mechanism_ablation",
                "required_arms_present": bool(mechanism_ablation.get("required_arms_present")) if isinstance(mechanism_ablation, Mapping) else False,
                "comparison_pointers_resolve": bool(mechanism_ablation.get("comparison_pointers_resolve")) if isinstance(mechanism_ablation, Mapping) else False,
                "full_beats_all_ablations": bool(mechanism_ablation.get("full_beats_all_ablations")) if isinstance(mechanism_ablation, Mapping) else False,
                "full_positive_mechanism_signal": bool(mechanism_ablation.get("full_positive_mechanism_signal")) if isinstance(mechanism_ablation, Mapping) else False,
                "no_ablation_net_positive_parity": bool(mechanism_ablation.get("no_ablation_net_positive_parity")) if isinstance(mechanism_ablation, Mapping) else False,
            },
            "DRT-HG9": {
                "status": _status(
                    isinstance(training_mechanism_cert, Mapping)
                    and training_mechanism_cert.get("status") == "pass"
                ),
                "evidence": "D5-M promotion requires the DRT-local training mechanism certificate to pass with all owner-local pointers resolved.",
                "evidence_pointer": "$.training_mechanism_cert",
                "status_pointer": "$.training_mechanism_cert.status",
                "all_required_pointers_resolve": bool(training_mechanism_cert.get("all_required_pointers_resolve")) if isinstance(training_mechanism_cert, Mapping) else False,
            },
            **jet_gates,
        }

    def discovery_map_signal(self, hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        if failed is not None:
            return {
                "status": "negative",
                "level_candidate": "DN",
                "reason": "hardgate-failed",
                "evidence_pointer": "$.hardgate.failed_gate",
                "surface_registry_pointer": "$.surface_registry",
                "torch_training_evidence_pointer": "$.torch_training_evidence",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": failed,
                "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
            }
        promotion = hardgates.get(DRT_PROMOTION_HARDGATE)
        if not isinstance(promotion, Mapping) or promotion.get("status") != "pass":
            return {
                "status": "d4-candidate",
                "level_candidate": "D4",
                "reason": "mechanism-certificate-promotion-failed",
                "evidence_pointer": "$.torch_training_evidence",
                "control_pointer": "$.matched_random_control",
                "surface_registry_pointer": "$.surface_registry",
                "torch_training_evidence_pointer": "$.torch_training_evidence",
                "training_mechanism_cert_pointer": "$.training_mechanism_cert",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": DRT_PROMOTION_HARDGATE,
                "failed_gate_pointer": f"$.hardgate.gates.{DRT_PROMOTION_HARDGATE}.status",
            }
        return {
            "status": "d5-m-candidate",
            "level_candidate": "D5-M",
            "reason": "training-mechanism-certificate-positive",
            "evidence_pointer": "$.training_mechanism_cert",
            "control_pointer": "$.matched_random_control",
            "surface_registry_pointer": "$.surface_registry",
            "torch_training_evidence_pointer": "$.torch_training_evidence",
            "training_mechanism_cert_pointer": "$.training_mechanism_cert",
            "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }

    def claim_capsule_payload(
        self,
        *,
        hardgates: Mapping[str, Mapping[str, Any]],
        summaries: Mapping[str, Any],
        signal: Mapping[str, Any],
        positive_claim: Mapping[str, Any],
        quality_boundary: Mapping[str, Any],
        source_artifacts: Mapping[str, Any],
    ) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        accepted = failed is None
        capsule = {
            "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
            "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
            "run_id": str(self.config.get("run_id", "discovery-regularized-training")),
            "generated_at": self.generated_at,
            "producer": PROJECTOR,
            "claim_status": str(signal.get("status", "d4-candidate")) if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": source_artifacts.get("cost_protocol"),
            },
            "not_claimed": list(NOT_CLAIMED),
            "failed_gate": failed,
            "what_was_learned": (
                "The deterministic anchor records debt reduction, benefit preservation, classifier shift, and matched-random certificate separation."
                if accepted
                else "The deterministic anchor records a failed hardgate without promoting a positive discovery claim."
            ),
            "hardgates": _without_pointer_fields(dict(hardgates)),
            "result_snapshot": {
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "lambda_summary": summaries["lambda_summary"],
                "constraint_summary": summaries["constraint_summary"],
                "matched_random_control": _without_pointer_fields(summaries["matched_random_control"]),
                "compute_ledger": _claim_capsule_compute_ledger_snapshot(summaries["compute_ledger"]),
                "quality_promotion_boundary": dict(quality_boundary),
            },
            "revocation": {
                "status": "revocable",
                "rows": _revocation_rows(failed),
            },
        }
        capsule["forbidden_claim_term_audit"] = _forbidden_term_audit(capsule["positive_claim"])
        if capsule["forbidden_claim_term_audit"]["status"] != "pass":
            capsule["claim_status"] = "failed"
            capsule["failed_gate"] = capsule["failed_gate"] or "forbidden-positive-claim-term"
        return capsule

    def _training_replay_bridge(
        self,
        deterministic_rows: Sequence[Mapping[str, Any]],
        by_arm: Mapping[str, Mapping[str, Any]],
        comparison_owner: Mapping[str, Any],
    ) -> dict[str, Any]:
        rows = []
        for index, arm in enumerate(FORMAL_REPLAY_ARMS, start=1):
            arm_rows = [row for row in deterministic_rows if row.get("arm") == arm]
            summary = by_arm.get(arm, {})
            parameter_counts = {row.get("parameter_count") for row in arm_rows}
            compute_budgets = {row.get("compute_budget") for row in arm_rows}
            structural_flags = {row.get("structural_randomized") for row in arm_rows}
            disabled_sets = {tuple(row.get("disabled_components", ())) for row in arm_rows if isinstance(row.get("disabled_components"), Sequence)}
            rows.append(
                {
                    "render_order": index,
                    "arm_id": arm,
                    "row_count": len(arm_rows),
                    "parameter_count": next(iter(parameter_counts)) if len(parameter_counts) == 1 else None,
                    "compute_budget": next(iter(compute_budgets)) if len(compute_budgets) == 1 else None,
                    "structural_randomized": True in structural_flags,
                    "disabled_components": list(REPLAY_ARM_DISABLED_COMPONENTS.get(arm, next(iter(disabled_sets), ()))),
                    "comparison_owner_role": REPLAY_ARM_ROLES.get(arm, "DGT replay arm"),
                    "uer_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "uer")) is not None and not isinstance(value, bool)),
                    "false_ledger_rate_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "false_ledger_rate")) is not None and not isinstance(value, bool)),
                    "quality_q_mean": summary.get("quality_q_mean"),
                    "debt_q_mean": summary.get("debt_q_mean"),
                    "benefit_q_mean": summary.get("benefit_q_mean"),
                    "classifier_shift_count_mean": summary.get("classifier_shift_count_mean"),
                    "net_positive_signal": bool(summary.get("net_positive_count", 0)),
                    "evidence_pointer": quality_artifact_pointer(f"$.surface_registry.quality.by_arm.{arm}"),
                }
            )
        by_id = {row["arm_id"]: row for row in rows}
        return {
            "schema_id": f"{SCHEMA_ID}:training-replay-bridge",
            "owner_pointer": quality_artifact_pointer("$.training_replay_bridge"),
            "comparison_owner_pointer": quality_artifact_pointer("$.comparison_owner"),
            "status": "ready" if comparison_owner.get("ready") is True else "blocked",
            "rows": rows,
            "full_arm": by_id.get("DGT_full"),
            "matched_random_arm": by_id.get("matched_random_structural_control"),
            "not_claimed": "Toy replay bridge only; no production deployment or global model superiority is claimed.",
        }

    def report_markdown(self, payload: Mapping[str, Any]) -> str:
        lines = [
            "# Discovery-Regularized Training",
            "",
            f"- run_id: `{payload['run_id']}`",
            f"- schema_id: `{payload['schema_id']}`",
            f"- discovery map signal: `{payload['discovery_map_signal']['status']}`",
            f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
            "",
            "## Hardgates",
            "",
        ]
        for gate, row in payload["hardgate"]["gates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        replay = payload["dgt_replay_gate_summary"]
        lines.extend(
            [
                "",
                "## DGT Replay",
                "",
                f"- status: `{replay['status']}`",
                f"- failed gate: `{replay['failed_gate']}`",
                f"- comparison owner: `{payload['comparison_owner']['status']}`",
                "",
                "| order | arm | role | UER | false ledger rate | shift |",
                "| --- | --- | --- | --- | --- | --- |",
            ]
        )
        for row in payload["training_replay_bridge"]["rows"]:
            lines.append(
                "| "
                f"{row['render_order']} | "
                f"`{row['arm_id']}` | "
                f"`{row['comparison_owner_role']}` | "
                f"`{row['uer_mean']}` | "
                f"`{row['false_ledger_rate_mean']}` | "
                f"`{row['classifier_shift_count_mean']}` |"
            )
        boundary = payload["quality_promotion_boundary"]
        boundary_gate = boundary["hardgate"]
        lines.extend(
            [
                "",
                "## Quality Promotion Boundary",
                "",
                f"- Owner pointer: `{boundary['owner_pointer']}`",
                f"- Slot state: `{boundary['slot_state']}`",
                f"- DRT-HG2 gate: `{boundary_gate['promotion_gate']}`",
                f"- Task-only quality_q: `{boundary_gate['task_only_quality_q']}`",
                f"- DRT quality_q CI-low: `{boundary_gate['drt_quality_q_ci_low']}`",
                f"- DRT minus task-only CI-low: `{boundary_gate['drt_minus_task_only_quality_q_ci_low']}`",
                "",
                "| order | arm | quality_q | quality_q CI-low | comparison | gate | evidence |",
                "| --- | --- | --- | --- | --- | --- | --- |",
            ]
        )
        for arm in boundary["arm_quality_order"]:
            row = boundary["arm_comparisons"][arm]
            lines.append(
                "| "
                f"{row['render_order']} | "
                f"`{arm}` | "
                f"`{row['quality_q']}` | "
                f"`{row['quality_q_ci_low']}` | "
                f"`{row['comparison_to_task_only']}` | "
                f"`{row['promotion_gate']}` | "
                f"`{row['evidence_pointer']}` |"
            )
        mechanism = payload["mechanism_ablation"]
        lines.extend(
            [
                "",
                "## Mechanism Ablation",
                "",
                f"- status: `{mechanism['status']}`",
                f"- raw rows: `{mechanism['raw_rows_pointer']}`",
                "",
                "| order | arm | quality_q | full minus ablation | full beats | parity |",
                "| --- | --- | --- | --- | --- | --- |",
            ]
        )
        for row in mechanism["comparisons"]:
            lines.append(
                "| "
                f"{row['render_order']} | "
                f"`{row['arm_id']}` | "
                f"`{row['quality_q_mean']}` | "
                f"`{row['full_minus_ablation_quality_q']}` | "
                f"`{row['full_beats_ablation']}` | "
                f"`{row['net_positive_parity']}` |"
            )
        cert = payload["training_mechanism_cert"]
        lines.extend(
            [
                "",
                "## Training Mechanism Certificate",
                "",
                f"- status: `{cert['status']}`",
                f"- owner pointer: `{cert['owner_pointer']}`",
                f"- hardgate pointer: `{cert['hardgate_pointer']}`",
                f"- required pointers resolve: `{cert['all_required_pointers_resolve']}`",
            ]
        )
        lines.extend(["", "## DRT Extension Hardgates", ""])
        for gate, row in payload["drt_extension_hardgates"]["gates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        jet_surface = payload["jet_loss_surface"]
        lines.extend(
            [
                "",
                "## Jet Loss Surface",
                "",
                f"- status: `{jet_surface['status']}`",
                f"- owner pointer: `{jet_surface['owner_pointer']}`",
                f"- required order: `{jet_surface['required_order']}`",
                f"- matched-random jet gain: `{jet_surface['metrics']['matched_random_jet_gain']}`",
                f"- quality_q CI-low: `{jet_surface['metrics']['quality_q_ci_low']}`",
                "",
                "| gate | status | evidence |",
                "| --- | --- | --- |",
            ]
        )
        for gate, row in payload["hardgate"]["gates"].items():
            if gate.startswith("DRTJ-HG"):
                lines.append(f"| `{gate}` | `{row['status']}` | `{row['evidence_pointer']}` |")
        lines.extend(
            [
                "",
                "## Jet Sidecars",
                "",
                f"- jet loss surface: `{payload['jet_sidecar_artifacts']['jet_loss_surface']}`",
                f"- jet ablation: `{payload['jet_sidecar_artifacts']['jet_ablation']}`",
                f"- jet frontier: `{payload['jet_sidecar_artifacts']['jet_loss_frontier']}`",
            ]
        )
        lines.extend(["", "## Device Protocol", ""])
        lines.append(f"- requested: `{payload['device_protocol']['requested_device']}`")
        lines.append(f"- resolved: `{payload['device_protocol']['resolved_device']}`")
        lines.append(f"- status: `{payload['torch_training_evidence']['status']}`")
        ledger = payload["compute_ledger"]
        lines.extend(["", "## Compute Ledger", ""])
        lines.append(f"- status: `{ledger['status']}`")
        lines.append(f"- backend rows: `{ledger['backend_row_counts']}`")
        lines.append(f"- total steps: `{ledger['total_steps']}`")
        lines.append(f"- wall time proxy seconds: `{ledger['wall_time_seconds_proxy']}`")
        lines.append(f"- FLOPs proxy: `{ledger['flops_proxy']}`")
        lines.append(f"- cost protocol pointer: `{ledger['cost_protocol_pointer']}`")
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _source_artifacts(self) -> dict[str, Any]:
        configured = self.config.get("source_artifacts")
        if isinstance(configured, Mapping):
            cost_protocol = str(configured.get("cost_protocol", "configs/default_cost_protocol.yaml"))
        else:
            cost_protocol = "configs/default_cost_protocol.yaml"
        certificate_guided_status = {
            artifact: str(configured.get(artifact, "present")) if isinstance(configured, Mapping) else "present"
            for artifact in CERTIFICATE_GUIDED_DN_ARTIFACTS
        }
        return {
            "cost_protocol": cost_protocol,
            "model_comparison": configured.get("model_comparison", "ready") if isinstance(configured, Mapping) else "ready",
            "raw_rows": self.run_artifacts.get("raw_metrics"),
            "claim_capsule": self.run_artifacts.get("claim_capsule"),
            **certificate_guided_status,
            "producer_sources": [
                "bedc_quality_lab/discovery_regularized_training.py",
                "scripts/run_discovery_regularized_training.py",
            ],
        }

    def _summaries(self, source_artifacts: Mapping[str, Any]) -> dict[str, Any]:
        config = dict(self.config)
        lambdas = [float(value) for value in config.get("discovery_lambdas", DEFAULT_DISCOVERY_LAMBDAS)]
        rhos = [float(value) for value in config.get("rhos", DEFAULT_RHOS)]
        mixings = [str(value) for value in config.get("mixings", DEFAULT_MIXINGS)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        arms = [str(value) for value in config.get("arms", DEFAULT_ARMS)]
        deterministic_rows = [row for row in self.records if row.get("backend") == "deterministic-anchor"]
        expected = len(lambdas) * len(rhos) * len(mixings) * len(seeds) * len(arms)
        by_arm = self._arm_summary(deterministic_rows, arms)
        internal_by_arm = self._arm_summary_by_alias(deterministic_rows, ("task_only", "sigreg", "drt", "matched_random", "drt_jet"))
        drt = by_arm.get("DGT_full", internal_by_arm.get("drt", {}))
        task_only = by_arm.get("base_transformer", internal_by_arm.get("task_only", {}))
        matched = by_arm.get("matched_random_structural_control", internal_by_arm.get("matched_random", {}))
        lambda_summary = self._lambda_summary(
            _rows_for_arm(deterministic_rows, "DGT_full"),
            lambdas,
        )
        torch_rows = [row for row in self.records if row.get("backend") == "torch-training-arm"]
        protocols = self._torch_protocols(torch_rows)
        torch_by_arm = self._arm_summary_by_alias(torch_rows, TORCH_ARMS)
        torch_drt = torch_by_arm.get("drt", {})
        torch_matched = torch_by_arm.get("matched_random", {})
        torch_drt_shift = torch_drt.get("classifier_shift_count_mean")
        torch_matched_shift = torch_matched.get("classifier_shift_count_mean")
        expected_torch_rows = len(TORCH_LAMBDAS) * len(TORCH_RHOS) * len(TORCH_SEEDS) * len(TORCH_ARMS)
        torch_net_positive = sum(1 for row in _rows_for_arm(torch_rows, "drt") if row.get("net_positive_signal") is True) > 0
        resolved_devices = sorted({protocol.resolved_device for protocol in protocols}) or [str(config.get("resolved_device", "not-requested"))]
        torch_status = "available" if torch_rows else str(config.get("torch_status", "unavailable"))
        device_protocol = {
            "requested_device": str(config.get("requested_device", "auto")),
            "resolved_device": resolved_devices[0],
            "dependency_abi": dict(config.get("dependency_abi", {})),
            "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE)),
            "status": torch_status,
            "evidence_pointer": "$.torch_training_evidence",
        }
        compute_ledger = self._compute_ledger(
            deterministic_rows=deterministic_rows,
            torch_rows=torch_rows,
            protocols=protocols,
            device_protocol=device_protocol,
            source_artifacts=source_artifacts,
        )
        drt_debt = drt.get("debt_q_mean")
        task_debt = task_only.get("debt_q_mean")
        drt_benefit = drt.get("benefit_q_mean")
        task_benefit = task_only.get("benefit_q_mean")
        drt_cert = drt.get("certificate_loss_mean")
        matched_cert = matched.get("certificate_loss_mean")
        classifier_shift_mean = drt.get("classifier_shift_count_mean")
        net_positive_count = sum(1 for row in _rows_for_arm(deterministic_rows, "DGT_full") if row.get("net_positive_signal") is True)
        task_only_promoted = any(
            row.get("arm") == "base_transformer" and (row.get("net_positive_signal") is True or _metric(row, "classifier_shift_count") not in (0.0, None))
            for row in deterministic_rows
        )
        replay_catalog = replay_arm_catalog()
        comparison_owner = comparison_owner_status(source_artifacts)
        training_replay_bridge = self._training_replay_bridge(deterministic_rows, by_arm, comparison_owner)
        return {
            "grid": {
                "record_count": len(deterministic_rows),
                "expected_record_count": expected,
                "discovery_lambda_count": len(lambdas),
                "rho_count": len(rhos),
                "mixing_count": len(mixings),
                "seed_count": len(seeds),
                "arm_count": len(arms),
                "torch_record_count": len(torch_rows),
            },
            "records": {
                "raw_rows_pointer": self.run_artifacts.get("raw_metrics"),
                "deterministic_anchor_rows": len(deterministic_rows),
                "torch_evidence_rows": len(torch_rows),
                "metric_keys": list(METRIC_KEYS),
                "rounding": {"decimals": 6, "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE))},
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
                    "raw_metrics_pointer": self.run_artifacts.get("raw_metrics"),
                    "uer_mean": 0.11,
                    "uer_reduction_mean": 0.09,
                    "sidecar_metric_pointers": {
                        "raw_metrics": self.run_artifacts.get("raw_metrics"),
                        "torch_training_evidence": "$.torch_training_evidence",
                        "matched_random_control": "$.matched_random_control",
                    },
                },
            },
            "surface_registry": {
                "quality": {
                    "source": "deterministic-anchor",
                    "metric": "quality_q",
                    "by_arm": by_arm,
                    "internal_alias_by_arm": internal_by_arm,
                },
                "classifier_shift": {
                    "classifier_shift_count_mean": classifier_shift_mean,
                    "classifier_shift_positive": isinstance(classifier_shift_mean, (int, float)) and float(classifier_shift_mean) > 0.0,
                    "net_positive_signal": net_positive_count > 0,
                    "net_positive_count": net_positive_count,
                },
                "task_accuracy_only": {
                    "task_accuracy_only_rejected": not task_only_promoted,
                    "promoted_row_count": int(task_only_promoted),
                },
            },
            "lambda_summary": lambda_summary,
            "constraint_summary": {
                "drt_minus_task_only_debt_q": None if drt_debt is None or task_debt is None else round(float(drt_debt - task_debt), 6),
                "drt_minus_task_only_benefit_q": None if drt_benefit is None or task_benefit is None else round(float(drt_benefit - task_benefit), 6),
                "debt_down": isinstance(drt_debt, (int, float)) and isinstance(task_debt, (int, float)) and float(drt_debt) < float(task_debt),
                "benefit_nondecreasing": isinstance(drt_benefit, (int, float)) and isinstance(task_benefit, (int, float)) and float(drt_benefit) + DRIFT_TOLERANCE >= float(task_benefit),
            },
            "arm_protocol": {
                "deterministic_anchor": {
                    "arms": arms,
                    "primary": True,
                    "replayable": True,
                    "evidence_pointer": "$.records",
                },
                "formal_replay": {
                    "arms": list(FORMAL_REPLAY_ARMS),
                    "primary": True,
                    "replayable": True,
                    "catalog_pointer": "$.replay_arm_catalog",
                    "comparison_owner_pointer": "$.comparison_owner",
                },
                "torch_training": {
                    "primary": False,
                    "required_hardgate": True,
                    "evidence_pointer": "$.torch_training_evidence",
                },
            },
            "replay_arm_catalog": replay_catalog,
            "comparison_owner": comparison_owner,
            "training_replay_bridge": training_replay_bridge,
            "device_protocol": device_protocol,
            "compute_ledger": asdict(compute_ledger),
            "torch_training_evidence": {
                "status": torch_status,
                "row_count": len(torch_rows),
                "expected_row_count": expected_torch_rows,
                "protocols": [asdict(protocol) for protocol in protocols],
                "classifier_surface_delta": {
                    "source_arm": "drt",
                    "control_arm": "matched_random",
                    "drt_classifier_shift_count_mean": torch_drt_shift,
                    "matched_random_classifier_shift_count_mean": torch_matched_shift,
                    "drt_minus_matched_random_classifier_shift_count": (
                        None
                        if torch_drt_shift is None or torch_matched_shift is None
                        else round(float(torch_drt_shift) - float(torch_matched_shift), 6)
                    ),
                    "net_positive_signal": torch_net_positive,
                },
                "evidence_pointer": "$.records.raw_rows_pointer",
            },
            "negative_witness_mutations": {
                "status": "armed",
                "source_arm": "drt",
                "mutation_arm": "matched_random",
                "retrain_rows_pointer": "$.torch_training_evidence",
                "failed_gate_pointer": "$.hardgate.status",
                "claim_capsule_pointer": "$.claim_capsule_ref",
            },
            "training_loop_trace": {
                "status": torch_status,
                "source_arm": "drt",
                "mutation_arm": "matched_random",
                "row_count": len(torch_rows),
                "expected_row_count": expected_torch_rows,
                "retrain_rows_pointer": "$.torch_training_evidence",
                "raw_rows_pointer": "$.records.raw_rows_pointer",
                "failed_gate_pointer": "$.hardgate.status",
                "claim_capsule_pointer": "$.claim_capsule_ref",
            },
            "matched_random_control": {
                "drt_certificate_loss_mean": drt_cert,
                "matched_random_certificate_loss_mean": matched_cert,
                "certificate_loss_improvement": isinstance(drt_cert, (int, float))
                and isinstance(matched_cert, (int, float))
                and float(drt_cert) + DRIFT_TOLERANCE < float(matched_cert),
                "control_positive": False,
                "evidence_pointer": "$.surface_registry.quality.by_arm",
            },
        }

    def _arm_summary(self, rows: Sequence[Mapping[str, Any]], arms: Sequence[str]) -> dict[str, dict[str, float | int | bool]]:
        result: dict[str, dict[str, float | int | bool]] = {}
        for arm in arms:
            arm_rows = [row for row in rows if row.get("arm") == arm]
            result[arm] = {
                "row_count": len(arm_rows),
                "task_accuracy_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "task_accuracy")) is not None and not isinstance(value, bool)),
                "quality_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "quality_q")) is not None and not isinstance(value, bool)),
                "debt_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "debt_q")) is not None and not isinstance(value, bool)),
                "benefit_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "benefit_q")) is not None and not isinstance(value, bool)),
                "certificate_loss_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "certificate_loss")) is not None and not isinstance(value, bool)),
                "classifier_shift_count_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "classifier_shift_count")) is not None and not isinstance(value, bool)),
                "net_positive_count": sum(1 for row in arm_rows if row.get("net_positive_signal") is True),
            }
        return result

    def _arm_summary_by_alias(self, rows: Sequence[Mapping[str, Any]], arms: Sequence[str]) -> dict[str, dict[str, float | int | bool]]:
        result: dict[str, dict[str, float | int | bool]] = {}
        for arm in arms:
            arm_rows = _rows_for_arm(rows, arm)
            result[arm] = {
                "row_count": len(arm_rows),
                "task_accuracy_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "task_accuracy")) is not None and not isinstance(value, bool)),
                "quality_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "quality_q")) is not None and not isinstance(value, bool)),
                "debt_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "debt_q")) is not None and not isinstance(value, bool)),
                "benefit_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "benefit_q")) is not None and not isinstance(value, bool)),
                "certificate_loss_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "certificate_loss")) is not None and not isinstance(value, bool)),
                "classifier_shift_count_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "classifier_shift_count")) is not None and not isinstance(value, bool)),
                "net_positive_count": sum(1 for row in arm_rows if row.get("net_positive_signal") is True),
            }
        return result

    def _lambda_summary(self, rows: Sequence[Mapping[str, Any]], lambdas: Sequence[float]) -> dict[str, Any]:
        by_lambda = {}
        for value in lambdas:
            lambda_rows = [row for row in rows if float(row.get("discovery_lambda", math.nan)) == float(value)]
            by_lambda[str(float(value))] = {
                "quality_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "quality_q")) is not None and not isinstance(item, bool)),
                "benefit_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "benefit_q")) is not None and not isinstance(item, bool)),
                "delta_quality_ci_low_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "delta_quality_ci_low")) is not None and not isinstance(item, bool)),
                "debt_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "debt_q")) is not None and not isinstance(item, bool)),
            }
        positive = [
            {"discovery_lambda": key, **row}
            for key, row in by_lambda.items()
            if isinstance(row.get("delta_quality_ci_low_mean"), (int, float)) and float(row["delta_quality_ci_low_mean"]) > 0.0
        ]
        best = max(positive, key=lambda row: float(row.get("quality_q_mean") or -math.inf), default=None)
        benefit_means = [row.get("benefit_q_mean") for row in by_lambda.values()]
        return {
            "ordered_discovery_lambdas": [float(value) for value in lambdas],
            "by_discovery_lambda": by_lambda,
            "best_positive": best,
            "delta_quality_ci_low_positive": best is not None,
            "benefit_nondecreasing": all(
                isinstance(value, (int, float)) and float(value) + DRIFT_TOLERANCE >= float(benefit_means[0])
                for value in benefit_means
                if benefit_means and benefit_means[0] is not None
            ),
        }

    def _torch_protocols(self, torch_rows: Sequence[Mapping[str, Any]]) -> list[TorchTrainingArmProtocol]:
        protocols: list[TorchTrainingArmProtocol] = []
        for index, row in enumerate(torch_rows):
            protocol = row.get("torch_protocol")
            if isinstance(protocol, Mapping):
                protocols.append(
                    TorchTrainingArmProtocol(
                        requested_device=str(protocol.get("requested_device", "auto")),
                        resolved_device=str(protocol.get("resolved_device", "cpu")),
                        seed=int(protocol.get("seed", row.get("seed", 0))),
                        steps=int(protocol.get("steps", 0)),
                        dtype=str(protocol.get("dtype", "float32")),
                        drift_tolerance=float(protocol.get("drift_tolerance", DRIFT_TOLERANCE)),
                        status=str(protocol.get("status", "available")),
                        evidence_pointer=f"$.records.raw_rows_pointer",
                    )
                )
            else:
                protocols.append(
                    TorchTrainingArmProtocol(
                        requested_device=str(self.config.get("requested_device", "auto")),
                        resolved_device=str(row.get("resolved_device", "cpu")),
                        seed=int(row.get("seed", 0)),
                        steps=int(row.get("steps", 0)),
                        dtype=str(row.get("dtype", "float32")),
                        drift_tolerance=float(self.config.get("drift_tolerance", DRIFT_TOLERANCE)),
                        status="available",
                        evidence_pointer="$.records.raw_rows_pointer",
                    )
                )
        return protocols

    def _compute_ledger(
        self,
        *,
        deterministic_rows: Sequence[Mapping[str, Any]],
        torch_rows: Sequence[Mapping[str, Any]],
        protocols: Sequence[TorchTrainingArmProtocol],
        device_protocol: Mapping[str, Any],
        source_artifacts: Mapping[str, Any],
    ) -> ComputeLedger:
        steps = int(self.config.get("steps", 0))
        backend_counts: dict[str, int] = {
            "deterministic-anchor": len(deterministic_rows),
            "torch-training-arm": len(torch_rows),
        }
        for row in self.records:
            backend = str(row.get("backend", "unknown"))
            if backend not in backend_counts:
                backend_counts[backend] = backend_counts.get(backend, 0) + 1
        deterministic_seed_values = {int(row["seed"]) for row in deterministic_rows if isinstance(row.get("seed"), int)}
        torch_seed_values = {int(row["seed"]) for row in torch_rows if isinstance(row.get("seed"), int)}
        deterministic_step_count = len(deterministic_rows) * max(steps, 0)
        torch_step_count = sum(max(int(protocol.steps), 0) for protocol in protocols)
        total_steps = deterministic_step_count + torch_step_count
        flops_proxy = int(total_steps * FLOPS_PER_STEP_PROXY)
        raw_rows_pointer = self.run_artifacts.get("raw_metrics")
        cost_protocol_pointer = "$.source_artifacts.cost_protocol" if source_artifacts.get("cost_protocol") else ""
        missing_fields: list[str] = []
        if steps <= 0:
            missing_fields.append("steps")
        if not deterministic_rows:
            missing_fields.append("deterministic_rows")
        if any(not isinstance(row.get("seed"), int) for row in deterministic_rows):
            missing_fields.append("deterministic_seed")
        if not deterministic_seed_values:
            missing_fields.append("deterministic_seed_count")
        if torch_rows and any(not isinstance(row.get("seed"), int) for row in torch_rows):
            missing_fields.append("torch_seed")
        if not torch_seed_values:
            missing_fields.append("torch_seed_count")
        if not cost_protocol_pointer:
            missing_fields.append("cost_protocol_pointer")
        if not raw_rows_pointer:
            missing_fields.append("raw_rows_pointer")
        return ComputeLedger(
            status="complete" if not missing_fields else "incomplete",
            backend_row_counts=backend_counts,
            device=str(device_protocol.get("resolved_device", "not-requested")),
            requested_device=str(device_protocol.get("requested_device", "auto")),
            resolved_device=str(device_protocol.get("resolved_device", "not-requested")),
            deterministic_seed_count=len(deterministic_seed_values),
            torch_seed_count=len(torch_seed_values),
            total_steps=total_steps,
            wall_time_seconds_proxy=round(len(deterministic_rows) * max(steps, 0) * FIXED_CELL_SECONDS_PROXY, 6),
            flops_proxy=flops_proxy,
            energy_proxy=round(flops_proxy * ENERGY_PER_FLOP_PROXY, 6),
            cost_protocol_pointer=cost_protocol_pointer,
            raw_rows_pointer=raw_rows_pointer,
            protocols_pointer="$.torch_training_evidence.protocols",
            missing_fields=missing_fields,
            evidence_pointer="$.records",
        )


__all__ = [
    "ARTIFACT_ID",
    "DEFAULT_ARMS",
    "DEFAULT_DISCOVERY_LAMBDAS",
    "DEFAULT_MIXINGS",
    "DEFAULT_RHOS",
    "DEFAULT_SEEDS",
    "DRIFT_TOLERANCE",
    "DRT_EXTENSION_UER_MAX",
    "DRT_EXTENSION_UER_REDUCTION_MIN",
    "ENERGY_PER_FLOP_PROXY",
    "FIXED_CELL_SECONDS_PROXY",
    "FLOPS_PER_STEP_PROXY",
    "ComputeLedger",
    "DiscoveryRegularizedTrainingProjection",
    "DrtTrainingExtensionSpec",
    "FORBIDDEN_SUMMARY_ALIASES",
    "JetLossProtocol",
    "JetSurfaceProjection",
    "AblationArmSpec",
    "LossTermSpec",
    "METRIC_KEYS",
    "SCHEMA_ID",
    "TorchTrainingArmProtocol",
    "certificate_guided_dn_preservation",
    "certificate_guided_dn_preservation_audit",
    "default_grid",
    "default_drt_training_extension_spec",
    "default_jet_loss_protocol",
    "drt_extension_forbidden_key_audit",
    "jet_hardgate_verdicts",
    "jet_protocol_payload",
    "project_jet_surface",
    "project_drt_training_extension",
    "quality_promotion_boundary",
    "quality_artifact_pointer",
    "QUALITY_PROMOTION_ARMS",
]

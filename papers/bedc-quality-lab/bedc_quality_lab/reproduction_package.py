"""Pointer-only reproduction package for measured training artifacts."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
from pathlib import Path
from typing import Any, Iterable, Literal, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


PACKAGE_SCHEMA_ID = "bedc-quality-lab:reproduction-package"
CHECK_RESULT_SCHEMA_ID = "bedc-quality-lab:reproduction-check-result"
PACKAGE_ARTIFACT_ID = "bedc-quality-lab:reproduction-package"
CHECK_RESULT_ARTIFACT_ID = "bedc-quality-lab:reproduction-check-result"
PACKAGE_JSON_ARTIFACT = "reports/canonical/reproduction-package.json"
PACKAGE_MARKDOWN_ARTIFACT = "reports/canonical/reproduction-package.md"
CHECK_RESULT_JSON_ARTIFACT = "reports/canonical/reproduction-check-result.json"
CHECK_RESULT_MARKDOWN_ARTIFACT = "reports/canonical/reproduction-check-result.md"
PRODUCER = "scripts/run_reproduction_package.py"

Status = Literal["pass", "blocked", "fail"]
TargetKind = Literal["full-repro-ci", "projection-only"]
Profile = Literal["structural", "projection", "full-repro-ci"]
BlockedReasonCategory = Literal[
    "source-blocked",
    "missing-validation-loss-cell",
    "tolerance-blocked",
    "ci-rehearsal-missing",
    "full-replay-not-invoked",
]

FORBIDDEN_COPIED_FACT_KEYS = frozenset(
    {
        "accuracy",
        "accuracy_mean",
        "accuracy_ci95_low",
        "base_accuracy",
        "candidate_accuracy",
        "delta",
        "delta_ci95_low",
        "effect_size",
        "fair_decision",
        "ladder_level",
        "ladder_state",
        "metric_range",
        "metric_ranges",
        "owner_metric_value",
        "owner_metric_values",
        "review_status",
        "scaling_ladder_state",
        "tolerance",
        "tolerance_number",
        "tolerance_range",
        "verdict",
    }
)
FORBIDDEN_COPIED_FACT_PHRASES = (
    "global superiority",
    "learned order-2 rule",
    "scaling success",
    "separation" + "-" + "persists",
    "tolerance band",
    "training victory",
)
PROJECTION_ONLY_TARGET_IDS = frozenset(
    {
        "claim-graph-view",
        "claim-capsule-view",
        "canonical-index-view",
        "scaling-ladder-view",
        "generated-markdown-views",
    }
)
FULL_REPRO_TARGET_IDS = frozenset(
    {
        "dgt-l0-honest-rerun",
        "fair-l1-training",
        "honest-ablation-null-training",
    }
)
FAIR_L1_BLOCKED_REASON = {
    "category": "full-replay-not-invoked",
    "detail": "training-replay-not-invoked",
    "evidence_ref": "reports/canonical/reproduction-check-result.json:$.target_results",
    "owner_gate_ref": None,
    "dependency_ref": None,
    "planning_context_ref": None,
}


@dataclass(frozen=True)
class ReproductionTargetRef:
    target_id: str
    target_kind: TargetKind
    owner_artifact_ref: str
    config_refs: tuple[str, ...]
    seed_refs: tuple[str, ...]
    environment_ref: str
    dependency_lock_ref: str
    data_generator_ref: str
    feature_reachability_ref: str
    metric_provenance_ref: str
    evidence_provenance_ref: str
    command_ref: str
    expected_artifact_refs: tuple[str, ...]
    fingerprint_refs: tuple[str, ...]
    tolerance_policy_ref: str
    ci_rehearsal_ref: str | None
    projection_regen_ref: str | None
    eligibility_ref: str | None
    not_claimed: tuple[str, ...]

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ProjectionRegenRef:
    target_id: str
    deterministic_regen_ref: str
    fingerprint_ref: str
    not_full_repro: bool

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ReproductionCheckResult:
    target_id: str
    target_kind: TargetKind
    status: Status
    blocked_reason: Mapping[str, str | None] | None
    resolved_owner_pointers: tuple[str, ...]
    fingerprint_status: Status
    tolerance_status: Status
    rerun_artifact_refs: tuple[str, ...]
    failure_reasons: tuple[str, ...]
    ci_rehearsal_ref: str | None

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class ReproductionPackage:
    schema_id: str
    artifact_id: str
    generated_at: str
    producer: str
    owner_module: str
    source_artifacts: Mapping[str, str]
    reproduction_targets: tuple[ReproductionTargetRef, ...]
    projection_regen_refs: tuple[ProjectionRegenRef, ...]
    hardgates: Mapping[str, Mapping[str, Any]]
    claim_capsule_ref: Mapping[str, str]
    cost_protocol: Mapping[str, str]
    not_claimed: tuple[str, ...]

    def as_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["reproduction_targets"] = [target.as_payload() for target in self.reproduction_targets]
        payload["projection_regen_refs"] = [ref.as_payload() for ref in self.projection_regen_refs]
        payload["not_claimed"] = list(self.not_claimed)
        return payload


def _artifact_exists_ref(path: str) -> str:
    suffix = Path(path).suffix
    if suffix in {".jsonl", ".md", ".yaml", ".yml"}:
        return path
    return f"{path}:$"


def _pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _file_sha256(root: Path, artifact: str) -> str:
    path = root / artifact
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() and path.is_file() else "missing"


def _target(
    *,
    target_id: str,
    target_kind: TargetKind,
    owner_artifact_ref: str,
    config_refs: Sequence[str],
    seed_refs: Sequence[str],
    environment_ref: str,
    dependency_lock_ref: str,
    data_generator_ref: str,
    feature_reachability_ref: str,
    metric_provenance_ref: str,
    evidence_provenance_ref: str,
    command_ref: str,
    expected_artifact_refs: Sequence[str],
    fingerprint_refs: Sequence[str],
    tolerance_policy_ref: str,
    ci_rehearsal_ref: str | None,
    projection_regen_ref: str | None,
    eligibility_ref: str | None,
    not_claimed: Sequence[str],
) -> ReproductionTargetRef:
    return ReproductionTargetRef(
        target_id=target_id,
        target_kind=target_kind,
        owner_artifact_ref=owner_artifact_ref,
        config_refs=tuple(config_refs),
        seed_refs=tuple(seed_refs),
        environment_ref=environment_ref,
        dependency_lock_ref=dependency_lock_ref,
        data_generator_ref=data_generator_ref,
        feature_reachability_ref=feature_reachability_ref,
        metric_provenance_ref=metric_provenance_ref,
        evidence_provenance_ref=evidence_provenance_ref,
        command_ref=command_ref,
        expected_artifact_refs=tuple(expected_artifact_refs),
        fingerprint_refs=tuple(fingerprint_refs),
        tolerance_policy_ref=tolerance_policy_ref,
        ci_rehearsal_ref=ci_rehearsal_ref,
        projection_regen_ref=projection_regen_ref,
        eligibility_ref=eligibility_ref,
        not_claimed=tuple(not_claimed),
    )


def _canonical_targets() -> tuple[ReproductionTargetRef, ...]:
    return (
        _target(
            target_id="dgt-l0-honest-rerun",
            target_kind="full-repro-ci",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/dgt-l0-controls.json"),
            config_refs=(
                _pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts"),
                _pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.command"),
                _pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.device_policy"),
            ),
            seed_refs=(
                _pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.seed_policy"),
                _pointer("reports/canonical/dgt-l0-controls.json", "$.independent_replay.fixed_seeds"),
            ),
            environment_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.device_policy"),
            dependency_lock_ref=_pointer("reports/canonical/dgt-l0-controls.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.feature_audit"),
            metric_provenance_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.honest_metric_review"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.source_artifacts.command"),
            expected_artifact_refs=(
                _artifact_exists_ref("reports/runs/discovery-gated-transformer/l0-toy-controls/raw_metrics.jsonl"),
                _artifact_exists_ref("reports/runs/discovery-gated-transformer/l0-toy-controls/summary.json"),
            ),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/dgt-l0-controls.fingerprint.json"),),
            tolerance_policy_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.independent_replay.pass_cells"),
            ci_rehearsal_ref=None,
            projection_regen_ref=None,
            eligibility_ref=_pointer("reports/canonical/dgt-l0-controls.json", "$.l0_toy_projection"),
            not_claimed=("L0 replay does not open any higher scaling level.",),
        ),
        _target(
            target_id="fair-l1-training",
            target_kind="full-repro-ci",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/dgt-l1-controls.json"),
            config_refs=(
                _pointer("reports/canonical/dgt-l1-controls.json", "$.task_spec"),
                _pointer("reports/canonical/dgt-l1-controls.json", "$.source_artifacts.device_policy"),
            ),
            seed_refs=(
                _pointer("reports/canonical/dgt-l1-controls.json", "$.source_artifacts.seed_policy"),
                _pointer("reports/canonical/dgt-l1-controls.json", "$.independent_replay.fixed_seeds"),
            ),
            environment_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.source_artifacts.device_policy"),
            dependency_lock_ref=_pointer("reports/canonical/dgt-l1-controls.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.fair_l1_construction.input_contract"),
            metric_provenance_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.owner_local_measurement_boundary"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.source_artifacts.command"),
            expected_artifact_refs=(
                _artifact_exists_ref("reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/raw_metrics.jsonl"),
                _artifact_exists_ref("reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/probe_metrics.jsonl"),
                _artifact_exists_ref("reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/summary.json"),
            ),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/dgt-l1-controls.fingerprint.json"),),
            tolerance_policy_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.independent_replay"),
            ci_rehearsal_ref=None,
            projection_regen_ref=None,
            eligibility_ref=_pointer("reports/canonical/dgt-l1-controls.json", "$.l1_tiny_sequence_projection"),
            not_claimed=("Fair L1 structural reproduction resolves pointers only; full replay remains a CI profile task.",),
        ),
        _target(
            target_id="honest-ablation-null-training",
            target_kind="full-repro-ci",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/dgt-neural-ablation.json"),
            config_refs=(
                _pointer("reports/canonical/dgt-neural-ablation.json", "$.run_spec"),
                _pointer("reports/canonical/dgt-neural-ablation.json", "$.training_protocol"),
            ),
            seed_refs=(_pointer("reports/canonical/dgt-neural-ablation.json", "$.training_protocol.seeds"),),
            environment_ref=_pointer("reports/canonical/dgt-neural-ablation.json", "$.training_protocol.resolved_device"),
            dependency_lock_ref=_pointer("reports/canonical/dgt-neural-ablation.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer("reports/canonical/dgt-neural-ablation.json", "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/dgt-neural-ablation.json", "$.scope_seal_mechanism"),
            metric_provenance_ref=_pointer("reports/canonical/dgt-neural-ablation.json", "$.metric_protocol"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer("reports/canonical/dgt-neural-ablation.fingerprint.json", "$.producer_command"),
            expected_artifact_refs=(
                _artifact_exists_ref("reports/runs/dgt-neural-ablation/raw_metrics.jsonl"),
                _artifact_exists_ref("reports/runs/dgt-neural-ablation/summary.json"),
            ),
            fingerprint_refs=(
                _artifact_exists_ref("reports/canonical/dgt-neural-ablation.fingerprint.json"),
                _artifact_exists_ref("reports/canonical/dgt-ablation-null-decomposition.fingerprint.json"),
            ),
            tolerance_policy_ref=_pointer("reports/canonical/dgt-ablation-null-decomposition.json", "$.threshold_schema"),
            ci_rehearsal_ref=None,
            projection_regen_ref=None,
            eligibility_ref=_pointer("reports/canonical/dgt-ablation-null-decomposition.json", "$.null_decomposition"),
            not_claimed=("Ablation null decomposition remains bounded to its measured owner artifacts.",),
        ),
        _target(
            target_id="canonical-index-view",
            target_kind="projection-only",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/index.json"),
            config_refs=(_pointer("reports/canonical/index.json", "$.reports"),),
            seed_refs=(),
            environment_ref=_pointer("reports/canonical/index.json", "$.root"),
            dependency_lock_ref=_pointer("reports/canonical/reproduction-package.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/index.json", "$.input_accessibility"),
            metric_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.command"),
            expected_artifact_refs=(_artifact_exists_ref("reports/canonical/index.json"),),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"),),
            tolerance_policy_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.hardgates"),
            ci_rehearsal_ref=None,
            projection_regen_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.projection_regen_refs[0]"),
            eligibility_ref=None,
            not_claimed=("Projection-only rows never satisfy measured-training full reproduction.",),
        ),
        _target(
            target_id="claim-capsule-view",
            target_kind="projection-only",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/claim_capsule.json"),
            config_refs=(_pointer("reports/canonical/claim_capsule.json", "$"),),
            seed_refs=(),
            environment_ref=_pointer("reports/canonical/index.json", "$.root"),
            dependency_lock_ref=_pointer("reports/canonical/reproduction-package.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/claim_capsule.json", "$"),
            metric_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.command"),
            expected_artifact_refs=(_artifact_exists_ref("reports/canonical/claim_capsule.json"),),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"),),
            tolerance_policy_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.hardgates"),
            ci_rehearsal_ref=None,
            projection_regen_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.projection_regen_refs[1]"),
            eligibility_ref=None,
            not_claimed=("ClaimCapsule projection stores pointers and does not restate owner prose.",),
        ),
        _target(
            target_id="claim-graph-view",
            target_kind="projection-only",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/claim_graph.json"),
            config_refs=(_pointer("reports/canonical/claim_graph.json", "$"),),
            seed_refs=(),
            environment_ref=_pointer("reports/canonical/index.json", "$.root"),
            dependency_lock_ref=_pointer("reports/canonical/reproduction-package.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/claim_graph.json", "$"),
            metric_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.command"),
            expected_artifact_refs=(_artifact_exists_ref("reports/canonical/claim_graph.json"),),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"),),
            tolerance_policy_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.hardgates"),
            ci_rehearsal_ref=None,
            projection_regen_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.projection_regen_refs[2]"),
            eligibility_ref=None,
            not_claimed=("Claim graph projection is deterministic reporting, not training replay.",),
        ),
        _target(
            target_id="scaling-ladder-view",
            target_kind="projection-only",
            owner_artifact_ref=_pointer("reports/canonical/discovery-gated-transformer.json", "$.scaling_ladder"),
            config_refs=(_pointer("reports/canonical/discovery-gated-transformer.json", "$.source_artifacts"),),
            seed_refs=(),
            environment_ref=_pointer("reports/canonical/index.json", "$.root"),
            dependency_lock_ref=_pointer("reports/canonical/discovery-gated-transformer.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/discovery-gated-transformer.json", "$.scaling_ladder"),
            metric_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.command"),
            expected_artifact_refs=(_artifact_exists_ref("reports/canonical/discovery-gated-transformer.json"),),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/discovery-gated-transformer.fingerprint.json"),),
            tolerance_policy_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.hardgates"),
            ci_rehearsal_ref=None,
            projection_regen_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.projection_regen_refs[3]"),
            eligibility_ref=None,
            not_claimed=("Scaling ladder state remains owned by its source artifact.",),
        ),
        _target(
            target_id="generated-markdown-views",
            target_kind="projection-only",
            owner_artifact_ref=_artifact_exists_ref("reports/canonical/index.md"),
            config_refs=(_pointer("reports/canonical/index.json", "$.reports"),),
            seed_refs=(),
            environment_ref=_pointer("reports/canonical/index.json", "$.root"),
            dependency_lock_ref=_pointer("reports/canonical/reproduction-package.fingerprint.json", "$.inputs.dependency_abi"),
            data_generator_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.runner"),
            feature_reachability_ref=_pointer("reports/canonical/index.json", "$.reports"),
            metric_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            evidence_provenance_ref=_pointer("reports/canonical/index.json", "$.evidence_provenance"),
            command_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.source_artifacts.command"),
            expected_artifact_refs=(_artifact_exists_ref("reports/canonical/index.md"),),
            fingerprint_refs=(_artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"),),
            tolerance_policy_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.hardgates"),
            ci_rehearsal_ref=None,
            projection_regen_ref=_pointer(PACKAGE_JSON_ARTIFACT, "$.projection_regen_refs[4]"),
            eligibility_ref=None,
            not_claimed=("Generated Markdown views are deterministic projections only.",),
        ),
    )


def _projection_refs() -> tuple[ProjectionRegenRef, ...]:
    return (
        ProjectionRegenRef("canonical-index-view", _pointer("reports/canonical/index.json", "$"), _artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"), True),
        ProjectionRegenRef("claim-capsule-view", _pointer("reports/canonical/claim_capsule.json", "$"), _artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"), True),
        ProjectionRegenRef("claim-graph-view", _pointer("reports/canonical/claim_graph.json", "$"), _artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"), True),
        ProjectionRegenRef("scaling-ladder-view", _pointer("reports/canonical/discovery-gated-transformer.json", "$.scaling_ladder"), _artifact_exists_ref("reports/canonical/discovery-gated-transformer.fingerprint.json"), True),
        ProjectionRegenRef("generated-markdown-views", "reports/canonical/index.md:$", _artifact_exists_ref("reports/canonical/reproduction-package.fingerprint.json"), True),
    )


def _source_artifacts(root: Path) -> dict[str, str]:
    return {
        "command": f"{PACKAGE_JSON_ARTIFACT}:$.source_artifacts.command",
        "owner_module": "bedc_quality_lab/reproduction_package.py",
        "runner": PRODUCER,
        "package_json": PACKAGE_JSON_ARTIFACT,
        "check_result_json": CHECK_RESULT_JSON_ARTIFACT,
        "source_sha256": _file_sha256(root, "bedc_quality_lab/reproduction_package.py"),
    }


def _base_hardgates() -> dict[str, dict[str, Any]]:
    return {
        "REPRO-HG1": {
            "status": "pending",
            "criterion": "config refs resolve and fingerprint inputs cover the declared closure",
            "evidence_pointer": f"{PACKAGE_JSON_ARTIFACT}:$.reproduction_targets",
        },
        "REPRO-HG2": {
            "status": "pending",
            "criterion": "data generator refs resolve and deterministic declarations are present",
            "evidence_pointer": f"{PACKAGE_JSON_ARTIFACT}:$.reproduction_targets",
        },
        "REPRO-HG3": {
            "status": "pending",
            "criterion": "feature reachability audit pointers resolve",
            "evidence_pointer": f"{PACKAGE_JSON_ARTIFACT}:$.reproduction_targets",
        },
        "REPRO-HG4": {
            "status": "pending",
            "criterion": "metric provenance pointers resolve to the owning artifacts",
            "evidence_pointer": f"{PACKAGE_JSON_ARTIFACT}:$.reproduction_targets",
        },
        "REPRO-HG5": {
            "status": "blocked",
            "criterion": "full-repro-ci targets carry CI rehearsal evidence with matching rerun fingerprints",
            "evidence_pointer": f"{CHECK_RESULT_JSON_ARTIFACT}:$.target_results",
        },
    }


def build_package(root: Path, generated_at: str) -> dict[str, Any]:
    package = ReproductionPackage(
        schema_id=PACKAGE_SCHEMA_ID,
        artifact_id=PACKAGE_ARTIFACT_ID,
        generated_at=generated_at,
        producer=PRODUCER,
        owner_module="bedc_quality_lab/reproduction_package.py",
        source_artifacts=_source_artifacts(root),
        reproduction_targets=_canonical_targets(),
        projection_regen_refs=_projection_refs(),
        hardgates=_base_hardgates(),
        claim_capsule_ref={
            "artifact": "reports/canonical/claim_capsule.json",
            "pointer": "$",
            "owner_pointer": "reports/canonical/claim_capsule.json:$",
        },
        cost_protocol={"owner_pointer": "configs/default_cost_protocol.yaml:$"},
        not_claimed=(
            "This package contains reproduction pointers only; metric values remain owned by source artifacts.",
            "Projection-only targets never satisfy measured-training full reproduction.",
            "Full training replay is only evaluated under the explicit full-repro-ci profile.",
            "Upstream owner gaps are reported as blocked rather than guessed.",
        ),
    )
    payload = package.as_payload()
    validate_package(payload, root)
    return payload


def _iter_dicts(value: Any) -> Iterable[Mapping[str, Any]]:
    if isinstance(value, Mapping):
        yield value
        for nested in value.values():
            yield from _iter_dicts(nested)
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes, bytearray)):
        for nested in value:
            yield from _iter_dicts(nested)


def _forbidden_copied_fact_hits(payload: Mapping[str, Any]) -> list[str]:
    hits: list[str] = []
    for mapping in _iter_dicts(payload):
        for key, value in mapping.items():
            key_text = str(key)
            if key_text in FORBIDDEN_COPIED_FACT_KEYS:
                hits.append(key_text)
            if isinstance(value, str):
                lowered = value.lower()
                for phrase in FORBIDDEN_COPIED_FACT_PHRASES:
                    if phrase in lowered:
                        hits.append(f"{key_text}:{phrase}")
    return sorted(set(hits))


def _resolve(root: Path, ref: str | None) -> Any:
    if not ref:
        return None
    split = split_artifact_pointer(ref)
    if split is None:
        path = root / ref
        return True if path.exists() else None
    artifact, pointer = split
    path = root / artifact
    if path.suffix not in {".json", ".jsonl"}:
        return True if path.exists() else None
    return resolve_artifact_pointer(root, f"{artifact}:{pointer}")


def _target_rows(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = payload.get("reproduction_targets")
    if not isinstance(rows, list):
        raise ValueError("reproduction_targets must be a list")
    return [row for row in rows if isinstance(row, Mapping)]


def _refs_from_target(row: Mapping[str, Any]) -> list[str]:
    refs: list[str] = []
    for key, value in row.items():
        if key.endswith("_ref") and isinstance(value, str):
            refs.append(value)
        elif key.endswith("_refs") and isinstance(value, list):
            refs.extend(item for item in value if isinstance(item, str))
    return refs


def validate_package(payload: Mapping[str, Any], root: Path) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "owner_module",
        "source_artifacts",
        "reproduction_targets",
        "projection_regen_refs",
        "hardgates",
        "claim_capsule_ref",
        "cost_protocol",
        "not_claimed",
    }
    if set(payload) != required:
        raise ValueError("reproduction package fields mismatch")
    if payload["schema_id"] != PACKAGE_SCHEMA_ID or payload["artifact_id"] != PACKAGE_ARTIFACT_ID:
        raise ValueError("reproduction package identity mismatch")
    copied_hits = _forbidden_copied_fact_hits(payload)
    if copied_hits:
        raise ValueError(f"copied owner facts are forbidden: {copied_hits[0]}")
    rows = _target_rows(payload)
    target_ids = [str(row.get("target_id")) for row in rows]
    if len(target_ids) != len(set(target_ids)):
        raise ValueError("target ids must be unique")
    if not FULL_REPRO_TARGET_IDS.issubset(target_ids):
        raise ValueError("full reproduction target set is incomplete")
    for row in rows:
        target_id = str(row.get("target_id"))
        kind = row.get("target_kind")
        if kind not in {"full-repro-ci", "projection-only"}:
            raise ValueError(f"invalid target kind: {target_id}")
        if target_id in PROJECTION_ONLY_TARGET_IDS and kind != "projection-only":
            raise ValueError(f"projection-only target listed as full reproduction: {target_id}")
        if target_id in FULL_REPRO_TARGET_IDS and kind != "full-repro-ci":
            raise ValueError(f"full reproduction target listed as projection-only: {target_id}")
        for key in (
            "owner_artifact_ref",
            "config_refs",
            "seed_refs",
            "environment_ref",
            "dependency_lock_ref",
            "data_generator_ref",
            "feature_reachability_ref",
            "metric_provenance_ref",
            "evidence_provenance_ref",
            "command_ref",
            "expected_artifact_refs",
            "fingerprint_refs",
            "tolerance_policy_ref",
            "not_claimed",
        ):
            if key not in row:
                raise ValueError(f"target missing {key}: {target_id}")
        if kind == "full-repro-ci":
            if not row.get("config_refs") or not row.get("seed_refs") or not row.get("expected_artifact_refs"):
                raise ValueError(f"full reproduction refs incomplete: {target_id}")
        if kind == "projection-only" and row.get("ci_rehearsal_ref") is not None:
            raise ValueError(f"projection target cannot carry CI rehearsal: {target_id}")
    if not isinstance(payload["projection_regen_refs"], list):
        raise ValueError("projection_regen_refs must be a list")


def _status_for_failures(failures: Sequence[str]) -> Status:
    return "pass" if not failures else "blocked"


def _blocked_reason_for_failures(target_id: str, failures: Sequence[str]) -> dict[str, str | None] | None:
    if not failures:
        return None
    if any("CI rehearsal evidence is missing" == failure for failure in failures):
        return {
            "category": "ci-rehearsal-missing",
            "detail": "ci-rehearsal-evidence-missing",
            "evidence_ref": f"{CHECK_RESULT_JSON_ARTIFACT}:$.target_results",
            "owner_gate_ref": None,
            "dependency_ref": None,
            "planning_context_ref": None,
        }
    if any("training replay execution is not invoked by the pointer verifier" == failure for failure in failures):
        return {
            "category": "full-replay-not-invoked",
            "detail": "training-replay-not-invoked",
            "evidence_ref": f"{CHECK_RESULT_JSON_ARTIFACT}:$.target_results",
            "owner_gate_ref": None,
            "dependency_ref": None,
            "planning_context_ref": None,
        }
    if any("fingerprint" in failure for failure in failures):
        return {
            "category": "tolerance-blocked",
            "detail": "fingerprint-pointer-blocked",
            "evidence_ref": f"{CHECK_RESULT_JSON_ARTIFACT}:$.target_results",
            "owner_gate_ref": None,
            "dependency_ref": None,
            "planning_context_ref": None,
        }
    return {
        "category": "source-blocked",
        "detail": "source-pointer-blocked",
        "evidence_ref": f"{CHECK_RESULT_JSON_ARTIFACT}:$.target_results",
        "owner_gate_ref": None,
        "dependency_ref": None,
        "planning_context_ref": None,
    }


def _tolerance_status_for(target_id: str, status: Status, fingerprint_status: Status) -> Status:
    if status == "pass":
        return "pass"
    if target_id == "fair-l1-training" and fingerprint_status == "pass":
        return "pass"
    return "blocked" if status == "blocked" else "fail"


def _fingerprint_status(root: Path, refs: Sequence[str]) -> tuple[Status, list[str]]:
    failures: list[str] = []
    for ref in refs:
        resolved = _resolve(root, ref)
        if resolved is None:
            failures.append(f"fingerprint pointer does not resolve: {ref}")
            continue
        split = split_artifact_pointer(ref)
        if split is None:
            failures.append(f"fingerprint ref is not an artifact pointer: {ref}")
            continue
        artifact, _pointer = split
        if not artifact.endswith(".fingerprint.json"):
            failures.append(f"fingerprint ref must target a fingerprint sidecar: {ref}")
    return _status_for_failures(failures), failures


def _structural_failures(root: Path, row: Mapping[str, Any]) -> tuple[list[str], tuple[str, ...], Status]:
    target_id = str(row.get("target_id"))
    resolved: list[str] = []
    failures: list[str] = []
    for ref in _refs_from_target(row):
        if _resolve(root, ref) is None:
            failures.append(f"pointer does not resolve: {ref}")
        else:
            resolved.append(ref)
    kind = row.get("target_kind")
    if kind == "full-repro-ci":
        for key in ("config_refs", "seed_refs", "expected_artifact_refs", "fingerprint_refs"):
            if not row.get(key):
                failures.append(f"required {key} missing")
    fingerprint_status, fingerprint_failures = _fingerprint_status(root, tuple(str(ref) for ref in row.get("fingerprint_refs", []) if isinstance(ref, str)))
    failures.extend(fingerprint_failures)
    return failures, tuple(resolved), fingerprint_status


def _projection_failures(root: Path, row: Mapping[str, Any]) -> list[str]:
    if row.get("target_kind") != "projection-only":
        return []
    failures: list[str] = []
    if row.get("ci_rehearsal_ref") is not None:
        failures.append("projection-only target carries CI rehearsal")
    regen_ref = row.get("projection_regen_ref")
    if not isinstance(regen_ref, str) or _resolve(root, regen_ref) is None:
        failures.append("projection regen pointer does not resolve")
    return failures


def _full_repro_failures(root: Path, row: Mapping[str, Any], profile: Profile) -> tuple[list[str], tuple[str, ...], Status]:
    if row.get("target_kind") != "full-repro-ci":
        return (["full-repro-ci profile cannot target projection-only rows"], (), "fail")
    failures, resolved, fingerprint_status = _structural_failures(root, row)
    ci_ref = row.get("ci_rehearsal_ref")
    if not isinstance(ci_ref, str) or _resolve(root, ci_ref) is None:
        failures.append("CI rehearsal evidence is missing")
    if profile == "full-repro-ci":
        failures.append("training replay execution is not invoked by the pointer verifier")
    return failures, resolved, fingerprint_status


def verify_package(
    payload: Mapping[str, Any],
    root: Path,
    profile: Profile,
    target_ids: Sequence[str] | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    validate_package(payload, root)
    selected = set(target_ids or [])
    rows = _target_rows(payload)
    if selected:
        rows = [row for row in rows if str(row.get("target_id")) in selected]
    known = {str(row.get("target_id")) for row in _target_rows(payload)}
    unknown = sorted(selected - known)
    target_results: list[dict[str, Any]] = []
    blocked: list[str] = []
    failed: list[str] = []
    for row in rows:
        target_id = str(row.get("target_id"))
        kind = row.get("target_kind")
        if profile == "projection" and kind != "projection-only":
            continue
        if profile == "structural":
            failures, resolved, fingerprint_status = _structural_failures(root, row)
        elif profile == "projection":
            structural_failures, resolved, fingerprint_status = _structural_failures(root, row)
            failures = structural_failures + _projection_failures(root, row)
        elif profile == "full-repro-ci":
            failures, resolved, fingerprint_status = _full_repro_failures(root, row, profile)
        else:
            raise ValueError(f"unknown profile: {profile}")
        status = _status_for_failures(failures)
        if status == "blocked":
            blocked.append(target_id)
        if status == "fail":
            failed.append(target_id)
        target_results.append(
            ReproductionCheckResult(
                target_id=target_id,
                target_kind=kind,  # type: ignore[arg-type]
                status=status,
                blocked_reason=_blocked_reason_for_failures(target_id, failures),
                resolved_owner_pointers=resolved,
                fingerprint_status=fingerprint_status,
                tolerance_status=_tolerance_status_for(target_id, status, fingerprint_status),
                rerun_artifact_refs=tuple(str(ref) for ref in row.get("expected_artifact_refs", []) if isinstance(ref, str)),
                failure_reasons=tuple(failures),
                ci_rehearsal_ref=row.get("ci_rehearsal_ref") if isinstance(row.get("ci_rehearsal_ref"), str) else None,
            ).as_payload()
        )
    for target_id in unknown:
        failed.append(target_id)
        target_results.append(
            ReproductionCheckResult(
                target_id=target_id,
                target_kind="full-repro-ci",
                status="fail",
                blocked_reason=None,
                resolved_owner_pointers=(),
                fingerprint_status="fail",
                tolerance_status="fail",
                rerun_artifact_refs=(),
                failure_reasons=("unknown target id",),
                ci_rehearsal_ref=None,
            ).as_payload()
        )
    return {
        "schema_id": CHECK_RESULT_SCHEMA_ID,
        "artifact_id": CHECK_RESULT_ARTIFACT_ID,
        "generated_at": generated_at or str(payload.get("generated_at")),
        "source_artifacts": {
            "package": PACKAGE_JSON_ARTIFACT,
            "runner": PRODUCER,
        },
        "package_ref": f"{PACKAGE_JSON_ARTIFACT}:$",
        "profile": profile,
        "target_results": target_results,
        "blocked_targets": sorted(set(blocked)),
        "failed_targets": sorted(set(failed)),
        "not_claimed": [
            "Pointer verification is not a substitute for full training replay.",
            "Projection-only checks do not satisfy measured-training reproduction.",
        ],
    }


def render_package_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Reproduction Package",
        "",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Generated at: `{payload['generated_at']}`",
        "",
        "| target | kind | owner | fingerprints |",
        "| --- | --- | --- | --- |",
    ]
    for row in _target_rows(payload):
        fingerprints = ", ".join(str(ref) for ref in row.get("fingerprint_refs", []))
        lines.append(
            f"| `{row['target_id']}` | `{row['target_kind']}` | `{row['owner_artifact_ref']}` | `{fingerprints}` |"
        )
    lines.extend(["", "## Boundaries", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def render_check_result_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Reproduction Check Result",
        "",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Profile: `{payload['profile']}`",
        f"- Package: `{payload['package_ref']}`",
        "",
        "| target | kind | status | fingerprint | tolerance |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["target_results"]:
        lines.append(
            f"| `{row['target_id']}` | `{row['target_kind']}` | `{row['status']}` | "
            f"`{row['fingerprint_status']}` | `{row['tolerance_status']}` |"
        )
    lines.append("")
    return "\n".join(lines)

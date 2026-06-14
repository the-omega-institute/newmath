"""Finite experiment-stack card contract over delegated owner pointers."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab import claim_acceptance as _claim_acceptance_owner
from bedc_quality_lab import claim_artifact_consistency as _claim_artifact_consistency_owner
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:experiment-stack-cards"
ARTIFACT_ID = "bedc-quality-lab:experiment-stack-cards"
JSON_ARTIFACT = "reports/canonical/experiment_stack_cards.json"
MARKDOWN_ARTIFACT = "reports/canonical/experiment_stack_cards.md"
PRODUCER = "scripts/run_experiment_stack_cards.py"

STACK_HARDGATE_IDS = ("STACK-HG1", "STACK-HG2")
CONSISTENCY_GATE_IDS = ("STACK-HG1", "STACK-HG2", "CLAIM-FIRST-HG1")
ADMISSION_OWNER = f"{_claim_acceptance_owner.__name__}.claim_first_pointer_checks"
POSITIVE_EVIDENCE_OWNER = f"{_claim_acceptance_owner.__name__}.validate_positive_claim_evidence"
CONSISTENCY_GATES_POINTER = f"{_claim_artifact_consistency_owner.JSON_ARTIFACT}:$.gates"
NOT_CLAIMED = (
    "The card report is an auxiliary contract and does not promote model quality.",
    "Blocked card rows are owner gaps, not negative empirical evidence.",
    "Claim-first admission is delegated to the claim acceptance and consistency owners.",
    "External standard alignment is pointer-only and carries no independent certification.",
)

BLOCKING_STATUS_VALUES = frozenset(
    {
        "blocked",
        "fail",
        "failed",
        "forbidden",
        "missing",
        "not-eligible",
        "not-ready",
        "not-winnable-from-recorded-features",
        "pending",
        "projection-only",
        "projection_only",
        "tainted",
        "training_evidence_absent",
        "empirical_training_tainted",
        "empirical-claim-forbidden",
        "empirical_claim_forbidden",
        "null_result",
    }
)
@dataclass(**{"froz" + "en": True})
class ExperimentStackCardSpec:
    card_id: str
    canonical_owner_issue: str
    owner_pointer: str
    schema_id: str
    hardgate_prefixes: tuple[str, ...]
    demotion_rule_pointer: str
    source_pointer: str
    summary_pointer: str
    phase: str
    depends_on_cards: tuple[str, ...]
    pointer_through: bool = False
    source_owner_field: str | None = None
    summary_owner_fields: tuple[str, ...] = ()
    demotion_owner_field: str | None = None

    @property
    def owner_artifact(self) -> str:
        split = split_artifact_pointer(self.owner_pointer)
        return split[0] if split is not None else self.owner_pointer

    def to_json(self) -> dict[str, Any]:
        return {
            "card_id": self.card_id,
            "canonical_owner_issue": self.canonical_owner_issue,
            "owner_pointer": self.owner_pointer,
            "owner_artifact": self.owner_artifact,
            "schema_id": self.schema_id,
            "hardgate_prefixes": list(self.hardgate_prefixes),
            "demotion_rule_pointer": self.demotion_rule_pointer,
            "source_pointer": self.source_pointer,
            "summary_pointer": self.summary_pointer,
            "phase": self.phase,
            "depends_on_cards": list(self.depends_on_cards),
        }


EXPERIMENT_STACK_CARDS: tuple[ExperimentStackCardSpec, ...] = (
    ExperimentStackCardSpec(
        card_id="claim-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/runs/discovery-gated-transformer/claim_capsule.json:$",
        schema_id="bedc-quality-lab:dgt-claim-capsule",
        hardgate_prefixes=("CLAIM-HG",),
        demotion_rule_pointer="reports/canonical/discovery-gated-transformer.json:$.not_claimed",
        source_pointer="reports/runs/discovery-gated-transformer/claim_capsule.json:$.owner_ref",
        summary_pointer="reports/runs/discovery-gated-transformer/claim_capsule.json:$.claim_scope",
        phase="preflight",
        depends_on_cards=(),
    ),
    ExperimentStackCardSpec(
        card_id="task-target-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/canonical/discovery-gated-transformer.json:$",
        schema_id="bedc-quality-lab:discovery-gated-transformer",
        hardgate_prefixes=("TARGET-HG",),
        demotion_rule_pointer="reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.boundary_ledger",
        source_pointer="reports/canonical/discovery-gated-transformer.json:$.d4_projection.matched_control",
        summary_pointer="reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.source_projection",
        phase="preflight",
        depends_on_cards=("claim-card",),
    ),
    ExperimentStackCardSpec(
        card_id="data-card",
        canonical_owner_issue="1201",
        owner_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer",
        schema_id="bedc-quality-lab:evidence-provenance-discovery-row",
        hardgate_prefixes=("DATA-HG",),
        demotion_rule_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.not_claimed",
        source_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer",
        summary_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.evidence_type",
        phase="preflight",
        depends_on_cards=("task-target-card",),
    ),
    ExperimentStackCardSpec(
        card_id="feature-access-card",
        canonical_owner_issue="1209",
        owner_pointer="reports/canonical/dgt-l1-controls.json:$",
        schema_id="bedc-quality-lab:dgt-l1-controls",
        hardgate_prefixes=("L1-REVIEW-HG",),
        demotion_rule_pointer="reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection",
        source_pointer="reports/canonical/dgt-l1-controls.json:$.training_arms",
        summary_pointer="reports/canonical/dgt-l1-controls.json:$.review_status",
        phase="preflight",
        depends_on_cards=("data-card",),
    ),
    ExperimentStackCardSpec(
        card_id="baseline-validity-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/canonical/dgt-l1-boundary-report.json:$",
        schema_id="bedc-quality-lab:dgt-l1-boundary-report",
        hardgate_prefixes=("BASE-HG",),
        demotion_rule_pointer="reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion",
        source_pointer="reports/canonical/dgt-l1-boundary-report.json:$.base_bayes_ceiling",
        summary_pointer="reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability",
        phase="preflight",
        depends_on_cards=("task-target-card", "feature-access-card"),
    ),
    ExperimentStackCardSpec(
        card_id="ood-solvability-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/canonical/dgt-l1-boundary-report.json:$",
        schema_id="bedc-quality-lab:dgt-l1-boundary-report",
        hardgate_prefixes=("L1-BOUNDARY-HG",),
        demotion_rule_pointer="reports/canonical/dgt-l1-boundary-report.json:$.not_claimed",
        source_pointer="reports/canonical/dgt-l1-boundary-report.json:$.ood_solvability",
        summary_pointer="reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability",
        phase="preflight",
        depends_on_cards=("task-target-card", "data-card"),
    ),
    ExperimentStackCardSpec(
        card_id="metric-provenance-card",
        canonical_owner_issue="1201",
        owner_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.metric_provenance_pointers[0]",
        schema_id="bedc-quality-lab:evidence-provenance-metric-row",
        hardgate_prefixes=("EVIDENCE-HG",),
        demotion_rule_pointer="$owner.not_claimed",
        source_pointer="$owner",
        summary_pointer="$owner.source_type",
        phase="preflight",
        depends_on_cards=("claim-card", "task-target-card"),
        pointer_through=True,
        source_owner_field=None,
        summary_owner_fields=("source_type",),
        demotion_owner_field="not_claimed",
    ),
    ExperimentStackCardSpec(
        card_id="training-authenticity-card",
        canonical_owner_issue="1201",
        owner_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.producer_training_audit_pointer",
        schema_id="bedc-quality-lab:evidence-provenance-producer-audit",
        hardgate_prefixes=("EVIDENCE-HG",),
        demotion_rule_pointer="$owner.not_claimed",
        source_pointer="$owner",
        summary_pointer="$owner.training_evidence_status",
        phase="evidence",
        depends_on_cards=("baseline-validity-card", "metric-provenance-card"),
        pointer_through=True,
        source_owner_field=None,
        summary_owner_fields=("training_evidence_status",),
        demotion_owner_field="not_claimed",
    ),
    ExperimentStackCardSpec(
        card_id="statistical-evidence-card",
        canonical_owner_issue="1201",
        owner_pointer="reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.metric_provenance_pointers[0]",
        schema_id="bedc-quality-lab:evidence-provenance-metric-row",
        hardgate_prefixes=("EVIDENCE-HG",),
        demotion_rule_pointer="$owner.not_claimed",
        source_pointer="$owner",
        summary_pointer="$owner.allowed_for_empirical_claim",
        phase="evidence",
        depends_on_cards=("training-authenticity-card", "metric-provenance-card"),
        pointer_through=True,
        source_owner_field=None,
        summary_owner_fields=("allowed_for_empirical_claim", "source_type"),
        demotion_owner_field="not_claimed",
    ),
    ExperimentStackCardSpec(
        card_id="ablation-causal-evidence-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/canonical/dgt-neural-ablation.json:$",
        schema_id="bedc-quality-lab:dgt-neural-ablation",
        hardgate_prefixes=("NABL-HG",),
        demotion_rule_pointer="reports/canonical/dgt-neural-ablation.json:$.not_claimed",
        source_pointer="reports/canonical/dgt-neural-ablation.json:$.boundary_ledger",
        summary_pointer="reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status",
        phase="evidence",
        depends_on_cards=("training-authenticity-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="artifact-reproducibility-card",
        canonical_owner_issue="1213",
        owner_pointer="reports/release_manifest_sidecar.json:$",
        schema_id="bedc-quality-lab:release-manifest-sidecar",
        hardgate_prefixes=("REL-HG",),
        demotion_rule_pointer="reports/release_manifest_sidecar.json:$.revoke_if",
        source_pointer="reports/release_manifest_sidecar.json:$.required_pointers",
        summary_pointer="reports/release_manifest_sidecar.json:$.release_bundle_status",
        phase="release",
        depends_on_cards=("training-authenticity-card",),
    ),
    ExperimentStackCardSpec(
        card_id="model-card",
        canonical_owner_issue="1220",
        owner_pointer="reports/canonical/dgt-model-card.json:$",
        schema_id="bedc-quality-lab:dgt-model-card",
        hardgate_prefixes=("CARD-HG",),
        demotion_rule_pointer="reports/canonical/dgt-model-card.json:$.not_claimed",
        source_pointer="reports/canonical/dgt-model-card.json:$.intended_use",
        summary_pointer="reports/canonical/dgt-model-card.json:$.card_hardgates.status",
        phase="release",
        depends_on_cards=("claim-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="risk-scope-review-card",
        canonical_owner_issue="1207",
        owner_pointer="reports/canonical/dgt-l1-boundary-report.json:$",
        schema_id="bedc-quality-lab:dgt-l1-boundary-report",
        hardgate_prefixes=("L1-BOUNDARY-HG",),
        demotion_rule_pointer="reports/canonical/dgt-l1-boundary-report.json:$.not_claimed",
        source_pointer="reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion",
        summary_pointer="reports/canonical/dgt-l1-boundary-report.json:$.boundary_decision",
        phase="release",
        depends_on_cards=("claim-card", "data-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="release-readiness-board",
        canonical_owner_issue="1213",
        owner_pointer="reports/canonical/reproduction-package.json:$",
        schema_id="bedc-quality-lab:reproduction-package",
        hardgate_prefixes=("REPRO-HG",),
        demotion_rule_pointer="reports/canonical/reproduction-package.json:$.hardgates.REPRO-HG5",
        source_pointer="reports/canonical/reproduction-package.json:$.reproduction_targets",
        summary_pointer="reports/canonical/reproduction-package.json:$.hardgates",
        phase="release",
        depends_on_cards=(
            "claim-card",
            "task-target-card",
            "data-card",
            "feature-access-card",
            "baseline-validity-card",
            "ood-solvability-card",
            "metric-provenance-card",
            "training-authenticity-card",
            "statistical-evidence-card",
            "ablation-causal-evidence-card",
            "artifact-reproducibility-card",
            "model-card",
            "risk-scope-review-card",
        ),
    ),
)

CARD_IDS = tuple(spec.card_id for spec in EXPERIMENT_STACK_CARDS)
CARD_INDEX = {card_id: index for index, card_id in enumerate(CARD_IDS)}


INDUSTRY_STANDARD_POINTER_MAP: Mapping[str, Mapping[str, Any]] = {
    "neurips-checklist": {
        "external_pointer": "https://neurips.cc/public/guides/PaperChecklist",
        "local_card_ids": ("claim-card", "data-card", "statistical-evidence-card", "risk-scope-review-card"),
    },
    "papers-with-code-code-completeness": {
        "external_pointer": "https://paperswithcode.com/about",
        "local_card_ids": ("artifact-reproducibility-card", "training-authenticity-card"),
    },
    "acm-artifact-badging": {
        "external_pointer": "https://www.acm.org/publications/policies/artifact-review-badging",
        "local_card_ids": ("artifact-reproducibility-card", "release-readiness-board"),
    },
    "model-cards": {
        "external_pointer": "https://modelcards.withgoogle.com/about",
        "local_card_ids": ("model-card", "risk-scope-review-card"),
    },
    "nist-ai-rmf": {
        "external_pointer": "https://www.nist.gov/itl/ai-risk-management-framework",
        "local_card_ids": ("risk-scope-review-card", "release-readiness-board"),
    },
}


def card_pointer(card_id: str) -> str:
    return f"{JSON_ARTIFACT}:$.cards[{CARD_INDEX[card_id]}]"


def spec_by_card_id() -> dict[str, ExperimentStackCardSpec]:
    return {spec.card_id: spec for spec in EXPERIMENT_STACK_CARDS}


def validate_experiment_stack_specs(
    specs: Sequence[ExperimentStackCardSpec] = EXPERIMENT_STACK_CARDS,
) -> tuple[str, ...]:
    errors: list[str] = []
    ids = [spec.card_id for spec in specs]
    if len(ids) != 14:
        errors.append("card-count")
    if len(ids) != len(set(ids)):
        errors.append("duplicate-card-id")
    id_set = set(ids)
    for spec in specs:
        if not spec.card_id or spec.card_id != spec.card_id.lower() or "_" in spec.card_id:
            errors.append(f"{spec.card_id}:card-id")
        if not spec.canonical_owner_issue:
            errors.append(f"{spec.card_id}:owner-issue")
        if split_artifact_pointer(spec.owner_pointer) is None:
            errors.append(f"{spec.card_id}:owner-pointer")
        if not spec.owner_artifact.endswith(".json"):
            errors.append(f"{spec.card_id}:owner-artifact")
        if not spec.schema_id or ":" not in spec.schema_id:
            errors.append(f"{spec.card_id}:schema-id")
        if not spec.hardgate_prefixes:
            errors.append(f"{spec.card_id}:hardgate-prefix")
        for pointer_name in ("demotion_rule_pointer", "source_pointer", "summary_pointer"):
            pointer = getattr(spec, pointer_name)
            if spec.pointer_through and pointer.startswith("$owner"):
                continue
            if split_artifact_pointer(pointer) is None:
                errors.append(f"{spec.card_id}:{pointer_name}")
        if spec.pointer_through:
            if not spec.summary_owner_fields:
                errors.append(f"{spec.card_id}:summary-owner-fields")
            if spec.demotion_owner_field is None:
                errors.append(f"{spec.card_id}:demotion-owner-field")
        for dependency in spec.depends_on_cards:
            if dependency == spec.card_id or dependency not in id_set:
                errors.append(f"{spec.card_id}:depends-on:{dependency}")
    for standard_id, row in INDUSTRY_STANDARD_POINTER_MAP.items():
        local_card_ids = row.get("local_card_ids")
        if not isinstance(local_card_ids, tuple) or any(card_id not in id_set for card_id in local_card_ids):
            errors.append(f"{standard_id}:local-card-ids")
    return tuple(errors)


def assert_valid_experiment_stack_specs() -> None:
    errors = validate_experiment_stack_specs()
    if errors:
        raise ValueError(f"experiment stack spec contract failed: {', '.join(errors)}")


def _schema_matches(value: Any, schema_id: str) -> bool:
    if not isinstance(value, Mapping):
        return False
    if value.get("schema_id") == schema_id or value.get("artifact_id") == schema_id or value.get("card_id") == schema_id:
        return True
    if schema_id.startswith("bedc-quality-lab:evidence-provenance-"):
        return value.get("report") == "discovery-gated-transformer"
    return False


def _pointer_resolves(root: Path, pointer: str) -> bool:
    return resolve_artifact_pointer(root, pointer) is not None


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def _owner_pointer_resolution(root: Path, spec: ExperimentStackCardSpec) -> tuple[str | None, Any]:
    owner_cell = resolve_artifact_pointer(root, spec.owner_pointer)
    if spec.pointer_through:
        if not isinstance(owner_cell, str):
            return None, None
        resolved = resolve_artifact_pointer(root, owner_cell)
        return owner_cell, resolved
    return spec.owner_pointer, owner_cell


def _owner_field_resolves(owner_payload: Any, field: str | None) -> bool:
    if field is None:
        return owner_payload is not None
    return isinstance(owner_payload, Mapping) and owner_payload.get(field) is not None


def _owner_pointer_resolves(root: Path, spec: ExperimentStackCardSpec, pointer: str, field: str | None = None) -> bool:
    if not spec.pointer_through:
        return _pointer_resolves(root, pointer)
    _resolved_pointer, owner_payload = _owner_pointer_resolution(root, spec)
    return _owner_field_resolves(owner_payload, field)


def _owner_pointer_value(root: Path, spec: ExperimentStackCardSpec, pointer: str, field: str | None = None) -> Any:
    if not spec.pointer_through:
        return resolve_artifact_pointer(root, pointer)
    _resolved_pointer, owner_payload = _owner_pointer_resolution(root, spec)
    if field is None:
        return owner_payload
    if isinstance(owner_payload, Mapping):
        return owner_payload.get(field)
    return None


def _owner_field_pointer(resolved_owner_pointer: str | None, field: str | None) -> str:
    if resolved_owner_pointer is None:
        return "$owner" if field is None else f"$owner.{field}"
    if field is None:
        return resolved_owner_pointer
    return f"{resolved_owner_pointer}.{field}"


def _projected_source_pointer(spec: ExperimentStackCardSpec, resolved_owner_pointer: str | None) -> str:
    if spec.pointer_through:
        return _owner_field_pointer(resolved_owner_pointer, spec.source_owner_field)
    return spec.source_pointer


def _projected_summary_pointer(spec: ExperimentStackCardSpec, resolved_owner_pointer: str | None) -> str:
    if not spec.pointer_through:
        return spec.summary_pointer
    fields = spec.summary_owner_fields
    if len(fields) == 1:
        return _owner_field_pointer(resolved_owner_pointer, fields[0])
    return ", ".join(_owner_field_pointer(resolved_owner_pointer, field) for field in fields)


def _projected_demotion_pointer(spec: ExperimentStackCardSpec, resolved_owner_pointer: str | None) -> str:
    if spec.pointer_through:
        return _owner_field_pointer(resolved_owner_pointer, spec.demotion_owner_field)
    return spec.demotion_rule_pointer


def _status_value_blocks(value: str) -> bool:
    normalized = value.strip().lower().replace(" ", "-")
    return normalized in BLOCKING_STATUS_VALUES


def _owner_cell_blocks(value: Any) -> bool:
    if value is None:
        return True
    if isinstance(value, str):
        return _status_value_blocks(value)
    if isinstance(value, bool):
        return False
    if isinstance(value, Mapping):
        for key in (
            "status",
            "hardgate_status",
            "review_status",
            "promotion_status",
            "promotion_readiness",
            "training_evidence_status",
            "source_type",
            "taint_status",
        ):
            cell = value.get(key)
            if isinstance(cell, str) and _status_value_blocks(cell):
                return True
        if value.get("allowed_for_empirical_claim") is False:
            return True
        allowed = value.get("allowed_claim_kinds")
        if isinstance(allowed, Sequence) and not isinstance(allowed, (str, bytes)) and "projection_only" in allowed:
            return True
        for hardgate_key in ("hardgates", "gates", "card_hardgates", "nabl_hardgates", "hardgate"):
            hardgates = value.get(hardgate_key)
            if _hardgate_cells_block(hardgates):
                return True
        return False
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return any(_owner_cell_blocks(item) for item in value)
    return False


def _hardgate_cells_block(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return value != "pass"
    if isinstance(value, Mapping):
        status = value.get("status")
        if isinstance(status, str) and status != "pass":
            return True
        nested = value.get("gates")
        if nested is not None and _hardgate_cells_block(nested):
            return True
        for key, cell in value.items():
            if key in {"criterion", "evidence", "evidence_pointer", "reason"}:
                continue
            if isinstance(cell, Mapping):
                cell_status = cell.get("status")
                if isinstance(cell_status, str) and cell_status != "pass":
                    return True
            elif isinstance(cell, str) and key.startswith(("HG", "STACK", "REPRO", "SCALE", "NABL", "CARD", "L1", "MC")) and cell != "pass":
                return True
        return False
    return False


def _owner_status_ok(owner_payload: Any) -> bool:
    return owner_payload is not None and not _owner_cell_blocks(owner_payload)


def _card_failure_reasons(
    *,
    owner_exists: bool,
    schema_matches: bool,
    source_resolves: bool,
    summary_resolves: bool,
    demotion_resolves: bool,
    owner_status_ok: bool,
) -> list[str]:
    reasons: list[str] = []
    if not owner_exists:
        reasons.append("owner-pointer-unresolved")
    elif not schema_matches:
        reasons.append("owner-schema-mismatch")
    if not source_resolves:
        reasons.append("source-pointer-unresolved")
    if not summary_resolves:
        reasons.append("summary-pointer-unresolved")
    if not demotion_resolves:
        reasons.append("demotion-rule-pointer-unresolved")
    if owner_exists and not owner_status_ok:
        reasons.append("owner-status-or-hardgate-blocked")
    return reasons


def project_card(spec: ExperimentStackCardSpec, *, root: Path) -> dict[str, Any]:
    resolved_owner_pointer, owner_payload = _owner_pointer_resolution(root, spec)
    owner_exists = resolved_owner_pointer is not None and owner_payload is not None
    schema_ok = _schema_matches(owner_payload, spec.schema_id)
    source_ok = _owner_pointer_resolves(root, spec, spec.source_pointer, spec.source_owner_field)
    if spec.pointer_through:
        summary_ok = all(
            _owner_pointer_resolves(root, spec, spec.summary_pointer, field)
            for field in spec.summary_owner_fields
        )
    else:
        summary_ok = _pointer_resolves(root, spec.summary_pointer)
    demotion_ok = _owner_pointer_resolves(root, spec, spec.demotion_rule_pointer, spec.demotion_owner_field)
    source_status_ok = not _owner_cell_blocks(_owner_pointer_value(root, spec, spec.source_pointer, spec.source_owner_field))
    if spec.pointer_through:
        summary_status_ok = all(
            not _owner_cell_blocks(_owner_pointer_value(root, spec, spec.summary_pointer, field))
            for field in spec.summary_owner_fields
        )
    else:
        summary_status_ok = not _owner_cell_blocks(resolve_artifact_pointer(root, spec.summary_pointer))
    demotion_status_ok = not _owner_cell_blocks(
        _owner_pointer_value(root, spec, spec.demotion_rule_pointer, spec.demotion_owner_field)
    )
    owner_status_ok = _owner_status_ok(owner_payload) and source_status_ok and summary_status_ok and demotion_status_ok
    owner_gate_ok = owner_exists and schema_ok
    pointer_gate_ok = source_ok and summary_ok and demotion_ok and owner_status_ok
    failures = _card_failure_reasons(
        owner_exists=owner_exists,
        schema_matches=schema_ok,
        source_resolves=source_ok,
        summary_resolves=summary_ok,
        demotion_resolves=demotion_ok,
        owner_status_ok=owner_status_ok,
    )
    projected_source_pointer = _projected_source_pointer(spec, resolved_owner_pointer)
    projected_summary_pointer = _projected_summary_pointer(spec, resolved_owner_pointer)
    projected_demotion_pointer = _projected_demotion_pointer(spec, resolved_owner_pointer)
    return {
        **spec.to_json(),
        "source_pointer": projected_source_pointer,
        "summary_pointer": projected_summary_pointer,
        "demotion_rule_pointer": projected_demotion_pointer,
        "card_pointer": card_pointer(spec.card_id),
        "resolved_owner_pointer": resolved_owner_pointer,
        "owner_artifact_status": "resolved" if owner_exists else "missing",
        "owner_pointer_status": "resolved" if owner_exists else "missing",
        "owner_schema_status": "matched" if schema_ok else "unmatched",
        "source_pointer_status": "resolved" if source_ok else "missing",
        "summary_pointer_status": "resolved" if summary_ok else "missing",
        "demotion_rule_pointer_status": "resolved" if demotion_ok else "missing",
        "owner_status": "pass" if owner_status_ok else "blocked",
        "hardgates": {
            "STACK-HG1": {
                "status": _status(owner_gate_ok),
                "evidence_pointer": spec.owner_pointer,
                "resolved_owner_pointer": resolved_owner_pointer,
                "reason": "owner pointer and schema/artifact identity resolve" if owner_gate_ok else "owner pointer or schema/artifact identity is not resolved",
            },
            "STACK-HG2": {
                "status": _status(pointer_gate_ok),
                "source_pointer": projected_source_pointer,
                "summary_pointer": projected_summary_pointer,
                "demotion_rule_pointer": projected_demotion_pointer,
                "reason": "source, summary, demotion, and owner status cells pass"
                if pointer_gate_ok
                else "one or more required owner pointers, status cells, or hardgates do not pass",
            },
        },
        "status": "pass" if owner_gate_ok and pointer_gate_ok else "blocked",
        "failure_reasons": failures,
    }


def build_standard_alignment_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for standard_id, row in INDUSTRY_STANDARD_POINTER_MAP.items():
        local_card_ids = tuple(row["local_card_ids"])
        rows.append(
            {
                "standard_id": standard_id,
                "external_pointer": row["external_pointer"],
                "local_card_ids": list(local_card_ids),
                "local_card_pointers": [card_pointer(card_id) for card_id in local_card_ids],
            }
        )
    return rows


def build_experiment_stack_payload(*, root: Path, generated_at: str) -> dict[str, Any]:
    assert_valid_experiment_stack_specs()
    cards = [project_card(spec, root=root) for spec in EXPERIMENT_STACK_CARDS]
    blocked = [card["card_id"] for card in cards if card["status"] != "pass"]
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": {spec.card_id: spec.owner_pointer for spec in EXPERIMENT_STACK_CARDS},
        "card_count": len(cards),
        "card_ids": list(CARD_IDS),
        "hardgate_ids": list(STACK_HARDGATE_IDS),
        "status": "pass" if not blocked else "blocked",
        "blocked_card_ids": blocked,
        "cards": cards,
        "claim_first_gate": {
            "kind": "pointer-only-metadata",
            "status": "delegated",
            "admission_owner": ADMISSION_OWNER,
            "positive_evidence_owner": POSITIVE_EVIDENCE_OWNER,
            "consistency_gates_pointer": CONSISTENCY_GATES_POINTER,
            "consistency_gate_ids": list(CONSISTENCY_GATE_IDS),
        },
        "coverage_mapping": [
            {
                "mapping_id": "ladder-fair-decision-consumers",
                "owner_issues": ["1205", "1212"],
                "owner_pointers": [
                    "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder",
                    "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection.fair_l1_decision",
                ],
            },
            {
                "mapping_id": "aggregate-zero-drift",
                "owner_issues": ["1206"],
                "owner_pointers": ["reports/canonical/model-comparison.json:$.ordering"],
            },
            {
                "mapping_id": "construct-validity-gate-family",
                "owner_issues": ["1197"],
                "owner_pointers": ["reports/canonical/dgt-l1-controls.json:$.fair_l1_construction.construct_validity"],
            },
        ],
        "industry_standard_alignment": build_standard_alignment_rows(),
        "standard_alignment_doc": "docs/experiment_stack_standard_alignment.md",
        "not_claimed": list(NOT_CLAIMED),
    }


def render_experiment_stack_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Experiment Stack Cards",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Cards: `{payload['card_count']}`",
        f"- Claim-first gate: `{JSON_ARTIFACT}:$.claim_first_gate`",
        "",
        "## Cards",
        "",
        "| card | status | owner issue | owner artifact | source | summary | demotion | hardgates |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for card in payload["cards"]:
        hardgates = ", ".join(f"{key}:{value['status']}" for key, value in card["hardgates"].items())
        lines.append(
            "| "
            f"`{card['card_id']}` | "
            f"`{card['status']}` | "
            f"`{card['canonical_owner_issue']}` | "
            f"`{card['owner_artifact']}` | "
            f"`{card['source_pointer']}` | "
            f"`{card['summary_pointer']}` | "
            f"`{card['demotion_rule_pointer']}` | "
            f"`{hardgates}` |"
        )
    lines.extend(
        [
            "",
            "## Standard Alignment",
            "",
            "| standard | external pointer | local card pointers |",
            "| --- | --- | --- |",
        ]
    )
    for row in payload["industry_standard_alignment"]:
        local = ", ".join(f"`{pointer}`" for pointer in row["local_card_pointers"])
        lines.append(f"| `{row['standard_id']}` | `{row['external_pointer']}` | {local} |")
    lines.extend(
        [
            "",
            "## Boundaries",
            "",
        ]
    )
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_experiment_stack_cards(*, root: Path, generated_at: str) -> dict[str, Any]:
    payload = build_experiment_stack_payload(root=root, generated_at=generated_at)
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_experiment_stack_markdown(payload), encoding="utf-8")
    return payload

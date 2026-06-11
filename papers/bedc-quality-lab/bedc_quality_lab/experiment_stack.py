"""Finite experiment-stack card contract and claim-first gate."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:experiment-stack-cards"
ARTIFACT_ID = "bedc-quality-lab:experiment-stack-cards"
JSON_ARTIFACT = "reports/canonical/experiment_stack_cards.json"
MARKDOWN_ARTIFACT = "reports/canonical/experiment_stack_cards.md"
PRODUCER = "scripts/run_experiment_stack_cards.py"
LAB_ROOT = Path(__file__).resolve().parents[1]

STACK_HARDGATE_IDS = ("STACK-HG1", "STACK-HG2")
REQUIRED_PREFLIGHT_CARD_IDS = (
    "claim-card",
    "task-target-card",
    "feature-access-card",
    "baseline-validity-card",
    "ood-solvability-card",
    "metric-provenance-card",
)
OWNER_BACKED_CARD_IDS = (
    "feature-access-card",
    "ood-solvability-card",
    "metric-provenance-card",
    "artifact-reproducibility-card",
    "model-card",
)
NOT_CLAIMED = (
    "The card report is an auxiliary contract and does not promote model quality.",
    "Blocked card rows are owner gaps, not negative empirical evidence.",
    "Claim-first gating only controls training-result promotion ordering.",
    "External standard alignment is pointer-only and carries no independent certification.",
)


@dataclass(**{"froz" + "en": True})
class ExperimentStackCardSpec:
    card_id: str
    canonical_owner_issue: str
    owner_artifact: str
    schema_id: str
    hardgate_prefixes: tuple[str, ...]
    demotion_rule_pointer: str
    source_pointer: str
    summary_pointer: str
    phase: str
    depends_on_cards: tuple[str, ...]

    def to_json(self) -> dict[str, Any]:
        return {
            "card_id": self.card_id,
            "canonical_owner_issue": self.canonical_owner_issue,
            "owner_artifact": self.owner_artifact,
            "schema_id": self.schema_id,
            "hardgate_prefixes": list(self.hardgate_prefixes),
            "demotion_rule_pointer": self.demotion_rule_pointer,
            "source_pointer": self.source_pointer,
            "summary_pointer": self.summary_pointer,
            "phase": self.phase,
            "depends_on_cards": list(self.depends_on_cards),
        }


@dataclass(**{"froz" + "en": True})
class ClaimFirstGateDecision:
    status: str
    failed_card_ids: tuple[str, ...]
    blocked_training_result_refs: tuple[str, ...]
    pointer_reasons: Mapping[str, str]

    def to_json(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "failed_card_ids": list(self.failed_card_ids),
            "blocked_training_result_refs": list(self.blocked_training_result_refs),
            "pointer_reasons": dict(self.pointer_reasons),
        }


def _planned_artifact(card_id: str) -> str:
    return f"reports/canonical/experiment_stack_{card_id.replace('-', '_')}.json"


def _planned_pointer(card_id: str, pointer: str) -> str:
    return f"{_planned_artifact(card_id)}:{pointer}"


EXPERIMENT_STACK_CARDS: tuple[ExperimentStackCardSpec, ...] = (
    ExperimentStackCardSpec(
        card_id="claim-card",
        canonical_owner_issue="child-of-1219:claim-card",
        owner_artifact=_planned_artifact("claim-card"),
        schema_id="bedc-quality-lab:experiment-stack-claim-card",
        hardgate_prefixes=("CLAIM-HG",),
        demotion_rule_pointer=_planned_pointer("claim-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("claim-card", "$.claim_surface"),
        summary_pointer=_planned_pointer("claim-card", "$.summary"),
        phase="preflight",
        depends_on_cards=(),
    ),
    ExperimentStackCardSpec(
        card_id="task-target-card",
        canonical_owner_issue="child-of-1219:task-target-card",
        owner_artifact=_planned_artifact("task-target-card"),
        schema_id="bedc-quality-lab:experiment-stack-task-target-card",
        hardgate_prefixes=("TARGET-HG",),
        demotion_rule_pointer=_planned_pointer("task-target-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("task-target-card", "$.label_function"),
        summary_pointer=_planned_pointer("task-target-card", "$.summary"),
        phase="preflight",
        depends_on_cards=("claim-card",),
    ),
    ExperimentStackCardSpec(
        card_id="data-card",
        canonical_owner_issue="child-of-1219:data-card",
        owner_artifact=_planned_artifact("data-card"),
        schema_id="bedc-quality-lab:experiment-stack-data-card",
        hardgate_prefixes=("DATA-HG",),
        demotion_rule_pointer=_planned_pointer("data-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("data-card", "$.data_boundary"),
        summary_pointer=_planned_pointer("data-card", "$.summary"),
        phase="preflight",
        depends_on_cards=("task-target-card",),
    ),
    ExperimentStackCardSpec(
        card_id="feature-access-card",
        canonical_owner_issue="1209",
        owner_artifact="reports/canonical/dgt-l1-controls.json",
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
        canonical_owner_issue="child-of-1219:baseline-validity-card",
        owner_artifact=_planned_artifact("baseline-validity-card"),
        schema_id="bedc-quality-lab:experiment-stack-baseline-validity-card",
        hardgate_prefixes=("BASE-HG",),
        demotion_rule_pointer=_planned_pointer("baseline-validity-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("baseline-validity-card", "$.baseline_contract"),
        summary_pointer=_planned_pointer("baseline-validity-card", "$.summary"),
        phase="preflight",
        depends_on_cards=("task-target-card", "feature-access-card"),
    ),
    ExperimentStackCardSpec(
        card_id="ood-solvability-card",
        canonical_owner_issue="1209,1203",
        owner_artifact="reports/canonical/model-comparison.json",
        schema_id="bedc-quality-lab:model-comparison",
        hardgate_prefixes=("MC-HG", "L1-REVIEW-HG"),
        demotion_rule_pointer="reports/canonical/model-comparison.json:$.hardgates.MC-HG7",
        source_pointer="reports/canonical/model-comparison.json:$.models[0].metrics.ood_accuracy",
        summary_pointer="reports/canonical/model-comparison.json:$.models[0].metrics_by_surface.out_of_distribution",
        phase="preflight",
        depends_on_cards=("task-target-card", "data-card"),
    ),
    ExperimentStackCardSpec(
        card_id="metric-provenance-card",
        canonical_owner_issue="1201",
        owner_artifact="reports/canonical/model-comparison.json",
        schema_id="bedc-quality-lab:model-comparison",
        hardgate_prefixes=("MC-HG",),
        demotion_rule_pointer="reports/canonical/model-comparison.json:$.hardgates.MC-HG3",
        source_pointer="reports/canonical/model-comparison.json:$.models[0].metrics",
        summary_pointer="reports/canonical/model-comparison.json:$.ranking_key",
        phase="preflight",
        depends_on_cards=("claim-card", "task-target-card"),
    ),
    ExperimentStackCardSpec(
        card_id="training-authenticity-card",
        canonical_owner_issue="child-of-1219:training-authenticity-card",
        owner_artifact=_planned_artifact("training-authenticity-card"),
        schema_id="bedc-quality-lab:experiment-stack-training-authenticity-card",
        hardgate_prefixes=("TRAIN-HG",),
        demotion_rule_pointer=_planned_pointer("training-authenticity-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("training-authenticity-card", "$.training_trace"),
        summary_pointer=_planned_pointer("training-authenticity-card", "$.summary"),
        phase="evidence",
        depends_on_cards=("baseline-validity-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="statistical-evidence-card",
        canonical_owner_issue="child-of-1219:statistical-evidence-card",
        owner_artifact=_planned_artifact("statistical-evidence-card"),
        schema_id="bedc-quality-lab:experiment-stack-statistical-evidence-card",
        hardgate_prefixes=("STAT-HG",),
        demotion_rule_pointer=_planned_pointer("statistical-evidence-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("statistical-evidence-card", "$.statistical_protocol"),
        summary_pointer=_planned_pointer("statistical-evidence-card", "$.summary"),
        phase="evidence",
        depends_on_cards=("training-authenticity-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="ablation-causal-evidence-card",
        canonical_owner_issue="child-of-1219:ablation-causal-evidence-card",
        owner_artifact=_planned_artifact("ablation-causal-evidence-card"),
        schema_id="bedc-quality-lab:experiment-stack-ablation-causal-evidence-card",
        hardgate_prefixes=("CAUSE-HG",),
        demotion_rule_pointer=_planned_pointer("ablation-causal-evidence-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("ablation-causal-evidence-card", "$.causal_evidence"),
        summary_pointer=_planned_pointer("ablation-causal-evidence-card", "$.summary"),
        phase="evidence",
        depends_on_cards=("training-authenticity-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="artifact-reproducibility-card",
        canonical_owner_issue="1213",
        owner_artifact="reports/release_manifest_sidecar.json",
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
        owner_artifact="reports/canonical/model_design_suite.json",
        schema_id="bedc-quality-lab:model-design-suite",
        hardgate_prefixes=("SUITE-HG",),
        demotion_rule_pointer="reports/canonical/model_design_suite.json:$.not_claimed",
        source_pointer="reports/canonical/model_design_suite.json:$.rows",
        summary_pointer="reports/canonical/model_design_suite.json:$.status",
        phase="release",
        depends_on_cards=("claim-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="risk-scope-review-card",
        canonical_owner_issue="child-of-1219:risk-scope-review-card",
        owner_artifact=_planned_artifact("risk-scope-review-card"),
        schema_id="bedc-quality-lab:experiment-stack-risk-scope-review-card",
        hardgate_prefixes=("RISK-HG",),
        demotion_rule_pointer=_planned_pointer("risk-scope-review-card", "$.demotion_rule"),
        source_pointer=_planned_pointer("risk-scope-review-card", "$.scope_review"),
        summary_pointer=_planned_pointer("risk-scope-review-card", "$.summary"),
        phase="release",
        depends_on_cards=("claim-card", "data-card", "metric-provenance-card"),
    ),
    ExperimentStackCardSpec(
        card_id="release-readiness-board",
        canonical_owner_issue="child-of-1219:release-readiness-board",
        owner_artifact=_planned_artifact("release-readiness-board"),
        schema_id="bedc-quality-lab:experiment-stack-release-readiness-board",
        hardgate_prefixes=("READY-HG",),
        demotion_rule_pointer=_planned_pointer("release-readiness-board", "$.demotion_rule"),
        source_pointer=_planned_pointer("release-readiness-board", "$.release_board"),
        summary_pointer=_planned_pointer("release-readiness-board", "$.summary"),
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
        if not spec.owner_artifact.endswith(".json"):
            errors.append(f"{spec.card_id}:owner-artifact")
        if not spec.schema_id.startswith("bedc-quality-lab:"):
            errors.append(f"{spec.card_id}:schema-id")
        if not spec.hardgate_prefixes:
            errors.append(f"{spec.card_id}:hardgate-prefix")
        for pointer_name in ("demotion_rule_pointer", "source_pointer", "summary_pointer"):
            pointer = getattr(spec, pointer_name)
            if split_artifact_pointer(pointer) is None:
                errors.append(f"{spec.card_id}:{pointer_name}")
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


def _load_json_object(root: Path, artifact: str) -> Mapping[str, Any] | None:
    path = root / artifact
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, Mapping) else None


def _schema_matches(payload: Mapping[str, Any] | None, schema_id: str) -> bool:
    if payload is None:
        return False
    return payload.get("schema_id") == schema_id or payload.get("artifact_id") == schema_id


def _pointer_resolves(root: Path, pointer: str) -> bool:
    return resolve_artifact_pointer(root, pointer) is not None


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def _card_failure_reasons(
    *,
    owner_exists: bool,
    schema_matches: bool,
    source_resolves: bool,
    summary_resolves: bool,
    demotion_resolves: bool,
) -> list[str]:
    reasons: list[str] = []
    if not owner_exists:
        reasons.append("owner-artifact-missing")
    elif not schema_matches:
        reasons.append("owner-schema-mismatch")
    if not source_resolves:
        reasons.append("source-pointer-unresolved")
    if not summary_resolves:
        reasons.append("summary-pointer-unresolved")
    if not demotion_resolves:
        reasons.append("demotion-rule-pointer-unresolved")
    return reasons


def project_card(spec: ExperimentStackCardSpec, *, root: Path) -> dict[str, Any]:
    owner_payload = _load_json_object(root, spec.owner_artifact)
    owner_exists = owner_payload is not None
    schema_ok = _schema_matches(owner_payload, spec.schema_id)
    source_ok = _pointer_resolves(root, spec.source_pointer)
    summary_ok = _pointer_resolves(root, spec.summary_pointer)
    demotion_ok = _pointer_resolves(root, spec.demotion_rule_pointer)
    owner_gate_ok = owner_exists and schema_ok
    pointer_gate_ok = source_ok and summary_ok and demotion_ok
    failures = _card_failure_reasons(
        owner_exists=owner_exists,
        schema_matches=schema_ok,
        source_resolves=source_ok,
        summary_resolves=summary_ok,
        demotion_resolves=demotion_ok,
    )
    return {
        **spec.to_json(),
        "card_pointer": card_pointer(spec.card_id),
        "owner_artifact_status": "resolved" if owner_exists else "missing",
        "owner_schema_status": "matched" if schema_ok else "unmatched",
        "source_pointer_status": "resolved" if source_ok else "missing",
        "summary_pointer_status": "resolved" if summary_ok else "missing",
        "demotion_rule_pointer_status": "resolved" if demotion_ok else "missing",
        "hardgates": {
            "STACK-HG1": {
                "status": _status(owner_gate_ok),
                "evidence_pointer": f"{spec.owner_artifact}:$",
                "reason": "owner artifact and schema resolve" if owner_gate_ok else "owner artifact or schema is not resolved",
            },
            "STACK-HG2": {
                "status": _status(pointer_gate_ok),
                "source_pointer": spec.source_pointer,
                "summary_pointer": spec.summary_pointer,
                "demotion_rule_pointer": spec.demotion_rule_pointer,
                "reason": "source, summary, and demotion pointers resolve"
                if pointer_gate_ok
                else "one or more required card pointers do not resolve",
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
        "source_artifacts": {spec.card_id: spec.owner_artifact for spec in EXPERIMENT_STACK_CARDS},
        "card_count": len(cards),
        "card_ids": list(CARD_IDS),
        "hardgate_ids": list(STACK_HARDGATE_IDS),
        "status": "pass" if not blocked else "blocked",
        "blocked_card_ids": blocked,
        "owner_backed_card_ids": list(OWNER_BACKED_CARD_IDS),
        "cards": cards,
        "claim_first_gate": {
            "status": "active",
            "required_preflight_cards": list(REQUIRED_PREFLIGHT_CARD_IDS),
            "cards_pointer": f"{JSON_ARTIFACT}:$.cards",
            "training_result_refs_pointer": "$.training_result_refs",
            "decision_function": "bedc_quality_lab.experiment_stack.evaluate_claim_first_gate",
        },
        "coverage_mapping": [
            {
                "mapping_id": "ladder-fair-decision-consumers",
                "owner_issues": ["1205", "1212"],
                "owner_pointers": [
                    "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder",
                    "reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit",
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
                "owner_pointers": ["reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit.construct_validity"],
            },
        ],
        "industry_standard_alignment": build_standard_alignment_rows(),
        "standard_alignment_doc": "docs/experiment_stack_standard_alignment.md",
        "not_claimed": list(NOT_CLAIMED),
    }


def _training_result_ref(row: Any, index: int) -> str:
    if isinstance(row, str):
        return row
    if isinstance(row, Mapping):
        for key in ("ref", "pointer", "artifact_pointer"):
            value = row.get(key)
            if isinstance(value, str):
                return value
    return f"$.training_result_refs[{index}]"


def _rows_by_card_id(cards: Any) -> dict[str, Mapping[str, Any]]:
    if not isinstance(cards, Sequence) or isinstance(cards, (str, bytes)):
        return {}
    rows: dict[str, Mapping[str, Any]] = {}
    for row in cards:
        if isinstance(row, Mapping):
            card_id = row.get("card_id")
            if isinstance(card_id, str):
                rows[card_id] = row
    return rows


def _context_cards(context: Mapping[str, Any]) -> Any:
    experiment_stack = context.get("experiment_stack")
    if isinstance(experiment_stack, Mapping):
        return experiment_stack.get("cards")
    return context.get("cards")


def _is_training_promotion_context(context: Mapping[str, Any], training_refs: Sequence[Any]) -> bool:
    claim_kind = context.get("claim_kind")
    return bool(training_refs) or claim_kind in {"promoted_training", "training_result_promotion"}


def _card_reason(card_id: str, row: Mapping[str, Any] | None) -> str:
    if row is None:
        if card_id == "task-target-card":
            return "missing label-function and target card before training-result promotion"
        if card_id == "baseline-validity-card":
            return "missing baseline-validity card before training-result promotion"
        return "missing required preflight card before training-result promotion"
    failures = row.get("failure_reasons")
    if isinstance(failures, Sequence) and not isinstance(failures, (str, bytes)) and failures:
        return ", ".join(str(item) for item in failures)
    return f"card status is {row.get('status', 'missing')}"


def _context_root(context: Mapping[str, Any]) -> Path:
    value = context.get("root", context.get("artifact_root", context.get("lab_root")))
    if isinstance(value, Path):
        return value
    if isinstance(value, str):
        return Path(value)
    return LAB_ROOT


def _hardgate_status(row: Mapping[str, Any], hardgate_id: str) -> str | None:
    hardgates = row.get("hardgates")
    if not isinstance(hardgates, Mapping):
        return None
    hardgate = hardgates.get(hardgate_id)
    if not isinstance(hardgate, Mapping):
        return None
    status = hardgate.get("status")
    return status if isinstance(status, str) else None


def _preflight_card_failures(spec: ExperimentStackCardSpec, row: Mapping[str, Any] | None, *, root: Path) -> tuple[str, ...]:
    if row is None:
        return (_card_reason(spec.card_id, None),)

    failures: list[str] = []
    projected = project_card(spec, root=root)
    expected_fields = (
        "owner_artifact",
        "schema_id",
        "source_pointer",
        "summary_pointer",
        "demotion_rule_pointer",
        "card_pointer",
    )
    for field in expected_fields:
        if row.get(field) != projected[field]:
            failures.append(f"{field}-mismatch")

    expected_statuses = {
        "status": "pass",
        "owner_artifact_status": "resolved",
        "owner_schema_status": "matched",
        "source_pointer_status": "resolved",
        "summary_pointer_status": "resolved",
        "demotion_rule_pointer_status": "resolved",
    }
    for field, expected in expected_statuses.items():
        if row.get(field) != expected:
            failures.append(f"{field}-not-{expected}")

    for hardgate_id in STACK_HARDGATE_IDS:
        if _hardgate_status(row, hardgate_id) != "pass":
            failures.append(f"{hardgate_id}-not-pass")

    if projected["status"] != "pass":
        failures.extend(str(reason) for reason in projected["failure_reasons"])
    for hardgate_id in STACK_HARDGATE_IDS:
        if projected["hardgates"][hardgate_id]["status"] != "pass":
            failures.append(f"{hardgate_id}-evidence-not-pass")

    return tuple(dict.fromkeys(failures))


def evaluate_claim_first_gate(context: Mapping[str, Any]) -> ClaimFirstGateDecision:
    training_refs_value = context.get("training_result_refs")
    training_refs = list(training_refs_value) if isinstance(training_refs_value, Sequence) and not isinstance(training_refs_value, (str, bytes)) else []
    if not _is_training_promotion_context(context, training_refs):
        return ClaimFirstGateDecision(
            status="not-applicable",
            failed_card_ids=(),
            blocked_training_result_refs=(),
            pointer_reasons={},
        )
    cards = _rows_by_card_id(_context_cards(context))
    root = _context_root(context)
    specs = spec_by_card_id()
    failed: list[str] = []
    reasons: dict[str, str] = {}
    for card_id in REQUIRED_PREFLIGHT_CARD_IDS:
        row = cards.get(card_id)
        card_failures = _preflight_card_failures(specs[card_id], row, root=root)
        if card_failures:
            failed.append(card_id)
            reasons[card_id] = ", ".join(card_failures)
    blocked_refs = tuple(_training_result_ref(row, index) for index, row in enumerate(training_refs))
    if failed:
        return ClaimFirstGateDecision(
            status="blocked",
            failed_card_ids=tuple(failed),
            blocked_training_result_refs=blocked_refs or ("$.training_result_refs",),
            pointer_reasons=reasons,
        )
    return ClaimFirstGateDecision(
        status="pass",
        failed_card_ids=(),
        blocked_training_result_refs=(),
        pointer_reasons={},
    )


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

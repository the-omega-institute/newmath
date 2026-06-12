"""Pointer-only base-undertraining audit for DGT L1 controls."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:dgt-base-undertraining-audit"
ARTIFACT_ID = "bedc-quality-lab:dgt-base-undertraining-audit"
PRODUCER = "scripts/run_dgt_base_undertraining_audit.py"
L1_SOURCE_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
INPUT_ACCESSIBILITY_SOURCE_ARTIFACT = "reports/canonical/input-accessibility.json"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.fingerprint.json"
CONTROLLER_EVIDENCE_POINTER = "https://github.com/the-omega-institute/newmath/issues/1190#issuecomment-4672534911"
FAIR_RECONSTRUCTION_POINTER = "https://github.com/the-omega-institute/newmath/issues/1196"
FEATURE_SOURCE_POINTER = "bedc_quality_lab/dgt_l1_controls.py:_TinySequenceModel._features"
LABEL_SOURCE_POINTER = "bedc_quality_lab/dgt_l1_controls.py:_make_sequences"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
REQUIRED_COMPARISONS = ("equal_step", "equal_compute", "equal_loss_decrease")
REQUIRED_BASE_GRID = (36, 72, 128, 256, 512)
NOT_CLAIMED = (
    "Bounded L1 tiny-sequence base-undertraining audit only.",
    "No undertraining discharge claim under information-starved baseline.",
    "No production deployment claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No cross-level verdict inheritance.",
)


@dataclass(frozen=True)
class BaseUndertrainingComparisonRow:
    comparison_id: str
    status: str
    source_artifact: str
    source_pointer: str
    match_axis: str
    match_value: float | int | None
    base_metric: float | None
    dgt_metric: float | None
    ci_overlap: bool | None
    ci_low_separation: float | None
    decision: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "comparison_id": self.comparison_id,
            "status": self.status,
            "source_artifact": self.source_artifact,
            "source_pointer": self.source_pointer,
            "match_axis": self.match_axis,
            "match_value": self.match_value,
            "base_metric": self.base_metric,
            "dgt_metric": self.dgt_metric,
            "ci_overlap": self.ci_overlap,
            "ci_low_separation": self.ci_low_separation,
            "decision": self.decision,
        }


@dataclass(frozen=True)
class BaseUndertrainingAudit:
    source_contract: Mapping[str, Any]
    construct_validity: Mapping[str, Any]
    comparison_rows: Sequence[Mapping[str, Any]]
    hardgates: Mapping[str, Any]
    mechanical_decision_table: Sequence[Mapping[str, str]]
    verdict: str
    claim_action: str
    boundary_ledger: Sequence[Mapping[str, Any]]
    evidence_ledger: Sequence[Mapping[str, Any]]
    not_claimed: Sequence[str]
    revoke_if: Sequence[str]

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "source_contract": dict(self.source_contract),
            "construct_validity": dict(self.construct_validity),
            "comparison_rows": list(self.comparison_rows),
            "hardgates": dict(self.hardgates),
            "mechanical_decision_table": list(self.mechanical_decision_table),
            "verdict": self.verdict,
            "claim_action": self.claim_action,
            "boundary_ledger": list(self.boundary_ledger),
            "evidence_ledger": list(self.evidence_ledger),
            "not_claimed": list(self.not_claimed),
            "revoke_if": list(self.revoke_if),
        }


def mechanical_decision_table() -> list[dict[str, str]]:
    return [
        {
            "condition": "baseline input bandwidth is lower than the label dependency bandwidth",
            "verdict": "construct-boundary",
            "claim_action": "defer-to-fair-reconstruction",
        },
        {
            "condition": "any required comparison row is missing or has unresolved source evidence",
            "verdict": "inconclusive",
            "claim_action": "hold",
        },
        {
            "condition": "base grid does not cover DGT compute and loss-decrease intervals",
            "verdict": "inconclusive",
            "claim_action": "hold",
        },
        {
            "condition": "equal-compute row has CI overlap or nonpositive CI-low separation",
            "verdict": "downgrade",
            "claim_action": "fair_compute_artifact",
        },
        {
            "condition": "equal-loss-decrease row has CI overlap or nonpositive CI-low separation",
            "verdict": "downgrade",
            "claim_action": "fair_loss_decrease_artifact",
        },
        {
            "condition": "all required rows resolve and non-informative rows retain positive CI-low separation",
            "verdict": "noninformative-separation",
            "claim_action": "record_noninformative_rows",
        },
    ]


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json_artifact(root: Path, artifact: str) -> tuple[str, dict[str, Any] | None, str | None]:
    path = root / artifact
    if not path.exists():
        return "missing", None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid", None, None
    if not isinstance(payload, dict):
        return "invalid", None, _file_digest(path)
    return "resolved", payload, _file_digest(path)


def _row_pointer(row: Mapping[str, Any]) -> str:
    return f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}#row_id={row['row_id']}"


def _input_accessibility_preconditions(
    root: Path,
    payload: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    status = "resolved"
    digest: str | None = None
    if payload is None:
        status, loaded, digest = _load_json_artifact(root, INPUT_ACCESSIBILITY_SOURCE_ARTIFACT)
        payload = loaded
    else:
        digest = _json_digest(payload)
    if status != "resolved" or not isinstance(payload, Mapping):
        return {
            "status": status,
            "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
            "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms_ref": [],
            "unanswerable_ood_splits_ref": [],
            "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            "source_pointers": {
                "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
                "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            },
            "sha256": digest,
            "failures": ["input-accessibility-artifact-unresolved"],
        }
    rows = payload.get("rows")
    consumers = payload.get("consumer_pointers")
    boundary = payload.get("boundary_ledger")
    if not isinstance(rows, list) or not isinstance(consumers, Mapping) or not isinstance(boundary, list):
        return {
            "status": "invalid",
            "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
            "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms_ref": [],
            "unanswerable_ood_splits_ref": [],
            "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            "source_pointers": {
                "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
                "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            },
            "sha256": digest,
            "failures": ["input-accessibility-shape-mismatch"],
        }
    rows_by_pointer = {
        _row_pointer(row): row
        for row in rows
        if isinstance(row, Mapping) and isinstance(row.get("row_id"), str)
    }
    information_refs = consumers.get("information_starved_arms_ref")
    unanswerable_refs = consumers.get("unanswerable_ood_splits_ref")
    failures: list[str] = []
    if consumers.get("input_accessibility_ref") != f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$":
        failures.append("input-accessibility-root-pointer-mismatch")
    if not isinstance(information_refs, list) or not all(ref in rows_by_pointer for ref in information_refs):
        failures.append("information-starved-pointer-unresolved")
        information_refs = []
    if not isinstance(unanswerable_refs, list) or not all(ref in rows_by_pointer for ref in unanswerable_refs):
        failures.append("unanswerable-ood-pointer-unresolved")
        unanswerable_refs = []
    information_rows = [rows_by_pointer[ref] for ref in information_refs]
    unanswerable_rows = [rows_by_pointer[ref] for ref in unanswerable_refs]
    if not information_rows:
        failures.append("information-starved-precondition-empty")
    if not unanswerable_rows:
        failures.append("unanswerable-ood-precondition-empty")
    missing_variables = sorted({
        variable
        for row in information_rows + unanswerable_rows
        for variable in row.get("missing_variables", [])
    })
    return {
        "status": "pass" if not failures else "fail",
        "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
        "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
        "information_starved_arms_ref": list(information_refs),
        "unanswerable_ood_splits_ref": list(unanswerable_refs),
        "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
        "boundary_ledger_count": len(boundary),
        "information_starved_row_count": len(information_rows),
        "unanswerable_ood_row_count": len(unanswerable_rows),
        "missing_variables": missing_variables,
        "source_pointers": {
            "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.consumer_pointers.information_starved_arms_ref",
            "unanswerable_ood_splits": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.consumer_pointers.unanswerable_ood_splits_ref",
            "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
        },
        "sha256": digest,
        "failures": failures,
    }


def _is_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def _round(value: float | None) -> float | None:
    return None if value is None else round(value, 6)


def _gcd(left: int, right: int) -> int:
    while right:
        left, right = right, left % right
    return abs(left)


def _step_rows(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = payload.get("l1_step_ladder", {}).get("per_step")
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, Mapping)]


def _metric(row: Mapping[str, Any], key: str) -> float | None:
    metrics = row.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    value = metrics.get(key)
    return float(value) if _is_number(value) else None


def _compute(row: Mapping[str, Any], arm_id: str) -> float | None:
    per_arm = row.get("compute_ledger", {}).get("per_arm")
    if not isinstance(per_arm, Mapping):
        return None
    arm = per_arm.get(arm_id)
    if not isinstance(arm, Mapping):
        return None
    value = arm.get("compute_units")
    return float(value) if _is_number(value) else None


def _steps(row: Mapping[str, Any]) -> int | None:
    value = row.get("training_steps")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else None


def _public_pointer(row: Mapping[str, Any], index: int) -> str:
    pointer = row.get("pointer")
    if isinstance(pointer, str) and pointer.startswith(f"{L1_SOURCE_ARTIFACT}:"):
        return pointer
    return f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step[{index}]"


def _row_by_steps(rows: Sequence[Mapping[str, Any]], steps: int) -> tuple[int, Mapping[str, Any]] | None:
    for index, row in enumerate(rows):
        if _steps(row) == steps:
            return index, row
    return None


def _nearest_by_value(
    rows: Sequence[Mapping[str, Any]],
    *,
    value_getter,
    target: float,
) -> tuple[int, Mapping[str, Any], float] | None:
    candidates: list[tuple[float, int, Mapping[str, Any], float]] = []
    for index, row in enumerate(rows):
        value = value_getter(row)
        if value is not None:
            candidates.append((abs(value - target), index, row, value))
    if not candidates:
        return None
    _distance, index, row, value = min(candidates, key=lambda item: (item[0], _steps(item[2]) or 0))
    return index, row, value


def _comparison_row(
    *,
    comparison_id: str,
    source_index: int | None,
    source_row: Mapping[str, Any] | None,
    match_axis: str,
    match_value: float | int | None,
    missing_reason: str | None = None,
) -> BaseUndertrainingComparisonRow:
    if source_index is None or source_row is None:
        return BaseUndertrainingComparisonRow(
            comparison_id=comparison_id,
            status="missing",
            source_artifact=L1_SOURCE_ARTIFACT,
            source_pointer=f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step",
            match_axis=match_axis,
            match_value=match_value,
            base_metric=None,
            dgt_metric=None,
            ci_overlap=None,
            ci_low_separation=None,
            decision=missing_reason or "required-evidence-missing",
        )
    base_metric = _metric(source_row, "information_starved_accuracy_mean")
    dgt_metric = _metric(source_row, "dgt_accuracy_mean")
    if base_metric is None or dgt_metric is None:
        status = "missing"
        ci_overlap = None
        ci_low = None
        decision = "required-metric-missing"
    else:
        ci_low = dgt_metric - base_metric
        ci_overlap = ci_low <= 0.0
        status = "resolved"
        decision = "information-starved-catches-up" if ci_overlap else "noninformative-dgt-separated"
    return BaseUndertrainingComparisonRow(
        comparison_id=comparison_id,
        status=status,
        source_artifact=L1_SOURCE_ARTIFACT,
        source_pointer=_public_pointer(source_row, source_index),
        match_axis=match_axis,
        match_value=_round(float(match_value)) if isinstance(match_value, float) else match_value,
        base_metric=_round(base_metric),
        dgt_metric=_round(dgt_metric),
        ci_overlap=ci_overlap,
        ci_low_separation=_round(ci_low),
        decision=decision,
    )


def _base_grid_coverage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    observed = sorted(step for row in rows if (step := _steps(row)) is not None)
    expected_present = all(step in observed for step in REQUIRED_BASE_GRID)
    return {
        "required_grid": list(REQUIRED_BASE_GRID),
        "observed_grid": observed,
        "required_grid_present": expected_present,
        "covers_dgt_compute_loss_interval": bool(observed and min(observed) <= 36 <= max(observed)),
        "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
    }


def construct_validity_assessment(
    *,
    baseline_input_order: int = 1,
    label_dependency_order: int = 2,
    second_predecessor_visible: bool = False,
    vocabulary_size: int = 16,
    hidden_coefficient: int = 5,
    input_accessibility_preconditions: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    information_starved = baseline_input_order < label_dependency_order and not second_predecessor_visible
    bayes_upper_bound = 1.0 / float(vocabulary_size) if information_starved else None
    preconditions = dict(input_accessibility_preconditions or {})
    source_pointers = {
        "feature_source": FEATURE_SOURCE_POINTER,
        "label_source": LABEL_SOURCE_POINTER,
        "controller_evidence": CONTROLLER_EVIDENCE_POINTER,
        "fair_reconstruction": FAIR_RECONSTRUCTION_POINTER,
    }
    source_pointers.update({
        key: value
        for key, value in preconditions.get("source_pointers", {}).items()
        if isinstance(key, str) and isinstance(value, str)
    })
    return {
        "status": "construct-boundary" if information_starved else "construct-valid",
        "baseline_input_order": baseline_input_order,
        "label_dependency_order": label_dependency_order,
        "second_predecessor_visible_to_baseline": second_predecessor_visible,
        "input_accessibility_preconditions": preconditions,
        "baseline_feature_wiring": "[embed(x_prev_1), zero_like(embed(x_prev_2))]",
        "label_rule": "(3*x_prev_1 + 5*x_prev_2 + 1) mod 16",
        "hidden_coefficient_modulus_gcd": _gcd(hidden_coefficient, vocabulary_size),
        "bayes_upper_bound_accuracy": _round(bayes_upper_bound),
        "chance_accuracy": _round(1.0 / float(vocabulary_size)),
        "source_pointers": source_pointers,
        "boundary_reason": (
            "Given x_prev_1, varying hidden x_prev_2 permutes all labels, so the baseline Bayes limit is chance."
            if information_starved
            else "Baseline input bandwidth covers the label dependency order."
        ),
    }


def _build_rows(l1_payload: Mapping[str, Any]) -> list[dict[str, Any]]:
    rows = _step_rows(l1_payload)
    anchor = _row_by_steps(rows, 36)
    equal_step = _comparison_row(
        comparison_id="equal_step",
        source_index=None if anchor is None else anchor[0],
        source_row=None if anchor is None else anchor[1],
        match_axis="training_steps",
        match_value=36,
        missing_reason="equal-step-anchor-missing",
    )
    if anchor is None:
        return [equal_step.as_dict()]

    _anchor_index, anchor_row = anchor
    dgt_compute = _compute(anchor_row, "dgt_l1")
    dgt_loss_dec = _metric(anchor_row, "dgt_loss_decrease_mean")
    equal_compute_match = (
        None
        if dgt_compute is None
        else _nearest_by_value(rows, value_getter=lambda row: _compute(row, "information_starved_l1_baseline"), target=dgt_compute)
    )
    equal_loss_match = (
        None
        if dgt_loss_dec is None
        else _nearest_by_value(
            rows,
            value_getter=lambda row: _metric(row, "information_starved_loss_decrease_mean"),
            target=dgt_loss_dec,
        )
    )
    equal_compute = _comparison_row(
        comparison_id="equal_compute",
        source_index=None if equal_compute_match is None else equal_compute_match[0],
        source_row=None if equal_compute_match is None else equal_compute_match[1],
        match_axis="compute_units",
        match_value=dgt_compute,
        missing_reason="equal-compute-source-missing",
    )
    equal_loss = _comparison_row(
        comparison_id="equal_loss_decrease",
        source_index=None if equal_loss_match is None else equal_loss_match[0],
        source_row=None if equal_loss_match is None else equal_loss_match[1],
        match_axis="loss_decrease",
        match_value=dgt_loss_dec,
        missing_reason="equal-loss-decrease-source-missing",
    )
    return [equal_step.as_dict(), equal_compute.as_dict(), equal_loss.as_dict()]


def _hardgates(
    comparison_rows: Sequence[Mapping[str, Any]],
    coverage: Mapping[str, Any],
    construct_validity: Mapping[str, Any],
) -> dict[str, Any]:
    row_ids = {str(row.get("comparison_id")) for row in comparison_rows}
    all_rows_present = set(REQUIRED_COMPARISONS).issubset(row_ids)
    all_rows_resolved = all(row.get("status") == "resolved" for row in comparison_rows) and all_rows_present
    fair_rows = [row for row in comparison_rows if row.get("comparison_id") in {"equal_compute", "equal_loss_decrease"}]
    fair_catchup = any(row.get("ci_overlap") is True or (row.get("ci_low_separation") is not None and row.get("ci_low_separation") <= 0.0) for row in fair_rows)
    fair_separates = bool(fair_rows) and all(
        row.get("ci_overlap") is False and row.get("ci_low_separation") is not None and row.get("ci_low_separation") > 0.0
        for row in fair_rows
    )
    construct_boundary = construct_validity.get("status") == "construct-boundary"
    input_accessibility = construct_validity.get("input_accessibility_preconditions")
    input_access_ok = isinstance(input_accessibility, Mapping) and input_accessibility.get("status") == "pass"
    return {
        "BASE-UNDER-HG0": {
            "criterion": "input-accessibility boundary pointers and baseline input bandwidth must pass before undertraining evidence is allowed",
            "status": "fail-closed" if construct_boundary or not input_access_ok else "pass",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.construct_validity",
            "input_accessibility_pointer": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
        },
        "BASE-UNDER-HG1": {
            "criterion": "equal-step, equal-compute, and equal-loss-decrease rows are present",
            "status": "pass" if all_rows_present else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.comparison_rows",
        },
        "BASE-UNDER-HG2": {
            "criterion": "base step grid covers the DGT compute and loss-decrease interval",
            "status": "pass" if coverage.get("covers_dgt_compute_loss_interval") else "fail",
            "evidence_pointer": coverage["source_pointer"],
        },
        "BASE-UNDER-HG3": {
            "criterion": "missing comparison evidence fails closed to inconclusive",
            "status": "pass" if all_rows_resolved else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.comparison_rows",
        },
        "BASE-UNDER-HG4": {
            "criterion": "construct-valid compute or loss catch-up records a bounded downgrade ledger",
            "status": "triggered" if fair_catchup else "not-triggered",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.boundary_ledger",
        },
        "BASE-UNDER-HG5": {
            "criterion": "resolved compute and loss rows retain positive CI-low separation",
            "status": "pass" if all_rows_resolved and fair_separates else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.evidence_ledger",
        },
    }


def _derive_decision(
    comparison_rows: Sequence[Mapping[str, Any]],
    hardgates: Mapping[str, Mapping[str, Any]],
    construct_validity: Mapping[str, Any],
) -> tuple[str, str, list[dict[str, Any]], list[dict[str, Any]]]:
    if construct_validity.get("status") == "construct-boundary" or hardgates["BASE-UNDER-HG0"]["status"] != "pass":
        return (
            "construct-boundary",
            "defer-to-fair-reconstruction",
            [
                {
                    "ledger_id": "base-undertraining-construct-validity",
                    "status": "construct-boundary",
                    "reason": (
                        "equal-compute and equal-loss-decrease rows are non-informative for an information-starved baseline"
                    ),
                    "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.construct_validity",
                    "reconstruction_pointer": FAIR_RECONSTRUCTION_POINTER,
                }
            ],
            [],
        )
    if hardgates["BASE-UNDER-HG1"]["status"] != "pass" or hardgates["BASE-UNDER-HG2"]["status"] != "pass" or hardgates["BASE-UNDER-HG3"]["status"] != "pass":
        return "inconclusive", "hold", [], []
    fair_rows = [row for row in comparison_rows if row["comparison_id"] in {"equal_compute", "equal_loss_decrease"}]
    catchup = [
        row for row in fair_rows
        if row.get("ci_overlap") is True or (row.get("ci_low_separation") is not None and row["ci_low_separation"] <= 0.0)
    ]
    if catchup:
        first = catchup[0]
        action = "fair_compute_artifact" if first["comparison_id"] == "equal_compute" else "fair_loss_decrease_artifact"
        return (
            "downgrade",
            action,
            [
                {
                    "ledger_id": f"base-undertraining-{row['comparison_id']}",
                    "comparison_id": row["comparison_id"],
                    "reason": "base reaches DGT after the construct-validity premise is satisfied",
                    "source_pointer": row["source_pointer"],
                }
                for row in catchup
            ],
            [],
        )
    return (
        "noninformative-separation",
        "record_noninformative_rows",
        [],
        [
            {
                "ledger_id": f"base-undertraining-{row['comparison_id']}",
                "comparison_id": row["comparison_id"],
                "ci_low_separation": row["ci_low_separation"],
                "source_pointer": row["source_pointer"],
            }
            for row in comparison_rows
        ],
    )


def build_payload(
    *,
    root: Path,
    generated_at: str = GENERATED_AT,
    l1_payload: Mapping[str, Any] | None = None,
    l1_status: str | None = None,
    l1_sha256: str | None = None,
    downstream_verdict: Any | None = None,
    construct_validity_override: Mapping[str, Any] | None = None,
    input_accessibility_payload: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if downstream_verdict is not None:
        raise ValueError("base-undertraining audit does not accept downstream verdict input")
    if l1_payload is None:
        resolved_status, loaded_payload, resolved_sha = _load_json_artifact(root, L1_SOURCE_ARTIFACT)
        l1_status = l1_status or resolved_status
        l1_payload = loaded_payload
        l1_sha256 = l1_sha256 if l1_sha256 is not None else resolved_sha
    else:
        l1_status = l1_status or "resolved"
        l1_sha256 = l1_sha256 if l1_sha256 is not None else _json_digest(l1_payload)

    if l1_status == "resolved" and isinstance(l1_payload, Mapping):
        comparison_rows = _build_rows(l1_payload)
        coverage = _base_grid_coverage(_step_rows(l1_payload))
    else:
        comparison_rows = []
        coverage = {
            "required_grid": list(REQUIRED_BASE_GRID),
            "observed_grid": [],
            "required_grid_present": False,
            "covers_dgt_compute_loss_interval": False,
            "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
        }

    input_accessibility_preconditions = _input_accessibility_preconditions(
        root,
        input_accessibility_payload,
    )
    construct_validity = dict(
        construct_validity_override
        or construct_validity_assessment(input_accessibility_preconditions=input_accessibility_preconditions)
    )
    construct_validity["input_accessibility_preconditions"] = input_accessibility_preconditions
    source_pointers = dict(construct_validity.get("source_pointers", {}))
    source_pointers.update(input_accessibility_preconditions["source_pointers"])
    construct_validity["source_pointers"] = source_pointers
    hardgates = _hardgates(comparison_rows, coverage, construct_validity)
    verdict, claim_action, boundary, evidence = _derive_decision(comparison_rows, hardgates, construct_validity)
    source_contract = {
        "source_artifact": L1_SOURCE_ARTIFACT,
        "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder",
        "sha256": l1_sha256,
        "status": l1_status or "invalid",
        "pointer_only": True,
        "required_pointers": sorted(
            {
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder",
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step",
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
                *(str(row["source_pointer"]) for row in comparison_rows),
                input_accessibility_preconditions["input_accessibility_ref"],
                input_accessibility_preconditions["boundary_ledger_ref"],
                *input_accessibility_preconditions["information_starved_arms_ref"],
                *input_accessibility_preconditions["unanswerable_ood_splits_ref"],
            }
        ),
        "base_step_grid_coverage": coverage,
        "input_accessibility_preconditions": input_accessibility_preconditions,
    }
    audit = BaseUndertrainingAudit(
        source_contract=source_contract,
        construct_validity=construct_validity,
        comparison_rows=comparison_rows,
        hardgates=hardgates,
        mechanical_decision_table=mechanical_decision_table(),
        verdict=verdict,
        claim_action=claim_action,
        boundary_ledger=boundary,
        evidence_ledger=evidence,
        not_claimed=NOT_CLAIMED,
        revoke_if=[
            "Any required L1 canonical pointer becomes missing or unresolvable.",
            "The construct-validity source no longer identifies the current baseline feature boundary.",
            "The audit is used as evidence outside bounded L1 tiny-sequence scope.",
        ],
    ).as_dict()
    audit["generated_at"] = generated_at
    audit["producer"] = PRODUCER
    payload = {"base_undertraining_audit": audit}
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if set(payload) != {"base_undertraining_audit"}:
        raise ValueError("base-undertraining payload must expose only base_undertraining_audit")
    audit = payload["base_undertraining_audit"]
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_contract",
        "construct_validity",
        "comparison_rows",
        "hardgates",
        "mechanical_decision_table",
        "verdict",
        "claim_action",
        "boundary_ledger",
        "evidence_ledger",
        "not_claimed",
        "revoke_if",
    }
    if not isinstance(audit, Mapping) or set(audit) != required:
        raise ValueError("base-undertraining audit fields mismatch")
    if audit["schema_id"] != SCHEMA_ID or audit["artifact_id"] != ARTIFACT_ID:
        raise ValueError("base-undertraining audit identity mismatch")
    construct_validity = audit["construct_validity"]
    if not isinstance(construct_validity, Mapping) or construct_validity.get("status") not in {"construct-boundary", "construct-valid"}:
        raise ValueError("base-undertraining construct validity mismatch")
    if construct_validity.get("status") == "construct-boundary":
        if audit["verdict"] != "construct-boundary" or audit["claim_action"] != "defer-to-fair-reconstruction":
            raise ValueError("construct-boundary audit must defer to fair reconstruction")
        if audit["evidence_ledger"]:
            raise ValueError("construct-boundary audit must not emit evidence strengthening")
    rows = audit["comparison_rows"]
    if not isinstance(rows, list):
        raise ValueError("base-undertraining comparison rows must be a list")
    row_ids = [row.get("comparison_id") for row in rows if isinstance(row, Mapping)]
    if len(row_ids) != len(set(row_ids)):
        raise ValueError("base-undertraining comparison rows must be unique")
    if audit["verdict"] not in {"inconclusive", "construct-boundary"} and set(row_ids) != set(REQUIRED_COMPARISONS):
        raise ValueError("non-inconclusive base-undertraining verdict requires all comparison rows")
    for row in rows:
        if set(row) != set(BaseUndertrainingComparisonRow("", "", "", "", "", None, None, None, None, None, "").as_dict()):
            raise ValueError("base-undertraining comparison row fields mismatch")
        if not str(row["source_pointer"]).startswith(f"{L1_SOURCE_ARTIFACT}:"):
            raise ValueError("base-undertraining row must point to L1 canonical artifact")
    serialized = json.dumps(payload, sort_keys=True)
    for forbidden in ("raw_metrics", "step_rows", "training_arms"):
        if forbidden in serialized:
            raise ValueError(f"base-undertraining audit must not duplicate L1 payload: {forbidden}")


def render_markdown(payload: Mapping[str, Any]) -> str:
    audit = payload["base_undertraining_audit"]
    lines = [
        "# DGT base undertraining audit",
        "",
        f"- Verdict: `{audit['verdict']}`",
        f"- Claim action: `{audit['claim_action']}`",
        f"- Source: `{audit['source_contract']['source_pointer']}`",
        f"- Construct validity: `{audit['construct_validity']['status']}`",
        "",
        "## Boundary ledger",
        "",
    ]
    for row in audit["boundary_ledger"]:
        lines.append(f"- `{row['ledger_id']}`: {row['reason']}")
    lines.extend([
        "",
        "## Comparison rows",
        "",
    ])
    for row in audit["comparison_rows"]:
        lines.append(
            f"- `{row['comparison_id']}`: `{row['decision']}` "
            f"(base `{row['base_metric']}`, DGT `{row['dgt_metric']}`, pointer `{row['source_pointer']}`)"
        )
    lines.extend(["", "## Not claimed", ""])
    for item in audit["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    audit = payload["base_undertraining_audit"]
    source_contract = audit["source_contract"]
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-base-undertraining-audit",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": _json_digest(source_contract),
        "output_digest": _json_digest(payload),
        "inputs": {"source_contract": source_contract},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    _write_json(root / CANONICAL_JSON_ARTIFACT, payload)
    markdown_path = root / CANONICAL_MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )

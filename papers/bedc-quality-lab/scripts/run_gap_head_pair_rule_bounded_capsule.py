#!/usr/bin/env python3
"""Build the gap-head pair-rule bounded capsule from owner artifacts."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


SCHEMA_ID = "bedc-quality-lab:gap-head-pair-rule-bounded-capsule"
ARTIFACT_ID = "bedc-quality-lab:gap-head-pair-rule-bounded-capsule"
JSON_ARTIFACT = "reports/canonical/gap-head-pair-rule-bounded-capsule.json"
REPORT_ARTIFACT = "reports/canonical/gap-head-pair-rule-bounded-capsule.md"
GAUSSIAN_OU_GAP_HEAD_ARTIFACT = "reports/canonical/gap-head-on-h.json"
PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT = "reports/canonical/dgt-pair-rule-construct-validity.json"
PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT_ID = "bedc-quality-lab:dgt-pair-rule-construct-validity"
PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_POINTER = "$.downstream_admission.status"
PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_OWNER_POINTER = (
    f"{PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT}:{PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_POINTER}"
)
PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER = (
    "reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.per_step[4].training_arms.parameter_matched_l1"
)
FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT = "reports/canonical/fair-alignment-control-ledger.json"
FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT_ID = "bedc-quality-lab:fair-alignment-control-ledger"
FAIR_ALIGNMENT_CONTROL_STATUS_POINTER = "$.claim_gate.status"
FAIR_ALIGNMENT_CONTROL_STATUS_OWNER_POINTER = (
    f"{FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT}:{FAIR_ALIGNMENT_CONTROL_STATUS_POINTER}"
)
PAIR_RULE_CLAIM_CAPSULE_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
PAIR_RULE_CLAIM_CAPSULE_ARTIFACT_ID = "bedc-quality-lab:dgt-l1-controls"
PAIR_RULE_BASE_EXCEEDS_CHANCE_POINTER = (
    "$.claim_capsule_ref.construct_validity.base_exceeds_chance.gate_status"
)
PAIR_RULE_ATTRIBUTION_ARTIFACT = "reports/canonical/gap-head-pair-rule-attribution.json"
PAIR_RULE_ATTRIBUTION_ARTIFACT_ID = "bedc-quality-lab:gap-head-pair-rule-attribution"
PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT = (
    "reports/canonical/gap-head-pair-rule-observed-debt-transfer.json"
)
PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT_ID = (
    "bedc-quality-lab:gap-head-pair-rule-observed-debt-transfer"
)


@dataclass(frozen=True)
class PrerequisiteSpec:
    prereq_id: str
    issue: int
    artifact: str
    status_pointer: str
    pass_values: tuple[Any, ...]
    expected_pointer_path: str | None = None
    expected_pointer_value: Any | None = None
    artifact_id_pointer: str | None = None
    expected_artifact_id: str | None = None


PREREQUISITES: tuple[PrerequisiteSpec, ...] = (
    PrerequisiteSpec(
        prereq_id="pair_rule_construct_validity",
        issue=1481,
        artifact=PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT,
        status_pointer=PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_POINTER,
        pass_values=("pass",),
        expected_pointer_path="$.source_artifacts.selected_l1_evidence",
        expected_pointer_value=PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=PAIR_RULE_CONSTRUCT_VALIDITY_ARTIFACT_ID,
    ),
    PrerequisiteSpec(
        prereq_id="fair_alignment_control_ledger",
        issue=1482,
        artifact=FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT,
        status_pointer=FAIR_ALIGNMENT_CONTROL_STATUS_POINTER,
        pass_values=("pass",),
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=FAIR_ALIGNMENT_CONTROL_LEDGER_ARTIFACT_ID,
    ),
    PrerequisiteSpec(
        prereq_id="pair_rule_base_exceeds_chance",
        issue=1483,
        artifact=PAIR_RULE_CLAIM_CAPSULE_ARTIFACT,
        status_pointer=PAIR_RULE_BASE_EXCEEDS_CHANCE_POINTER,
        pass_values=("pass",),
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=PAIR_RULE_CLAIM_CAPSULE_ARTIFACT_ID,
    ),
    PrerequisiteSpec(
        prereq_id="pair_rule_attribution",
        issue=1484,
        artifact=PAIR_RULE_ATTRIBUTION_ARTIFACT,
        status_pointer="$.d5_m.status",
        pass_values=("pass",),
        expected_pointer_path="$.d5_m.source_surface_owner_pointer",
        expected_pointer_value=PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=PAIR_RULE_ATTRIBUTION_ARTIFACT_ID,
    ),
    PrerequisiteSpec(
        prereq_id="pair_rule_observed_debt_transfer",
        issue=1484,
        artifact=PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT,
        status_pointer="$.observed_debt_transfer.status",
        pass_values=("pass",),
        expected_pointer_path="$.observed_debt_transfer.source_surface_owner_pointer",
        expected_pointer_value=PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT_ID,
    ),
)


def _artifact_pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _load_json(relative_path: str) -> dict[str, Any] | None:
    path = ROOT / relative_path
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"artifact payload must be an object: {relative_path}")
    return payload


def _value_status(value: Any, pass_values: tuple[Any, ...]) -> str:
    if value in pass_values:
        return "pass"
    if value in {"failed", "fail", "blocked", False}:
        return "bounded-negative"
    return "blocked"


def _check_prerequisite(spec: PrerequisiteSpec) -> dict[str, Any]:
    payload = _load_json(spec.artifact)
    owner_pointer = _artifact_pointer(spec.artifact, spec.status_pointer)
    if payload is None:
        return {
            "id": spec.prereq_id,
            "issue": spec.issue,
            "artifact": spec.artifact,
            "owner_pointer": owner_pointer,
            "status_pointer": spec.status_pointer,
            "status": "blocked",
            "reason": "missing_artifact",
            "expected_values": list(spec.pass_values),
            "observed_value": None,
        }
    if spec.artifact_id_pointer is not None:
        observed_artifact_id = pointer_value(payload, spec.artifact_id_pointer)
        if observed_artifact_id != spec.expected_artifact_id:
            return {
                "id": spec.prereq_id,
                "issue": spec.issue,
                "artifact": spec.artifact,
                "owner_pointer": owner_pointer,
                "status_pointer": spec.status_pointer,
                "status": "blocked",
                "reason": "mismatched_artifact_id",
                "expected_artifact_id": spec.expected_artifact_id,
                "observed_artifact_id": observed_artifact_id,
                "expected_values": list(spec.pass_values),
                "observed_value": pointer_value(payload, spec.status_pointer),
            }
    if spec.expected_pointer_path is not None:
        observed_pointer = pointer_value(payload, spec.expected_pointer_path)
        if observed_pointer != spec.expected_pointer_value:
            return {
                "id": spec.prereq_id,
                "issue": spec.issue,
                "artifact": spec.artifact,
                "owner_pointer": owner_pointer,
                "status_pointer": spec.status_pointer,
                "status": "blocked",
                "reason": "mismatched_expected_pointer",
                "expected_pointer_path": spec.expected_pointer_path,
                "expected_pointer_value": spec.expected_pointer_value,
                "observed_pointer_value": observed_pointer,
                "expected_values": list(spec.pass_values),
                "observed_value": pointer_value(payload, spec.status_pointer),
            }
    observed = pointer_value(payload, spec.status_pointer)
    if observed is None or observed == "unresolved":
        status = "blocked"
        reason = "unresolved_status_pointer"
    else:
        status = _value_status(observed, spec.pass_values)
        reason = "status_pass" if status == "pass" else "status_not_pass"
    return {
        "id": spec.prereq_id,
        "issue": spec.issue,
        "artifact": spec.artifact,
        "owner_pointer": owner_pointer,
        "status_pointer": spec.status_pointer,
        "status": status,
        "reason": reason,
        "expected_values": list(spec.pass_values),
        "observed_value": observed,
    }


def _capsule_status(checks: list[Mapping[str, Any]]) -> str:
    statuses = {str(check["status"]) for check in checks}
    if statuses == {"pass"}:
        return "pass"
    if "blocked" in statuses:
        return "blocked"
    return "bounded-negative"


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_gap_head_pair_rule_bounded_capsule.py",
        "pair_rule_surface_owner": PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        "construct_validity_owner": PAIR_RULE_CONSTRUCT_VALIDITY_STATUS_OWNER_POINTER,
        "fair_alignment_control_owner": FAIR_ALIGNMENT_CONTROL_STATUS_OWNER_POINTER,
        "base_exceeds_chance_owner": _artifact_pointer(
            PAIR_RULE_CLAIM_CAPSULE_ARTIFACT,
            PAIR_RULE_BASE_EXCEEDS_CHANCE_POINTER,
        ),
        "pair_rule_attribution_owner": _artifact_pointer(PAIR_RULE_ATTRIBUTION_ARTIFACT, "$.d5_m.status"),
        "pair_rule_observed_debt_transfer_owner": _artifact_pointer(
            PAIR_RULE_OBSERVED_DEBT_TRANSFER_ARTIFACT,
            "$.observed_debt_transfer.status",
        ),
    }


def _pair_rule_surface(checks: list[Mapping[str, Any]]) -> dict[str, Any]:
    return {
        "surface_id": "non-starving-order-2-gap-head-pair-rule",
        "order": 2,
        "starvation_policy": "non-starving",
        "source_surface": {
            "owner_pointer": PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
            "task_id": "dgt_l1_order2_pair_rule",
            "label_rule": "y=(3*x_prev_1+5*x_prev_2+1) mod16",
        },
        "adaptation": "bounded capsule over prerequisite owner pointers",
        "prerequisite_owner_pointers": [check["owner_pointer"] for check in checks],
    }


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    checks = [_check_prerequisite(spec) for spec in PREREQUISITES]
    status = _capsule_status(checks)
    positive_status = "pass" if status == "pass" else "blocked"
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "source_issues": [1481, 1482, 1483, 1484],
        "source_artifacts": _source_artifacts(),
        "pair_rule_surface": _pair_rule_surface(checks),
        "prerequisite_checks": checks,
        "prerequisite_checks_by_id": {check["id"]: check for check in checks},
        "capsule_verdict": {
            "status": status,
            "owner_pointer": _artifact_pointer(JSON_ARTIFACT, "$.capsule_verdict.status"),
            "pass_rule": "all prerequisite owner pointers resolve to expected pass values",
            "blocked_rule": "missing, unresolved, or mismatched prerequisite pointers block the capsule",
            "bounded_negative_rule": "resolved non-pass prerequisite statuses bound the capsule negative",
        },
        "bounded_negative": {
            "status": "bounded-negative" if status == "bounded-negative" else "not-applicable",
            "bounded_negative_prerequisite_ids": [
                check["id"] for check in checks if check["status"] == "bounded-negative"
            ],
        },
        "positive_claim": {
            "status": positive_status,
            "pointer": "$.capsule_verdict.status",
            "artifact_pointer": _artifact_pointer(JSON_ARTIFACT, "$.capsule_verdict.status"),
        },
        "control_pointer": "$.prerequisite_checks",
        "cost_protocol": {
            "status": "pointer-only",
            "recomputed_upstream_truth": False,
            "surface_owner": PAIR_RULE_SOURCE_SURFACE_OWNER_POINTER,
        },
        "not_claimed": [
            "no recomputation of base learnability",
            "no recomputation of FairControl rows",
            "no recomputation of attribution truth",
            "no recomputation of observed-debt transfer truth",
            "no shared gap-head surface provider or fair-control ledger module",
        ],
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Gap-Head Pair-Rule Bounded Capsule",
        "",
        f"- Artifact id: `{payload['artifact_id']}`",
        f"- JSON artifact: `{payload['artifact']}`",
        f"- Capsule status pointer: `{payload['artifact']}:$.capsule_verdict.status`",
        f"- Positive claim pointer: `{payload['artifact']}:$.positive_claim.status`",
        f"- Pair-rule surface pointer: `{payload['artifact']}:$.pair_rule_surface`",
        f"- Prerequisite checks pointer: `{payload['artifact']}:$.prerequisite_checks`",
        "",
        "## Prerequisite Pointers",
        "",
        "| prerequisite | status | owner pointer |",
        "| --- | --- | --- |",
    ]
    for check in payload["prerequisite_checks"]:
        lines.append(f"| `{check['id']}` | `{check['status']}` | `{check['owner_pointer']}` |")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            f"- Order: `{payload['pair_rule_surface']['order']}`",
            f"- Starvation policy: `{payload['pair_rule_surface']['starvation_policy']}`",
            f"- Cost protocol: `{payload['artifact']}:$.cost_protocol`",
            f"- Not claimed: `{payload['artifact']}:$.not_claimed`",
            "",
        ]
    )
    return "\n".join(lines)


def write_payload(payload: Mapping[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    markdown_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")


def _reusable_generated_at() -> str | None:
    path = ROOT / JSON_ARTIFACT
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def main() -> None:
    payload = build_payload(generated_at=_reusable_generated_at())
    write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"status {payload['capsule_verdict']['status']}")


if __name__ == "__main__":
    main()

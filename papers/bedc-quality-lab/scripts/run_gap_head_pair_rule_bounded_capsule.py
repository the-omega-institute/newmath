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
GAP_HEAD_ON_H_ARTIFACT = "reports/canonical/gap-head-on-h.json"
GAP_HEAD_DISCOVERY_ARTIFACT = "reports/canonical/gap-head-discovery.json"
OBSERVED_DEBT_TRANSFER_ARTIFACT = "reports/canonical/gap-head-observed-debt-transfer.json"
OBSERVED_DEBT_TRANSFER_ARTIFACT_ID = "bedc-quality-lab:gap-head-observed-debt-transfer"
ATTRIBUTION_CAPSULE_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
ATTRIBUTION_CAPSULE_ARTIFACT_ID = "gap_head_attribution_capsule"
TRANSFER_STATUS_POINTER = "$.gap_head_on_h_observed_debt_transfer.status"


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
        prereq_id="gap_head_discovery",
        issue=1481,
        artifact=GAP_HEAD_DISCOVERY_ARTIFACT,
        status_pointer="$.final_main_claim_status",
        pass_values=("promoted",),
        expected_pointer_path="$.source_artifacts.source_json_artifact",
        expected_pointer_value=GAP_HEAD_ON_H_ARTIFACT,
    ),
    PrerequisiteSpec(
        prereq_id="gap_head_observed_debt_transfer",
        issue=1482,
        artifact=OBSERVED_DEBT_TRANSFER_ARTIFACT,
        status_pointer=TRANSFER_STATUS_POINTER,
        pass_values=("pass",),
        expected_pointer_path="$.gap_head_on_h_observed_debt_transfer.discovery_map_pointer",
        expected_pointer_value=TRANSFER_STATUS_POINTER,
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=OBSERVED_DEBT_TRANSFER_ARTIFACT_ID,
    ),
    PrerequisiteSpec(
        prereq_id="gap_head_attribution_capsule",
        issue=1483,
        artifact=ATTRIBUTION_CAPSULE_ARTIFACT,
        status_pointer="$.d5_m.status",
        pass_values=("pass",),
        artifact_id_pointer="$.artifact_id",
        expected_artifact_id=ATTRIBUTION_CAPSULE_ARTIFACT_ID,
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
        "gap_head_surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
        "gap_head_training_owner": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
        "matched_random_control_owner": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
        "metric_helper_owner": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
        "discovery_owner": "scripts/run_gap_head_discovery.py",
        "observed_debt_transfer_owner": "scripts/run_gap_head_observed_debt_transfer.py",
        "attribution_owner": "scripts/run_gap_head_attribution_capsule.py",
    }


def _pair_rule_surface(checks: list[Mapping[str, Any]]) -> dict[str, Any]:
    return {
        "surface_id": "non-starving-order-2-gap-head-pair-rule",
        "order": 2,
        "starvation_policy": "non-starving",
        "source_surface": {
            "artifact": GAP_HEAD_ON_H_ARTIFACT,
            "owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
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
            "blocked_prerequisites": [
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
            "surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
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

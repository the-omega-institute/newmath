"""Hidden-Polarity Rotor task-local diagnostic and admission surface."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:hidden-polarity-rotor"
ARTIFACT_ID = "bedc-quality-lab:hidden-polarity-rotor"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/hidden-polarity-rotor.json"
MARKDOWN_ARTIFACT = "reports/canonical/hidden-polarity-rotor.md"
FINGERPRINT_ARTIFACT = "reports/canonical/hidden-polarity-rotor.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-20T00:00:00+00:00"
SOURCE_REF = "gh-issue-1700"
IDENTIFIABILITY_MARGIN = 0.12
CONTROL_MARGIN = 0.03
MIN_SAMPLE_COUNT = 64
CONTROL_IDS = ("phase_shuffle", "polarity_swap", "rotor_blind")
VERDICTS = ("diagnostic_only", "positive", "bounded_negative", "ill_posed")
CLAIM_KIND = "bounded_physical_identifiability"
DOWNSTREAM_GATE_POINTER = "reports/canonical/hidden-polarity-rotor.json:$.claim_boundary"


@dataclass(frozen=True)
class HPRDiagnosticArm:
    """One deterministic rotor fixture arm."""

    arm_id: str
    role: str
    rotor_phase_degrees: int
    hidden_polarity: int
    observation_policy: str
    expected_signal: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "role": self.role,
            "rotor_phase_degrees": self.rotor_phase_degrees,
            "hidden_polarity": self.hidden_polarity,
            "observation_policy": self.observation_policy,
            "expected_signal": self.expected_signal,
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def default_diagnostic_fixture() -> tuple[HPRDiagnosticArm, ...]:
    return (
        HPRDiagnosticArm(
            arm_id="aligned_rotor",
            role="target",
            rotor_phase_degrees=0,
            hidden_polarity=1,
            observation_policy="phase-and-polarity-observed",
            expected_signal="orientation recovers the hidden polarity",
        ),
        HPRDiagnosticArm(
            arm_id="opposed_rotor",
            role="target",
            rotor_phase_degrees=180,
            hidden_polarity=-1,
            observation_policy="phase-and-polarity-observed",
            expected_signal="orientation flips with the hidden polarity",
        ),
        HPRDiagnosticArm(
            arm_id="phase_shuffle",
            role="control",
            rotor_phase_degrees=90,
            hidden_polarity=1,
            observation_policy="phase-randomized",
            expected_signal="phase-only shortcut is not sufficient",
        ),
        HPRDiagnosticArm(
            arm_id="polarity_swap",
            role="control",
            rotor_phase_degrees=0,
            hidden_polarity=-1,
            observation_policy="polarity-label-swapped",
            expected_signal="label leakage is not sufficient",
        ),
        HPRDiagnosticArm(
            arm_id="rotor_blind",
            role="control",
            rotor_phase_degrees=0,
            hidden_polarity=1,
            observation_policy="rotor-observation-masked",
            expected_signal="metadata-only evidence is not sufficient",
        ),
    )


def task_facts() -> dict[str, Any]:
    return {
        "task_id": "hidden-polarity-rotor",
        "task_family": "bounded-physical-identifiability",
        "owner": "bedc_quality_lab.tasks.hidden_polarity_rotor",
        "source_ref": SOURCE_REF,
        "fact_source": "owner-local",
        "evaluation_unit": "deterministic diagnostic fixture plus optional measured-result intake",
        "identifiability_margin": IDENTIFIABILITY_MARGIN,
        "control_margin": CONTROL_MARGIN,
        "min_sample_count": MIN_SAMPLE_COUNT,
        "control_ids": list(CONTROL_IDS),
        "allowed_verdicts": list(VERDICTS),
    }


def preregistration_capsule() -> dict[str, Any]:
    capsule = {
        "schema_id": "bedc-quality-lab:hidden-polarity-rotor-preregistration",
        "source_ref": SOURCE_REF,
        "task": task_facts(),
        "diagnostic_fixture_rule": {
            "criterion": "default artifact is diagnostic_only until a measured result is explicitly provided",
            "fixture_digest_pointer": "$.diagnostic_fixture.fixture_digest",
        },
        "identifiability_rule": {
            "margin": IDENTIFIABILITY_MARGIN,
            "criterion": "effect_lower_ci - chance_upper_ci >= identifiability_margin",
            "minimum_sample_count": MIN_SAMPLE_COUNT,
        },
        "control_rule": {
            "margin": CONTROL_MARGIN,
            "criterion": "each control upper_ci <= chance_upper_ci + control_margin",
            "controls": list(CONTROL_IDS),
        },
        "verdict_rule": {
            "diagnostic_only": "no measured result is provided and the fixture validates",
            "positive": "measured result validates and all admission gates pass",
            "bounded_negative": "measured result validates but an evidence gate fails",
            "ill_posed": "payload shape, dependency envelope, or control arms fail closed",
        },
        "downstream_gate_pointer": DOWNSTREAM_GATE_POINTER,
    }
    capsule["preregistration_digest"] = canonical_digest(capsule)
    return capsule


def _round_metric(value: Any) -> float:
    return round(float(value), 6)


def _mean(values: Sequence[float]) -> float:
    return round(sum(float(value) for value in values) / len(values), 6) if values else 0.0


def _fixture_payload(fixture: Sequence[HPRDiagnosticArm] | Sequence[Mapping[str, Any]] | None) -> dict[str, Any]:
    rows = [
        item.to_dict() if isinstance(item, HPRDiagnosticArm) else dict(item)
        for item in (default_diagnostic_fixture() if fixture is None else fixture)
    ]
    return {
        "schema_id": "bedc-quality-lab:hidden-polarity-rotor-fixture",
        "arms": rows,
        "target_arm_ids": [row["arm_id"] for row in rows if row.get("role") == "target"],
        "control_arm_ids": [row["arm_id"] for row in rows if row.get("role") == "control"],
        "fixture_digest": canonical_digest(rows),
    }


def _diagnostic_dependency_status() -> dict[str, Any]:
    return {
        "status": "downgraded",
        "reason": "measured_result_not_provided",
        "fallback": "deterministic_diagnostic_fixture",
        "required_for_claim": True,
    }


def _normalize_measured_result(measured_result: Mapping[str, Any] | None) -> tuple[dict[str, Any], list[str]]:
    if measured_result is None:
        return {
            "status": "not_provided",
            "source": None,
            "normalized": None,
            "shape_errors": [],
        }, []
    errors: list[str] = []
    result = dict(measured_result)
    dependency = result.get("dependency_status", {})
    if not isinstance(dependency, Mapping):
        errors.append("dependency_status must be an object")
        dependency = {}
    dependency_status = str(dependency.get("status", "available"))
    if dependency_status != "available":
        errors.append(f"dependency_status must be available, got {dependency_status}")
    try:
        effect = {
            "score": _round_metric(result["effect"]["score"]),
            "lower_ci": _round_metric(result["effect"]["lower_ci"]),
            "chance_upper_ci": _round_metric(result["effect"]["chance_upper_ci"]),
            "sample_count": int(result["effect"]["sample_count"]),
        }
    except (KeyError, TypeError, ValueError) as exc:
        errors.append(f"effect shape invalid: {exc}")
        effect = {"score": 0.0, "lower_ci": 0.0, "chance_upper_ci": 1.0, "sample_count": 0}
    controls_raw = result.get("controls", {})
    controls: dict[str, dict[str, Any]] = {}
    if not isinstance(controls_raw, Mapping):
        errors.append("controls must be an object")
        controls_raw = {}
    if tuple(sorted(controls_raw)) != tuple(sorted(CONTROL_IDS)):
        errors.append("control set mismatch")
    for control_id in CONTROL_IDS:
        control = controls_raw.get(control_id, {})
        if not isinstance(control, Mapping):
            errors.append(f"control {control_id} must be an object")
            control = {}
        try:
            controls[control_id] = {
                "score": _round_metric(control["score"]),
                "upper_ci": _round_metric(control["upper_ci"]),
                "sample_count": int(control.get("sample_count", effect["sample_count"])),
            }
        except (KeyError, TypeError, ValueError) as exc:
            errors.append(f"control {control_id} shape invalid: {exc}")
            controls[control_id] = {"score": 0.0, "upper_ci": 1.0, "sample_count": 0}
    numeric_values = [effect["score"], effect["lower_ci"], effect["chance_upper_ci"]]
    numeric_values.extend(float(row["score"]) for row in controls.values())
    numeric_values.extend(float(row["upper_ci"]) for row in controls.values())
    if any(value < 0.0 or value > 1.0 for value in numeric_values):
        errors.append("probability metrics must be between 0 and 1")
    if effect["sample_count"] < MIN_SAMPLE_COUNT:
        errors.append("effect sample_count below minimum")
    if any(int(row["sample_count"]) < MIN_SAMPLE_COUNT for row in controls.values()):
        errors.append("control sample_count below minimum")
    normalized = {
        "run_id": str(result.get("run_id", "measured-hpr")),
        "source": result.get("source"),
        "dependency_status": dict(dependency),
        "effect": effect,
        "controls": controls,
    }
    return {
        "status": "accepted" if not errors else "ill_posed",
        "source": result.get("source"),
        "normalized": normalized,
        "shape_errors": errors,
    }, errors


def _dependency_status(intake: Mapping[str, Any]) -> dict[str, Any]:
    if intake.get("status") == "not_provided":
        return _diagnostic_dependency_status()
    normalized = intake.get("normalized", {})
    dependency = normalized.get("dependency_status", {}) if isinstance(normalized, Mapping) else {}
    if intake.get("status") == "accepted":
        return {
            "status": "available",
            "reason": "measured_result_validated",
            "fallback": None,
            "required_for_claim": True,
            "details": dependency,
        }
    return {
        "status": "blocked",
        "reason": "measured_result_failed_shape_or_dependency_check",
        "fallback": "fail_closed_no_claim",
        "required_for_claim": True,
        "details": dependency,
    }


def _evidence_gate(intake: Mapping[str, Any]) -> dict[str, Any]:
    if intake.get("status") == "not_provided":
        return {
            "status": "not_evaluated",
            "criterion": "effect_lower_ci - chance_upper_ci >= identifiability_margin",
            "margin": IDENTIFIABILITY_MARGIN,
            "effect_margin": None,
            "score": None,
            "reason": "measured_result_not_provided",
        }
    if intake.get("status") != "accepted":
        return {
            "status": "fail",
            "criterion": "effect_lower_ci - chance_upper_ci >= identifiability_margin",
            "margin": IDENTIFIABILITY_MARGIN,
            "effect_margin": None,
            "score": None,
            "reason": "measured_result_ill_posed",
        }
    effect = intake["normalized"]["effect"]
    effect_margin = round(float(effect["lower_ci"]) - float(effect["chance_upper_ci"]), 6)
    return {
        "status": "pass" if effect_margin >= IDENTIFIABILITY_MARGIN else "fail",
        "criterion": "effect_lower_ci - chance_upper_ci >= identifiability_margin",
        "margin": IDENTIFIABILITY_MARGIN,
        "effect_margin": effect_margin,
        "score": effect["score"],
        "lower_ci": effect["lower_ci"],
        "chance_upper_ci": effect["chance_upper_ci"],
        "sample_count": effect["sample_count"],
    }


def _control_gate(intake: Mapping[str, Any]) -> dict[str, Any]:
    if intake.get("status") == "not_provided":
        return {
            "status": "not_evaluated",
            "criterion": "each control upper_ci <= chance_upper_ci + control_margin",
            "control_margin": CONTROL_MARGIN,
            "controls": {control_id: {"status": "not_evaluated", "max_delta_over_chance": None} for control_id in CONTROL_IDS},
            "failed_controls": [],
            "reason": "measured_result_not_provided",
        }
    if intake.get("status") != "accepted":
        return {
            "status": "fail",
            "criterion": "each control upper_ci <= chance_upper_ci + control_margin",
            "control_margin": CONTROL_MARGIN,
            "controls": {control_id: {"status": "fail", "max_delta_over_chance": None} for control_id in CONTROL_IDS},
            "failed_controls": [{"control_id": "shape", "reason": "measured_result_ill_posed"}],
        }
    normalized = intake["normalized"]
    chance_upper = float(normalized["effect"]["chance_upper_ci"])
    failures: list[dict[str, Any]] = []
    by_control: dict[str, dict[str, Any]] = {}
    for control_id, control in normalized["controls"].items():
        delta = round(float(control["upper_ci"]) - chance_upper, 6)
        status = "pass" if delta <= CONTROL_MARGIN else "fail"
        if status != "pass":
            failures.append({"control_id": control_id, "delta_over_chance": delta})
        by_control[control_id] = {
            "status": status,
            "max_delta_over_chance": delta,
            "score": control["score"],
            "upper_ci": control["upper_ci"],
            "sample_count": control["sample_count"],
        }
    return {
        "status": "fail" if failures else "pass",
        "criterion": "each control upper_ci <= chance_upper_ci + control_margin",
        "control_margin": CONTROL_MARGIN,
        "controls": by_control,
        "failed_controls": failures,
        "control_upper_ci_mean": _mean([float(row["upper_ci"]) for row in normalized["controls"].values()]),
    }


def _hardgate(intake: Mapping[str, Any], evidence: Mapping[str, Any], controls: Mapping[str, Any]) -> dict[str, Any]:
    gates = {
        "FIXTURE": {
            "status": "pass",
            "criterion": "deterministic HPR fixture is present",
            "evidence_pointer": "$.diagnostic_fixture",
        },
        "MEASURED-RESULT": {
            "status": "not_evaluated" if intake.get("status") == "not_provided" else ("pass" if intake.get("status") == "accepted" else "fail"),
            "criterion": "measured result is optional, but must validate when provided",
            "evidence_pointer": "$.measured_result_intake",
        },
        "IDENTIFIABILITY": {
            "status": evidence.get("status"),
            "criterion": "effect lower confidence bound clears chance upper confidence bound",
            "evidence_pointer": "$.evidence_gate",
        },
        "CONTROL": {
            "status": controls.get("status"),
            "criterion": "negative controls remain within the preregistered chance envelope",
            "evidence_pointer": "$.controls",
        },
        "PAYLOAD": {
            "status": "pass" if intake.get("status") != "ill_posed" else "fail",
            "criterion": "payload validates against owner-local HPR required fields",
            "evidence_pointer": "$",
        },
    }
    failed = [name for name, gate in gates.items() if gate["status"] == "fail"]
    return {
        "status": "pass" if not failed and intake.get("status") == "accepted" else ("diagnostic" if intake.get("status") == "not_provided" else "fail"),
        "failed_gate": failed[0] if failed else None,
        "gates": gates,
    }


def _verdict(intake: Mapping[str, Any], evidence: Mapping[str, Any], controls: Mapping[str, Any]) -> str:
    if intake.get("status") == "not_provided":
        return "diagnostic_only"
    if intake.get("status") != "accepted":
        return "ill_posed"
    if evidence.get("status") == "pass" and controls.get("status") == "pass":
        return "positive"
    return "bounded_negative"


def _claim_boundary(verdict: str, hardgate: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "bounded" if verdict == "positive" else ("diagnostic" if verdict == "diagnostic_only" else "blocked"),
        "claim_kind": CLAIM_KIND if verdict == "positive" else None,
        "positive": verdict == "positive",
        "verdict": verdict,
        "failed_gate": hardgate.get("failed_gate"),
        "boundary": (
            "Only the provided HPR measured-result intake may support bounded physical identifiability."
            if verdict == "positive"
            else "No bounded physical identifiability claim is opened by this artifact."
        ),
    }


def _reproducibility_contract(verdict: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": "exact_fixture" if verdict == "diagnostic_only" else "measured_result_intake",
        "seed_list": [0],
        "metric_bands": [
            {
                "pointer": "$.verdict",
                "reference_value": verdict,
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "hidden-polarity-rotor",
                "calibration_source": "$.preregistration",
                "seed_basis": {"seed_count": 1, "source": "owner-local fixture or measured-result file"},
            }
        ],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "HPR admission consumes deterministic fixture data and optional JSON measurements",
            "backend_details": {"torch": "not-requested", "mujoco": "not-requested"},
        },
        "framework_provenance": {"python": "not-material-to-deterministic-fixture"},
        "calibration": {
            "calibration_source": "$.preregistration",
            "owner": "hidden-polarity-rotor",
            "basis": "fixed fixture rows, authorized controls, and measured confidence-bound intake",
        },
    }


def build_payload(
    *,
    generated_at: str | None = None,
    measured_result: Mapping[str, Any] | None = None,
    fixture: Sequence[HPRDiagnosticArm] | Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    fixture_payload = _fixture_payload(fixture)
    prereg = preregistration_capsule()
    intake, shape_errors = _normalize_measured_result(measured_result)
    dependency_status = _dependency_status(intake)
    evidence = _evidence_gate(intake)
    controls = _control_gate(intake)
    hardgate = _hardgate(intake, evidence, controls)
    verdict = _verdict(intake, evidence, controls)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": "hidden-polarity-rotor",
        "source_ref": SOURCE_REF,
        "producer": "bedc_quality_lab.tasks.hidden_polarity_rotor",
        "canonical_role": "owner_local_task_admission",
        "source_artifacts": {
            "task_fact_owner": "bedc_quality_lab.tasks.hidden_polarity_rotor",
            "preregistration_digest": prereg["preregistration_digest"],
            "measured_result_source": intake.get("source"),
        },
        "task_facts": task_facts(),
        "preregistration": prereg,
        "config": {
            "identifiability_margin": IDENTIFIABILITY_MARGIN,
            "control_margin": CONTROL_MARGIN,
            "min_sample_count": MIN_SAMPLE_COUNT,
            "control_ids": list(CONTROL_IDS),
            "verdicts": list(VERDICTS),
        },
        "diagnostic_fixture": fixture_payload,
        "measured_result_intake": intake,
        "dependency_status": dependency_status,
        "evidence_gate": evidence,
        "controls": controls,
        "verdict": verdict,
        "claim_boundary": _claim_boundary(verdict, hardgate),
        "hardgate": hardgate,
        "not_claimed": [
            "No claim is made from issue comments, task prose, controller logs, or temporary scripts.",
            "No shared HPR admission framework is introduced.",
            "No GPU, MuJoCo, torch, or external simulator dependency is required for the default artifact.",
            "No downstream report may treat diagnostic_only as a positive physical identifiability claim.",
        ],
        "what_was_learned": _what_was_learned(verdict),
        "reproducibility_contract": _reproducibility_contract(verdict),
    }
    payload["raw_digest"] = canonical_digest(
        {
            "task_facts": payload["task_facts"],
            "config": payload["config"],
            "diagnostic_fixture": payload["diagnostic_fixture"],
            "measured_result_intake": payload["measured_result_intake"],
            "dependency_status": payload["dependency_status"],
            "verdict": payload["verdict"],
            "shape_errors": shape_errors,
        }
    )
    validate_hpr_payload(payload)
    return payload


def _what_was_learned(verdict: str) -> str:
    if verdict == "diagnostic_only":
        return "The HPR artifact is a deterministic diagnostic fixture and does not open the measured claim gate."
    if verdict == "positive":
        return "The measured HPR intake clears the bounded identifiability and negative-control gates."
    if verdict == "bounded_negative":
        return "The measured HPR intake is well-shaped but remains bounded by a failed evidence gate."
    return "The measured HPR intake is ill-posed and fails closed before a claim can be evaluated."


def validate_hpr_payload(payload: Mapping[str, Any]) -> None:
    required = (
        "schema_id",
        "artifact_id",
        "generated_at",
        "task_facts",
        "preregistration",
        "config",
        "diagnostic_fixture",
        "measured_result_intake",
        "dependency_status",
        "evidence_gate",
        "controls",
        "verdict",
        "claim_boundary",
        "hardgate",
        "not_claimed",
    )
    missing = [key for key in required if key not in payload]
    if missing:
        raise ValueError(f"HPR payload missing required keys: {', '.join(missing)}")
    if payload["schema_id"] != SCHEMA_ID:
        raise ValueError("HPR payload schema_id mismatch")
    facts = payload.get("task_facts", {})
    if not isinstance(facts, Mapping) or facts.get("owner") != "bedc_quality_lab.tasks.hidden_polarity_rotor":
        raise ValueError("HPR task facts must be owner-local")
    if tuple(facts.get("control_ids", ())) != CONTROL_IDS:
        raise ValueError("HPR control ids mismatch")
    verdict = payload.get("verdict")
    if verdict not in VERDICTS:
        raise ValueError("HPR verdict outside the allowed four-value set")
    for key, value in payload.items():
        if key != "claim_boundary" and key == "claim_kind":
            raise ValueError("HPR claim_kind must only appear inside claim_boundary")
        if key != "claim_boundary" and isinstance(value, Mapping) and "claim_kind" in value:
            raise ValueError("HPR claim_kind must only appear inside claim_boundary")
    fixture = payload.get("diagnostic_fixture", {})
    if not isinstance(fixture, Mapping) or not fixture.get("arms"):
        raise ValueError("HPR diagnostic fixture must contain arms")
    if tuple(sorted(fixture.get("control_arm_ids", ()))) != tuple(sorted(CONTROL_IDS)):
        raise ValueError("HPR fixture control arms mismatch")
    intake = payload.get("measured_result_intake", {})
    if not isinstance(intake, Mapping):
        raise ValueError("HPR measured_result_intake must be an object")
    if verdict == "diagnostic_only" and intake.get("status") != "not_provided":
        raise ValueError("HPR diagnostic_only verdict requires absent measured result")
    if verdict == "positive" and payload.get("claim_boundary", {}).get("claim_kind") != CLAIM_KIND:
        raise ValueError("HPR positive verdict requires bounded claim kind inside claim_boundary")
    if verdict != "positive" and payload.get("claim_boundary", {}).get("claim_kind") is not None:
        raise ValueError("HPR non-positive verdict must not carry a claim kind")
    if verdict == "positive" and payload.get("hardgate", {}).get("status") != "pass":
        raise ValueError("HPR positive verdict requires passing hardgate")
    if verdict == "bounded_negative" and payload.get("hardgate", {}).get("status") != "fail":
        raise ValueError("HPR bounded_negative verdict requires a failed measured gate")
    controls = payload.get("controls", {})
    if not isinstance(controls, Mapping) or tuple(sorted(controls.get("controls", {}))) != tuple(sorted(CONTROL_IDS)):
        raise ValueError("HPR control gate must report every authorized control")


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Hidden-Polarity Rotor",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Verdict: `{payload.get('verdict')}`",
        f"- Dependency status: `{payload.get('dependency_status', {}).get('status')}`",
        f"- Identifiability gate: `{payload.get('evidence_gate', {}).get('criterion')}`",
        f"- Control gate: `{payload.get('controls', {}).get('criterion')}`",
        f"- Claim boundary: `{DOWNSTREAM_GATE_POINTER}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | evidence |",
        "| --- | --- | --- |",
    ]
    gates = payload.get("hardgate", {}).get("gates", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    if isinstance(gates, Mapping):
        for gate_name in ("FIXTURE", "MEASURED-RESULT", "IDENTIFIABILITY", "CONTROL", "PAYLOAD"):
            row = gates.get(gate_name, {})
            lines.append(f"| `{gate_name}` | `{row.get('status')}` | `{row.get('evidence_pointer')}` |")
    lines.extend(["", "## Controls", "", "| control | status | max delta over chance |", "| --- | --- | --- |"])
    controls = payload.get("controls", {}).get("controls", {}) if isinstance(payload.get("controls"), Mapping) else {}
    if isinstance(controls, Mapping):
        for control_id in CONTROL_IDS:
            row = controls.get(control_id, {})
            lines.append(f"| `{control_id}` | `{row.get('status')}` | `{row.get('max_delta_over_chance')}` |")
    lines.extend(["", "## Claim Boundary", ""])
    boundary = payload.get("claim_boundary", {})
    if isinstance(boundary, Mapping):
        lines.append(f"- Status: `{boundary.get('status')}`")
        lines.append(f"- Claim kind: `{boundary.get('claim_kind')}`")
        lines.append(f"- Boundary: {boundary.get('boundary')}")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "hidden-polarity-rotor",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_hidden_polarity_rotor.py"],
        "payload_sha256": canonical_digest(payload),
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.tasks.hidden_polarity_rotor",
                "task_facts": payload.get("task_facts"),
                "config": payload.get("config"),
                "diagnostic_fixture_digest": payload.get("diagnostic_fixture", {}).get("fixture_digest"),
                "measured_result_digest": canonical_digest(payload.get("measured_result_intake")),
                "preregistration_digest": payload.get("preregistration", {}).get("preregistration_digest"),
            }
        ),
        "reproducibility_mode": payload.get("reproducibility_contract", {}).get("mode"),
        "reproducibility_contract": payload.get("reproducibility_contract"),
        "reproducibility_contract_digest": canonical_digest(payload.get("reproducibility_contract")),
        "generated_by": {
            "runner": "scripts/run_hidden_polarity_rotor.py",
            "generated_at": generated_at,
        },
    }


def write_artifacts(
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    generated_at: str | None = None,
    measured_result: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(generated_at=generated_at, measured_result=measured_result)
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_fingerprint.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(json.dumps(fingerprint, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload

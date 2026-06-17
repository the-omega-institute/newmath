"""STI task-admission surface with owner-local chance and control rules."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:sti-admission"
ARTIFACT_ID = "bedc-quality-lab:sti-admission"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/sti-admission.json"
MARKDOWN_ARTIFACT = "reports/canonical/sti-admission.md"
FINGERPRINT_ARTIFACT = "reports/canonical/sti-admission.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-18T00:00:00+00:00"
SOURCE_ISSUE = "#1533"
BASE_MARGIN = 0.05
CONTROL_MARGIN = 0.02
DOWNSTREAM_GATE_POINTER = "reports/canonical/sti-admission.json:$.downstream_gate"
CONTROL_IDS = ("metadata_only", "label_shuffle", "context_blind", "surface_permutation")
VERDICTS = ("accepted", "bounded_negative")


@dataclass(frozen=True)
class STIObservation:
    """One deterministic STI evaluation row."""

    split: str
    base_score: float
    chance_score: float
    control_scores: Mapping[str, float]

    def to_dict(self) -> dict[str, Any]:
        return {
            "split": self.split,
            "base_score": round(float(self.base_score), 6),
            "chance_score": round(float(self.chance_score), 6),
            "control_scores": {key: round(float(value), 6) for key, value in self.control_scores.items()},
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def default_observations() -> tuple[STIObservation, ...]:
    return (
        STIObservation(
            split="heldout-a",
            base_score=0.74,
            chance_score=0.62,
            control_scores={
                "metadata_only": 0.60,
                "label_shuffle": 0.59,
                "context_blind": 0.61,
                "surface_permutation": 0.58,
            },
        ),
        STIObservation(
            split="heldout-b",
            base_score=0.71,
            chance_score=0.61,
            control_scores={
                "metadata_only": 0.59,
                "label_shuffle": 0.60,
                "context_blind": 0.60,
                "surface_permutation": 0.59,
            },
        ),
        STIObservation(
            split="heldout-c",
            base_score=0.73,
            chance_score=0.60,
            control_scores={
                "metadata_only": 0.58,
                "label_shuffle": 0.58,
                "context_blind": 0.60,
                "surface_permutation": 0.57,
            },
        ),
    )


def task_facts() -> dict[str, Any]:
    return {
        "task_id": "sti",
        "task_family": "structural-temporal-integration",
        "owner": "bedc_quality_lab.tasks.sti",
        "source_issue": SOURCE_ISSUE,
        "fact_source": "owner-local",
        "evaluation_unit": "deterministic split-level STI admission row",
        "base_margin": BASE_MARGIN,
        "control_margin": CONTROL_MARGIN,
        "control_ids": list(CONTROL_IDS),
        "accepted_verdict": "accepted",
        "negative_verdict": "bounded_negative",
    }


def preregistration_capsule() -> dict[str, Any]:
    capsule = {
        "schema_id": "bedc-quality-lab:sti-preregistration",
        "source_issue": SOURCE_ISSUE,
        "task": task_facts(),
        "base_chance_rule": {
            "margin": BASE_MARGIN,
            "criterion": "min_split(base_score - chance_score) >= base_margin",
        },
        "control_rule": {
            "margin": CONTROL_MARGIN,
            "criterion": "max_control_score <= chance_score + control_margin for every split and control",
            "controls": list(CONTROL_IDS),
        },
        "verdict_rule": {
            "accepted": "base_chance_gate and control_gate both pass",
            "bounded_negative": "any owner-local STI admission gate fails",
        },
        "downstream_gate_pointer": DOWNSTREAM_GATE_POINTER,
    }
    capsule["preregistration_digest"] = canonical_digest(capsule)
    return capsule


def _mean(values: Sequence[float]) -> float:
    return round(sum(float(value) for value in values) / len(values), 6) if values else 0.0


def _observation_rows(observations: Sequence[STIObservation]) -> list[dict[str, Any]]:
    return [observation.to_dict() for observation in observations]


def _base_chance_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    margins = [
        round(float(row["base_score"]) - float(row["chance_score"]), 6)
        for row in rows
    ]
    min_margin = min(margins) if margins else 0.0
    status = "pass" if margins and min_margin >= BASE_MARGIN else "fail"
    return {
        "status": status,
        "criterion": "min_split(base_score - chance_score) >= base_margin",
        "base_margin": BASE_MARGIN,
        "min_margin": round(min_margin, 6),
        "split_margins": margins,
        "base_score_mean": _mean([float(row["base_score"]) for row in rows]),
        "chance_score_mean": _mean([float(row["chance_score"]) for row in rows]),
    }


def _control_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    failures: list[dict[str, Any]] = []
    by_control: dict[str, dict[str, Any]] = {}
    for control_id in CONTROL_IDS:
        deltas: list[float] = []
        for row in rows:
            controls = row.get("control_scores", {})
            if not isinstance(controls, Mapping) or control_id not in controls:
                failures.append({"split": row.get("split"), "control_id": control_id, "reason": "missing_control"})
                continue
            delta = round(float(controls[control_id]) - float(row["chance_score"]), 6)
            deltas.append(delta)
            if delta > CONTROL_MARGIN:
                failures.append(
                    {
                        "split": row.get("split"),
                        "control_id": control_id,
                        "delta_over_chance": delta,
                    }
                )
        by_control[control_id] = {
            "max_delta_over_chance": round(max(deltas), 6) if deltas else None,
            "status": "fail" if any(failure.get("control_id") == control_id for failure in failures) else "pass",
        }
    return {
        "status": "fail" if failures else "pass",
        "criterion": "max_control_score <= chance_score + control_margin",
        "control_margin": CONTROL_MARGIN,
        "controls": by_control,
        "failed_controls": failures,
    }


def _hardgate(base_chance: Mapping[str, Any], controls: Mapping[str, Any]) -> dict[str, Any]:
    gates = {
        "BASE-CHANCE": {
            "status": "pass" if base_chance.get("status") == "pass" else "fail",
            "criterion": "base clears owner-local chance by at least 0.05 on every split",
            "evidence_pointer": "$.base_chance_gate",
        },
        "CONTROL": {
            "status": "pass" if controls.get("status") == "pass" else "fail",
            "criterion": "all four controls stay within chance plus 0.02",
            "evidence_pointer": "$.controls",
        },
        "PAYLOAD": {
            "status": "pass",
            "criterion": "STI payload validates against owner-local required fields",
            "evidence_pointer": "$",
        },
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "failed_gate": failed[0] if failed else None,
        "gates": gates,
    }


def build_payload(
    *,
    generated_at: str | None = None,
    observations: Sequence[STIObservation] | Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    source_observations = default_observations() if observations is None else observations
    rows = [
        item.to_dict() if isinstance(item, STIObservation) else dict(item)
        for item in source_observations
    ]
    prereg = preregistration_capsule()
    base_chance = _base_chance_gate(rows)
    controls = _control_gate(rows)
    hardgate = _hardgate(base_chance, controls)
    verdict = "accepted" if hardgate["status"] == "pass" else "bounded_negative"
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": "sti-admission",
        "source_issue": SOURCE_ISSUE,
        "producer": "bedc_quality_lab.tasks.sti",
        "canonical_role": "owner_local_task_admission",
        "source_artifacts": {
            "task_fact_owner": "bedc_quality_lab.tasks.sti",
            "preregistration_digest": prereg["preregistration_digest"],
        },
        "task_facts": task_facts(),
        "preregistration": prereg,
        "config": {
            "base_margin": BASE_MARGIN,
            "control_margin": CONTROL_MARGIN,
            "control_ids": list(CONTROL_IDS),
            "verdicts": list(VERDICTS),
        },
        "observations": rows,
        "base_chance_gate": base_chance,
        "controls": controls,
        "verdict": verdict,
        "claim_boundary": {
            "status": "pass" if verdict == "accepted" else "bounded-negative",
            "accepted": verdict == "accepted",
            "failed_gate": hardgate["failed_gate"],
        },
        "positive_claim": {
            "status": "accepted" if verdict == "accepted" else "bounded-negative",
            "positive_discovery": verdict == "accepted",
            "claim": "STI clears owner-local base/chance and negative controls" if verdict == "accepted" else None,
        },
        "downstream_gate": {
            "status": "ready" if verdict == "accepted" else "blocked",
            "pointer": DOWNSTREAM_GATE_POINTER,
            "consumer_contract": "downstream consumers may only read the STI verdict through this owner-local gate pointer",
        },
        "hardgate": hardgate,
        "not_claimed": [
            "No shared base/chance admission protocol is introduced.",
            "No non-STI task producer is covered by this payload.",
            "No downstream report may bypass the STI downstream gate pointer.",
            "No public benchmark superiority claim is made.",
        ],
        "what_was_learned": (
            "STI clears the preregistered owner-local admission margins and controls."
            if verdict == "accepted"
            else "STI remains bounded by a failed owner-local admission gate."
        ),
        "reproducibility_contract": {
            "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
            "mode": "exact_fixture",
            "seed_list": [0],
            "metric_bands": [
                {
                    "pointer": "$.verdict",
                    "reference_value": verdict,
                    "tolerance": 0,
                    "comparison": "status_equal",
                    "owner": "sti-admission",
                    "calibration_source": "$.preregistration",
                    "seed_basis": {"seed_count": 1, "source": "owner-local deterministic rows"},
                }
            ],
            "device_policy": {
                "requested_device": "cpu",
                "resolved_device": "cpu",
                "resolution_status": "available",
                "resolution_reason": "STI admission is an owner-local deterministic payload validation surface",
                "backend_details": {"torch": "not-requested"},
            },
            "framework_provenance": {"python": "not-material-to-deterministic-fixture"},
            "calibration": {
                "calibration_source": "$.preregistration",
                "owner": "sti-admission",
                "basis": "fixed owner-local margins, controls, and deterministic observations",
            },
        },
    }
    payload["raw_digest"] = canonical_digest(
        {
            "task_facts": payload["task_facts"],
            "config": payload["config"],
            "observations": payload["observations"],
            "verdict": payload["verdict"],
        }
    )
    validate_sti_payload(payload)
    return payload


def validate_sti_payload(payload: Mapping[str, Any]) -> None:
    required = (
        "schema_id",
        "artifact_id",
        "generated_at",
        "task_facts",
        "preregistration",
        "config",
        "observations",
        "base_chance_gate",
        "controls",
        "verdict",
        "downstream_gate",
        "hardgate",
        "not_claimed",
    )
    missing = [key for key in required if key not in payload]
    if missing:
        raise ValueError(f"STI payload missing required keys: {', '.join(missing)}")
    if payload["schema_id"] != SCHEMA_ID:
        raise ValueError("STI payload schema_id mismatch")
    facts = payload.get("task_facts", {})
    if not isinstance(facts, Mapping) or facts.get("owner") != "bedc_quality_lab.tasks.sti":
        raise ValueError("STI task facts must be owner-local")
    if facts.get("base_margin") != BASE_MARGIN or facts.get("control_margin") != CONTROL_MARGIN:
        raise ValueError("STI margin constants must match owner-local constants")
    if tuple(facts.get("control_ids", ())) != CONTROL_IDS:
        raise ValueError("STI control ids mismatch")
    verdict = payload.get("verdict")
    if verdict not in VERDICTS:
        raise ValueError("STI verdict must be accepted or bounded_negative")
    hardgate = payload.get("hardgate", {})
    expected_verdict = "accepted" if isinstance(hardgate, Mapping) and hardgate.get("status") == "pass" else "bounded_negative"
    if verdict != expected_verdict:
        raise ValueError("STI verdict does not match hardgate status")
    downstream = payload.get("downstream_gate", {})
    if not isinstance(downstream, Mapping) or downstream.get("pointer") != DOWNSTREAM_GATE_POINTER:
        raise ValueError("STI downstream gate pointer mismatch")
    rows = payload.get("observations")
    if not isinstance(rows, list) or not rows:
        raise ValueError("STI observations must be a non-empty list")
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            raise ValueError(f"STI observation {index} must be an object")
        controls = row.get("control_scores")
        if not isinstance(controls, Mapping) or tuple(sorted(controls)) != tuple(sorted(CONTROL_IDS)):
            raise ValueError(f"STI observation {index} control set mismatch")


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# STI Admission",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Verdict: `{payload.get('verdict')}`",
        f"- Base margin: `{payload.get('config', {}).get('base_margin')}`",
        f"- Control margin: `{payload.get('config', {}).get('control_margin')}`",
        f"- Downstream gate: `{payload.get('downstream_gate', {}).get('pointer')}`",
        "",
        "## Hardgates",
        "",
        "| gate | status | evidence |",
        "| --- | --- | --- |",
    ]
    gates = payload.get("hardgate", {}).get("gates", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    if isinstance(gates, Mapping):
        for gate_name in ("BASE-CHANCE", "CONTROL", "PAYLOAD"):
            row = gates.get(gate_name, {})
            lines.append(f"| `{gate_name}` | `{row.get('status')}` | `{row.get('evidence_pointer')}` |")
    lines.extend(["", "## Controls", "", "| control | status | max delta over chance |", "| --- | --- | --- |"])
    controls = payload.get("controls", {}).get("controls", {}) if isinstance(payload.get("controls"), Mapping) else {}
    if isinstance(controls, Mapping):
        for control_id in CONTROL_IDS:
            row = controls.get(control_id, {})
            lines.append(f"| `{control_id}` | `{row.get('status')}` | `{row.get('max_delta_over_chance')}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "sti-admission",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "payload_sha256": canonical_digest(payload),
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.tasks.sti",
                "task_facts": payload.get("task_facts"),
                "config": payload.get("config"),
                "preregistration_digest": payload.get("preregistration", {}).get("preregistration_digest"),
            }
        ),
        "reproducibility_contract": payload.get("reproducibility_contract"),
        "reproducibility_contract_digest": canonical_digest(payload.get("reproducibility_contract")),
        "generated_by": {
            "runner": "scripts/run_sti_admission.py",
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
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(generated_at=generated_at)
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

"""Pointer-only character-level DGT transition helper."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer, split_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:dgt-character-lm-transition"
TARGET_SURFACE = "character-level-lm"
CHARACTER_TRANSITION_POINTER = "<dgt-owner>.json:$.character_lm_transition"
REQUIRED_RERUN_POINTER_KEYS = (
    "char_lm_run",
    "ledger_head_evidence",
    "gap_head_evidence",
    "certificate_head_evidence",
    "drt_rerun_evidence",
    "classifier_surface_delta",
)
FORBIDDEN_OUTPUT_KEYS = frozenset(
    {
        "metrics",
        "metric",
        "raw_metrics",
        "raw_body",
        "raw_report_body",
        "copied_evidence",
        "evidence_payload",
        "terminal_verdict",
        "claim_verdict",
        "discovery_projection",
    }
)
NOT_CLAIMED = (
    "No inherited D4 status.",
    "No real-world language-model claim.",
    "No terminal D5-M claim.",
    "No ClaimGraph or ClaimVerdicts acceptance.",
    "No toy DRT substitution.",
)


def build_character_lm_transition(
    *,
    toy_antecedent_pointer: str | None,
    required_rerun_pointers: Mapping[str, str],
    root: Path | None = None,
) -> dict[str, Any]:
    payload = {
        "schema_id": SCHEMA_ID,
        "target_surface": TARGET_SURFACE,
        "status": "present-but-fail-closed",
        "toy_antecedent_pointer": toy_antecedent_pointer,
        "required_rerun_pointers": dict(required_rerun_pointers),
        "hardgate": {
            "DGT-CHAR-HG1": {
                "status": "fail",
                "requirement": "character rerun pointers resolve with character DRT evidence and net-positive classifier delta",
                "failed_reason": "not-evaluated",
                "antecedent_pointer": toy_antecedent_pointer,
                "required_pointers": {key: None for key in REQUIRED_RERUN_POINTER_KEYS},
                "failed_pointer": None,
                "not_claimed_pointer": f"{CHARACTER_TRANSITION_POINTER}.not_claimed",
            }
        },
        "discovery_map_signal": {
            "level_candidate": "DN",
            "status": "present-but-fail-closed",
            "evidence_pointer": None,
            "failed_gate": "DGT-CHAR-HG1",
            "failed_gate_pointer": f"{CHARACTER_TRANSITION_POINTER}.hardgate.DGT-CHAR-HG1",
            "net_positive_signal": False,
        },
        "not_claimed": list(NOT_CLAIMED),
    }
    return validate_character_lm_transition(payload, root=root)


def validate_character_lm_transition(payload: Mapping[str, Any], *, root: Path | None = None) -> dict[str, Any]:
    _require_schema(payload)
    output = {key: _copy_value(value) for key, value in payload.items()}
    pointers = dict(output["required_rerun_pointers"])
    gate = output["hardgate"]["DGT-CHAR-HG1"]
    signal = output["discovery_map_signal"]
    failed_reason, failed_pointer = _first_failure(pointers, root=root)
    passed = failed_reason is None

    gate["status"] = "pass" if passed else "fail"
    gate["required_pointers"] = {key: pointers[key] for key in REQUIRED_RERUN_POINTER_KEYS}
    gate["failed_reason"] = None if passed else failed_reason
    gate["failed_pointer"] = None if passed else failed_pointer

    output["status"] = "pass" if passed else "present-but-fail-closed"
    signal["level_candidate"] = "D4" if passed else "DN"
    signal["status"] = "pass" if passed else "present-but-fail-closed"
    signal["evidence_pointer"] = pointers["classifier_surface_delta"] if passed else None
    signal["failed_gate"] = None if passed else "DGT-CHAR-HG1"
    signal["failed_gate_pointer"] = None if passed else f"{CHARACTER_TRANSITION_POINTER}.hardgate.DGT-CHAR-HG1"
    signal["net_positive_signal"] = _net_positive_signal(pointers["classifier_surface_delta"], root=root)
    _assert_pointer_only(output)
    return output


def _require_schema(payload: Mapping[str, Any]) -> None:
    expected = {
        "schema_id",
        "target_surface",
        "status",
        "toy_antecedent_pointer",
        "required_rerun_pointers",
        "hardgate",
        "discovery_map_signal",
        "not_claimed",
    }
    if set(payload) != expected:
        raise ValueError("character_lm_transition top-level fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["target_surface"] != TARGET_SURFACE:
        raise ValueError("character_lm_transition identity mismatch")
    pointers = payload["required_rerun_pointers"]
    if not isinstance(pointers, Mapping) or tuple(pointers) != REQUIRED_RERUN_POINTER_KEYS:
        raise ValueError("character_lm_transition rerun pointer set mismatch")
    if set(payload["hardgate"]) != {"DGT-CHAR-HG1"}:
        raise ValueError("character_lm_transition hardgate mismatch")
    if "discovery_projection" in payload:
        raise ValueError("character_lm_transition uses unsupported discovery_projection alias")


def _first_failure(pointers: Mapping[str, str], *, root: Path | None) -> tuple[str | None, str | None]:
    for key in REQUIRED_RERUN_POINTER_KEYS:
        pointer = pointers[key]
        if not _host_canonical_pointer(pointer):
            return "non-canonical-or-invalid-pointer", pointer
        if root is not None and resolve_artifact_pointer(root, pointer) is None:
            return "unresolved-pointer", pointer
    for key, pointer in pointers.items():
        lowered = pointer.lower()
        if "toy" in lowered:
            return "toy-evidence-is-antecedent-only", pointer
        if key != "drt_rerun_evidence" and "drt" in lowered:
            return "existing-drt-evidence-is-not-character-rerun", pointer
    drt = _resolved_mapping(pointers["drt_rerun_evidence"], root=root)
    if root is not None and drt.get("target_surface") != TARGET_SURFACE:
        return "drt-rerun-is-not-character-surface", pointers["drt_rerun_evidence"]
    if root is not None and not bool(drt.get("character_surface_rerun")):
        return "drt-rerun-is-not-character-surface", pointers["drt_rerun_evidence"]
    if not _net_positive_signal(pointers["classifier_surface_delta"], root=root):
        return "classifier-surface-delta-not-net-positive", pointers["classifier_surface_delta"]
    return None, None


def _host_canonical_pointer(pointer: Any) -> bool:
    if not isinstance(pointer, str):
        return False
    split = split_artifact_pointer(pointer)
    return split is not None and split[0].startswith("reports/canonical/")


def _resolved_mapping(pointer: str, *, root: Path | None) -> Mapping[str, Any]:
    if root is None:
        return {}
    value = resolve_artifact_pointer(root, pointer)
    return value if isinstance(value, Mapping) else {}


def _net_positive_signal(pointer: str, *, root: Path | None) -> bool:
    if root is None:
        return False
    value = resolve_artifact_pointer(root, pointer)
    return isinstance(value, Mapping) and value.get("target_surface") == TARGET_SURFACE and value.get("net_positive_signal") is True


def _assert_pointer_only(value: Any) -> None:
    if isinstance(value, Mapping):
        for key, child in value.items():
            if key in FORBIDDEN_OUTPUT_KEYS:
                raise ValueError(f"character_lm_transition copied evidence field: {key}")
            _assert_pointer_only(child)
    elif isinstance(value, list):
        for child in value:
            _assert_pointer_only(child)
    elif isinstance(value, str) and ".refactor-loop" in value:
        raise ValueError("character_lm_transition contains orchestration path")


def _copy_value(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {key: _copy_value(child) for key, child in value.items()}
    if isinstance(value, list):
        return [_copy_value(child) for child in value]
    return value

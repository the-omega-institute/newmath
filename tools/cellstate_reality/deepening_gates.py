#!/usr/bin/env python3
"""Deterministic gates for cell-state conjecture deepening packets."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_CONJECTURES = SCRIPT_DIR / "inbox" / "conjectures.jsonl"
DEFAULT_CONTACTS = SCRIPT_DIR / "inbox" / "reality_contacts.jsonl"
DEFAULT_PROBES = SCRIPT_DIR / "inbox" / "probes.jsonl"
DEFAULT_MISMATCHES = SCRIPT_DIR / "inbox" / "mismatches.jsonl"
DEFAULT_OUTPUT = SCRIPT_DIR / "out" / "gate_results.jsonl"

ID_PATTERN = r"^[a-z0-9][a-z0-9.:-]*$"
ID_SYNTAX = f"ids must match {ID_PATTERN}; use lowercase dotted/kebab tokens, not underscores or uppercase"
ID_RE = re.compile(ID_PATTERN)

LAYERS = {
    "genome_source",
    "context",
    "age_signature",
    "cell_identity",
    "function_realization",
    "safety_boundary",
    "renewable_maintenance",
    "organismal_maintenance",
    "cross_layer_relation",
}
LAYER_ORDER = [
    "genome_source",
    "context",
    "age_signature",
    "cell_identity",
    "function_realization",
    "safety_boundary",
    "renewable_maintenance",
    "organismal_maintenance",
    "cross_layer_relation",
]
LAYER_RANK = {layer: index for index, layer in enumerate(LAYER_ORDER)}
OVERCLAIM_GATES_ENABLED = True
PROXY_OBJECTIVE_EVIDENCE_BASIS = {"internal_structure", "derived_probe"}
EVIDENCE_BASIS = {
    "external_reality",
    "internal_structure",
    "bedc_coordinate",
    "bedc_closure",
    "bedc_spectrum",
    "derived_probe",
    "mismatch_ledger",
    "mechanism_bridge",
}
CONTACT_KINDS = {
    "methylation_array",
    "clock_coefficient_table",
    "rnaseq_expression",
    "identity_marker_panel",
    "pluripotency_marker_panel",
    "functional_assay",
    "safety_assay",
    "perturbation_data",
    "longitudinal_cycle_data",
    "organismal_phenotype",
    "curated_annotation",
    "manual_observation",
}
REALIZATION_CONTACT_KINDS_BY_LAYER = {
    "age_signature": {
        "methylation_array",
        "clock_coefficient_table",
        "perturbation_data",
    },
    "context": {
        "methylation_array",
        "rnaseq_expression",
        "perturbation_data",
    },
    "cell_identity": {
        "rnaseq_expression",
        "identity_marker_panel",
        "perturbation_data",
    },
    "function_realization": {
        "functional_assay",
        "perturbation_data",
    },
    "safety_boundary": {
        "pluripotency_marker_panel",
        "safety_assay",
        "rnaseq_expression",
        "perturbation_data",
    },
    "renewable_maintenance": {
        "longitudinal_cycle_data",
        "perturbation_data",
    },
    "organismal_maintenance": {
        "organismal_phenotype",
        "functional_assay",
        "perturbation_data",
    },
    "cross_layer_relation": {
        "methylation_array",
        "clock_coefficient_table",
        "rnaseq_expression",
        "identity_marker_panel",
        "pluripotency_marker_panel",
        "functional_assay",
        "safety_assay",
        "perturbation_data",
        "longitudinal_cycle_data",
        "organismal_phenotype",
    },
}
PROBE_KINDS = {
    "finite_enumeration",
    "forbidden_pattern",
    "closure_completion",
    "spectral_concentration",
    "counterexample_search",
    "boundary_mismatch",
    "known_special_case",
    "cross_layer_consistency",
}
PROBE_REQUIRED_FIELDS = {
    "probe_id",
    "conjecture_ref",
    "probe_kind",
    "derived_from",
    "test_statement",
    "support_condition",
    "break_condition",
    "required_contacts",
    "forbidden_interpretations",
    "null_reason",
}
DERIVED_FROM = {
    "bedc_coordinate",
    "bedc_closure",
    "bedc_spectrum",
    "trigger_relation",
    "rank_relation",
    "homology_witness",
    "external_reality_hint",
}
MISMATCH_STATUS = {"aligned", "partially_aligned", "mismatch", "underdetermined", "blocked_null"}
MISMATCH_KINDS = {
    "coordinate_failure",
    "scope_too_large",
    "missing_context",
    "external_data_bias",
    "mechanism_gap",
    "conjecture_overclaim",
    "none",
}
INTERNAL_STRUCTURES = {"coordinate", "closure", "spectrum", "trigger", "rank", "homology", "relation", "none"}
MECHANISM_WORDS = {
    "cause",
    "causes",
    "mechanism",
    "mechanistic",
    "biochemical mechanism",
    "evolutionary necessity",
}
MECHANISM_STRONG_WORDS = {
    "mechanism",
    "mechanistic",
    "causal",
    "causes",
    "caused by",
    "realization",
    "realizes",
    "realise",
    "realises",
    "executes",
    "execution",
    "function realization",
    "biological function",
    "protein function",
    "functional role",
    "physical admissibility",
    "physical admissib",
    "folding mechanism",
    "translation mechanism",
    "biochemical mechanism",
}
MECHANISM_NEGATION_WORDS = {
    "not",
    "no",
    "cannot",
    "can't",
    "does not",
    "doesn't",
    "do not",
    "don't",
}
TOTAL_BIOLOGY_WORDS = {
    "full biology",
    "all biology",
    "general biological model",
    "total biology",
}
AGE_CLOCK_CONTEXT_WORDS = {
    "ageclockshift",
    "age-clock",
    "age clock",
    "clock shift",
    "dnam age",
    "dna methylation age",
    "methylation age",
    "horvath",
}
AGE_CLOCK_PROMOTION_REQUIREMENTS = [
    (
        "identity_retention",
        {"identitypreservingagereset", "identity-preserving age reset", "identity preserving age reset", "age reset"},
        {"cell_identity"},
    ),
    (
        "functional_repair_or_rejuvenation",
        {"rejuvenation", "rejuvenationcandidate", "functional repair", "phenotype repair"},
        {"function_realization"},
    ),
    (
        "partial_reprogramming_state_boundary",
        {"partialreprogramming", "partial reprogramming"},
        {"cell_identity", "safety_boundary"},
    ),
    (
        "renewable_maintenance_horizon",
        {"renewablemaintenance", "renewable maintenance", "repeat cycle", "repeat-cycle"},
        {"renewable_maintenance"},
    ),
    (
        "organismal_horizon",
        {"immortalitypotential", "immortality potential", "immortality"},
        {"organismal_maintenance"},
    ),
]


def read_jsonl(path: Path, *, allow_missing: bool = True) -> list[dict[str, Any]]:
    if not path.exists():
        if allow_missing:
            return []
        raise FileNotFoundError(path)
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                data = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            records.append(data)
    return records


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _missing(record: dict[str, Any], required: set[str]) -> list[str]:
    return [f"missing required field: {key}" for key in sorted(required - set(record))]


def _id(key: str, value: Any, issues: list[str]) -> None:
    if not isinstance(value, str) or not ID_RE.match(value):
        issues.append(_invalid_id_issue(key, value))


def _is_id(value: Any) -> bool:
    return isinstance(value, str) and ID_RE.match(value) is not None


def _id_repair_hint(value: Any) -> str:
    if not isinstance(value, str) or not value:
        return ""
    repaired = re.sub(r"[^a-z0-9.:-]+", "-", value.lower()).strip(".:-")
    hint = f"; suggested normalized id: {repaired}" if repaired and repaired != value else ""
    return hint + _id_layer_token_hint(value)


def _id_layer_token_hint(value: str) -> str:
    layer_tokens = [layer for layer in LAYER_ORDER if layer in value.lower()]
    if not layer_tokens:
        return ""
    examples = ", ".join(f"{layer}->{layer.replace('_', '-')}" for layer in layer_tokens[:2])
    return f"; layer tokens embedded in ids must be hyphenated ({examples}); keep underscores in layer fields"


def _invalid_id_issue(key: str, value: Any) -> str:
    observed = f": {value}" if isinstance(value, str) and value else ""
    return f"{key}: invalid id{observed}; {ID_SYNTAX}{_id_repair_hint(value)}"


def _nonempty(key: str, value: Any, issues: list[str]) -> None:
    if not isinstance(value, str) or not value.strip():
        issues.append(f"{key} must be a nonempty string")


def _array(key: str, value: Any, issues: list[str], *, allowed: set[str] | None = None, min_items: int = 0) -> list[str]:
    values: list[str] = []
    if not isinstance(value, list):
        issues.append(f"{key} must be an array")
        return values
    if len(value) < min_items:
        issues.append(f"{key} must contain at least {min_items} item(s)")
    for item in value:
        if not isinstance(item, str) or not item.strip():
            issues.append(f"{key} contains a non-string item")
            continue
        if allowed is not None and item not in allowed:
            issues.append(f"{key} contains unrecognized item: {item}")
        values.append(item)
    return values


def _has_any(text: str, needles: set[str]) -> bool:
    lowered = text.lower()
    return any(needle in lowered for needle in needles)


def _normalize_layer_text(value: Any) -> str:
    return str(value).lower().strip().replace("_", " ")


def _layer_in_scope(layer: str, scope: str) -> bool:
    normalized_layer = _normalize_layer_text(layer)
    normalized_scope = _normalize_layer_text(scope)
    return normalized_layer == normalized_scope or normalized_layer in normalized_scope


def _highest_can_test_layer(can_test: list[str]) -> str | None:
    covered = [
        layer
        for layer in LAYER_ORDER
        if any(_layer_in_scope(layer, item) for item in can_test)
    ]
    return covered[-1] if covered else None


def _has_positive_mechanism_language(text: Any) -> bool:
    if not isinstance(text, str):
        return False
    lowered = text.lower()
    if any(re.search(rf"\b{re.escape(negation)}\b", lowered) for negation in MECHANISM_NEGATION_WORDS):
        return False
    return any(word in lowered for word in MECHANISM_STRONG_WORDS)


def _has_layer_contact(can_test: list[str], required_layers: set[str]) -> bool:
    return any(_layer_in_scope(layer, item) for layer in required_layers for item in can_test)


def _positive_phrase_present(lowered: str, compact: str, phrase: str) -> bool:
    if phrase in lowered:
        start = lowered.find(phrase)
        prefix = lowered[max(0, start - 40) : start]
        if any(negation in prefix for negation in MECHANISM_NEGATION_WORDS):
            return False
        return True
    compact_phrase = re.sub(r"[^a-z0-9]+", "", phrase)
    if compact_phrase and compact_phrase in compact:
        start = compact.find(compact_phrase)
        prefix = compact[max(0, start - 40) : start]
        return not any(negation.replace(" ", "") in prefix for negation in MECHANISM_NEGATION_WORDS)
    return False


def _age_clock_promotion_issues(statement_text: str, can_test: list[str]) -> list[str]:
    lowered = statement_text.lower()
    compact = re.sub(r"[^a-z0-9]+", "", lowered)
    if not any(word in lowered or word in compact for word in AGE_CLOCK_CONTEXT_WORDS):
        return []
    issues: list[str] = []
    for gate_name, phrases, required_layers in AGE_CLOCK_PROMOTION_REQUIREMENTS:
        if any(_positive_phrase_present(lowered, compact, phrase) for phrase in phrases) and not _has_layer_contact(
            can_test, required_layers
        ):
            required = ", ".join(sorted(required_layers))
            issues.append(
                f"age_clock_promotion_requires_separate_contact:{gate_name}: clock/DNAm age rows cannot be "
                f"promoted to this claim without a reality contact whose can_test includes {required}"
            )
    return issues


def validate_contact(record: dict[str, Any]) -> list[str]:
    required = {
        "contact_id",
        "source_kind",
        "source_ref",
        "source_snapshot",
        "observed_fact",
        "resolution",
        "known_noise_or_bias",
        "can_test",
        "cannot_test",
        "null_reason",
    }
    issues = _missing(record, required)
    if issues:
        return issues
    _id("contact_id", record.get("contact_id"), issues)
    if record.get("source_kind") not in CONTACT_KINDS:
        issues.append("source_kind is not recognized")
    for key in ("source_ref", "source_snapshot", "observed_fact", "resolution"):
        _nonempty(key, record.get(key), issues)
    _array("can_test", record.get("can_test"), issues, min_items=1)
    _array("cannot_test", record.get("cannot_test"), issues, min_items=1)
    return issues


def validate_probe(record: dict[str, Any], conjecture_by_id: dict[str, dict[str, Any]], contact_ids: set[str]) -> list[str]:
    issues = _missing(record, PROBE_REQUIRED_FIELDS)
    if issues:
        return issues
    _id("probe_id", record.get("probe_id"), issues)
    _id("conjecture_ref", record.get("conjecture_ref"), issues)
    conjecture = conjecture_by_id.get(str(record.get("conjecture_ref") or ""))
    if _is_id(record.get("conjecture_ref")) and conjecture is None:
        issues.append(f"conjecture_ref not found: {record.get('conjecture_ref')}")
    if record.get("probe_kind") not in PROBE_KINDS:
        issues.append("probe_kind is not recognized")
    _array("derived_from", record.get("derived_from"), issues, allowed=DERIVED_FROM, min_items=1)
    for key in ("test_statement", "support_condition", "break_condition"):
        _nonempty(key, record.get(key), issues)
    contacts = _array("required_contacts", record.get("required_contacts"), issues)
    for contact in contacts:
        if not _is_id(contact):
            issues.append(_invalid_id_issue("required_contacts item", contact))
        elif contact not in contact_ids:
            issues.append(f"required contact not found: {contact}")
    _array("forbidden_interpretations", record.get("forbidden_interpretations"), issues, min_items=1)
    structural_probe_kinds = {
        "boundary_mismatch",
        "finite_enumeration",
        "forbidden_pattern",
        "closure_completion",
        "spectral_concentration",
    }
    if record.get("probe_kind") in structural_probe_kinds and conjecture is not None:
        claimed_layer = conjecture.get("claimed_layer")
        evidence = conjecture.get("evidence_basis")
        if (
            claimed_layer not in {"genome_source"}
            and (not isinstance(evidence, list) or "mechanism_bridge" not in evidence)
        ):
            issues.append(
                f"structural probe_kind {record.get('probe_kind')} attached to higher-layer conjecture "
                f"{record.get('conjecture_ref')} requires mechanism_bridge evidence on the conjecture"
            )
    return issues


def validate_mismatch(record: dict[str, Any], probe_ids: set[str], contact_ids: set[str]) -> list[str]:
    required = {
        "mismatch_id",
        "probe_ref",
        "contact_ref",
        "status",
        "mismatch_kind",
        "observed_delta",
        "refinement_pressure",
        "blocked_claims",
        "null_reason",
    }
    issues = _missing(record, required)
    if issues:
        return issues
    _id("mismatch_id", record.get("mismatch_id"), issues)
    _id("probe_ref", record.get("probe_ref"), issues)
    _id("contact_ref", record.get("contact_ref"), issues)
    if _is_id(record.get("probe_ref")) and record.get("probe_ref") not in probe_ids:
        probe_ref = str(record.get("probe_ref"))
        issues.append(f"probe_ref not found: {probe_ref}")
        mismatch_id = str(record.get("mismatch_id") or "")
        if mismatch_id.endswith(".scope-review"):
            issues.append(
                f"scope_review_requires_existing_probe: {mismatch_id} cannot be reviewed until probe_ref {probe_ref} exists"
            )
    if _is_id(record.get("contact_ref")) and record.get("contact_ref") not in contact_ids:
        issues.append(f"contact_ref not found: {record.get('contact_ref')}")
    if record.get("status") not in MISMATCH_STATUS:
        issues.append("status is not recognized")
    if record.get("mismatch_kind") not in MISMATCH_KINDS:
        issues.append("mismatch_kind is not recognized")
    if record.get("status") in {"mismatch", "partially_aligned"} and record.get("mismatch_kind") == "none":
        issues.append("mismatch or partial alignment requires a non-none mismatch_kind")
    for key in ("observed_delta", "refinement_pressure"):
        _nonempty(key, record.get(key), issues)
    _array("blocked_claims", record.get("blocked_claims"), issues, min_items=1)
    return issues


def validate_conjecture(
    record: dict[str, Any],
    contact_by_id: dict[str, dict[str, Any]],
    probe_ids: set[str],
) -> list[str]:
    required = {
        "conjecture_id",
        "biological_object",
        "informal_statement",
        "bedc_minimal_form",
        "claimed_layer",
        "evidence_basis",
        "reality_contact_refs",
        "probe_refs",
        "forbidden_claims",
        "null_reason",
    }
    issues = _missing(record, required)
    if issues:
        return issues
    _id("conjecture_id", record.get("conjecture_id"), issues)
    for key in ("biological_object", "informal_statement"):
        _nonempty(key, record.get(key), issues)
    if record.get("claimed_layer") not in LAYERS:
        issues.append("claimed_layer is not recognized")
    evidence = set(_array("evidence_basis", record.get("evidence_basis"), issues, allowed=EVIDENCE_BASIS, min_items=1))
    contacts = _array("reality_contact_refs", record.get("reality_contact_refs"), issues)
    probes = _array("probe_refs", record.get("probe_refs"), issues)
    _array("forbidden_claims", record.get("forbidden_claims"), issues, min_items=1)
    for contact in contacts:
        if not _is_id(contact):
            issues.append(_invalid_id_issue("reality_contact_refs item", contact))
        elif contact not in contact_by_id:
            issues.append(f"reality contact not found: {contact}")
    for probe in probes:
        if not _is_id(probe):
            issues.append(_invalid_id_issue("probe_refs item", probe))
        elif probe not in probe_ids:
            issues.append(f"probe not found: {probe}")

    form = record.get("bedc_minimal_form")
    if not isinstance(form, dict):
        issues.append("bedc_minimal_form must be an object")
    else:
        for key in ("carrier", "readback"):
            _nonempty(f"bedc_minimal_form.{key}", form.get(key), issues)
        _array("bedc_minimal_form.distinctions", form.get("distinctions"), issues, min_items=1)
        internal = set(_array("bedc_minimal_form.internal_structure", form.get("internal_structure"), issues, allowed=INTERNAL_STRUCTURES))
        if "none" in internal and len(internal) > 1:
            issues.append("bedc_minimal_form.internal_structure cannot mix none with explicit structures")
        if evidence & {"bedc_coordinate", "bedc_closure", "bedc_spectrum"} and not (internal - {"none"}):
            issues.append("BEDC evidence requires explicit internal structure")

    text_parts = [
        str(record.get("biological_object", "")),
        str(record.get("informal_statement", "")),
        " ".join(str(item) for item in record.get("forbidden_claims", []) if isinstance(item, str)),
    ]
    claim_text_parts = [
        str(record.get("biological_object", "")),
        str(record.get("informal_statement", "")),
    ]
    if isinstance(form, dict):
        text_parts.extend([str(form.get("readback", "")), str(form.get("carrier", ""))])
        claim_text_parts.extend([str(form.get("readback", "")), str(form.get("carrier", ""))])
    text = " ".join(text_parts)
    claim_text = " ".join(claim_text_parts)
    if "external_reality" in evidence and not contacts:
        issues.append("external_reality evidence requires reality_contact_refs")
    if "derived_probe" in evidence and not probes:
        issues.append("derived_probe evidence requires probe_refs")
    if contacts:
        claimed_layer = record.get("claimed_layer")
        normalized_layer = _normalize_layer_text(claimed_layer)
        can_test: list[str] = []
        cannot_test: list[str] = []
        contact_kinds: set[str] = set()
        for contact_ref in contacts:
            contact_record = contact_by_id.get(contact_ref)
            if contact_record is None:
                continue
            if isinstance(contact_record.get("source_kind"), str):
                contact_kinds.add(str(contact_record.get("source_kind")))
            can_test.extend(str(item) for item in contact_record.get("can_test", []) if isinstance(item, str))
            cannot_test.extend(str(item) for item in contact_record.get("cannot_test", []) if isinstance(item, str))
        layer_in_can_test = any(normalized_layer == _normalize_layer_text(item) or normalized_layer in _normalize_layer_text(item) for item in can_test)
        layer_in_cannot_test = any(
            normalized_layer == _normalize_layer_text(item) or normalized_layer in _normalize_layer_text(item)
            for item in cannot_test
        )
        realization_kinds = REALIZATION_CONTACT_KINDS_BY_LAYER.get(str(claimed_layer))
        if realization_kinds is not None and not (contact_kinds & realization_kinds):
            issues.append(
                f"claimed_layer {claimed_layer} requires a layer-matched realization reality contact; "
                f"source signatures and BEDC geometry do not establish context, identity, function, safety, maintenance, or cross-layer law"
            )
        if not layer_in_can_test and layer_in_cannot_test:
            issues.append(
                f"claimed_layer {claimed_layer} is in cannot_test of all attached contacts; promote requires "
                f"a separate reality contact that can_test layer {claimed_layer}"
            )
        elif not layer_in_can_test and not layer_in_cannot_test:
            issues.append(f"claimed_layer {claimed_layer} is not addressed by any attached reality contact")
        max_can_test = _highest_can_test_layer(can_test)
        claimed_layer_rank = LAYER_RANK.get(str(claimed_layer))
        max_can_test_rank = LAYER_RANK.get(str(max_can_test)) if max_can_test is not None else None
        if (
            OVERCLAIM_GATES_ENABLED
            and claimed_layer_rank is not None
            and max_can_test_rank is not None
            and claimed_layer_rank > max_can_test_rank
            and evidence & PROXY_OBJECTIVE_EVIDENCE_BASIS
        ):
            basis = ", ".join(sorted(evidence & PROXY_OBJECTIVE_EVIDENCE_BASIS))
            issues.append(
                f"proxy_objective_separation: proxy/internal evidence ({basis}) cannot support claimed_layer "
                f"{claimed_layer} above reality-contact can_test {max_can_test}"
            )
        if (
            OVERCLAIM_GATES_ENABLED
            and claimed_layer_rank is not None
            and _has_positive_mechanism_language(record.get("informal_statement"))
            and not layer_in_can_test
        ):
            issues.append(
                "mechanism_closure_requires_separate_contact: mechanism/realization wording requires "
                f"a layer-matched reality contact whose can_test includes {claimed_layer}"
            )
        issues.extend(_age_clock_promotion_issues(claim_text, can_test))
    elif (
        OVERCLAIM_GATES_ENABLED
        and record.get("claimed_layer") in LAYERS
        and _has_positive_mechanism_language(record.get("informal_statement"))
    ):
        issues.append(
            "mechanism_closure_requires_separate_contact: mechanism/realization wording requires "
            f"a layer-matched reality contact whose can_test includes {record.get('claimed_layer')}"
        )
    if _has_any(text, MECHANISM_WORDS) and "mechanism_bridge" not in evidence:
        issues.append("mechanism language requires mechanism_bridge evidence")
    if _has_any(text, TOTAL_BIOLOGY_WORDS):
        issues.append("total-biology language is blocked in conjecture packets")
    return issues


def _index(records: list[dict[str, Any]], key: str) -> tuple[dict[str, dict[str, Any]], list[str]]:
    by_id: dict[str, dict[str, Any]] = {}
    issues: list[str] = []
    for index, record in enumerate(records, 1):
        value = str(record.get(key) or "")
        if not ID_RE.match(value):
            issues.append(f"{key}:{index}: {_invalid_id_issue(key, value)}")
            continue
        if value in by_id:
            issues.append(f"{key}:{index}: duplicate id: {value}")
            continue
        by_id[value] = record
    return by_id, issues


def gate_all(
    conjectures: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    contact_by_id, contact_index_issues = _index(contacts, "contact_id")
    conjecture_by_id, conjecture_index_issues = _index(conjectures, "conjecture_id")
    probe_by_id, probe_index_issues = _index(probes, "probe_id")
    contact_ids = set(contact_by_id)
    probe_ids = set(probe_by_id)

    shared_issues = contact_index_issues + conjecture_index_issues + probe_index_issues
    results: list[dict[str, Any]] = []
    for contact in contacts:
        contact_id = str(contact.get("contact_id") or "")
        issues = validate_contact(contact) + shared_issues
        results.append(_result("reality_contact", contact_id, issues))
    for probe in probes:
        probe_id = str(probe.get("probe_id") or "")
        issues = validate_probe(probe, conjecture_by_id, contact_ids) + shared_issues
        results.append(_result("probe", probe_id, issues))
    for mismatch in mismatches:
        mismatch_id = str(mismatch.get("mismatch_id") or "")
        issues = validate_mismatch(mismatch, probe_ids, contact_ids) + shared_issues
        results.append(_result("mismatch", mismatch_id, issues))
    for conjecture in conjectures:
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        issues = validate_conjecture(conjecture, contact_by_id, probe_ids) + shared_issues
        results.append(_result("conjecture", conjecture_id, issues))
    return sorted(results, key=lambda item: (item["gate_status"], item["packet_kind"], item["packet_id"]))


def _result(packet_kind: str, packet_id: str, issues: list[str]) -> dict[str, Any]:
    return {
        "packet_kind": packet_kind,
        "packet_id": packet_id,
        "gate_status": "gate_blocked" if issues else "gate_passed",
        "issues": issues,
        "allowed_write": "none",
        "next_action": "fix gate issues before review" if issues else "eligible for operator review only",
    }


def self_test() -> int:
    contact = {
        "contact_id": "clock.horvath.array",
        "source_kind": "methylation_array",
        "source_ref": "paired methylation age-clock fixture",
        "source_snapshot": "fixture",
        "observed_fact": "A paired methylation fixture records a named age-clock shift.",
        "resolution": "clock CpG readback",
        "known_noise_or_bias": "fixture only",
        "can_test": ["age_signature layer"],
        "cannot_test": ["cell identity", "function realization", "safety boundary", "renewable maintenance"],
        "null_reason": "",
    }
    perturbation_contact = {
        "contact_id": "reprogramming.perturbation.fixture",
        "source_kind": "perturbation_data",
        "source_ref": "fixture perturbation matrix for clock and identity readbacks",
        "source_snapshot": "fixture",
        "observed_fact": "A perturbation fixture records age-signature and cross-layer responses.",
        "resolution": "perturbation readback",
        "known_noise_or_bias": "fixture only",
        "can_test": ["age_signature", "cross_layer_relation"],
        "cannot_test": ["immortality", "organismal maintenance"],
        "null_reason": "",
    }
    function_contact = {
        "contact_id": "function.assay.fixture",
        "source_kind": "functional_assay",
        "source_ref": "fixture function assay",
        "source_snapshot": "fixture",
        "observed_fact": "A functional assay fixture records a bounded function-layer readback.",
        "resolution": "function assay readback",
        "known_noise_or_bias": "fixture only",
        "can_test": ["function_realization"],
        "cannot_test": ["renewable maintenance", "organismal maintenance"],
        "null_reason": "",
    }
    conjecture = {
        "conjecture_id": "age-clock-shift.clock.read",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "A named clock records an age-signature shift under paired methylation contact.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["pre perturbation clock value", "post perturbation clock value"],
            "readback": "named clock coefficient table applied to the pair",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "age_signature",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["An age-clock shift alone is not identity preservation, function, safety, rejuvenation, or immortality."],
        "null_reason": "",
    }
    overclaim = {
        "conjecture_id": "cellstate.world.model",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "This is a full biology explanation for rejuvenation and immortal potential.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock delta"],
            "readback": "clock shift",
            "internal_structure": ["none"],
        },
        "claimed_layer": "renewable_maintenance",
        "evidence_basis": ["external_reality"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["No forbidden claim."],
        "null_reason": "",
    }
    b1_overclaim = {
        "conjecture_id": "identity.overclaim",
        "biological_object": "IdentityPreservingAgeResetUp",
        "informal_statement": "The age-clock coordinate is presented as a cell-identity packet.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock delta"],
            "readback": "age-signature readback",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "cell_identity",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["The clock contact alone does not establish identity preservation."],
        "null_reason": "",
    }
    b3_conjecture = {
        "conjecture_id": "identity.probe.overreach",
        "biological_object": "IdentityPreservingAgeResetUp",
        "informal_statement": "The packet is placed at the cell-identity layer.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock delta"],
            "readback": "age-signature readback",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "cell_identity",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": ["identity.boundary.probe.overreach"],
        "forbidden_claims": ["The boundary probe is not an identity-marker contact."],
        "null_reason": "",
    }
    b3_probe = {
        "probe_id": "identity.boundary.probe.overreach",
        "conjecture_ref": "identity.probe.overreach",
        "probe_kind": "boundary_mismatch",
        "derived_from": ["bedc_coordinate"],
        "test_statement": "Check whether a coordinate boundary mismatches the clock readback.",
        "support_condition": "The boundary is stable under the finite age-signature reading.",
        "break_condition": "The boundary does not survive contact with the paired clock readback.",
        "required_contacts": ["clock.horvath.array"],
        "forbidden_interpretations": ["The boundary alone proves identity preservation."],
        "null_reason": "",
    }
    bedc_without_structure = {
        "conjecture_id": "bedc.structure.missing",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "The packet has BEDC coordinate evidence but no internal structure.",
        "bedc_minimal_form": {
            "carrier": "clock window",
            "distinctions": ["clock boundary"],
            "readback": "clock enumeration",
            "internal_structure": [],
        },
        "claimed_layer": "genome_source",
        "evidence_basis": ["bedc_coordinate"],
        "reality_contact_refs": [],
        "probe_refs": [],
        "forbidden_claims": ["Coordinate evidence alone is not age-signature realization."],
        "null_reason": "",
    }
    mixed_none_structure = {
        "conjecture_id": "bedc.structure.mixed",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "The packet mixes no internal structure with an explicit coordinate.",
        "bedc_minimal_form": {
            "carrier": "clock window",
            "distinctions": ["clock boundary"],
            "readback": "clock enumeration",
            "internal_structure": ["none", "coordinate"],
        },
        "claimed_layer": "genome_source",
        "evidence_basis": ["bedc_coordinate"],
        "reality_contact_refs": [],
        "probe_refs": [],
        "forbidden_claims": ["Coordinate evidence alone is not age-signature realization."],
        "null_reason": "",
    }
    cross_layer_code_only = {
        "conjecture_id": "cross.layer.clock.only",
        "biological_object": "AgeClockShiftUp to IdentityPreservingAgeResetUp",
        "informal_statement": "The packet claims only a cross-layer relation.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock boundary"],
            "readback": "clock table",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "cross_layer_relation",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["The clock contact alone does not establish a cross-layer promotion."],
        "null_reason": "",
    }
    cross_layer_perturbed = {
        "conjecture_id": "cross.layer.perturbed",
        "biological_object": "AgeClockShiftUp to context response",
        "informal_statement": "The packet claims a bounded cross-layer relation with perturbation contact.",
        "bedc_minimal_form": {
            "carrier": "paired perturbation readback",
            "distinctions": ["clock boundary"],
            "readback": "perturbation readback",
            "internal_structure": ["coordinate", "relation"],
        },
        "claimed_layer": "cross_layer_relation",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["reprogramming.perturbation.fixture"],
        "probe_refs": [],
        "forbidden_claims": ["The perturbation readback is not a rejuvenation or immortality law."],
        "null_reason": "",
    }
    proxy_objective_overclaim = {
        "conjecture_id": "proxy.objective.overclaim",
        "biological_object": "IdentityPreservingAgeResetUp",
        "informal_statement": "The internal coordinate is presented as a cell-identity packet.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock delta"],
            "readback": "age-signature readback",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "cell_identity",
        "evidence_basis": ["external_reality", "internal_structure"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["The clock contact alone does not establish identity preservation."],
        "null_reason": "",
    }
    mechanism_without_contact = {
        "conjecture_id": "mechanism.contact.missing",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "The coordinate realizes age-signature resetting in the packet.",
        "bedc_minimal_form": {
            "carrier": "clock window",
            "distinctions": ["clock boundary"],
            "readback": "clock enumeration",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "age_signature",
        "evidence_basis": ["bedc_coordinate"],
        "reality_contact_refs": [],
        "probe_refs": [],
        "forbidden_claims": ["Coordinate evidence alone is not an age-signature mechanism."],
        "null_reason": "",
    }
    mechanism_layer_matched = {
        "conjecture_id": "mechanism.layer.matched",
        "biological_object": "functional assay packet",
        "informal_statement": "The assay realizes bounded cell function for the packet.",
        "bedc_minimal_form": {
            "carrier": "assay readback",
            "distinctions": ["activity label"],
            "readback": "functional assay readback",
            "internal_structure": ["none"],
        },
        "claimed_layer": "function_realization",
        "evidence_basis": ["external_reality", "mechanism_bridge"],
        "reality_contact_refs": ["function.assay.fixture"],
        "probe_refs": [],
        "forbidden_claims": ["The assay does not establish renewable or organismal maintenance."],
        "null_reason": "",
    }
    age_clock_rejuvenation_rephrase = {
        "conjecture_id": "age.clock.rejuvenation.rephrase",
        "biological_object": "AgeClockShiftUp",
        "informal_statement": "The DNAm age clock shift is presented as rejuvenation.",
        "bedc_minimal_form": {
            "carrier": "paired methylation profile",
            "distinctions": ["clock delta"],
            "readback": "Horvath clock shift",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "age_signature",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["clock.horvath.array"],
        "probe_refs": [],
        "forbidden_claims": ["The clock contact alone does not establish rejuvenation."],
        "null_reason": "",
    }
    results = gate_all(
        [
            conjecture,
            overclaim,
            b1_overclaim,
            b3_conjecture,
            bedc_without_structure,
            mixed_none_structure,
            cross_layer_code_only,
            cross_layer_perturbed,
            proxy_objective_overclaim,
            mechanism_without_contact,
            mechanism_layer_matched,
            age_clock_rejuvenation_rephrase,
        ],
        [contact, perturbation_contact, function_contact],
        [b3_probe],
        [],
    )
    by_id = {str(result["packet_id"]): result for result in results}
    invalid_contact_id_cases = {
        "paired_methylation_clock_control": "paired-methylation-clock-control",
        "identity_marker_panel_A": "identity-marker-panel-a",
    }
    for invalid_contact_id, normalized_contact_id in invalid_contact_id_cases.items():
        invalid_contact_results = gate_all(
            [],
            [
                {
                    **contact,
                    "contact_id": invalid_contact_id,
                }
            ],
            [],
            [],
        )
        if not any("not underscores or uppercase" in issue for result in invalid_contact_results for issue in result["issues"]):
            print(json.dumps(invalid_contact_results, indent=2), file=sys.stderr)
            return 1
        if not any(
            issue.startswith(f"contact_id: invalid id: {invalid_contact_id}; ids must match {ID_PATTERN}")
            for result in invalid_contact_results
            for issue in result["issues"]
        ):
            print(json.dumps(invalid_contact_results, indent=2), file=sys.stderr)
            return 1
        if not any(
            f"suggested normalized id: {normalized_contact_id}" in issue
            for result in invalid_contact_results
            for issue in result["issues"]
        ):
            print(json.dumps(invalid_contact_results, indent=2), file=sys.stderr)
            return 1
    recurring_probe_failure_results = gate_all(
        [],
        [
            {**contact, "contact_id": f"fixture.contact.{index}"}
            for index in range(1, 8)
        ]
        + [
                {
                    **contact,
                    "contact_id": "paired_methylation_clock_control",
                }
        ],
        [
            {
                "probe_id": "age-clock-shift-boundary-break-condition",
                "conjecture_ref": "age-clock-shift.boundary.matrix",
                "derived_from": ["bedc_spectrum"],
                "test_statement": "Check whether the age-clock boundary break condition has a bounded reality contact.",
                "support_condition": "A separate curated cell-state contact supports the bounded claim.",
                "break_condition": "The packet lacks the contact or promotes the clock boundary beyond its evidence layer.",
                "forbidden_interpretations": [
                    "Do not infer identity, function, safety, rejuvenation, or immortality from the clock geometry alone."
                ],
            }
        ],
        [],
    )
    recurring_probe_failure = next(
        result
        for result in recurring_probe_failure_results
        if result["packet_id"] == "age-clock-shift-boundary-break-condition"
    )
    recurring_probe_issues = set(recurring_probe_failure["issues"])
    if recurring_probe_failure["gate_status"] != "gate_blocked" or not {
        "missing required field: null_reason",
        "missing required field: probe_kind",
        "missing required field: required_contacts",
    }.issubset(recurring_probe_issues):
        print(json.dumps(recurring_probe_failure_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        issue.startswith("contact_id:8: contact_id: invalid id: paired_methylation_clock_control;")
        and f"suggested normalized id: {invalid_contact_id_cases['paired_methylation_clock_control']}" in issue
        for issue in recurring_probe_failure["issues"]
    ):
        print(json.dumps(recurring_probe_failure_results, indent=2), file=sys.stderr)
        return 1
    event_mismatch_failure_results = gate_all(
        [],
        [
            {**contact, "contact_id": f"fixture.contact.{index}"}
            for index in range(1, 8)
        ]
        + [
                {
                    **contact,
                    "contact_id": "paired_methylation_clock_control",
                }
        ],
        [],
        [
            {
                "mismatch_id": "curated.clock-table.cross-cellstate-id-shape-boundary",
                "probe_ref": "fixture.probe",
                "contact_ref": "fixture.contact.1",
                "status": "underdetermined",
                "mismatch_kind": "missing_context",
                "observed_delta": "The packet carries an invalid indexed contact id.",
                "refinement_pressure": "Normalize the reality contact id before review.",
                "blocked_claims": ["Do not review a mismatch against an invalid contact table."],
                "null_reason": "",
            }
        ],
    )
    event_mismatch_failure = next(
        result
        for result in event_mismatch_failure_results
        if result["packet_id"] == "curated.clock-table.cross-cellstate-id-shape-boundary"
    )
    if event_mismatch_failure["gate_status"] != "gate_blocked" or not any(
        issue.startswith("contact_id:8: contact_id: invalid id: paired_methylation_clock_control;")
        and f"suggested normalized id: {invalid_contact_id_cases['paired_methylation_clock_control']}" in issue
        for issue in event_mismatch_failure["issues"]
    ):
        print(json.dumps(event_mismatch_failure_results, indent=2), file=sys.stderr)
        return 1
    scalar_test_scope_results = gate_all(
        [],
        [
            {
                **contact,
                "contact_id": "paired-methylation-clock-control",
                "can_test": "age_signature layer",
                "cannot_test": "cell identity",
            }
        ],
        [],
        [],
    )
    scalar_test_scope = next(
        result for result in scalar_test_scope_results if result["packet_id"] == "paired-methylation-clock-control"
    )
    if scalar_test_scope["gate_status"] != "gate_blocked" or not {
        "can_test must be an array",
        "cannot_test must be an array",
    }.issubset(set(scalar_test_scope["issues"])):
        print(json.dumps(scalar_test_scope_results, indent=2), file=sys.stderr)
        return 1
    invalid_contact_scalar_scope_results = gate_all(
        [],
        [
            {
                **contact,
                "contact_id": "paired_methylation_clock_control",
                "can_test": "age_signature layer",
                "cannot_test": "cell identity",
            }
        ],
        [],
        [],
    )
    invalid_contact_scalar_scope = next(
        result
        for result in invalid_contact_scalar_scope_results
        if result["packet_id"] == "paired_methylation_clock_control"
    )
    if invalid_contact_scalar_scope["gate_status"] != "gate_blocked" or not {
        "can_test must be an array",
        "cannot_test must be an array",
    }.issubset(set(invalid_contact_scalar_scope["issues"])):
        print(json.dumps(invalid_contact_scalar_scope_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        f"contact_id: invalid id: paired_methylation_clock_control" in issue
        for issue in invalid_contact_scalar_scope["issues"]
    ):
        print(json.dumps(invalid_contact_scalar_scope_results, indent=2), file=sys.stderr)
        return 1
    invalid_contact_id = "paired_methylation_clock_control"
    normalized_contact_id = invalid_contact_id_cases[invalid_contact_id]
    invalid_contact_mismatch_results = gate_all(
        [],
        [
            {
                **contact,
                "contact_id": invalid_contact_id,
            }
        ],
        [],
        [
            {
                "mismatch_id": "age-clock-shift.identity-boundary.no-promotion.scope-review",
                "probe_ref": "identity.boundary.probe.overreach",
                "contact_ref": invalid_contact_id,
                "status": "underdetermined",
                "mismatch_kind": "missing_context",
                "observed_delta": "The packet cites an invalid contact id.",
                "refinement_pressure": "Normalize the contact id before review.",
                "blocked_claims": ["Do not review a mismatch against an invalid reality contact id."],
                "null_reason": "",
            }
        ],
    )
    invalid_contact_mismatch = next(
        result
        for result in invalid_contact_mismatch_results
        if result["packet_id"] == "age-clock-shift.identity-boundary.no-promotion.scope-review"
    )
    if invalid_contact_mismatch["gate_status"] != "gate_blocked" or not any(
        f"contact_id: invalid id: {invalid_contact_id}" in issue
        and f"suggested normalized id: {normalized_contact_id}" in issue
        for issue in invalid_contact_mismatch["issues"]
    ):
        print(json.dumps(invalid_contact_mismatch_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        f"contact_ref: invalid id: {invalid_contact_id}" in issue
        and f"suggested normalized id: {normalized_contact_id}" in issue
        for issue in invalid_contact_mismatch["issues"]
    ):
        print(json.dumps(invalid_contact_mismatch_results, indent=2), file=sys.stderr)
        return 1
    if any(f"contact_ref not found: {invalid_contact_id}" in issue for issue in invalid_contact_mismatch["issues"]):
        print(json.dumps(invalid_contact_mismatch_results, indent=2), file=sys.stderr)
        return 1
    invalid_probe_ref_id = "identity_marker_multi_context_extension"
    normalized_probe_ref_id = "identity-marker-multi-context-extension"
    invalid_probe_ref_mismatch_results = gate_all(
        [],
        [contact],
        [],
        [
            {
                "mismatch_id": "identity-marker-multi-context-extension.contact-gap",
                "probe_ref": invalid_probe_ref_id,
                "contact_ref": "clock.horvath.array",
                "status": "underdetermined",
                "mismatch_kind": "missing_context",
                "observed_delta": "The packet cites an invalid probe id.",
                "refinement_pressure": "Normalize the probe id before review.",
                "blocked_claims": ["Do not review a mismatch against an invalid probe id."],
                "null_reason": "",
            }
        ],
    )
    invalid_probe_ref_mismatch = next(
        result
        for result in invalid_probe_ref_mismatch_results
        if result["packet_id"] == "identity-marker-multi-context-extension.contact-gap"
    )
    if invalid_probe_ref_mismatch["gate_status"] != "gate_blocked" or not any(
        f"probe_ref: invalid id: {invalid_probe_ref_id}" in issue
        and f"suggested normalized id: {normalized_probe_ref_id}" in issue
        for issue in invalid_probe_ref_mismatch["issues"]
    ):
        print(json.dumps(invalid_probe_ref_mismatch_results, indent=2), file=sys.stderr)
        return 1
    if any(f"probe_ref not found: {invalid_probe_ref_id}" in issue for issue in invalid_probe_ref_mismatch["issues"]):
        print(json.dumps(invalid_probe_ref_mismatch_results, indent=2), file=sys.stderr)
        return 1
    missing_probe_scope_review_results = gate_all(
        [],
        [contact],
        [],
        [
            {
                "mismatch_id": "rejuvenation-candidate.same-scope-function-contact.scope-review",
                "probe_ref": "rejuvenation-candidate.same-scope-function-contact",
                "contact_ref": "clock.horvath.array",
                "status": "blocked_null",
                "mismatch_kind": "missing_context",
                "observed_delta": "The scope-review packet cites a probe that is not present.",
                "refinement_pressure": "Create the probe packet before mismatch review.",
                "blocked_claims": ["Do not review a scope boundary without its probe packet."],
                "null_reason": "",
            },
            {
                "mismatch_id": "identity-preserving-age-reset.same-scope-identity-contact.scope-review",
                "probe_ref": "identity-preserving-age-reset.same-scope-identity-contact",
                "contact_ref": "clock.horvath.array",
                "status": "blocked_null",
                "mismatch_kind": "missing_context",
                "observed_delta": "The scope-review packet cites a same-scope identity-contact probe that is not present.",
                "refinement_pressure": "Create the identity-contact probe packet before mismatch review.",
                "blocked_claims": ["Do not review identity-contact scope without its probe packet."],
                "null_reason": "",
            }
        ],
    )
    missing_probe_scope_review = next(
        result
        for result in missing_probe_scope_review_results
        if result["packet_id"] == "rejuvenation-candidate.same-scope-function-contact.scope-review"
    )
    if missing_probe_scope_review["gate_status"] != "gate_blocked" or not any(
        issue
        == (
            "scope_review_requires_existing_probe: rejuvenation-candidate.same-scope-function-contact.scope-review "
            "cannot be reviewed until probe_ref rejuvenation-candidate.same-scope-function-contact exists"
        )
        for issue in missing_probe_scope_review["issues"]
    ):
        print(json.dumps(missing_probe_scope_review_results, indent=2), file=sys.stderr)
        return 1
    identity_contact_scope_review = next(
        result
        for result in missing_probe_scope_review_results
        if result["packet_id"] == "identity-preserving-age-reset.same-scope-identity-contact.scope-review"
    )
    if identity_contact_scope_review["gate_status"] != "gate_blocked" or not any(
        issue
        == (
            "scope_review_requires_existing_probe: "
            "identity-preserving-age-reset.same-scope-identity-contact.scope-review "
            "cannot be reviewed until probe_ref identity-preserving-age-reset.same-scope-identity-contact exists"
        )
        for issue in identity_contact_scope_review["issues"]
    ):
        print(json.dumps(missing_probe_scope_review_results, indent=2), file=sys.stderr)
        return 1
    invalid_required_contact_results = gate_all(
        [conjecture],
        [contact],
        [
            {
                **b3_probe,
                "required_contacts": [invalid_contact_id],
                "conjecture_ref": "age-clock-shift.clock.read",
            }
        ],
        [],
    )
    if not any(
        "required_contacts item: invalid id" in issue
        and f"suggested normalized id: {normalized_contact_id}" in issue
        for result in invalid_required_contact_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_required_contact_results, indent=2), file=sys.stderr)
        return 1
    if any(
        f"required contact not found: {invalid_contact_id}" in issue
        for result in invalid_required_contact_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_required_contact_results, indent=2), file=sys.stderr)
        return 1
    invalid_conjecture_contact_ref_results = gate_all(
        [
            {
                **conjecture,
                "conjecture_id": "age-clock-shift.invalid-contact-ref",
                "reality_contact_refs": [invalid_contact_id],
            }
        ],
        [contact],
        [],
        [],
    )
    if not any(
        "reality_contact_refs item: invalid id" in issue
        and f"suggested normalized id: {normalized_contact_id}" in issue
        for result in invalid_conjecture_contact_ref_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_contact_ref_results, indent=2), file=sys.stderr)
        return 1
    if any(
        f"reality contact not found: {invalid_contact_id}" in issue
        for result in invalid_conjecture_contact_ref_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_contact_ref_results, indent=2), file=sys.stderr)
        return 1
    invalid_conjecture_probe_ref_results = gate_all(
        [
            {
                **conjecture,
                "conjecture_id": "age-clock-shift.invalid-probe-ref",
                "evidence_basis": ["derived_probe"],
                "probe_refs": [invalid_probe_ref_id],
            }
        ],
        [contact],
        [],
        [],
    )
    if not any(
        "probe_refs item: invalid id" in issue
        and f"suggested normalized id: {normalized_probe_ref_id}" in issue
        for result in invalid_conjecture_probe_ref_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_probe_ref_results, indent=2), file=sys.stderr)
        return 1
    if any(
        issue == f"probe not found: {invalid_probe_ref_id}"
        for result in invalid_conjecture_probe_ref_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_probe_ref_results, indent=2), file=sys.stderr)
        return 1
    invalid_conjecture_id = "cross_context.identity_marker_gate.cell_identity"
    normalized_conjecture_id = "cross-context.identity-marker-gate.cell-identity"
    invalid_conjecture_id_results = gate_all(
        [
            {**conjecture, "conjecture_id": "fixture.conjecture.1"},
            {**conjecture, "conjecture_id": invalid_conjecture_id},
        ],
        [contact],
        [],
        [],
    )
    if not any(
        issue.startswith(f"conjecture_id:2: conjecture_id: invalid id: {invalid_conjecture_id};")
        and f"suggested normalized id: {normalized_conjecture_id}" in issue
        for result in invalid_conjecture_id_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_id_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        issue.startswith(f"conjecture_id: invalid id: {invalid_conjecture_id};")
        and f"suggested normalized id: {normalized_conjecture_id}" in issue
        for result in invalid_conjecture_id_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_conjecture_id_results, indent=2), file=sys.stderr)
        return 1
    mixed_invalid_id_results = gate_all(
        [
            {**conjecture, "conjecture_id": "fixture.conjecture.1"},
            {**conjecture, "conjecture_id": "genome_source.seed.boundary"},
            {
                **conjecture,
                "conjecture_id": "cross_context.identity_marker_gate.cell_identity",
            },
            {
                **conjecture,
                "conjecture_id": "residual_basis.clock_topology_after_age_signature.cell_identity",
            },
            {
                **conjecture,
                "conjecture_id": "function_realization.seed.boundary",
            },
        ],
        [
            {**contact, "contact_id": "fixture.contact.1"},
            {**contact, "contact_id": "fixture.contact.2"},
            {**contact, "contact_id": "clock_shift_per_context"},
            {**contact, "contact_id": "fixture.contact.4"},
            {**contact, "contact_id": "fixture.contact.5"},
            {**contact, "contact_id": "rna_expression_identity_panel"},
        ],
        [
            {**b3_probe, "probe_id": f"fixture.probe.{index}", "conjecture_ref": "fixture.conjecture.1"}
            for index in range(1, 5)
        ]
        + [
            {
                **b3_probe,
                "probe_id": "cross_context.identity_marker_signal_correlates_with_clock_shift",
                "conjecture_ref": "fixture.conjecture.1",
            },
            {
                **b3_probe,
                "probe_id": "residual_basis.clock_only_local_optimum_insufficiency",
                "conjecture_ref": "fixture.conjecture.1",
            },
            {
                **b3_probe,
                "probe_id": "cross_context.identity_boundary.no_promotion",
                "conjecture_ref": "fixture.conjecture.1",
            },
            {
                **b3_probe,
                "probe_id": "residual_basis.clock_readout_boundary.no_promotion",
                "conjecture_ref": "fixture.conjecture.1",
            },
            {
                **b3_probe,
                "probe_id": "age_clock_shift_matrix_break_condition",
                "conjecture_ref": "fixture.conjecture.1",
            },
            {
                **b3_probe,
                "probe_id": "identity_marker_multi_context_extension",
                "conjecture_ref": "fixture.conjecture.1",
            },
        ],
        [],
    )
    mixed_invalid_id_expectations = {
        "contact_id:3": ("clock_shift_per_context", "clock-shift-per-context"),
        "contact_id:6": ("rna_expression_identity_panel", "rna-expression-identity-panel"),
        "conjecture_id:2": ("genome_source.seed.boundary", "genome-source.seed.boundary"),
        "conjecture_id:3": (
            "cross_context.identity_marker_gate.cell_identity",
            "cross-context.identity-marker-gate.cell-identity",
        ),
        "conjecture_id:4": (
            "residual_basis.clock_topology_after_age_signature.cell_identity",
            "residual-basis.clock-topology-after-age-signature.cell-identity",
        ),
        "conjecture_id:5": (
            "function_realization.seed.boundary",
            "function-realization.seed.boundary",
        ),
        "probe_id:5": (
            "cross_context.identity_marker_signal_correlates_with_clock_shift",
            "cross-context.identity-marker-signal-correlates-with-clock-shift",
        ),
        "probe_id:6": (
            "residual_basis.clock_only_local_optimum_insufficiency",
            "residual-basis.clock-only-local-optimum-insufficiency",
        ),
        "probe_id:7": (
            "cross_context.identity_boundary.no_promotion",
            "cross-context.identity-boundary.no-promotion",
        ),
        "probe_id:8": (
            "residual_basis.clock_readout_boundary.no_promotion",
            "residual-basis.clock-readout-boundary.no-promotion",
        ),
        "probe_id:9": ("age_clock_shift_matrix_break_condition", "age-clock-shift-matrix-break-condition"),
        "probe_id:10": ("identity_marker_multi_context_extension", "identity-marker-multi-context-extension"),
    }
    mixed_invalid_id_issues = [issue for result in mixed_invalid_id_results for issue in result["issues"]]
    for prefix, (invalid_id, normalized_id) in mixed_invalid_id_expectations.items():
        if not any(
            issue.startswith(f"{prefix}: {prefix.split(':', 1)[0]}: invalid id: {invalid_id};")
            and f"suggested normalized id: {normalized_id}" in issue
            for issue in mixed_invalid_id_issues
        ):
            print(json.dumps(mixed_invalid_id_results, indent=2), file=sys.stderr)
            return 1
    if not any(
        issue.startswith("conjecture_id:5: conjecture_id: invalid id: function_realization.seed.boundary;")
        and "layer tokens embedded in ids must be hyphenated (function_realization->function-realization)" in issue
        and "keep underscores in layer fields" in issue
        for issue in mixed_invalid_id_issues
    ):
        print(json.dumps(mixed_invalid_id_results, indent=2), file=sys.stderr)
        return 1
    function_realization_seed_boundary_results = gate_all(
        [
            {
                **conjecture,
                "conjecture_id": "function_realization.seed.boundary",
                "biological_object": "FunctionRealizationSeedBoundaryUp",
                "informal_statement": "The BEDC coordinate realizes bounded function realization.",
                "bedc_minimal_form": {
                    "carrier": "function boundary seed",
                    "distinctions": ["seed boundary"],
                    "readback": "coordinate readback",
                    "internal_structure": [],
                },
                "claimed_layer": "function_realization",
                "evidence_basis": ["bedc_coordinate"],
                "reality_contact_refs": [],
                "probe_refs": [],
                "forbidden_claims": ["BEDC coordinate evidence alone is not function realization."],
            }
        ],
        [],
        [],
        [],
    )
    function_realization_seed_boundary_issues = [
        issue for result in function_realization_seed_boundary_results for issue in result["issues"]
    ]
    if not any(
        issue.startswith("conjecture_id: invalid id: function_realization.seed.boundary;")
        and "suggested normalized id: function-realization.seed.boundary" in issue
        for issue in function_realization_seed_boundary_issues
    ):
        print(json.dumps(function_realization_seed_boundary_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        issue.startswith("conjecture_id:1: conjecture_id: invalid id: function_realization.seed.boundary;")
        and "suggested normalized id: function-realization.seed.boundary" in issue
        for issue in function_realization_seed_boundary_issues
    ):
        print(json.dumps(function_realization_seed_boundary_results, indent=2), file=sys.stderr)
        return 1
    if "BEDC evidence requires explicit internal structure" not in function_realization_seed_boundary_issues:
        print(json.dumps(function_realization_seed_boundary_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        issue
        == (
            "mechanism_closure_requires_separate_contact: mechanism/realization wording requires "
            "a layer-matched reality contact whose can_test includes function_realization"
        )
        for issue in function_realization_seed_boundary_issues
    ):
        print(json.dumps(function_realization_seed_boundary_results, indent=2), file=sys.stderr)
        return 1
    contact_schema = json.loads((SCRIPT_DIR / "reality_contact.schema.json").read_text(encoding="utf-8"))
    contact_id_pattern = contact_schema.get("properties", {}).get("contact_id", {}).get("pattern")
    if contact_id_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "reality_contact.schema.json",
                    "field": "contact_id",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": contact_id_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    contact_schema_properties = contact_schema.get("properties", {})
    for scope_field in ("can_test", "cannot_test"):
        scope_schema = contact_schema_properties.get(scope_field, {})
        if scope_schema.get("type") != "array" or scope_schema.get("minItems") != 1:
            print(
                json.dumps(
                    {
                        "schema": "reality_contact.schema.json",
                        "field": scope_field,
                        "expected_type": "array",
                        "expected_minItems": 1,
                        "actual_type": scope_schema.get("type"),
                        "actual_minItems": scope_schema.get("minItems"),
                    },
                    indent=2,
                ),
                file=sys.stderr,
            )
            return 1
    conjecture_schema = json.loads((SCRIPT_DIR / "conjecture.schema.json").read_text(encoding="utf-8"))
    conjecture_id_pattern = conjecture_schema.get("properties", {}).get("conjecture_id", {}).get("pattern")
    if conjecture_id_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "conjecture.schema.json",
                    "field": "conjecture_id",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": conjecture_id_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    conjecture_contact_ref_pattern = (
        conjecture_schema.get("properties", {}).get("reality_contact_refs", {}).get("items", {}).get("pattern")
    )
    if conjecture_contact_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "conjecture.schema.json",
                    "field": "reality_contact_refs.items",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": conjecture_contact_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    conjecture_probe_ref_pattern = (
        conjecture_schema.get("properties", {}).get("probe_refs", {}).get("items", {}).get("pattern")
    )
    if conjecture_probe_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "conjecture.schema.json",
                    "field": "probe_refs.items",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": conjecture_probe_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    probe_schema = json.loads((SCRIPT_DIR / "probe.schema.json").read_text(encoding="utf-8"))
    probe_id_pattern = probe_schema.get("properties", {}).get("probe_id", {}).get("pattern")
    if probe_id_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "probe_id",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": probe_id_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    probe_conjecture_ref_pattern = probe_schema.get("properties", {}).get("conjecture_ref", {}).get("pattern")
    if probe_conjecture_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "conjecture_ref",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": probe_conjecture_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    probe_required_contact_pattern = (
        probe_schema.get("properties", {}).get("required_contacts", {}).get("items", {}).get("pattern")
    )
    if probe_required_contact_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "required_contacts.items",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": probe_required_contact_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    mismatch_schema = json.loads((SCRIPT_DIR / "mismatch.schema.json").read_text(encoding="utf-8"))
    mismatch_id_pattern = mismatch_schema.get("properties", {}).get("mismatch_id", {}).get("pattern")
    if mismatch_id_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "mismatch.schema.json",
                    "field": "mismatch_id",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": mismatch_id_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    mismatch_probe_ref_pattern = mismatch_schema.get("properties", {}).get("probe_ref", {}).get("pattern")
    if mismatch_probe_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "mismatch.schema.json",
                    "field": "probe_ref",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": mismatch_probe_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    mismatch_contact_ref_pattern = mismatch_schema.get("properties", {}).get("contact_ref", {}).get("pattern")
    if mismatch_contact_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "mismatch.schema.json",
                    "field": "contact_ref",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": mismatch_contact_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    invalid_probe_results = gate_all(
        [conjecture],
        [contact],
        [
            {
                **b3_probe,
                "probe_id": "cross_context.identity_marker_signal_correlates_with_RNASeq",
                "conjecture_ref": "age-clock-shift.clock.read",
            }
        ],
        [],
    )
    if not any("not underscores or uppercase" in issue for result in invalid_probe_results for issue in result["issues"]):
        print(json.dumps(invalid_probe_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        issue.startswith(
            f"probe_id:1: probe_id: invalid id: cross_context.identity_marker_signal_correlates_with_RNASeq; "
            f"ids must match {ID_PATTERN}"
        )
        for result in invalid_probe_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_probe_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        "suggested normalized id: cross-context.identity-marker-signal-correlates-with-rnaseq" in issue
        for result in invalid_probe_results
        for issue in result["issues"]
    ):
        print(json.dumps(invalid_probe_results, indent=2), file=sys.stderr)
        return 1
    indexed_invalid_probe_results = gate_all(
        [conjecture],
        [contact],
        [
            {
                **b3_probe,
                "probe_id": f"fixture.probe.{index}",
                "conjecture_ref": "age-clock-shift.clock.read",
            }
            for index in range(1, 5)
        ]
        + [
            {
                **b3_probe,
                "probe_id": "cross_context.identity_marker_signal_correlates_with_RNASeq",
                "conjecture_ref": "age-clock-shift.clock.read",
            }
        ],
        [],
    )
    if not any(
        issue.startswith(
            f"probe_id:5: probe_id: invalid id: cross_context.identity_marker_signal_correlates_with_RNASeq; "
            f"ids must match {ID_PATTERN}"
        )
        for result in indexed_invalid_probe_results
        for issue in result["issues"]
    ):
        print(json.dumps(indexed_invalid_probe_results, indent=2), file=sys.stderr)
        return 1
    if not any(
        "suggested normalized id: cross-context.identity-marker-signal-correlates-with-rnaseq" in issue
        for result in indexed_invalid_probe_results
        for issue in result["issues"]
    ):
        print(json.dumps(indexed_invalid_probe_results, indent=2), file=sys.stderr)
        return 1
    probe_schema = json.loads((SCRIPT_DIR / "probe.schema.json").read_text(encoding="utf-8"))
    probe_schema_required = set(probe_schema.get("required", []))
    if probe_schema_required != PROBE_REQUIRED_FIELDS:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "expected_required": sorted(PROBE_REQUIRED_FIELDS),
                    "actual_required": sorted(probe_schema_required),
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    probe_id_pattern = probe_schema.get("properties", {}).get("probe_id", {}).get("pattern")
    if probe_id_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "probe_id",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": probe_id_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    conjecture_ref_pattern = probe_schema.get("properties", {}).get("conjecture_ref", {}).get("pattern")
    if conjecture_ref_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "conjecture_ref",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": conjecture_ref_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    required_contacts_pattern = probe_schema.get("properties", {}).get("required_contacts", {}).get("items", {}).get("pattern")
    if required_contacts_pattern != ID_PATTERN:
        print(
            json.dumps(
                {
                    "schema": "probe.schema.json",
                    "field": "required_contacts.items",
                    "expected_pattern": ID_PATTERN,
                    "actual_pattern": required_contacts_pattern,
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 1
    if by_id["age-clock-shift.clock.read"]["gate_status"] != "gate_passed":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["cellstate.world.model"]["gate_status"] != "gate_blocked":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["identity.overclaim"]["gate_status"] != "gate_blocked" or not any(
        "in cannot_test" in issue for issue in by_id["identity.overclaim"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["identity.boundary.probe.overreach"]["gate_status"] != "gate_blocked" or not any(
        "structural probe_kind" in issue for issue in by_id["identity.boundary.probe.overreach"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["bedc.structure.missing"]["gate_status"] != "gate_blocked" or not any(
        "BEDC evidence requires explicit internal structure" in issue for issue in by_id["bedc.structure.missing"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["bedc.structure.mixed"]["gate_status"] != "gate_blocked" or not any(
        "cannot mix none" in issue for issue in by_id["bedc.structure.mixed"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["cross.layer.clock.only"]["gate_status"] != "gate_blocked" or not any(
        "is not addressed by any attached reality contact" in issue for issue in by_id["cross.layer.clock.only"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["cross.layer.perturbed"]["gate_status"] != "gate_passed":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["proxy.objective.overclaim"]["gate_status"] != "gate_blocked" or not any(
        issue.startswith("proxy_objective_separation:")
        for issue in by_id["proxy.objective.overclaim"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["mechanism.contact.missing"]["gate_status"] != "gate_blocked" or not any(
        issue.startswith("mechanism_closure_requires_separate_contact:")
        for issue in by_id["mechanism.contact.missing"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["mechanism.layer.matched"]["gate_status"] != "gate_passed":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["age.clock.rejuvenation.rephrase"]["gate_status"] != "gate_blocked" or not any(
        issue.startswith("age_clock_promotion_requires_separate_contact:functional_repair_or_rejuvenation:")
        for issue in by_id["age.clock.rejuvenation.rephrase"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    print("[cellstate-reality-gates] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run CellStateReality deepening gates")
    parser.add_argument("--conjectures", default=str(DEFAULT_CONJECTURES), help="conjecture JSONL")
    parser.add_argument("--contacts", default=str(DEFAULT_CONTACTS), help="reality contact JSONL")
    parser.add_argument("--probes", default=str(DEFAULT_PROBES), help="probe JSONL")
    parser.add_argument("--mismatches", default=str(DEFAULT_MISMATCHES), help="mismatch JSONL")
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="gate result JSONL")
    parser.add_argument("--allow-empty", action="store_true", help="allow no input packets")
    parser.add_argument("--self-test", action="store_true", help="run built-in fixture")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    try:
        conjectures = read_jsonl(Path(args.conjectures))
        contacts = read_jsonl(Path(args.contacts))
        probes = read_jsonl(Path(args.probes))
        mismatches = read_jsonl(Path(args.mismatches))
        if not args.allow_empty and not any((conjectures, contacts, probes, mismatches)):
            print("[cellstate-reality-gates] no input packets", file=sys.stderr)
            return 1
        results = gate_all(conjectures, contacts, probes, mismatches)
        write_jsonl(Path(args.output), results)
    except Exception as exc:
        print(f"[cellstate-reality-gates] error: {exc}", file=sys.stderr)
        return 1

    blocked = sum(1 for result in results if result["gate_status"] == "gate_blocked")
    passed = len(results) - blocked
    print(f"[cellstate-reality-gates] wrote {len(results)} result(s) to {args.output}; passed={passed} blocked={blocked}")
    return 0 if blocked == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())

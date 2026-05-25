#!/usr/bin/env python3
"""Deterministic gates for biological conjecture deepening packets."""

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

ID_RE = re.compile(r"^[a-z0-9][a-z0-9._:-]*$")

LAYERS = {
    "code_read",
    "orf_eligibility",
    "translation_realization",
    "structural_order",
    "physical_admissibility",
    "function_realization",
    "system_phenotype",
    "cross_layer_relation",
}
EVIDENCE_BASIS = {
    "external_reality",
    "bedc_coordinate",
    "bedc_closure",
    "bedc_spectrum",
    "derived_probe",
    "mismatch_ledger",
    "mechanism_bridge",
}
CONTACT_KINDS = {
    "genetic_code_table",
    "sequence_database",
    "transcript_evidence",
    "protein_measurement",
    "structure_experiment",
    "structure_prediction",
    "physical_assay",
    "functional_assay",
    "phenotype_assay",
    "curated_annotation",
    "manual_observation",
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
TOTAL_BIOLOGY_WORDS = {
    "full biology",
    "all biology",
    "general biological model",
    "total biology",
}


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
        issues.append(f"{key} must match ^[a-z0-9][a-z0-9._:-]*$")


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
    required = {
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
    issues = _missing(record, required)
    if issues:
        return issues
    _id("probe_id", record.get("probe_id"), issues)
    _id("conjecture_ref", record.get("conjecture_ref"), issues)
    conjecture = conjecture_by_id.get(str(record.get("conjecture_ref") or ""))
    if conjecture is None:
        issues.append(f"conjecture_ref not found: {record.get('conjecture_ref')}")
    if record.get("probe_kind") not in PROBE_KINDS:
        issues.append("probe_kind is not recognized")
    _array("derived_from", record.get("derived_from"), issues, allowed=DERIVED_FROM, min_items=1)
    for key in ("test_statement", "support_condition", "break_condition"):
        _nonempty(key, record.get(key), issues)
    contacts = _array("required_contacts", record.get("required_contacts"), issues)
    for contact in contacts:
        if not ID_RE.match(contact):
            issues.append(f"required_contacts contains invalid id: {contact}")
        if contact not in contact_ids:
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
            claimed_layer not in {"code_read", "orf_eligibility"}
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
    if record.get("probe_ref") not in probe_ids:
        issues.append(f"probe_ref not found: {record.get('probe_ref')}")
    if record.get("contact_ref") not in contact_ids:
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
        if not ID_RE.match(contact):
            issues.append(f"reality_contact_refs contains invalid id: {contact}")
        if contact not in contact_by_id:
            issues.append(f"reality contact not found: {contact}")
    for probe in probes:
        if not ID_RE.match(probe):
            issues.append(f"probe_refs contains invalid id: {probe}")
        if probe not in probe_ids:
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
    if isinstance(form, dict):
        text_parts.extend([str(form.get("readback", "")), str(form.get("carrier", ""))])
    text = " ".join(text_parts)
    if "external_reality" in evidence and not contacts:
        issues.append("external_reality evidence requires reality_contact_refs")
    if "derived_probe" in evidence and not probes:
        issues.append("derived_probe evidence requires probe_refs")
    if contacts:
        claimed_layer = record.get("claimed_layer")
        normalized_layer = _normalize_layer_text(claimed_layer)
        can_test: list[str] = []
        cannot_test: list[str] = []
        for contact_ref in contacts:
            contact_record = contact_by_id.get(contact_ref)
            if contact_record is None:
                continue
            can_test.extend(str(item) for item in contact_record.get("can_test", []) if isinstance(item, str))
            cannot_test.extend(str(item) for item in contact_record.get("cannot_test", []) if isinstance(item, str))
        layer_in_can_test = any(normalized_layer == _normalize_layer_text(item) or normalized_layer in _normalize_layer_text(item) for item in can_test)
        layer_in_cannot_test = any(
            normalized_layer == _normalize_layer_text(item) or normalized_layer in _normalize_layer_text(item)
            for item in cannot_test
        )
        if not layer_in_can_test and layer_in_cannot_test:
            issues.append(
                f"claimed_layer {claimed_layer} is in cannot_test of all attached contacts; promote requires "
                f"a separate reality contact that can_test layer {claimed_layer}"
            )
        elif not layer_in_can_test and not layer_in_cannot_test:
            issues.append(f"claimed_layer {claimed_layer} is not addressed by any attached reality contact")
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
            issues.append(f"{key}:{index}: invalid id: {value}")
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
        "contact_id": "ncbi.standard.code",
        "source_kind": "genetic_code_table",
        "source_ref": "NCBI translation table",
        "source_snapshot": "fixture",
        "observed_fact": "A curated table maps codons to amino-acid or stop labels.",
        "resolution": "codon assignment",
        "known_noise_or_bias": "fixture only",
        "can_test": ["code_read layer"],
        "cannot_test": ["protein realization", "biological function", "function realization"],
        "null_reason": "",
    }
    conjecture = {
        "conjecture_id": "codon.code.read",
        "biological_object": "codon table",
        "informal_statement": "Codon assignment can be read as a code-layer reality contact.",
        "bedc_minimal_form": {
            "carrier": "codon stream",
            "distinctions": ["codon label", "stop label"],
            "readback": "named genetic-code table",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "code_read",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["ncbi.standard.code"],
        "probe_refs": [],
        "forbidden_claims": ["Codon assignment alone is not protein realization."],
        "null_reason": "",
    }
    overclaim = {
        "conjecture_id": "protein.world.model",
        "biological_object": "DNA to protein",
        "informal_statement": "This is a full biology explanation for DNA-to-protein function.",
        "bedc_minimal_form": {
            "carrier": "sequence",
            "distinctions": ["base"],
            "readback": "sequence",
            "internal_structure": ["none"],
        },
        "claimed_layer": "function_realization",
        "evidence_basis": ["external_reality"],
        "reality_contact_refs": ["ncbi.standard.code"],
        "probe_refs": [],
        "forbidden_claims": ["No forbidden claim."],
        "null_reason": "",
    }
    b1_overclaim = {
        "conjecture_id": "function.overclaim",
        "biological_object": "gene product",
        "informal_statement": "The coordinate is presented as a function-layer packet.",
        "bedc_minimal_form": {
            "carrier": "annotated sequence",
            "distinctions": ["label"],
            "readback": "sequence annotation",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "function_realization",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["ncbi.standard.code"],
        "probe_refs": [],
        "forbidden_claims": ["The code table alone does not establish biological function."],
        "null_reason": "",
    }
    b3_conjecture = {
        "conjecture_id": "structure.probe.overreach",
        "biological_object": "gene product",
        "informal_statement": "The packet is placed at the function layer.",
        "bedc_minimal_form": {
            "carrier": "annotated sequence",
            "distinctions": ["label"],
            "readback": "sequence annotation",
            "internal_structure": ["coordinate"],
        },
        "claimed_layer": "function_realization",
        "evidence_basis": ["external_reality", "bedc_coordinate"],
        "reality_contact_refs": ["ncbi.standard.code"],
        "probe_refs": ["boundary.probe.overreach"],
        "forbidden_claims": ["The structural probe is not a functional assay."],
        "null_reason": "",
    }
    b3_probe = {
        "probe_id": "boundary.probe.overreach",
        "conjecture_ref": "structure.probe.overreach",
        "probe_kind": "boundary_mismatch",
        "derived_from": ["bedc_coordinate"],
        "test_statement": "Check whether a coordinate boundary mismatches the readback.",
        "support_condition": "The boundary is stable under the finite reading.",
        "break_condition": "The boundary does not survive contact with the readback.",
        "required_contacts": ["ncbi.standard.code"],
        "forbidden_interpretations": ["The boundary alone proves function."],
        "null_reason": "",
    }
    bedc_without_structure = {
        "conjecture_id": "bedc.structure.missing",
        "biological_object": "codon window",
        "informal_statement": "The packet has BEDC coordinate evidence but no internal structure.",
        "bedc_minimal_form": {
            "carrier": "codon window",
            "distinctions": ["window boundary"],
            "readback": "window enumeration",
            "internal_structure": [],
        },
        "claimed_layer": "orf_eligibility",
        "evidence_basis": ["bedc_coordinate"],
        "reality_contact_refs": [],
        "probe_refs": [],
        "forbidden_claims": ["Coordinate evidence alone is not translation realization."],
        "null_reason": "",
    }
    mixed_none_structure = {
        "conjecture_id": "bedc.structure.mixed",
        "biological_object": "codon window",
        "informal_statement": "The packet mixes no internal structure with an explicit coordinate.",
        "bedc_minimal_form": {
            "carrier": "codon window",
            "distinctions": ["window boundary"],
            "readback": "window enumeration",
            "internal_structure": ["none", "coordinate"],
        },
        "claimed_layer": "orf_eligibility",
        "evidence_basis": ["bedc_coordinate"],
        "reality_contact_refs": [],
        "probe_refs": [],
        "forbidden_claims": ["Coordinate evidence alone is not translation realization."],
        "null_reason": "",
    }
    results = gate_all(
        [conjecture, overclaim, b1_overclaim, b3_conjecture, bedc_without_structure, mixed_none_structure],
        [contact],
        [b3_probe],
        [],
    )
    by_id = {str(result["packet_id"]): result for result in results}
    if by_id["codon.code.read"]["gate_status"] != "gate_passed":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["protein.world.model"]["gate_status"] != "gate_blocked":
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["function.overclaim"]["gate_status"] != "gate_blocked" or not any(
        "in cannot_test" in issue for issue in by_id["function.overclaim"]["issues"]
    ):
        print(json.dumps(results, indent=2), file=sys.stderr)
        return 1
    if by_id["boundary.probe.overreach"]["gate_status"] != "gate_blocked" or not any(
        "structural probe_kind" in issue for issue in by_id["boundary.probe.overreach"]["issues"]
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
    print("[bio-reality-gates] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run BioReality deepening gates")
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
            print("[bio-reality-gates] no input packets", file=sys.stderr)
            return 1
        results = gate_all(conjectures, contacts, probes, mismatches)
        write_jsonl(Path(args.output), results)
    except Exception as exc:
        print(f"[bio-reality-gates] error: {exc}", file=sys.stderr)
        return 1

    blocked = sum(1 for result in results if result["gate_status"] == "gate_blocked")
    passed = len(results) - blocked
    print(f"[bio-reality-gates] wrote {len(results)} result(s) to {args.output}; passed={passed} blocked={blocked}")
    return 0 if blocked == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())

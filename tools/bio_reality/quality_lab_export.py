#!/usr/bin/env python3
"""Compile BioReality runtime packets into quality-lab durable exports."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent

DEFAULT_CONJECTURES = SCRIPT_DIR / "inbox" / "conjectures.jsonl"
DEFAULT_CONTACTS = SCRIPT_DIR / "inbox" / "reality_contacts.jsonl"
DEFAULT_PROBES = SCRIPT_DIR / "inbox" / "probes.jsonl"
DEFAULT_MISMATCHES = SCRIPT_DIR / "inbox" / "mismatches.jsonl"
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "gate_results.jsonl"
DEFAULT_REVIEW_QUEUE = SCRIPT_DIR / "out" / "review_queue.jsonl"
DEFAULT_CLAIMS = SCRIPT_DIR / "registries" / "claims.json"
DEFAULT_OUTPUT = SCRIPT_DIR / "registries" / "quality_lab_exports.json"

SCHEMA_ID = "bio-reality:quality-lab-exports"
OWNER = "tools.bio_reality.quality_lab_export"
DEFAULT_GENERATED_AT = "pipeline-generated"

LAYERS = [
    "code_read",
    "codon_usage_topology",
    "orf_eligibility",
    "translation_realization",
    "structural_order",
    "physical_admissibility",
    "function_realization",
    "system_phenotype",
    "cross_layer_relation",
]

LAYER_DISPLAY = {
    "code_read": "code read",
    "codon_usage_topology": "codon usage topology",
    "orf_eligibility": "orf eligibility",
    "translation_realization": "translation realization",
    "structural_order": "structural order",
    "physical_admissibility": "physical admissibility",
    "function_realization": "function realization",
    "system_phenotype": "system phenotype",
    "cross_layer_relation": "cross layer relation",
}

OPEN_MISMATCH_STATUSES = {"mismatch", "partially_aligned", "underdetermined", "blocked_null"}


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
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
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            records.append(data)
    return records


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object")
    return data


def write_json(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, indent=2)
        handle.write("\n")


def as_strings(value: Any) -> list[str]:
    if not isinstance(value, list):
        return []
    return [str(item) for item in value if isinstance(item, (str, int, float)) and str(item)]


def first_string(record: dict[str, Any], keys: list[str]) -> str:
    for key in keys:
        value = record.get(key)
        if isinstance(value, str) and value:
            return value
    return ""


def dedup(values: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for value in values:
        if value in seen:
            continue
        seen.add(value)
        out.append(value)
    return out


def index_by(records: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    indexed: dict[str, dict[str, Any]] = {}
    for record in records:
        value = record.get(key)
        if isinstance(value, str) and value and value not in indexed:
            indexed[value] = record
    return indexed


def normalize_layer_text(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value).lower().replace("_", " ")).strip()


def text_mentions_layer(text: str, layer: str) -> bool:
    normalized = normalize_layer_text(text)
    layer_text = normalize_layer_text(layer)
    display_text = normalize_layer_text(LAYER_DISPLAY.get(layer, layer))
    return normalized == layer_text or normalized == display_text or layer_text in normalized or display_text in normalized


def contact_can_test_layer(contact: dict[str, Any], layer: str) -> bool:
    return any(text_mentions_layer(item, layer) for item in as_strings(contact.get("can_test")))


def any_contact_can_test_layer(contacts: list[dict[str, Any]], layer: str) -> bool:
    return any(contact_can_test_layer(contact, layer) for contact in contacts)


def higher_layers(claimed_layer: str) -> list[str]:
    if claimed_layer not in LAYERS:
        return []
    return LAYERS[LAYERS.index(claimed_layer) + 1 :]


def claims_indexes(claims_doc: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    claim_by_id: dict[str, dict[str, Any]] = {}
    claims_by_conjecture: dict[str, list[dict[str, Any]]] = {}
    claims = claims_doc.get("claims")
    if not isinstance(claims, list):
        return claim_by_id, claims_by_conjecture
    for item in claims:
        if not isinstance(item, dict):
            continue
        claim_id = item.get("claim_id")
        if isinstance(claim_id, str) and claim_id:
            claim_by_id[claim_id] = item
        linked = item.get("linked_conjecture_id")
        if isinstance(linked, str) and linked:
            claims_by_conjecture.setdefault(linked, []).append(item)
    return claim_by_id, claims_by_conjecture


def review_ready_value(value: Any) -> bool:
    return str(value or "").replace("-", "_") == "review_ready"


def eligible_packets(
    gate_results: list[dict[str, Any]],
    review_queue: list[dict[str, Any]],
    limit: int,
) -> list[tuple[str, str, dict[str, Any], dict[str, Any]]]:
    gate_by_key = {
        (str(item.get("packet_kind") or ""), str(item.get("packet_id") or "")): item
        for item in gate_results
        if item.get("packet_kind") and item.get("packet_id")
    }
    review_by_key = {
        (str(item.get("packet_kind") or ""), str(item.get("packet_id") or "")): item
        for item in review_queue
        if item.get("packet_kind") and item.get("packet_id")
    }
    ordered_keys: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for item in gate_results:
        key = (str(item.get("packet_kind") or ""), str(item.get("packet_id") or ""))
        if not key[0] or not key[1]:
            continue
        if item.get("gate_status") == "gate_passed" and key not in seen:
            ordered_keys.append(key)
            seen.add(key)
    for item in review_queue:
        key = (str(item.get("packet_kind") or ""), str(item.get("packet_id") or ""))
        if not key[0] or not key[1]:
            continue
        if review_ready_value(item.get("review_decision")) and key not in seen:
            ordered_keys.append(key)
            seen.add(key)
    packets: list[tuple[str, str, dict[str, Any], dict[str, Any]]] = []
    for key in ordered_keys:
        gate = gate_by_key.get(key, {})
        review = review_by_key.get(key, {})
        packets.append((key[0], key[1], gate, review))
        if len(packets) >= limit:
            break
    return packets


def find_conjecture(
    packet_kind: str,
    packet_id: str,
    conjecture_by_id: dict[str, dict[str, Any]],
    claim_by_id: dict[str, dict[str, Any]],
) -> dict[str, Any] | None:
    if packet_kind == "conjecture" and packet_id in conjecture_by_id:
        return conjecture_by_id[packet_id]
    claim = claim_by_id.get(packet_id)
    linked = claim.get("linked_conjecture_id") if isinstance(claim, dict) else None
    if isinstance(linked, str) and linked in conjecture_by_id:
        return conjecture_by_id[linked]
    for conjecture in conjecture_by_id.values():
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        if packet_id == conjecture_id:
            return conjecture
        if packet_id in as_strings(conjecture.get("linked_claim_ids")):
            return conjecture
        if packet_id in as_strings(conjecture.get("probe_refs")):
            return conjecture
        if packet_id in as_strings(conjecture.get("reality_contact_refs")):
            return conjecture
    return None


def claim_id_for(
    packet_kind: str,
    packet_id: str,
    conjecture: dict[str, Any],
    claim_by_id: dict[str, dict[str, Any]],
    claims_by_conjecture: dict[str, list[dict[str, Any]]],
) -> str:
    if packet_id in claim_by_id:
        return packet_id
    linked_claims = [item for item in as_strings(conjecture.get("linked_claim_ids")) if item in claim_by_id]
    if linked_claims:
        return linked_claims[0]
    conjecture_id = str(conjecture.get("conjecture_id") or "")
    linked = claims_by_conjecture.get(conjecture_id, [])
    if linked:
        value = linked[0].get("claim_id")
        if isinstance(value, str) and value:
            return value
    if packet_kind == "claim":
        return packet_id
    return conjecture_id


def referenced_contacts(
    conjecture: dict[str, Any],
    contacts_by_id: dict[str, dict[str, Any]],
    probes: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    refs = as_strings(conjecture.get("reality_contact_refs"))
    probe_refs = set(as_strings(conjecture.get("probe_refs")))
    for probe in probes:
        if str(probe.get("probe_id") or "") in probe_refs or str(probe.get("conjecture_ref") or "") == str(conjecture.get("conjecture_id") or ""):
            refs.extend(as_strings(probe.get("required_contacts")))
    out = [contacts_by_id[ref] for ref in dedup(refs) if ref in contacts_by_id]
    return out


def referenced_probes(conjecture: dict[str, Any], probes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    conjecture_id = str(conjecture.get("conjecture_id") or "")
    refs = set(as_strings(conjecture.get("probe_refs")))
    out: list[dict[str, Any]] = []
    for probe in probes:
        probe_id = str(probe.get("probe_id") or "")
        if probe_id in refs or str(probe.get("conjecture_ref") or "") == conjecture_id:
            out.append(probe)
    return out


def referenced_mismatches(
    probes: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    probe_refs = {str(item.get("probe_id") or "") for item in probes if item.get("probe_id")}
    contact_refs = {str(item.get("contact_id") or "") for item in contacts if item.get("contact_id")}
    out: list[dict[str, Any]] = []
    for mismatch in mismatches:
        if str(mismatch.get("probe_ref") or "") in probe_refs or str(mismatch.get("contact_ref") or "") in contact_refs:
            out.append(mismatch)
    return out


def has_probe_contact_mismatch_chain(probes: list[dict[str, Any]], contacts: list[dict[str, Any]], mismatches: list[dict[str, Any]]) -> bool:
    probe_refs = {str(item.get("probe_id") or "") for item in probes if item.get("probe_id")}
    contact_refs = {str(item.get("contact_id") or "") for item in contacts if item.get("contact_id")}
    for mismatch in mismatches:
        if str(mismatch.get("probe_ref") or "") in probe_refs and str(mismatch.get("contact_ref") or "") in contact_refs:
            return True
    return False


def blocked_overclaim(gate: dict[str, Any]) -> bool:
    if gate.get("gate_status") != "gate_blocked":
        return False
    issues = " ".join(as_strings(gate.get("issues"))).lower()
    return "overclaim" in issues or "total-biology" in issues or "mechanism" in issues


def export_status(gate: dict[str, Any], review: dict[str, Any]) -> str:
    if review_ready_value(review.get("review_decision")):
        return "review_ready"
    return "gate_passed"


def replication_status(conjecture: dict[str, Any], gate: dict[str, Any], review: dict[str, Any]) -> str:
    for record in (gate, review, conjecture):
        value = record.get("replication_status")
        if isinstance(value, str) and value:
            return value
    return "not_claimed"


def ledger_row(kind: str, residue: str, status: str, severity: str, pointer: str) -> dict[str, str]:
    return {
        "kind": kind,
        "residue": residue,
        "status": status,
        "severity": severity,
        "evidence_pointer": pointer,
        "owner": OWNER,
    }


def ledger_rows(
    conjecture: dict[str, Any],
    contacts: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    conjecture_id = str(conjecture.get("conjecture_id") or "")
    claimed_layer = str(conjecture.get("claimed_layer") or "")
    for layer in higher_layers(claimed_layer):
        if not any_contact_can_test_layer(contacts, layer):
            rows.append(
                ledger_row(
                    "source",
                    f"higher-layer-contact-missing:{layer}",
                    "open",
                    "boundary",
                    f"conjecture:{conjecture_id}#layer:{layer}",
                )
            )
    for mismatch in mismatches:
        status = str(mismatch.get("status") or "")
        if status in OPEN_MISMATCH_STATUSES:
            row_status = "partial" if status == "partially_aligned" else "open"
            mismatch_id = str(mismatch.get("mismatch_id") or "")
            mismatch_kind = str(mismatch.get("mismatch_kind") or "boundary")
            rows.append(
                ledger_row(
                    "boundary",
                    f"mismatch-open:{status}:{mismatch_kind}",
                    row_status,
                    mismatch_kind if mismatch_kind else "boundary",
                    f"mismatch:{mismatch_id}",
                )
            )
    if claimed_layer in LAYERS and not any_contact_can_test_layer(contacts, claimed_layer):
        rows.append(
            ledger_row(
                "overclaim",
                f"claimed-layer-not-covered-by-contact:{claimed_layer}",
                "open",
                "boundary",
                f"conjecture:{conjecture_id}#claimed_layer:{claimed_layer}",
            )
        )
    return rows


def not_claimed(conjecture: dict[str, Any]) -> list[str]:
    claimed_layer = str(conjecture.get("claimed_layer") or "")
    values = as_strings(conjecture.get("forbidden_claims"))
    values.extend(LAYER_DISPLAY.get(layer, layer) for layer in higher_layers(claimed_layer))
    return dedup(values)


def path_string(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def tokens(value: str) -> list[str]:
    return [part for part in re.split(r"[^a-z0-9]+", value.lower()) if part]


def best_artifact(paths: list[Path], candidates: list[str], fallback: str) -> str:
    scored: list[tuple[int, str]] = []
    candidate_tokens = set()
    for candidate in candidates:
        candidate_tokens.update(tokens(candidate))
    for path in paths:
        path_text = path_string(path).lower()
        score = sum(1 for token in candidate_tokens if token and token in path_text)
        if score:
            scored.append((score, path_string(path)))
    if scored:
        scored.sort(key=lambda item: (-item[0], item[1]))
        return scored[0][1]
    return fallback


def artifact_paths(claim_id: str, conjecture: dict[str, Any]) -> dict[str, str]:
    candidates = [
        claim_id,
        str(conjecture.get("conjecture_id") or ""),
        str(conjecture.get("biological_object") or ""),
    ]
    bio_paths = sorted((REPO_ROOT / "papers" / "bio_reality" / "parts").glob("**/*.tex"))
    bedc_paths = sorted((REPO_ROOT / "papers" / "bedc" / "parts" / "concrete_instances").glob("*bioreality*.tex"))
    bio_fallback = "papers/bio_reality/parts/codon_window_reality_boundary.tex"
    bedc_fallback = "papers/bedc/parts/concrete_instances/14104_bioreality_namecert_construction.tex"
    return {
        "bedc_module": best_artifact(bedc_paths, candidates, bedc_fallback),
        "bio_paper": best_artifact(bio_paths, candidates, bio_fallback),
    }


def compile_export(
    packet_kind: str,
    packet_id: str,
    gate: dict[str, Any],
    review: dict[str, Any],
    conjecture: dict[str, Any],
    claim_id: str,
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
) -> dict[str, Any]:
    contact_refs = [str(item.get("contact_id") or "") for item in contacts if item.get("contact_id")]
    probe_refs = [str(item.get("probe_id") or "") for item in probes if item.get("probe_id")]
    mismatch_refs = [str(item.get("mismatch_id") or "") for item in mismatches if item.get("mismatch_id")]
    form = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
    internal = as_strings(form.get("internal_structure")) if isinstance(form, dict) else []
    gate_status = str(gate.get("gate_status") or review.get("gate_status") or "")
    review_decision = str(review.get("review_decision") or "")
    finite_row_count = 1 + len(contact_refs) + len(probe_refs) + len(mismatch_refs) + (1 if gate else 0)
    return {
        "packet_id": packet_id,
        "claim_id": claim_id,
        "claimed_layer": str(conjecture.get("claimed_layer") or ""),
        "export_status": export_status(gate, review),
        "source_spec": {
            "reality_contacts": contact_refs,
            "can_test": dedup([item for contact in contacts for item in as_strings(contact.get("can_test"))]),
            "cannot_test": dedup([item for contact in contacts for item in as_strings(contact.get("cannot_test"))]),
        },
        "pattern_spec": {
            "internal_surfaces": internal,
            "probe_refs": probe_refs,
        },
        "classifier_spec": {
            "gate_status": gate_status,
            "review_decision": review_decision,
            "blocked_overclaim": blocked_overclaim(gate),
        },
        "stability_spec": {
            "sample_scope": "finite_rows",
            "population_claim": False,
            "replication_status": replication_status(conjecture, gate, review),
        },
        "metrics": {
            "finite_row_count": finite_row_count,
            "has_reality_contact": bool(contact_refs),
            "has_probe_contact_mismatch_chain": has_probe_contact_mismatch_chain(probes, contacts, mismatches),
        },
        "ledger_rows": ledger_rows(conjecture, contacts, mismatches),
        "not_claimed": not_claimed(conjecture),
        "artifacts": artifact_paths(claim_id, conjecture),
        "fact_owner": {
            "contact_refs": contact_refs,
            "probe_refs": probe_refs,
            "mismatch_refs": mismatch_refs,
            "gate_result_ref": f"{packet_kind}:{packet_id}",
        },
    }


def compile_exports(
    conjectures: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
    gate_results: list[dict[str, Any]],
    review_queue: list[dict[str, Any]],
    claims_doc: dict[str, Any],
    limit: int,
) -> list[dict[str, Any]]:
    conjecture_by_id = index_by(conjectures, "conjecture_id")
    contacts_by_id = index_by(contacts, "contact_id")
    claim_by_id, claims_by_conjecture = claims_indexes(claims_doc)
    exports: list[dict[str, Any]] = []
    for packet_kind, packet_id, gate, review in eligible_packets(gate_results, review_queue, limit):
        conjecture = find_conjecture(packet_kind, packet_id, conjecture_by_id, claim_by_id)
        if conjecture is None:
            continue
        claim_id = claim_id_for(packet_kind, packet_id, conjecture, claim_by_id, claims_by_conjecture)
        packet_probes = referenced_probes(conjecture, probes)
        packet_contacts = referenced_contacts(conjecture, contacts_by_id, packet_probes)
        packet_mismatches = referenced_mismatches(packet_probes, packet_contacts, mismatches)
        exports.append(
            compile_export(
                packet_kind,
                packet_id,
                gate,
                review,
                conjecture,
                claim_id,
                packet_contacts,
                packet_probes,
                packet_mismatches,
            )
        )
    return exports


def seeded_runtime() -> tuple[
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
]:
    contacts = [
        {
            "can_test": ["code_read layer"],
            "cannot_test": ["translation realization", "structural order", "function realization"],
            "contact_id": "ncbi.standard.code",
            "observed_fact": "A curated table maps codons to amino-acid or stop labels.",
            "source_kind": "genetic_code_table",
            "source_ref": "NCBI translation table",
        },
        {
            "can_test": ["orf_eligibility"],
            "cannot_test": ["translation realization", "structural order", "function realization"],
            "contact_id": "curated.orf.interval.contact",
            "observed_fact": "A curated interval dataset marks start-stop windows.",
            "source_kind": "sequence_database",
            "source_ref": "tools/bio_reality/data/curated_orf_interval_contact_dataset.json",
        },
        {
            "can_test": ["translation_realization", "cross_layer_relation"],
            "cannot_test": ["global biological law", "system phenotype"],
            "contact_id": "translation.perturbation.fixture",
            "observed_fact": "A bounded perturbation readback records translation-layer response.",
            "source_kind": "perturbation_data",
            "source_ref": "fixture perturbation matrix",
        },
    ]
    conjectures = [
        {
            "bedc_minimal_form": {
                "carrier": "codon stream",
                "distinctions": ["codon label", "stop label"],
                "internal_structure": ["coordinate"],
                "readback": "named genetic-code table",
            },
            "biological_object": "codon table",
            "claimed_layer": "code_read",
            "conjecture_id": "codon.window6.local.tile.boundary",
            "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
            "forbidden_claims": ["Codon assignment alone is not protein realization."],
            "linked_claim_ids": ["h0.R.cardinality.13"],
            "probe_refs": ["codon.assignment.probe"],
            "reality_contact_refs": ["ncbi.standard.code"],
        },
        {
            "bedc_minimal_form": {
                "carrier": "orf interval",
                "distinctions": ["start", "stop", "window"],
                "internal_structure": ["coordinate", "relation"],
                "readback": "curated interval contact",
            },
            "biological_object": "orf window",
            "claimed_layer": "orf_eligibility",
            "conjecture_id": "orf_eligibility.seed.boundary",
            "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
            "forbidden_claims": ["Coordinate evidence alone is not translation realization."],
            "linked_claim_ids": ["h0.R.motif.compression"],
            "probe_refs": ["orf.interval.probe"],
            "reality_contact_refs": ["curated.orf.interval.contact"],
        },
        {
            "bedc_minimal_form": {
                "carrier": "translation perturbation window",
                "distinctions": ["codon usage", "translation response"],
                "internal_structure": ["coordinate", "relation"],
                "readback": "bounded perturbation readback",
            },
            "biological_object": "DNA to protein",
            "claimed_layer": "cross_layer_relation",
            "conjecture_id": "cross.layer.perturbed",
            "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe", "mechanism_bridge"],
            "forbidden_claims": ["The perturbation readback is not a global biological law."],
            "linked_claim_ids": ["h3.translation_realization.cross_organism_cun_uur_leu_gate"],
            "probe_refs": ["translation.perturbation.probe"],
            "reality_contact_refs": ["translation.perturbation.fixture"],
        },
    ]
    probes = [
        {
            "conjecture_ref": "codon.window6.local.tile.boundary",
            "probe_id": "codon.assignment.probe",
            "required_contacts": ["ncbi.standard.code"],
        },
        {
            "conjecture_ref": "orf_eligibility.seed.boundary",
            "probe_id": "orf.interval.probe",
            "required_contacts": ["curated.orf.interval.contact"],
        },
        {
            "conjecture_ref": "cross.layer.perturbed",
            "probe_id": "translation.perturbation.probe",
            "required_contacts": ["translation.perturbation.fixture"],
        },
    ]
    mismatches = [
        {
            "blocked_claims": ["protein realization"],
            "contact_ref": "ncbi.standard.code",
            "mismatch_id": "codon.assignment.scope",
            "mismatch_kind": "none",
            "observed_delta": "The contact is only code-layer evidence.",
            "probe_ref": "codon.assignment.probe",
            "status": "aligned",
        },
        {
            "blocked_claims": ["translation realization"],
            "contact_ref": "curated.orf.interval.contact",
            "mismatch_id": "orf.interval.scope",
            "mismatch_kind": "none",
            "observed_delta": "The contact is only ORF-eligibility evidence.",
            "probe_ref": "orf.interval.probe",
            "status": "aligned",
        },
        {
            "blocked_claims": ["global biological law"],
            "contact_ref": "translation.perturbation.fixture",
            "mismatch_id": "translation.perturbation.boundary",
            "mismatch_kind": "scope_too_large",
            "observed_delta": "The perturbation readback is bounded.",
            "probe_ref": "translation.perturbation.probe",
            "status": "partially_aligned",
        },
    ]
    gate_results = [
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "issues": [],
            "next_action": "eligible for operator review only",
            "packet_id": "codon.window6.local.tile.boundary",
            "packet_kind": "conjecture",
        },
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "issues": [],
            "next_action": "eligible for operator review only",
            "packet_id": "orf_eligibility.seed.boundary",
            "packet_kind": "conjecture",
        },
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "issues": [],
            "next_action": "eligible for operator review only",
            "packet_id": "cross.layer.perturbed",
            "packet_kind": "conjecture",
        },
    ]
    review_queue = [
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "packet_id": "codon.window6.local.tile.boundary",
            "packet_kind": "conjecture",
            "review_decision": "review_ready",
        },
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "packet_id": "orf_eligibility.seed.boundary",
            "packet_kind": "conjecture",
            "review_decision": "review_ready",
        },
        {
            "allowed_write": "none",
            "gate_status": "gate_passed",
            "packet_id": "cross.layer.perturbed",
            "packet_kind": "conjecture",
            "review_decision": "review_ready",
        },
    ]
    return conjectures, contacts, probes, mismatches, gate_results, review_queue


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Compile BioReality quality-lab export registry")
    parser.add_argument("--conjectures", default=str(DEFAULT_CONJECTURES))
    parser.add_argument("--contacts", default=str(DEFAULT_CONTACTS))
    parser.add_argument("--probes", default=str(DEFAULT_PROBES))
    parser.add_argument("--mismatches", default=str(DEFAULT_MISMATCHES))
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--review-queue", default=str(DEFAULT_REVIEW_QUEUE))
    parser.add_argument("--claims", default=str(DEFAULT_CLAIMS))
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT))
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    parser.add_argument("--limit", type=int, default=5)
    parser.add_argument("--seed-fixture", action="store_true")
    args = parser.parse_args(argv)

    if args.limit < 1:
        print("[quality-lab-export] error: --limit must be positive", file=sys.stderr)
        return 1

    try:
        conjectures = read_jsonl(Path(args.conjectures))
        contacts = read_jsonl(Path(args.contacts))
        probes = read_jsonl(Path(args.probes))
        mismatches = read_jsonl(Path(args.mismatches))
        gate_results = read_jsonl(Path(args.gate_results))
        review_queue = read_jsonl(Path(args.review_queue))
        if args.seed_fixture:
            conjectures, contacts, probes, mismatches, gate_results, review_queue = seeded_runtime()
        claims_doc = read_json(Path(args.claims))
        exports = compile_exports(
            conjectures,
            contacts,
            probes,
            mismatches,
            gate_results,
            review_queue,
            claims_doc,
            args.limit,
        )
        output = {
            "schema_id": SCHEMA_ID,
            "generated_at": args.generated_at,
            "exports": exports,
        }
        write_json(Path(args.output), output)
    except Exception as exc:
        print(f"[quality-lab-export] error: {exc}", file=sys.stderr)
        return 1

    sample = exports[0]["packet_id"] if exports else "none"
    print(f"[quality-lab-export] exports={len(exports)} sample_packet={sample}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

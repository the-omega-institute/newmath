#!/usr/bin/env python3
"""Run one deterministic BioReality conjecture-deepening loop."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

try:
    from deepening_gates import gate_all
    from store import BioRealityPaths, BioRealityStore, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from deepening_gates import gate_all
    from store import BioRealityPaths, BioRealityStore, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent


def _ids(records: list[dict[str, Any]], key: str) -> set[str]:
    return {str(record.get(key)) for record in records if record.get(key)}


def _mismatches_by_probe(mismatches: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    by_probe: dict[str, list[dict[str, Any]]] = {}
    for mismatch in mismatches:
        probe_ref = str(mismatch.get("probe_ref") or "")
        if probe_ref:
            by_probe.setdefault(probe_ref, []).append(mismatch)
    return by_probe


def _gate_by_packet(results: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    return {
        (str(result.get("packet_kind") or ""), str(result.get("packet_id") or "")): result
        for result in results
    }


def _task(packet_kind: str, packet_id: str, task_kind: str, reason: str, priority: int) -> dict[str, Any]:
    return {
        "packet_kind": packet_kind,
        "packet_id": packet_id,
        "task_kind": task_kind,
        "priority": priority,
        "reason": reason,
    }


def plan_deepening_tasks(
    conjectures: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
    gate_results: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    contact_ids = _ids(contacts, "contact_id")
    probe_ids = _ids(probes, "probe_id")
    gate_by_packet = _gate_by_packet(gate_results)
    mismatch_by_probe = _mismatches_by_probe(mismatches)
    tasks: list[dict[str, Any]] = []

    for result in gate_results:
        if result.get("gate_status") == "gate_blocked":
            issues = result.get("issues") if isinstance(result.get("issues"), list) else []
            task_kind = "blocked_overclaim" if any("total-biology" in str(issue) or "mechanism" in str(issue) for issue in issues) else "blocked_shape"
            tasks.append(
                _task(
                    str(result.get("packet_kind") or ""),
                    str(result.get("packet_id") or ""),
                    task_kind,
                    "; ".join(str(issue) for issue in issues[:3]) or "gate blocked",
                    100,
                )
            )

    for conjecture in conjectures:
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        evidence = set(conjecture.get("evidence_basis") or [])
        contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
        probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
        if not probe_refs:
            tasks.append(_task("conjecture", conjecture_id, "needs_probe", "conjecture has no derived probe", 80))
        if "external_reality" in evidence and not contact_refs:
            tasks.append(_task("conjecture", conjecture_id, "needs_reality_contact", "external reality evidence has no contact ref", 90))
        for contact_ref in contact_refs:
            if contact_ref not in contact_ids:
                tasks.append(_task("conjecture", conjecture_id, "needs_reality_contact", f"missing contact {contact_ref}", 90))
        for probe_ref in probe_refs:
            if probe_ref not in probe_ids:
                tasks.append(_task("conjecture", conjecture_id, "needs_probe", f"missing probe {probe_ref}", 85))

    for probe in probes:
        probe_id = str(probe.get("probe_id") or "")
        required_contacts = [str(item) for item in probe.get("required_contacts", []) if isinstance(item, str)]
        if not required_contacts:
            tasks.append(_task("probe", probe_id, "needs_reality_contact", "probe has no required reality contact", 75))
        for contact_ref in required_contacts:
            if contact_ref not in contact_ids:
                tasks.append(_task("probe", probe_id, "needs_reality_contact", f"missing contact {contact_ref}", 90))
        if required_contacts and not mismatch_by_probe.get(probe_id):
            tasks.append(_task("probe", probe_id, "needs_mismatch_review", "probe has contacts but no mismatch record", 70))

    for mismatch in mismatches:
        mismatch_id = str(mismatch.get("mismatch_id") or "")
        status = str(mismatch.get("status") or "")
        if status in {"mismatch", "partially_aligned", "underdetermined"}:
            tasks.append(_task("mismatch", mismatch_id, "needs_refinement", f"mismatch status is {status}", 95))

    ready_ids: set[tuple[str, str]] = set()
    for conjecture in conjectures:
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        conjecture_gate = gate_by_packet.get(("conjecture", conjecture_id), {})
        probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
        has_chain = any(mismatch_by_probe.get(probe_ref) for probe_ref in probe_refs)
        if conjecture_gate.get("gate_status") == "gate_passed" and has_chain:
            ready_ids.add(("conjecture", conjecture_id))
    for packet_kind, packet_id in ready_ids:
        tasks.append(_task(packet_kind, packet_id, "ready_for_operator_review", "conjecture has gate pass and probe-contact-mismatch chain", 20))

    tasks.sort(key=lambda item: (-int(item["priority"]), str(item["packet_kind"]), str(item["packet_id"]), str(item["task_kind"])))
    return tasks


def plan_review_queue(gate_results: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    blocked = {(task["packet_kind"], task["packet_id"]) for task in tasks if str(task.get("task_kind", "")).startswith("blocked")}
    ready = {(task["packet_kind"], task["packet_id"]) for task in tasks if task.get("task_kind") == "ready_for_operator_review"}
    review: list[dict[str, Any]] = []
    for result in gate_results:
        key = (str(result.get("packet_kind") or ""), str(result.get("packet_id") or ""))
        if key in blocked:
            decision = "blocked"
        elif key in ready:
            decision = "review_ready"
        elif result.get("gate_status") == "gate_passed":
            decision = "needs_deepening"
        else:
            decision = "blocked"
        review.append(
            {
                "packet_kind": key[0],
                "packet_id": key[1],
                "gate_status": result.get("gate_status"),
                "review_decision": decision,
                "allowed_write": "none",
            }
        )
    review.sort(key=lambda item: (item["review_decision"], item["packet_kind"], item["packet_id"]))
    return review


def run_once(store: BioRealityStore) -> dict[str, Any]:
    conjectures = store.load_conjectures()
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    gate_results = gate_all(conjectures, contacts, probes, mismatches)
    tasks = plan_deepening_tasks(conjectures, contacts, probes, mismatches, gate_results)
    review = plan_review_queue(gate_results, tasks)
    store.write_gate_results(gate_results)
    store.write_deepening_tasks(tasks)
    store.write_review_queue(review)
    return {
        "conjectures": len(conjectures),
        "contacts": len(contacts),
        "probes": len(probes),
        "mismatches": len(mismatches),
        "gate_results": len(gate_results),
        "tasks": len(tasks),
        "review_items": len(review),
        "blocked": sum(1 for result in gate_results if result.get("gate_status") == "gate_blocked"),
    }


def self_test() -> int:
    base = SCRIPT_DIR / "state" / "self_test"
    paths = BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=base / "conjectures.jsonl",
        contacts=base / "reality_contacts.jsonl",
        probes=base / "probes.jsonl",
        mismatches=base / "mismatches.jsonl",
        gate_results=base / "gate_results.jsonl",
        deepening_tasks=base / "deepening_tasks.jsonl",
        review_queue=base / "review_queue.jsonl",
    )
    contact = {
        "contact_id": "ncbi.standard.code",
        "source_kind": "genetic_code_table",
        "source_ref": "NCBI translation table",
        "source_snapshot": "fixture",
        "observed_fact": "A curated table maps codons to amino-acid or stop labels.",
        "resolution": "codon assignment",
        "known_noise_or_bias": "fixture only",
        "can_test": ["code_read layer"],
        "cannot_test": ["protein realization"],
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
        "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
        "reality_contact_refs": ["ncbi.standard.code"],
        "probe_refs": ["codon.assignment.probe"],
        "forbidden_claims": ["Codon assignment alone is not protein realization."],
        "null_reason": "",
    }
    probe = {
        "probe_id": "codon.assignment.probe",
        "conjecture_ref": "codon.code.read",
        "probe_kind": "finite_enumeration",
        "derived_from": ["bedc_coordinate"],
        "test_statement": "The contact supports code-layer assignment only.",
        "support_condition": "Contact can test code_read.",
        "break_condition": "Contact is used to claim protein realization.",
        "required_contacts": ["ncbi.standard.code"],
        "forbidden_interpretations": ["Do not infer function."],
        "null_reason": "",
    }
    mismatch = {
        "mismatch_id": "codon.assignment.scope",
        "probe_ref": "codon.assignment.probe",
        "contact_ref": "ncbi.standard.code",
        "status": "aligned",
        "mismatch_kind": "none",
        "observed_delta": "The contact is only code-layer evidence.",
        "refinement_pressure": "Keep higher-layer claims blocked.",
        "blocked_claims": ["protein realization"],
        "null_reason": "",
    }
    for path, records in (
        (paths.contacts, [contact]),
        (paths.conjectures, [conjecture]),
        (paths.probes, [probe]),
        (paths.mismatches, [mismatch]),
    ):
        write_jsonl(path, records)
    summary = run_once(BioRealityStore(paths))
    tasks = BioRealityStore(paths).paths.deepening_tasks.read_text(encoding="utf-8")
    if summary["blocked"] != 0 or "ready_for_operator_review" not in tasks:
        print(json.dumps(summary, indent=2), file=sys.stderr)
        return 1
    print("[bio-reality-loop] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run one BioReality deepening loop")
    parser.add_argument("--conjectures", default=str(BioRealityPaths.conjectures), help="conjecture JSONL")
    parser.add_argument("--contacts", default=str(BioRealityPaths.contacts), help="reality contact JSONL")
    parser.add_argument("--probes", default=str(BioRealityPaths.probes), help="probe JSONL")
    parser.add_argument("--mismatches", default=str(BioRealityPaths.mismatches), help="mismatch JSONL")
    parser.add_argument("--gate-results", default=str(BioRealityPaths.gate_results), help="gate result JSONL")
    parser.add_argument("--deepening-tasks", default=str(BioRealityPaths.deepening_tasks), help="deepening task JSONL")
    parser.add_argument("--review-queue", default=str(BioRealityPaths.review_queue), help="review queue JSONL")
    parser.add_argument("--self-test", action="store_true", help="run built-in loop fixture")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    paths = BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=Path(args.conjectures),
        contacts=Path(args.contacts),
        probes=Path(args.probes),
        mismatches=Path(args.mismatches),
        gate_results=Path(args.gate_results),
        deepening_tasks=Path(args.deepening_tasks),
        review_queue=Path(args.review_queue),
    )
    try:
        summary = run_once(BioRealityStore(paths))
    except Exception as exc:
        print(f"[bio-reality-loop] error: {exc}", file=sys.stderr)
        return 1
    print(
        "[bio-reality-loop] "
        f"conjectures={summary['conjectures']} contacts={summary['contacts']} "
        f"probes={summary['probes']} mismatches={summary['mismatches']} "
        f"tasks={summary['tasks']} review_items={summary['review_items']} blocked={summary['blocked']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

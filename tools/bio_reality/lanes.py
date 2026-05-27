#!/usr/bin/env python3
"""P/G/A lane helpers for BioReality automation."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import re
import socket
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    import agent_bus
    import bedc_writeback_gates
    import bio_reality_loop
    import oracle_consultation
    from experiments import runner as experiment_runner
    import signal_assimilator
    import vision_intake
    from store import BioRealityPaths, BioRealityStore, append_jsonl, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import agent_bus
    import bedc_writeback_gates
    import bio_reality_loop
    import oracle_consultation
    from experiments import runner as experiment_runner
    import signal_assimilator
    import vision_intake
    from store import BioRealityPaths, BioRealityStore, append_jsonl, read_jsonl, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
DOMAIN_PROFILE = SCRIPT_DIR / "dna_to_protein_ladder.json"
PIPELINE_CONFIG = SCRIPT_DIR / "pipeline_config.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _packet_target(packet_kind: str, packet_id: str, lane: str, reason: str, priority: int) -> dict[str, Any]:
    return {
        "packet_kind": packet_kind,
        "packet_id": packet_id,
        "lane": lane,
        "priority": priority,
        "reason": reason,
        "created_at": now_iso(),
        "allowed_write": "runtime_packet_only",
    }


def _dedup_targets(targets: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str, str, str]] = set()
    out: list[dict[str, Any]] = []
    for target in targets:
        key = (
            str(target.get("packet_kind") or ""),
            str(target.get("packet_id") or ""),
            str(target.get("lane") or ""),
            str(target.get("reason") or ""),
        )
        if key in seen:
            continue
        seen.add(key)
        out.append(target)
    out.sort(key=lambda item: (-int(item.get("priority") or 0), str(item.get("packet_kind") or ""), str(item.get("packet_id") or "")))
    return out


def _load_domain_profile() -> dict[str, Any]:
    try:
        data = json.loads(DOMAIN_PROFILE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def run_vision_lane(store: BioRealityStore) -> dict[str, Any]:
    return vision_intake.run_vision_lane(store)


def bootstrap_research_memory(store: BioRealityStore) -> dict[str, Any]:
    """Create the first self-generated BioReality packets when memory is empty."""
    if any((store.load_conjectures(), store.load_contacts(), store.load_probes(), store.load_mismatches())):
        return {"bootstrapped": False}
    profile = _load_domain_profile()
    profile_id = str(profile.get("profile_id") or "dna_to_protein_realization")
    contacts = [
        {
            "contact_id": "curated.standard.code.table",
            "source_kind": "genetic_code_table",
            "source_ref": "curated standard genetic-code bridge",
            "source_snapshot": profile_id,
            "observed_fact": "A curated standard-code table assigns codons to amino-acid or stop labels.",
            "resolution": "codon label readback",
            "known_noise_or_bias": "The table is a reality bridge for code labels, not a mechanism or universality proof.",
            "can_test": ["code_read", "local codon tile label split"],
            "cannot_test": ["translation realization", "structural order", "physical admissibility", "function realization"],
            "null_reason": "",
        }
    ]
    conjectures = [
        {
            "conjecture_id": "codon.window6.local.tile.boundary",
            "biological_object": "standard-code codon table",
            "informal_statement": (
                "Window-six codon coordinates may expose local boundary-tile structure, "
                "but curated code labels remain external reality contacts."
            ),
            "bedc_minimal_form": {
                "carrier": "codon cube Q6",
                "distinctions": ["six-bit codon display", "local tile face", "singleton label corner", "three-point label class"],
                "readback": "standard-code label table",
                "internal_structure": ["coordinate", "closure", "spectrum", "relation"],
            },
            "claimed_layer": "code_read",
            "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
            "reality_contact_refs": ["curated.standard.code.table"],
            "probe_refs": ["codon.local.tile.no.global.law"],
            "forbidden_claims": [
                "A local codon tile is not a global biological law.",
                "Window-six geometry alone is not translation, structure, physical admissibility, or function.",
            ],
            "null_reason": "",
        }
    ]
    probes = [
        {
            "probe_id": "codon.local.tile.no.global.law",
            "conjecture_ref": "codon.window6.local.tile.boundary",
            "probe_kind": "boundary_mismatch",
            "derived_from": ["bedc_coordinate", "bedc_closure", "external_reality_hint"],
            "test_statement": "A local codon-tile pattern must stay at code_read unless a separate higher-layer contact is supplied.",
            "support_condition": "The curated code table supports only codon-label readback and local split checks.",
            "break_condition": "The pipeline promotes the local tile to translation, structure, physical admissibility, function, or universal mechanism.",
            "required_contacts": ["curated.standard.code.table"],
            "forbidden_interpretations": [
                "Do not infer that DNA obeys BEDC geometry as biological necessity.",
                "Do not infer protein function from a codon-tile split.",
            ],
            "null_reason": "",
        }
    ]
    mismatches = [
        {
            "mismatch_id": "codon.local.tile.scope.boundary",
            "probe_ref": "codon.local.tile.no.global.law",
            "contact_ref": "curated.standard.code.table",
            "status": "aligned",
            "mismatch_kind": "none",
            "observed_delta": "The contact supports code-layer readback and blocks higher-layer promotion.",
            "refinement_pressure": "Next cycles should search for separate reality contacts before crossing the translation or function boundary.",
            "blocked_claims": ["protein realization", "folded structure", "physical admissibility", "biological function", "universal mechanism"],
            "null_reason": "",
        }
    ]
    store.write_contacts(contacts)
    store.write_conjectures(conjectures)
    store.write_probes(probes)
    store.write_mismatches(mismatches)
    return {
        "bootstrapped": True,
        "profile_id": profile_id,
        "conjectures": len(conjectures),
        "contacts": len(contacts),
        "probes": len(probes),
        "mismatches": len(mismatches),
    }


def _profile_layers(profile: dict[str, Any]) -> list[str]:
    layers = profile.get("layers", [])
    if not isinstance(layers, list):
        return []
    out: list[str] = []
    for layer in layers:
        if isinstance(layer, str) and layer:
            out.append(layer)
        elif isinstance(layer, dict) and isinstance(layer.get("layer"), str) and layer.get("layer"):
            out.append(str(layer["layer"]))
    return out


def promote_next_layer(store: BioRealityStore) -> dict[str, Any]:
    """When all conjectures at the current depth are aligned, seed the next layer."""
    profile = _load_domain_profile()
    layers = _profile_layers(profile)
    if not layers:
        return {"promoted": False, "reason": "no layer ladder"}
    layer_descriptions = profile.get("layer_descriptions", {})
    if not isinstance(layer_descriptions, dict):
        layer_descriptions = {}

    conjectures = store.load_conjectures()
    mismatches = store.load_mismatches()
    for index, layer in enumerate(layers[:-1]):
        layer_conjectures = [
            conjecture
            for conjecture in conjectures
            if str(conjecture.get("claimed_layer") or "") == layer
        ]
        if not layer_conjectures:
            continue
        layer_probe_refs = {
            str(probe_ref)
            for conjecture in layer_conjectures
            for probe_ref in conjecture.get("probe_refs", [])
            if isinstance(probe_ref, str)
        }
        related_mismatches = [
            mismatch
            for mismatch in mismatches
            if str(mismatch.get("probe_ref") or "") in layer_probe_refs
        ]
        mismatch_probe_refs = {
            str(mismatch.get("probe_ref") or "")
            for mismatch in related_mismatches
        }
        if not all(
            any(probe_ref in mismatch_probe_refs for probe_ref in conjecture.get("probe_refs", []) if isinstance(probe_ref, str))
            for conjecture in layer_conjectures
        ):
            continue
        if not all(str(mismatch.get("status") or "") in {"aligned", "blocked_null"} for mismatch in related_mismatches):
            continue

        next_layer = layers[index + 1]
        if any(str(conjecture.get("claimed_layer") or "") == next_layer for conjecture in conjectures):
            return {"promoted": False, "reason": "next layer already seeded"}
        new_conjecture_id = f"{next_layer}.seed.boundary"
        conjectures.append(
            {
                "conjecture_id": new_conjecture_id,
                "biological_object": str(layer_descriptions.get(next_layer, next_layer)),
                "informal_statement": (
                    f"Seed packet for layer {next_layer}. Awaits a separate reality contact before any claim can be made."
                ),
                "bedc_minimal_form": {
                    "carrier": "awaiting reality contact",
                    "distinctions": ["awaiting reality contact"],
                    "readback": "awaiting reality contact",
                    "internal_structure": ["none"],
                },
                "claimed_layer": next_layer,
                "evidence_basis": ["bedc_coordinate"],
                "reality_contact_refs": [],
                "probe_refs": [],
                "forbidden_claims": [
                    f"Layer {next_layer} cannot be promoted to higher layers without a separate reality contact.",
                    f"BEDC coordinate alone does not realize layer {next_layer}.",
                ],
                "null_reason": "",
            }
        )
        store.write_conjectures(conjectures)
        return {
            "promoted": True,
            "new_conjecture_id": new_conjecture_id,
            "from_layer": layer,
            "to_layer": next_layer,
        }
    return {"promoted": False, "reason": "no aligned-closed layer"}


def run_packet_lane(store: BioRealityStore) -> dict[str, Any]:
    bootstrap = bootstrap_research_memory(store)
    promotion = promote_next_layer(store)
    conjectures = store.load_conjectures()
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    contact_ids = {str(item.get("contact_id") or "") for item in contacts}
    probe_ids = {str(item.get("probe_id") or "") for item in probes}
    mismatch_probe_ids = {str(item.get("probe_ref") or "") for item in mismatches}
    targets: list[dict[str, Any]] = []

    for conjecture in conjectures:
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        if not conjecture_id:
            continue
        probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
        contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
        evidence = set(str(item) for item in conjecture.get("evidence_basis", []) if isinstance(item, str))
        if not probe_refs:
            targets.append(_packet_target("conjecture", conjecture_id, "bio-P", "derive falsifiable probe from BEDC minimal form", 90))
        if "external_reality" in evidence and not contact_refs:
            targets.append(_packet_target("conjecture", conjecture_id, "bio-P", "attach curated reality contact without promoting mechanism", 95))
        for contact_ref in contact_refs:
            if contact_ref not in contact_ids:
                targets.append(_packet_target("conjecture", conjecture_id, "bio-P", f"resolve missing reality contact {contact_ref}", 95))
        for probe_ref in probe_refs:
            if probe_ref not in probe_ids:
                targets.append(_packet_target("conjecture", conjecture_id, "bio-P", f"resolve missing probe {probe_ref}", 88))

    for probe in probes:
        probe_id = str(probe.get("probe_id") or "")
        if not probe_id:
            continue
        required_contacts = [str(item) for item in probe.get("required_contacts", []) if isinstance(item, str)]
        if not required_contacts:
            targets.append(_packet_target("probe", probe_id, "bio-P", "name at least one reality contact required by the probe", 82))
        for contact_ref in required_contacts:
            if contact_ref not in contact_ids:
                targets.append(_packet_target("probe", probe_id, "bio-P", f"resolve missing required contact {contact_ref}", 92))
        if required_contacts and probe_id not in mismatch_probe_ids:
            targets.append(_packet_target("probe", probe_id, "bio-P", "record mismatch or alignment ledger for contact chain", 78))

    for mismatch in mismatches:
        mismatch_id = str(mismatch.get("mismatch_id") or "")
        status = str(mismatch.get("status") or "")
        if mismatch_id and status in {"mismatch", "partially_aligned", "underdetermined"}:
            targets.append(_packet_target("mismatch", mismatch_id, "bio-P", f"refine conjecture after {status} contact", 97))

    targets = _dedup_targets(targets)
    store.write_packet_targets(targets)
    render_lane_dashboard(store.paths, targets)
    return {
        "lane": "bio-P",
        **bootstrap,
        "promotion": promotion,
        "conjectures": len(conjectures),
        "contacts": len(contacts),
        "probes": len(probes),
        "mismatches": len(mismatches),
        "packet_targets": len(targets),
    }


def _oracle_session_backfill_lane(store: BioRealityStore) -> dict[str, Any]:
    """Scan oracle_sessions/conv_*.json for substantive ChatGPT responses that
    never made it into a lane transcript (because the Python client gave up
    before the userscript posted back). Reconstruct client-side transcripts
    and synthesize oracle_consultation_completed events so bio-oracle-consumer
    can ingest them on the next cycle. Idempotent — re-runs detect already-
    backfilled topics via the `.backfill` suffix."""
    summary = {"lane": "bio-C", "scanned": 0, "backfilled": 0, "skipped_thin": 0, "skipped_present": 0}
    sessions_dir = store.paths.events.parent.parent / "state" / "oracle_sessions" if not (store.paths.events.parent.parent / "state" / "oracle_sessions").exists() else store.paths.events.parent.parent / "state" / "oracle_sessions"
    if not sessions_dir.exists():
        sessions_dir = Path(__file__).parent / "state" / "oracle_sessions"
    if not sessions_dir.exists():
        return summary
    events_path = store.paths.events
    for conv_path in sorted(sessions_dir.glob("conv_*.json")):
        summary["scanned"] += 1
        try:
            conv = json.loads(conv_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        turns = conv.get("turns") or []
        if not turns:
            summary["skipped_thin"] += 1
            continue
        first = turns[0]
        response = str(first.get("response") or "")
        if not response or "ERROR" in response[:120] or "[TIMEOUT" in response[:120] or len(response) < 300:
            summary["skipped_thin"] += 1
            continue
        tag = str(conv.get("tag") or "")
        if not tag or tag in {"oracle-bridge-smoke-test"}:
            continue
        lane = "bio-Plan" if (tag.startswith("bio-Plan") or tag.startswith("phase.")) else "bio-G"
        topic_base = re.sub(r"[^A-Za-z0-9._-]+", ".", tag.strip()) or "review"
        if not topic_base.startswith(lane):
            topic_base = f"{lane}.review.{topic_base}"
        topic = f"{topic_base}.backfill"
        lane_dir = sessions_dir / lane
        lane_dir.mkdir(parents=True, exist_ok=True)
        already = False
        for existing in lane_dir.glob("*.jsonl"):
            stem = existing.stem
            if stem.split("__", 1)[-1] == topic:
                already = True
                break
        if already:
            summary["skipped_present"] += 1
            continue
        created = conv.get("created_at", "")
        try:
            stamp = datetime.fromisoformat(created).astimezone(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        except ValueError:
            stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        base = lane_dir / f"{stamp}__{topic}"
        session = {
            "record_kind": "session",
            "lane": lane,
            "topic": topic,
            "conversation_id": conv.get("conversation_id", ""),
            "turn_count": 1,
            "pdf_attached": True,
            "pdf_skipped_reason": "",
            "closed_reason": "backfilled_substantive_server_response",
            "max_turns_reached": False,
        }
        turn_rec = {
            "record_kind": "turn",
            "turn": 0,
            "prompt": "(backfilled from server-side conv; original client transcript timed out before this response was posted)",
            "result": {
                "status": "completed",
                "response": response,
                "conversation_id": conv.get("conversation_id", ""),
                "task_id": first.get("task_id", ""),
            },
        }
        with base.with_suffix(".jsonl").open("w", encoding="utf-8") as fh:
            fh.write(json.dumps(session, ensure_ascii=False) + "\n")
            fh.write(json.dumps(turn_rec, ensure_ascii=False) + "\n")
        digest = "\n".join([
            f"# Oracle consultation: {topic}",
            "",
            f"- lane: {lane}",
            f"- conversation_id: {conv.get('conversation_id', '')}",
            f"- closed_reason: backfilled_substantive_server_response",
            f"- pdf_attached: True",
            f"- turns: 1",
            "",
            "## Turn 0",
            "",
            "Response:",
            "",
            "```text",
            response,
            "```",
            "",
        ])
        base.with_suffix(".md").write_text(digest + "\n", encoding="utf-8")
        eid = f"event.{hashlib.sha256((topic + created).encode()).hexdigest()[:16]}"
        subject_id = f"{lane}.{hashlib.sha256(topic.encode()).hexdigest()[:12]}"
        event = {
            "event_id": eid,
            "event_kind": "oracle_consultation_completed",
            "source": lane,
            "subject_kind": "oracle_consultation",
            "subject_id": subject_id,
            "reason": "backfilled from server-side ChatGPT response",
            "payload": {
                "lane": lane,
                "topic": topic,
                "intended_claim_id": "",
                "conversation_id": conv.get("conversation_id", ""),
                "turns": len(turns),
                "closed_reason": "backfilled_substantive_server_response",
                "max_turns_reached": False,
            },
            "stable_event_key": f"oracle_consultation_completed::oracle_consultation::{subject_id}",
            "status": "open",
            "created_at": now_iso(),
        }
        existing_events = store.load_events()
        if not any(e.get("stable_event_key") == event["stable_event_key"] for e in existing_events):
            events_path.parent.mkdir(parents=True, exist_ok=True)
            with events_path.open("a", encoding="utf-8") as fh:
                fh.write(json.dumps(event, ensure_ascii=False) + "\n")
            summary["backfilled"] += 1
        else:
            summary["skipped_present"] += 1
    return summary


def run_gate_lane(store: BioRealityStore) -> dict[str, Any]:
    summary = bio_reality_loop.run_once(store)
    oracle_summary = _maybe_run_bio_g_oracle(store)
    return {"lane": "bio-G", **summary, **oracle_summary}


def _load_pipeline_config() -> dict[str, Any]:
    try:
        data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _load_oracle_integration_config() -> dict[str, Any]:
    config = _load_pipeline_config().get("oracle_integration")
    return config if isinstance(config, dict) else {}


def _repo_root_from_store(store: BioRealityStore) -> Path:
    return Path(store.paths.root).resolve().parent.parent


def _resolve_repo_path(repo_root: Path, value: Any) -> Path:
    path = Path(str(value or ""))
    return path if path.is_absolute() else repo_root / path


def _oracle_state_path(store: BioRealityStore) -> Path:
    events_parent = store.paths.events.parent
    if events_parent.name == "out":
        return events_parent.parent / "state" / "oracle_integration.json"
    return events_parent / "state" / "oracle_integration.json"


def _read_oracle_state(store: BioRealityStore) -> dict[str, Any]:
    return _read_json_object(_oracle_state_path(store))


def _write_oracle_state(store: BioRealityStore, state: dict[str, Any]) -> None:
    path = _oracle_state_path(store)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_iso_seconds(value: Any) -> float:
    try:
        text = str(value or "")
        if text.endswith("Z"):
            text = text[:-1] + "+00:00"
        return datetime.fromisoformat(text).timestamp()
    except (TypeError, ValueError):
        return 0.0


def _event_subject_id(lane: str, topic: str) -> str:
    return f"{lane}.{hashlib.sha256(topic.encode('utf-8')).hexdigest()[:12]}"


def _append_oracle_event(
    store: BioRealityStore,
    lane: str,
    topic: str,
    result: dict[str, Any],
    *,
    intended_claim_id: str = "",
    reason: str = "",
) -> None:
    event = agent_bus._event(
        "oracle_consultation_completed",
        lane,
        "oracle_consultation",
        _event_subject_id(lane, topic),
        reason or str(result.get("closed_reason") or "oracle consultation completed"),
        {
            "lane": lane,
            "topic": topic,
            "intended_claim_id": intended_claim_id,
            "conversation_id": result.get("conversation_id"),
            "turns": len(result.get("turns") if isinstance(result.get("turns"), list) else []),
            "closed_reason": result.get("closed_reason"),
            "max_turns_reached": result.get("max_turns_reached"),
            "pdf_attached": bool(result.get("pdf_attached")),
            "pdf_skipped_reason": result.get("pdf_skipped_reason") or "",
            "judge_calls": int(result.get("judge_calls") or 0),
            "transcript_jsonl": result.get("transcript_jsonl"),
            "transcript_md": result.get("transcript_md"),
        },
    )
    store.write_events(agent_bus._dedup(store.load_events() + [event], "event_id"))


def _oracle_skip(reason: str) -> dict[str, Any]:
    return {"oracle_consultations": 0, "oracle_turns_total": 0, "oracle_skipped_reason": reason}


def _turn_count(result: dict[str, Any]) -> int:
    turns = result.get("turns")
    return len(turns) if isinstance(turns, list) else 0


def _gate_candidate_priority(result: dict[str, Any]) -> tuple[float, str, str]:
    try:
        priority = float(result.get("priority_score"))
    except (TypeError, ValueError):
        priority = 0.0
    failed = str(result.get("failed_at") or result.get("created_at") or result.get("updated_at") or "")
    return (priority, failed, str(result.get("packet_id") or result.get("claim_id") or ""))


def _has_concern_flag(result: dict[str, Any]) -> bool:
    if result.get("concern_flag"):
        return True
    flags = result.get("concern_flags")
    return isinstance(flags, list) and bool(flags)


def _select_bio_g_oracle_candidate(gate_results: list[dict[str, Any]]) -> dict[str, Any] | None:
    candidates = [
        result
        for result in gate_results
        if isinstance(result, dict)
        and (
            str(result.get("verdict") or "") == "needs_review"
            or str(result.get("gate_status") or "") == "gate_blocked"
            or _has_concern_flag(result)
        )
    ]
    if not candidates:
        return None
    return sorted(candidates, key=_gate_candidate_priority)[0]


def _compact_json(value: Any, *, limit: int = 3000) -> str:
    text = json.dumps(value, ensure_ascii=False, sort_keys=True)
    if len(text) <= limit:
        return text
    return text[: limit - 3] + "..."


def _conjecture_by_id(store: BioRealityStore, conjecture_id: str) -> dict[str, Any]:
    for conjecture in store.load_conjectures():
        if str(conjecture.get("conjecture_id") or "") == conjecture_id:
            return conjecture
    return {}


def _oracle_linked_records_for_conjecture(store: BioRealityStore, conjecture: dict[str, Any]) -> dict[str, Any]:
    contact_refs = {str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)}
    probe_refs = {str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)}
    contacts = [contact for contact in store.load_contacts() if str(contact.get("contact_id") or "") in contact_refs]
    probes = [probe for probe in store.load_probes() if str(probe.get("probe_id") or "") in probe_refs]
    mismatches = [
        mismatch
        for mismatch in store.load_mismatches()
        if str(mismatch.get("probe_ref") or "") in probe_refs
        or str(mismatch.get("contact_ref") or "") in contact_refs
    ]
    return {"reality_contacts": contacts, "probes": probes, "mismatches": mismatches}


def _namecert_proposal_text(store: BioRealityStore, claim_id: str) -> str:
    path = store.paths.namecert_proposals_dir / f"{claim_id}.md"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return ""
    return text[:4000]


def _bio_g_initial_prompt(store: BioRealityStore, candidate: dict[str, Any]) -> tuple[str, str]:
    claim_id = str(candidate.get("claim_id") or candidate.get("packet_id") or "")
    conjecture = _conjecture_by_id(store, claim_id) if str(candidate.get("packet_kind") or "") == "conjecture" else {}
    form = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
    verified_facts = {
        "gate_result": candidate,
        "conjecture": conjecture,
    }
    linked = _oracle_linked_records_for_conjecture(store, conjecture) if conjecture else {"reality_contacts": [], "probes": [], "mismatches": []}
    minimal_form = {
        "carrier": form.get("carrier") if isinstance(form, dict) else "",
        "distinctions": form.get("distinctions") if isinstance(form, dict) else [],
        "readback": form.get("readback") if isinstance(form, dict) else "",
        "internal_structure": form.get("internal_structure") if isinstance(form, dict) else [],
    }
    prompt = "\n".join(
        [
            "Review the BEDC minimal form for this BioReality gate candidate.",
            f"claim_id: {claim_id}",
            "",
            "current verified_facts compact JSON:",
            _compact_json(verified_facts),
            "",
            "bio-namer markdown proposal if present:",
            _namecert_proposal_text(store, claim_id) or "none",
            "",
            "BEDC minimal-form summary:",
            _compact_json(minimal_form),
            "",
            "reality contacts and probes:",
            _compact_json(linked),
            "",
            "Question: Is the carrier truly minimal? Are there dependency leaks or unjustified internal structure? "
            "Is the closure boundary correct? Propose concrete refinement steps if any.",
        ]
    )
    return claim_id, prompt


def _select_bio_g_rotation_candidate(
    gate_results: list[dict[str, Any]],
    lane_state: dict[str, Any],
    store: BioRealityStore | None = None,
) -> dict[str, Any] | None:
    # Only rotate through conjecture packets — mismatch/probe gate_results carry no BEDC
    # minimal form, so asking ChatGPT to deep-review them produces an empty-prompt session
    # that simply burns the poll timeout. Also require the linked conjecture to expose at
    # least a carrier so the review has something concrete to anchor on.
    eligible: list[dict[str, Any]] = []
    conjectures_by_id: dict[str, dict[str, Any]] = {}
    if store is not None:
        for c in store.load_conjectures():
            cid = str(c.get("conjecture_id") or "")
            if cid:
                conjectures_by_id[cid] = c
    for result in gate_results:
        if not isinstance(result, dict):
            continue
        if str(result.get("gate_status") or "") != "gate_passed":
            continue
        if str(result.get("packet_kind") or "") != "conjecture":
            continue
        packet_id = str(result.get("claim_id") or result.get("packet_id") or "")
        if not packet_id:
            continue
        conjecture = conjectures_by_id.get(packet_id, {})
        form = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
        if not form.get("carrier"):
            continue
        eligible.append(result)
    if not eligible:
        return None
    consulted = lane_state.get("consulted_claim_ids") if isinstance(lane_state.get("consulted_claim_ids"), dict) else {}
    def sort_key(result: dict[str, Any]) -> tuple[str, str]:
        cid = str(result.get("claim_id") or result.get("packet_id") or "")
        return (str(consulted.get(cid) or ""), cid)
    return sorted(eligible, key=sort_key)[0]


def _maybe_run_bio_g_oracle(store: BioRealityStore) -> dict[str, Any]:
    config = _load_oracle_integration_config()
    lane_config = config.get("bio_g") if isinstance(config.get("bio_g"), dict) else {}
    if not config.get("enabled", False) or not lane_config.get("enabled", False):
        return _oracle_skip("disabled")
    gate_results = read_jsonl(store.paths.gate_results)
    state = _read_oracle_state(store)
    lane_state = state.get("bio-G") if isinstance(state.get("bio-G"), dict) else {}
    candidate = _select_bio_g_oracle_candidate(gate_results)
    rotation_used = False
    if candidate is None:
        candidate = _select_bio_g_rotation_candidate(gate_results, lane_state, store)
        rotation_used = candidate is not None
    if candidate is None:
        return _oracle_skip("no_candidate")
    min_seconds = float(lane_config.get("min_seconds_between_consultations") or 0)
    last_at = _parse_iso_seconds(lane_state.get("last_consulted_at"))
    if min_seconds > 0 and last_at > 0 and time.time() - last_at < min_seconds:
        return _oracle_skip("rate_limited")
    repo_root = _repo_root_from_store(store)
    pdf_path = _resolve_repo_path(repo_root, config.get("pdf_attach_path") or "")
    if not pdf_path.exists():
        pdf_path = None
    persist_dir = _resolve_repo_path(repo_root, config.get("persist_dir") or "tools/bio_reality/state/oracle_sessions")
    server_url = str(config.get("server_url") or "http://127.0.0.1:8769")
    server_host, server_port = _parse_server_host_port(server_url)
    if server_host and server_port and not _localhost_available(server_host, server_port):
        return _oracle_skip("oracle_server_unreachable")
    if not _network_available():
        return _oracle_skip("network_unreachable")
    claim_id, prompt = _bio_g_initial_prompt(store, candidate)
    topic = f"bio-G.review.{claim_id}"
    topic_conversations = lane_state.get("topic_conversations") if isinstance(lane_state.get("topic_conversations"), dict) else {}
    existing_conv_id = str(topic_conversations.get(topic) or "")
    result = oracle_consultation.run_oracle_consultation(
        repo_root,
        "bio-G",
        topic,
        prompt,
        intended_claim_id=claim_id,
        pdf_path=pdf_path,
        max_turns=int(lane_config.get("max_turns") or 10),
        persist_dir=persist_dir,
        server_url=str(config.get("server_url") or "http://127.0.0.1:8769"),
        poll_timeout=int(lane_config.get("poll_timeout_seconds") or 600),
        codex_judge_timeout=int(lane_config.get("codex_judge_timeout_seconds") or 240),
        existing_conversation_id=existing_conv_id,
        close_on_exit=False,
    )
    lane_state.update({"last_consulted_at": now_iso(), "last_topic": topic, "last_claim_id": claim_id})
    consulted_map = lane_state.get("consulted_claim_ids") if isinstance(lane_state.get("consulted_claim_ids"), dict) else {}
    consulted_map[claim_id] = now_iso()
    lane_state["consulted_claim_ids"] = consulted_map
    new_conv_id = str(result.get("conversation_id") or "") if isinstance(result, dict) else ""
    if new_conv_id:
        topic_conversations[topic] = new_conv_id
        lane_state["topic_conversations"] = topic_conversations
    state["bio-G"] = lane_state
    _write_oracle_state(store, state)
    _append_oracle_event(store, "bio-G", topic, result, intended_claim_id=claim_id, reason=("rotation_deep_review" if rotation_used else ""))
    return {"oracle_consultations": 1, "oracle_turns_total": _turn_count(result), "oracle_skipped_reason": "", "oracle_rotation_used": rotation_used, "oracle_resumed": bool(existing_conv_id)}


def _load_claims_document(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": "bio-reality-claims-v1", "claims": []}
    if not isinstance(data, dict):
        return {"version": "bio-reality-claims-v1", "claims": []}
    claims = data.get("claims")
    if not isinstance(claims, list):
        data["claims"] = []
    return data


def _load_experiments_document(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"version": "bio-reality-experiments-v1", "experiments": []}
    if not isinstance(data, dict):
        return {"version": "bio-reality-experiments-v1", "experiments": []}
    experiments = data.get("experiments")
    if not isinstance(experiments, list):
        data["experiments"] = []
    return data


def _open_event_keys(events: list[dict[str, Any]]) -> set[tuple[str, str]]:
    return {
        (str(event.get("event_kind") or ""), str(event.get("subject_id") or ""))
        for event in events
        if str(event.get("status") or "open") == "open"
    }


def _failed_check_name(run: dict[str, Any]) -> str:
    checks = run.get("checks")
    if not isinstance(checks, list):
        return ""
    for check in checks:
        if not isinstance(check, dict):
            continue
        if check.get("passed") is False:
            name = str(check.get("name") or "")
            if name:
                return name
    return ""


def _brief_run(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "experiment_run_id": record.get("experiment_run_id"),
        "completed_at": record.get("completed_at"),
        "status": record.get("status"),
        "failed_check": _failed_check_name(record),
    }


def _namecert_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.namecert_lane_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.namecert_lane_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _string_tokens(value: Any) -> set[str]:
    text = json.dumps(value, ensure_ascii=False, sort_keys=True) if isinstance(value, (dict, list)) else str(value or "")
    tokens: set[str] = set()
    current: list[str] = []
    for char in text.lower():
        if char.isalnum():
            current.append(char)
        else:
            if len(current) >= 2:
                tokens.add("".join(current))
            current = []
    if len(current) >= 2:
        tokens.add("".join(current))
    return tokens


def _claim_match_tokens(claim: dict[str, Any]) -> set[str]:
    fields = [
        claim.get("claim_id"),
        claim.get("statement"),
        claim.get("bedc_minimal_form"),
        claim.get("bedc_form"),
        claim.get("experiment_id"),
    ]
    tokens: set[str] = set()
    for field in fields:
        tokens.update(_string_tokens(field))
    if "q6" in tokens:
        tokens.add("q")
        tokens.add("6")
    return tokens


def _conjecture_match_tokens(conjecture: dict[str, Any]) -> set[str]:
    bedc = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
    fields = [
        conjecture.get("conjecture_id"),
        conjecture.get("biological_object"),
        conjecture.get("informal_statement"),
        bedc.get("carrier") if isinstance(bedc, dict) else None,
        bedc.get("distinctions") if isinstance(bedc, dict) else None,
        bedc.get("readback") if isinstance(bedc, dict) else None,
        bedc.get("internal_structure") if isinstance(bedc, dict) else None,
        conjecture.get("probe_refs"),
    ]
    tokens: set[str] = set()
    for field in fields:
        tokens.update(_string_tokens(field))
    if "q6" in tokens:
        tokens.add("q")
        tokens.add("6")
    return tokens


def _latest_passed_run_for_claim(claim: dict[str, Any], runs: list[dict[str, Any]]) -> dict[str, Any] | None:
    claim_id = str(claim.get("claim_id") or "")
    experiment_id = str(claim.get("experiment_id") or "")
    candidates = [
        run
        for run in runs
        if str(run.get("status") or "") == "passed"
        and (
            (claim_id and str(run.get("claim_id") or "") == claim_id)
            or (experiment_id and str(run.get("experiment_id") or "") == experiment_id)
        )
    ]
    if not candidates:
        return None
    candidates.sort(key=lambda run: str(run.get("completed_at") or run.get("started_at") or ""), reverse=True)
    return candidates[0]


def _verified_facts_from_run(run: dict[str, Any]) -> dict[str, Any]:
    values: dict[str, Any] = {}
    checks = run.get("checks")
    if isinstance(checks, list):
        for check in checks:
            if not isinstance(check, dict):
                continue
            name = str(check.get("name") or "")
            if name and "actual" in check:
                values[name] = check.get("actual")
    result = run.get("result")
    if isinstance(result, dict):
        for key, value in result.items():
            if isinstance(value, (str, int, float, bool)) or value is None:
                values[str(key)] = value
    return values


def _find_matching_conjecture(
    claim: dict[str, Any],
    conjectures: list[dict[str, Any]],
    runs: list[dict[str, Any]],
) -> dict[str, Any] | None:
    linked_id = str(claim.get("linked_conjecture_id") or "")
    if linked_id:
        for conjecture in conjectures:
            if str(conjecture.get("conjecture_id") or "") == linked_id:
                return conjecture

    experiment_id = str(claim.get("experiment_id") or "")
    experiment_run_probe_tokens: set[str] = set()
    for run in runs:
        if experiment_id and str(run.get("experiment_id") or "") == experiment_id:
            experiment_run_probe_tokens.update(_string_tokens(run.get("probe_id")))
            experiment_run_probe_tokens.update(_string_tokens(run.get("probe_ref")))
            experiment_run_probe_tokens.update(_string_tokens(run.get("probe_refs")))

    claim_tokens = _claim_match_tokens(claim)
    strong_terms = {"codon", "q6", "median", "med", "spectrum", "reassignment", "genetic", "table", "boundary"}
    best: tuple[int, str, dict[str, Any]] | None = None
    for conjecture in conjectures:
        probe_refs = {
            str(item)
            for item in conjecture.get("probe_refs", [])
            if isinstance(item, str) and item
        }
        score = 0
        if experiment_run_probe_tokens and (experiment_run_probe_tokens & _string_tokens(probe_refs)):
            score += 8
        conjecture_tokens = _conjecture_match_tokens(conjecture)
        overlap = claim_tokens & conjecture_tokens
        score += len(overlap)
        score += 3 * len(overlap & strong_terms)
        if score <= 0:
            continue
        candidate = (score, str(conjecture.get("conjecture_id") or ""), conjecture)
        if best is None or candidate[0] > best[0] or (candidate[0] == best[0] and candidate[1] < best[1]):
            best = candidate
    return best[2] if best is not None else None


def _loning_naming_hint(claim: dict[str, Any], conjecture: dict[str, Any]) -> str:
    tokens = _claim_match_tokens(claim) | _conjecture_match_tokens(conjecture)
    if {"q6", "median", "med"} & tokens:
        return "BioRealityQSix"
    if "codon" in tokens and ("spectrum" in tokens or "reassignment" in tokens):
        return "EmpiricalCodonSpectrum"
    if "table" in tokens or "genetic" in tokens:
        return "CuratedGeneticTableLedger"
    if "codon" in tokens:
        return "RealityBoundCodonTopology"
    return "BioReality"


def _proposal_exists(store: BioRealityStore, claim_id: str) -> bool:
    return (store.paths.namecert_proposals_dir / f"{claim_id}.md").exists()


def _experiment_claim_index(claims: list[dict[str, Any]], experiments: list[dict[str, Any]]) -> dict[str, str]:
    claim_by_experiment = {
        str(claim.get("experiment_id") or ""): str(claim.get("claim_id") or "")
        for claim in claims
        if claim.get("experiment_id") and claim.get("claim_id")
    }
    for experiment in experiments:
        experiment_id = str(experiment.get("experiment_id") or "")
        claim_id = str(experiment.get("claim_id") or "")
        if experiment_id and claim_id:
            claim_by_experiment[experiment_id] = claim_id
    return claim_by_experiment


def _passed_claim_summary(claims: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "claim_id": claim.get("claim_id"),
            "phase": claim.get("phase"),
            "hypothesis_level": claim.get("hypothesis_level"),
            "statement": claim.get("statement") or claim.get("informal_statement") or "",
            "experiment_id": claim.get("experiment_id") or "",
        }
        for claim in claims
        if str(claim.get("status") or "") == "passed"
    ]


def _current_phase(claims: list[dict[str, Any]], phases_passed: list[int]) -> int | str:
    if phases_passed:
        return max(phases_passed) + 1
    open_phases: list[int] = []
    for claim in claims:
        if str(claim.get("status") or "") == "passed":
            continue
        try:
            open_phases.append(int(claim.get("phase")))
        except (TypeError, ValueError):
            continue
    if open_phases:
        return min(open_phases)
    numeric_phases: list[int] = []
    for claim in claims:
        try:
            numeric_phases.append(int(claim.get("phase")))
        except (TypeError, ValueError):
            continue
    return max(numeric_phases) if numeric_phases else "unknown"


def _bio_plan_trigger(new_events: list[dict[str, Any]]) -> dict[str, Any] | None:
    for event in new_events:
        if event.get("event_kind") == "phase_advance_proposed":
            return event
    for event in new_events:
        if event.get("event_kind") == "claim_redesign_proposed":
            return event
    return None


def _bio_plan_prompt(
    claims: list[dict[str, Any]],
    phases_passed: list[int],
    trigger_event: dict[str, Any],
) -> tuple[str, str, str]:
    event_kind = str(trigger_event.get("event_kind") or "")
    payload = trigger_event.get("payload") if isinstance(trigger_event.get("payload"), dict) else {}
    phase = _current_phase(claims, phases_passed)
    common = {
        "passed_claims": _passed_claim_summary(claims),
        "current_phase": phase,
    }
    if event_kind == "phase_advance_proposed":
        subject_id = str(trigger_event.get("subject_id") or payload.get("phase") or phase)
        topic = f"bio-Plan.phase.{subject_id}.next"
        question = "What's the strongest next experiment for the newly opened phase?"
        body = {"trigger": trigger_event, **common}
        return topic, "", "\n".join([question, "", "Planning context:", _compact_json(body)])
    claim_id = str(payload.get("claim_id") or trigger_event.get("subject_id") or "")
    topic = f"bio-Plan.stuck.{claim_id or trigger_event.get('subject_id')}"
    question = f"How to refine null model / strengthen control for stuck claim {claim_id or 'unknown'}?"
    body = {"trigger": trigger_event, "stuck_claim_record": payload, **common}
    return topic, claim_id, "\n".join([question, "", "Planning context:", _compact_json(body)])


def _maybe_run_bio_plan_oracle(
    store: BioRealityStore,
    claims: list[dict[str, Any]],
    phases_passed: list[int],
    trigger_event: dict[str, Any] | None,
) -> dict[str, Any]:
    config = _load_oracle_integration_config()
    lane_config = config.get("bio_plan") if isinstance(config.get("bio_plan"), dict) else {}
    state = _read_oracle_state(store)
    lane_state = state.get("bio-Plan") if isinstance(state.get("bio-Plan"), dict) else {}
    cycle = int(lane_state.get("cycle") or 0) + 1
    lane_state["cycle"] = cycle
    state["bio-Plan"] = lane_state
    _write_oracle_state(store, state)
    if not config.get("enabled", False) or not lane_config.get("enabled", False):
        return _oracle_skip("disabled")
    if trigger_event is None:
        return _oracle_skip("no_topic")
    min_cycles = int(lane_config.get("min_cycles_between_consultations") or 0)
    last_cycle = int(lane_state.get("last_consulted_cycle") or 0)
    if min_cycles > 0 and last_cycle > 0 and cycle - last_cycle < min_cycles:
        return _oracle_skip("rate_limited")
    repo_root = _repo_root_from_store(store)
    pdf_path = _resolve_repo_path(repo_root, config.get("pdf_attach_path") or "")
    if not pdf_path.exists():
        pdf_path = None
    persist_dir = _resolve_repo_path(repo_root, config.get("persist_dir") or "tools/bio_reality/state/oracle_sessions")
    server_url = str(config.get("server_url") or "http://127.0.0.1:8769")
    server_host, server_port = _parse_server_host_port(server_url)
    if server_host and server_port and not _localhost_available(server_host, server_port):
        return _oracle_skip("oracle_server_unreachable")
    if not _network_available():
        return _oracle_skip("network_unreachable")
    topic, claim_id, prompt = _bio_plan_prompt(claims, phases_passed, trigger_event)
    topic_conversations = lane_state.get("topic_conversations") if isinstance(lane_state.get("topic_conversations"), dict) else {}
    existing_conv_id = str(topic_conversations.get(topic) or "")
    result = oracle_consultation.run_oracle_consultation(
        repo_root,
        "bio-Plan",
        topic,
        prompt,
        intended_claim_id=claim_id,
        pdf_path=pdf_path,
        max_turns=int(lane_config.get("max_turns") or 12),
        persist_dir=persist_dir,
        server_url=str(config.get("server_url") or "http://127.0.0.1:8769"),
        poll_timeout=int(lane_config.get("poll_timeout_seconds") or 600),
        codex_judge_timeout=int(lane_config.get("codex_judge_timeout_seconds") or 240),
        existing_conversation_id=existing_conv_id,
        close_on_exit=False,
    )
    lane_state.update({"last_consulted_at": now_iso(), "last_consulted_cycle": cycle, "last_topic": topic})
    new_conv_id = str(result.get("conversation_id") or "") if isinstance(result, dict) else ""
    if new_conv_id:
        topic_conversations[topic] = new_conv_id
        lane_state["topic_conversations"] = topic_conversations
    state["bio-Plan"] = lane_state
    _write_oracle_state(store, state)
    _append_oracle_event(store, "bio-Plan", topic, result, intended_claim_id=claim_id)
    return {"oracle_consultations": 1, "oracle_turns_total": _turn_count(result), "oracle_skipped_reason": "", "oracle_resumed": bool(existing_conv_id)}


def run_plan_lane(store: BioRealityStore) -> dict[str, Any]:
    """Detect phase-advance and stuck-claim signals, emit events for bio-R."""
    claims_document = _load_claims_document(store.paths.claims_registry)
    experiments_document = _load_experiments_document(store.paths.experiments_registry)
    claims = [
        item
        for item in claims_document.get("claims", [])
        if isinstance(item, dict) and str(item.get("hypothesis_level") or "") != "meta"
    ]
    experiments = [item for item in experiments_document.get("experiments", []) if isinstance(item, dict)]
    existing_events = store.load_events()
    open_event_keys = _open_event_keys(existing_events)
    new_events: list[dict[str, Any]] = []
    phases_passed: list[int] = []

    claims_by_phase: dict[int, list[dict[str, Any]]] = {}
    for claim in claims:
        phase_value = claim.get("phase")
        try:
            phase = int(phase_value)
        except (TypeError, ValueError):
            continue
        claims_by_phase.setdefault(phase, []).append(claim)

    for phase in sorted(claims_by_phase):
        group = claims_by_phase[phase]
        if not group or not all(str(claim.get("status") or "") == "passed" for claim in group):
            continue
        phases_passed.append(phase)
        if ("phase_advance_proposed", str(phase)) in open_event_keys:
            continue
        new_events.append(
            agent_bus._event(
                "phase_advance_proposed",
                "bio-Plan",
                "phase",
                str(phase),
                f"all {len(group)} claim(s) at phase {phase} passed; propose next phase",
                {"phase": phase, "passed_claims": [str(claim.get("claim_id") or "") for claim in group]},
            )
        )
        open_event_keys.add(("phase_advance_proposed", str(phase)))

    claim_by_id = {
        str(claim.get("claim_id") or ""): claim
        for claim in claims
        if claim.get("claim_id")
    }
    claim_id_by_experiment = _experiment_claim_index(claims, experiments)
    runs_by_experiment: dict[str, list[dict[str, Any]]] = {}
    for run in read_jsonl(store.paths.experiment_runs):
        experiment_id = str(run.get("experiment_id") or "")
        if experiment_id:
            runs_by_experiment.setdefault(experiment_id, []).append(run)

    stuck_statuses = {"failed", "error", "timeout"}
    for experiment_id in sorted(runs_by_experiment):
        runs = sorted(
            runs_by_experiment[experiment_id],
            key=lambda record: str(record.get("completed_at") or record.get("started_at") or ""),
            reverse=True,
        )
        recent = runs[:3]
        if len(recent) < 3:
            continue
        statuses = {str(run.get("status") or "") for run in recent}
        if not statuses <= stuck_statuses:
            continue
        claim_id = claim_id_by_experiment.get(experiment_id) or str(recent[0].get("claim_id") or "")
        claim = claim_by_id.get(claim_id, {})
        if not claim_id or str(claim.get("status") or "") == "passed":
            continue
        if ("claim_redesign_proposed", experiment_id) in open_event_keys:
            continue
        failed_checks = [_failed_check_name(run) for run in recent if _failed_check_name(run)]
        check_name = failed_checks[0] if failed_checks else ""
        distinct_checks = sorted(set(failed_checks))
        reason = (
            f"experiment {experiment_id} status failed in last 3 runs; "
            f"failed checks observed: {', '.join(distinct_checks) or 'unspecified'}"
        )
        new_events.append(
            agent_bus._event(
                "claim_redesign_proposed",
                "bio-Plan",
                "experiment",
                experiment_id,
                reason,
                {
                    "experiment_id": experiment_id,
                    "claim_id": claim_id,
                    "failed_check": check_name,
                    "failed_checks_distinct": distinct_checks,
                    "recent_runs": [_brief_run(run) for run in recent],
                },
            )
        )
        open_event_keys.add(("claim_redesign_proposed", experiment_id))

    phase_advance_events = sum(1 for event in new_events if event.get("event_kind") == "phase_advance_proposed")
    stuck_redesign_events = sum(1 for event in new_events if event.get("event_kind") == "claim_redesign_proposed")
    trigger_event = _bio_plan_trigger(new_events)
    merged = agent_bus._dedup(existing_events + new_events, "event_id")
    store.write_events(merged)
    oracle_summary = _maybe_run_bio_plan_oracle(store, claims, phases_passed, trigger_event)
    return {
        "lane": "bio-Plan",
        "phase_advance_events": phase_advance_events,
        "stuck_redesign_events": stuck_redesign_events,
        "phases_passed": phases_passed,
        **oracle_summary,
    }


def _history_entry(status: str, reason: str, **extra: Any) -> dict[str, Any]:
    entry = {"ts": now_iso(), "status": status, "reason": reason}
    entry.update(extra)
    return entry


def _claim_state_counts(claims: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for claim in claims:
        status = str(claim.get("status") or "open")
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _run_id(result: dict[str, Any]) -> str:
    material = json.dumps(result, sort_keys=True, ensure_ascii=True)
    return hashlib.sha256(material.encode("utf-8")).hexdigest()[:12]


def _check_summary(checks: Any) -> dict[str, int]:
    if not isinstance(checks, list):
        return {"total": 0, "passed": 0, "failed": 0}
    total = sum(1 for item in checks if isinstance(item, dict))
    passed = sum(1 for item in checks if isinstance(item, dict) and item.get("passed") is True)
    return {"total": total, "passed": passed, "failed": total - passed}


def _missing_required_data(repo_root: Path, experiment: dict[str, Any]) -> list[str]:
    required = experiment.get("required_data")
    if not isinstance(required, list):
        return []
    missing: list[str] = []
    for item in required:
        if not isinstance(item, str) or not item:
            continue
        path = Path(item)
        if path.is_absolute() or not (repo_root / path).exists():
            missing.append(item)
    return missing


def _write_claims_document(path: Path, document: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2, ensure_ascii=False, sort_keys=False) + "\n", encoding="utf-8")


def _experiment_changed_since_last_history(
    claim: dict[str, Any],
    experiment: dict[str, Any],
    repo_root: Path,
    experiments_registry: Path,
) -> bool:
    """Return True if the experiment script or its registry entry has been
    modified after the most recent claim.history timestamp. Used to promote
    a failed/error claim back to needs_rerun when bio-planner reshapes the
    experiment."""
    from datetime import datetime
    history = claim.get("history")
    if not isinstance(history, list) or not history:
        return False
    last = history[-1] if isinstance(history[-1], dict) else None
    if not last:
        return False
    last_ts_text = str(last.get("ts") or "")
    if not last_ts_text:
        return False
    try:
        last_ts = datetime.fromisoformat(last_ts_text).timestamp()
    except ValueError:
        return False
    script_path = experiment.get("script_path")
    candidates: list[Path] = []
    if isinstance(script_path, str) and script_path:
        candidates.append(repo_root / script_path)
    if experiments_registry.exists():
        candidates.append(experiments_registry)
    for path in candidates:
        try:
            mtime = path.stat().st_mtime
        except OSError:
            continue
        if mtime > last_ts + 0.5:
            return True
    return False


def run_execute_lane(store: BioRealityStore) -> dict[str, Any]:
    claims_document = _load_claims_document(store.paths.claims_registry)
    experiments_document = _load_experiments_document(store.paths.experiments_registry)
    claims = [item for item in claims_document.get("claims", []) if isinstance(item, dict)]
    experiments = [item for item in experiments_document.get("experiments", []) if isinstance(item, dict)]
    experiment_by_id = {
        str(experiment.get("experiment_id") or ""): experiment
        for experiment in experiments
        if experiment.get("experiment_id")
    }
    claim_by_id = {
        str(claim.get("claim_id") or ""): claim
        for claim in claims
        if claim.get("claim_id")
    }
    repo_root = SCRIPT_DIR.parent.parent
    summary = {
        "lane": "bio-X",
        "executed": 0,
        "passed_this_cycle": 0,
        "failed_this_cycle": 0,
        "needs_data_this_cycle": 0,
        "error_this_cycle": 0,
        "skipped_unmet_dep": 0,
        "claim_states": {},
    }

    for claim in claims:
        status = str(claim.get("status") or "open")
        experiment_id = str(claim.get("experiment_id") or "")
        experiment = experiment_by_id.get(experiment_id)
        if status not in {"open", "needs_rerun"}:
            if status in {"failed", "error"} and experiment is not None and _experiment_changed_since_last_history(claim, experiment, repo_root, store.paths.experiments_registry):
                claim["status"] = "needs_rerun"
                status = "needs_rerun"
                history = claim.setdefault("history", [])
                if isinstance(history, list):
                    history.append(_history_entry("needs_rerun", "experiment script or acceptance changed since last run"))
            else:
                continue
        if experiment is None:
            continue
        dependencies = [str(item) for item in claim.get("depends_on", []) if isinstance(item, str)]
        unmet = [dep for dep in dependencies if str(claim_by_id.get(dep, {}).get("status") or "") != "passed"]
        if unmet:
            history = claim.setdefault("history", [])
            if isinstance(history, list):
                history.append(_history_entry("skipped", "skipped due to unmet dependency", unmet_dependencies=unmet))
            summary["skipped_unmet_dep"] += 1
            continue
        missing_data = _missing_required_data(repo_root, experiment)
        if missing_data:
            claim["status"] = "needs_data"
            history = claim.setdefault("history", [])
            if isinstance(history, list):
                history.append(_history_entry("needs_data", "missing required_data", missing_data=missing_data))
            result = {
                "experiment_id": experiment_id,
                "claim_id": str(claim.get("claim_id") or ""),
                "started_at": now_iso(),
                "completed_at": now_iso(),
                "status": "needs_data",
                "checks": [],
                "result": {"missing_data": missing_data},
                "stdout_tail": "",
                "stderr_tail": "",
                "returncode": None,
            }
            result["experiment_run_id"] = _run_id(result)
            append_jsonl(store.paths.experiment_runs, [result])
            summary["needs_data_this_cycle"] += 1
            continue
        timeout = int(experiment.get("timeout_seconds") or 300)
        result = experiment_runner.run_experiment(experiment, timeout_seconds=timeout, repo_root=repo_root)
        result["experiment_run_id"] = _run_id(result)
        append_jsonl(store.paths.experiment_runs, [result])
        summary["executed"] += 1
        result_status = str(result.get("status") or "error")
        if result_status == "passed":
            claim["status"] = "passed"
            summary["passed_this_cycle"] += 1
        elif result_status == "failed":
            claim["status"] = "failed"
            summary["failed_this_cycle"] += 1
        elif result_status == "needs_data":
            claim["status"] = "needs_data"
            summary["needs_data_this_cycle"] += 1
        else:
            claim["status"] = "error"
            summary["error_this_cycle"] += 1
        history = claim.setdefault("history", [])
        if isinstance(history, list):
            history.append(
                _history_entry(
                    str(claim.get("status") or "error"),
                    "experiment result",
                    experiment_run_id=result["experiment_run_id"],
                    checks=_check_summary(result.get("checks")),
                )
            )

    claims_document["claims"] = claims
    _write_claims_document(store.paths.claims_registry, claims_document)
    summary["claim_states"] = _claim_state_counts(claims)
    return summary


def run_namecert_lane(store: BioRealityStore) -> dict[str, Any]:
    claims_document = _load_claims_document(store.paths.claims_registry)
    claims = [item for item in claims_document.get("claims", []) if isinstance(item, dict)]
    conjectures = store.load_conjectures()
    runs = read_jsonl(store.paths.experiment_runs)
    passed_claims = [claim for claim in claims if str(claim.get("status") or "") == "passed"]
    summary = {
        "lane": "bio-N",
        "passed_claims_scanned": len(passed_claims),
        "newly_linked": 0,
        "verified_facts_updated": 0,
        "proposal_events_emitted": 0,
        "skipped_no_match": 0,
    }
    new_events: list[dict[str, Any]] = []

    for claim in passed_claims:
        claim_id = str(claim.get("claim_id") or "")
        if not claim_id:
            continue
        had_link = bool(str(claim.get("linked_conjecture_id") or ""))
        conjecture = _find_matching_conjecture(claim, conjectures, runs)
        if conjecture is None:
            summary["skipped_no_match"] += 1
            _namecert_log(store, "no_linked_conjecture", {"claim_id": claim_id})
            continue
        latest_run = _latest_passed_run_for_claim(claim, runs)
        if latest_run is None:
            _namecert_log(store, "no_passed_experiment_run", {"claim_id": claim_id})
            continue
        conjecture_id = str(conjecture.get("conjecture_id") or "")
        if not had_link and conjecture_id:
            claim["linked_conjecture_id"] = conjecture_id
            summary["newly_linked"] += 1

        verified_facts = conjecture.setdefault("verified_facts", {})
        if not isinstance(verified_facts, dict):
            verified_facts = {}
            conjecture["verified_facts"] = verified_facts
        was_verified = claim_id in verified_facts
        values = _verified_facts_from_run(latest_run)
        verified_record = {
            "verified_at": now_iso(),
            "experiment_run_id": latest_run.get("experiment_run_id"),
            "values": values,
        }
        verified_facts[claim_id] = verified_record
        conjecture["last_verified_at"] = verified_record["verified_at"]
        linked_claim_ids = conjecture.setdefault("linked_claim_ids", [])
        if not isinstance(linked_claim_ids, list):
            linked_claim_ids = []
            conjecture["linked_claim_ids"] = linked_claim_ids
        if claim_id not in [str(item) for item in linked_claim_ids]:
            linked_claim_ids.append(claim_id)
        if not was_verified:
            summary["verified_facts_updated"] += 1

        if (not had_link or not was_verified) and not _proposal_exists(store, claim_id):
            event = agent_bus._event(
                "namecert_proposal_needed",
                "bio-N",
                "claim",
                claim_id,
                f"claim {claim_id} is stable; NameCert proposal not yet written",
                {
                    "claim_id": claim_id,
                    "linked_conjecture_id": conjecture_id,
                    "verified_facts": verified_record,
                    "loning_naming_hint": _loning_naming_hint(claim, conjecture),
                },
            )
            new_events.append(event)

    store.write_conjectures(conjectures)
    claims_document["claims"] = claims
    _write_claims_document(store.paths.claims_registry, claims_document)
    existing_events = store.load_events()
    merged = agent_bus._dedup(existing_events + new_events, "event_id")
    store.write_events(merged)
    existing_open = {
        agent_bus._event_stable_key(event)
        for event in existing_events
        if str(event.get("status") or "open") == "open"
    }
    summary["proposal_events_emitted"] = sum(
        1
        for event in new_events
        if agent_bus._event_stable_key(event) not in existing_open
    )
    return summary


def run_agent_lane(store: BioRealityStore, *, execute_codex: bool = True, max_dispatch: int = 1) -> dict[str, Any]:
    return agent_bus.run_agent_lane(store, execute_codex=execute_codex, max_dispatch=max_dispatch)


def run_quality_lane(store: BioRealityStore) -> dict[str, Any]:
    return agent_bus.run_quality_lane(store)


def run_assimilation_lane(paths: BioRealityPaths) -> dict[str, Any]:
    signals = signal_assimilator.summarize(paths)
    targets = read_jsonl(paths.packet_targets)
    events = read_jsonl(paths.events)
    agent_tasks = read_jsonl(paths.agent_tasks)
    dispatch_results = read_jsonl(paths.dispatch_results)
    hardening_targets = read_jsonl(paths.hardening_targets)
    vision_rows = read_jsonl(paths.vision_ledger)
    signals["packet_targets"] = len(targets)
    signals["events"] = len(events)
    signals["agent_tasks"] = len(agent_tasks)
    signals["dispatch_results"] = len(dispatch_results)
    signals["dispatch_planned_only"] = sum(1 for item in dispatch_results if item.get("dispatch_status") == "planned_only")
    signals["hardening_targets"] = len(hardening_targets)
    signals["vision_rows"] = len(vision_rows)
    signals["lane"] = "bio-A"
    signal_assimilator.write_summary(signals)
    render_lane_dashboard(paths, targets, signals)
    return signals


def _load_keep_lane_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    config = data.get("keep_lane")
    return config if isinstance(config, dict) else {}


def _load_sync_lane_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    config = data.get("sync_lane")
    return config if isinstance(config, dict) else {}


def _load_bedc_writeback_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    config = data.get("bedc_writeback")
    return config if isinstance(config, dict) else {}


def _load_writeback_lane_config() -> dict[str, Any]:
    data = json.loads(PIPELINE_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        return {}
    lanes = data.get("lanes")
    if isinstance(lanes, list):
        for lane in lanes:
            if isinstance(lane, dict) and lane.get("lane") == "bio-W":
                return lane
    return {}


def _run_command(repo_root: Path, cmd: list[str], *, timeout: float = 60.0) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=repo_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def _append_sync_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.sync_lane_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.sync_lane_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _append_keep_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.keep_lane_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.keep_lane_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _write_sync_state(store: BioRealityStore, state: dict[str, Any]) -> None:
    store.paths.sync_lane_state.parent.mkdir(parents=True, exist_ok=True)
    store.paths.sync_lane_state.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sync_commit_range(last_synced_sha: str, remote: str, branch: str) -> str:
    compare_ref = f"{remote}/{branch}"
    return f"{last_synced_sha}..{compare_ref}" if last_synced_sha else f"HEAD..{compare_ref}"


def _parse_sync_git_log(output: str) -> list[dict[str, Any]]:
    commits: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        maybe_sha, sep, subject = line.partition("|")
        if sep and len(maybe_sha) == 40 and all(char in "0123456789abcdefABCDEF" for char in maybe_sha):
            current = {"sha": maybe_sha, "subject": subject, "files": []}
            commits.append(current)
            continue
        if current is not None:
            files = current.setdefault("files", [])
            if isinstance(files, list):
                files.append(line)
    return commits


def _sync_match_commit(
    commit: dict[str, Any],
    keywords: list[str],
    path_prefixes: list[str],
) -> dict[str, Any] | None:
    files = [str(item) for item in commit.get("files", []) if isinstance(item, str)]
    lowered_keywords = [(keyword, keyword.lower()) for keyword in keywords if keyword]
    matched_keywords: list[str] = []
    matched_paths: list[str] = []
    for path in files:
        path_lower = path.lower()
        for original, lowered in lowered_keywords:
            if lowered in path_lower and original not in matched_keywords:
                matched_keywords.append(original)
        for prefix in path_prefixes:
            if path.startswith(prefix) or fnmatch.fnmatch(path, f"{prefix}*"):
                if prefix not in matched_paths:
                    matched_paths.append(prefix)
    if not matched_keywords and not matched_paths:
        return None
    return {
        "ts": now_iso(),
        "loning_commit_sha": str(commit.get("sha") or ""),
        "subject": str(commit.get("subject") or ""),
        "files_changed": files,
        "matched_keywords": matched_keywords,
        "matched_paths": matched_paths,
    }


def _sync_intelligence_records(
    commits: list[dict[str, Any]],
    keywords: list[str],
    path_prefixes: list[str],
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for commit in commits:
        record = _sync_match_commit(commit, keywords, path_prefixes)
        if record is not None:
            records.append(record)
    return records


def _git_status_porcelain(repo_root: Path) -> list[tuple[str, str]]:
    result = _run_command(repo_root, ["git", "status", "--porcelain"])
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "git status failed").strip())
    changed: list[tuple[str, str]] = []
    for line in result.stdout.splitlines():
        if len(line) < 4:
            continue
        status_code = line[:2]
        path = line[3:]
        if " -> " in path:
            path = path.rsplit(" -> ", 1)[1]
        if path:
            changed.append((status_code, path))
    return changed


def _filter_paths(
    changed: list[tuple[str, str]],
    include_paths: list[str],
    exclude_paths: list[str],
) -> tuple[list[str], list[str]]:
    selected: list[str] = []
    dropped: list[str] = []
    seen: set[str] = set()
    for _status_code, path in changed:
        included = any(fnmatch.fnmatch(path, pattern) for pattern in include_paths)
        excluded = any(fnmatch.fnmatch(path, pattern) for pattern in exclude_paths)
        if included and not excluded:
            if path not in seen:
                selected.append(path)
                seen.add(path)
        else:
            dropped.append(path)
    return selected, dropped


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _rev_list_ahead_behind(repo_root: Path, compare_ref: str) -> tuple[int, int]:
    counts = _run_command(repo_root, ["git", "rev-list", "--left-right", "--count", f"HEAD...{compare_ref}"], timeout=60.0)
    if counts.returncode != 0:
        raise RuntimeError((counts.stderr or counts.stdout or "git rev-list failed").strip())
    parts = counts.stdout.strip().split()
    if len(parts) != 2:
        raise RuntimeError(f"unexpected rev-list output: {counts.stdout.strip()}")
    return int(parts[0]), int(parts[1])


_NETWORK_PROBE_HOST = "github.com"
_NETWORK_PROBE_PORT = 443
_NETWORK_PROBE_TIMEOUT = 3.0


def _network_available(host: str = _NETWORK_PROBE_HOST, port: int = _NETWORK_PROBE_PORT, timeout: float = _NETWORK_PROBE_TIMEOUT) -> bool:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def _localhost_available(host: str, port: int, timeout: float = 2.0) -> bool:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def _parse_server_host_port(url: str) -> tuple[str, int]:
    try:
        from urllib.parse import urlparse
        parsed = urlparse(url)
        host = parsed.hostname or "127.0.0.1"
        port = int(parsed.port or (443 if parsed.scheme == "https" else 80))
        return host, port
    except (ValueError, TypeError):
        return "", 0


def run_sync_lane(store: BioRealityStore) -> dict[str, Any]:
    """Fetch origin/auto-dev, extract Loning's recent biology-related work, attempt fast-forward / no-ff merge."""
    if not _network_available():
        return {"lane": "bio-S", "skipped": "network_unreachable", "host": _NETWORK_PROBE_HOST, "port": _NETWORK_PROBE_PORT}
    try:
        config = _load_sync_lane_config()
    except (OSError, json.JSONDecodeError) as exc:
        _append_sync_log(store, "config_error", {"error": str(exc)})
        return {"lane": "bio-S", "error": "config_error"}
    if not config.get("enabled"):
        return {"lane": "bio-S", "skipped": "disabled"}

    state = _read_json_object(store.paths.sync_lane_state)
    now_ts = time.time()
    min_seconds = float(config.get("min_seconds_between_syncs") or 0.0)
    last_fetch_ts = float(state.get("last_fetch_ts") or 0.0)
    if last_fetch_ts and now_ts - last_fetch_ts < min_seconds:
        return {"lane": "bio-S", "skipped": "throttled", "age_seconds": round(now_ts - last_fetch_ts, 3)}

    repo_root = SCRIPT_DIR.parent.parent
    remote = str(config.get("remote") or "origin")
    branch = str(config.get("upstream_branch") or "auto-dev")
    compare_ref = f"{remote}/{branch}"
    fetch_timeout = float(config.get("fetch_timeout_seconds") or 60.0)
    max_commits = max(1, int(config.get("max_commits_per_sync") or 50))
    last_synced_sha = str(state.get("last_synced_sha") or "")

    try:
        fetch = _run_command(repo_root, ["git", "fetch", remote, branch], timeout=fetch_timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "fetch_failed", {"remote": remote, "branch": branch, "error": str(exc)})
        return {"lane": "bio-S", "error": "fetch_failed", "detail": str(exc)}
    if fetch.returncode != 0:
        detail = (fetch.stderr or fetch.stdout or "git fetch failed").strip()
        _append_sync_log(store, "fetch_failed", {"remote": remote, "branch": branch, "returncode": fetch.returncode, "detail": detail[-2000:]})
        return {"lane": "bio-S", "error": "fetch_failed", "detail": detail[-500:]}

    try:
        rev_parse = _run_command(repo_root, ["git", "rev-parse", compare_ref], timeout=30.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "rev_parse_failed", {"ref": compare_ref, "error": str(exc)})
        return {"lane": "bio-S", "error": "rev_parse_failed", "detail": str(exc)}
    if rev_parse.returncode != 0:
        detail = (rev_parse.stderr or rev_parse.stdout or "git rev-parse failed").strip()
        _append_sync_log(store, "rev_parse_failed", {"ref": compare_ref, "returncode": rev_parse.returncode, "detail": detail[-2000:]})
        return {"lane": "bio-S", "error": "rev_parse_failed", "detail": detail[-500:]}
    upstream_sha = rev_parse.stdout.strip()

    working_tree_clean = False
    try:
        working_tree_clean = not _git_status_porcelain(repo_root)
    except (OSError, RuntimeError) as exc:
        _append_sync_log(store, "git_status_error", {"error": str(exc)})

    if upstream_sha == last_synced_sha and working_tree_clean:
        new_state = dict(state)
        new_state.update({"last_fetch_ts": now_ts, "last_synced_sha": upstream_sha, "last_intelligence_count": 0})
        try:
            _write_sync_state(store, new_state)
        except OSError as exc:
            _append_sync_log(store, "state_write_failed", {"error": str(exc), "upstream_sha": upstream_sha})
        return {"lane": "bio-S", "skipped": "already current", "last_synced_sha": upstream_sha}

    ahead_before_sync = 0
    behind_before_sync = 0
    try:
        ahead_before_sync, behind_before_sync = _rev_list_ahead_behind(repo_root, compare_ref)
    except (OSError, RuntimeError, ValueError) as exc:
        _append_sync_log(store, "rev_list_failed", {"ref": compare_ref, "error": str(exc)})

    commit_range = _sync_commit_range(last_synced_sha, remote, branch)
    try:
        log_result = _run_command(
            repo_root,
            ["git", "log", f"-n{max_commits}", "--name-only", "--format=%H|%s", commit_range],
            timeout=60.0,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_sync_log(store, "git_log_failed", {"range": commit_range, "error": str(exc)})
        commits: list[dict[str, Any]] = []
    else:
        if log_result.returncode == 0:
            commits = _parse_sync_git_log(log_result.stdout)
        else:
            detail = (log_result.stderr or log_result.stdout or "git log failed").strip()
            _append_sync_log(store, "git_log_failed", {"range": commit_range, "returncode": log_result.returncode, "detail": detail[-2000:]})
            commits = []

    keywords = [str(item) for item in config.get("intelligence_keywords", []) if isinstance(item, str)]
    path_prefixes = [str(item) for item in config.get("intelligence_paths", []) if isinstance(item, str)]
    records = _sync_intelligence_records(commits, keywords, path_prefixes)
    try:
        append_jsonl(store.paths.loning_intelligence, records)
    except OSError as exc:
        _append_sync_log(store, "intelligence_write_failed", {"error": str(exc), "records": len(records)})
        records = []

    merge_attempted = False
    merge_status = "skipped"
    merge_sha = ""
    if behind_before_sync > 0:
        merge_attempted = True
        try:
            merge = _run_command(repo_root, ["git", "merge", "--no-ff", "-m", f"Sync auto-dev {upstream_sha[:12]}", compare_ref], timeout=300.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            merge_status = "conflict_aborted"
            _append_sync_log(store, "merge_error", {"ref": compare_ref, "error": str(exc)})
            try:
                _run_command(repo_root, ["git", "merge", "--abort"], timeout=60.0)
            except (OSError, subprocess.TimeoutExpired) as abort_exc:
                _append_sync_log(store, "merge_abort_failed", {"error": str(abort_exc)})
        else:
            if merge.returncode == 0:
                merge_status = "ok"
                try:
                    head = _run_command(repo_root, ["git", "rev-parse", "HEAD"], timeout=30.0)
                    merge_sha = head.stdout.strip() if head.returncode == 0 else ""
                except (OSError, subprocess.TimeoutExpired):
                    merge_sha = ""
                _append_sync_log(store, "merge_ok", {"ref": compare_ref, "merge_sha": merge_sha, "upstream_sha": upstream_sha})
            else:
                merge_status = "conflict_aborted"
                detail = (merge.stderr or merge.stdout or "git merge failed").strip()
                _append_sync_log(store, "merge_conflict_aborted", {"ref": compare_ref, "returncode": merge.returncode, "detail": detail[-2000:]})
                abort = _run_command(repo_root, ["git", "merge", "--abort"], timeout=60.0)
                if abort.returncode != 0:
                    abort_detail = (abort.stderr or abort.stdout or "git merge --abort failed").strip()
                    _append_sync_log(store, "merge_abort_failed", {"returncode": abort.returncode, "detail": abort_detail[-2000:]})

    new_state = dict(state)
    new_state.update(
        {
            "last_fetch_ts": now_ts,
            "last_synced_sha": upstream_sha,
            "last_intelligence_count": len(records),
        }
    )
    if merge_sha:
        new_state["last_merge_sha"] = merge_sha
    try:
        _write_sync_state(store, new_state)
    except OSError as exc:
        _append_sync_log(store, "state_write_failed", {"error": str(exc), "upstream_sha": upstream_sha})

    return {
        "lane": "bio-S",
        "fetched": True,
        "behind_before_sync": behind_before_sync,
        "ahead_before_sync": ahead_before_sync,
        "interesting_commits": len(records),
        "intelligence_records_appended": len(records),
        "merge_attempted": merge_attempted,
        "merge_status": merge_status,
        "merge_sha": merge_sha,
        "last_synced_sha": upstream_sha,
    }


def _keep_lane_recently_pushed(store: BioRealityStore, min_seconds: float) -> tuple[bool, float]:
    state = _read_json_object(store.paths.keep_lane_state)
    last_push_ts = float(state.get("last_push_ts") or 0.0)
    age = time.time() - last_push_ts if last_push_ts else min_seconds + 1.0
    return last_push_ts > 0 and age < min_seconds, age


def _run_keep_gates(store: BioRealityStore, repo_root: Path, gates: list[Any]) -> tuple[bool, list[str] | None]:
    for gate in gates:
        if not isinstance(gate, list) or not all(isinstance(item, str) for item in gate):
            _append_keep_log(store, "gate_invalid", {"gate": gate})
            return False, [str(gate)]
        try:
            result = _run_command(repo_root, gate, timeout=60.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            _append_keep_log(store, "gate_error", {"gate": gate, "error": str(exc)})
            return False, gate
        if result.returncode != 0:
            _append_keep_log(
                store,
                "gate_failure",
                {
                    "gate": gate,
                    "returncode": result.returncode,
                    "stdout_tail": result.stdout[-2000:],
                    "stderr_tail": result.stderr[-2000:],
                },
            )
            return False, gate
    return True, None


def _remote_behind_count(repo_root: Path, remote: str, branch: str) -> int:
    fetch = _run_command(repo_root, ["git", "fetch", remote, branch], timeout=60.0)
    if fetch.returncode != 0:
        raise RuntimeError((fetch.stderr or fetch.stdout or "git fetch failed").strip())
    compare_ref = f"{remote}/{branch}"
    counts = _run_command(repo_root, ["git", "rev-list", "--left-right", "--count", f"HEAD...{compare_ref}"], timeout=60.0)
    if counts.returncode != 0:
        raise RuntimeError((counts.stderr or counts.stdout or "git rev-list failed").strip())
    parts = counts.stdout.strip().split()
    if len(parts) != 2:
        raise RuntimeError(f"unexpected rev-list output: {counts.stdout.strip()}")
    return int(parts[1])


def _local_ahead_count(repo_root: Path, remote: str, branch: str) -> int:
    fetch = _run_command(repo_root, ["git", "fetch", remote, branch], timeout=60.0)
    if fetch.returncode != 0:
        raise RuntimeError((fetch.stderr or fetch.stdout or "git fetch failed").strip())
    compare_ref = f"{remote}/{branch}"
    counts = _run_command(repo_root, ["git", "rev-list", "--left-right", "--count", f"HEAD...{compare_ref}"], timeout=60.0)
    if counts.returncode != 0:
        raise RuntimeError((counts.stderr or counts.stdout or "git rev-list failed").strip())
    parts = counts.stdout.strip().split()
    if len(parts) != 2:
        raise RuntimeError(f"unexpected rev-list output: {counts.stdout.strip()}")
    return int(parts[0])


def _push_ahead_only(store: BioRealityStore, repo_root: Path, remote: str, branch: str) -> tuple[bool, str]:
    """Push HEAD to remote when local is ahead but working tree has no
    changes to commit. Used for syncing bio-S merge commits and any other
    commits made outside bio-K. Fast-forward only; never force-pushes."""
    push = _run_command(repo_root, ["git", "push", remote, f"HEAD:{branch}"], timeout=180.0)
    if push.returncode != 0:
        return False, (push.stderr or push.stdout or "git push failed").strip()[-500:]
    return True, ""


def _keep_lane_commit_message(store: BioRealityStore, selected: list[str]) -> str:
    loop_state = _read_json_object(store.paths.root / "state" / "loop_state.json")
    loops = loop_state.get("loops") if isinstance(loop_state.get("loops"), dict) else {}
    bio_x = loops.get("bio_X_execute_experiments", {}) if isinstance(loops, dict) else {}
    bio_x_summary = bio_x.get("last_summary") if isinstance(bio_x, dict) and isinstance(bio_x.get("last_summary"), dict) else {}
    claims = _load_claims_document(store.paths.claims_registry).get("claims", [])
    claim_states = _claim_state_counts([item for item in claims if isinstance(item, dict)]) if isinstance(claims, list) else {}
    title = f"BioReality cycle {now_iso()}: {len(selected)} file(s)"
    body = [
        "",
        "Selected files:",
        *[f"- {path}" for path in selected],
        "",
        f"loop_last_attempt_ts: {bio_x.get('last_attempt_ts') if isinstance(bio_x, dict) else ''}",
        f"claim_states: {json.dumps(claim_states, sort_keys=True)}",
        "bio_X: "
        + json.dumps(
            {
                "executed": bio_x_summary.get("executed", 0),
                "passed_this_cycle": bio_x_summary.get("passed_this_cycle", 0),
                "failed_this_cycle": bio_x_summary.get("failed_this_cycle", 0),
            },
            sort_keys=True,
        ),
    ]
    return title + "\n" + "\n".join(body)


def run_keep_lane(store: BioRealityStore) -> dict[str, Any]:
    try:
        config = _load_keep_lane_config()
    except (OSError, json.JSONDecodeError) as exc:
        _append_keep_log(store, "config_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "config error"}
    if not config.get("enabled"):
        return {"lane": "bio-K", "skipped": "disabled"}

    repo_root = store.paths.root.parent.parent
    try:
        changed = _git_status_porcelain(repo_root)
    except (OSError, RuntimeError) as exc:
        _append_keep_log(store, "git_status_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "git status failed"}

    remote_default = str(config.get("remote") or "origin")
    branch_default = str(config.get("branch") or "feat/bio-reality-deepening")

    if not changed:
        try:
            ahead = _local_ahead_count(repo_root, remote_default, branch_default)
        except (OSError, RuntimeError, ValueError) as exc:
            _append_keep_log(store, "ahead_check_error", {"error": str(exc)})
            return {"lane": "bio-K", "skipped": "no changes", "ahead_check_error": True}
        if ahead <= 0:
            return {"lane": "bio-K", "skipped": "no changes"}
        try:
            push_ok, push_detail = _push_ahead_only(store, repo_root, remote_default, branch_default)
        except (OSError, subprocess.TimeoutExpired, RuntimeError) as exc:
            _append_keep_log(store, "ahead_push_error", {"error": str(exc), "ahead": ahead})
            return {"lane": "bio-K", "skipped": "no changes", "ahead": ahead, "push_error": str(exc)}
        if push_ok:
            return {"lane": "bio-K", "pushed_ahead": ahead, "no_local_commit": True}
        _append_keep_log(store, "ahead_push_failure", {"ahead": ahead, "detail": push_detail})
        return {"lane": "bio-K", "skipped": "ahead_push_failed", "ahead": ahead, "detail": push_detail}

    include_paths = [str(item) for item in config.get("include_paths", []) if isinstance(item, str)]
    exclude_paths = [str(item) for item in config.get("exclude_paths", []) if isinstance(item, str)]
    selected, dropped = _filter_paths(changed, include_paths, exclude_paths)
    if not selected:
        # Working tree has changes but they're all filtered out by exclude
        # rules (runtime drift). Still push any local commits ahead of remote
        # so bio-S merge commits and other off-lane commits don't accumulate.
        try:
            ahead = _local_ahead_count(repo_root, remote_default, branch_default)
        except (OSError, RuntimeError, ValueError) as exc:
            _append_keep_log(store, "ahead_check_error_after_drop", {"error": str(exc), "dropped": len(dropped)})
            return {"lane": "bio-K", "skipped": "no useful changes", "dropped": len(dropped), "ahead_check_error": True}
        if ahead <= 0:
            return {"lane": "bio-K", "skipped": "no useful changes", "dropped": len(dropped)}
        try:
            push_ok, push_detail = _push_ahead_only(store, repo_root, remote_default, branch_default)
        except (OSError, subprocess.TimeoutExpired, RuntimeError) as exc:
            _append_keep_log(store, "ahead_push_error_after_drop", {"error": str(exc), "ahead": ahead})
            return {"lane": "bio-K", "skipped": "no useful changes", "dropped": len(dropped), "ahead": ahead, "push_error": str(exc)}
        if push_ok:
            return {"lane": "bio-K", "pushed_ahead": ahead, "no_local_commit": True, "dropped": len(dropped)}
        _append_keep_log(store, "ahead_push_failure_after_drop", {"ahead": ahead, "detail": push_detail})
        return {"lane": "bio-K", "skipped": "ahead_push_failed", "ahead": ahead, "detail": push_detail, "dropped": len(dropped)}

    min_seconds = float(config.get("min_seconds_between_pushes") or 0.0)
    try:
        too_soon, age = _keep_lane_recently_pushed(store, min_seconds)
    except (OSError, ValueError) as exc:
        _append_keep_log(store, "state_read_error", {"error": str(exc)})
        return {"lane": "bio-K", "error": "state read failed"}
    if too_soon:
        return {"lane": "bio-K", "skipped": "recent push", "age_seconds": round(age, 3), "files": len(selected), "dropped": len(dropped)}

    gates = config.get("pre_commit_gates", [])
    ok, failed_gate = _run_keep_gates(store, repo_root, gates if isinstance(gates, list) else [])
    if not ok:
        return {"lane": "bio-K", "skipped": "gate failure", "failed_gate": failed_gate, "files": len(selected), "dropped": len(dropped)}

    remote = str(config.get("remote") or "origin")
    branch = str(config.get("branch") or "feat/bio-reality-deepening")
    try:
        behind = _remote_behind_count(repo_root, remote, branch)
    except (OSError, RuntimeError, ValueError) as exc:
        _append_keep_log(store, "remote_check_error", {"remote": remote, "branch": branch, "error": str(exc)})
        return {"lane": "bio-K", "error": "remote check failed", "files": len(selected), "dropped": len(dropped)}
    if behind > 0:
        _append_keep_log(store, "behind_remote", {"remote": remote, "branch": branch, "behind": behind, "selected": selected})
        return {"lane": "bio-K", "skipped": "behind remote", "behind": behind, "files": len(selected), "dropped": len(dropped)}

    try:
        add = _run_command(repo_root, ["git", "add", "--", *selected], timeout=60.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_keep_log(store, "git_add_error", {"error": str(exc), "selected": selected})
        return {"lane": "bio-K", "error": "git add failed", "files": len(selected), "dropped": len(dropped)}
    if add.returncode != 0:
        _append_keep_log(store, "git_add_failure", {"returncode": add.returncode, "stderr": add.stderr[-2000:], "selected": selected})
        return {"lane": "bio-K", "error": "git add failed", "files": len(selected), "dropped": len(dropped)}

    message = _keep_lane_commit_message(store, selected)
    try:
        commit = _run_command(repo_root, ["git", "commit", "-m", message], timeout=60.0)
    except (OSError, subprocess.TimeoutExpired) as exc:
        _append_keep_log(store, "git_commit_error", {"error": str(exc), "selected": selected})
        return {"lane": "bio-K", "error": "git commit failed", "files": len(selected), "dropped": len(dropped)}
    if commit.returncode != 0:
        _append_keep_log(store, "git_commit_failure", {"returncode": commit.returncode, "stdout": commit.stdout[-2000:], "stderr": commit.stderr[-2000:]})
        return {"lane": "bio-K", "error": "git commit failed", "files": len(selected), "dropped": len(dropped)}

    try:
        sha_result = _run_command(repo_root, ["git", "rev-parse", "HEAD"], timeout=60.0)
        commit_sha = sha_result.stdout.strip() if sha_result.returncode == 0 else ""
    except (OSError, subprocess.TimeoutExpired):
        commit_sha = ""
    retries = int(config.get("max_push_retries") or 0)
    push_ok = False
    last_push_error = ""
    if not _network_available():
        _append_keep_log(store, "network_unreachable", {"remote": remote, "branch": branch, "commit_sha": commit_sha})
        return {"lane": "bio-K", "committed": True, "pushed": False, "skipped_push": "network_unreachable", "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha}
    for attempt in range(retries + 1):
        try:
            push = _run_command(repo_root, ["git", "push", remote, f"HEAD:{branch}"], timeout=60.0)
        except (OSError, subprocess.TimeoutExpired) as exc:
            last_push_error = str(exc)
            push = None
        if push is None:
            if attempt < retries:
                time.sleep(float(2 ** attempt))
            continue
        if push.returncode == 0:
            push_ok = True
            break
        last_push_error = (push.stderr or push.stdout or "git push failed").strip()
        if attempt < retries:
            time.sleep(float(2 ** attempt))
    if not push_ok:
        _append_keep_log(store, "git_push_failure", {"remote": remote, "branch": branch, "error": last_push_error[-2000:], "commit_sha": commit_sha})
        return {"lane": "bio-K", "error": "git push failed", "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha}

    state = {"last_push_ts": time.time(), "last_commit_sha": commit_sha, "last_pushed_files": selected}
    try:
        store.paths.keep_lane_state.parent.mkdir(parents=True, exist_ok=True)
        store.paths.keep_lane_state.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except OSError as exc:
        _append_keep_log(store, "state_write_error", {"error": str(exc), "commit_sha": commit_sha})
        return {"lane": "bio-K", "error": "state write failed", "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha, "pushed": True}
    return {"lane": "bio-K", "committed": True, "files": len(selected), "dropped": len(dropped), "commit_sha": commit_sha, "pushed": True}


def _tex_escape(value: Any) -> str:
    text = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(char, char) for char in text)


def _sentence_list(items: Any) -> str:
    if not isinstance(items, list) or not items:
        return "none recorded"
    return "; ".join(_tex_escape(item) for item in items if isinstance(item, str) and item.strip()) or "none recorded"


def _by_id(records: list[dict[str, Any]], key: str) -> dict[str, dict[str, Any]]:
    return {str(record.get(key) or ""): record for record in records if record.get(key)}


def _passed_conjectures(store: BioRealityStore) -> list[dict[str, Any]]:
    conjectures = store.load_conjectures()
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    results = bio_reality_loop.gate_all(conjectures, contacts, probes, mismatches)
    passed = {
        str(result.get("packet_id") or "")
        for result in results
        if result.get("packet_kind") == "conjecture" and result.get("gate_status") == "gate_passed"
    }
    return [record for record in conjectures if str(record.get("conjecture_id") or "") in passed]


def _temp_paths(base: Path) -> BioRealityPaths:
    return BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=base / "conjectures.jsonl",
        contacts=base / "reality_contacts.jsonl",
        probes=base / "probes.jsonl",
        mismatches=base / "mismatches.jsonl",
        gate_results=base / "gate_results.jsonl",
        deepening_tasks=base / "deepening_tasks.jsonl",
        review_queue=base / "review_queue.jsonl",
        packet_targets=base / "packet_targets.jsonl",
        events=base / "events.jsonl",
        agent_tasks=base / "agent_tasks.jsonl",
        agent_reviews=base / "agent_reviews.jsonl",
        dispatch_results=base / "dispatch_results.jsonl",
        hardening_targets=base / "hardening_targets.jsonl",
        lane_dashboard=base / "lane_dashboard.md",
        claims_registry=base / "claims.json",
        experiments_registry=base / "experiments.json",
        experiment_runs=base / "experiment_runs.jsonl",
        sync_lane_state=base / "sync_lane.json",
        sync_lane_log=base / "sync_lane.log",
        loning_intelligence=base / "loning_intelligence.jsonl",
        namecert_proposals_dir=base / "namecert_proposals",
        namecert_lane_log=base / "namecert_lane.log",
        bedc_writeback_log=base / "bedc_writeback.log",
        experiments_dir=base / "experiments",
        data_dir=base / "data",
        vision_dir=base / "vision",
        vision_ledger=base / "vision" / "ledger" / "intake_evaluations.jsonl",
        paper_main=base / "paper" / "main.tex",
        paper_part=base / "paper" / "parts" / "codon_window_reality_boundary.tex",
    )


def _render_paper_main(paths: BioRealityPaths, namecert_slugs: list[str]) -> str:
    lines = [
        r"\documentclass[11pt]{article}",
        r"\usepackage[margin=1in]{geometry}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage{lmodern}",
        r"\usepackage{microtype}",
        r"\usepackage{hyperref}",
        "",
        r"\title{BioReality: Reality-Bound Biological Deepening}",
        r"\author{The Omega Institute}",
        r"\date{}",
        "",
        r"\begin{document}",
        r"\maketitle",
        "",
        r"\section{Scope}",
        "BioReality records biological conjecture deepening under explicit provenance boundaries. "
        "External curated biology is recorded as reality input; newmath and BEDC-style structure is recorded as internal derivation; every cross-layer biological claim remains blocked until a separate reality contact supports that layer.",
        "",
        r"\input{parts/codon_window_reality_boundary}",
        "",
    ]
    if namecert_slugs:
        lines.extend(
            [
                r"\section{NameCert Proposals}",
                "These deterministic writeback chapters promote draft NameCert proposal notes into reviewable paper text.",
                "",
            ]
        )
        for slug in sorted(namecert_slugs):
            lines.extend([rf"\input{{parts/namecerts/{slug}}}", ""])
    lines.extend(
        [
            r"\end{document}",
            "",
        ]
    )
    return "\n".join(lines)


def _format_verified_fact_value(value: Any) -> str | None:
    if isinstance(value, bool):
        return "True" if value else "False"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return f"{value:.6g}"
    if isinstance(value, str):
        return _tex_escape(value)
    if isinstance(value, list) and all(isinstance(item, str) and len(item) <= 32 for item in value):
        return r"\{" + ", ".join(_tex_escape(item) for item in value) + r"\}"
    return None


def _render_verified_facts(conjecture: dict[str, Any]) -> list[str]:
    lines = [r"\paragraph{Verified facts.}"]
    verified_facts = conjecture.get("verified_facts")
    if not isinstance(verified_facts, dict) or not verified_facts:
        return lines + ["No verified facts attached yet.", ""]
    for claim_id, fact in sorted(verified_facts.items()):
        if not isinstance(fact, dict):
            continue
        experiment_run_id = str(fact.get("experiment_run_id") or "")
        values = fact.get("values") if isinstance(fact.get("values"), dict) else {}
        rendered_values: list[str] = []
        for key, value in sorted(values.items()):
            rendered_value = _format_verified_fact_value(value)
            if rendered_value is not None:
                rendered_values.append(f"{_tex_escape(str(key))}={rendered_value}")
        values_text = ", ".join(rendered_values) if rendered_values else "no scalar values recorded"
        lines.extend(
            [
                rf"\textbf{{{_tex_escape(str(claim_id))}}}. Run {_tex_escape(experiment_run_id[:12])}. {values_text}.",
                "",
            ]
        )
    if len(lines) == 1:
        lines.extend(["No verified facts attached yet.", ""])
    return lines


def _bio_w_codex_writer_config(config: dict[str, Any]) -> dict[str, Any]:
    raw = config.get("codex_writer")
    writer = raw if isinstance(raw, dict) else {}
    return {
        "enabled": bool(writer.get("enabled", True)),
        "max_retries": max(1, int(writer.get("max_retries", 2))),
        "timeout_seconds": max(1, int(writer.get("timeout_seconds", writer.get("timeout", 600)))),
        "log_dir": str(writer.get("log_dir", "tools/bio_reality/state/writeback_codex_logs")),
        "min_audit_score": int(writer.get("min_audit_score", 7)),
        "min_used_fact_ids": max(0, int(writer.get("min_used_fact_ids", 2))),
        "corrective_retry_on_gate_failure": bool(
            writer.get("corrective_retry_on_gate_failure", writer.get("corrective_retry", True))
        ),
    }


def _verified_facts_for_claim(conjecture: dict[str, Any], claim_id: str) -> dict[str, Any]:
    verified_facts = conjecture.get("verified_facts")
    if not isinstance(verified_facts, dict):
        return {}
    claim_facts = verified_facts.get(claim_id)
    return claim_facts if isinstance(claim_facts, dict) else {}


def _all_verified_facts(conjecture: dict[str, Any]) -> dict[str, Any]:
    verified_facts = conjecture.get("verified_facts")
    return verified_facts if isinstance(verified_facts, dict) else {}


def _linked_records_for_conjecture(
    conjecture: dict[str, Any],
    contacts_by_id: dict[str, dict[str, Any]],
    probes_by_id: dict[str, dict[str, Any]],
    mismatches_by_probe: dict[str, list[dict[str, Any]]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
    probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
    linked_contacts = [contacts_by_id[ref] for ref in contact_refs if ref in contacts_by_id]
    linked_probes = [probes_by_id[ref] for ref in probe_refs if ref in probes_by_id]
    linked_mismatches = [
        mismatch
        for probe_ref in probe_refs
        for mismatch in mismatches_by_probe.get(probe_ref, [])
    ]
    return linked_contacts, linked_probes, linked_mismatches


def _extract_codex_event_text(stdout: str) -> str:
    texts: list[str] = []
    for line in stdout.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        try:
            event = json.loads(stripped)
        except json.JSONDecodeError:
            texts.append(stripped)
            continue
        if not isinstance(event, dict):
            continue
        for key in ("text", "message", "content"):
            value = event.get(key)
            if isinstance(value, str) and value.strip():
                texts.append(value)
        item = event.get("item")
        if isinstance(item, dict):
            item_text = item.get("text")
            if isinstance(item_text, str) and item_text.strip():
                texts.append(item_text)
            content = item.get("content")
            if isinstance(content, list):
                for part in content:
                    if isinstance(part, dict):
                        value = part.get("text")
                        if isinstance(value, str) and value.strip():
                            texts.append(value)
            elif isinstance(content, str) and content.strip():
                texts.append(content)
        delta = event.get("delta")
        if isinstance(delta, str) and delta.strip():
            texts.append(delta)
    return texts[-1] if texts else stdout


def _extract_json_object_from_text(text: str) -> dict[str, Any] | None:
    fence_matches = list(re.finditer(r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL | re.IGNORECASE))
    candidates = [match.group(1) for match in fence_matches]
    stripped = text.strip()
    if stripped:
        candidates.append(stripped)
    first = stripped.find("{")
    last = stripped.rfind("}")
    if first != -1 and last != -1 and last > first:
        candidates.append(stripped[first : last + 1])
    for candidate in reversed(candidates):
        try:
            parsed = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            return parsed
    return None


def _parse_bio_w_codex_json(stdout: str) -> dict[str, Any] | None:
    parsed = _extract_json_object_from_text(_extract_codex_event_text(stdout))
    if not isinstance(parsed, dict):
        return None
    required = ["verdict", "audit_score", "used_fact_ids", "chapter_content", "risk_notes", "missing_data_notes"]
    if any(field not in parsed for field in required):
        return None
    if parsed.get("verdict") not in {"ready", "needs_more_data", "skip"}:
        return None
    try:
        audit_score = int(parsed.get("audit_score"))
    except (TypeError, ValueError):
        return None
    if audit_score < 0 or audit_score > 10:
        return None
    if not isinstance(parsed.get("used_fact_ids"), list) or not all(isinstance(item, str) for item in parsed["used_fact_ids"]):
        return None
    if not isinstance(parsed.get("chapter_content"), str):
        return None
    if not isinstance(parsed.get("risk_notes"), str) or not isinstance(parsed.get("missing_data_notes"), str):
        return None
    parsed["audit_score"] = audit_score
    return parsed


def _run_bio_w_codex(prompt: str, repo_root: Path, timeout_seconds: int) -> tuple[dict[str, Any] | None, str, str]:
    try:
        completed = subprocess.run(
            [
                "codex",
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--sandbox",
                "read-only",
                "--json",
                "-C",
                str(repo_root),
                "-",
            ],
            input=prompt,
            text=True,
            capture_output=True,
            timeout=timeout_seconds,
            check=False,
        )
    except (subprocess.TimeoutExpired, OSError) as exc:
        return None, "", f"subprocess_error: {exc}"
    if completed.returncode != 0:
        return None, completed.stdout or "", completed.stderr or ""
    return _parse_bio_w_codex_json(completed.stdout or ""), completed.stdout or "", completed.stderr or ""


def _write_bio_w_codex_log(
    repo_root: Path,
    log_dir: str | Path,
    task_id: str,
    prompt: str,
    parsed: dict[str, Any] | None,
    raw_stdout: str = "",
    raw_stderr: str = "",
) -> None:
    path = Path(log_dir)
    if not path.is_absolute():
        path = repo_root / path
    try:
        path.mkdir(parents=True, exist_ok=True)
        (path / f"{task_id}.prompt.txt").write_text(prompt, encoding="utf-8")
        (path / f"{task_id}.parsed.json").write_text(
            json.dumps(parsed or {"status": "none"}, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        if raw_stdout:
            (path / f"{task_id}.raw.txt").write_text(raw_stdout, encoding="utf-8")
        if raw_stderr:
            (path / f"{task_id}.stderr.txt").write_text(raw_stderr, encoding="utf-8")
    except OSError:
        return


def _bio_w_author_prompt(
    *,
    mode: str,
    claim_id: str,
    slug: str,
    verified_facts: dict[str, Any],
    conjecture: dict[str, Any],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
    corrective_feedback: list[str] | None = None,
) -> str:
    payload = {
        "mode": mode,
        "claim_id": claim_id,
        "slug": slug,
        "verified_facts": verified_facts,
        "conjecture": conjecture,
        "contacts": contacts,
        "probes": probes,
        "mismatches": mismatches,
    }
    lines = [
        "You are writing English mathematical TeX for the standalone BioReality paper.",
        "Return only one JSON object, preferably inside a ```json code block. Do not write files.",
        "",
        "# Finite-row data",
        "```json",
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True),
        "```",
        "",
        "# Hard constraints",
        r"- chapter_content must be complete TeX prose with \subsection, \label, and \paragraph{...} structure.",
        r"- Include \origin{ai}; BioReality chapters are ai-discovered vision-level records.",
        "- Use concrete finite-row numbers from verified_facts: R lists, M lists, lambda values, p-values, module classification, hit_rate, row counts, and related scalar data when present.",
        "- Do not write placeholders or generic template prose.",
        r"- Do not use cross-paper or cross-chapter \autoref references; keep the chapter self-contained.",
        r"- Do not write Lean macros such as \leanchecked, \leanstmt, \leandef, \leanvariant, \leansorryd, or \leantarget.",
        r"- Math style: inline math is $...$; display math is $$\begin{aligned}...\end{aligned}$$. Do not use \[...\], equation, align, or eqnarray.",
        "- State the cannot-claim boundary locally: no translation, folding, physical admissibility, function, mechanism, or universality follows unless a separate contact supplies it.",
        "- The prose must be chapter-specific and at least 1500 characters when verdict is ready.",
        "",
    ]
    if corrective_feedback:
        lines.extend(["# Corrective feedback"])
        for issue in corrective_feedback:
            lines.append(f"- {issue}")
        lines.append("")
    lines.extend(
        [
            "# Output schema",
            "{",
            '  "verdict": "ready" | "needs_more_data" | "skip",',
            '  "audit_score": 0-10,',
            '  "used_fact_ids": ["verified_facts keys actually cited"],',
            '  "chapter_content": "complete TeX section text",',
            '  "risk_notes": "short risk note",',
            '  "missing_data_notes": "empty string or specific missing finite-row data"',
            "}",
        ]
    )
    return "\n".join(lines)


def _bio_w_cache_paths(repo_root: Path, log_dir: str | Path, task_id: str) -> tuple[Path, Path]:
    base = Path(log_dir)
    if not base.is_absolute():
        base = repo_root / base
    return base / f"{task_id}.input.sha256", base / f"{task_id}.cached_chapter.tex"


def _bio_w_cached_render(
    repo_root: Path,
    log_dir: str | Path,
    task_id: str,
    prompt: str,
    corrective_feedback: list[str] | None,
) -> dict[str, Any] | None:
    # Skip cache when corrective feedback is present — caller wants a fresh attempt with feedback applied.
    if corrective_feedback:
        return None
    hash_path, chapter_path = _bio_w_cache_paths(repo_root, log_dir, task_id)
    if not hash_path.exists() or not chapter_path.exists():
        return None
    try:
        stored_hash = hash_path.read_text(encoding="utf-8").strip()
    except OSError:
        return None
    current_hash = hashlib.sha256(prompt.encode("utf-8")).hexdigest()
    if stored_hash != current_hash:
        return None
    try:
        cached = chapter_path.read_text(encoding="utf-8")
    except OSError:
        return None
    if not cached.strip():
        return None
    return {
        "verdict": "ready",
        "audit_score": 10,
        "used_fact_ids": ["cached"],
        "chapter_content": cached,
        "risk_notes": "",
        "missing_data_notes": "",
        "cache_hit": True,
    }


def _bio_w_persist_cache(
    repo_root: Path,
    log_dir: str | Path,
    task_id: str,
    prompt: str,
    parsed: dict[str, Any] | None,
) -> None:
    if not isinstance(parsed, dict) or parsed.get("verdict") != "ready":
        return
    chapter_text = str(parsed.get("chapter_content") or "")
    if not chapter_text.strip():
        return
    hash_path, chapter_path = _bio_w_cache_paths(repo_root, log_dir, task_id)
    try:
        hash_path.parent.mkdir(parents=True, exist_ok=True)
        hash_path.write_text(hashlib.sha256(prompt.encode("utf-8")).hexdigest(), encoding="utf-8")
        chapter_path.write_text(chapter_text, encoding="utf-8")
    except OSError:
        return


def render_namecert_with_codex(
    claim_id: str,
    slug: str,
    verified_facts: dict[str, Any],
    conjecture: dict[str, Any],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
    repo_root: Path,
    *,
    timeout_seconds: int = 600,
    corrective_feedback: list[str] | None = None,
    log_dir: str | Path = "tools/bio_reality/state/writeback_codex_logs",
) -> dict[str, Any] | None:
    prompt = _bio_w_author_prompt(
        mode="namecert",
        claim_id=claim_id,
        slug=slug,
        verified_facts=verified_facts,
        conjecture=conjecture,
        contacts=contacts,
        probes=probes,
        mismatches=mismatches,
        corrective_feedback=corrective_feedback,
    )
    task_id = _safe_task_id(f"namecert-{claim_id}")
    cached = _bio_w_cached_render(repo_root, log_dir, task_id, prompt, corrective_feedback)
    if cached is not None:
        return cached
    parsed, raw_stdout, raw_stderr = _run_bio_w_codex(prompt, repo_root, timeout_seconds)
    _write_bio_w_codex_log(repo_root, log_dir, task_id, prompt, parsed, raw_stdout, raw_stderr)
    _bio_w_persist_cache(repo_root, log_dir, task_id, prompt, parsed)
    return parsed


def render_conjecture_with_codex(
    conjecture: dict[str, Any],
    verified_facts: dict[str, Any],
    contacts: list[dict[str, Any]],
    probes: list[dict[str, Any]],
    mismatches: list[dict[str, Any]],
    repo_root: Path,
    *,
    timeout_seconds: int = 600,
    corrective_feedback: list[str] | None = None,
    log_dir: str | Path = "tools/bio_reality/state/writeback_codex_logs",
) -> dict[str, Any] | None:
    conjecture_id = str(conjecture.get("conjecture_id") or "unnamed")
    prompt = _bio_w_author_prompt(
        mode="conjecture",
        claim_id=conjecture_id,
        slug=re.sub(r"[^a-z0-9]+", "-", conjecture_id.lower()).strip("-") or "conjecture",
        verified_facts=verified_facts,
        conjecture=conjecture,
        contacts=contacts,
        probes=probes,
        mismatches=mismatches,
        corrective_feedback=corrective_feedback,
    )
    task_id = _safe_task_id(f"conjecture-{conjecture_id}")
    cached = _bio_w_cached_render(repo_root, log_dir, task_id, prompt, corrective_feedback)
    if cached is not None:
        return cached
    parsed, raw_stdout, raw_stderr = _run_bio_w_codex(prompt, repo_root, timeout_seconds)
    _write_bio_w_codex_log(repo_root, log_dir, task_id, prompt, parsed, raw_stdout, raw_stderr)
    _bio_w_persist_cache(repo_root, log_dir, task_id, prompt, parsed)
    return parsed


def _namecert_slug(markdown_path: Path) -> str:
    slug = re.sub(r"[^a-z0-9]+", "_", markdown_path.stem.lower()).strip("_")
    return slug or "namecert"


def _namecert_claim_id(markdown_path: Path) -> str:
    return markdown_path.stem


def _namecert_paragraph_title(title: str) -> str:
    cleaned = re.sub(r"^\s*\d+\.\s*", "", title).strip()
    if cleaned.lower() == "loning-format chapter slug":
        return "NameCert chapter slug"
    return cleaned or "Section"


def _render_namecert_proposal(markdown_path: Path, slug: str) -> str:
    lines = [
        rf"\subsection{{NameCert: {_tex_escape(_namecert_claim_id(markdown_path))}}}",
        rf"\label{{sec:namecert-{slug}}}",
        r"\noindent\textit{Proposed by bio-namer; review status: draft.}",
        "",
    ]
    current_title: str | None = None
    current_body: list[str] = []

    def flush_section() -> None:
        nonlocal current_title, current_body
        if current_title is None:
            current_body = []
            return
        body = "\n".join(line for line in current_body).strip()
        lines.extend([rf"\paragraph{{{_tex_escape(_namecert_paragraph_title(current_title))}.}}"])
        if body:
            paragraphs = [part.strip() for part in re.split(r"\n\s*\n", body) if part.strip()]
            for paragraph in paragraphs:
                lines.extend([_tex_escape(" ".join(paragraph.splitlines())), ""])
        else:
            lines.extend(["No proposal text recorded.", ""])
        current_title = None
        current_body = []

    for raw_line in markdown_path.read_text(encoding="utf-8").splitlines():
        if raw_line.startswith("## "):
            flush_section()
            current_title = raw_line[3:].strip()
            current_body = []
        elif current_title is not None:
            current_body.append(raw_line)
    flush_section()
    return "\n".join(lines) + "\n"


def _render_conjecture_section(
    conjecture: dict[str, Any],
    contacts_by_id: dict[str, dict[str, Any]],
    probes_by_id: dict[str, dict[str, Any]],
    mismatches_by_probe: dict[str, list[dict[str, Any]]],
) -> list[str]:
    conjecture_id = str(conjecture.get("conjecture_id") or "unnamed")
    form = conjecture.get("bedc_minimal_form") if isinstance(conjecture.get("bedc_minimal_form"), dict) else {}
    contact_refs = [str(item) for item in conjecture.get("reality_contact_refs", []) if isinstance(item, str)]
    probe_refs = [str(item) for item in conjecture.get("probe_refs", []) if isinstance(item, str)]
    lines = [
        rf"\subsection{{{_tex_escape(conjecture_id)}}}",
        "",
        rf"\paragraph{{Biological object.}} {_tex_escape(conjecture.get('biological_object', ''))}",
        "",
        rf"\paragraph{{Current claim.}} {_tex_escape(conjecture.get('informal_statement', ''))}",
        "",
        rf"\paragraph{{External reality input.}}",
    ]
    if contact_refs:
        for contact_ref in contact_refs:
            contact = contacts_by_id.get(contact_ref, {})
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(contact_ref)}}}. {_tex_escape(contact.get('observed_fact', 'missing contact record'))}",
                    "",
                    rf"Can test: {_sentence_list(contact.get('can_test'))}. Cannot test: {_sentence_list(contact.get('cannot_test'))}.",
                    "",
                ]
            )
    else:
        lines.extend(["No external contact is attached.", ""])
    lines.extend(
        [
            rf"\paragraph{{Internal newmath/BEDC derivation.}} Carrier: {_tex_escape(form.get('carrier', ''))}. "
            rf"Distinctions: {_sentence_list(form.get('distinctions'))}. "
            rf"Readback: {_tex_escape(form.get('readback', ''))}. "
            rf"Internal structure: {_sentence_list(form.get('internal_structure'))}.",
            "",
            rf"\paragraph{{Falsifiable probes.}}",
        ]
    )
    if probe_refs:
        for probe_ref in probe_refs:
            probe = probes_by_id.get(probe_ref, {})
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(probe_ref)}}}. {_tex_escape(probe.get('test_statement', 'missing probe record'))}",
                    "",
                    rf"Support condition: {_tex_escape(probe.get('support_condition', ''))}",
                    "",
                    rf"Break condition: {_tex_escape(probe.get('break_condition', ''))}",
                    "",
                ]
            )
    else:
        lines.extend(["No derived probe is attached.", ""])
    lines.append(r"\paragraph{Mismatch ledger.}")
    for probe_ref in probe_refs:
        for mismatch in mismatches_by_probe.get(probe_ref, []):
            lines.extend(
                [
                    rf"\textbf{{{_tex_escape(mismatch.get('mismatch_id', ''))}}}. Status: {_tex_escape(mismatch.get('status', ''))}. "
                    rf"Delta: {_tex_escape(mismatch.get('observed_delta', ''))}",
                    "",
                    rf"Refinement pressure: {_tex_escape(mismatch.get('refinement_pressure', ''))}",
                    "",
                ]
            )
    lines.extend(
        [
            rf"\paragraph{{Cannot-claim boundary.}} {_sentence_list(conjecture.get('forbidden_claims'))}",
            "",
        ]
    )
    lines.extend(_render_verified_facts(conjecture))
    return lines


def _codex_chapter_gate_issues(
    codex_result: dict[str, Any],
    verified_facts: dict[str, Any],
    claim_id: str,
    writer_config: dict[str, Any],
) -> list[str]:
    issues: list[str] = []
    if codex_result.get("verdict") != "ready":
        issues.append(f"codex verdict {codex_result.get('verdict')}")
    audit_score = int(codex_result.get("audit_score") or 0)
    if audit_score < int(writer_config["min_audit_score"]):
        issues.append(f"audit_score {audit_score} below required {writer_config['min_audit_score']}")
    used_fact_ids = [str(item) for item in codex_result.get("used_fact_ids", []) if isinstance(item, str) and item.strip()]
    if len(used_fact_ids) < int(writer_config["min_used_fact_ids"]):
        issues.append(f"used_fact_ids {len(used_fact_ids)} below required {writer_config['min_used_fact_ids']}")
    chapter_text = str(codex_result.get("chapter_content") or "")
    gate_ok, gate_reason = bedc_writeback_gates.check_namecert_generic_prose(chapter_text, verified_facts, claim_id)
    if not gate_ok:
        issues.append(gate_reason)
    if r"\origin{ai}" not in chapter_text:
        issues.append(r"chapter missing \origin{ai}")
    if r"\autoref{" in chapter_text:
        issues.append(r"chapter contains forbidden \autoref")
    issues.extend(bedc_writeback_gates.no_top_level_math_envs(chapter_text))
    issues.extend(bedc_writeback_gates.no_naked_leanstmt(chapter_text))
    return issues


def _codex_written_content(
    render_func: Any,
    render_args: tuple[Any, ...],
    verified_facts: dict[str, Any],
    claim_id: str,
    repo_root: Path,
    writer_config: dict[str, Any],
) -> str | None:
    corrective_feedback: list[str] | None = None
    if not writer_config["enabled"] or not verified_facts:
        return None
    for _attempt_index in range(1, int(writer_config["max_retries"]) + 1):
        codex_result = render_func(
            *render_args,
            repo_root,
            timeout_seconds=int(writer_config["timeout_seconds"]),
            corrective_feedback=corrective_feedback,
            log_dir=str(writer_config["log_dir"]),
        )
        if codex_result is None:
            corrective_feedback = ["codex invocation failed or returned unparsable output"]
            continue
        issues = _codex_chapter_gate_issues(codex_result, verified_facts, claim_id, writer_config)
        if not issues:
            return str(codex_result.get("chapter_content") or "")
        if not writer_config["corrective_retry_on_gate_failure"]:
            break
        corrective_feedback = issues
    return None


def _write_namecert_proposals(
    paths: BioRealityPaths,
    conjectures: list[dict[str, Any]],
    contacts_by_id: dict[str, dict[str, Any]],
    probes_by_id: dict[str, dict[str, Any]],
    mismatches_by_probe: dict[str, list[dict[str, Any]]],
    repo_root: Path,
    writer_config: dict[str, Any],
) -> list[str]:
    proposals_dir = paths.namecert_proposals_dir
    namecerts_dir = paths.paper_part.parent / "namecerts"
    markdown_paths = sorted(proposals_dir.glob("*.md")) if proposals_dir.exists() else []
    if not markdown_paths:
        return []
    namecerts_dir.mkdir(parents=True, exist_ok=True)
    slugs: list[str] = []
    used_slugs: set[str] = set()
    for markdown_path in markdown_paths:
        slug = _namecert_slug(markdown_path)
        original_slug = slug
        suffix = 2
        while slug in used_slugs:
            slug = f"{original_slug}_{suffix}"
            suffix += 1
        used_slugs.add(slug)
        claim_id = _namecert_claim_id(markdown_path)
        conjecture = _linked_conjecture_for_claim(conjectures, claim_id) or {}
        linked_contacts, linked_probes, linked_mismatches = _linked_records_for_conjecture(
            conjecture,
            contacts_by_id,
            probes_by_id,
            mismatches_by_probe,
        )
        verified_facts = _verified_facts_for_claim(conjecture, claim_id)
        codex_text = _codex_written_content(
            render_namecert_with_codex,
            (claim_id, slug, verified_facts, conjecture, linked_contacts, linked_probes, linked_mismatches),
            verified_facts,
            claim_id,
            repo_root,
            writer_config,
        )
        text = codex_text if codex_text else _render_namecert_proposal(markdown_path, slug)
        (namecerts_dir / f"{slug}.tex").write_text(text, encoding="utf-8")
        slugs.append(slug)
    return slugs


def run_writeback_lane(store: BioRealityStore) -> dict[str, Any]:
    writer_config = _bio_w_codex_writer_config(_load_writeback_lane_config())
    repo_root = store.paths.root.parent.parent
    conjectures = _passed_conjectures(store)
    contacts = store.load_contacts()
    probes = store.load_probes()
    mismatches = store.load_mismatches()
    contacts_by_id = _by_id(contacts, "contact_id")
    probes_by_id = _by_id(probes, "probe_id")
    mismatches_by_probe: dict[str, list[dict[str, Any]]] = {}
    for mismatch in mismatches:
        probe_ref = str(mismatch.get("probe_ref") or "")
        if probe_ref:
            mismatches_by_probe.setdefault(probe_ref, []).append(mismatch)

    part_lines = [
        r"\section{Codon Window Reality Boundary}",
        r"\label{sec:codon-window-reality-boundary}",
        "",
        "This section records gate-passed BioReality research memory. "
        "Its statements separate curated biological reality contacts from internal coordinate, closure, spectrum, and relation readings.",
        "",
    ]
    for conjecture in conjectures:
        linked_contacts, linked_probes, linked_mismatches = _linked_records_for_conjecture(
            conjecture,
            contacts_by_id,
            probes_by_id,
            mismatches_by_probe,
        )
        verified_facts = _all_verified_facts(conjecture)
        conjecture_id = str(conjecture.get("conjecture_id") or "unnamed")
        codex_text = _codex_written_content(
            render_conjecture_with_codex,
            (conjecture, verified_facts, linked_contacts, linked_probes, linked_mismatches),
            verified_facts,
            conjecture_id,
            repo_root,
            writer_config,
        )
        if codex_text:
            part_lines.extend([codex_text.rstrip(), ""])
        else:
            part_lines.extend(_render_conjecture_section(conjecture, contacts_by_id, probes_by_id, mismatches_by_probe))
    if not conjectures:
        part_lines.extend(["No conjecture has passed the BioReality gates.", ""])

    paths = store.paths
    paths.paper_main.parent.mkdir(parents=True, exist_ok=True)
    paths.paper_part.parent.mkdir(parents=True, exist_ok=True)
    paths.paper_part.write_text("\n".join(part_lines), encoding="utf-8")
    namecert_slugs = _write_namecert_proposals(
        paths,
        conjectures,
        contacts_by_id,
        probes_by_id,
        mismatches_by_probe,
        repo_root,
        writer_config,
    )
    paths.paper_main.write_text(_render_paper_main(paths, namecert_slugs), encoding="utf-8")
    return {
        "lane": "bio-W",
        "paper_main": str(paths.paper_main),
        "paper_part": str(paths.paper_part),
        "written_conjectures": len(conjectures),
        "namecerts_written": len(namecert_slugs),
    }


def _append_bedc_writeback_log(store: BioRealityStore, event: str, details: dict[str, Any]) -> None:
    record = {"ts": now_iso(), "event": event, "details": details}
    try:
        store.paths.bedc_writeback_log.parent.mkdir(parents=True, exist_ok=True)
        with store.paths.bedc_writeback_log.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")
    except OSError:
        return


def _mapping_records(config: dict[str, Any]) -> list[dict[str, Any]]:
    mappings = config.get("claim_to_chapter_mapping")
    if not isinstance(mappings, list):
        return []
    return [item for item in mappings if isinstance(item, dict)]


def _skip_claim_ids(config: dict[str, Any]) -> set[str]:
    raw = config.get("skip_claim_ids")
    if not isinstance(raw, list):
        return set()
    return {str(item) for item in raw if str(item)}


def _markdown_section(text: str, heading_re: str) -> str:
    lines = text.splitlines()
    start: int | None = None
    for index, line in enumerate(lines):
        if re.match(heading_re, line.strip()):
            start = index + 1
            break
    if start is None:
        return ""
    section_lines: list[str] = []
    for line in lines[start:]:
        if re.match(r"^##\s+", line.strip()):
            break
        section_lines.append(line)
    return "\n".join(section_lines).strip()


def _first_markdown_paragraph(text: str) -> str:
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n", text) if part.strip()]
    return paragraphs[0] if paragraphs else ""


def _auto_discovered_bedc_mappings(proposal_dir: Path, mapped_claim_ids: set[str]) -> list[dict[str, Any]]:
    if not proposal_dir.exists():
        return []
    derived: list[dict[str, Any]] = []
    for proposal_path in sorted(proposal_dir.glob("*.md"), key=lambda path: path.stem):
        if not proposal_path.is_file():
            continue
        claim_id = proposal_path.stem
        if claim_id == "self.claim" or claim_id in mapped_claim_ids:
            continue
        try:
            proposal_text = proposal_path.read_text(encoding="utf-8")
        except OSError:
            continue
        slug_section = _markdown_section(proposal_text, r"^##\s+1\.\s+Loning-format chapter slug\s*$")
        carrier_section = _markdown_section(proposal_text, r"^##\s+2\.\s+Carrier\s*$")
        slug_match = re.search(
            r"(\d{4,6}_[a-z0-9_]+_namecert_construction)",
            _first_markdown_paragraph(slug_section),
        )
        carrier_match = re.search(r"\b(BioReality\w+|RealityBound\w+|Empirical\w+|Curated\w+)\b", carrier_section)
        if not slug_match or not carrier_match:
            continue
        proposed_slug = slug_match.group(1)
        carrier_name = carrier_match.group(1)
        derived.append(
            {
                "claim_id": claim_id,
                "hub_filename": f"{proposed_slug}.tex",
                "subdir_slug": proposed_slug.rsplit("_namecert_construction", 1)[0],
                "carrier_name": carrier_name.rstrip("Up"),
                "natural_language": f"the finite reality-bound seed witness for {claim_id}",
            }
        )
    return derived


def _repo_path(value: Any, repo_root: Path) -> Path:
    text = str(value or "")
    path = Path(text)
    return path if path.is_absolute() else repo_root / path


def _tex_literal(value: Any) -> str:
    return _tex_escape(value)


def _render_bedc_hub(mapping: dict[str, Any]) -> str:
    claim_id = _tex_literal(mapping.get("claim_id", "unnamed"))
    subdir_slug = str(mapping.get("subdir_slug") or "bioreality_packet")
    return "\n".join(
        [
            f"% Auto-generated BioReality NameCert hub for {claim_id}.",
            "% This hub follows the newmath concrete-instances hub+subdir layout.",
            r"% Only orienting prose and \input lines are allowed here.",
            rf"\input{{parts/concrete_instances/{subdir_slug}/namecert_construction}}",
            "",
        ]
    )


def _render_bedc_spine(mapping: dict[str, Any], proposal_text: str, conjecture: dict[str, Any] | None) -> str:
    claim_id = _tex_literal(mapping.get("claim_id", "unnamed"))
    subdir_slug = str(mapping.get("subdir_slug") or "bioreality_packet")
    carrier_name = re.sub(r"[^A-Za-z0-9]", "", str(mapping.get("carrier_name") or "BioRealityPacket")) or "BioRealityPacket"
    natural_language = _tex_literal(mapping.get("natural_language", "a finite reality-bound BioReality packet"))
    _ = proposal_text
    forbidden_claims = conjecture.get("forbidden_claims") if conjecture else []
    verified_facts = conjecture.get("verified_facts") if conjecture else {}
    if isinstance(forbidden_claims, list):
        _ = [str(item) for item in forbidden_claims if isinstance(item, str)]
    if isinstance(verified_facts, dict):
        _ = sorted(str(key) for key in verified_facts)
    return "\n".join(
        [
            rf"\chapter{{A Concrete Naming Certificate for $\{carrier_name}Up$}}",
            rf"\label{{ch:concrete-instances-{subdir_slug}-namecert}}",
            r"\origin{ai}",
            "",
            f"This BioReality NameCert packet records a finite, reality-bound seed",
            f"witness for the claim {claim_id}. It does not claim biological-code",
            "necessity, translation realization, folded structure, physical",
            "admissibility, function realization, mechanism, or universality. The",
            "external curated standard-code bridge and the empirical witness rows",
            "remain provenance fields and are not BEDC kernel facts.",
            "",
            rf"\paragraph{{Carrier.}} $\{carrier_name}Up$ is the BEDC packet name we",
            f"reserve for the finite reality-bound seed of {natural_language}.",
            "",
            r"\paragraph{External reality bridge.} A curated standard-code bridge",
            "row is the external source for the labelling. The bridge appears as a",
            "provenance row and not as kernel content of the packet. The bridge can",
            "test code-layer readback only; it cannot test translation, folding,",
            "physical admissibility, or function.",
            "",
            r"\paragraph{Internal coordinate structure.} The packet records six-bit",
            "codon-coordinate, median-closure, quotient, and spectrum bookkeeping.",
            "No biological mechanism, function, or universality is asserted at this",
            "layer.",
            "",
            r"\paragraph{Cannot-claim boundary.}",
            r"\begin{itemize}",
            "  \\item This chapter does not claim biological-code necessity.",
            "  \\item This chapter does not claim window-six geometry realizes translation.",
            "  \\item This chapter does not claim folded protein structure, physical admissibility, biological function, or universal mechanism from this packet.",
            "  \\item This chapter does not claim that a curated code-row, spectral value, polynomial coefficient, tolerance threshold, or statistical witness is a BEDC kernel fact.",
            r"\end{itemize}",
            "",
            rf"\falsifiablePrediction{{A $\{carrier_name}Up$ packet cannot export a",
            "translation, folding, physical admissibility, function realization, or",
            "universality claim without a separate, independent external reality",
            "contact that can test that higher layer.}",
            "",
            r"\independenceWitness{The carrier records only coordinate, closure,",
            "quotient, and spectrum bookkeeping; it does not export biological",
            "mechanism, evolutionary necessity, or biochemical detail. Any apparent",
            "biological consequence must be re-derived through a separate bridge.}",
            "",
            rf"\closureat{{{carrier_name}Up}}{{seedStr}}",
            rf"\begin{{closurestatus}}{{\{carrier_name}Up}}",
            f"  \\constructivestory{{Finite reality-bound seed witness for {claim_id};",
            "    records six-bit codon-coordinate and closure/spectrum bookkeeping",
            "    behind a curated standard-code bridge.}",
            r"  \theoryclosure{\seedClosure}",
            "  \\scopeclosed{Code-layer readback under the curated standard-code",
            "    bridge only.}",
            r"  \formalstatus{\unformalizedV}",
            r"  \bridgestatus{paperBridge}",
            "  \\notclaimed{This chapter does not close biological-code necessity,",
            "    translation realization, folded structure, physical admissibility,",
            "    function realization, mechanism, universality, or any cross-layer",
            "    biological consequence.}",
            "  \\upgradepath{Attach a separate reality contact that can test the",
            "    higher realization layer and re-derive through a new bridge",
            "    chapter.}",
            r"\end{closurestatus}",
            "",
        ]
    )


def _bedc_codex_writer_config(config: dict[str, Any]) -> dict[str, Any]:
    raw = config.get("codex_writer")
    writer = raw if isinstance(raw, dict) else {}
    return {
        "enabled": bool(writer.get("enabled", True)),
        "max_retries": max(1, int(writer.get("max_retries", config.get("codex_max_retries") or 2))),
        "timeout_seconds": max(1, int(writer.get("timeout_seconds", config.get("codex_timeout_seconds") or 600))),
        "log_dir": str(writer.get("log_dir", config.get("codex_log_dir") or "tools/bio_reality/state/bedc_writeback_logs")),
        "min_audit_score": int(writer.get("min_audit_score", config.get("min_audit_score") or 7)),
        "min_used_fact_ids": max(0, int(writer.get("min_used_fact_ids", config.get("min_used_fact_ids") or 3))),
        "corrective_retry_on_gate_failure": bool(writer.get("corrective_retry_on_gate_failure", True)),
    }


def _safe_task_id(value: str) -> str:
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", value).strip("._")
    return safe or "unnamed"


def _tail_text(value: str, limit: int = 4000) -> str:
    return value[-limit:] if len(value) > limit else value


def _codex_author_prompt(
    target: dict[str, Any],
    verified_facts: dict[str, Any],
    corrective_feedback: list[str] | None = None,
) -> str:
    claim_id = str(target.get("claim_id") or "")
    carrier_name = re.sub(r"Up$", "", str(target.get("carrier_name") or ""))
    subdir_slug = str(target.get("subdir_slug") or "")
    hub_filename = str(target.get("hub_filename") or "")
    facts_json = json.dumps(verified_facts, ensure_ascii=False, indent=2, sort_keys=True)
    lines = [
        "你是 BioReality NameCert chapter author. 你只写 LaTeX content, 不直接写文件.",
        "",
        "# Target",
        f"claim_id: {claim_id}",
        f"carrier_name: {carrier_name}",
        f"subdir_slug: {subdir_slug}",
        f"hub_filename: {hub_filename}",
        "",
        "# Verified facts (硬数据, 不许造数, 不许超出此范围)",
        "```json",
        facts_json,
        "```",
        "",
        "# BEDC self-contained 硬约束",
        r"- 不写 \autoref 引其它 chapter",
        r"- 不写 Lean 宏 (\leanchecked / \leanstmt / \leandef / \leanvariant / \leansorryd / \leantarget)",
        "- 不写 file path / URL / experiment_run_id 字面值在 kernel prose 里 (这些只能在 bridge/provenance 字段)",
        r"- 数学环境: 行内 $...$, 展示 $$\begin{aligned}$$ / $$\begin{gathered}$$, **禁** \begin{equation} / align / eqnarray / \[...\]",
        r"- \FooUp 类宏在 text-mode 参数必须 $...$ 包裹",
        "- spine <= 800 行",
        r"- hub <= 15 行, 仅 \input + orienting prose, 无 theorem env, 无 closurestatus",
        "- 完整 closurestatus block (constructivestory / theoryclosure / scopeclosed / formalstatus / bridgestatus / notclaimed / upgradepath) 全 7 字段非空",
        "",
        "# 必须章节特定差异化 (反对 generic template)",
        "- 章节正文必须明确点名 verified_facts 中至少 3 个具体数字 / row count / witness name / codon list / p-value",
        '- output JSON 的 used_fact_ids 字段必须列出实际引用了哪些 verified_facts key (e.g. ["M_codons", "lambda_M", "p_exact", ...])',
        '- 不许写"finite reality-bound seed witness for the claim X"这种 generic 套话',
        "",
    ]
    if corrective_feedback:
        lines.extend(
            [
                "# Corrective retry feedback",
                "上一轮没有通过 gate. 这轮必须修正以下问题, 仍然只返回 schema 要求的单一 JSON object:",
            ]
        )
        for issue in corrective_feedback:
            lines.append(f"- {issue}")
        lines.append("")
    lines.extend(
        [
            "# Output schema (返回 单一 JSON object, 在 stdout 最后一非空行)",
            "{",
            '  "verdict": "ready" | "needs_more_facts" | "abort",',
            '  "audit_score": 0-10 (自评章节质量),',
            '  "used_fact_ids": ["..."],',
            '  "hub_content": "<完整 LaTeX hub 内容 <=15 行>",',
            '  "spine_content": "<完整 LaTeX spine 内容 <=800 行>",',
            '  "risk_notes": "可选诊断"',
            "}",
            "",
            'verdict="needs_more_facts" 表示 verified_facts 不足以写出 chapter-specific prose, 拒绝 hallucinate.',
            'verdict="abort" 表示 prompt 内有冲突 / 无法满足约束.',
            'verdict="ready" 表示 hub_content + spine_content 已生成可写.',
            "",
            "audit_score < 7 时, caller 把 used_fact_ids 数 / 不足之处反馈喂下一轮 retry.",
        ]
    )
    return "\n".join(lines)


def _parse_codex_author_json(stdout: str) -> dict[str, Any]:
    nonempty = [line.strip() for line in stdout.splitlines() if line.strip()]
    if not nonempty:
        return {"status": "error", "error_kind": "empty_stdout"}
    agent_text = _extract_codex_event_text(stdout)
    candidates: list[str] = []
    if agent_text and agent_text != stdout:
        candidates.append(agent_text)
        fence_matches = list(re.finditer(r"```(?:json)?\s*(\{.*?\})\s*```", agent_text, re.DOTALL | re.IGNORECASE))
        candidates.extend(match.group(1) for match in fence_matches)
        first = agent_text.find("{")
        last = agent_text.rfind("}")
        if first != -1 and last != -1 and last > first:
            candidates.append(agent_text[first : last + 1])
    candidates.append(nonempty[-1])
    parsed = None
    last_error: str = ""
    for candidate in candidates:
        try:
            obj = json.loads(candidate)
        except json.JSONDecodeError as exc:
            last_error = str(exc)
            continue
        if isinstance(obj, dict) and "verdict" in obj:
            parsed = obj
            break
        if isinstance(obj, dict) and parsed is None:
            parsed = obj
    if parsed is None:
        return {"status": "error", "error_kind": "non_json_output", "error": last_error or "no JSON object found"}
    if not isinstance(parsed, dict):
        return {"status": "error", "error_kind": "schema_invalid", "error": "top-level output is not an object"}
    required = ["verdict", "audit_score", "used_fact_ids", "hub_content", "spine_content", "risk_notes"]
    missing = [field for field in required if field not in parsed]
    if missing:
        return {"status": "error", "error_kind": "schema_invalid", "error": f"missing field(s): {', '.join(missing)}", "parsed": parsed}
    if parsed.get("verdict") not in {"ready", "needs_more_facts", "abort"}:
        return {"status": "error", "error_kind": "schema_invalid", "error": "invalid verdict", "parsed": parsed}
    try:
        audit_score = int(parsed.get("audit_score"))
    except (TypeError, ValueError):
        return {"status": "error", "error_kind": "schema_invalid", "error": "audit_score is not an integer", "parsed": parsed}
    if audit_score < 0 or audit_score > 10:
        return {"status": "error", "error_kind": "schema_invalid", "error": "audit_score outside 0-10", "parsed": parsed}
    if not isinstance(parsed.get("used_fact_ids"), list) or not all(isinstance(item, str) for item in parsed["used_fact_ids"]):
        return {"status": "error", "error_kind": "schema_invalid", "error": "used_fact_ids must be a string list", "parsed": parsed}
    if not isinstance(parsed.get("hub_content"), str) or not isinstance(parsed.get("spine_content"), str):
        return {"status": "error", "error_kind": "schema_invalid", "error": "hub_content and spine_content must be strings", "parsed": parsed}
    if not isinstance(parsed.get("risk_notes"), str):
        return {"status": "error", "error_kind": "schema_invalid", "error": "risk_notes must be a string", "parsed": parsed}
    parsed["audit_score"] = audit_score
    parsed["status"] = "ok"
    return parsed


def _write_codex_author_logs(log_dir: Path, task_id: str, prompt: str, raw: str, parsed: dict[str, Any]) -> None:
    try:
        log_dir.mkdir(parents=True, exist_ok=True)
        (log_dir / f"{task_id}.prompt.txt").write_text(prompt, encoding="utf-8")
        (log_dir / f"{task_id}.raw.txt").write_text(raw, encoding="utf-8")
        (log_dir / f"{task_id}.parsed.txt").write_text(json.dumps(parsed, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except OSError:
        return


def render_chapter_with_codex(
    target: dict[str, Any],
    verified_facts: dict[str, Any],
    repo_root: Path,
    *,
    timeout_seconds: int = 600,
    log_dir: str | Path = "tools/bio_reality/state/bedc_writeback_logs",
    corrective_feedback: list[str] | None = None,
) -> dict[str, Any]:
    prompt = _codex_author_prompt(target, verified_facts, corrective_feedback=corrective_feedback)
    claim_id = str(target.get("claim_id") or "unnamed")
    attempt = str(target.get("_codex_attempt") or "1")
    task_id = _safe_task_id(f"{claim_id}.attempt-{attempt}")
    log_path = Path(log_dir)
    if not log_path.is_absolute():
        log_path = repo_root / log_path
    raw_stdout = ""
    raw_stderr = ""
    try:
        completed = subprocess.run(
            [
                "codex",
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--sandbox",
                "read-only",
                "--json",
                "-C",
                str(repo_root),
                "-",
            ],
            input=prompt,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
            check=False,
        )
        raw_stdout = completed.stdout or ""
        raw_stderr = completed.stderr or ""
    except subprocess.TimeoutExpired as exc:
        raw_stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        raw_stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        parsed = {
            "status": "error",
            "error_kind": "timeout",
            "raw_stdout_tail": _tail_text(raw_stdout),
            "raw_stderr_tail": _tail_text(raw_stderr),
        }
        _write_codex_author_logs(log_path, task_id, prompt, raw_stdout + "\n--- STDERR ---\n" + raw_stderr, parsed)
        return parsed
    except OSError as exc:
        parsed = {
            "status": "error",
            "error_kind": "exec_failed",
            "error": str(exc),
            "raw_stdout_tail": "",
            "raw_stderr_tail": "",
        }
        _write_codex_author_logs(log_path, task_id, prompt, "", parsed)
        return parsed

    parsed = _parse_codex_author_json(raw_stdout)
    if parsed.get("status") == "error":
        parsed["raw_stdout_tail"] = _tail_text(raw_stdout)
        parsed["raw_stderr_tail"] = _tail_text(raw_stderr)
    raw = raw_stdout + "\n--- STDERR ---\n" + raw_stderr
    _write_codex_author_logs(log_path, task_id, prompt, raw, parsed)
    return parsed


def _linked_conjecture_for_claim(conjectures: list[dict[str, Any]], claim_id: str) -> dict[str, Any] | None:
    for conjecture in conjectures:
        if str(conjecture.get("conjecture_id") or "") == claim_id:
            return conjecture
        linked = conjecture.get("linked_claim_ids")
        if isinstance(linked, list) and claim_id in [str(item) for item in linked]:
            return conjecture
        verified = conjecture.get("verified_facts")
        if isinstance(verified, dict) and claim_id in verified:
            return conjecture
    return None


def _ensure_aggregator_line(aggregator: Path, subdir_slug: str) -> None:
    line = rf"\input{{parts/concrete_instances/{subdir_slug}/namecert_construction}}"
    if aggregator.exists():
        text = aggregator.read_text(encoding="utf-8")
        if line in text.splitlines():
            return
        text = text.rstrip() + "\n" + line + "\n"
    else:
        text = "\n".join(
            [
                "% BioReality BEDC module aggregator.",
                "% Operators input this file from the BEDC paper integration point.",
                line,
                "",
            ]
        )
    aggregator.parent.mkdir(parents=True, exist_ok=True)
    aggregator.write_text(text, encoding="utf-8")


def run_bedc_writeback_lane(store: BioRealityStore) -> dict[str, Any]:
    try:
        config = _load_bedc_writeback_config()
    except (OSError, json.JSONDecodeError) as exc:
        _append_bedc_writeback_log(store, "config_error", {"error": str(exc)})
        return {"lane": "bio-B", "error": "config_error"}
    if not config.get("enabled"):
        return {"lane": "bio-B", "skipped": "disabled"}

    repo_root = store.paths.root.parent.parent
    target_dir = _repo_path(config.get("target_concrete_instances_dir"), repo_root)
    aggregator = _repo_path(config.get("module_aggregator"), repo_root)
    max_writebacks = max(1, int(config.get("max_writebacks_per_cycle") or 1))
    writer_config = _bedc_codex_writer_config(config)
    conjectures = store.load_conjectures()
    proposal_dir = store.paths.namecert_proposals_dir
    attempted = 0
    written = 0
    blocked_by_gate = 0
    auto_discovered_written = 0
    issues_summary: list[dict[str, Any]] = []
    config_mappings = _mapping_records(config)
    skipped_claim_ids = _skip_claim_ids(config)
    mapped_claim_ids = {str(mapping.get("claim_id") or "") for mapping in config_mappings}
    auto_mappings = _auto_discovered_bedc_mappings(proposal_dir, mapped_claim_ids)
    mapping_queue: list[tuple[str, dict[str, Any]]] = [("config", mapping) for mapping in config_mappings]
    mapping_queue.extend(("auto", mapping) for mapping in auto_mappings)
    skipped_by_dedup = 0

    for mapping_source, mapping in mapping_queue:
        if written >= max_writebacks:
            break
        claim_id = str(mapping.get("claim_id") or "")
        if claim_id in skipped_claim_ids:
            skipped_by_dedup += 1
            continue
        hub_filename = str(mapping.get("hub_filename") or "")
        subdir_slug = str(mapping.get("subdir_slug") or "")
        if not claim_id or not hub_filename or not subdir_slug:
            issues_summary.append({"claim_id": claim_id, "issues": ["mapping missing claim_id, hub_filename, or subdir_slug"]})
            continue
        hub_path = target_dir / hub_filename
        if hub_path.exists():
            continue
        proposal_path = proposal_dir / f"{claim_id}.md"
        if not proposal_path.exists():
            continue
        attempted += 1
        proposal_text = proposal_path.read_text(encoding="utf-8")
        conjecture = _linked_conjecture_for_claim(conjectures, claim_id)
        verified_facts: dict[str, Any] = {}
        if conjecture:
            raw_verified = conjecture.get("verified_facts")
            if isinstance(raw_verified, dict):
                claim_facts = raw_verified.get(claim_id)
                if isinstance(claim_facts, dict):
                    verified_facts = claim_facts
        hub_text = ""
        spine_text = ""
        used_fact_ids: list[str] | None = None
        gate_result: dict[str, Any] | None = None
        codex_blocked = False
        if writer_config["enabled"]:
            if not verified_facts:
                blocked_by_gate += 1
                issue_record = {"claim_id": claim_id, "issues": ["no_verified_facts"]}
                issues_summary.append(issue_record)
                _append_bedc_writeback_log(store, "no_verified_facts", issue_record)
                continue
            corrective_feedback: list[str] | None = None
            for attempt_index in range(1, int(writer_config["max_retries"]) + 1):
                codex_target = dict(mapping)
                codex_target["_codex_attempt"] = attempt_index
                codex_result = render_chapter_with_codex(
                    codex_target,
                    verified_facts,
                    repo_root,
                    timeout_seconds=int(writer_config["timeout_seconds"]),
                    log_dir=str(writer_config["log_dir"]),
                    corrective_feedback=corrective_feedback,
                )
                if codex_result.get("status") != "ok":
                    corrective_feedback = [str(codex_result.get("error_kind") or "codex output failed schema validation")]
                    _append_bedc_writeback_log(
                        store,
                        "codex_writer_error",
                        {
                            "claim_id": claim_id,
                            "attempt": attempt_index,
                            "error_kind": codex_result.get("error_kind"),
                            "raw_stdout_tail": codex_result.get("raw_stdout_tail", ""),
                            "raw_stderr_tail": codex_result.get("raw_stderr_tail", ""),
                        },
                    )
                    continue
                if codex_result.get("verdict") != "ready":
                    codex_blocked = True
                    issue_record = {
                        "claim_id": claim_id,
                        "issues": [f"codex verdict {codex_result.get('verdict')}"],
                        "risk_notes": codex_result.get("risk_notes", ""),
                    }
                    issues_summary.append(issue_record)
                    _append_bedc_writeback_log(store, "codex_writer_blocked", issue_record)
                    break
                used_fact_ids = [str(item) for item in codex_result.get("used_fact_ids", []) if isinstance(item, str)]
                audit_score = int(codex_result.get("audit_score") or 0)
                hub_text = str(codex_result.get("hub_content") or "")
                spine_text = str(codex_result.get("spine_content") or "")
                candidate_issues: list[str] = []
                if audit_score < int(writer_config["min_audit_score"]):
                    candidate_issues.append(
                        f"audit_score {audit_score} below required {writer_config['min_audit_score']}"
                    )
                gate_result = bedc_writeback_gates.validate_chapter_pair(
                    hub_text,
                    spine_text,
                    used_fact_ids,
                    int(writer_config["min_used_fact_ids"]),
                )
                candidate_issues.extend(str(issue) for issue in gate_result["issues"])
                if not candidate_issues:
                    break
                if attempt_index >= int(writer_config["max_retries"]) or not writer_config["corrective_retry_on_gate_failure"]:
                    gate_result = dict(gate_result)
                    gate_result["issues"] = candidate_issues
                    break
                corrective_feedback = candidate_issues
            else:
                gate_result = None
            if codex_blocked:
                blocked_by_gate += 1
                continue
        if not hub_text or not spine_text:
            hub_text = _render_bedc_hub(mapping)
            spine_text = _render_bedc_spine(mapping, proposal_text, conjecture)
            used_fact_ids = None
            gate_result = bedc_writeback_gates.validate_chapter_pair(hub_text, spine_text)
        elif gate_result is None:
            gate_result = bedc_writeback_gates.validate_chapter_pair(
                hub_text,
                spine_text,
                used_fact_ids,
                int(writer_config["min_used_fact_ids"]) if writer_config["enabled"] else 0,
            )
        if not gate_result["passed"]:
            blocked_by_gate += 1
            issue_record = {"claim_id": claim_id, "issues": gate_result["issues"]}
            issues_summary.append(issue_record)
            _append_bedc_writeback_log(store, "gate_blocked", issue_record)
            continue

        spine_path = target_dir / subdir_slug / "namecert_construction.tex"
        hub_path.parent.mkdir(parents=True, exist_ok=True)
        spine_path.parent.mkdir(parents=True, exist_ok=True)
        hub_path.write_text(hub_text, encoding="utf-8")
        spine_path.write_text(spine_text, encoding="utf-8")
        _ensure_aggregator_line(aggregator, subdir_slug)
        written += 1
        _append_bedc_writeback_log(
            store,
            "written",
            {"claim_id": claim_id, "hub_filename": hub_filename, "subdir_slug": subdir_slug},
        )
        if mapping_source == "auto":
            auto_discovered_written += 1

    return {
        "lane": "bio-B",
        "attempted": attempted,
        "written": written,
        "blocked_by_gate": blocked_by_gate,
        "auto_discovered_candidates": len(auto_mappings),
        "auto_discovered_written": auto_discovered_written,
        "skipped_by_dedup": skipped_by_dedup,
        "issues_summary": issues_summary,
    }


def render_lane_dashboard(paths: BioRealityPaths, targets: list[dict[str, Any]], signals: dict[str, Any] | None = None) -> None:
    lines = [
        "# BioReality lane dashboard",
        "",
        f"- checked_at: {now_iso()}",
        f"- packet_targets: {len(targets)}",
    ]
    if signals:
        lines.extend(
            [
                f"- gate_results: {signals.get('gate_results', 0)}",
                f"- blocked: {signals.get('blocked', 0)}",
                f"- deepening_tasks: {signals.get('deepening_tasks', 0)}",
                f"- review_ready: {signals.get('review_ready', 0)}",
                f"- events: {signals.get('events', 0)}",
                f"- agent_tasks: {signals.get('agent_tasks', 0)}",
                f"- dispatch_results: {signals.get('dispatch_results', 0)}",
                f"- dispatch_planned_only: {signals.get('dispatch_planned_only', 0)}",
                f"- hardening_targets: {signals.get('hardening_targets', 0)}",
                f"- vision_rows: {signals.get('vision_rows', 0)}",
            ]
        )
    lines.extend(
        [
            "",
            "V lane scans user-authored vision files. P lane writes runtime packet targets only. G lane runs boundary gates.",
            "R lane plans Codex agent tasks from events. W lane writes only the",
            "standalone BioReality paper. Q lane converts review outcomes into",
            "hardening targets. A lane summarizes failures and scheduling pressure.",
            "No lane writes BEDC paper, Lean, remote refs, or un-gated biological conclusions.",
            "",
            "## Packet targets",
            "",
        ]
    )
    for target in targets[:40]:
        lines.append(
            f"- {target.get('lane')} {target.get('packet_kind')}:{target.get('packet_id')} "
            f"priority={target.get('priority')} - {target.get('reason')}"
        )
    lines.append("")
    paths.lane_dashboard.parent.mkdir(parents=True, exist_ok=True)
    paths.lane_dashboard.write_text("\n".join(lines), encoding="utf-8")


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="bio-reality-lanes-") as tmp:
        base = Path(tmp)
        paths = _temp_paths(base)
        writeback_disabled_config_path = base / "writeback_disabled_pipeline_config.json"
        writeback_disabled_config_path.write_text(
            json.dumps({"lanes": [{"lane": "bio-W", "codex_writer": {"enabled": False}}]}, indent=2),
            encoding="utf-8",
        )
        disabled_config_path = base / "disabled_pipeline_config.json"
        disabled_config_path.write_text(json.dumps({"sync_lane": {"enabled": False}}, indent=2), encoding="utf-8")
        oracle_disabled_config_path = base / "oracle_disabled_pipeline_config.json"
        oracle_disabled_config_path.write_text(json.dumps({"oracle_integration": {"enabled": False}}, indent=2), encoding="utf-8")
        oracle_config_path = base / "oracle_pipeline_config.json"
        oracle_config_path.write_text(
            json.dumps(
                {
                    "oracle_integration": {
                        "enabled": True,
                        "server_url": "http://127.0.0.1:8769",
                        "pdf_attach_path": "missing-main.pdf",
                        "persist_dir": str(base / "oracle_sessions"),
                        "bio_g": {
                            "enabled": True,
                            "max_turns": 10,
                            "min_seconds_between_consultations": 1800,
                            "codex_judge_timeout_seconds": 5,
                            "poll_timeout_seconds": 5,
                        },
                        "bio_plan": {
                            "enabled": True,
                            "max_turns": 12,
                            "min_cycles_between_consultations": 5,
                            "codex_judge_timeout_seconds": 5,
                            "poll_timeout_seconds": 5,
                        },
                    }
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = disabled_config_path
        try:
            disabled_summary = run_sync_lane(BioRealityStore(paths))
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if disabled_summary != {"lane": "bio-S", "skipped": "disabled"}:
            print(json.dumps(disabled_summary, indent=2), file=sys.stderr)
            return 1

        log_output = "\n".join(
            [
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa|Add codon science note",
                "papers/bedc/parts/visions/philosophy/science/codon_window.tex",
                "lean4/BEDC/Derived/Genetic/StopCodon.lean",
                "",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb|Adjust unrelated prose",
                "docs/roadmap.txt",
                "",
                "cccccccccccccccccccccccccccccccccccccccc|Protein path only",
                "papers/bedc/parts/concrete_instances/protein/namecert_construction.tex",
            ]
        )
        parsed_commits = _parse_sync_git_log(log_output)
        if len(parsed_commits) != 3 or parsed_commits[0]["files"] != [
            "papers/bedc/parts/visions/philosophy/science/codon_window.tex",
            "lean4/BEDC/Derived/Genetic/StopCodon.lean",
        ]:
            print(json.dumps(parsed_commits, indent=2), file=sys.stderr)
            return 1
        records = _sync_intelligence_records(
            parsed_commits,
            ["codon", "genetic", "amino", "bio", "protein", "dna", "rna", "translation", "ribosom", "nucleotide", "tRNA"],
            [
                "papers/bedc/parts/visions/philosophy/science/",
                "papers/bedc/parts/concrete_instances/",
                "lean4/BEDC/Derived/",
            ],
        )
        if len(records) != 2:
            print(json.dumps(records, indent=2), file=sys.stderr)
            return 1
        first_record = records[0]
        if first_record["loning_commit_sha"] != "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa":
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1
        if "codon" not in first_record["matched_keywords"] or "genetic" not in first_record["matched_keywords"]:
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1
        if "papers/bedc/parts/visions/philosophy/science/" not in first_record["matched_paths"]:
            print(json.dumps(first_record, indent=2), file=sys.stderr)
            return 1

        paths.vision_dir.mkdir(parents=True)
        (paths.vision_dir / "dna-to-protein-boundary.md").write_text(
            "\n".join(
                [
                    "---",
                    "slug: dna-to-protein-boundary",
                    'title: "Separate code readback from protein realization"',
                    "target_paper_section:",
                    "  - papers/bio_reality/parts/codon_window_reality_boundary.tex",
                    "required_reality_contacts:",
                    "  - curated.standard.code.table",
                    "required_gates:",
                    "forbidden_claims_to_check:",
                    "  - local_tile_as_global_biological_law",
                    "ripeness: ready",
                    "---",
                    "",
                    "Keep code-layer reality separate from protein realization.",
                ]
            ),
            encoding="utf-8",
        )
        store = BioRealityStore(paths)
        vision_summary = run_vision_lane(store)
        packet_summary = run_packet_lane(store)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = oracle_disabled_config_path
        try:
            gate_summary = run_gate_lane(store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        agent_summary = run_agent_lane(store, execute_codex=False)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = writeback_disabled_config_path
        try:
            writeback_summary = run_writeback_lane(store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        quality_summary = run_quality_lane(store)
        signals = run_assimilation_lane(paths)
        targets = read_jsonl(paths.packet_targets)
        if not packet_summary.get("bootstrapped") or packet_summary["conjectures"] != 2:
            print(json.dumps(packet_summary, indent=2), file=sys.stderr)
            return 1
        if packet_summary["promotion"].get("to_layer") != "orf_eligibility":
            print(json.dumps(packet_summary, indent=2), file=sys.stderr)
            return 1
        if vision_summary["visions"] != 1 or vision_summary["ready"] != 0:
            print(json.dumps(vision_summary, indent=2), file=sys.stderr)
            return 1
        if gate_summary["blocked"] != 1 or gate_summary["review_items"] == 0:
            print(json.dumps(gate_summary, indent=2), file=sys.stderr)
            return 1
        if signals["packet_targets"] != len(targets):
            print(json.dumps({"gate": gate_summary, "signals": signals}, indent=2), file=sys.stderr)
            return 1
        if writeback_summary["written_conjectures"] != 1 or not paths.paper_part.exists():
            print(json.dumps(writeback_summary, indent=2), file=sys.stderr)
            return 1
        if agent_summary["events"] == 0 or agent_summary["agent_tasks"] == 0:
            print(json.dumps(agent_summary, indent=2), file=sys.stderr)
            return 1
        if quality_summary["agent_reviews"] == 0:
            print(json.dumps(quality_summary, indent=2), file=sys.stderr)
            return 1
        keep_config = _load_keep_lane_config()
        if keep_config.get("enabled") is not True:
            print(json.dumps(keep_config, indent=2), file=sys.stderr)
            return 1
        keep_selected, keep_dropped = _filter_paths(
            [
                (" M", "tools/bio_reality/state/foo.jsonl"),
                (" M", "tools/bio_reality/experiments/run_X.py"),
                ("??", "tools/bio_reality/vision/index.md"),
            ],
            [str(item) for item in keep_config.get("include_paths", []) if isinstance(item, str)],
            [str(item) for item in keep_config.get("exclude_paths", []) if isinstance(item, str)],
        )
        if keep_selected != ["tools/bio_reality/experiments/run_X.py"]:
            print(json.dumps({"selected": keep_selected, "dropped": keep_dropped}, indent=2), file=sys.stderr)
            return 1
        if "tools/bio_reality/state/foo.jsonl" not in keep_dropped:
            print(json.dumps({"selected": keep_selected, "dropped": keep_dropped}, indent=2), file=sys.stderr)
            return 1

        bedc_paths = _temp_paths(base / "bedc")
        bedc_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        bedc_claim_id = "h0.M.equals.WNR.CUN"
        bedc_target_dir = base / "bedc_target" / "concrete_instances"
        bedc_aggregator = base / "bedc_target" / "bio_reality_module.tex"
        bedc_mappings = [
            {
                "claim_id": bedc_claim_id,
                "hub_filename": "14102_bioreality_q_six_median_closure_ledger_namecert_construction.tex",
                "subdir_slug": "bioreality_q_six_median_closure_ledger",
                "carrier_name": "BioRealityQSixMedianClosureLedger",
                "natural_language": "the finite reality-bound median closure ledger for the standard-code reassignment support",
            },
            {
                "claim_id": "h0.M.shape.significance",
                "hub_filename": "14103_bioreality_q_six_median_shape_significance_namecert_construction.tex",
                "subdir_slug": "bioreality_q_six_median_shape_significance",
                "carrier_name": "BioRealityQSixMedianShapeSignificance",
                "natural_language": "the finite reality-bound median-shape rarity packet under a curated standard-code bridge",
            },
            {
                "claim_id": "h0.quotient.geometry",
                "hub_filename": "14104_reality_bound_codon_topology_quotient_geometry_namecert_construction.tex",
                "subdir_slug": "reality_bound_codon_topology_quotient_geometry",
                "carrier_name": "RealityBoundCodonTopologyQuotientGeometry",
                "natural_language": "the finite reality-bound quotient and product bookkeeping of the codon-coordinate cube",
            },
            {
                "claim_id": "h0.R.cardinality.13",
                "hub_filename": "14106_bioreality_q_six_reassigned_codon_ledger_namecert_construction.tex",
                "subdir_slug": "bioreality_q_six_reassigned_codon_ledger",
                "carrier_name": "BioRealityQSixReassignedCodonLedger",
                "natural_language": "the finite reality-bound ledger for the standard-code reassigned-codon support under a curated bridge",
            },
            {
                "claim_id": "h0.spectrum",
                "hub_filename": "14107_bioreality_q_six_empirical_codon_spectrum_namecert_construction.tex",
                "subdir_slug": "bioreality_q_six_empirical_codon_spectrum",
                "carrier_name": "BioRealityQSixEmpiricalCodonSpectrum",
                "natural_language": "the finite reality-bound spectral bookkeeping packet behind a curated standard-code bridge",
            },
        ]
        bedc_config_path = base / "bedc_pipeline_config.json"
        bedc_config_path.write_text(
            json.dumps(
                {
                    "bedc_writeback": {
                        "enabled": True,
                        "target_concrete_instances_dir": str(bedc_target_dir),
                        "module_aggregator": str(bedc_aggregator),
                        "max_writebacks_per_cycle": 1,
                        "codex_writer": {"enabled": False},
                        "claim_to_chapter_mapping": bedc_mappings,
                    }
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        (bedc_paths.namecert_proposals_dir / f"{bedc_claim_id}.md").write_text(
            "\n".join(
                [
                    "# NameCert proposal",
                    "",
                    "This proposal is an internal review packet for a coordinate ledger.",
                ]
            ),
            encoding="utf-8",
        )
        write_jsonl(
            bedc_paths.conjectures,
            [
                {
                    "conjecture_id": "codon.window6.local.tile.boundary",
                    "linked_claim_ids": [bedc_claim_id],
                    "forbidden_claims": ["no translation realization"],
                    "verified_facts": {bedc_claim_id: {"values": {"status": "passed"}}},
                }
            ],
        )
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bedc_config_path
        try:
            bedc_summary = run_bedc_writeback_lane(BioRealityStore(bedc_paths))
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if len(bedc_mappings) != 5:
            print(json.dumps(bedc_mappings, indent=2), file=sys.stderr)
            return 1
        if bedc_summary["written"] != 1 or bedc_summary["blocked_by_gate"] != 0:
            print(json.dumps(bedc_summary, indent=2), file=sys.stderr)
            return 1
        bedc_hub = bedc_target_dir / bedc_mappings[0]["hub_filename"]
        bedc_spine = bedc_target_dir / bedc_mappings[0]["subdir_slug"] / "namecert_construction.tex"
        if not bedc_hub.exists() or not bedc_spine.exists() or not bedc_aggregator.exists():
            print(json.dumps({"hub": str(bedc_hub), "spine": str(bedc_spine), "aggregator": str(bedc_aggregator)}, indent=2), file=sys.stderr)
            return 1
        bedc_gate = bedc_writeback_gates.validate_chapter_pair(
            bedc_hub.read_text(encoding="utf-8"),
            bedc_spine.read_text(encoding="utf-8"),
        )
        if not bedc_gate["passed"]:
            print(json.dumps(bedc_gate, indent=2), file=sys.stderr)
            return 1

        bedc_auto_paths = _temp_paths(base / "bedc_auto")
        bedc_auto_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        bedc_auto_target_dir = base / "bedc_auto_target" / "concrete_instances"
        bedc_auto_aggregator = base / "bedc_auto_target" / "bio_reality_module.tex"
        bedc_auto_mappings = [
            {
                "claim_id": "mapped.claim",
                "hub_filename": "14120_bioreality_mapped_seed_namecert_construction.tex",
                "subdir_slug": "bioreality_mapped_seed",
                "carrier_name": "BioRealityMappedSeed",
                "natural_language": "the finite reality-bound mapped seed witness",
            }
        ]
        bedc_auto_config_path = base / "bedc_auto_pipeline_config.json"
        bedc_auto_config_path.write_text(
            json.dumps(
                {
                    "bedc_writeback": {
                        "enabled": True,
                        "target_concrete_instances_dir": str(bedc_auto_target_dir),
                        "module_aggregator": str(bedc_auto_aggregator),
                        "max_writebacks_per_cycle": 2,
                        "codex_writer": {"enabled": False},
                        "claim_to_chapter_mapping": bedc_auto_mappings,
                    }
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        (bedc_auto_paths.namecert_proposals_dir / "mapped.claim.md").write_text(
            "\n".join(
                [
                    "# NameCert proposal for mapped.claim",
                    "",
                    "Mapped proposal body.",
                ]
            ),
            encoding="utf-8",
        )
        (bedc_auto_paths.namecert_proposals_dir / "extra.md").write_text(
            "\n".join(
                [
                    "# NameCert proposal for extra",
                    "",
                    "## 1. Loning-format chapter slug",
                    "",
                    "Proposed chapter slug: 14121_bioreality_extra_seed_namecert_construction.",
                    "",
                    "## 2. Carrier",
                    "",
                    "Carrier: BioRealityExtraSeedUp.",
                ]
            ),
            encoding="utf-8",
        )
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bedc_auto_config_path
        try:
            bedc_auto_summary = run_bedc_writeback_lane(BioRealityStore(bedc_auto_paths))
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if bedc_auto_summary["written"] != 2 or bedc_auto_summary["auto_discovered_written"] != 1:
            print(json.dumps(bedc_auto_summary, indent=2), file=sys.stderr)
            return 1
        bedc_auto_hub = bedc_auto_target_dir / "14121_bioreality_extra_seed_namecert_construction.tex"
        bedc_auto_spine = bedc_auto_target_dir / "14121_bioreality_extra_seed" / "namecert_construction.tex"
        if not bedc_auto_hub.exists() or not bedc_auto_spine.exists():
            print(json.dumps({"hub": str(bedc_auto_hub), "spine": str(bedc_auto_spine)}, indent=2), file=sys.stderr)
            return 1
        bedc_auto_gate = bedc_writeback_gates.validate_chapter_pair(
            bedc_auto_hub.read_text(encoding="utf-8"),
            bedc_auto_spine.read_text(encoding="utf-8"),
        )
        if not bedc_auto_gate["passed"]:
            print(json.dumps(bedc_auto_gate, indent=2), file=sys.stderr)
            return 1

        (bedc_auto_paths.namecert_proposals_dir / "blocked.auto.md").write_text(
            "\n".join(
                [
                    "# NameCert proposal for blocked.auto",
                    "",
                    "## 1. Loning-format chapter slug",
                    "",
                    "Proposed chapter slug: 14122_bioreality_blocked_seed_namecert_construction.",
                    "",
                    "## 2. Carrier",
                    "",
                    "Carrier: BioRealityBlockedSeedUp.",
                ]
            ),
            encoding="utf-8",
        )
        bedc_skip_config_path = base / "bedc_skip_pipeline_config.json"
        bedc_skip_target_dir = base / "bedc_skip_target" / "concrete_instances"
        bedc_skip_aggregator = base / "bedc_skip_target" / "bio_reality_module.tex"
        bedc_skip_config_path.write_text(
            json.dumps(
                {
                    "bedc_writeback": {
                        "enabled": True,
                        "target_concrete_instances_dir": str(bedc_skip_target_dir),
                        "module_aggregator": str(bedc_skip_aggregator),
                        "max_writebacks_per_cycle": 2,
                        "codex_writer": {"enabled": False},
                        "skip_claim_ids": ["mapped.claim", "blocked.auto"],
                        "claim_to_chapter_mapping": bedc_auto_mappings,
                    }
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bedc_skip_config_path
        try:
            bedc_skip_summary = run_bedc_writeback_lane(BioRealityStore(bedc_auto_paths))
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if (
            bedc_skip_summary["written"] != 1
            or bedc_skip_summary["auto_discovered_written"] != 1
            or bedc_skip_summary["skipped_by_dedup"] != 2
        ):
            print(json.dumps(bedc_skip_summary, indent=2), file=sys.stderr)
            return 1
        if (bedc_skip_target_dir / "14120_bioreality_mapped_seed_namecert_construction.tex").exists():
            print(json.dumps(bedc_skip_summary, indent=2), file=sys.stderr)
            return 1
        if (bedc_skip_target_dir / "14122_bioreality_blocked_seed_namecert_construction.tex").exists():
            print(json.dumps(bedc_skip_summary, indent=2), file=sys.stderr)
            return 1

        bedc_codex_paths = _temp_paths(base / "bedc_codex")
        bedc_codex_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        bedc_codex_claim_id = "h0.author.writer"
        bedc_codex_target_dir = base / "bedc_author_target" / "concrete_instances"
        bedc_codex_aggregator = base / "bedc_author_target" / "bio_reality_module.tex"
        bedc_codex_mapping = {
            "claim_id": bedc_codex_claim_id,
            "hub_filename": "14130_bioreality_author_writer_namecert_construction.tex",
            "subdir_slug": "bioreality_author_writer",
            "carrier_name": "BioRealityAuthorWriter",
            "natural_language": "the authored fixture packet",
        }
        bedc_codex_config_path = base / "bedc_author_pipeline_config.json"
        bedc_codex_config_path.write_text(
            json.dumps(
                {
                    "bedc_writeback": {
                        "enabled": True,
                        "target_concrete_instances_dir": str(bedc_codex_target_dir),
                        "module_aggregator": str(bedc_codex_aggregator),
                        "max_writebacks_per_cycle": 1,
                        "codex_writer": {
                            "enabled": True,
                            "max_retries": 2,
                            "timeout_seconds": 600,
                            "log_dir": str(base / "bedc_author_logs"),
                            "min_audit_score": 7,
                            "min_used_fact_ids": 3,
                            "corrective_retry_on_gate_failure": True,
                        },
                        "claim_to_chapter_mapping": [bedc_codex_mapping],
                    }
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        (bedc_codex_paths.namecert_proposals_dir / f"{bedc_codex_claim_id}.md").write_text(
            "# NameCert proposal for h0.author.writer\n",
            encoding="utf-8",
        )
        write_jsonl(
            bedc_codex_paths.conjectures,
            [
                {
                    "conjecture_id": "author.writer.fixture",
                    "linked_claim_ids": [bedc_codex_claim_id],
                    "verified_facts": {
                        bedc_codex_claim_id: {
                            "x": 64,
                            "y": 13,
                            "z": 0.675248,
                        }
                    },
                }
            ],
        )
        original_render_chapter_with_codex = render_chapter_with_codex

        def _mock_render_chapter_with_codex(
            target: dict[str, Any],
            verified_facts: dict[str, Any],
            repo_root: Path,
            *,
            timeout_seconds: int = 600,
            log_dir: str | Path = "tools/bio_reality/state/bedc_writeback_logs",
            corrective_feedback: list[str] | None = None,
        ) -> dict[str, Any]:
            _ = (verified_facts, repo_root, timeout_seconds, log_dir, corrective_feedback)
            carrier = str(target.get("carrier_name") or "BioRealityAuthorWriter")
            slug = str(target.get("subdir_slug") or "bioreality_author_writer")
            return {
                "status": "ok",
                "verdict": "ready",
                "audit_score": 9,
                "used_fact_ids": ["x", "y", "z"],
                "hub_content": "\n".join(
                    [
                        "% BioReality author fixture hub.",
                        rf"\input{{parts/concrete_instances/{slug}/namecert_construction}}",
                        "",
                    ]
                ),
                "spine_content": "\n".join(
                    [
                        rf"\chapter{{A Concrete Naming Certificate for $\{carrier}Up$}}",
                        rf"\label{{ch:concrete-instances-{slug}-namecert}}",
                        r"\origin{ai}",
                        "",
                        "This authored fixture records 64 codon coordinates, a row count of 13, and a lambda value of 0.675248. "
                        "The packet also names witness x, witness y, and witness z as the three verified fact keys consumed by this chapter. "
                        "It stays self-contained and does not cite another chapter, path, URL, run identifier, or Lean marker. "
                        "The prose is deliberately thick enough to be a NameCert packet: it separates code-layer readback from translation, folding, physical admissibility, function, and universality. "
                        "It treats the three values only as finite audit data for a naming certificate, not as a biological mechanism. "
                        "A reader can inspect the carrier without importing another chapter because every operational boundary is stated locally. "
                        "The code-read contact is a bridge boundary, while the BEDC kernel prose names only the finite coordinate surface. "
                        "No external file path is written into the packet body. "
                        "The fixture repeats the three grounded observations in prose: 64 coordinates, 13 rows, and lambda 0.675248. "
                        "That repetition is intentional for the gate fixture, because it demonstrates that the author path consumes verified facts instead of returning a generic template. "
                        "The chapter refuses all higher-layer promotions unless a separate reality contact is supplied.",
                        "",
                        rf"\paragraph{{Carrier.}} $\{carrier}Up$ is the local BEDC packet name for this author fixture.",
                        "",
                        rf"\falsifiablePrediction{{A $\{carrier}Up$ packet cannot export translation, folding, physical admissibility, function, or universality from 64 coordinates, 13 rows, or lambda 0.675248 alone.}}",
                        "",
                        rf"\independenceWitness{{The $\{carrier}Up$ carrier records only the local coordinate and audit surface named by x, y, and z.}}",
                        "",
                        rf"\closureat{{{carrier}Up}}{{seedStr}}",
                        rf"\begin{{closurestatus}}{{\{carrier}Up}}",
                        r"  \constructivestory{The packet records 64 coordinates, 13 rows, and lambda 0.675248 as finite code-read audit data.}",
                        r"  \theoryclosure{\seedClosure}",
                        r"  \scopeclosed{Code-layer readback for the three consumed fixture facts only.}",
                        r"  \formalstatus{\unformalizedV}",
                        r"  \bridgestatus{paperBridge}",
                        r"  \notclaimed{No translation, folding, physical admissibility, function, mechanism, universality, or cross-layer biological consequence is closed.}",
                        r"  \upgradepath{Attach a separate testable reality contact before promoting any higher biological layer.}",
                        r"\end{closurestatus}",
                        "",
                    ]
                ),
                "risk_notes": "",
            }

        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bedc_codex_config_path
        globals()["render_chapter_with_codex"] = _mock_render_chapter_with_codex
        try:
            bedc_codex_summary = run_bedc_writeback_lane(BioRealityStore(bedc_codex_paths))
        finally:
            globals()["render_chapter_with_codex"] = original_render_chapter_with_codex
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if bedc_codex_summary["written"] != 1 or bedc_codex_summary["blocked_by_gate"] != 0:
            print(json.dumps(bedc_codex_summary, indent=2), file=sys.stderr)
            return 1
        bedc_codex_hub = bedc_codex_target_dir / bedc_codex_mapping["hub_filename"]
        bedc_codex_spine = bedc_codex_target_dir / bedc_codex_mapping["subdir_slug"] / "namecert_construction.tex"
        if not bedc_codex_hub.exists() or not bedc_codex_spine.exists():
            print(json.dumps({"hub": str(bedc_codex_hub), "spine": str(bedc_codex_spine)}, indent=2), file=sys.stderr)
            return 1
        bedc_codex_gate = bedc_writeback_gates.validate_chapter_pair(
            bedc_codex_hub.read_text(encoding="utf-8"),
            bedc_codex_spine.read_text(encoding="utf-8"),
            ["x", "y", "z"],
            3,
        )
        if not bedc_codex_gate["passed"]:
            print(json.dumps(bedc_codex_gate, indent=2), file=sys.stderr)
            return 1

        parse_fixture = {
            "verdict": "ready",
            "audit_score": 9,
            "used_fact_ids": ["values.size", "values.lambda_M"],
            "chapter_content": r"\subsection{NameCert: h0.test}\label{sec:namecert-h0-test}\origin{ai}" + "\n"
            + (
                r"\paragraph{Grounded record.} The packet cites 13 rows and lambda 0.675248 while keeping the result at code-read scope. "
                "It refuses translation, folding, physical admissibility, function, mechanism, and universality without a separate contact. "
            )
            * 20,
            "risk_notes": "",
            "missing_data_notes": "",
        }
        event_stdout = json.dumps(
            {
                "type": "agent_message",
                "item": {
                    "content": [
                        {
                            "type": "output_text",
                            "text": "```json\n" + json.dumps(parse_fixture) + "\n```",
                        }
                    ]
                },
            }
        )
        if _parse_bio_w_codex_json(event_stdout) != parse_fixture:
            print(event_stdout, file=sys.stderr)
            return 1

        bio_w_codex_paths = _temp_paths(base / "bio_w_codex")
        bio_w_codex_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        bio_w_config_path = base / "bio_w_codex_pipeline_config.json"
        bio_w_config_path.write_text(
            json.dumps(
                {
                    "lanes": [
                        {
                            "lane": "bio-W",
                            "codex_writer": {
                                "enabled": True,
                                "max_retries": 2,
                                "timeout": 600,
                                "log_dir": str(base / "bio_w_codex_logs"),
                                "min_audit_score": 7,
                                "min_used_fact_ids": 2,
                                "corrective_retry": True,
                            },
                        }
                    ]
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            bio_w_codex_paths.conjectures,
            [
                {
                    "conjecture_id": "test.codon.codex",
                    "biological_object": "codon table",
                    "informal_statement": "codex-authored codon median packet",
                    "bedc_minimal_form": {
                        "carrier": "codon carrier",
                        "distinctions": ["codons in R", "codons in M"],
                        "readback": "observable codon table",
                        "internal_structure": ["closure"],
                    },
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": ["codon.codex.probe"],
                    "forbidden_claims": ["translation realisation"],
                    "null_reason": "",
                    "verified_facts": {
                        "h0.codex": {
                            "values": {"size": 13, "lambda_M": 0.675248},
                        }
                    },
                }
            ],
        )
        write_jsonl(
            bio_w_codex_paths.contacts,
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "fixture",
                    "source_snapshot": "fixture",
                    "observed_fact": "curated code table",
                    "resolution": "code readback",
                    "known_noise_or_bias": "fixture only",
                    "can_test": ["code_read"],
                    "cannot_test": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            bio_w_codex_paths.probes,
            [
                {
                    "probe_id": "codon.codex.probe",
                    "conjecture_ref": "test.codon.codex",
                    "probe_kind": "boundary_mismatch",
                    "derived_from": ["bedc_coordinate"],
                    "test_statement": "codex probe",
                    "support_condition": "passed run",
                    "break_condition": "failed run",
                    "required_contacts": ["curated.standard.code.table"],
                    "forbidden_interpretations": ["codex probe does not prove translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            bio_w_codex_paths.mismatches,
            [
                {
                    "mismatch_id": "codon.codex.aligned",
                    "probe_ref": "codon.codex.probe",
                    "contact_ref": "curated.standard.code.table",
                    "status": "aligned",
                    "mismatch_kind": "none",
                    "observed_delta": "none",
                    "refinement_pressure": "none",
                    "blocked_claims": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        (bio_w_codex_paths.namecert_proposals_dir / "h0.codex.md").write_text(
            "# NameCert proposal for h0.codex\n",
            encoding="utf-8",
        )
        def _bio_w_mock_result(chapter_id: str) -> dict[str, Any]:
            return {
                "verdict": "ready",
                "audit_score": 9,
                "used_fact_ids": ["values.size", "values.lambda_M"],
                "chapter_content": rf"\subsection{{{chapter_id}}}" + "\n"
                + rf"\label{{sec:{re.sub(r'[^a-z0-9]+', '-', chapter_id.lower()).strip('-')}}}" + "\n"
                + r"\origin{ai}"
                + "\n\n"
                + (
                    r"\paragraph{Grounded finite rows.} This codex-authored BioReality record cites 13 rows and lambda 0.675248 from the verified facts. "
                    "The chapter keeps those numbers at the code-read layer and refuses translation, folding, physical admissibility, function, mechanism, and universality without a separate contact. "
                    "The local carrier is read as a finite paper witness rather than a biological mechanism. "
                )
                * 12,
                "risk_notes": "",
                "missing_data_notes": "",
            }

        def _mock_run_bio_w_codex(prompt: str, repo_root: Path, timeout_seconds: int) -> tuple[dict[str, Any] | None, str, str]:
            _ = (repo_root, timeout_seconds)
            chapter_id = "NameCert: h0.codex" if "h0.codex" in prompt else "test.codon.codex"
            parsed = _bio_w_mock_result(chapter_id)
            raw = json.dumps(parsed)
            return parsed, raw, ""

        original_run_bio_w_codex = _run_bio_w_codex
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bio_w_config_path
        globals()["_run_bio_w_codex"] = _mock_run_bio_w_codex
        try:
            bio_w_codex_summary = run_writeback_lane(BioRealityStore(bio_w_codex_paths))
        finally:
            globals()["_run_bio_w_codex"] = original_run_bio_w_codex
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        bio_w_part = bio_w_codex_paths.paper_part.read_text(encoding="utf-8")
        bio_w_namecert = bio_w_codex_paths.paper_part.parent / "namecerts" / "h0_codex.tex"
        if bio_w_codex_summary["namecerts_written"] != 1 or not bio_w_namecert.exists():
            print(json.dumps(bio_w_codex_summary, indent=2), file=sys.stderr)
            return 1
        if "codex-authored BioReality record cites 13 rows and lambda 0.675248" not in bio_w_part:
            print(bio_w_part, file=sys.stderr)
            return 1
        if "NameCert: h0.codex" not in bio_w_namecert.read_text(encoding="utf-8"):
            print(bio_w_namecert.read_text(encoding="utf-8"), file=sys.stderr)
            return 1

        bio_w_fallback_paths = _temp_paths(base / "bio_w_fallback")
        bio_w_fallback_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        write_jsonl(
            bio_w_fallback_paths.conjectures,
            [
                {
                    "conjecture_id": "fallback.codon",
                    "biological_object": "codon table",
                    "informal_statement": "fallback packet",
                    "bedc_minimal_form": {"carrier": "codon carrier"},
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": ["codon.fallback.probe"],
                    "forbidden_claims": ["translation realisation"],
                    "null_reason": "",
                    "verified_facts": {"h0.fallback": {"values": {"size": 13, "lambda_M": 0.675248}}},
                }
            ],
        )
        write_jsonl(
            bio_w_fallback_paths.contacts,
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "fixture",
                    "source_snapshot": "fixture",
                    "observed_fact": "curated code table",
                    "resolution": "code readback",
                    "known_noise_or_bias": "fixture only",
                    "can_test": ["code_read"],
                    "cannot_test": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            bio_w_fallback_paths.probes,
            [
                {
                    "probe_id": "codon.fallback.probe",
                    "conjecture_ref": "fallback.codon",
                    "probe_kind": "boundary_mismatch",
                    "derived_from": ["bedc_coordinate"],
                    "test_statement": "fallback probe",
                    "support_condition": "passed run",
                    "break_condition": "failed run",
                    "required_contacts": ["curated.standard.code.table"],
                    "forbidden_interpretations": ["fallback probe does not prove translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            bio_w_fallback_paths.mismatches,
            [
                {
                    "mismatch_id": "codon.fallback.aligned",
                    "probe_ref": "codon.fallback.probe",
                    "contact_ref": "curated.standard.code.table",
                    "status": "aligned",
                    "mismatch_kind": "none",
                    "observed_delta": "none",
                    "refinement_pressure": "none",
                    "blocked_claims": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        (bio_w_fallback_paths.namecert_proposals_dir / "h0.fallback.md").write_text(
            "\n".join(["# NameCert proposal", "## 1. Loning-format chapter slug", "Fallback slug.", "## 2. Carrier", "Fallback carrier."]),
            encoding="utf-8",
        )
        original_render_namecert_with_codex = render_namecert_with_codex
        original_render_conjecture_with_codex = render_conjecture_with_codex
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = bio_w_config_path
        globals()["render_namecert_with_codex"] = lambda *args, **kwargs: None
        globals()["render_conjecture_with_codex"] = lambda *args, **kwargs: None
        try:
            fallback_summary = run_writeback_lane(BioRealityStore(bio_w_fallback_paths))
        finally:
            globals()["render_namecert_with_codex"] = original_render_namecert_with_codex
            globals()["render_conjecture_with_codex"] = original_render_conjecture_with_codex
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        fallback_namecert = bio_w_fallback_paths.paper_part.parent / "namecerts" / "h0_fallback.tex"
        if fallback_summary["namecerts_written"] != 1 or not fallback_namecert.exists():
            print(json.dumps(fallback_summary, indent=2), file=sys.stderr)
            return 1
        if "NameCert chapter slug" not in fallback_namecert.read_text(encoding="utf-8"):
            print(fallback_namecert.read_text(encoding="utf-8"), file=sys.stderr)
            return 1

        promote_paths = _temp_paths(base / "promote")
        promote_store = BioRealityStore(promote_paths)
        promote_store.write_conjectures(
            [
                {
                    "conjecture_id": "codon.window6.local.tile.boundary",
                    "biological_object": "standard-code codon table",
                    "informal_statement": (
                        "Window-six codon coordinates may expose local boundary-tile structure, "
                        "but curated code labels remain external reality contacts."
                    ),
                    "bedc_minimal_form": {
                        "carrier": "codon cube Q6",
                        "distinctions": ["six-bit codon display", "local tile face", "singleton label corner", "three-point label class"],
                        "readback": "standard-code label table",
                        "internal_structure": ["coordinate", "closure", "spectrum", "relation"],
                    },
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": ["codon.local.tile.no.global.law"],
                    "forbidden_claims": [
                        "A local codon tile is not a global biological law.",
                        "Window-six geometry alone is not translation, structure, physical admissibility, or function.",
                    ],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_contacts(
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "curated standard genetic-code bridge",
                    "source_snapshot": "dna_to_protein_realization",
                    "observed_fact": "A curated standard-code table assigns codons to amino-acid or stop labels.",
                    "resolution": "codon label readback",
                    "known_noise_or_bias": "The table is a reality bridge for code labels, not a mechanism or universality proof.",
                    "can_test": ["code_read", "local codon tile label split"],
                    "cannot_test": ["translation realization", "structural order", "physical admissibility", "function realization"],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_probes(
            [
                {
                    "probe_id": "codon.local.tile.no.global.law",
                    "conjecture_ref": "codon.window6.local.tile.boundary",
                    "probe_kind": "boundary_mismatch",
                    "derived_from": ["bedc_coordinate", "bedc_closure", "external_reality_hint"],
                    "test_statement": "A local codon-tile pattern must stay at code_read unless a separate higher-layer contact is supplied.",
                    "support_condition": "The curated code table supports only codon-label readback and local split checks.",
                    "break_condition": "The pipeline promotes the local tile to translation, structure, physical admissibility, function, or universal mechanism.",
                    "required_contacts": ["curated.standard.code.table"],
                    "forbidden_interpretations": [
                        "Do not infer that DNA obeys BEDC geometry as biological necessity.",
                        "Do not infer protein function from a codon-tile split.",
                    ],
                    "null_reason": "",
                }
            ]
        )
        promote_store.write_mismatches(
            [
                {
                    "mismatch_id": "codon.local.tile.scope.boundary",
                    "probe_ref": "codon.local.tile.no.global.law",
                    "contact_ref": "curated.standard.code.table",
                    "status": "aligned",
                    "mismatch_kind": "none",
                    "observed_delta": "The contact supports code-layer readback and blocks higher-layer promotion.",
                    "refinement_pressure": "Next cycles should search for separate reality contacts before crossing the translation or function boundary.",
                    "blocked_claims": ["protein realization", "folded structure", "physical admissibility", "biological function", "universal mechanism"],
                    "null_reason": "",
                }
            ]
        )
        promote_summary = run_packet_lane(promote_store)
        promoted_conjectures = promote_store.load_conjectures()
        new_conjecture = next(
            item for item in promoted_conjectures if item.get("conjecture_id") == "orf_eligibility.seed.boundary"
        )
        if promote_summary["promotion"].get("promoted") is not True:
            print(json.dumps(promote_summary, indent=2), file=sys.stderr)
            return 1
        if promote_summary["promotion"].get("to_layer") != "orf_eligibility":
            print(json.dumps(promote_summary, indent=2), file=sys.stderr)
            return 1
        if len(promoted_conjectures) != 2:
            print(json.dumps(promoted_conjectures, indent=2), file=sys.stderr)
            return 1
        if new_conjecture.get("evidence_basis") != ["bedc_coordinate"] or new_conjecture.get("reality_contact_refs") != []:
            print(json.dumps(new_conjecture, indent=2), file=sys.stderr)
            return 1

        execute_paths = _temp_paths(base / "execute")
        execute_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        execute_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        execute_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {
                            "claim_id": "self.claim",
                            "hypothesis_level": "H0",
                            "phase": 1,
                            "statement": "self test claim",
                            "depends_on": [],
                            "status": "open",
                            "experiment_id": "self_missing_script",
                            "history": [],
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        execute_paths.experiments_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-experiments-v1",
                    "experiments": [
                        {
                            "experiment_id": "self_missing_script",
                            "script_path": "tools/bio_reality/experiments/run_self_missing_script.py",
                            "claim_id": "self.claim",
                            "required_data": [],
                            "timeout_seconds": 5,
                            "acceptance": {"required_checks": []},
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        execute_store = BioRealityStore(execute_paths)
        execute_summary = run_execute_lane(execute_store)
        updated_claims = json.loads(execute_paths.claims_registry.read_text(encoding="utf-8"))["claims"]
        if execute_summary["error_this_cycle"] != 1 or updated_claims[0].get("status") != "error":
            print(json.dumps({"summary": execute_summary, "claims": updated_claims}, indent=2), file=sys.stderr)
            return 1

        namecert_paths = _temp_paths(base / "namecert")
        namecert_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        namecert_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {
                            "claim_id": "test.M.size",
                            "statement": "codon median set M has size 20",
                            "depends_on": [],
                            "status": "passed",
                            "experiment_id": "check_size",
                            "history": [],
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            namecert_paths.conjectures,
            [
                {
                    "conjecture_id": "test.codon",
                    "biological_object": "codon table",
                    "informal_statement": "codon median packet",
                    "bedc_minimal_form": {
                        "carrier": "codon carrier",
                        "distinctions": ["codons in R", "codons in M"],
                        "readback": "observable codon table",
                        "internal_structure": ["closure"],
                    },
                    "probe_refs": ["codon.size.probe"],
                    "forbidden_claims": ["translation realisation"],
                }
            ],
        )
        write_jsonl(
            namecert_paths.experiment_runs,
            [
                {
                    "experiment_run_id": "run.test.size.1",
                    "experiment_id": "check_size",
                    "claim_id": "test.M.size",
                    "status": "passed",
                    "checks": [{"name": "M_size_equals_20", "passed": True, "actual": 20}],
                    "result": {"lambda": 0.5, "nested": {"skip": True}, "items": [1, 2]},
                    "completed_at": "2026-05-25T00:00:01+00:00",
                }
            ],
        )
        namecert_store = BioRealityStore(namecert_paths)
        namecert_summary = run_namecert_lane(namecert_store)
        namecert_claims = json.loads(namecert_paths.claims_registry.read_text(encoding="utf-8"))["claims"]
        namecert_conjectures = namecert_store.load_conjectures()
        namecert_events = namecert_store.load_events()
        if (
            namecert_summary["passed_claims_scanned"] != 1
            or namecert_summary["newly_linked"] != 1
            or namecert_summary["verified_facts_updated"] != 1
            or namecert_summary["proposal_events_emitted"] != 1
            or namecert_claims[0].get("linked_conjecture_id") != "test.codon"
            or "test.M.size" not in namecert_conjectures[0].get("verified_facts", {})
            or not namecert_conjectures[0].get("last_verified_at")
            or not any(event.get("event_kind") == "namecert_proposal_needed" for event in namecert_events)
        ):
            print(json.dumps({"summary": namecert_summary, "claims": namecert_claims, "conjectures": namecert_conjectures, "events": namecert_events}, indent=2), file=sys.stderr)
            return 1
        namecert_repeat = run_namecert_lane(namecert_store)
        if namecert_repeat["proposal_events_emitted"] != 0:
            print(json.dumps({"summary": namecert_repeat, "events": namecert_store.load_events()}, indent=2), file=sys.stderr)
            return 1
        writeback_empty_fact_paths = _temp_paths(base / "writeback_empty_fact")
        write_jsonl(
            writeback_empty_fact_paths.conjectures,
            [
                {
                    "conjecture_id": "empty.fact.codon",
                    "biological_object": "codon table",
                    "informal_statement": "codon code readback",
                    "bedc_minimal_form": {
                        "carrier": "codon carrier",
                        "distinctions": ["codon label"],
                        "readback": "observable codon table",
                        "internal_structure": ["coordinate"],
                    },
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality", "bedc_coordinate"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": [],
                    "forbidden_claims": ["code readback is not translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            writeback_empty_fact_paths.contacts,
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "fixture",
                    "source_snapshot": "fixture",
                    "observed_fact": "curated code table",
                    "resolution": "code readback",
                    "known_noise_or_bias": "fixture only",
                    "can_test": ["code_read"],
                    "cannot_test": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        writeback_empty_fact_store = BioRealityStore(writeback_empty_fact_paths)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = writeback_disabled_config_path
        try:
            writeback_empty_fact_summary = run_writeback_lane(writeback_empty_fact_store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        writeback_empty_fact_part = writeback_empty_fact_paths.paper_part.read_text(encoding="utf-8")
        if writeback_empty_fact_summary["written_conjectures"] != 1:
            print(json.dumps(writeback_empty_fact_summary, indent=2), file=sys.stderr)
            return 1
        if "Verified facts" not in writeback_empty_fact_part or "No verified facts attached yet." not in writeback_empty_fact_part:
            print(writeback_empty_fact_part, file=sys.stderr)
            return 1
        writeback_fact_paths = _temp_paths(base / "writeback_fact")
        writeback_fact_paths.namecert_proposals_dir.mkdir(parents=True, exist_ok=True)
        write_jsonl(
            writeback_fact_paths.conjectures,
            [
                {
                    "conjecture_id": "test.codon",
                    "biological_object": "codon table",
                    "informal_statement": "codon median packet",
                    "bedc_minimal_form": {
                        "carrier": "codon carrier",
                        "distinctions": ["codons in R", "codons in M"],
                        "readback": "observable codon table",
                        "internal_structure": ["closure"],
                    },
                    "claimed_layer": "code_read",
                    "evidence_basis": ["external_reality", "bedc_coordinate", "derived_probe"],
                    "reality_contact_refs": ["curated.standard.code.table"],
                    "probe_refs": ["codon.size.probe"],
                    "forbidden_claims": ["translation realisation"],
                    "null_reason": "",
                    "verified_facts": {
                        "h0.test": {
                            "verified_at": "2026-05-25T00:00:01+00:00",
                            "experiment_run_id": "abcd1234efgh",
                            "values": {"size": 13, "lambda_M": 0.675248},
                        }
                    },
                }
            ],
        )
        write_jsonl(
            writeback_fact_paths.contacts,
            [
                {
                    "contact_id": "curated.standard.code.table",
                    "source_kind": "genetic_code_table",
                    "source_ref": "fixture",
                    "source_snapshot": "fixture",
                    "observed_fact": "curated code table",
                    "resolution": "code readback",
                    "known_noise_or_bias": "fixture only",
                    "can_test": ["code_read"],
                    "cannot_test": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            writeback_fact_paths.probes,
            [
                {
                    "probe_id": "codon.size.probe",
                    "conjecture_ref": "test.codon",
                    "probe_kind": "boundary_mismatch",
                    "derived_from": ["bedc_coordinate"],
                    "test_statement": "size probe",
                    "support_condition": "passed run",
                    "break_condition": "failed run",
                    "required_contacts": ["curated.standard.code.table"],
                    "forbidden_interpretations": ["size probe does not prove translation"],
                    "null_reason": "",
                }
            ],
        )
        write_jsonl(
            writeback_fact_paths.mismatches,
            [
                {
                    "mismatch_id": "codon.size.aligned",
                    "probe_ref": "codon.size.probe",
                    "contact_ref": "curated.standard.code.table",
                    "status": "aligned",
                    "mismatch_kind": "none",
                    "observed_delta": "none",
                    "refinement_pressure": "none",
                    "blocked_claims": ["translation"],
                    "null_reason": "",
                }
            ],
        )
        (writeback_fact_paths.namecert_proposals_dir / "h0.test.md").write_text(
            "\n".join(
                [
                    "# NameCert proposal for h0.test",
                    "## 1. Loning-format chapter slug",
                    "Proposed slug: 14101_test",
                    "## 2. Carrier",
                    "Test carrier.",
                ]
            ),
            encoding="utf-8",
        )
        writeback_fact_store = BioRealityStore(writeback_fact_paths)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = writeback_disabled_config_path
        try:
            writeback_fact_summary = run_writeback_lane(writeback_fact_store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        writeback_fact_part = writeback_fact_paths.paper_part.read_text(encoding="utf-8")
        writeback_fact_main = writeback_fact_paths.paper_main.read_text(encoding="utf-8")
        writeback_fact_namecert = writeback_fact_paths.paper_part.parent / "namecerts" / "h0_test.tex"
        if writeback_fact_summary["namecerts_written"] != 1:
            print(json.dumps(writeback_fact_summary, indent=2), file=sys.stderr)
            return 1
        if "Verified facts" not in writeback_fact_part or "size=13" not in writeback_fact_part or "lambda\\_M=0.675248" not in writeback_fact_part:
            print(writeback_fact_part, file=sys.stderr)
            return 1
        if not writeback_fact_namecert.exists():
            print(str(writeback_fact_namecert), file=sys.stderr)
            return 1
        writeback_fact_namecert_text = writeback_fact_namecert.read_text(encoding="utf-8")
        if "NameCert chapter slug" not in writeback_fact_namecert_text or "Carrier" not in writeback_fact_namecert_text:
            print(writeback_fact_namecert_text, file=sys.stderr)
            return 1
        if r"\input{parts/namecerts/h0_test}" not in writeback_fact_main:
            print(writeback_fact_main, file=sys.stderr)
            return 1

        oracle_original_run_session = oracle_consultation.oracle_client.run_session
        oracle_original_subprocess_run = oracle_consultation.subprocess.run
        oracle_call_log: list[dict[str, Any]] = []
        codex_judge_calls = {"count": 0}

        def fake_run_session(
            initial_prompt: str,
            *,
            topic: str,
            judge_callback,
            max_turns: int = 20,
            intended_claim_id: str = "",
            intended_lane: str = "",
            pdf_base64: str = "",
            pdf_name: str = "",
            existing_conversation_id: str = "",
            close_on_exit: bool = True,
            server_url: str = "",
            poll_timeout: int = 600,
            poll_interval: float = 5.0,
        ) -> dict[str, Any]:
            turns: list[dict[str, Any]] = []
            prompt = initial_prompt
            for turn_index in range(min(3, max_turns)):
                turns.append(
                    {
                        "turn": turn_index,
                        "prompt": prompt,
                        "result": {
                            "status": "completed",
                            "conversation_id": f"conv-{topic}",
                            "response": f"oracle response {turn_index} for {topic}",
                        },
                    }
                )
                if turn_index == 2:
                    break
                decision = judge_callback(turns)
                if not decision.get("continue"):
                    break
                prompt = str(decision.get("next_prompt") or "")
            oracle_call_log.append({"topic": topic, "lane": intended_lane, "claim_id": intended_claim_id, "turns": len(turns)})
            return {
                "topic": topic,
                "conversation_id": f"conv-{topic}",
                "turns": turns,
                "closed_reason": "fake complete",
                "max_turns_reached": False,
            }

        def fake_codex_run(*args: Any, **kwargs: Any):
            codex_judge_calls["count"] += 1
            payload = {"continue": True, "next_prompt": "Ask for one sharper control.", "rationale": "more useful", "useful_score": 8}
            return subprocess.CompletedProcess(args[0] if args else [], 0, json.dumps(payload), "")

        oracle_consultation.oracle_client.run_session = fake_run_session
        oracle_consultation.subprocess.run = fake_codex_run
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = oracle_config_path
        try:
            oracle_gate_paths = _temp_paths(base / "oracle_gate")
            write_jsonl(
                oracle_gate_paths.contacts,
                [
                    {
                        "contact_id": "curated.standard.code.table",
                        "source_kind": "genetic_code_table",
                        "source_ref": "fixture code table",
                        "source_snapshot": "fixture",
                        "observed_fact": "A curated table maps codons to labels.",
                        "resolution": "codon labels",
                        "known_noise_or_bias": "fixture only",
                        "can_test": ["code_read"],
                        "cannot_test": ["translation_realization"],
                        "null_reason": "",
                    }
                ],
            )
            write_jsonl(
                oracle_gate_paths.conjectures,
                [
                    {
                        "conjecture_id": "oracle.review.claim",
                        "biological_object": "standard-code codon table",
                        "informal_statement": "Codon geometry causes translation realization.",
                        "bedc_minimal_form": {
                            "carrier": "codon cube",
                            "distinctions": ["codon label"],
                            "readback": "curated code table",
                            "internal_structure": ["coordinate"],
                        },
                        "claimed_layer": "translation_realization",
                        "evidence_basis": ["external_reality", "bedc_coordinate"],
                        "reality_contact_refs": ["curated.standard.code.table"],
                        "probe_refs": [],
                        "forbidden_claims": ["Code-layer data alone is not translation realization."],
                        "null_reason": "",
                    }
                ],
            )
            write_jsonl(oracle_gate_paths.probes, [])
            write_jsonl(oracle_gate_paths.mismatches, [])
            (oracle_gate_paths.namecert_proposals_dir).mkdir(parents=True, exist_ok=True)
            (oracle_gate_paths.namecert_proposals_dir / "oracle.review.claim.md").write_text(
                "# Oracle review claim\n\nCarrier proposal.",
                encoding="utf-8",
            )
            oracle_gate_store = BioRealityStore(oracle_gate_paths)
            oracle_gate_summary = run_gate_lane(oracle_gate_store)
            oracle_gate_repeat = run_gate_lane(oracle_gate_store)
            oracle_gate_events = oracle_gate_store.load_events()
            if oracle_gate_summary.get("oracle_consultations") != 1 or oracle_gate_summary.get("oracle_turns_total") != 3:
                print(json.dumps(oracle_gate_summary, indent=2), file=sys.stderr)
                return 1
            if oracle_gate_repeat.get("oracle_consultations") != 0 or oracle_gate_repeat.get("oracle_skipped_reason") != "rate_limited":
                print(json.dumps(oracle_gate_repeat, indent=2), file=sys.stderr)
                return 1
            if not any(event.get("event_kind") == "oracle_consultation_completed" and event.get("source") == "bio-G" for event in oracle_gate_events):
                print(json.dumps(oracle_gate_events, indent=2), file=sys.stderr)
                return 1
            if not list((base / "oracle_sessions" / "bio-G").glob("*.jsonl")) or not list((base / "oracle_sessions" / "bio-G").glob("*.md")):
                print("bio-G oracle transcript missing", file=sys.stderr)
                return 1

            oracle_plan_paths = _temp_paths(base / "oracle_plan")
            oracle_plan_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
            oracle_plan_paths.claims_registry.write_text(
                json.dumps(
                    {
                        "version": "bio-reality-claims-v1",
                        "claims": [
                            {"claim_id": "oracle.phase.a", "hypothesis_level": "H0", "phase": 1, "status": "passed"},
                            {"claim_id": "oracle.phase.b", "hypothesis_level": "H1", "phase": 1, "status": "passed"},
                        ],
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            oracle_plan_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
            oracle_plan_paths.experiments_registry.write_text(
                json.dumps({"version": "bio-reality-experiments-v1", "experiments": []}, indent=2),
                encoding="utf-8",
            )
            oracle_plan_store = BioRealityStore(oracle_plan_paths)
            oracle_plan_summary = run_plan_lane(oracle_plan_store)
            oracle_plan_repeat = run_plan_lane(oracle_plan_store)
            oracle_plan_events = oracle_plan_store.load_events()
            if oracle_plan_summary.get("oracle_consultations") != 1 or oracle_plan_summary.get("oracle_turns_total") != 3:
                print(json.dumps(oracle_plan_summary, indent=2), file=sys.stderr)
                return 1
            if oracle_plan_repeat.get("oracle_consultations") != 0:
                print(json.dumps(oracle_plan_repeat, indent=2), file=sys.stderr)
                return 1
            if not any(event.get("event_kind") == "oracle_consultation_completed" and event.get("source") == "bio-Plan" for event in oracle_plan_events):
                print(json.dumps(oracle_plan_events, indent=2), file=sys.stderr)
                return 1
            if not list((base / "oracle_sessions" / "bio-Plan").glob("*.jsonl")) or not list((base / "oracle_sessions" / "bio-Plan").glob("*.md")):
                print("bio-Plan oracle transcript missing", file=sys.stderr)
                return 1
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
            oracle_consultation.oracle_client.run_session = oracle_original_run_session
            oracle_consultation.subprocess.run = oracle_original_subprocess_run

        plan_phase_paths = _temp_paths(base / "plan_phase")
        plan_phase_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        plan_phase_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {"claim_id": "phase.one.a", "hypothesis_level": "H0", "phase": 1, "status": "passed"},
                        {"claim_id": "phase.one.b", "hypothesis_level": "H1", "phase": 1, "status": "passed"},
                        {"claim_id": "phase.one.c", "hypothesis_level": "H2", "phase": 1, "status": "passed"},
                        {"claim_id": "self.claim", "hypothesis_level": "meta", "phase": 1, "status": "open"},
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        plan_phase_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        plan_phase_paths.experiments_registry.write_text(
            json.dumps({"version": "bio-reality-experiments-v1", "experiments": []}, indent=2),
            encoding="utf-8",
        )
        plan_phase_store = BioRealityStore(plan_phase_paths)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = oracle_disabled_config_path
        try:
            plan_phase_summary = run_plan_lane(plan_phase_store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        plan_phase_events = plan_phase_store.load_events()
        if plan_phase_summary["phase_advance_events"] != 1:
            print(json.dumps({"summary": plan_phase_summary, "events": plan_phase_events}, indent=2), file=sys.stderr)
            return 1
        if not any(event.get("event_kind") == "phase_advance_proposed" and event.get("subject_id") == "1" for event in plan_phase_events):
            print(json.dumps(plan_phase_events, indent=2), file=sys.stderr)
            return 1
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = oracle_disabled_config_path
        try:
            plan_phase_repeat = run_plan_lane(plan_phase_store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        if plan_phase_repeat["phase_advance_events"] != 0:
            print(json.dumps({"summary": plan_phase_repeat, "events": plan_phase_store.load_events()}, indent=2), file=sys.stderr)
            return 1

        stuck_paths = _temp_paths(base / "plan_stuck")
        stuck_paths.claims_registry.parent.mkdir(parents=True, exist_ok=True)
        stuck_paths.claims_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-claims-v1",
                    "claims": [
                        {
                            "claim_id": "stuck.claim",
                            "hypothesis_level": "H1",
                            "phase": 1,
                            "status": "failed",
                            "experiment_id": "x",
                        }
                    ],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        stuck_paths.experiments_registry.parent.mkdir(parents=True, exist_ok=True)
        stuck_paths.experiments_registry.write_text(
            json.dumps(
                {
                    "version": "bio-reality-experiments-v1",
                    "experiments": [{"experiment_id": "x", "claim_id": "stuck.claim"}],
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            stuck_paths.experiment_runs,
            [
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:01+00:00",
                },
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:02+00:00",
                },
                {
                    "experiment_id": "x",
                    "claim_id": "stuck.claim",
                    "status": "failed",
                    "checks": [{"name": "check_y", "passed": False}],
                    "completed_at": "2026-05-25T00:00:03+00:00",
                },
            ],
        )
        stuck_store = BioRealityStore(stuck_paths)
        original_pipeline_config = PIPELINE_CONFIG
        globals()["PIPELINE_CONFIG"] = oracle_disabled_config_path
        try:
            stuck_summary = run_plan_lane(stuck_store)
        finally:
            globals()["PIPELINE_CONFIG"] = original_pipeline_config
        stuck_events = stuck_store.load_events()
        if stuck_summary["stuck_redesign_events"] != 1:
            print(json.dumps({"summary": stuck_summary, "events": stuck_events}, indent=2), file=sys.stderr)
            return 1
        if not any(event.get("event_kind") == "claim_redesign_proposed" and event.get("subject_id") == "x" for event in stuck_events):
            print(json.dumps(stuck_events, indent=2), file=sys.stderr)
            return 1
    print("[bio-reality-lanes] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run BioReality V/P/G/X/N/R/W/B/Q/A lanes")
    parser.add_argument("--lane", choices=["vision", "packet", "gate", "execute", "namecert", "agent", "writeback", "bedc", "quality", "assimilate", "all"], default="all")
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--max-dispatch", type=int, default=1)
    parser.add_argument("--conjectures", default=str(BioRealityPaths.conjectures))
    parser.add_argument("--contacts", default=str(BioRealityPaths.contacts))
    parser.add_argument("--probes", default=str(BioRealityPaths.probes))
    parser.add_argument("--mismatches", default=str(BioRealityPaths.mismatches))
    parser.add_argument("--gate-results", default=str(BioRealityPaths.gate_results))
    parser.add_argument("--deepening-tasks", default=str(BioRealityPaths.deepening_tasks))
    parser.add_argument("--review-queue", default=str(BioRealityPaths.review_queue))
    parser.add_argument("--packet-targets", default=str(BioRealityPaths.packet_targets))
    parser.add_argument("--events", default=str(BioRealityPaths.events))
    parser.add_argument("--agent-tasks", default=str(BioRealityPaths.agent_tasks))
    parser.add_argument("--agent-reviews", default=str(BioRealityPaths.agent_reviews))
    parser.add_argument("--dispatch-results", default=str(BioRealityPaths.dispatch_results))
    parser.add_argument("--hardening-targets", default=str(BioRealityPaths.hardening_targets))
    parser.add_argument("--lane-dashboard", default=str(BioRealityPaths.lane_dashboard))
    parser.add_argument("--vision-dir", default=str(BioRealityPaths.vision_dir))
    parser.add_argument("--vision-ledger", default=str(BioRealityPaths.vision_ledger))
    parser.add_argument("--paper-main", default=str(BioRealityPaths.paper_main))
    parser.add_argument("--paper-part", default=str(BioRealityPaths.paper_part))
    parser.add_argument("--self-test", action="store_true")
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
        packet_targets=Path(args.packet_targets),
        events=Path(args.events),
        agent_tasks=Path(args.agent_tasks),
        agent_reviews=Path(args.agent_reviews),
        dispatch_results=Path(args.dispatch_results),
        hardening_targets=Path(args.hardening_targets),
        lane_dashboard=Path(args.lane_dashboard),
        vision_dir=Path(args.vision_dir),
        vision_ledger=Path(args.vision_ledger),
        paper_main=Path(args.paper_main),
        paper_part=Path(args.paper_part),
    )
    store = BioRealityStore(paths)
    summaries: list[dict[str, Any]] = []
    if args.lane in {"vision", "all"}:
        summaries.append(run_vision_lane(store))
    if args.lane in {"packet", "all"}:
        summaries.append(run_packet_lane(store))
    if args.lane in {"gate", "all"}:
        summaries.append(run_gate_lane(store))
    if args.lane in {"execute", "all"}:
        summaries.append(run_execute_lane(store))
    if args.lane in {"namecert", "all"}:
        summaries.append(run_namecert_lane(store))
    if args.lane in {"agent", "all"}:
        summaries.append(run_agent_lane(store, execute_codex=not args.plan_only, max_dispatch=max(0, args.max_dispatch)))
    if args.lane in {"writeback", "all"}:
        summaries.append(run_writeback_lane(store))
    if args.lane in {"bedc", "all"}:
        summaries.append(run_bedc_writeback_lane(store))
    if args.lane in {"quality", "all"}:
        summaries.append(run_quality_lane(store))
    if args.lane in {"assimilate", "all"}:
        summaries.append(run_assimilation_lane(paths))
    print(json.dumps(summaries, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

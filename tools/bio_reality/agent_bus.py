#!/usr/bin/env python3
"""Event-driven agent dispatch contracts for BioReality."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from store import BioRealityPaths, BioRealityStore, read_jsonl, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from store import BioRealityPaths, BioRealityStore, read_jsonl, write_jsonl

try:
    from experiments.runner import load_claims_registry as runner_load_claims_registry
except ModuleNotFoundError:  # pragma: no cover
    try:
        from .experiments.runner import load_claims_registry as runner_load_claims_registry
    except ImportError:  # pragma: no cover
        runner_load_claims_registry = None


SCRIPT_DIR = Path(__file__).resolve().parent
EVENT_STATUSES = {"open", "consumed", "archived"}
TASK_STATUSES = {"queued", "in_flight", "completed", "failed", "archived"}

AGENTS = {
    "bio-researcher": {
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/inbox/conjectures.jsonl",
            "tools/bio_reality/inbox/reality_contacts.jsonl",
            "tools/bio_reality/inbox/probes.jsonl",
            "tools/bio_reality/inbox/mismatches.jsonl",
        ],
        "mission": "extend BioReality research memory under external-reality and cannot-claim discipline",
    },
    "bio-gate-curator": {
        "lane": "bio-Q",
        "writes": [
            "tools/bio_reality/deepening_gates.py",
            "tools/bio_reality/*.schema.json",
            "tools/bio_reality/pipeline_config.json",
        ],
        "mission": "harden deterministic gates from recurring pass and failure reasons",
    },
    "bio-experimentalist": {
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/experiments/run_*.py",
            "tools/bio_reality/data/*.json",
            "tools/bio_reality/registries/experiments.json",
        ],
        "mission": "implement or repair BioReality experiment scripts that produce a single JSON result with checks and status",
    },
    "bio-planner": {
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/registries/claims.json",
            "tools/bio_reality/registries/experiments.json",
            "tools/bio_reality/experiments/run_*.py",
            "tools/bio_reality/data/*.json",
        ],
        "mission": "decompose passed BioReality content into next-step BEDC claim and experiment skeletons, or redesign stuck claims with stronger statistics",
    },
    "bio-namer": {
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/state/namecert_proposals/*.md",
        ],
        "mission": "translate a stable BioReality claim into a Loning-format NameCert proposal markdown with explicit external-reality fields and avoid Loning's already-occupied namespaces",
    },
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def stable_id(prefix: str, payload: dict[str, Any]) -> str:
    material = json.dumps(payload, sort_keys=True, ensure_ascii=True)
    digest = hashlib.sha256(material.encode("utf-8")).hexdigest()[:16]
    return f"{prefix}.{digest}"


def _stable_event_key(event_kind: str, subject_kind: str, subject_id: str) -> str:
    return f"{event_kind}::{subject_kind}::{subject_id}"


def _event_stable_key(event: dict[str, Any]) -> str:
    return str(
        event.get("stable_event_key")
        or _stable_event_key(
            str(event.get("event_kind") or ""),
            str(event.get("subject_kind") or ""),
            str(event.get("subject_id") or ""),
        )
    )


def _dedup(records: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    status_rank = {"open": 0, "consumed": 1, "archived": 2}
    by_stable_key: dict[str, dict[str, Any]] = {}
    for record in records:
        value = str(record.get(key) or stable_id(key, record))
        if value in seen:
            continue
        seen.add(value)
        if key != "event_id":
            out.append(record)
            continue
        normalized = _normalize_event(record)
        stable_key = _event_stable_key(normalized)
        normalized["stable_event_key"] = stable_key
        previous = by_stable_key.get(stable_key)
        if previous is None:
            by_stable_key[stable_key] = normalized
            out.append(normalized)
            continue
        previous_status = str(previous.get("status") or "open")
        current_status = str(normalized.get("status") or "open")
        terminal_statuses = {"consumed", "archived"}
        # When the previous record reached a terminal state and the current
        # record is a fresh open signal (new event_id), keep both. The new
        # emission represents a re-detected condition that should drive a new
        # downstream task; merging would silently swallow it.
        if previous_status in terminal_statuses and current_status == "open":
            by_stable_key[stable_key] = normalized
            out.append(normalized)
            continue
        keep_status = previous_status
        if status_rank.get(current_status, 0) > status_rank.get(previous_status, 0):
            keep_status = current_status
        created_values = [str(item.get("created_at") or "") for item in (previous, normalized) if item.get("created_at")]
        merged = dict(previous)
        merged.update(normalized)
        merged["event_id"] = previous.get("event_id") or normalized.get("event_id")
        merged["status"] = keep_status
        if created_values:
            merged["created_at"] = min(created_values)
        index = out.index(previous)
        out[index] = merged
        by_stable_key[stable_key] = merged
    return out


def _normalize_event(event: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(event)
    status = str(normalized.get("status") or "open")
    normalized["status"] = status if status in EVENT_STATUSES else "open"
    normalized["stable_event_key"] = _event_stable_key(normalized)
    return normalized


def _normalize_task(task: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(task)
    status = str(normalized.get("status") or "queued")
    normalized["status"] = status if status in TASK_STATUSES else "queued"
    normalized["last_dispatch_at"] = normalized.get("last_dispatch_at")
    try:
        normalized["dispatch_count"] = int(normalized.get("dispatch_count") or 0)
    except (TypeError, ValueError):
        normalized["dispatch_count"] = 0
    return normalized


def _status_sort(task: dict[str, Any]) -> tuple[int, str, str]:
    return (-int(task.get("priority") or 0), str(task.get("agent_id") or ""), str(task.get("task_id") or ""))


def _event(event_kind: str, source: str, subject_kind: str, subject_id: str, reason: str, payload: dict[str, Any]) -> dict[str, Any]:
    stable_event_key = _stable_event_key(event_kind, subject_kind, subject_id)
    base = {
        "event_kind": event_kind,
        "source": source,
        "subject_kind": subject_kind,
        "subject_id": subject_id,
        "reason": reason,
        "payload": payload,
    }
    return {
        "event_id": stable_id("event", base),
        "created_at": now_iso(),
        "status": "open",
        "stable_event_key": stable_event_key,
        **base,
    }


def _read_claims_registry(path: Path) -> dict[str, dict[str, Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    claims = data.get("claims") if isinstance(data, dict) else None
    if not isinstance(claims, list):
        return {}
    return {
        str(item.get("claim_id")): item
        for item in claims
        if isinstance(item, dict) and item.get("claim_id")
    }


def _load_claims_registry(store: BioRealityStore) -> dict[str, dict[str, Any]]:
    default_path = (SCRIPT_DIR / "registries" / "claims.json").resolve()
    configured_path = store.paths.claims_registry.resolve()
    if runner_load_claims_registry is not None and configured_path == default_path:
        claims = runner_load_claims_registry(SCRIPT_DIR.parent.parent)
        if claims:
            return claims
    return _read_claims_registry(store.paths.claims_registry)


def _claim_status_by_experiment(store: BioRealityStore) -> dict[str, str]:
    statuses: dict[str, str] = {}
    for claim in _load_claims_registry(store).values():
        experiment_id = str(claim.get("experiment_id") or "")
        if experiment_id:
            statuses[experiment_id] = str(claim.get("status") or "")
    return statuses


def _latest_experiment_runs(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    latest_by_experiment: dict[str, dict[str, Any]] = {}
    for record in sorted(records, key=lambda item: str(item.get("completed_at") or ""), reverse=True):
        experiment_id = str(record.get("experiment_id") or "")
        if not experiment_id or experiment_id in latest_by_experiment:
            continue
        latest_by_experiment[experiment_id] = record
    return list(latest_by_experiment.values())


def build_events(store: BioRealityStore) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = [_normalize_event(event) for event in store.load_events()]
    for task in read_jsonl(store.paths.deepening_tasks):
        task_kind = str(task.get("task_kind") or "")
        packet_kind = str(task.get("packet_kind") or "")
        packet_id = str(task.get("packet_id") or "")
        reason = str(task.get("reason") or task_kind)
        if task_kind == "ready_for_operator_review":
            events.append(_event("research_review_ready", "bio-G", packet_kind, packet_id, reason, task))
        elif task_kind:
            events.append(_event("research_deepening_needed", "bio-G", packet_kind, packet_id, reason, task))
    for result in read_jsonl(store.paths.gate_results):
        if result.get("gate_status") != "gate_blocked":
            continue
        packet_kind = str(result.get("packet_kind") or "")
        packet_id = str(result.get("packet_id") or "")
        issues = result.get("issues") if isinstance(result.get("issues"), list) else []
        reason = "; ".join(str(issue) for issue in issues[:3]) or "gate blocked"
        events.append(_event("gate_failure", "bio-G", packet_kind, packet_id, reason, result))
    claim_status_by_experiment = _claim_status_by_experiment(store)
    for result in _latest_experiment_runs(read_jsonl(store.paths.experiment_runs)):
        status = str(result.get("status") or "")
        experiment_id = str(result.get("experiment_id") or "")
        claim_id = str(result.get("claim_id") or "")
        claim_status = claim_status_by_experiment.get(experiment_id, "")
        if claim_status == "passed":
            # skipped event: claim already passed
            continue
        if status in {"failed", "error"}:
            events.append(
                _event(
                    "experiment_failed",
                    "bio-X",
                    "experiment",
                    experiment_id,
                    f"experiment {status}: {claim_id}",
                    result,
                )
            )
        elif status == "needs_data":
            events.append(
                _event(
                    "data_contact_needed",
                    "bio-X",
                    "experiment",
                    experiment_id,
                    f"experiment needs data: {claim_id}",
                    result,
                )
            )
    return _dedup(events, "event_id")


def _task_for_event(event: dict[str, Any], agent_id: str, action: str, priority: int) -> dict[str, Any]:
    agent = AGENTS[agent_id]
    stable_event_key = _event_stable_key(event)
    base = {
        "agent_id": agent_id,
        "action": action,
        "stable_event_key": stable_event_key,
    }
    return {
        "task_id": stable_id("agent-task", base),
        "created_at": now_iso(),
        "status": "queued",
        "last_dispatch_at": None,
        "dispatch_count": 0,
        "priority": priority,
        "agent_id": agent_id,
        "lane": agent["lane"],
        "event_id": event["event_id"],
        "stable_event_key": stable_event_key,
        "action": action,
        "reason": event["reason"],
        "allowed_writes": agent["writes"],
        "prompt": render_prompt(event, agent_id, action),
    }


def _active_task_key(task: dict[str, Any]) -> tuple[str, str, str]:
    return (
        str(task.get("agent_id") or ""),
        str(task.get("action") or ""),
        str(task.get("stable_event_key") or ""),
    )


def plan_agent_tasks(events: list[dict[str, Any]], existing_tasks: list[dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []
    # Planner actions are allowed to retry after a completed round because the
    # planner reads current state each time and the prompt forbids goalpost
    # shifts. Other agent actions treat "completed" as terminal to avoid
    # re-editing scripts that are already passing.
    planner_actions = {"redesign_stuck_claim", "draft_next_phase_claim_and_experiment"}
    strict_statuses = {"queued", "in_flight", "completed"}
    relaxed_statuses = {"queued", "in_flight"}
    strict_keys: set[tuple[str, str, str]] = set()
    relaxed_keys: set[tuple[str, str, str]] = set()
    for task in existing_tasks or []:
        if not str(task.get("stable_event_key") or ""):
            continue
        status = str(task.get("status") or "queued")
        key = _active_task_key(task)
        if status in strict_statuses:
            strict_keys.add(key)
        if status in relaxed_statuses:
            relaxed_keys.add(key)

    def append_task(event: dict[str, Any], agent_id: str, action: str, priority: int) -> None:
        stable_key = _event_stable_key(event)
        key = (agent_id, action, stable_key)
        guard = relaxed_keys if action in planner_actions else strict_keys
        if key in guard:
            return
        task = _task_for_event(event, agent_id, action, priority)
        new_key = _active_task_key(task)
        strict_keys.add(new_key)
        relaxed_keys.add(new_key)
        tasks.append(task)

    for event in events:
        if str(event.get("status") or "open") != "open":
            continue
        kind = str(event.get("event_kind") or "")
        if kind == "research_deepening_needed":
            append_task(event, "bio-researcher", "extend_research_memory", 85)
        elif kind == "research_review_ready":
            append_task(event, "bio-researcher", "seek_next_reality_boundary", 40)
        elif kind == "vision_ready":
            append_task(event, "bio-researcher", "materialize_vision_into_research_memory", 88)
        elif kind == "vision_blocked":
            append_task(event, "bio-gate-curator", "harden_vision_intake_or_dependencies", 80)
        elif kind == "gate_failure":
            append_task(event, "bio-gate-curator", "harden_gate_or_schema", 95)
        elif kind in {"experiment_failed", "experiment_error"}:
            append_task(event, "bio-experimentalist", "repair_experiment_script", 98)
        elif kind == "data_contact_needed":
            append_task(event, "bio-experimentalist", "add_data_manifest", 96)
        elif kind == "phase_advance_proposed":
            append_task(event, "bio-planner", "draft_next_phase_claim_and_experiment", 70)
        elif kind == "claim_redesign_proposed":
            append_task(event, "bio-planner", "redesign_stuck_claim", 75)
        elif kind == "namecert_proposal_needed":
            append_task(event, "bio-namer", "draft_namecert_proposal", 60)
    tasks.sort(key=_status_sort)
    return _dedup(tasks, "task_id")


def merge_agent_tasks(existing: list[dict[str, Any]], planned: list[dict[str, Any]]) -> list[dict[str, Any]]:
    task_by_id: dict[str, dict[str, Any]] = {}
    order: list[str] = []
    planned_event_ids = {str(task.get("event_id") or "") for task in planned}
    planned_stable_keys = {str(task.get("stable_event_key") or "") for task in planned}
    for task in existing:
        normalized = _normalize_task(task)
        task_id = str(normalized.get("task_id") or stable_id("agent-task", normalized))
        normalized["task_id"] = task_id
        if task_id not in task_by_id:
            order.append(task_id)
        task_by_id[task_id] = normalized
    for task in planned:
        normalized = _normalize_task(task)
        task_id = str(normalized.get("task_id") or "")
        previous = task_by_id.get(task_id)
        if previous is not None:
            merged = {**normalized, **previous}
            if str(merged.get("status") or "") == "failed" and (
                str(merged.get("event_id") or "") in planned_event_ids
                or str(merged.get("stable_event_key") or "") in planned_stable_keys
            ):
                merged["status"] = "queued"
            task_by_id[task_id] = _normalize_task(merged)
        else:
            order.append(task_id)
            task_by_id[task_id] = normalized
    return sorted((task_by_id[task_id] for task_id in order), key=_status_sort)


def render_prompt(event: dict[str, Any], agent_id: str, action: str) -> str:
    agent = AGENTS[agent_id]
    payload = json.dumps(event, ensure_ascii=False, sort_keys=True, indent=2)
    extra_rules: list[str] = []
    if agent_id == "bio-experimentalist":
        extra_rules = [
            "",
            "Bio-experimentalist constraints:",
            "",
            "MANDATORY pre-edit self-check:",
            "",
            "Step 0a. Identify the target experiment script from the event's subject_id:",
            "- subject_id is the experiment_id; find the matching script_path in tools/bio_reality/registries/experiments.json.",
            "",
            "Step 0b. Run the current script BEFORE making any edit:",
            "- python3 <script_path>",
            "- Parse the last non-empty stdout line as JSON.",
            '- If the parsed JSON\'s "status" field equals "passed":',
            "  - Do NOT edit any file.",
            '  - Print "no-op: experiment <id> already passing under current claim acceptance".',
            "  - Exit with code 0.",
            "",
            'Step 0c. Only proceed to repair if status != "passed".',
            "",
            'Step 0d. After repair, run the script again and confirm it now produces status="passed". If the failure is theoretically real and not a script bug, Do NOT fake passed: leave it failed and instead propose adding a new experiment with a different statistic; in this case write a notes file tools/bio_reality/state/proposed_experiments/<id>.md describing what new experiment should be added, but you yourself may not add it.',
            "",
            "You may only edit script files matching tools/bio_reality/experiments/run_*.py or data files under tools/bio_reality/data/. The script must end by printing a single-line JSON to stdout with fields experiment_id, claim_id, status, checks, result, started_at, completed_at. Python 3 stdlib only.",
        ]
    elif agent_id == "bio-planner":
        extra_rules = [
            "",
            "PLANNING DISCIPLINE (hard rules for bio-planner):",
            "",
            "- BEDC five-tuple is mandatory for every new conjecture: carrier,",
            "  distinctions (list, non-empty), readback, internal_structure (list,",
            '  must not be just ["none"] when bedc_* evidence is claimed),',
            "  forbidden_claims (list, must name what the new claim does NOT cover).",
            "",
            "- depends_on must list ONLY claim_ids that currently have status",
            '  "passed" in claims.json. Never list a "failed" / "open" / "needs_data"',
            "  claim as a dependency.",
            "",
            "- Layer monotonicity: a new claim's claimed_layer must be the next",
            "  layer in dna_to_protein_ladder.json (e.g. orf_eligibility may be",
            "  drafted only after all code_read claims are passed). Never skip",
            "  layers.",
            "",
            "- Phase monotonicity: do not add a phase 2 claim while any phase 1",
            "  claim is still failed or open. Do not add a phase 3 claim while any",
            "  phase 2 claim is still failed or open.",
            "",
            "- When drafting a new experiment script, the script must be a real",
            "  Python 3 stdlib computation. Emit single-line JSON on stdout. Return",
            '  status="needs_data" if external data is unavailable; never return',
            '  status="passed" without computation.',
            "",
            "- When redesigning a stuck claim: ANALYZE first (read the most recent",
            "  experiment_runs for that experiment_id, identify which check is",
            "  failing and why), then propose a STRONGER statistic (larger N,",
            "  alternative null, different significance test) - never weaken the acceptance",
            "  to make a failing claim pass. If you cannot find a",
            "  scientifically stronger test, write a single-paragraph rationale to",
            "  tools/bio_reality/state/proposed_experiments/<claim_id>.md and DO",
            "  NOT modify the claim.",
            "",
            '- Do not delete or modify any claim with status "passed".',
            '- Do not modify claims.json claim definitions (statement, depends_on,',
            '  experiment_id) for claims currently status="failed" - only allowed',
            "  to (a) leave them, (b) propose a new sibling claim, (c) propose a",
            "  new acceptance criterion in registries/experiments.json that the",
            "  experiment must now satisfy.",
            "- All edits must be atomic and pass the BioReality self-tests before",
            "  you finish.",
        ]
    elif agent_id == "bio-namer":
        extra_rules = [
            "",
            "NAMECERT PROPOSAL DISCIPLINE (hard rules for bio-namer):",
            "",
            "Step 0. Read the event payload to find claim_id and linked_conjecture_id.",
            "  Read tools/bio_reality/registries/claims.json and find the matching claim;",
            "  read tools/bio_reality/inbox/conjectures.jsonl and find the matching",
            "  conjecture; read the latest experiment_runs.jsonl entry for the claim.",
            "",
            "Step 1. Read tools/bio_reality/state/research_notes/loning_writeback_pattern.md",
            "  if it exists. It records Loning's already-occupied terms",
            "  (Codon64, Q_6, M^star, StopCodonZeckendorfSuffix, etc.) and recommended",
            "  prefixes (BioRealityQSix, RealityBoundCodonTopology, CuratedGeneticTableLedger,",
            "  EmpiricalCodonSpectrum). Avoid Loning's occupied names; use the recommended",
            "  prefixes.",
            "",
            "Step 2. Compose a NameCert proposal markdown at",
            "  tools/bio_reality/state/namecert_proposals/<claim_id>.md with EXACTLY these",
            "  sections (in order, including the header lines verbatim):",
            "",
            "  # NameCert proposal for <claim_id>",
            "",
            "  ## 1. Loning-format chapter slug",
            "  Propose a slug like <NNN>_<concept_in_snake_case>_namecert_construction",
            "  using a BioReality-namespaced concept (must not clash with Loning).",
            "",
            "  ## 2. Carrier",
            "  Carrier name (CamelCase, must start with BioReality or RealityBound or Empirical",
            "  or Curated). Include short BEDC 5-tuple description.",
            "",
            "  ## 3. Distinctions",
            "  List the distinctions enumerated by the experiment (e.g., codons in R, codons in M).",
            "",
            "  ## 4. Readback",
            "  How the carrier reads back to observable data.",
            "",
            "  ## 5. Internal newmath/BEDC derivation",
            "  Pure-BEDC content (median closure, spectrum, quotient). NO external biological",
            "  numbers as kernel facts. Numbers go in section 6.",
            "",
            "  ## 6. External reality sources",
            "  Cite curated NCBI tables, experiment_run IDs, and statistical witnesses by",
            "  reference, not by repeating their contents. External numbers stay as bridge /",
            "  provenance fields, never internalised.",
            "",
            "  ## 7. Cannot-claim boundary",
            "  Use Loning's pattern: list what this chapter explicitly does NOT claim",
            "  (e.g., biological-code necessity, translation realisation, folding,",
            "  function realisation, universal mechanism).",
            "",
            "  ## 8. Bridge disclaimer",
            '  Single paragraph mirroring Loning\'s "vision-level scientific-model bridge"',
            "  language, adjusted for this claim.",
            "",
            "  ## 9. Lean target sketch (statement-only)",
            "  A single line describing what Lean object would carry this (e.g.,",
            "  BEDC.Derived.BioRealityQSixMedianClosureUp.TasteGate carrier alignment).",
            "  Do NOT write Lean code; this section is text only.",
            "",
            "Step 3. Do not edit any other file. Do not modify claims.json, conjectures.jsonl,",
            "  or any registry. Do not create new experiments. Do not call codex",
            "  recursively. Do not push remote.",
            "",
            "Step 4. After writing the proposal, print a one-line completion summary to",
            "  stdout listing the proposal path and the proposed slug.",
        ]
    return "\n".join(
        [
            "You are a BioReality automation agent inside the newmath repository.",
            f"Agent: {agent_id}",
            f"Mission: {agent['mission']}",
            f"Action: {action}",
            "",
            "Hard rules:",
            "- Preserve the distinction between external curated biological reality and internal newmath/BEDC derivation.",
            "- Do not promote codon/window geometry to translation, structure, physical admissibility, function, or global biological law without a separate reality contact.",
            "- Write only inside the allowed paths named in the task.",
            "- Make one minimal research-memory or gate-hardening change; do not broaden the project scope.",
            "- Run the relevant BioReality gates before reporting completion.",
            "- Do not commit and do not push remote refs; the supervisor/orchestrator owns commits.",
            *extra_rules,
            "",
            "Allowed write paths:",
            json.dumps(agent["writes"], ensure_ascii=False, indent=2),
            "",
            "Event:",
            payload,
            "",
            "Return a concise completion summary naming changed files, gate result, and remaining blockers.",
        ]
    )


def review_tasks(tasks: list[dict[str, Any]], events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    event_by_id = {str(event.get("event_id") or ""): event for event in events}
    reviews: list[dict[str, Any]] = []
    for task in tasks:
        event = event_by_id.get(str(task.get("event_id") or ""), {})
        event_kind = str(event.get("event_kind") or "")
        if event_kind == "gate_failure":
            decision = "requires_gate_hardening"
        elif event_kind == "vision_blocked":
            decision = "requires_gate_hardening"
        elif event_kind == "research_review_ready":
            decision = "ready_for_next_boundary_search"
        elif event_kind == "vision_ready":
            decision = "requires_research_execution"
        else:
            decision = "requires_research_execution"
        base = {
            "task_id": task.get("task_id"),
            "decision": decision,
            "event_kind": event_kind,
        }
        reviews.append(
            {
                "review_id": stable_id("agent-review", base),
                "created_at": now_iso(),
                "task_id": task.get("task_id"),
                "agent_id": task.get("agent_id"),
                "event_id": task.get("event_id"),
                "decision": decision,
                "reason": task.get("reason"),
                "passed": decision == "ready_for_next_boundary_search",
            }
        )
    return _dedup(reviews, "review_id")


def reviews_from_dispatches(dispatches: list[dict[str, Any]], tasks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    task_by_id = {str(task.get("task_id") or ""): task for task in tasks}
    reviews: list[dict[str, Any]] = []
    for dispatch in dispatches:
        task_id = str(dispatch.get("task_id") or "")
        task = task_by_id.get(task_id, {})
        status = str(dispatch.get("dispatch_status") or "")
        if status == "completed":
            decision = "dispatch_completed_needs_gate_review"
            passed = True
        elif status == "planned_only":
            decision = "dispatch_planned_only"
            passed = False
        else:
            decision = "dispatch_failed"
            passed = False
        base = {"task_id": task_id, "decision": decision, "status": status}
        reviews.append(
            {
                "review_id": stable_id("dispatch-review", base),
                "created_at": now_iso(),
                "task_id": task_id,
                "agent_id": task.get("agent_id"),
                "event_id": task.get("event_id"),
                "decision": decision,
                "reason": dispatch.get("stderr_tail") or dispatch.get("stdout_tail") or dispatch.get("dispatch_status"),
                "passed": passed,
            }
        )
    return _dedup(reviews, "review_id")


def _parse_git_status(output: str) -> dict[str, str]:
    status: dict[str, str] = {}
    for raw_line in output.splitlines():
        if not raw_line:
            continue
        code = raw_line[:2]
        path = raw_line[3:] if len(raw_line) > 3 else ""
        if " -> " in path:
            path = path.rsplit(" -> ", 1)[1]
        if path:
            status[path] = code
    return status


def _git_status(repo_root: Path) -> dict[str, str]:
    result = subprocess.run(
        ["git", "-C", str(repo_root), "status", "--porcelain"],
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        return {}
    return _parse_git_status(result.stdout)


def _paths_changed_since(before: dict[str, str], after: dict[str, str]) -> list[str]:
    changed = [path for path, status in after.items() if before.get(path) != status]
    return sorted(changed)


def _allowed_path(path: str, patterns: list[str]) -> bool:
    return any(fnmatch.fnmatch(path, pattern) for pattern in patterns)


def _revert_paths(repo_root: Path, paths: list[str]) -> None:
    for path in sorted(set(paths)):
        subprocess.run(
            ["git", "-C", str(repo_root), "checkout", "HEAD", "--", path],
            text=True,
            capture_output=True,
            check=False,
        )
        current = _git_status(repo_root).get(path)
        if current == "??":
            target = repo_root / path
            if target.is_dir():
                for child in sorted(target.rglob("*"), reverse=True):
                    if child.is_file() or child.is_symlink():
                        child.unlink()
                    elif child.is_dir():
                        child.rmdir()
                target.rmdir()
            elif target.exists() or target.is_symlink():
                target.unlink()


def _expanded_allowed_paths(repo_root: Path, patterns: list[str]) -> list[str]:
    paths: set[str] = set()
    for pattern in patterns:
        if any(char in pattern for char in "*?["):
            for match in repo_root.glob(pattern):
                try:
                    paths.add(match.relative_to(repo_root).as_posix())
                except ValueError:
                    continue
        else:
            paths.add(pattern)
    return sorted(paths)


def _append_stderr_tail(dispatch: dict[str, Any], message: str) -> None:
    previous = str(dispatch.get("stderr_tail") or "")
    combined = f"{previous}\n{message}" if previous else message
    dispatch["stderr_tail"] = combined[-2000:]


def hardening_targets(reviews: list[dict[str, Any]]) -> list[dict[str, Any]]:
    targets: list[dict[str, Any]] = []
    for review in reviews:
        decision = str(review.get("decision") or "")
        if decision not in {"requires_gate_hardening", "requires_research_execution", "dispatch_failed", "dispatch_planned_only"}:
            continue
        base = {
            "decision": decision,
            "task_id": review.get("task_id"),
            "reason": review.get("reason"),
        }
        targets.append(
            {
                "target_id": stable_id("hardening", base),
                "created_at": now_iso(),
                "source_review": review.get("review_id"),
                "target_kind": "gate_or_prompt" if decision == "requires_gate_hardening" else "research_prompt",
                "reason": review.get("reason"),
                "next_action": "tighten BioReality gate/schema" if decision == "requires_gate_hardening" else "dispatch bio-researcher with event prompt",
            }
        )
    return _dedup(targets, "target_id")


def dispatch_codex(task: dict[str, Any], *, execute: bool) -> dict[str, Any]:
    if not execute:
        return {"task_id": task["task_id"], "dispatch_status": "planned_only"}
    repo_root = SCRIPT_DIR.parent.parent
    allowed_writes = [str(path) for path in task.get("allowed_writes", []) if str(path)]
    before_status = _git_status(repo_root)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".md", delete=False) as handle:
        handle.write(str(task.get("prompt") or ""))
        prompt_path = Path(handle.name)
    result: subprocess.CompletedProcess[str] | None = None
    dispatch: dict[str, Any] | None = None
    try:
        try:
            result = subprocess.run(
                ["codex", "exec", "-C", str(repo_root), prompt_path.read_text(encoding="utf-8")],
                text=True,
                capture_output=True,
                check=False,
                timeout=3600,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            dispatch = {
                "task_id": task["task_id"],
                "dispatch_status": "failed",
                "returncode": None,
                "stdout_tail": "",
                "stderr_tail": str(exc),
            }
    finally:
        try:
            prompt_path.unlink()
        except OSError:
            pass
    if dispatch is None and result is not None:
        dispatch = {
            "task_id": task["task_id"],
            "dispatch_status": "completed" if result.returncode == 0 else "failed",
            "returncode": result.returncode,
            "stdout_tail": result.stdout[-2000:],
            "stderr_tail": result.stderr[-2000:],
        }
    if dispatch is None:
        dispatch = {
            "task_id": task["task_id"],
            "dispatch_status": "failed",
            "returncode": None,
            "stdout_tail": "",
            "stderr_tail": "codex dispatch did not produce a result",
        }
    after_status = _git_status(repo_root)
    changed_paths = _paths_changed_since(before_status, after_status)
    violations = [path for path in changed_paths if not _allowed_path(path, allowed_writes)]
    if violations:
        _revert_paths(repo_root, violations)
        dispatch["dispatch_status"] = "write_path_violation"
        _append_stderr_tail(dispatch, "write_path_violation: " + ", ".join(violations))
        return dispatch
    if task.get("agent_id") == "bio-gate-curator" and dispatch["dispatch_status"] == "completed":
        self_test = subprocess.run(
            ["python3", "tools/bio_reality/deepening_gates.py", "--self-test"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if self_test.returncode != 0:
            _revert_paths(repo_root, _expanded_allowed_paths(repo_root, allowed_writes))
            dispatch["dispatch_status"] = "self_test_failed"
            _append_stderr_tail(dispatch, "self_test_failed: " + self_test.stderr[-500:])
    return dispatch


def apply_dispatch_lifecycle(
    events: list[dict[str, Any]],
    tasks: list[dict[str, Any]],
    dispatches: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    event_by_id = {str(event.get("event_id") or ""): event for event in events}
    task_by_id = {str(task.get("task_id") or ""): task for task in tasks}
    for dispatch in dispatches:
        task = task_by_id.get(str(dispatch.get("task_id") or ""))
        if not task:
            continue
        status = str(dispatch.get("dispatch_status") or "")
        event = event_by_id.get(str(task.get("event_id") or ""))
        if status == "planned_only":
            task["status"] = "queued"
            continue
        if status == "completed":
            task["status"] = "completed"
            if event is not None:
                event["status"] = "consumed"
            continue
        task["status"] = "failed"
        try:
            dispatch_count = int(task.get("dispatch_count") or 0)
        except (TypeError, ValueError):
            dispatch_count = 0
        if event is not None and dispatch_count > 3:
            event["status"] = "archived"
    return events, tasks


def run_agent_lane(store: BioRealityStore, *, execute_codex: bool = True, max_dispatch: int = 1) -> dict[str, Any]:
    events = build_events(store)
    existing_tasks = store.load_agent_tasks()
    planned_tasks = plan_agent_tasks(events, existing_tasks)
    tasks = merge_agent_tasks(existing_tasks, planned_tasks)
    planned_reviews = review_tasks(planned_tasks, events)
    queued = [task for task in tasks if str(task.get("status") or "queued") == "queued"]
    queued.sort(key=_status_sort)
    selected = queued[:max_dispatch]
    if execute_codex:
        dispatch_at = now_iso()
        selected_ids = {str(task.get("task_id") or "") for task in selected}
        for task in tasks:
            if str(task.get("task_id") or "") not in selected_ids:
                continue
            task["status"] = "in_flight"
            task["last_dispatch_at"] = dispatch_at
            task["dispatch_count"] = int(task.get("dispatch_count") or 0) + 1
        store.write_events(events)
        store.write_agent_tasks(tasks)
    dispatches = [dispatch_codex(task, execute=execute_codex) for task in selected]
    events, tasks = apply_dispatch_lifecycle(events, tasks, dispatches)
    reviews = _dedup(planned_reviews + reviews_from_dispatches(dispatches, tasks), "review_id")
    store.write_events(events)
    store.write_agent_tasks(tasks)
    store.append_agent_reviews(reviews)
    store.append_dispatch_results(dispatches)
    return {
        "lane": "bio-R",
        "events": len(events),
        "agent_tasks": len(tasks),
        "agent_reviews": len(reviews),
        "dispatches": len(dispatches),
        "execute_codex": execute_codex,
        "dispatch_completed": sum(1 for item in dispatches if item.get("dispatch_status") == "completed"),
        "dispatch_failed": sum(1 for item in dispatches if item.get("dispatch_status") == "failed"),
    }


def run_quality_lane(store: BioRealityStore) -> dict[str, Any]:
    reviews = store.load_agent_reviews()
    targets = hardening_targets(reviews)
    store.write_hardening_targets(targets)
    return {
        "lane": "bio-Q",
        "agent_reviews": len(reviews),
        "hardening_targets": len(targets),
        "gate_hardening": sum(1 for item in targets if item.get("target_kind") == "gate_or_prompt"),
        "research_prompt_hardening": sum(1 for item in targets if item.get("target_kind") == "research_prompt"),
    }


def self_test() -> int:
    with tempfile.TemporaryDirectory(prefix="bio-reality-agent-bus-") as tmp:
        base = Path(tmp)
        paths = BioRealityPaths(
            root=SCRIPT_DIR,
            gate_results=base / "gate_results.jsonl",
            deepening_tasks=base / "deepening_tasks.jsonl",
            events=base / "events.jsonl",
            agent_tasks=base / "agent_tasks.jsonl",
            agent_reviews=base / "agent_reviews.jsonl",
            agent_reviews_archive=base / "agent_reviews.archive.jsonl",
            dispatch_results=base / "dispatch_results.jsonl",
            dispatch_results_archive=base / "dispatch_results.archive.jsonl",
            hardening_targets=base / "hardening_targets.jsonl",
            claims_registry=base / "claims.json",
            experiment_runs=base / "experiment_runs.jsonl",
        )
        paths.claims_registry.write_text(
            json.dumps(
                {
                    "claims": [
                        {
                            "claim_id": "self.claim",
                            "experiment_id": "self_experiment",
                            "status": "failed",
                        }
                    ]
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            paths.deepening_tasks,
            [
                {
                    "packet_kind": "conjecture",
                    "packet_id": "codon.window6.local.tile.boundary",
                    "task_kind": "ready_for_operator_review",
                    "priority": 20,
                    "reason": "conjecture has gate pass and probe-contact-mismatch chain",
                }
            ],
        )
        write_jsonl(
            paths.gate_results,
            [
                {
                    "packet_kind": "conjecture",
                    "packet_id": "protein.overclaim",
                    "gate_status": "gate_blocked",
                    "issues": ["total-biology language is blocked in conjecture packets"],
                }
            ],
        )
        write_jsonl(
            paths.experiment_runs,
            [
                {
                    "experiment_id": "self_experiment",
                    "claim_id": "self.claim",
                    "status": "failed",
                    "checks": [{"name": "self_check", "passed": False}],
                    "result": {},
                    "completed_at": "2026-05-25T00:00:00+00:00",
                }
            ],
        )
        store = BioRealityStore(paths)
        agent = run_agent_lane(store, execute_codex=False)
        quality = run_quality_lane(store)
        if agent["events"] != 3 or agent["agent_tasks"] != 3:
            print(json.dumps(agent, indent=2), file=sys.stderr)
            return 1
        duplicate_a = _event(
            "vision_ready",
            "bio-V",
            "vision",
            "same-vision",
            "old reason",
            {"checked_at": "2026-05-25T00:00:00+00:00", "value": "old"},
        )
        duplicate_b = _event(
            "vision_ready",
            "bio-V",
            "vision",
            "same-vision",
            "new reason",
            {"checked_at": "2026-05-25T00:00:01+00:00", "value": "new"},
        )
        duplicate_a["created_at"] = "2026-05-25T00:00:00+00:00"
        duplicate_a["status"] = "consumed"
        duplicate_b["created_at"] = "2026-05-25T00:00:01+00:00"
        duplicate_b["status"] = "open"
        duplicate_events = _dedup([duplicate_a, duplicate_b], "event_id")
        # When the previous event with the same stable_event_key is in a
        # terminal state and the current is a fresh open signal, both must
        # survive so the new emission can drive a downstream task.
        if (
            len(duplicate_events) != 2
            or duplicate_events[0].get("status") != "consumed"
            or duplicate_events[1].get("status") != "open"
            or duplicate_events[1].get("reason") != "new reason"
        ):
            print(json.dumps(duplicate_events, indent=2), file=sys.stderr)
            return 1
        # When both records share status "open", the merge still collapses to
        # a single event keeping the newer reason.
        open_a = dict(duplicate_a, status="open", event_id="event.same.open.a")
        open_b = dict(duplicate_b, status="open", event_id="event.same.open.b")
        merged_open = _dedup([open_a, open_b], "event_id")
        if (
            len(merged_open) != 1
            or merged_open[0].get("status") != "open"
            or merged_open[0].get("reason") != "new reason"
        ):
            print(json.dumps(merged_open, indent=2), file=sys.stderr)
            return 1
        filter_paths = BioRealityPaths(
            root=SCRIPT_DIR,
            gate_results=base / "filter_gate_results.jsonl",
            deepening_tasks=base / "filter_deepening_tasks.jsonl",
            events=base / "filter_events.jsonl",
            agent_tasks=base / "filter_agent_tasks.jsonl",
            agent_reviews=base / "filter_agent_reviews.jsonl",
            agent_reviews_archive=base / "filter_agent_reviews.archive.jsonl",
            dispatch_results=base / "filter_dispatch_results.jsonl",
            dispatch_results_archive=base / "filter_dispatch_results.archive.jsonl",
            hardening_targets=base / "filter_hardening_targets.jsonl",
            claims_registry=base / "filter_claims.json",
            experiment_runs=base / "filter_experiment_runs.jsonl",
        )
        filter_paths.claims_registry.write_text(
            json.dumps(
                {
                    "claims": [
                        {
                            "claim_id": "h0.null.model.significance",
                            "experiment_id": "null_model_uniform",
                            "status": "failed",
                        },
                        {
                            "claim_id": "h1.leave.one.codon.out",
                            "experiment_id": "leave_one_codon_out",
                            "status": "passed",
                        },
                    ]
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            filter_paths.experiment_runs,
            [
                {
                    "experiment_id": "leave_one_codon_out",
                    "claim_id": "h1.leave.one.codon.out",
                    "status": "failed",
                    "completed_at": "2026-05-25T00:00:02+00:00",
                },
                {
                    "experiment_id": "null_model_uniform",
                    "claim_id": "h0.null.model.significance",
                    "status": "failed",
                    "completed_at": "2026-05-25T00:00:03+00:00",
                },
            ],
        )
        filtered_events = build_events(BioRealityStore(filter_paths))
        filtered_experiment_failed = [
            event
            for event in filtered_events
            if event.get("event_kind") == "experiment_failed"
        ]
        if len(filtered_experiment_failed) != 1 or filtered_experiment_failed[0].get("subject_id") != "null_model_uniform":
            print(json.dumps(filtered_events, indent=2), file=sys.stderr)
            return 1
        latest_paths = BioRealityPaths(
            root=SCRIPT_DIR,
            gate_results=base / "latest_gate_results.jsonl",
            deepening_tasks=base / "latest_deepening_tasks.jsonl",
            events=base / "latest_events.jsonl",
            agent_tasks=base / "latest_agent_tasks.jsonl",
            agent_reviews=base / "latest_agent_reviews.jsonl",
            agent_reviews_archive=base / "latest_agent_reviews.archive.jsonl",
            dispatch_results=base / "latest_dispatch_results.jsonl",
            dispatch_results_archive=base / "latest_dispatch_results.archive.jsonl",
            hardening_targets=base / "latest_hardening_targets.jsonl",
            claims_registry=base / "latest_claims.json",
            experiment_runs=base / "latest_experiment_runs.jsonl",
        )
        latest_paths.claims_registry.write_text(
            json.dumps(
                {
                    "claims": [
                        {
                            "claim_id": "h0.null.model.significance",
                            "experiment_id": "null_model_uniform",
                            "status": "failed",
                        }
                    ]
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        write_jsonl(
            latest_paths.experiment_runs,
            [
                {
                    "experiment_id": "null_model_uniform",
                    "claim_id": "h0.null.model.significance",
                    "status": "failed",
                    "completed_at": "2026-05-25T00:00:01+00:00",
                },
                {
                    "experiment_id": "null_model_uniform",
                    "claim_id": "h0.null.model.significance",
                    "status": "passed",
                    "completed_at": "2026-05-25T00:00:04+00:00",
                },
            ],
        )
        latest_events = build_events(BioRealityStore(latest_paths))
        if any(event.get("event_kind") == "experiment_failed" for event in latest_events):
            print(json.dumps(latest_events, indent=2), file=sys.stderr)
            return 1
        priority_tasks = plan_agent_tasks(
            [
                _event("vision_ready", "bio-V", "vision", "priority-vision", "ready", {}),
                _event("experiment_failed", "bio-X", "experiment", "priority-experiment", "failed", {}),
            ]
        )
        priority_by_kind = {
            str(task.get("action") or ""): int(task.get("priority") or 0)
            for task in priority_tasks
        }
        if (
            priority_by_kind.get("repair_experiment_script") != 98
            or priority_by_kind.get("materialize_vision_into_research_memory") != 88
            or priority_by_kind["repair_experiment_script"] <= priority_by_kind["materialize_vision_into_research_memory"]
        ):
            print(json.dumps(priority_tasks, indent=2), file=sys.stderr)
            return 1
        planner_tasks = plan_agent_tasks(
            [
                _event("phase_advance_proposed", "bio-Plan", "phase", "1", "phase passed", {}),
                _event("claim_redesign_proposed", "bio-Plan", "experiment", "x", "stuck check", {}),
            ]
        )
        planner_by_action = {
            str(task.get("action") or ""): task
            for task in planner_tasks
        }
        if (
            planner_by_action.get("draft_next_phase_claim_and_experiment", {}).get("agent_id") != "bio-planner"
            or int(planner_by_action.get("draft_next_phase_claim_and_experiment", {}).get("priority") or 0) != 70
            or planner_by_action.get("redesign_stuck_claim", {}).get("agent_id") != "bio-planner"
            or int(planner_by_action.get("redesign_stuck_claim", {}).get("priority") or 0) != 75
        ):
            print(json.dumps(planner_tasks, indent=2), file=sys.stderr)
            return 1
        planner_prompt = render_prompt(
            _event("phase_advance_proposed", "bio-Plan", "phase", "1", "phase passed", {}),
            "bio-planner",
            "draft_next_phase_claim_and_experiment",
        )
        for required_text in ("PLANNING DISCIPLINE", "depends_on must list ONLY", "never weaken the acceptance"):
            if required_text not in planner_prompt:
                print(json.dumps({"missing": required_text, "prompt": planner_prompt}, indent=2), file=sys.stderr)
                return 1
        namer_tasks = plan_agent_tasks(
            [
                _event(
                    "namecert_proposal_needed",
                    "bio-N",
                    "claim",
                    "test.M.size",
                    "claim test.M.size is stable; NameCert proposal not yet written",
                    {"claim_id": "test.M.size", "linked_conjecture_id": "test.codon"},
                )
            ]
        )
        namer_task = next((task for task in namer_tasks if task.get("agent_id") == "bio-namer"), {})
        if namer_task.get("action") != "draft_namecert_proposal" or int(namer_task.get("priority") or 0) != 60:
            print(json.dumps(namer_tasks, indent=2), file=sys.stderr)
            return 1
        namer_prompt = render_prompt(
            _event(
                "namecert_proposal_needed",
                "bio-N",
                "claim",
                "test.M.size",
                "claim test.M.size is stable; NameCert proposal not yet written",
                {"claim_id": "test.M.size", "linked_conjecture_id": "test.codon"},
            ),
            "bio-namer",
            "draft_namecert_proposal",
        )
        for required_text in ("NAMECERT PROPOSAL DISCIPLINE", "BioReality or RealityBound", "vision-level scientific-model bridge"):
            if required_text not in namer_prompt:
                print(json.dumps({"missing": required_text, "prompt": namer_prompt}, indent=2), file=sys.stderr)
                return 1
        stable_event = _event("experiment_failed", "bio-X", "experiment", "same-experiment", "failed", {})
        in_flight = _task_for_event(stable_event, "bio-experimentalist", "repair_experiment_script", 98)
        in_flight["status"] = "in_flight"
        repeat_event = _event(
            "experiment_failed",
            "bio-X",
            "experiment",
            "same-experiment",
            "failed again",
            {"checked_at": "2026-05-25T00:00:02+00:00"},
        )
        if plan_agent_tasks([repeat_event], [in_flight]):
            print(json.dumps({"existing": in_flight, "event": repeat_event}, indent=2), file=sys.stderr)
            return 1
        prompt = render_prompt(stable_event, "bio-experimentalist", "repair_experiment_script")
        for required_text in ("MANDATORY pre-edit self-check", "Do NOT edit any file", "Do NOT fake passed"):
            if required_text not in prompt:
                print(json.dumps({"missing": required_text, "prompt": prompt}, indent=2), file=sys.stderr)
                return 1
        experimentalist_task = next((task for task in store.load_agent_tasks() if task.get("agent_id") == "bio-experimentalist"), {})
        if experimentalist_task.get("action") != "repair_experiment_script":
            print(json.dumps(store.load_agent_tasks(), indent=2), file=sys.stderr)
            return 1
        if quality["hardening_targets"] == 0:
            print(json.dumps(quality, indent=2), file=sys.stderr)
            return 1
        tasks = store.load_agent_tasks()
        first_task = next((task for task in tasks if str(task.get("status") or "") == "queued"), {})
        if not first_task:
            print(json.dumps(tasks, indent=2), file=sys.stderr)
            return 1
        original_dispatch = globals()["dispatch_codex"]
        completed_task_id = first_task["task_id"]
        try:
            globals()["dispatch_codex"] = lambda task, *, execute: {"task_id": task["task_id"], "dispatch_status": "completed"}
            completed_agent = run_agent_lane(store, execute_codex=True, max_dispatch=1)
        finally:
            globals()["dispatch_codex"] = original_dispatch
        completed_store_task = next((task for task in store.load_agent_tasks() if task.get("task_id") == completed_task_id), {})
        completed_store_event = next((item for item in store.load_events() if item.get("event_id") == first_task.get("event_id")), {})
        if completed_agent["dispatch_completed"] != 1 or completed_store_task.get("status") != "completed":
            print(json.dumps({"agent": completed_agent, "task": completed_store_task}, indent=2), file=sys.stderr)
            return 1
        if completed_store_event.get("status") != "consumed":
            print(json.dumps(completed_store_event, indent=2), file=sys.stderr)
            return 1
        events = store.load_events()
        event = next((item for item in events if item.get("event_id") == first_task.get("event_id")), {})
        completed_events, completed_tasks = apply_dispatch_lifecycle(
            events,
            [dict(first_task, status="in_flight", dispatch_count=1)],
            [{"task_id": first_task["task_id"], "dispatch_status": "completed"}],
        )
        if completed_tasks[0]["status"] != "completed":
            print(json.dumps(completed_tasks, indent=2), file=sys.stderr)
            return 1
        completed_event = next((item for item in completed_events if item.get("event_id") == event.get("event_id")), {})
        if completed_event.get("status") != "consumed":
            print(json.dumps(completed_events, indent=2), file=sys.stderr)
            return 1
        failed_events, _failed_tasks = apply_dispatch_lifecycle(
            [_normalize_event(dict(event, status="open"))],
            [dict(first_task, status="in_flight", dispatch_count=4)],
            [{"task_id": first_task["task_id"], "dispatch_status": "failed"}],
        )
        if failed_events[0]["status"] != "archived":
            print(json.dumps(failed_events, indent=2), file=sys.stderr)
            return 1
        if not _allowed_path("tools/bio_reality/inbox/conjectures.jsonl", ["tools/bio_reality/inbox/*.jsonl"]):
            print("expected inbox jsonl glob to match", file=sys.stderr)
            return 1
        if _allowed_path("lean4/Foo.lean", ["tools/bio_reality/inbox/*.jsonl"]):
            print("expected lean4 path not to match inbox glob", file=sys.stderr)
            return 1
    print("[bio-reality-agent-bus] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Plan and review BioReality agent tasks from events")
    parser.add_argument("--plan-only", action="store_true")
    parser.add_argument("--max-dispatch", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    store = BioRealityStore()
    agent = run_agent_lane(store, execute_codex=not args.plan_only, max_dispatch=max(0, args.max_dispatch))
    quality = run_quality_lane(store)
    print(json.dumps({"agent": agent, "quality": quality}, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

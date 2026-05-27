#!/usr/bin/env python3
"""Event-driven agent dispatch contracts for BioReality."""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import re
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
    "bio-data-fetcher": {
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/data/*.json",
            "tools/bio_reality/data/*.py",
            "tools/bio_reality/data/manifests/*.json",
        ],
        "mission": "fetch curated public biological reality data (NCBI / UniProt / Ensembl / RefSeq / EBI) via urllib.request, store as versioned JSON under tools/bio_reality/data/ with provenance, never write paper or experiment scripts",
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
    "bio-oracle-consumer": {
        "agent_id": "bio-oracle-consumer",
        "description": "reads a finished oracle transcript and proposes downstream actions",
        "lane": "bio-R",
        "writes": [
            "tools/bio_reality/registries/claims.json",
            "tools/bio_reality/registries/experiments.json",
            "tools/bio_reality/state/oracle_refinements/*.json",
        ],
        "mission": "read a finished oracle transcript and propose downstream actions",
        "allowed_actions": [
            "consume_oracle_plan_consultation",
            "consume_oracle_gate_consultation",
        ],
        "default_priority": 70,
    },
}


ORACLE_ESCALATION_RULES = [
    "",
    "ORACLE ESCALATION (optional, last resort):",
    "- If after careful analysis you cannot decide between two BEDC-consistent options",
    "  for decomposing a stable BioReality finding, or you cannot identify a stronger",
    "  null model that respects the existing acceptance criteria, you may consult",
    "  the BioReality oracle via:",
    '    python3 tools/bio_reality/oracle/oracle_client.py --query "<concise question>" \\',
    "      --intended-claim <claim_id>",
    "- The oracle responds with text reasoning from a ChatGPT thread. Treat the",
    "  response as advisory, not authoritative. You must still verify any",
    "  proposed change passes the existing deterministic gates.",
    "- Do NOT use oracle for: trivial questions, basic Python syntax, anything you",
    "  can solve with stdlib + the prompt context. Oracle is for BEDC reasoning",
    "  forks and cross-layer concept questions only.",
    "- Oracle responses must not be cited inside paper kernel content. They live",
    "  in proposal markdown notes or commit messages.",
]


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


def _oracle_consumer_key(lane: str, topic: str) -> str:
    return f"oracle_consumer_dispatched::{lane}::{topic}"


def _oracle_consultation_subject_id(lane: str, topic: str) -> str:
    return f"{lane}.{hashlib.sha256(topic.encode('utf-8')).hexdigest()[:12]}"


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


def _read_json_object(path: Path, fallback: dict[str, Any]) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return dict(fallback)
    return data if isinstance(data, dict) else dict(fallback)


def _write_json_object(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False, sort_keys=False) + "\n", encoding="utf-8")


def _load_claims_document(path: Path) -> dict[str, Any]:
    data = _read_json_object(path, {"version": "bio-reality-claims-v1", "claims": []})
    if not isinstance(data.get("claims"), list):
        data["claims"] = []
    return data


def _load_experiments_document(path: Path) -> dict[str, Any]:
    data = _read_json_object(path, {"version": "bio-reality-experiments-v1", "experiments": []})
    if not isinstance(data.get("experiments"), list):
        data["experiments"] = []
    return data


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


def _oracle_sessions_dir(store: BioRealityStore) -> Path:
    events_parent = store.paths.events.parent
    if events_parent.name == "out":
        return events_parent.parent / "state" / "oracle_sessions"
    return events_parent / "state" / "oracle_sessions"


def _oracle_refinements_dir(store: BioRealityStore) -> Path:
    events_parent = store.paths.events.parent
    if events_parent.name == "out":
        return events_parent.parent / "state" / "oracle_refinements"
    return events_parent / "state" / "oracle_refinements"


def _safe_oracle_topic(value: str, *, max_len: int = 80) -> str:
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", value.strip()).strip("-._")
    return (slug or "oracle-topic")[:max_len]


def _parse_oracle_jsonl_header(path: Path) -> dict[str, Any]:
    try:
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                stripped = line.strip()
                if not stripped:
                    continue
                data = json.loads(stripped)
                return data if isinstance(data, dict) else {}
    except (OSError, json.JSONDecodeError):
        return {}
    return {}


def _resolve_oracle_transcript(event: dict[str, Any], store: BioRealityStore | None = None) -> tuple[Path | None, str]:
    payload = event.get("payload") if isinstance(event.get("payload"), dict) else {}
    repo_root = SCRIPT_DIR.parent.parent
    lane = str(payload.get("lane") or event.get("source") or "")
    topic = str(payload.get("topic") or "")
    candidates: list[Path] = []
    for key in ("transcript_md", "transcript_jsonl"):
        value = payload.get(key)
        if isinstance(value, str) and value:
            path = Path(value)
            candidates.append(path if path.is_absolute() else repo_root / path)
    if lane and topic:
        base = _oracle_sessions_dir(store) if store is not None else SCRIPT_DIR / "state" / "oracle_sessions"
        lane_dir = base / lane
        stem_suffix = f"__{_safe_oracle_topic(topic)}"
        if lane_dir.exists():
            for suffix in (".md", ".jsonl"):
                matches = sorted(lane_dir.glob(f"*{stem_suffix}{suffix}"), reverse=True)
                candidates.extend(matches)
    for candidate in candidates:
        if candidate.exists() and candidate.is_file():
            try:
                rel = candidate.relative_to(repo_root).as_posix()
            except ValueError:
                rel = str(candidate)
            return candidate, rel
    return None, ""


def _backfill_oracle_consultation_events(store: BioRealityStore, events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    sessions_dir = _oracle_sessions_dir(store)
    if not sessions_dir.exists():
        return events
    existing_consumer_keys = {
        str(event.get("stable_event_key") or "")
        for event in events
        if str(event.get("event_kind") or "") == "oracle_consumer_dispatched"
    }
    existing_open_oracle = {
        _oracle_consumer_key(
            str((event.get("payload") if isinstance(event.get("payload"), dict) else {}).get("lane") or event.get("source") or ""),
            str((event.get("payload") if isinstance(event.get("payload"), dict) else {}).get("topic") or ""),
        )
        for event in events
        if str(event.get("event_kind") or "") == "oracle_consultation_completed"
        and str(event.get("status") or "open") == "open"
    }
    synthesized: list[dict[str, Any]] = []
    for jsonl_path in sorted(sessions_dir.glob("*/*.jsonl")):
        lane = jsonl_path.parent.name
        header = _parse_oracle_jsonl_header(jsonl_path)
        topic = str(header.get("topic") or "")
        if not topic:
            stem = jsonl_path.stem
            topic = stem.split("__", 1)[1] if "__" in stem else stem
        consumer_key = _oracle_consumer_key(lane, topic)
        if consumer_key in existing_consumer_keys or consumer_key in existing_open_oracle:
            continue
        md_path = jsonl_path.with_suffix(".md")
        payload = {
            "lane": lane,
            "topic": topic,
            "intended_claim_id": str(header.get("intended_claim_id") or ""),
            "conversation_id": header.get("conversation_id"),
            "turns": int(header.get("turn_count") or 0),
            "closed_reason": header.get("closed_reason"),
            "max_turns_reached": header.get("max_turns_reached"),
            "pdf_attached": bool(header.get("pdf_attached")),
            "pdf_skipped_reason": header.get("pdf_skipped_reason") or "",
            "judge_calls": int(header.get("judge_calls") or 0),
            "transcript_jsonl": str(jsonl_path),
            "transcript_md": str(md_path) if md_path.exists() else "",
            "backfilled": True,
        }
        synthesized.append(
            _event(
                "oracle_consultation_completed",
                lane,
                "oracle_consultation",
                _oracle_consultation_subject_id(lane, topic),
                str(header.get("closed_reason") or "oracle consultation transcript backfilled"),
                payload,
            )
        )
        existing_open_oracle.add(consumer_key)
    if not synthesized:
        return events
    return _dedup(events + synthesized, "event_id")


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
    events = _dedup(events, "event_id")
    return _backfill_oracle_consultation_events(store, events)


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
            append_task(event, "bio-data-fetcher", "fetch_curated_external_data", 96)
        elif kind == "phase_advance_proposed":
            append_task(event, "bio-planner", "draft_next_phase_claim_and_experiment", 70)
        elif kind == "claim_redesign_proposed":
            append_task(event, "bio-planner", "redesign_stuck_claim", 75)
        elif kind == "namecert_proposal_needed":
            append_task(event, "bio-namer", "draft_namecert_proposal", 60)
        elif kind == "oracle_consultation_completed":
            source = str(event.get("source") or "")
            if source == "bio-Plan":
                append_task(event, "bio-oracle-consumer", "consume_oracle_plan_consultation", 70)
            elif source == "bio-G":
                append_task(event, "bio-oracle-consumer", "consume_oracle_gate_consultation", 70)
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
    if agent_id == "bio-oracle-consumer":
        transcript_path, transcript_label = _resolve_oracle_transcript(event)
        if transcript_path is not None:
            try:
                transcript_text = transcript_path.read_text(encoding="utf-8")
            except OSError:
                transcript_text = ""
        else:
            transcript_text = ""
        if action == "consume_oracle_plan_consultation":
            schema = {
                "verdict": "proposed | needs_more_data | no_actionable_signal",
                "next_experiment": {
                    "claim_id": "...",
                    "hypothesis_level": "H0|H1|H2|...",
                    "statement": "...",
                    "experiment_id": "...",
                    "dependencies": ["..."],
                    "rationale": "...",
                },
                "rationale": "...",
                "risk_notes": "...",
            }
            target_lines = [
                "Action target:",
                "- Extract the SINGLE strongest next-experiment proposal from the multi-turn ChatGPT session.",
                "- If the transcript does not support a concrete next experiment, use verdict no_actionable_signal or needs_more_data.",
            ]
        else:
            schema = {
                "verdict": "refinement_proposed | carrier_ok | needs_more_data",
                "claim_id": "...",
                "refinement_diff": [{"field": "...", "from": "...", "to": "...", "reason": "..."}],
                "rationale": "...",
                "risk_notes": "...",
            }
            target_lines = [
                "Action target:",
                "- Extract concrete refinement proposals for the reviewed claim's BEDC carrier.",
                "- If the transcript mentions ANY dependency leak, kernel/bridge re-layering, label-readback distinction migration, REFINE_BEFORE_MINIMAL_PASS verdict, 'conditional pass / not strictly minimal', kernel-distinction reclassification, or a proposed alternate JSON form, treat that as verdict=refinement_proposed and produce a refinement_diff that captures the moves (e.g. {\"field\": \"distinctions[\\\"singleton label corner\\\"]\", \"from\": \"kernel\", \"to\": \"external_readback_distinctions\", \"reason\": \"label-dependent per ChatGPT review\"}).",
                "- Use verdict=carrier_ok ONLY when the transcript states explicitly that the current minimal form needs no changes and no fields should move between kernel/bridge/derived layers.",
                "- Use verdict=needs_more_data only if the transcript is empty, truncated, error, or otherwise contains no substantive review.",
            ]
        return "\n".join(
            [
                "You are a BioReality oracle-consumer agent inside the newmath repository.",
                f"Agent: {agent_id}",
                f"Mission: {agent['mission']}",
                f"Action: {action}",
                "",
                "Hard rules:",
                "- Use information from the transcript only. Do not add facts from your own training or outside knowledge.",
                "- Return exactly one JSON object matching the requested schema; no Markdown wrapper.",
                "- Do not edit files, do not run network tools, do not call oracle, and do not call codex recursively.",
                "- If the transcript is missing, empty, or inconclusive, return the non-actionable verdict for this action.",
                "",
                "Transcript path:",
                transcript_label or "<not found>",
                "",
                "Original trigger event payload:",
                payload,
                "",
                *target_lines,
                "",
                "Required JSON schema:",
                json.dumps(schema, ensure_ascii=False, indent=2),
                "",
                "Transcript markdown or jsonl content follows verbatim:",
                "```text",
                transcript_text,
                "```",
            ]
        )
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
    elif agent_id == "bio-data-fetcher":
        extra_rules = [
            "",
            "DATA FETCHER DISCIPLINE (hard rules for bio-data-fetcher):",
            "",
            "Allowed sources (公开 reality 信息, 无黑名单):",
            "- NCBI E-utilities REST (eutils.ncbi.nlm.nih.gov): CDS, RefSeq, transl_table",
            "- UniProt REST (rest.uniprot.org): protein and proteome metadata",
            "- Ensembl REST (rest.ensembl.org): genome and transcript annotations",
            "- gtRNAdb (gtrnadb.ucsc.edu): tRNA reference",
            "- ENA / EBI REST (ebi.ac.uk): nucleotide accessions",
            "- arXiv / bioRxiv (export.arxiv.org, api.biorxiv.org): preprint metadata and abstracts as reality input",
            "- Wikipedia / Wikidata API (en.wikipedia.org/api, www.wikidata.org/wiki/Special:EntityData/...): authoritative external curated names and IDs",
            "- GitHub API (api.github.com): authoritative reference repos for biological data formats / curated tables",
            "- Any other public, stable, machine-readable endpoint that returns JSON / XML / CSV / FASTA / GTF / GFF / RDF",
            "",
            "Credential broker:",
            "- For any endpoint that needs an API key, OAuth token, GitHub token, or SSH key, use the nyxid CLI (see /nyxid skill): nyxid brokers credentials so the worker never sees the raw secret. Never inline API keys or tokens in code or commits.",
            "",
            "Source discipline (no blacklist; just rules):",
            "- Prefer REST / JSON over HTML scraping when both are available",
            "- HTML pages are allowed when they are the canonical curated source (e.g. NCBI Taxonomy genetic-code table HTML when no JSON equivalent), but parse defensively with stdlib html.parser",
            "- Reject and abort if response > 100 MB",
            "- urllib.request timeout=60s; set User-Agent to BioReality-data-fetcher/1.0",
            "",
            "Mandatory provenance for every fetched artifact:",
            "1. Save raw payload to tools/bio_reality/data/<source_name>_<accession_or_id>.json (or appropriate extension)",
            "2. Compute sha256 of the raw response bytes",
            "3. Save provenance to tools/bio_reality/data/manifests/<basename>.json with:",
            "   {",
            '     "fetched_at": "<iso-utc>",',
            '     "source_url": "<exact URL queried>",',
            '     "source_name": "ncbi|uniprot|ensembl|gtrnadb|ena|arxiv|biorxiv|wikipedia|wikidata|github|other",',
            '     "accession_or_id": "<...>",',
            '     "sha256": "<hex>",',
            '     "byte_size": <int>,',
            '     "content_type": "<HTTP Content-Type>",',
            '     "fetched_by": "bio-data-fetcher",',
            '     "intended_claim_id": "<claim_id from event>",',
            '     "license_or_terms": "<short summary of source terms if applicable>"',
            "   }",
            "",
            "Mandatory pre-fetch steps:",
            "- Inspect event payload to learn which claim's needs_data triggered this. Read tools/bio_reality/registries/claims.json to find the claim; read tools/bio_reality/registries/experiments.json to find required_data list for the experiment.",
            "- For each missing required_data file, decide which source provides it. Multiple sources are fine; cross-checking is encouraged.",
            "- If no suitable public source is reachable (private DB, paywall, custom dataset), write the diagnosis to tools/bio_reality/state/proposed_data_sources/<claim_id>.md and STOP.",
            "",
            "Mandatory post-fetch BEDC processing chain (this is the **core** discipline):",
            "- Fetching alone is not the goal; the goal is BEDC writeback. After data lands you must:",
            "  1. Re-run the claim's experiment via python3 <script_path>. If status changes to passed / failed (not needs_data), the data is functional.",
            "  2. If the experiment yields new structural information (carriers, distinctions, closure facts, spectrum, statistics), make sure the verified_facts pipeline can pick them up — bio-N will link the claim to a conjecture in the next cycle and copy the run values into conjecture.verified_facts.",
            "  3. The downstream BEDC chain (bio-N → bio-namer → bio-B) will then decompose the new fact into a minimal BEDC NameCert packet and write it back to papers/bedc/parts/concrete_instances/ with the strict gate set. You do NOT do that yourself, but you must leave the data + experiment_run in a shape that those lanes can consume.",
            "  4. If the experiment still needs_data after the fetch, the fetch did not solve the gap. Delete the JSON file you wrote, remove the manifest, and write a precise diagnosis to state/proposed_data_sources/<claim_id>.md.",
            "",
            "BEDC methodology reminder (apply to every fetched artifact):",
            "- External reality data is INPUT, not BEDC kernel content. It belongs in bridge / provenance fields, never in kernel derivations.",
            "- The downstream packet must keep curated reality and internal BEDC structure separated; the data file path must never appear inside paper kernel prose.",
            "- Minimum formalizable unit means: one carrier, one distinct readback, one falsifiable boundary, one cannot-claim row. Anything richer than that becomes a follow-up packet, not a single overloaded chapter.",
            "",
            "Strict no-go:",
            "- Never write any .py file outside tools/bio_reality/data/",
            "- Never modify experiment scripts (bio-experimentalist's job)",
            "- Never modify claims.json or experiments.json (bio-planner's job)",
            "- Never write Lean code or Lean markers (Lean is a separate downstream pipeline)",
            "- Never commit; the orchestrator owns commits",
            "- Never fabricate data when no source is available — write a proposed_data_sources note instead",
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
            *ORACLE_ESCALATION_RULES,
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
            *ORACLE_ESCALATION_RULES,
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
                        part_text = part.get("text")
                        if isinstance(part_text, str) and part_text.strip():
                            texts.append(part_text)
            elif isinstance(content, str) and content.strip():
                texts.append(content)
        delta = event.get("delta")
        if isinstance(delta, str) and delta.strip():
            texts.append(delta)
    return texts[-1] if texts else stdout


def _extract_json_object_from_text(text: str) -> dict[str, Any] | None:
    stripped = text.strip()
    candidates: list[str] = []
    for match in re.finditer(r"```(?:json)?\s*(\{.*?\})\s*```", stripped, re.DOTALL | re.IGNORECASE):
        candidates.append(match.group(1))
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


def _parse_oracle_consumer_result(stdout: str) -> dict[str, Any] | None:
    return _extract_json_object_from_text(_extract_codex_event_text(stdout or ""))


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
    if task.get("agent_id") == "bio-oracle-consumer":
        try:
            result = subprocess.run(
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
                input=str(task.get("prompt") or ""),
                text=True,
                capture_output=True,
                check=False,
                timeout=3600,
            )
            parsed = _parse_oracle_consumer_result(result.stdout or "")
            dispatch = {
                "task_id": task["task_id"],
                "dispatch_status": "completed" if result.returncode == 0 and parsed is not None else "failed",
                "returncode": result.returncode,
                "stdout_tail": result.stdout[-2000:],
                "stderr_tail": result.stderr[-2000:],
            }
            if parsed is not None:
                dispatch["result"] = parsed
            else:
                _append_stderr_tail(dispatch, "oracle consumer returned no parseable JSON object")
        except (OSError, subprocess.TimeoutExpired) as exc:
            dispatch = {
                "task_id": task["task_id"],
                "dispatch_status": "failed",
                "returncode": None,
                "stdout_tail": "",
                "stderr_tail": str(exc),
            }
        changed_paths = _paths_changed_since(before_status, _git_status(repo_root))
        violations = [path for path in changed_paths if not _allowed_path(path, allowed_writes)]
        if violations:
            _revert_paths(repo_root, violations)
            dispatch["dispatch_status"] = "write_path_violation"
            _append_stderr_tail(dispatch, "write_path_violation: " + ", ".join(violations))
        return dispatch
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


def _next_phase_from_claims(claims: list[dict[str, Any]]) -> int:
    phases: list[int] = []
    for claim in claims:
        try:
            phases.append(int(claim.get("phase")))
        except (TypeError, ValueError):
            continue
    return (max(phases) + 1) if phases else 1


def _next_phase_for_oracle_proposal(event: dict[str, Any], claims: list[dict[str, Any]]) -> int:
    payload = event.get("payload") if isinstance(event.get("payload"), dict) else {}
    for value in (payload.get("phase"),):
        try:
            return int(value)
        except (TypeError, ValueError):
            continue
    topic = str(payload.get("topic") or "")
    match = re.search(r"\.phase\.([0-9]+)\.next(?:$|\.)", topic)
    if match:
        return int(match.group(1))
    return _next_phase_from_claims(claims)


def _append_or_replace_by_key(items: list[dict[str, Any]], key: str, item: dict[str, Any]) -> None:
    value = str(item.get(key) or "")
    for index, existing in enumerate(items):
        if str(existing.get(key) or "") == value:
            items[index] = {**existing, **item}
            return
    items.append(item)


def _landing_log_event(task: dict[str, Any], event: dict[str, Any], verdict: str, reason: str, payload: dict[str, Any]) -> dict[str, Any]:
    base = {
        "task_id": task.get("task_id"),
        "event_id": event.get("event_id"),
        "verdict": verdict,
        "reason": reason,
    }
    return {
        "event_id": stable_id("event", {"event_kind": "oracle_consultation_reviewed", **base}),
        "created_at": now_iso(),
        "status": "consumed",
        "stable_event_key": _stable_event_key("oracle_consultation_reviewed", "agent_task", str(task.get("task_id") or "")),
        "event_kind": "oracle_consultation_reviewed",
        "source": "bio-oracle-consumer",
        "subject_kind": "agent_task",
        "subject_id": str(task.get("task_id") or ""),
        "reason": reason,
        "payload": payload,
    }


def _apply_oracle_plan_landing(
    store: BioRealityStore,
    task: dict[str, Any],
    event: dict[str, Any],
    result: dict[str, Any],
) -> dict[str, Any]:
    verdict = str(result.get("verdict") or "")
    if verdict != "proposed":
        return {
            "applied": False,
            "event": _landing_log_event(task, event, verdict, "oracle plan consultation reviewed; no action taken", {"oracle_result": result}),
        }
    next_experiment = result.get("next_experiment") if isinstance(result.get("next_experiment"), dict) else {}
    claim_id = str(next_experiment.get("claim_id") or "")
    experiment_id = str(next_experiment.get("experiment_id") or "")
    if not claim_id or not experiment_id:
        return {
            "applied": False,
            "event": _landing_log_event(task, event, verdict, "oracle plan proposal missing claim_id or experiment_id", {"oracle_result": result}),
        }
    claims_document = _load_claims_document(store.paths.claims_registry)
    experiments_document = _load_experiments_document(store.paths.experiments_registry)
    claims = [item for item in claims_document.get("claims", []) if isinstance(item, dict)]
    experiments = [item for item in experiments_document.get("experiments", []) if isinstance(item, dict)]
    phase = _next_phase_for_oracle_proposal(event, claims)
    claim_record = {
        "claim_id": claim_id,
        "hypothesis_level": str(next_experiment.get("hypothesis_level") or ""),
        "phase": phase,
        "statement": str(next_experiment.get("statement") or ""),
        "depends_on": [str(item) for item in next_experiment.get("dependencies", []) if isinstance(item, str)],
        "status": "open",
        "experiment_id": experiment_id,
        "history": [
            {
                "ts": now_iso(),
                "status": "open",
                "reason": "proposed_by_oracle",
                "source_event_id": event.get("event_id"),
            }
        ],
    }
    experiment_record = {
        **next_experiment,
        "experiment_id": experiment_id,
        "claim_id": claim_id,
        "status": "proposed_by_oracle",
        "proposal_rationale": str(next_experiment.get("rationale") or result.get("rationale") or ""),
        "proposed_by": "bio-oracle-consumer",
        "source_event_id": event.get("event_id"),
        "created_at": now_iso(),
    }
    _append_or_replace_by_key(claims, "claim_id", claim_record)
    _append_or_replace_by_key(experiments, "experiment_id", experiment_record)
    claims_document["claims"] = claims
    experiments_document["experiments"] = experiments
    _write_json_object(store.paths.claims_registry, claims_document)
    _write_json_object(store.paths.experiments_registry, experiments_document)
    return {
        "applied": True,
        "event": _landing_log_event(
            task,
            event,
            verdict,
            "oracle plan consultation produced next experiment proposal",
            {"claim_id": claim_id, "experiment_id": experiment_id, "oracle_result": result},
        ),
    }


def _safe_file_token(value: str) -> str:
    token = re.sub(r"[^A-Za-z0-9._-]+", "-", value.strip()).strip("-._")
    return token or "claim"


def _apply_oracle_gate_landing(
    store: BioRealityStore,
    task: dict[str, Any],
    event: dict[str, Any],
    result: dict[str, Any],
) -> dict[str, Any]:
    verdict = str(result.get("verdict") or "")
    if verdict != "refinement_proposed":
        return {
            "applied": False,
            "event": _landing_log_event(task, event, verdict, "oracle gate consultation reviewed; no action taken", {"oracle_result": result}),
        }
    payload = event.get("payload") if isinstance(event.get("payload"), dict) else {}
    claim_id = str(result.get("claim_id") or payload.get("intended_claim_id") or event.get("subject_id") or "")
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    refinement = {
        "created_at": now_iso(),
        "claim_id": claim_id,
        "source_event_id": event.get("event_id"),
        "source_task_id": task.get("task_id"),
        "refinement_diff": result.get("refinement_diff") if isinstance(result.get("refinement_diff"), list) else [],
        "rationale": str(result.get("rationale") or ""),
        "risk_notes": str(result.get("risk_notes") or ""),
    }
    path = _oracle_refinements_dir(store) / f"{_safe_file_token(claim_id)}__{timestamp}.json"
    _write_json_object(path, refinement)
    refinement_event = _event(
        "oracle_refinement_proposed",
        "bio-oracle-consumer",
        "claim",
        claim_id,
        "oracle gate consultation proposed carrier refinement",
        {"claim_id": claim_id, "refinement_path": str(path), "source_event_id": event.get("event_id")},
    )
    return {
        "applied": True,
        "event": refinement_event,
        "review_event": _landing_log_event(
            task,
            event,
            verdict,
            "oracle gate consultation produced carrier refinement proposal",
            {"claim_id": claim_id, "refinement_path": str(path), "oracle_result": result},
        ),
    }


def apply_oracle_consumer_landings(
    store: BioRealityStore,
    events: list[dict[str, Any]],
    tasks: list[dict[str, Any]],
    dispatches: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    event_by_id = {str(event.get("event_id") or ""): event for event in events}
    task_by_id = {str(task.get("task_id") or ""): task for task in tasks}
    new_events: list[dict[str, Any]] = []
    for dispatch in dispatches:
        if str(dispatch.get("dispatch_status") or "") != "completed":
            continue
        task = task_by_id.get(str(dispatch.get("task_id") or ""))
        if not task or str(task.get("agent_id") or "") != "bio-oracle-consumer":
            continue
        event = event_by_id.get(str(task.get("event_id") or ""))
        result = dispatch.get("result") if isinstance(dispatch.get("result"), dict) else None
        if event is None or result is None:
            continue
        consumer_event = {
            "event_id": stable_id("event", {"event_kind": "oracle_consumer_dispatched", "task_id": task.get("task_id")}),
            "created_at": now_iso(),
            "status": "consumed",
            "stable_event_key": _oracle_consumer_key(
                str((event.get("payload") if isinstance(event.get("payload"), dict) else {}).get("lane") or event.get("source") or ""),
                str((event.get("payload") if isinstance(event.get("payload"), dict) else {}).get("topic") or ""),
            ),
            "event_kind": "oracle_consumer_dispatched",
            "source": "bio-oracle-consumer",
            "subject_kind": "oracle_consultation",
            "subject_id": str(event.get("subject_id") or ""),
            "reason": "oracle consultation dispatched to consumer",
            "payload": {"source_event_id": event.get("event_id"), "task_id": task.get("task_id"), "action": task.get("action")},
        }
        new_events.append(consumer_event)
        action = str(task.get("action") or "")
        if action == "consume_oracle_plan_consultation":
            applied = _apply_oracle_plan_landing(store, task, event, result)
        elif action == "consume_oracle_gate_consultation":
            applied = _apply_oracle_gate_landing(store, task, event, result)
        else:
            continue
        for key in ("event", "review_event"):
            value = applied.get(key)
            if isinstance(value, dict):
                new_events.append(value)
    return _dedup(events + new_events, "event_id")


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
    events = apply_oracle_consumer_landings(store, events, tasks, dispatches)
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
        data_fetch_tasks = plan_agent_tasks(
            [
                _event(
                    "data_contact_needed",
                    "bio-X",
                    "experiment",
                    "self_experiment",
                    "experiment needs data: self.claim",
                    {"claim_id": "self.claim", "experiment_id": "self_experiment", "status": "needs_data"},
                )
            ]
        )
        data_fetch_task = next((task for task in data_fetch_tasks if task.get("agent_id") == "bio-data-fetcher"), {})
        if (
            data_fetch_task.get("action") != "fetch_curated_external_data"
            or int(data_fetch_task.get("priority") or 0) != 96
        ):
            print(json.dumps(data_fetch_tasks, indent=2), file=sys.stderr)
            return 1
        oracle_plan_event = _event(
            "oracle_consultation_completed",
            "bio-Plan",
            "oracle_consultation",
            _oracle_consultation_subject_id("bio-Plan", "bio-Plan.phase.2.next"),
            "oracle consultation completed",
            {"lane": "bio-Plan", "topic": "bio-Plan.phase.2.next", "intended_claim_id": ""},
        )
        oracle_gate_event = _event(
            "oracle_consultation_completed",
            "bio-G",
            "oracle_consultation",
            _oracle_consultation_subject_id("bio-G", "bio-G.review.self.claim"),
            "oracle consultation completed",
            {"lane": "bio-G", "topic": "bio-G.review.self.claim", "intended_claim_id": "self.claim"},
        )
        oracle_tasks = plan_agent_tasks([oracle_plan_event, oracle_gate_event])
        oracle_by_action = {
            str(task.get("action") or ""): task
            for task in oracle_tasks
        }
        if (
            oracle_by_action.get("consume_oracle_plan_consultation", {}).get("agent_id") != "bio-oracle-consumer"
            or int(oracle_by_action.get("consume_oracle_plan_consultation", {}).get("priority") or 0) != 70
            or oracle_by_action.get("consume_oracle_gate_consultation", {}).get("agent_id") != "bio-oracle-consumer"
            or int(oracle_by_action.get("consume_oracle_gate_consultation", {}).get("priority") or 0) != 70
        ):
            print(json.dumps(oracle_tasks, indent=2), file=sys.stderr)
            return 1
        data_fetch_prompt = render_prompt(
            _event(
                "data_contact_needed",
                "bio-X",
                "experiment",
                "self_experiment",
                "experiment needs data: self.claim",
                {"claim_id": "self.claim", "experiment_id": "self_experiment", "status": "needs_data"},
            ),
            "bio-data-fetcher",
            "fetch_curated_external_data",
        )
        for required_text in (
            "DATA FETCHER DISCIPLINE",
            "Allowed sources",
            "Mandatory provenance",
            "Never write Lean code",
            "nyxid",
            "Mandatory post-fetch BEDC processing chain",
        ):
            if required_text not in data_fetch_prompt:
                print(json.dumps({"missing": required_text, "prompt": data_fetch_prompt}, indent=2), file=sys.stderr)
                return 1
        planner_prompt = render_prompt(
            _event("phase_advance_proposed", "bio-Plan", "phase", "1", "phase passed", {}),
            "bio-planner",
            "draft_next_phase_claim_and_experiment",
        )
        for required_text in (
            "PLANNING DISCIPLINE",
            "depends_on must list ONLY",
            "never weaken the acceptance",
            "ORACLE ESCALATION",
        ):
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
        for required_text in (
            "NAMECERT PROPOSAL DISCIPLINE",
            "BioReality or RealityBound",
            "vision-level scientific-model bridge",
            "ORACLE ESCALATION",
        ):
            if required_text not in namer_prompt:
                print(json.dumps({"missing": required_text, "prompt": namer_prompt}, indent=2), file=sys.stderr)
                return 1
        stable_event = _event("experiment_failed", "bio-X", "experiment", "same-experiment", "failed", {})
        for mechanical_agent in ("bio-experimentalist", "bio-data-fetcher", "bio-gate-curator", "bio-researcher"):
            mechanical_prompt = render_prompt(stable_event, mechanical_agent, "self_test_action")
            if "ORACLE ESCALATION" in mechanical_prompt:
                print(json.dumps({"unexpected_oracle": mechanical_agent}, indent=2), file=sys.stderr)
                return 1
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
        oracle_base = base / "oracle_case"
        oracle_paths = BioRealityPaths(
            root=SCRIPT_DIR,
            gate_results=oracle_base / "out" / "gate_results.jsonl",
            deepening_tasks=oracle_base / "out" / "deepening_tasks.jsonl",
            events=oracle_base / "out" / "events.jsonl",
            agent_tasks=oracle_base / "out" / "agent_tasks.jsonl",
            agent_reviews=oracle_base / "out" / "agent_reviews.jsonl",
            agent_reviews_archive=oracle_base / "out" / "agent_reviews.archive.jsonl",
            dispatch_results=oracle_base / "out" / "dispatch_results.jsonl",
            dispatch_results_archive=oracle_base / "out" / "dispatch_results.archive.jsonl",
            hardening_targets=oracle_base / "out" / "hardening_targets.jsonl",
            claims_registry=oracle_base / "registries" / "claims.json",
            experiments_registry=oracle_base / "registries" / "experiments.json",
            experiment_runs=oracle_base / "state" / "experiment_runs.jsonl",
        )
        _write_json_object(
            oracle_paths.claims_registry,
            {
                "version": "bio-reality-claims-v1",
                "claims": [
                    {
                        "claim_id": "h0.seed",
                        "hypothesis_level": "H0",
                        "phase": 1,
                        "statement": "seed claim",
                        "depends_on": [],
                        "status": "passed",
                        "experiment_id": "seed_experiment",
                    }
                ],
            },
        )
        _write_json_object(
            oracle_paths.experiments_registry,
            {
                "version": "bio-reality-experiments-v1",
                "experiments": [
                    {
                        "experiment_id": "seed_experiment",
                        "claim_id": "h0.seed",
                        "required_data": [],
                    }
                ],
            },
        )
        oracle_store = BioRealityStore(oracle_paths)
        session_dir = oracle_base / "state" / "oracle_sessions" / "bio-Plan"
        session_dir.mkdir(parents=True, exist_ok=True)
        topic = "bio-Plan.phase.2.next"
        transcript_jsonl = session_dir / f"20260525T000000Z__{_safe_oracle_topic(topic)}.jsonl"
        transcript_md = transcript_jsonl.with_suffix(".md")
        write_jsonl(
            transcript_jsonl,
            [
                {
                    "record_kind": "session",
                    "lane": "bio-Plan",
                    "topic": topic,
                    "conversation_id": "conv-self-test",
                    "closed_reason": "done",
                    "max_turns_reached": False,
                    "turn_count": 1,
                },
                {
                    "record_kind": "turn",
                    "turn": 1,
                    "prompt": "next experiment?",
                    "result": {"response": "The strongest next experiment is h1.oracle.next."},
                },
            ],
        )
        transcript_md.write_text(
            "\n".join(
                [
                    "# Oracle consultation: bio-Plan.phase.2.next",
                    "",
                    "Transcript says the strongest next experiment is h1.oracle.next.",
                ]
            ),
            encoding="utf-8",
        )
        oracle_event = _event(
            "oracle_consultation_completed",
            "bio-Plan",
            "oracle_consultation",
            _oracle_consultation_subject_id("bio-Plan", topic),
            "done",
            {
                "lane": "bio-Plan",
                "topic": topic,
                "intended_claim_id": "",
                "conversation_id": "conv-self-test",
                "turns": 1,
                "closed_reason": "done",
                "max_turns_reached": False,
                "transcript_jsonl": str(transcript_jsonl),
                "transcript_md": str(transcript_md),
            },
        )
        oracle_store.write_events([oracle_event])
        oracle_prompt = render_prompt(oracle_event, "bio-oracle-consumer", "consume_oracle_plan_consultation")
        for required_text in (
            "Use information from the transcript only",
            "SINGLE strongest next-experiment proposal",
            "h1.oracle.next",
            "Required JSON schema",
        ):
            if required_text not in oracle_prompt:
                print(json.dumps({"missing": required_text, "prompt": oracle_prompt}, indent=2), file=sys.stderr)
                return 1
        original_subprocess_run = subprocess.run

        def fake_subprocess_run(*args: Any, **kwargs: Any) -> subprocess.CompletedProcess[str]:
            cmd = args[0] if args else kwargs.get("args")
            if isinstance(cmd, list) and cmd[:2] == ["codex", "exec"]:
                if "--sandbox" not in cmd or "read-only" not in cmd or "--json" not in cmd or cmd[-1] != "-":
                    return subprocess.CompletedProcess(cmd, 2, "", "bad codex invocation")
                stdout = json.dumps(
                    {
                        "verdict": "proposed",
                        "next_experiment": {
                            "claim_id": "h1.oracle.next",
                            "hypothesis_level": "H1",
                            "statement": "Oracle transcript proposes a stronger phase-two measurement.",
                            "experiment_id": "oracle_next_experiment",
                            "dependencies": ["h0.seed"],
                            "rationale": "Selected from transcript.",
                        },
                        "rationale": "Transcript-supported proposal.",
                        "risk_notes": "self-test only",
                    },
                    ensure_ascii=False,
                )
                return subprocess.CompletedProcess(cmd, 0, stdout, "")
            return original_subprocess_run(*args, **kwargs)

        try:
            subprocess.run = fake_subprocess_run
            oracle_agent = run_agent_lane(oracle_store, execute_codex=True, max_dispatch=1)
            oracle_tasks_after = oracle_store.load_agent_tasks()
            oracle_task_after = next((task for task in oracle_tasks_after if task.get("agent_id") == "bio-oracle-consumer"), {})
            claims_after = _load_claims_document(oracle_paths.claims_registry).get("claims", [])
            experiments_after = _load_experiments_document(oracle_paths.experiments_registry).get("experiments", [])
            events_after = oracle_store.load_events()
            if (
                oracle_agent.get("dispatch_completed") != 1
                or oracle_task_after.get("action") != "consume_oracle_plan_consultation"
                or oracle_task_after.get("status") != "completed"
                or not any(isinstance(claim, dict) and claim.get("claim_id") == "h1.oracle.next" and claim.get("status") == "open" for claim in claims_after)
                or not any(isinstance(experiment, dict) and experiment.get("experiment_id") == "oracle_next_experiment" and experiment.get("status") == "proposed_by_oracle" for experiment in experiments_after)
                or not any(event.get("event_kind") == "oracle_consumer_dispatched" for event in events_after)
                or next((event for event in events_after if event.get("event_id") == oracle_event.get("event_id")), {}).get("status") != "consumed"
            ):
                print(
                    json.dumps(
                        {
                            "agent": oracle_agent,
                            "tasks": oracle_tasks_after,
                            "claims": claims_after,
                            "experiments": experiments_after,
                            "events": events_after,
                        },
                        indent=2,
                        ensure_ascii=False,
                    ),
                    file=sys.stderr,
                )
                return 1
            oracle_agent_repeat = run_agent_lane(oracle_store, execute_codex=True, max_dispatch=1)
            repeat_tasks = oracle_store.load_agent_tasks()
            consumer_tasks = [task for task in repeat_tasks if task.get("agent_id") == "bio-oracle-consumer"]
            if oracle_agent_repeat.get("dispatches") != 0 or len(consumer_tasks) != 1:
                print(json.dumps({"repeat": oracle_agent_repeat, "tasks": repeat_tasks}, indent=2), file=sys.stderr)
                return 1
        finally:
            subprocess.run = original_subprocess_run
        backfill_base = base / "oracle_backfill"
        backfill_paths = BioRealityPaths(
            root=SCRIPT_DIR,
            gate_results=backfill_base / "out" / "gate_results.jsonl",
            deepening_tasks=backfill_base / "out" / "deepening_tasks.jsonl",
            events=backfill_base / "out" / "events.jsonl",
            agent_tasks=backfill_base / "out" / "agent_tasks.jsonl",
            agent_reviews=backfill_base / "out" / "agent_reviews.jsonl",
            agent_reviews_archive=backfill_base / "out" / "agent_reviews.archive.jsonl",
            dispatch_results=backfill_base / "out" / "dispatch_results.jsonl",
            dispatch_results_archive=backfill_base / "out" / "dispatch_results.archive.jsonl",
            hardening_targets=backfill_base / "out" / "hardening_targets.jsonl",
            claims_registry=backfill_base / "claims.json",
            experiments_registry=backfill_base / "experiments.json",
            experiment_runs=backfill_base / "experiment_runs.jsonl",
        )
        backfill_session_dir = backfill_base / "state" / "oracle_sessions" / "bio-G"
        backfill_session_dir.mkdir(parents=True, exist_ok=True)
        backfill_topic = "bio-G.review.backfill.claim"
        backfill_jsonl = backfill_session_dir / f"20260525T000001Z__{_safe_oracle_topic(backfill_topic)}.jsonl"
        write_jsonl(
            backfill_jsonl,
            [
                {
                    "record_kind": "session",
                    "lane": "bio-G",
                    "topic": backfill_topic,
                    "conversation_id": "conv-backfill",
                    "closed_reason": "done",
                    "turn_count": 1,
                }
            ],
        )
        backfilled_events = build_events(BioRealityStore(backfill_paths))
        if not any(
            event.get("event_kind") == "oracle_consultation_completed"
            and event.get("source") == "bio-G"
            and (event.get("payload") if isinstance(event.get("payload"), dict) else {}).get("backfilled") is True
            for event in backfilled_events
        ):
            print(json.dumps(backfilled_events, indent=2), file=sys.stderr)
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

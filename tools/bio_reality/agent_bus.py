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
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def stable_id(prefix: str, payload: dict[str, Any]) -> str:
    material = json.dumps(payload, sort_keys=True, ensure_ascii=True)
    digest = hashlib.sha256(material.encode("utf-8")).hexdigest()[:16]
    return f"{prefix}.{digest}"


def _dedup(records: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for record in records:
        value = str(record.get(key) or stable_id(key, record))
        if value in seen:
            continue
        seen.add(value)
        out.append(record)
    return out


def _normalize_event(event: dict[str, Any]) -> dict[str, Any]:
    normalized = dict(event)
    status = str(normalized.get("status") or "open")
    normalized["status"] = status if status in EVENT_STATUSES else "open"
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
        **base,
    }


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
    return _dedup(events, "event_id")


def _task_for_event(event: dict[str, Any], agent_id: str, action: str, priority: int) -> dict[str, Any]:
    agent = AGENTS[agent_id]
    base = {
        "agent_id": agent_id,
        "event_id": event["event_id"],
        "action": action,
        "subject_kind": event["subject_kind"],
        "subject_id": event["subject_id"],
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
        "action": action,
        "reason": event["reason"],
        "allowed_writes": agent["writes"],
        "prompt": render_prompt(event, agent_id, action),
    }


def plan_agent_tasks(events: list[dict[str, Any]]) -> list[dict[str, Any]]:
    tasks: list[dict[str, Any]] = []
    for event in events:
        if str(event.get("status") or "open") != "open":
            continue
        kind = str(event.get("event_kind") or "")
        if kind == "research_deepening_needed":
            tasks.append(_task_for_event(event, "bio-researcher", "extend_research_memory", 90))
        elif kind == "research_review_ready":
            tasks.append(_task_for_event(event, "bio-researcher", "seek_next_reality_boundary", 40))
        elif kind == "vision_ready":
            tasks.append(_task_for_event(event, "bio-researcher", "materialize_vision_into_research_memory", 100))
        elif kind == "vision_blocked":
            tasks.append(_task_for_event(event, "bio-gate-curator", "harden_vision_intake_or_dependencies", 80))
        elif kind == "gate_failure":
            tasks.append(_task_for_event(event, "bio-gate-curator", "harden_gate_or_schema", 95))
    tasks.sort(key=_status_sort)
    return _dedup(tasks, "task_id")


def merge_agent_tasks(existing: list[dict[str, Any]], planned: list[dict[str, Any]]) -> list[dict[str, Any]]:
    task_by_id: dict[str, dict[str, Any]] = {}
    order: list[str] = []
    planned_event_ids = {str(task.get("event_id") or "") for task in planned}
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
            if str(merged.get("status") or "") == "failed" and str(merged.get("event_id") or "") in planned_event_ids:
                merged["status"] = "queued"
            task_by_id[task_id] = _normalize_task(merged)
        else:
            order.append(task_id)
            task_by_id[task_id] = normalized
    return sorted((task_by_id[task_id] for task_id in order), key=_status_sort)


def render_prompt(event: dict[str, Any], agent_id: str, action: str) -> str:
    agent = AGENTS[agent_id]
    payload = json.dumps(event, ensure_ascii=False, sort_keys=True, indent=2)
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
    planned_tasks = plan_agent_tasks(events)
    tasks = merge_agent_tasks(store.load_agent_tasks(), planned_tasks)
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
        store = BioRealityStore(paths)
        agent = run_agent_lane(store, execute_codex=False)
        quality = run_quality_lane(store)
        if agent["events"] != 2 or agent["agent_tasks"] != 2:
            print(json.dumps(agent, indent=2), file=sys.stderr)
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

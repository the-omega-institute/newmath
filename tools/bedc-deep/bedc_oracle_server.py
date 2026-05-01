#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BEDC Oracle bridge server — multi-turn deep reasoning for BEDC targets.

Forked from tools/chatgpt-oracle/oracle_server.py and adapted for follow-up
questions. The paper-review oracle is single-shot: each task_id is independent.
The BEDC oracle supports a *session* (= one ChatGPT conversation) into which
multiple follow-up prompts can be threaded — the userscript navigates to the
existing chat URL and posts the next prompt in the same conversation.

Differences vs the paper oracle:
  - Port 8767 (paper oracle is 8765). Run them side by side.
  - Task payload accepts `conversation_id` and `conversation_url`. When set, the
    userscript MUST navigate to that URL and post as a follow-up there.
  - After each turn, the userscript POSTs back the chat URL it landed on. The
    server stores it on the session so subsequent turns reuse the same chat.
  - Sessions persist to disk at tools/bedc-deep/bedc_oracle/sessions/
    so server restart doesn't lose the conversation thread.
  - No PDF support (BEDC claim-packet reviews work on inline research.md text); kept as
    optional pass-through if ever needed later.

Usage:
    python3 tools/bedc-deep/bedc_oracle_server.py

    # Open ChatGPT.com tab(s) with bedc_oracle_macos.user.js installed,
    # set ACTIVE in the panel, server will dispatch tasks.

Hard rules:
  - Server never speaks to chatgpt.com directly. The userscript is the only
    code that touches the model.
  - Server never auto-publishes anything. Results land in sessions/ and are
    consumed by tools/bedc-deep/oracle_client.py state JSON.
"""

from __future__ import annotations

import base64
import json
import re
import sys
import threading
import time
import uuid
from http.server import HTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from datetime import datetime, timezone
from collections import deque
from urllib.parse import urlparse, parse_qs

PORT = 8767
ORACLE_DIR = Path(__file__).parent / "bedc_oracle"
SESSIONS_DIR = ORACLE_DIR / "sessions"
RESULTS_DIR = ORACLE_DIR / "results"

MAX_AGENTS = 3
TASK_TIMEOUT = 14400  # 4 hours; ChatGPT Pro thinking can be 60+ min/turn
AGENT_RECENT_SECONDS = 120
SESSION_IDLE_RETENTION = 14 * 24 * 3600  # keep sessions on disk for 14 days

# In-memory state (durable copy on disk)
task_queue: deque[dict] = deque()
results: dict[str, dict] = {}             # task_id -> result record
pending_tasks: dict[str, dict] = {}       # agent_id -> task currently in flight
dispatch_times: dict[str, float] = {}     # agent_id -> dispatch timestamp
recent_agents: dict[str, dict] = {}       # agent_id -> latest poll/ack/result
sessions: dict[str, dict] = {}            # conv_id -> session record
cancelled_tasks: set[str] = set()
_lock = threading.Lock()


# ---------------------------------------------------------------------------
# Session persistence
# ---------------------------------------------------------------------------


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _ensure_dirs() -> None:
    SESSIONS_DIR.mkdir(parents=True, exist_ok=True)
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)


def _session_path(conv_id: str) -> Path:
    return SESSIONS_DIR / f"{conv_id}.json"


def _load_session(conv_id: str) -> dict:
    p = _session_path(conv_id)
    if not p.exists():
        return {}
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _write_session(session: dict) -> None:
    conv_id = session.get("conversation_id")
    if not conv_id:
        return
    _session_path(conv_id).write_text(
        json.dumps(session, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def _hydrate_sessions() -> None:
    """Rebuild in-memory sessions dict from disk."""
    _ensure_dirs()
    for p in SESSIONS_DIR.glob("*.json"):
        try:
            sess = json.loads(p.read_text(encoding="utf-8"))
            cid = sess.get("conversation_id")
            if cid:
                sessions[cid] = sess
        except Exception:
            continue


def _new_conversation_id() -> str:
    # Server-issued ID. The chat URL captured later carries the ChatGPT-side
    # uuid; we keep our own for stable cross-restart referencing.
    return f"conv_{uuid.uuid4().hex[:16]}"


def _record_turn(conv_id: str, turn: dict) -> None:
    with _lock:
        sess = sessions.get(conv_id) or _load_session(conv_id) or {
            "conversation_id": conv_id,
            "created_at": _now(),
            "turns": [],
        }
        sess.setdefault("turns", []).append(turn)
        sess["updated_at"] = _now()
        if "chatgpt_url" in turn and turn["chatgpt_url"]:
            sess["chatgpt_url"] = turn["chatgpt_url"]
        sessions[conv_id] = sess
        _write_session(sess)


def _record_agent_seen(agent_id: str, *, event: str, metrics: dict | None = None) -> None:
    if not agent_id:
        return
    rec = {
        "agent_id": agent_id,
        "event": event,
        "last_seen": time.time(),
        "last_seen_at": _now(),
    }
    if metrics:
        rec["metrics"] = metrics
    recent_agents[agent_id] = rec


def _agent_summary(now: float) -> dict[str, dict]:
    summary: dict[str, dict] = {}
    for aid, rec in recent_agents.items():
        idle = int(now - float(rec.get("last_seen", now)))
        summary[aid] = {
            "event": rec.get("event", ""),
            "last_seen_at": rec.get("last_seen_at", ""),
            "idle_seconds": idle,
            "recent": idle <= AGENT_RECENT_SECONDS,
        }
        if isinstance(rec.get("metrics"), dict):
            summary[aid]["metrics"] = rec["metrics"]
    return summary


def _queued_summary(now: float) -> list[dict]:
    items: list[dict] = []
    for task in list(task_queue)[:10]:
        submitted_ts = float(task.get("submitted_ts", now))
        items.append({
            "task_id": task.get("task_id", ""),
            "conversation_id": task.get("conversation_id", ""),
            "tag": task.get("tag", ""),
            "age_seconds": int(now - submitted_ts),
            "prompt_chars": len(task.get("prompt", "")),
            "is_followup": bool(task.get("is_followup")),
        })
    return items


def _clean_response_text(text: str) -> str:
    cleaned = text or ""
    cleaned = re.sub(r"^\s*ChatGPT said:\s*", "", cleaned)
    cleaned = re.sub(r"\bThought for [0-9hm s]+", "", cleaned)
    cleaned = re.sub(r"\n?window\.__oai_logHTML\?.*\Z", "", cleaned, flags=re.DOTALL)
    cleaned = re.sub(r"\n?Extended Pro\s*ChatGPT can make mistakes\..*\Z", "", cleaned, flags=re.DOTALL)
    cleaned = re.sub(r"\n?ChatGPT can make mistakes\..*\Z", "", cleaned, flags=re.DOTALL)
    return cleaned.strip()


def _response_is_error(text: str) -> bool:
    return bool(re.match(r"\s*ERROR\b", text or "", re.IGNORECASE))


def _response_is_bedc_contaminated(text: str) -> bool:
    markers = (
        "Round 1: Discovery",
        "Candidate open problems",
        "Omega Project capability digest",
        "Survivors ranked",
        "TOP-3 picks for deep reasoning",
        "EXPECTED-PUBLICATION:",
    )
    return any(marker in (text or "") for marker in markers)


def _should_replace_result(existing: dict | None, response: str) -> bool:
    if not existing:
        return True
    old_response = existing.get("response", "")
    if _response_is_error(old_response) and not _response_is_error(response):
        return True
    if not _response_is_error(old_response) and _response_is_error(response):
        return False
    return len(response) >= len(old_response)


# ---------------------------------------------------------------------------
# HTTP handler
# ---------------------------------------------------------------------------


class BEDCOracleHandler(BaseHTTPRequestHandler):

    def log_message(self, fmt, *args):
        return  # silence default logging

    def _send_json(self, data: dict, status: int = 200):
        body = json.dumps(data, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self._send_json({})

    def _cleanup_stale(self):
        now = time.time()
        with _lock:
            stale = [aid for aid, t in dispatch_times.items()
                     if now - t > TASK_TIMEOUT and aid in pending_tasks]
            for aid in stale:
                task = pending_tasks.pop(aid)
                dispatch_times.pop(aid, None)
                task_queue.appendleft(task)
                print(f"[server] Agent {aid} timed out — task {task['task_id']} re-queued")

    def do_GET(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)

        if parsed.path == "/task":
            self._cleanup_stale()
            agent_id = (qs.get("agent", [None])[0]
                        or qs.get("agent_id", [None])[0]
                        or "default")
            poll_metrics = {
                "script_version": (qs.get("script_version", [""])[0] or ""),
                "page_url": (qs.get("page_url", [""])[0] or ""),
                "chatgpt_url": (qs.get("chatgpt_url", [""])[0] or ""),
            }
            with _lock:
                _record_agent_seen(agent_id, event="poll", metrics=poll_metrics)
                if agent_id in pending_tasks:
                    self._send_json(pending_tasks[agent_id])
                    return
                if task_queue and len(pending_tasks) < MAX_AGENTS:
                    task = task_queue.popleft()
                    task["assigned_agent"] = agent_id
                    pending_tasks[agent_id] = task
                    dispatch_times[agent_id] = time.time()
                    print(f"[server] Dispatched {task['task_id']} → {agent_id} "
                          f"(conv={task.get('conversation_id','-')[:12]} "
                          f"agents={len(pending_tasks)}/{MAX_AGENTS} "
                          f"queue={len(task_queue)})")
                    self._send_json(task)
                    return
                self._send_json({"status": "idle"})
            return

        if parsed.path == "/status":
            self._cleanup_stale()
            with _lock:
                now = time.time()
                agents_info = {
                    aid: {"task_id": t.get("task_id", "?"),
                          "conversation_id": t.get("conversation_id", ""),
                          "elapsed": int(time.time() - dispatch_times.get(aid, time.time()))}
                    for aid, t in pending_tasks.items()
                }
                recent = _agent_summary(now)
                active_recent = [aid for aid, rec in recent.items() if rec["recent"]]
                active_poll = [
                    aid for aid, rec in recent.items()
                    if rec["recent"] and rec.get("event") == "poll"
                ]
                stale_busy = [
                    aid for aid in pending_tasks
                    if not recent.get(aid, {}).get("recent", False)
                ]
                if task_queue and not pending_tasks and not active_poll:
                    diagnosis = "queue_waiting_for_browser_agent"
                elif pending_tasks:
                    diagnosis = "agent_busy_with_stale" if stale_busy else "agent_busy"
                elif task_queue:
                    diagnosis = "queue_waiting_for_free_agent"
                else:
                    diagnosis = "idle"
                self._send_json({
                    "queue_length": len(task_queue),
                    "queued_tasks": _queued_summary(now),
                    "agents_busy": len(pending_tasks),
                    "max_agents": MAX_AGENTS,
                    "agents": agents_info,
                    "recent_agents": recent,
                    "active_recent_agents": active_recent,
                    "active_poll_agents": active_poll,
                    "stale_busy_agents": stale_busy,
                    "agent_recent_seconds": AGENT_RECENT_SECONDS,
                    "completed": len(results),
                    "active_sessions": len(sessions),
                    "port": PORT,
                    "kind": "bedc-oracle",
                    "diagnosis": diagnosis,
                })
            return

        if parsed.path.startswith("/result/"):
            task_id = parsed.path[len("/result/"):]
            with _lock:
                rec = results.get(task_id)
            if rec:
                self._send_json(rec)
            else:
                self._send_json({"status": "not_found"}, 404)
            return

        if parsed.path.startswith("/session/"):
            conv_id = parsed.path[len("/session/"):]
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id)
            if sess:
                self._send_json(sess)
            else:
                self._send_json({"status": "not_found"}, 404)
            return

        if parsed.path == "/sessions":
            with _lock:
                summary = [
                    {
                        "conversation_id": s["conversation_id"],
                        "turns": len(s.get("turns", [])),
                        "updated_at": s.get("updated_at", ""),
                        "chatgpt_url": s.get("chatgpt_url", ""),
                        "tag": s.get("tag", ""),
                    }
                    for s in sessions.values()
                ]
            self._send_json({"sessions": sorted(summary, key=lambda x: x["updated_at"], reverse=True)})
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    def do_POST(self):
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode("utf-8") if length else ""
        try:
            data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            self._send_json({"error": "invalid JSON"}, 400)
            return

        if self.path == "/submit":
            self._handle_submit(data, is_continue=False)
            return
        if self.path == "/continue":
            self._handle_submit(data, is_continue=True)
            return
        if self.path == "/result":
            self._handle_result(data)
            return
        if self.path == "/ack":
            self._handle_ack(data)
            return
        if self.path == "/close":
            self._handle_close(data)
            return
        if self.path == "/retry":
            self._handle_retry(data)
            return
        if self.path == "/cancel":
            self._handle_cancel(data)
            return
        if self.path == "/pin-conv-url":
            self._handle_pin_conv_url(data)
            return

        self._send_json({"error": "unknown endpoint"}, 404)

    def _handle_submit(self, data: dict, *, is_continue: bool):
        prompt = data.get("prompt", "")
        if not prompt:
            self._send_json({"error": "prompt required"}, 400)
            return
        task_id = data.get("task_id") or f"bedc_{int(time.time())}_{uuid.uuid4().hex[:6]}"
        conv_id = data.get("conversation_id")
        if is_continue:
            if not conv_id:
                self._send_json({"error": "/continue requires conversation_id"}, 400)
                return
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id)
            if not sess:
                self._send_json({"error": f"unknown conversation_id {conv_id}"}, 404)
                return
            chatgpt_url = sess.get("chatgpt_url", "")
        else:
            if not conv_id:
                conv_id = _new_conversation_id()
            with _lock:
                sess = sessions.get(conv_id) or _load_session(conv_id) or {
                    "conversation_id": conv_id,
                    "created_at": _now(),
                    "turns": [],
                    "tag": data.get("tag", ""),
                }
                sessions[conv_id] = sess
                _write_session(sess)
            chatgpt_url = sess.get("chatgpt_url", "")

        task = {
            "task_id": task_id,
            "prompt": prompt,
            "conversation_id": conv_id,
            "conversation_url": chatgpt_url,
            "is_followup": bool(is_continue or chatgpt_url),
            "model": data.get("model", "chatgpt-5.5-pro"),
            "tag": data.get("tag", ""),
            "submitted_at": _now(),
            "submitted_ts": time.time(),
            "status": "queued",
        }
        with _lock:
            cancelled_tasks.discard(task_id)
        # Optional PDF passthrough, kept for forward compatibility.
        if "pdf_base64" in data:
            task["pdf_base64"] = data["pdf_base64"]
            task["pdf_name"] = data.get("pdf_name", "attachment.pdf")
        with _lock:
            task_queue.append(task)
        print(f"[server] {'CONT ' if is_continue else 'NEW  '}queued {task_id} "
              f"conv={conv_id[:12]} prompt={len(prompt)} chars "
              f"queue={len(task_queue)}")
        self._send_json({
            "status": "queued",
            "task_id": task_id,
            "conversation_id": conv_id,
            "queue_position": len(task_queue),
        })

    def _handle_result(self, data: dict):
        task_id = data.get("task_id", "")
        raw_response = data.get("response", "")
        response = _clean_response_text(raw_response)
        agent_id = data.get("agent_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        if not task_id or not response:
            self._send_json({"error": "task_id and response required"}, 400)
            return

        # Pull the matching pending task (carries our conversation_id)
        with _lock:
            task = None
            freed_agent = ""
            for aid in list(pending_tasks):
                if pending_tasks[aid].get("task_id") == task_id:
                    task = pending_tasks.pop(aid)
                    dispatch_times.pop(aid, None)
                    freed_agent = aid
                    break
            existing = results.get(task_id)
        if task is None and existing is None:
            print(f"[server] Ignored orphan result {task_id} ({len(response)} chars)")
            self._send_json({"status": "ignored_orphan", "task_id": task_id})
            return
        conv_id = (task or {}).get("conversation_id", "") or (existing or {}).get("conversation_id", "")
        if not chatgpt_url:
            chatgpt_url = (task or {}).get("conversation_url", "") or (existing or {}).get("chatgpt_url", "")
        if _response_is_bedc_contaminated(response):
            print(f"[server] Ignored contaminated result {task_id} ({len(response)} chars)")
            self._send_json({"status": "ignored_contaminated", "task_id": task_id})
            return

        record = {
            "task_id": task_id,
            "response": response,
            "conversation_id": conv_id,
            "chatgpt_url": chatgpt_url,
            "model": data.get("model", "chatgpt-5.5-pro"),
            "agent_id": agent_id,
            "script_version": data.get("script_version", ""),
            "page_url": data.get("page_url", ""),
            "completed_at": _now(),
            "status": "completed",
            "response_chars": len(response),
            "raw_response_chars": len(raw_response),
        }
        if not _should_replace_result(existing, response):
            print(f"[server] Ignored stale result {task_id} ({len(response)} chars) "
                  f"conv={conv_id[:12]} freed={freed_agent}")
            self._send_json({"status": "ignored", "task_id": task_id})
            return
        with _lock:
            _record_agent_seen(agent_id, event="result")
            results[task_id] = record

        if conv_id:
            _record_turn(conv_id, {
                "task_id": task_id,
                "prompt": (task or {}).get("prompt", ""),
                "response": response,
                "chatgpt_url": chatgpt_url,
                "completed_at": record["completed_at"],
                "model": record["model"],
                "response_chars": len(response),
                "raw_response_chars": len(raw_response),
            })

        # Mirror to disk for offline inspection
        _ensure_dirs()
        out = RESULTS_DIR / f"{task_id}.md"
        meta = {k: v for k, v in record.items() if k != "response"}
        out.write_text(
            f"<!-- bedc-oracle: {json.dumps(meta, ensure_ascii=False)} -->\n\n{response}",
            encoding="utf-8",
        )
        print(f"[server] Result {task_id} ({len(response)} chars) "
              f"conv={conv_id[:12]} freed={freed_agent}")
        self._send_json({"status": "saved", "task_id": task_id})

    def _handle_ack(self, data: dict):
        task_id = data.get("task_id", "")
        agent_id = data.get("agent_id", "?")
        event = "heartbeat" if data.get("heartbeat") else "ack"
        metrics = data.get("metrics") if isinstance(data.get("metrics"), dict) else None
        if metrics:
            metrics = {
                "task_id": task_id,
                "script_version": data.get("script_version", ""),
                "page_url": data.get("page_url", ""),
                "chatgpt_url": data.get("chatgpt_url", ""),
                "elapsed_seconds": metrics.get("elapsed_seconds"),
                "extracted_chars": metrics.get("extracted_chars"),
                "page_chars": metrics.get("page_chars"),
                "stable_count": metrics.get("stable_count"),
                "generating": metrics.get("generating"),
                "url_tail": metrics.get("url_tail"),
            }
        else:
            metrics = {
                "task_id": task_id,
                "script_version": data.get("script_version", ""),
                "page_url": data.get("page_url", ""),
                "chatgpt_url": data.get("chatgpt_url", ""),
            }
        with _lock:
            _record_agent_seen(agent_id, event=event, metrics=metrics)
            if event == "heartbeat" and task_id:
                still_pending = any(t.get("task_id") == task_id for t in pending_tasks.values())
                if task_id in cancelled_tasks or (not still_pending and task_id not in results):
                    self._send_json({"status": "cancelled", "task_id": task_id})
                    return
            if agent_id in dispatch_times:
                dispatch_times[agent_id] = time.time()
        if event == "ack":
            print(f"[server] Ack {task_id} by {agent_id}")
        self._send_json({"status": "ok"})

    def _handle_cancel(self, data: dict):
        task_id = data.get("task_id", "")
        cancel_all = bool(data.get("all", False))
        cancelled: list[str] = []
        with _lock:
            if cancel_all:
                while task_queue:
                    task = task_queue.popleft()
                    tid = task.get("task_id", "")
                    cancelled.append(tid)
                    if tid:
                        cancelled_tasks.add(tid)
                for aid, task in list(pending_tasks.items()):
                    tid = task.get("task_id", "")
                    cancelled.append(tid)
                    if tid:
                        cancelled_tasks.add(tid)
                    pending_tasks.pop(aid, None)
                    dispatch_times.pop(aid, None)
            elif task_id:
                kept: deque[dict] = deque()
                while task_queue:
                    task = task_queue.popleft()
                    if task.get("task_id") == task_id:
                        cancelled.append(task_id)
                        cancelled_tasks.add(task_id)
                    else:
                        kept.append(task)
                task_queue.extend(kept)
                for aid, task in list(pending_tasks.items()):
                    if task.get("task_id") == task_id:
                        cancelled.append(task_id)
                        cancelled_tasks.add(task_id)
                        pending_tasks.pop(aid, None)
                        dispatch_times.pop(aid, None)
            else:
                self._send_json({"error": "task_id or all=true required"}, 400)
                return
        print(f"[server] Cancelled {len(cancelled)} task(s): {cancelled}")
        self._send_json({"status": "cancelled", "tasks": cancelled})

    def _handle_close(self, data: dict):
        conv_id = data.get("conversation_id", "")
        if not conv_id:
            self._send_json({"error": "conversation_id required"}, 400)
            return
        with _lock:
            sess = sessions.get(conv_id) or _load_session(conv_id)
            if sess:
                sess["closed_at"] = _now()
                sessions[conv_id] = sess
                _write_session(sess)
        self._send_json({"status": "closed", "conversation_id": conv_id})

    def _handle_pin_conv_url(self, data: dict):
        """Userscript reports the /c/<uuid> URL it landed on for an in-flight task.

        We pin it to the task's conversation_id so future re-extract or
        follow-up tasks know where to navigate.
        """
        task_id = data.get("task_id", "")
        chatgpt_url = data.get("chatgpt_url", "")
        if not task_id or not chatgpt_url:
            self._send_json({"error": "task_id and chatgpt_url required"}, 400)
            return
        with _lock:
            # Find the conversation_id from result record OR pending task
            conv_id = ""
            rec = results.get(task_id)
            if rec:
                conv_id = rec.get("conversation_id", "")
            if not conv_id:
                for aid, t in pending_tasks.items():
                    if t.get("task_id") == task_id:
                        conv_id = t.get("conversation_id", "")
                        break
            if not conv_id:
                self._send_json({"error": f"unknown task_id {task_id}"}, 404)
                return
            sess = sessions.get(conv_id) or _load_session(conv_id) or {
                "conversation_id": conv_id, "created_at": _now(), "turns": [],
            }
            sess["chatgpt_url"] = chatgpt_url
            sess["updated_at"] = _now()
            sessions[conv_id] = sess
            _write_session(sess)
        print(f"[server] pinned chatgpt_url={chatgpt_url[-50:]} to conv={conv_id[:12]}")
        self._send_json({"status": "pinned", "conversation_id": conv_id, "chatgpt_url": chatgpt_url})

    def _handle_retry(self, data: dict):
        """Re-queue an existing task as a re-extract task.

        Use case: oracle review came back with ERROR or sub-threshold response,
        but ChatGPT actually wrote a real review in the conversation. We
        re-dispatch the same conversation with re_extract=true so the userscript
        navigates back, skips prompt entry, and just reads the latest assistant
        message. If conversation has no chatgpt_url pinned yet (e.g. previous
        run errored before capturing), we instead enqueue a follow-up that
        asks ChatGPT to repeat its prior review verbatim.
        """
        task_id = data.get("task_id", "")
        conv_id = data.get("conversation_id", "")
        if not task_id and not conv_id:
            self._send_json({"error": "task_id or conversation_id required"}, 400)
            return
        with _lock:
            # Resolve conversation_id from task_id if needed
            if not conv_id:
                rec = results.get(task_id)
                if rec:
                    conv_id = rec.get("conversation_id", "")
            if not conv_id:
                self._send_json({"error": f"could not resolve conversation_id for {task_id}"}, 404)
                return
            sess = sessions.get(conv_id) or _load_session(conv_id)
            if not sess:
                self._send_json({"error": f"unknown conversation {conv_id}"}, 404)
                return
            chatgpt_url = sess.get("chatgpt_url", "")

        new_task_id = f"retry_{conv_id[:12]}_{int(time.time())}_{uuid.uuid4().hex[:4]}"
        # Pull original prompt from the first turn so the userscript can
        # configure setSentPrompt and discriminate prompt-echo from response.
        original_prompt = ""
        for t in sess.get("turns", []) or []:
            if isinstance(t, dict) and t.get("prompt"):
                original_prompt = t["prompt"]
                break
        if chatgpt_url:
            # Re-extract mode: userscript navigates and just reads. We still
            # send the original prompt so the userscript can dedupe page-text
            # against prompt echo.
            task = {
                "task_id": new_task_id,
                "prompt": original_prompt,
                "conversation_id": conv_id,
                "conversation_url": chatgpt_url,
                "is_followup": True,
                "re_extract": True,
                "model": data.get("model", "chatgpt-5.5-pro"),
                "tag": data.get("tag", "retry"),
                "submitted_at": _now(),
                "submitted_ts": time.time(),
                "status": "queued",
            }
            mode = "re-extract"
        else:
            # Fallback: ask ChatGPT to repeat its review verbatim.
            task = {
                "task_id": new_task_id,
                "prompt": ("Please paste your final review from the previous turn verbatim, "
                           "no preamble, no commentary, just the review text including the "
                           "VERDICT/SCORE/TOP-RISK/TOP-RECOMMENDATION block."),
                "conversation_id": conv_id,
                "conversation_url": "",
                "is_followup": True,
                "model": data.get("model", "chatgpt-5.5-pro"),
                "tag": data.get("tag", "retry-repeat"),
                "submitted_at": _now(),
                "submitted_ts": time.time(),
                "status": "queued",
            }
            mode = "repeat-prompt"
        with _lock:
            task_queue.append(task)
        print(f"[server] retry {mode} → queued {new_task_id} conv={conv_id[:12]}")
        self._send_json({
            "status": "queued",
            "task_id": new_task_id,
            "conversation_id": conv_id,
            "mode": mode,
            "queue_position": len(task_queue),
        })


def main():
    _ensure_dirs()
    _hydrate_sessions()
    server = HTTPServer(("127.0.0.1", PORT), BEDCOracleHandler)
    print(f"[bedc-oracle] running on http://localhost:{PORT}")
    print(f"[bedc-oracle] sessions dir: {SESSIONS_DIR}")
    print(f"[bedc-oracle] results dir:  {RESULTS_DIR}")
    print(f"[bedc-oracle] hydrated {len(sessions)} sessions from disk")
    print(f"[bedc-oracle] max {MAX_AGENTS} concurrent tabs (multi-turn capable)")
    print(f"[bedc-oracle] open tabs:")
    for i in range(1, MAX_AGENTS + 1):
        print(f"  Tab {i}: https://chatgpt.com/?bedc={i}")
    print(f"[bedc-oracle] Ctrl+C to stop.\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n[bedc-oracle] stopped.")
        server.server_close()


if __name__ == "__main__":
    main()

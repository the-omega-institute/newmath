#!/usr/bin/env python3
"""Thin stdlib HTTP client for the BioReality oracle daemon."""

from __future__ import annotations

import argparse
import base64
import json
import socket
import sys
import time
from pathlib import Path
from typing import Any, Callable
from urllib.error import HTTPError, URLError
from urllib.parse import urljoin
from urllib.request import Request, urlopen


DEFAULT_SERVER_URL = "http://127.0.0.1:8769"


def _server_url(server_url: str) -> str:
    return server_url.rstrip("/") + "/"


def _error(kind: str, detail: str) -> dict[str, Any]:
    return {"status": "error", "error_kind": kind, "detail": detail}


def _request_json(method: str, server_url: str, path: str, payload: dict[str, Any] | None, timeout_seconds: float) -> dict[str, Any]:
    url = urljoin(_server_url(server_url), path.lstrip("/"))
    body = None if payload is None else json.dumps(payload).encode("utf-8")
    req = Request(url, data=body, method=method)
    if body is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urlopen(req, timeout=timeout_seconds) as resp:
            text = resp.read().decode("utf-8")
    except HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        return _error("http_error", f"{exc.code}: {detail}")
    except socket.timeout as exc:
        return _error("timeout", str(exc))
    except TimeoutError as exc:
        return _error("timeout", str(exc))
    except URLError as exc:
        reason = getattr(exc, "reason", exc)
        if isinstance(reason, socket.timeout):
            return _error("timeout", str(reason))
        return _error("connection_error", str(reason))
    except OSError as exc:
        return _error("connection_error", str(exc))
    try:
        return json.loads(text or "{}")
    except json.JSONDecodeError as exc:
        return _error("invalid_json", str(exc))


def submit_query(
    text: str,
    *,
    intended_claim_id: str = "",
    intended_lane: str = "",
    pdf_base64: str = "",
    pdf_name: str = "",
    server_url: str = DEFAULT_SERVER_URL,
    timeout_seconds: int = 60,
) -> str:
    """Submit a query to the BioReality oracle. Returns task_id only (backward compat).
    For sessions that need the server-assigned conversation_id immediately use submit_query_full()."""
    task_id, _conv_id = submit_query_full(
        text,
        intended_claim_id=intended_claim_id,
        intended_lane=intended_lane,
        pdf_base64=pdf_base64,
        pdf_name=pdf_name,
        server_url=server_url,
        timeout_seconds=timeout_seconds,
    )
    return task_id


def submit_query_full(
    text: str,
    *,
    intended_claim_id: str = "",
    intended_lane: str = "",
    pdf_base64: str = "",
    pdf_name: str = "",
    server_url: str = DEFAULT_SERVER_URL,
    timeout_seconds: int = 60,
) -> tuple[str, str]:
    """Submit a query and return (task_id, conversation_id). The server assigns conv_id
    immediately at /tasks even before the userscript picks the task up — capturing it
    here lets the caller persist conv_id for follow-up even if the later poll_result
    times out before a response is posted back."""
    payload = {
        "text": text,
        "prompt": text,
        "intended_claim_id": intended_claim_id,
        "intended_lane": intended_lane,
        "tag": intended_claim_id or intended_lane or "bio-oracle-query",
    }
    if pdf_base64:
        payload["pdf_base64"] = pdf_base64
        payload["pdf_name"] = pdf_name or "main.pdf"
    data = _request_json("POST", server_url, "/tasks", payload, timeout_seconds)
    if data.get("status") == "error":
        return ("", "")
    return (str(data.get("task_id") or ""), str(data.get("conversation_id") or ""))


_PDF_CACHE: dict[str, Any] = {"path": None, "mtime": None, "b64": None, "name": None}


def encode_pdf_for_attach(pdf_path: str | Path | None = None) -> tuple[str, str]:
    """Return (base64, filename) ready to attach to submit_query. Empty strings
    if pdf_path is None or file missing. Caches across calls, re-reads on mtime change."""
    if pdf_path is None:
        return ("", "")
    p = Path(pdf_path)
    if not p.exists():
        return ("", "")
    try:
        st = p.stat()
    except OSError:
        return ("", "")
    if (
        _PDF_CACHE["path"] == str(p)
        and _PDF_CACHE["mtime"] == st.st_mtime
        and _PDF_CACHE["b64"]
    ):
        return (_PDF_CACHE["b64"], _PDF_CACHE["name"])
    try:
        b64 = base64.b64encode(p.read_bytes()).decode("ascii")
    except OSError:
        return ("", "")
    _PDF_CACHE.update({"path": str(p), "mtime": st.st_mtime, "b64": b64, "name": p.name})
    return (b64, p.name)


def continue_query(
    conversation_id: str,
    text: str,
    *,
    intended_claim_id: str = "",
    intended_lane: str = "",
    tag: str = "",
    server_url: str = DEFAULT_SERVER_URL,
    timeout_seconds: int = 60,
) -> str:
    """Submit a follow-up query in an existing oracle conversation. Returns task_id."""
    payload = {
        "conversation_id": conversation_id,
        "text": text,
        "prompt": text,
        "intended_claim_id": intended_claim_id,
        "intended_lane": intended_lane,
        "tag": tag or intended_claim_id or intended_lane or "bio-oracle-followup",
    }
    data = _request_json("POST", server_url, "/continue", payload, timeout_seconds)
    if data.get("status") == "error" or data.get("error"):
        return ""
    return str(data.get("task_id") or "")


def close_conversation(
    conversation_id: str,
    *,
    server_url: str = DEFAULT_SERVER_URL,
    timeout_seconds: int = 60,
) -> bool:
    """Close an oracle conversation on the server."""
    if not conversation_id:
        return False
    data = _request_json("POST", server_url, "/close", {"conversation_id": conversation_id}, timeout_seconds)
    return data.get("status") != "error" and not data.get("error")


def poll_result(
    task_id: str,
    *,
    server_url: str = DEFAULT_SERVER_URL,
    max_wait_seconds: int = 600,
    poll_interval: float = 5.0,
) -> dict[str, Any]:
    """Block until oracle posts back the result or timeout. Return result dict."""
    if not task_id:
        return _error("invalid_task_id", "task_id is empty")
    deadline = time.monotonic() + max(0, max_wait_seconds)
    interval = max(0.1, float(poll_interval))
    while True:
        data = _request_json("GET", server_url, f"/tasks/{task_id}", None, min(interval, 30.0))
        status = str(data.get("status") or "")
        if status in {"completed", "cancelled", "error"}:
            return data
        if status == "not_found":
            return _error("not_found", f"oracle task not found: {task_id}")
        now = time.monotonic()
        if now >= deadline:
            return _error("timeout", f"timed out waiting for oracle task {task_id}")
        time.sleep(min(interval, max(0.0, deadline - now)))


def run_session(
    initial_prompt: str,
    *,
    topic: str,
    judge_callback: Callable[[list[dict[str, Any]]], dict[str, Any]],
    max_turns: int = 20,
    intended_claim_id: str = "",
    intended_lane: str = "",
    pdf_base64: str = "",
    pdf_name: str = "",
    existing_conversation_id: str = "",
    close_on_exit: bool = True,
    server_url: str = DEFAULT_SERVER_URL,
    poll_timeout: int = 600,
    poll_interval: float = 5.0,
) -> dict[str, Any]:
    """
    Run a multi-turn oracle session pinned to a single conversation_id.

    Each turn:
      1. submit_query (turn 0) or continue_query (turn N).
      2. poll_result.
      3. judge_callback(turn_history) decides:
         {"continue": True, "next_prompt": "..."} -> next turn
         {"continue": False, "reason": "..."} -> close + return.

    Returns:
        {
          "topic": str,
          "conversation_id": str,
          "turns": list[dict],
          "closed_reason": str,
          "max_turns_reached": bool,
        }
    """
    turns: list[dict[str, Any]] = []
    conversation_id = str(existing_conversation_id or "")
    closed_reason = ""
    max_turns_reached = False
    current_prompt = initial_prompt
    total_turns = max(0, int(max_turns))
    resumed = bool(conversation_id)

    try:
        for turn_index in range(total_turns):
            if turn_index == 0 and not conversation_id:
                task_id, new_conv_id = submit_query_full(
                    current_prompt,
                    intended_claim_id=intended_claim_id,
                    intended_lane=intended_lane,
                    pdf_base64=pdf_base64,
                    pdf_name=pdf_name,
                    server_url=server_url,
                )
                # Capture conv_id immediately from server's submit response so
                # caller can persist it for follow-up even if poll_result times out.
                if new_conv_id and not conversation_id:
                    conversation_id = new_conv_id
            elif turn_index == 0 and conversation_id:
                # Resuming an existing ChatGPT conversation across cycles.
                task_id = continue_query(
                    conversation_id,
                    current_prompt,
                    intended_claim_id=intended_claim_id,
                    intended_lane=intended_lane,
                    tag=topic,
                    server_url=server_url,
                )
            else:
                task_id = continue_query(
                    conversation_id,
                    current_prompt,
                    intended_claim_id=intended_claim_id,
                    intended_lane=intended_lane,
                    tag=topic,
                    server_url=server_url,
                )
            if not task_id:
                result = _error("submit_failed", f"oracle task submission failed at turn {turn_index}")
                turns.append({"turn": turn_index, "prompt": current_prompt, "result": result})
                closed_reason = result["detail"]
                break

            result = poll_result(
                task_id,
                server_url=server_url,
                max_wait_seconds=poll_timeout,
                poll_interval=poll_interval,
            )
            if not conversation_id:
                conversation_id = str(result.get("conversation_id") or "")
            turns.append({"turn": turn_index, "prompt": current_prompt, "result": result})

            status = str(result.get("status") or "")
            if status in {"cancelled", "error"}:
                closed_reason = f"turn {turn_index} ended with status {status}"
                break

            if turn_index + 1 >= total_turns:
                max_turns_reached = True
                closed_reason = "max_turns reached"
                break

            try:
                decision = judge_callback(turns)
            except Exception as exc:
                closed_reason = f"judge_callback error: {exc}"
                break
            if not isinstance(decision, dict):
                closed_reason = "judge_callback returned a non-dict decision"
                break
            if not bool(decision.get("continue")):
                closed_reason = str(decision.get("reason") or "judge_callback stopped")
                break
            next_prompt = str(decision.get("next_prompt") or "")
            if not next_prompt:
                closed_reason = "judge_callback requested continue without next_prompt"
                break
            current_prompt = next_prompt

        if total_turns == 0:
            max_turns_reached = True
            closed_reason = "max_turns reached"
        elif not closed_reason:
            closed_reason = "session ended"
    finally:
        if conversation_id and close_on_exit:
            close_conversation(conversation_id, server_url=server_url)

    return {
        "topic": topic,
        "conversation_id": conversation_id,
        "turns": turns,
        "closed_reason": closed_reason,
        "max_turns_reached": max_turns_reached,
        "resumed": resumed,
        "closed": bool(conversation_id and close_on_exit),
    }


def health_check(server_url: str = DEFAULT_SERVER_URL, timeout_seconds: int = 5) -> bool:
    """Return True if oracle server is reachable + has at least one active userscript tab."""
    data = _request_json("GET", server_url, "/health", None, timeout_seconds)
    if data.get("status") != "ok":
        return False
    try:
        return int(data.get("active_userscript_tabs") or 0) > 0
    except (TypeError, ValueError):
        return False


def _self_test() -> int:
    from http.server import BaseHTTPRequestHandler, HTTPServer
    import threading

    state: dict[str, Any] = {
        "tasks": {},
        "active_tabs": 1,
        "slow": False,
        "next_task": 1,
        "next_conversation": 1,
        "sessions": {},
        "continue_conversation_ids": [],
        "close_conversation_ids": [],
    }

    def next_task_id() -> str:
        task_id = f"bio_mock_{state['next_task']}"
        state["next_task"] += 1
        return task_id

    def next_conversation_id() -> str:
        conv_id = f"conv_mock_{state['next_conversation']}"
        state["next_conversation"] += 1
        return conv_id

    class MockHandler(BaseHTTPRequestHandler):
        def log_message(self, fmt, *args):
            return

        def _send(self, payload: dict[str, Any], status: int = 200) -> None:
            body = json.dumps(payload).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if self.path == "/health":
                self._send({"status": "ok", "active_userscript_tabs": state["active_tabs"]})
                return
            if self.path.startswith("/tasks/"):
                task_id = self.path.split("/", 2)[2]
                if state["slow"]:
                    self._send({"status": "queued", "task_id": task_id})
                    return
                task = state["tasks"].get(task_id)
                if not task:
                    self._send({"status": "not_found", "task_id": task_id}, 404)
                    return
                self._send({
                    "status": "completed",
                    "task_id": task_id,
                    "response": task["response"],
                    "conversation_id": task["conversation_id"],
                })
                return
            self._send({"status": "not_found"}, 404)

        def do_POST(self):
            length = int(self.headers.get("Content-Length", "0") or 0)
            payload = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
            if self.path == "/tasks":
                task_id = next_task_id()
                conv_id = payload.get("conversation_id") or next_conversation_id()
                state["sessions"].setdefault(conv_id, {"conversation_id": conv_id})
                state["tasks"][task_id] = {
                    "prompt": payload.get("prompt", ""),
                    "response": f"mock result {task_id}",
                    "conversation_id": conv_id,
                }
                self._send({"status": "queued", "task_id": task_id, "conversation_id": conv_id})
                return
            if self.path == "/continue":
                conv_id = payload.get("conversation_id", "")
                if not conv_id:
                    self._send({"error": "conversation_id required"}, 400)
                    return
                state["continue_conversation_ids"].append(conv_id)
                task_id = next_task_id()
                state["tasks"][task_id] = {
                    "prompt": payload.get("prompt", ""),
                    "response": f"mock result {task_id}",
                    "conversation_id": conv_id,
                }
                self._send({"status": "queued", "task_id": task_id, "conversation_id": conv_id})
                return
            if self.path == "/close":
                conv_id = payload.get("conversation_id", "")
                state["close_conversation_ids"].append(conv_id)
                self._send({"status": "closed", "conversation_id": conv_id})
                return
            self._send({"status": "not_found"}, 404)

    server = HTTPServer(("127.0.0.1", 0), MockHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{server.server_address[1]}"
    try:
        task_id = submit_query("mock question", intended_claim_id="h0.mock", server_url=base)
        if task_id != "bio_mock_1":
            print(json.dumps({"task_id": task_id}, indent=2), file=sys.stderr)
            return 1
        result = poll_result(task_id, server_url=base, max_wait_seconds=2, poll_interval=0.1)
        if result.get("status") != "completed" or result.get("response") != "mock result bio_mock_1":
            print(json.dumps({"result": result}, indent=2), file=sys.stderr)
            return 1
        if not health_check(server_url=base):
            print("expected health_check true", file=sys.stderr)
            return 1
        state["active_tabs"] = 0
        if health_check(server_url=base):
            print("expected health_check false", file=sys.stderr)
            return 1
        state["slow"] = True
        timeout_result = poll_result(task_id, server_url=base, max_wait_seconds=0, poll_interval=0.1)
        if timeout_result.get("status") != "error" or timeout_result.get("error_kind") != "timeout":
            print(json.dumps({"timeout_result": timeout_result}, indent=2), file=sys.stderr)
            return 1
        state["slow"] = False
        state["active_tabs"] = 1

        start_continue_count = len(state["continue_conversation_ids"])
        start_close_count = len(state["close_conversation_ids"])

        def three_turn_judge(turns: list[dict[str, Any]]) -> dict[str, Any]:
            if len(turns) < 3:
                return {"continue": True, "next_prompt": f"follow up {len(turns)}"}
            return {"continue": False, "reason": "enough signal"}

        session_result = run_session(
            "initial session question",
            topic="mock-topic",
            judge_callback=three_turn_judge,
            server_url=base,
            poll_timeout=2,
            poll_interval=0.1,
        )
        if len(session_result["turns"]) != 3 or session_result["closed_reason"] != "enough signal":
            print(json.dumps({"session_result": session_result}, indent=2), file=sys.stderr)
            return 1
        session_conv_id = session_result["conversation_id"]
        new_continue_ids = state["continue_conversation_ids"][start_continue_count:]
        if new_continue_ids != [session_conv_id, session_conv_id]:
            print(json.dumps({"continue_conversation_ids": new_continue_ids, "session_conv_id": session_conv_id}, indent=2), file=sys.stderr)
            return 1
        new_close_ids = state["close_conversation_ids"][start_close_count:]
        if new_close_ids != [session_conv_id]:
            print(json.dumps({"close_conversation_ids": new_close_ids, "session_conv_id": session_conv_id}, indent=2), file=sys.stderr)
            return 1

        start_close_count = len(state["close_conversation_ids"])

        def always_continue(turns: list[dict[str, Any]]) -> dict[str, Any]:
            return {"continue": True, "next_prompt": f"next {len(turns)}"}

        capped_session_result = run_session(
            "capped session question",
            topic="mock-topic-cap",
            judge_callback=always_continue,
            max_turns=2,
            server_url=base,
            poll_timeout=2,
            poll_interval=0.1,
        )
        if len(capped_session_result["turns"]) != 2 or not capped_session_result["max_turns_reached"]:
            print(json.dumps({"capped_session_result": capped_session_result}, indent=2), file=sys.stderr)
            return 1
        capped_conv_id = capped_session_result["conversation_id"]
        new_close_ids = state["close_conversation_ids"][start_close_count:]
        if new_close_ids != [capped_conv_id]:
            print(json.dumps({"close_conversation_ids": new_close_ids, "capped_conv_id": capped_conv_id}, indent=2), file=sys.stderr)
            return 1
        print("[bio-oracle-client] self-test ok")
        return 0
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Submit and poll BioReality oracle queries")
    parser.add_argument("--server-url", default=DEFAULT_SERVER_URL)
    parser.add_argument("--query", default="")
    parser.add_argument("--intended-claim", default="")
    parser.add_argument("--intended-lane", default="")
    parser.add_argument("--max-wait-seconds", type=int, default=600)
    parser.add_argument("--poll-interval", type=float, default=5.0)
    parser.add_argument("--health-check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return _self_test()
    if args.health_check:
        ok = health_check(server_url=args.server_url)
        print(json.dumps({"status": "ok" if ok else "error", "active_userscript_tab": ok}, sort_keys=True))
        return 0 if ok else 1
    if not args.query:
        parser.error("--query is required unless --health-check or --self-test is used")
    task_id = submit_query(
        args.query,
        intended_claim_id=args.intended_claim,
        intended_lane=args.intended_lane,
        server_url=args.server_url,
    )
    print(json.dumps({"task_id": task_id}, sort_keys=True))
    if not task_id:
        print(json.dumps(_error("submit_failed", "oracle server did not return a task_id"), sort_keys=True))
        return 1
    result = poll_result(
        task_id,
        server_url=args.server_url,
        max_wait_seconds=args.max_wait_seconds,
        poll_interval=args.poll_interval,
    )
    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
    return 0 if result.get("status") != "error" else 1


if __name__ == "__main__":
    raise SystemExit(main())

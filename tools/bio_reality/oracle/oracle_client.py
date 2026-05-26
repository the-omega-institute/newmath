#!/usr/bin/env python3
"""Thin stdlib HTTP client for the BioReality oracle daemon."""

from __future__ import annotations

import argparse
import json
import socket
import sys
import time
from typing import Any
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
    server_url: str = DEFAULT_SERVER_URL,
    timeout_seconds: int = 60,
) -> str:
    """Submit a query to the BioReality oracle. Returns task_id."""
    payload = {
        "text": text,
        "prompt": text,
        "intended_claim_id": intended_claim_id,
        "intended_lane": intended_lane,
        "tag": intended_claim_id or intended_lane or "bio-oracle-query",
    }
    data = _request_json("POST", server_url, "/tasks", payload, timeout_seconds)
    if data.get("status") == "error":
        return ""
    return str(data.get("task_id") or "")


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

    state: dict[str, Any] = {"tasks": {}, "active_tabs": 1, "slow": False}

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
                self._send({"status": "completed", "task_id": task_id, "response": task["response"]})
                return
            self._send({"status": "not_found"}, 404)

        def do_POST(self):
            length = int(self.headers.get("Content-Length", "0") or 0)
            payload = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
            if self.path == "/tasks":
                task_id = "bio_mock_1"
                state["tasks"][task_id] = {"prompt": payload.get("prompt", ""), "response": "mock result"}
                self._send({"status": "queued", "task_id": task_id})
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
        if result.get("status") != "completed" or result.get("response") != "mock result":
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

#!/usr/bin/env python3
"""BEDC client for the local ChatGPT oracle server.

The expected server is tools/bedc-deep/bedc_oracle_server.py on
http://localhost:8767.
This client only sends prompts and stores local runtime artifacts. It never
runs Lean, never edits Lean files, and never writes paper markers.
"""

from __future__ import annotations

import argparse
import json
import re
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone
from pathlib import Path

from dispatch_bedc_target import SCRIPT_DIR, BedcTarget, build_initial_prompt, parse_board


ORACLE_SERVER = "http://localhost:8767"
STATE_DIR = SCRIPT_DIR / "state"
TARGETS_DIR = SCRIPT_DIR / "targets"
CLAIM_PACKET_PROMPT = SCRIPT_DIR / "prompts" / "claim_packet.txt"

FOLLOW_UPS = [
    "Take the weakest link in your previous answer and test it. Is the claim derived, or does it need a setup field?",
    "Construct the smallest finite countermodel that would break the current claim. If no countermodel is visible, explain the exact obstruction.",
    "State the narrowest local lemma in ordinary mathematical prose, with all assumptions explicit. Do not write Lean code.",
    "Separate the definitional part from the policy-assumption part. Which sentence is doing the real work?",
    "Identify the smallest object or relation that must exist before this claim can be checked.",
    "If the target is too strong, give the strongest weaker statement that still preserves the BEDC intent.",
]


def http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def http_get(url: str, timeout: int = 10) -> dict:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def server_status(server_url: str) -> dict:
    return http_get(f"{server_url}/status", timeout=5)


def server_alive(server_url: str) -> bool:
    try:
        return "queue_length" in server_status(server_url)
    except Exception:
        return False


def status_line(status: dict) -> str:
    recent = status.get("active_recent_agents") or []
    return (
        f"diagnosis={status.get('diagnosis', 'unknown')} "
        f"queue={status.get('queue_length', '?')} "
        f"busy={status.get('agents_busy', '?')}/{status.get('max_agents', '?')} "
        f"recent_agents={len(recent)} completed={status.get('completed', '?')}"
    )


def print_status_hint(server_url: str) -> dict:
    try:
        status = server_status(server_url)
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise SystemExit(
            f"oracle server is not reachable at {server_url}; "
            "start: python3 tools/bedc-deep/bedc_oracle_server.py"
        ) from exc
    print(f"[status] {status_line(status)}", flush=True)
    if status.get("diagnosis") == "queue_waiting_for_browser_agent":
        print("[status] queued work has no active BEDC ChatGPT tab.", flush=True)
        print("[status] install userscript: tools/bedc-deep/bedc_oracle_macos.user.js", flush=True)
        print("[status] open: https://chatgpt.com/?bedc=1 and click Start in the BEDC panel", flush=True)
    return status


def watch_status(server_url: str, interval: int) -> None:
    while True:
        status = print_status_hint(server_url)
        queued = status.get("queued_tasks") or []
        if queued:
            oldest = queued[0]
            print(
                "[watch] oldest="
                f"{oldest.get('task_id', '')} age={oldest.get('age_seconds', '?')}s "
                f"chars={oldest.get('prompt_chars', '?')}",
                flush=True,
            )
        time.sleep(max(1, interval))


def submit_turn(
    server_url: str,
    task_id: str,
    prompt: str,
    conversation_id: str = "",
    model: str = "chatgpt-5.5-pro",
) -> dict:
    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": model,
        "tag": "bedc-deep",
    }
    if conversation_id:
        payload["conversation_id"] = conversation_id
    endpoint = "/continue" if conversation_id else "/submit"
    return http_post(f"{server_url}{endpoint}", payload, timeout=30)


def wait_for_recent_agent(server_url: str, seconds: int, poll_interval: int) -> bool:
    if seconds <= 0:
        return True
    deadline = time.time() + seconds
    while time.time() < deadline:
        status = print_status_hint(server_url)
        if status.get("active_recent_agents"):
            return True
        time.sleep(max(1, poll_interval))
    return False


def poll_result(
    server_url: str,
    task_id: str,
    timeout: int,
    poll_interval: int,
    status_interval: int,
) -> str:
    start = time.time()
    next_status_at = start
    while time.time() - start < timeout:
        try:
            data = http_get(f"{server_url}/result/{task_id}", timeout=10)
            if data.get("status") == "completed":
                return data.get("response", "")
        except Exception:
            pass
        now = time.time()
        if now >= next_status_at:
            try:
                status = server_status(server_url)
                print(f"[wait:{task_id}] {status_line(status)}", flush=True)
                if status.get("diagnosis") == "queue_waiting_for_browser_agent":
                    print("[wait] no active BEDC ChatGPT tab is polling; start one with https://chatgpt.com/?bedc=1", flush=True)
            except Exception as exc:
                print(f"[wait:{task_id}] status unavailable: {exc}", flush=True)
            next_status_at = now + max(1, status_interval)
        time.sleep(poll_interval)
    return ""


def artifact_dir(target: BedcTarget) -> Path:
    path = TARGETS_DIR / target.slug
    path.mkdir(parents=True, exist_ok=True)
    return path


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def detect_verdict(text: str) -> str:
    if re.search(r"\b(False|TooStrong)\b", text):
        return "OBSTRUCTION"
    if re.search(r"\bDerived\b", text):
        return "DERIVED_CANDIDATE"
    if re.search(r"\b(NeedsDefinition|NeedsSetupField|NarrativeOnly)\b", text):
        return "NEEDS_BOUNDARY"
    if re.search(r"\bSTUCK\b", text, re.IGNORECASE):
        return "STUCK"
    return "OPEN"


def save_state(target: BedcTarget, state: dict) -> Path:
    path = STATE_DIR / f"{target.slug}.json"
    write_text(path, json.dumps(state, ensure_ascii=False, indent=2) + "\n")
    return path


def run_loop(args: argparse.Namespace) -> int:
    targets = parse_board()
    target = targets.get(args.target_id)
    if target is None:
        known = ", ".join(targets)
        raise SystemExit(f"unknown target {args.target_id}; known targets: {known}")

    print_status_hint(args.server)
    if args.preflight_agent_wait > 0 and not wait_for_recent_agent(
        args.server, args.preflight_agent_wait, args.poll_interval
    ):
        raise SystemExit(
            "no active BEDC ChatGPT tab appeared before preflight timeout; "
            "open https://chatgpt.com/?bedc=1 and click Start"
        )

    out_dir = artifact_dir(target)
    turns: list[dict] = []
    conversation_id = ""
    started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    prompt = build_initial_prompt(target)

    for turn in range(args.max_turns):
        if turn > 0:
            prompt = FOLLOW_UPS[(turn - 1) % len(FOLLOW_UPS)]
        task_id = f"bedc_{target.target_id.lower()}_{int(time.time() * 1000)}"
        write_text(out_dir / f"turn_{turn:02d}_prompt.md", prompt)
        submit = submit_turn(args.server, task_id, prompt, conversation_id, model=args.model)
        if "error" in submit:
            raise SystemExit(f"oracle submit failed: {submit['error']}")
        conversation_id = submit.get("conversation_id") or conversation_id
        print(
            f"[submit] task={task_id} conv={conversation_id[:12]} "
            f"queue_position={submit.get('queue_position', '?')}",
            flush=True,
        )
        response = poll_result(
            args.server,
            task_id,
            args.timeout,
            args.poll_interval,
            args.status_interval,
        )
        if not response:
            turns.append({"turn": turn, "task_id": task_id, "response": "", "verdict": "TIMEOUT"})
            break
        write_text(out_dir / f"turn_{turn:02d}_response.md", response)
        verdict = detect_verdict(response)
        turns.append({"turn": turn, "task_id": task_id, "response_file": f"turn_{turn:02d}_response.md", "verdict": verdict})
        if verdict in {"DERIVED_CANDIDATE", "OBSTRUCTION", "STUCK"} and turn + 1 >= args.min_turns:
            break

    packet_file = ""
    if args.write_packet and conversation_id:
        packet_prompt = CLAIM_PACKET_PROMPT.read_text(encoding="utf-8")
        task_id = f"bedc_{target.target_id.lower()}_packet_{int(time.time() * 1000)}"
        write_text(out_dir / "claim_packet_prompt.md", packet_prompt)
        submit = submit_turn(args.server, task_id, packet_prompt, conversation_id, model=args.model)
        if "error" in submit:
            raise SystemExit(f"claim packet submit failed: {submit['error']}")
        print(
            f"[submit] task={task_id} conv={conversation_id[:12]} "
            f"queue_position={submit.get('queue_position', '?')}",
            flush=True,
        )
        packet = poll_result(
            args.server,
            task_id,
            args.timeout,
            args.poll_interval,
            args.status_interval,
        )
        if packet:
            packet_file = "claim_packet.md"
            write_text(out_dir / packet_file, packet)

    state = {
        "target_id": target.target_id,
        "title": target.title,
        "conversation_id": conversation_id,
        "started_at": started_at,
        "completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "turns": turns,
        "claim_packet_file": packet_file,
    }
    state_path = save_state(target, state)
    print(f"state: {state_path}", flush=True)
    if packet_file:
        print(f"claim_packet: {out_dir / packet_file}", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Run a BEDC target through the ChatGPT oracle bridge")
    parser.add_argument("target_id", nargs="?", help="Target id such as B-01")
    parser.add_argument("--server", default=ORACLE_SERVER, help="Oracle server URL")
    parser.add_argument("--model", default="chatgpt-5.5-pro", help="Model name passed to the oracle server")
    parser.add_argument("--max-turns", type=int, default=6, help="Maximum reasoning turns")
    parser.add_argument("--min-turns", type=int, default=2, help="Minimum turns before early stop")
    parser.add_argument("--timeout", type=int, default=7200, help="Per-turn timeout in seconds")
    parser.add_argument("--poll-interval", type=int, default=30, help="Polling interval in seconds")
    parser.add_argument("--status-interval", type=int, default=30, help="Status print interval while waiting")
    parser.add_argument("--preflight-agent-wait", type=int, default=0, help="Wait this many seconds for an active browser agent before submitting")
    parser.add_argument("--status", action="store_true", help="Print server status and exit")
    parser.add_argument("--watch-status", type=int, default=0, metavar="SECONDS", help="Continuously print server status every N seconds")
    parser.add_argument("--write-packet", action="store_true", help="Ask for a terminal claim packet")
    args = parser.parse_args()
    if args.watch_status > 0:
        try:
            watch_status(args.server, args.watch_status)
        except KeyboardInterrupt:
            print("\n[watch] stopped", flush=True)
        return 0
    if args.status:
        print(json.dumps(print_status_hint(args.server), ensure_ascii=False, indent=2))
        return 0
    if not args.target_id:
        parser.error("target_id is required unless --status is used")
    return run_loop(args)


if __name__ == "__main__":
    raise SystemExit(main())

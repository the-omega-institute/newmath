#!/usr/bin/env python3
"""oracle_board_refill — when BOARD is dry, ask oracle to propose new targets.

Codex's static gap-scan (auto_discovery probe) finds mechanical missing
pieces (definition without theorem, A→B without B→A, etc.). It runs out
quickly because it can only spot patterns that were ALREADY visible in
paper structure. Once those are filled, codex says "no candidates"
indefinitely.

Oracle has the full paper PDF (project-attached) and mathematical research
intuition. It can suggest deeper directions: structural / classification /
rigidity theorems, obstruction results, multi-scale induction closures.
This script invokes that capability directly.

Flow:
  1. Build prompt: oracle_board_refill.txt + existing BOARD content +
     all paper \\label values (so oracle skips already-proven things).
  2. Submit as a fresh oracle task via the oracle_server (same channel as
     normal pipeline tasks — the userscript handles upload routing).
  3. Poll for response (with reasonable timeout).
  4. Parse the candidate JSON list.
  5. Pipe through board_spawn.spawn_from_candidates which runs the
     claude judge (maker/checker) over them and atomically appends
     accepted ones to BOARD.md.
  6. Report stats.

Usage:
  python3 tools/bedc-deep/oracle_board_refill.py [--server URL] [--timeout SEC]

Standalone CLI script — supervisor can call it via subprocess on a cooldown
when unfinished count drops below threshold.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.request
from datetime import datetime
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "board_refill_logs"
ORACLE_SERVER = "http://localhost:8767"

DEFAULT_TIMEOUT = 7200  # 2 hours — oracle can take long on a meta-question
DEFAULT_POLL_INTERVAL = 30


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def _http_get(url: str, timeout: int = 10) -> dict:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def _board_content() -> str:
    p = SCRIPT_DIR / "BOARD.md"
    return p.read_text(encoding="utf-8") if p.exists() else "(empty)"


def _scan_paper_labels(limit: int = 600) -> str:
    """Quick scan of papers/bedc/parts/**/*.tex for theorem-flavored labels."""
    parts = REPO_ROOT / "papers" / "bedc" / "parts"
    if not parts.exists():
        return "(no parts/ found)"
    pat = re.compile(r"\\label\{(thm|lem|prop|cor|def):([^}]+)\}")
    labels: list[str] = []
    for path in parts.rglob("*.tex"):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in pat.finditer(text):
            labels.append(f"{m.group(1)}:{m.group(2)}")
    labels = sorted(set(labels))
    if len(labels) > limit:
        labels = labels[:limit]
        labels.append(f"... ({len(labels) - limit} more truncated)")
    return "\n".join(labels)


def _extract_json_object(text: str) -> Optional[dict]:
    """Robust scanner — same as elsewhere in pipeline."""
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    for start in range(len(text)):
        if text[start] != "{":
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(text)):
            ch = text[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    cand = text[start : i + 1]
                    try:
                        return json.loads(cand)
                    except json.JSONDecodeError:
                        break
    return None


# ---------------------------------------------------------------------------
# Build prompt
# ---------------------------------------------------------------------------


def build_refill_prompt() -> str:
    template = (PROMPTS_DIR / "oracle_board_refill.txt").read_text(encoding="utf-8")
    board = _board_content()
    labels = _scan_paper_labels()
    return template.format(
        board_content=_safe(board[:30000]),
        paper_labels=_safe(labels),
    )


# ---------------------------------------------------------------------------
# Submit + poll oracle
# ---------------------------------------------------------------------------


def submit_refill(server_url: str, prompt: str) -> dict:
    """Submit as a NEW oracle task (no conversation_id) so userscript opens
    a fresh chat in the BEDC Project (which has the PDF attached at project
    level). The oracle then sees the PDF + our refill prompt."""
    task_id = f"bedc_board_refill_{int(time.time() * 1000)}"
    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": "chatgpt-5.5-pro",
        "tag": "bedc-deep-board-refill",
    }
    req = urllib.request.Request(
        f"{server_url}/submit",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def poll_result(server_url: str, task_id: str, timeout: int, poll_interval: int) -> str:
    start = time.time()
    last_log = start
    while time.time() - start < timeout:
        try:
            data = _http_get(f"{server_url}/result/{task_id}", timeout=10)
            if data.get("status") == "completed":
                return data.get("response", "")
        except Exception:
            pass
        if time.time() - last_log > 60:
            elapsed = int(time.time() - start)
            print(f"[board_refill] waiting... {elapsed}s elapsed", flush=True)
            last_log = time.time()
        time.sleep(poll_interval)
    return ""


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Ask oracle for new BOARD candidates via Project-attached PDF",
    )
    parser.add_argument("--server", default=ORACLE_SERVER)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    parser.add_argument("--dry-run", action="store_true",
                        help="Only build + print prompt, don't submit.")
    args = parser.parse_args()

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()

    prompt = build_refill_prompt()
    (LOG_DIR / f"refill_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    print(f"[board_refill] prompt built ({len(prompt)} chars)", flush=True)

    if args.dry_run:
        print(prompt[:2000])
        print(f"... [{len(prompt)} chars total]")
        return 0

    # Verify server reachable
    try:
        status = _http_get(f"{args.server}/status", timeout=5)
        if not status.get("active_recent_agents"):
            print(
                f"[board_refill] WARN: no active ChatGPT tabs polling. "
                f"Submit will queue but won't dispatch. Open the BEDC Project "
                f"tabs first.",
                flush=True,
            )
    except Exception as exc:
        print(f"[board_refill] server unreachable at {args.server}: {exc}", flush=True)
        return 1

    submit_resp = submit_refill(args.server, prompt)
    if "error" in submit_resp:
        print(f"[board_refill] submit failed: {submit_resp['error']}", flush=True)
        return 1
    task_id = submit_resp.get("task_id", "")
    conv_id = submit_resp.get("conversation_id", "")
    print(f"[board_refill] submitted task={task_id} conv={conv_id[:14]}", flush=True)

    response = poll_result(args.server, task_id, args.timeout, args.poll_interval)
    if not response:
        print(f"[board_refill] timeout waiting for response (limit={args.timeout}s)",
              flush=True)
        return 1

    (LOG_DIR / f"refill_{ts}.response.md").write_text(response, encoding="utf-8")
    print(f"[board_refill] received {len(response)} chars", flush=True)

    parsed = _extract_json_object(response)
    if not parsed:
        print("[board_refill] response was not parseable JSON", flush=True)
        return 1

    candidates = parsed.get("candidates") or []
    if not isinstance(candidates, list):
        print(f"[board_refill] candidates field is not a list: {type(candidates)}",
              flush=True)
        return 1

    # Stamp source for board_spawn judge to know
    for c in candidates:
        if isinstance(c, dict):
            c["source"] = "oracle_board_refill"

    print(f"[board_refill] oracle returned {len(candidates)} raw candidates",
          flush=True)
    if not candidates:
        print("[board_refill] empty candidate list — oracle declined to suggest anything",
              flush=True)
        return 0

    # Pipe through board_spawn judge
    sys.path.insert(0, str(SCRIPT_DIR))
    import board_spawn

    spawn_result = board_spawn.spawn_from_candidates(
        codex_candidates=[],
        oracle_candidates=candidates,
    )
    summary = {
        "ok": spawn_result.ok,
        "candidates_proposed": len(candidates),
        "accepted": len(spawn_result.accepted),
        "rejected": len(spawn_result.rejected),
        "appended_ids": spawn_result.appended_ids,
        "error": spawn_result.error,
        "ts": ts,
    }
    (LOG_DIR / f"refill_{ts}.summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8",
    )
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if spawn_result.ok and spawn_result.appended_ids else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Codex driver for the BEDC oracle deep-reasoning loop.

Runs `codex exec --json` as a per-turn orchestrator: reads the conversation
transcript and the latest oracle response, returns a JSON object containing
the next prompt, a progress score, and a one-line contribution summary.

Also exposes topic-discovery: after a target reaches verdict=done, scan the
full transcript for adjacent claims worth opening as new BOARD entries.

Hard rule: this module never edits Lean files and never edits paper files.
It only produces JSON used by oracle_client.py.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "codex_logs"

CODEX_PATH = shutil.which("codex") or "/opt/homebrew/bin/codex"
DEFAULT_TIMEOUT = 600
HISTORY_EXCERPT_LIMIT = 320
PAPER_CONTEXT_TAIL_LINES = 80


@dataclass(frozen=True)
class CodexResult:
    ok: bool
    parsed: dict
    raw_output: str
    rc: int
    error: str = ""


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _truncate(text: str, limit: int) -> str:
    text = text or ""
    if len(text) <= limit:
        return text
    return text[: limit - 3].rstrip() + "..."


def _safe(text: str) -> str:
    """Escape braces so str.format() never interprets user data as a placeholder."""
    return (text or "").replace("{", "{{").replace("}", "}}")


def _strip_jsonl_to_text(stdout: str) -> str:
    """Best-effort: extract assistant output from codex --json stdout."""
    parts: list[str] = []
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        msg = obj.get("message") or obj.get("content") or ""
        if isinstance(msg, list):
            for chunk in msg:
                if isinstance(chunk, dict):
                    text = chunk.get("text") or chunk.get("content") or ""
                    if text:
                        parts.append(str(text))
        elif isinstance(msg, str) and msg:
            parts.append(msg)
    return "\n".join(parts).strip()


def _extract_json_object(text: str) -> Optional[dict]:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        candidate = fence.group(1)
    else:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first : last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


def codex_exec(prompt: str, *, timeout: int = DEFAULT_TIMEOUT, log_tag: str = "") -> CodexResult:
    """Run `codex exec --json` with stdin prompt; return raw output + rc."""
    if not CODEX_PATH or not Path(CODEX_PATH).exists():
        return CodexResult(False, {}, "", -1, error=f"codex CLI not found at {CODEX_PATH}")

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    tag = log_tag or "turn"
    ts = _now_tag()
    prompt_file = LOG_DIR / f"{tag}_{ts}.prompt.txt"
    output_file = LOG_DIR / f"{tag}_{ts}.out.txt"
    stdout_file = LOG_DIR / f"{tag}_{ts}.stdout.jsonl"
    stderr_file = LOG_DIR / f"{tag}_{ts}.stderr.txt"
    prompt_file.write_text(prompt, encoding="utf-8")

    cmd = [
        CODEX_PATH,
        "exec",
        "--sandbox",
        "read-only",
        "--json",
        "-C",
        str(REPO_ROOT),
        "-o",
        str(output_file),
        "-",
    ]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=str(REPO_ROOT),
        env=env,
        encoding="utf-8",
        errors="replace",
        start_new_session=True,
    )
    stdout = ""
    stderr = ""
    rc: int = -1
    # Hard-kill watchdog: subprocess.communicate's own timeout has been
    # observed to not fire on long codex runs (B-18/B-19 took 38 min with
    # timeout=600). A separate threading.Timer schedules an explicit
    # SIGKILL on the process group at timeout + 60s so even if communicate
    # misbehaves, the worker is bounded.
    hard_killed = {"flag": False}
    def _hard_kill() -> None:
        hard_killed["flag"] = True
        try:
            os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError):
            pass
    watchdog = threading.Timer(timeout + 60, _hard_kill)
    watchdog.daemon = True
    watchdog.start()
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""
            stderr = stderr or ""
        rc = -9
    finally:
        watchdog.cancel()
    if hard_killed["flag"] and rc == 0:
        # communicate returned 0 because the watchdog kill caused EOF on
        # the pipes, but the run exceeded its budget — demote to timeout.
        rc = -9
    stdout_file.write_text(stdout or "", encoding="utf-8")
    stderr_file.write_text(stderr or "", encoding="utf-8")

    if rc != 0:
        return CodexResult(False, {}, stdout, rc, error=f"codex exec rc={rc}")

    raw = ""
    if output_file.exists() and output_file.stat().st_size > 0:
        raw = output_file.read_text(encoding="utf-8", errors="replace")
    if not raw:
        raw = _strip_jsonl_to_text(stdout)
    parsed = _extract_json_object(raw) or {}
    return CodexResult(True, parsed, raw, rc)


def _format_history(turns: list[dict]) -> str:
    lines: list[str] = []
    for t in turns:
        n = t.get("turn", "?")
        contrib = _truncate(t.get("contribution_one_liner", "") or "", HISTORY_EXCERPT_LIMIT)
        delta = t.get("progress_delta", "?")
        lines.append(f"T{n} (Δ={delta}): {contrib or '(no contribution recorded)'}")
    if not lines:
        return "(no prior turns)"
    return "\n".join(lines)


def _read_paper_tail(target_tex_file: Path) -> str:
    if not target_tex_file or not target_tex_file.exists():
        return "(target paper file not yet selected)"
    try:
        text = target_tex_file.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "(could not read target paper file)"
    lines = text.splitlines()
    tail = lines[-PAPER_CONTEXT_TAIL_LINES:]
    return "\n".join(tail)


def orchestrate_turn(
    *,
    target_id: str,
    target_title: str,
    target_context: str,
    history_turns: list[dict],
    last_response: str,
    target_tex_file: Optional[Path],
) -> CodexResult:
    """Ask codex for the next-turn JSON. Returns CodexResult with parsed payload."""
    template = (PROMPTS_DIR / "codex_orchestrator.txt").read_text(encoding="utf-8")
    paper_context = _read_paper_tail(target_tex_file) if target_tex_file else "(none)"
    prompt = template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        target_context=_safe(target_context),
        history_summary=_safe(_format_history(history_turns)),
        last_response=_safe(last_response),
        paper_context=_safe(paper_context),
    )
    return codex_exec(prompt, log_tag=f"orchestrate_{target_id}")


def discover_topics(
    *,
    target_id: str,
    target_title: str,
    full_transcript: str,
    board_content: str,
) -> CodexResult:
    """Ask codex for adjacent topic candidates. Returns CodexResult with parsed payload."""
    template = (PROMPTS_DIR / "topic_discovery.txt").read_text(encoding="utf-8")
    prompt = template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        full_transcript=_safe(full_transcript),
        board_content=_safe(board_content),
    )
    return codex_exec(prompt, log_tag=f"discover_{target_id}", timeout=900)


def main() -> int:
    """Tiny CLI for smoke-testing the codex driver."""
    import argparse

    parser = argparse.ArgumentParser(description="codex orchestrator smoke test")
    parser.add_argument("prompt_file", help="path to a prompt file to feed codex")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    args = parser.parse_args()

    prompt = Path(args.prompt_file).read_text(encoding="utf-8")
    result = codex_exec(prompt, timeout=args.timeout, log_tag="smoke")
    print(json.dumps({"ok": result.ok, "rc": result.rc, "parsed_keys": list(result.parsed)}, indent=2))
    if result.error:
        print(f"error: {result.error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

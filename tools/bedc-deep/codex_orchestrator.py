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
DEFAULT_CODEX_MODELS = "gpt-5.5,gpt-5.4,gpt-5.2,gpt-5.4-mini"
DEFAULT_CODEX_REASONING_EFFORT = "high"


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
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    # Fallback: scan forward from each '{' looking for a balanced JSON object
    # that parses. Robust against prose-embedded braces (e.g. math subscripts
    # like _{l,u}) that would defeat a naive first-{-to-last-} substring.
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
                    candidate = text[start : i + 1]
                    try:
                        return json.loads(candidate)
                    except json.JSONDecodeError:
                        break
    return None


def _codex_models() -> list[str]:
    raw = os.environ.get("BEDC_CODEX_MODELS") or os.environ.get("BEDC_CODEX_MODEL") or DEFAULT_CODEX_MODELS
    models: list[str] = []
    seen: set[str] = set()
    for item in raw.split(","):
        model = item.strip()
        if model and model not in seen:
            models.append(model)
            seen.add(model)
    return models or [DEFAULT_CODEX_MODELS.split(",", 1)[0]]


def _is_model_limit_error(text: str) -> bool:
    low = (text or "").lower()
    return "usage limit" in low or "switch to another model" in low


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

    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    effort = os.environ.get("BEDC_CODEX_REASONING_EFFORT", DEFAULT_CODEX_REASONING_EFFORT).strip()
    attempts: list[tuple[str, str, str, int]] = []
    stdout = ""
    stderr = ""
    rc: int = -1

    for model in _codex_models():
        cmd = [
            CODEX_PATH,
            "exec",
            "--model",
            model,
        ]
        if effort:
            cmd += ["-c", f"model_reasoning_effort={json.dumps(effort)}"]
        cmd += [
            "--sandbox",
            "read-only",
            "--json",
            "-C",
            str(REPO_ROOT),
            "-o",
            str(output_file),
            "-",
        ]
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
        model_stdout = ""
        model_stderr = ""
        model_rc: int = -1
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
            model_stdout, model_stderr = proc.communicate(input=prompt, timeout=timeout + 30)
            model_rc = proc.returncode
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, 9)
            except ProcessLookupError:
                pass
            try:
                model_stdout, model_stderr = proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                model_stdout = model_stdout or ""
                model_stderr = model_stderr or ""
            model_rc = -9
        finally:
            watchdog.cancel()
        if hard_killed["flag"] and model_rc == 0:
            # communicate returned 0 because the watchdog kill caused EOF on
            # the pipes, but the run exceeded its budget; demote to timeout.
            model_rc = -9

        attempts.append((model, model_stdout or "", model_stderr or "", model_rc))
        stdout = model_stdout or ""
        stderr = model_stderr or ""
        rc = model_rc
        if model_rc == 0:
            break
        if not _is_model_limit_error((model_stdout or "") + "\n" + (model_stderr or "")):
            break

    stdout_file.write_text(
        "\n".join(f"### model={model} rc={model_rc}\n{out}" for model, out, _err, model_rc in attempts),
        encoding="utf-8",
    )
    stderr_file.write_text(
        "\n".join(f"### model={model} rc={model_rc}\n{err}" for model, _out, err, model_rc in attempts),
        encoding="utf-8",
    )

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






def _fallback_oracle_directive(history_turns: list[dict]) -> str:
    """Generic fallback when codex can't produce a tailored directive."""
    n = len(history_turns)
    return (
        f"延续上一轮的最强结论, 把它的 weakest link 重做为带前提最小化的引理, "
        f"前提直接对应 BEDC 已有 setup field. 编号继续从 #{n + 1} 开始递增, "
        f"禁止重复本对话此前已产出的内容。"
    )


# ---------------------------------------------------------------------------
# Oracle-loop terminator: decide when oracle has produced enough to close
# the target. Replaces the old progress_delta gate.
# ---------------------------------------------------------------------------


def evaluate_oracle_done(
    *,
    target_id: str,
    target_title: str,
    target_object: str,
    history_turns: list[dict],
    last_response: str,
) -> CodexResult:
    """Codex inspects the latest oracle turn and decides done/continue/escalate.

    Returns a CodexResult with parsed payload:
      {
        "verdict": "done" | "continue" | "escalate",
        "reason": "...",
        "next_directive": "...",   # when continue
        "publishable_summary": "..." # when done
      }

    On infrastructure failure, returns CodexResult.ok=False; caller should
    treat as "continue" with a fallback directive (avoid prematurely closing
    or escalating on transient errors).
    """
    template = (PROMPTS_DIR / "codex_oracle_done_check.txt").read_text(encoding="utf-8")
    prompt = template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        target_object=_safe(target_object),
        history_summary=_safe(_format_history(history_turns)),
        last_response=_safe(last_response[:8000]),
    )
    return codex_exec(prompt, log_tag=f"oracle_done_{target_id}", timeout=240)



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

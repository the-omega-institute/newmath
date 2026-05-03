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
    """Ask codex for the next-turn JSON. Returns CodexResult with parsed payload.

    Legacy interface — used by the old verdict-gated Stage 1 loop. New
    oracle track invocations should use build_oracle_followup_directive()
    below, which returns just the directive string for embedding in the
    short oracle_followup template (no progress_delta scoring).
    """
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


# ---------------------------------------------------------------------------
# Dynamic oracle follow-up directive (new oracle track)
# ---------------------------------------------------------------------------

# Codex picks one of these directives based on last_response content. The
# selection itself is what codex decides; we provide the menu shape so the
# selection is grounded, not free-form.
_FOLLOWUP_DIRECTIVE_MENU = """
Pick the directive from this menu that best matches the last oracle response,
and rewrite it concretely with object names from that response (do NOT echo
generic placeholders like "the obstruction" — substitute the actual named
construct):

  D1: 把上一条 #{N} 的 weakest link 重做为带前提最小化的引理, 前提应直接对应 BEDC 现有 setup field
  D2: 以你提出的 {obstruction_name} 为坏例子结构, 给出该 obstruction 的判别定理或反例的有限分类
  D3: 把 #{a}-#{b} 这一系列结果整合为一个主定理 + 推论链, 附依赖图, 对每个 lemma 给出最强可证版本
  D4: 为 #{N} 给出一个 finite countermodel, 验证其前提是必要的; 并把否定的版本陈述为不可实现性定理
  D5: 你给的 outline 已足够, 请把它形式化为可直接进入 papers/bedc/parts 的完整证明 (最小依赖、最强陈述, 编号继续递增)
  D6: 上一条结论已经很强, 请用同一框架在邻近对象上证明 counterpart 定理 (例如把 LatticeUp 上的结论搬到 PosetUp 或反过来)
  D7: 上一条没新增数学内容, 是同义改写或弱化版. 你必须放弃这条思路, 转向 {alternative_anchor} 重新立论

Return ONLY the rewritten directive string (no JSON, no preamble, no choice
label). 1-3 sentences max. Embed the actual named objects from the last
response so the oracle has a concrete next step.
"""


def build_oracle_followup_directive(
    *,
    target_id: str,
    target_title: str,
    history_turns: list[dict],
    last_response: str,
) -> str:
    """Ask codex to pick + rewrite a follow-up directive based on the last
    oracle response. Returns the directive string ready to embed in the
    oracle_followup.txt template's {specific_directive} slot.

    Falls back to a generic directive if codex is unavailable, so the oracle
    loop never starves on infrastructure failures.
    """
    instructions = (
        f"Target id: {target_id}\n"
        f"Target title: {target_title}\n\n"
        f"History turn summaries (oldest first):\n{_format_history(history_turns)}\n\n"
        f"Last oracle response (full text):\n{_safe(last_response)[:8000]}\n\n"
        f"{_FOLLOWUP_DIRECTIVE_MENU}\n"
    )
    cr = codex_exec(instructions, log_tag=f"oracle_followup_{target_id}", timeout=240)
    if not cr.ok:
        return _fallback_oracle_directive(history_turns)
    raw = (cr.raw_output or "").strip()
    # Strip any leading "D1:" / "D7:" labels codex may include
    raw = re.sub(r"^\s*D\d+\s*:\s*", "", raw)
    if not raw or len(raw) > 800:
        return _fallback_oracle_directive(history_turns)
    return raw


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

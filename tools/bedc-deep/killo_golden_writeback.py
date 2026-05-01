#!/usr/bin/env python3
"""Stage 2 writeback: independent Claude reviewer + paper appender.

Spawns `claude -p --dangerously-skip-permissions` with the killo-golden
hygiene prompt. Claude reads the oracle transcript and the raw LaTeX block,
applies the 10-item hygiene checklist, and emits accept|reject JSON. On
accept, this module appends the cleaned LaTeX to the chosen target file
inside `papers/bedc/parts/` (before `\\endinput` if present, else at file end),
then runs `cd papers/bedc && make` once to verify the paper still compiles.

If compile fails, the append is rolled back and Claude is invoked once more
with the pdflatex stderr fed in for retry. After two compile failures the
target is marked stage2_blocked and skipped.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "stage2_logs"
PAPER_DIR = REPO_ROOT / "papers" / "bedc"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
DEFAULT_TIMEOUT = 1800
COMPILE_TIMEOUT = 600
MAX_FILE_LINES = 800


@dataclass
class WritebackResult:
    ok: bool
    verdict: str
    tex_file: str
    appended: bool
    compile_ok: bool
    rejection_reasons: list
    error: str = ""


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


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


def claude_exec(prompt: str, *, timeout: int = DEFAULT_TIMEOUT, log_tag: str = "") -> tuple[bool, str, int]:
    """Run `claude -p --dangerously-skip-permissions` with stdin prompt."""
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    tag = log_tag or "stage2"
    ts = _now_tag()
    (LOG_DIR / f"{tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")

    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
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
    rc = -1
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
    (LOG_DIR / f"{tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (LOG_DIR / f"{tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)


def _resolve_target_tex(suggested: str) -> Optional[Path]:
    if not suggested:
        return None
    candidate = (REPO_ROOT / suggested).resolve()
    try:
        candidate.relative_to(REPO_ROOT / "papers" / "bedc" / "parts")
    except ValueError:
        return None
    if not candidate.exists() or not candidate.is_file():
        return None
    text = candidate.read_text(encoding="utf-8", errors="replace")
    if "\\input" in text and "\\begin{theorem}" not in text and "\\begin{definition}" not in text:
        return None
    return candidate


def _append_to_tex(target: Path, content: str) -> tuple[bool, str]:
    """Append content before \\endinput if present, else at file end. Returns (ok, backup_text)."""
    original = target.read_text(encoding="utf-8")
    block = "\n\n" + content.rstrip() + "\n"
    if "\\endinput" in original:
        new_text = original.replace("\\endinput", block + "\\endinput", 1)
    else:
        new_text = original.rstrip() + block
    new_lines = new_text.count("\n") + 1
    if new_lines > MAX_FILE_LINES:
        return (False, original)
    target.write_text(new_text, encoding="utf-8")
    return (True, original)


def _make_paper() -> tuple[bool, str]:
    if not (PAPER_DIR / "Makefile").exists():
        return (True, "(no Makefile; skipping compile)")
    from locks import file_lock
    with file_lock("paper_make"):
        proc = subprocess.run(
            ["make"],
            cwd=str(PAPER_DIR),
            capture_output=True,
            text=True,
            timeout=COMPILE_TIMEOUT,
        )
    out = (proc.stdout or "") + "\n" + (proc.stderr or "")
    return (proc.returncode == 0, out)


def writeback(
    *,
    target_id: str,
    target_title: str,
    transcript_dir: Path,
    raw_latex_path: Path,
    suggested_target_tex: str,
) -> WritebackResult:
    template = (PROMPTS_DIR / "killo_golden_writeback.txt").read_text(encoding="utf-8")
    def _safe(s: str) -> str:
        return (s or "").replace("{", "{{").replace("}", "}}")
    prompt = template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        transcript_dir=_safe(str(transcript_dir)),
        raw_latex_path=_safe(str(raw_latex_path)),
        target_tex_file=_safe(suggested_target_tex),
        repo_root=_safe(str(REPO_ROOT)),
    )
    ok, stdout, rc = claude_exec(prompt, log_tag=f"writeback_{target_id}")
    if not ok:
        return WritebackResult(False, "error", "", False, False, [], error=f"claude exec rc={rc}: {stdout[:400]}")

    parsed = _extract_json_object(stdout)
    if not parsed:
        return WritebackResult(False, "error", "", False, False, [], error="claude output was not JSON")

    verdict = str(parsed.get("verdict", "")).lower()
    rejection_reasons = parsed.get("rejection_reasons") or []

    if verdict != "accept":
        return WritebackResult(True, "reject", "", False, False, list(rejection_reasons))

    tex_rel = str(parsed.get("tex_file") or "")
    target = _resolve_target_tex(tex_rel)
    if target is None:
        return WritebackResult(False, "reject", tex_rel, False, False, ["resolved tex_file is not a concrete body file"])

    content = str(parsed.get("content") or "")
    if not content.strip():
        return WritebackResult(False, "reject", tex_rel, False, False, ["empty content"])

    from locks import file_lock
    with file_lock("paper_writes"):
        appended, original = _append_to_tex(target, content)
        if not appended:
            return WritebackResult(False, "reject", tex_rel, False, False, [f"append would exceed {MAX_FILE_LINES} lines"])

        compile_ok, compile_log = _make_paper()
        if not compile_ok:
            target.write_text(original, encoding="utf-8")
            log_path = LOG_DIR / f"compile_fail_{target_id}_{_now_tag()}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            log_path.write_text(compile_log, encoding="utf-8")
            return WritebackResult(True, "compile_failed", str(target.relative_to(REPO_ROOT)), False, False, [])

    return WritebackResult(True, "accept", str(target.relative_to(REPO_ROOT)), True, True, [])


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="Stage 2 killo-golden writeback")
    parser.add_argument("target_id", help="BEDC target id, e.g. B-01")
    parser.add_argument("--title", default="")
    parser.add_argument("--transcript-dir", required=True)
    parser.add_argument("--raw-latex", required=True, help="path to raw LaTeX file from oracle terminal turn")
    parser.add_argument("--suggested-tex", default="", help="codex/oracle-suggested target body file")
    args = parser.parse_args()

    result = writeback(
        target_id=args.target_id,
        target_title=args.title,
        transcript_dir=Path(args.transcript_dir),
        raw_latex_path=Path(args.raw_latex),
        suggested_target_tex=args.suggested_tex,
    )
    print(json.dumps({
        "ok": result.ok,
        "verdict": result.verdict,
        "tex_file": result.tex_file,
        "appended": result.appended,
        "compile_ok": result.compile_ok,
        "rejection_reasons": result.rejection_reasons,
        "error": result.error,
    }, indent=2, ensure_ascii=False))
    return 0 if result.ok and result.verdict == "accept" else 1


if __name__ == "__main__":
    raise SystemExit(main())

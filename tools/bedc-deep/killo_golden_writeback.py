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
    # On verdict=="compile_failed", carries a compact extract of pdflatex's
    # real error lines (Undefined control seq / Missing / Extra etc.) so
    # the runtime can feed them as rejection_reasons to codex corrective.
    compile_errors: list = None  # type: ignore
    closure_candidate: dict = None  # type: ignore


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


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


def claude_exec(prompt: str, *, timeout: int = DEFAULT_TIMEOUT, log_tag: str = "") -> tuple[bool, str, int]:
    """Run `claude -p --dangerously-skip-permissions` with stdin prompt."""
    if os.environ.get("BEDC_DISABLE_CLAUDE"):
        return (False, "claude disabled by BEDC_DISABLE_CLAUDE", -2)
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    tag = log_tag or "stage2"
    ts = _now_tag()
    (LOG_DIR / f"{tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")

    cmd = [
        CLAUDE_PATH, "-p", "--dangerously-skip-permissions",
        # Tools so claude can verify autoref existence, look up adjacent
        # relation usage style, and check the target file's neighborhood.
        # Edit/Write withheld — claude proposes content via JSON output,
        # the Python writeback() does the actual file mutation.
        "--allowed-tools",
        "Read,Grep,Glob,Bash(grep:*),Bash(find:*),Bash(wc:*),Bash(ls:*)",
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


def codex_json_fallback(
    prompt: str,
    *,
    timeout: int = DEFAULT_TIMEOUT,
    log_tag: str = "",
    role_note: str = "Claude is unavailable for this BEDC gate.",
) -> tuple[bool, dict, str, str]:
    """Run an independent read-only Codex JSON gate when Claude is unavailable."""
    import codex_orchestrator

    fallback_prompt = (
        f"{role_note}\n"
        "Act as the independent fallback checker for this gate. Preserve the "
        "same acceptance standard and return only the JSON object required by "
        "the original prompt. Do not edit files.\n\n"
        f"{prompt}"
    )
    tag = (log_tag or "stage2") + "_codex_fallback"
    result = codex_orchestrator.codex_exec(
        fallback_prompt,
        timeout=timeout,
        log_tag=tag,
    )
    if not result.ok:
        return (False, {}, result.raw_output, result.error or f"codex rc={result.rc}")
    parsed = result.parsed or _extract_json_object(result.raw_output) or {}
    if not parsed:
        return (False, {}, result.raw_output, "codex fallback output was not JSON")
    return (True, parsed, result.raw_output, "")


def _all_paper_labels() -> set[str]:
    """Return all \\label{X} values from papers/bedc/parts/**/*.tex.

    Recomputed each call (~500ms). We do not cache because pipeline
    writebacks append content to existing .tex files without updating
    parent-dir mtime, so cache invalidation is unreliable. Per-call
    cost is acceptable: writebacks happen every 5-10 min.
    """
    parts = REPO_ROOT / "papers" / "bedc" / "parts"
    if not parts.exists():
        return set()
    labels: set[str] = set()
    for path in parts.rglob("*.tex"):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        labels.update(re.findall(r"\\label\{([^}]+)\}", text))
    return labels


def _detect_dangling_autorefs(content: str) -> list[str]:
    """Return list of \\autoref{X} / \\ref{X} citations whose label is
    not present anywhere in papers/bedc/parts/. Excludes refs to labels
    defined IN the candidate content itself (forward refs within the
    new block are valid)."""
    cited = set(re.findall(r"\\autoref\{([^}]+)\}", content))
    cited.update(re.findall(r"(?<!\\auto)\\ref\{([^}]+)\}", content))
    if not cited:
        return []
    own_labels = set(re.findall(r"\\label\{([^}]+)\}", content))
    cited -= own_labels
    paper_labels = _all_paper_labels()
    missing = sorted(cited - paper_labels)
    return missing


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
    """Append content before \\endinput if present, else at file end. Returns (ok, backup_text).

    Atomic write via temp + replace so a crash mid-write never leaves the
    paper file truncated."""
    original = target.read_text(encoding="utf-8")
    block = "\n\n" + content.rstrip() + "\n"
    if "\\endinput" in original:
        new_text = original.replace("\\endinput", block + "\\endinput", 1)
    else:
        new_text = original.rstrip() + block
    new_lines = new_text.count("\n") + 1
    if new_lines > MAX_FILE_LINES:
        return (False, original)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(new_text, encoding="utf-8")
    tmp.replace(target)
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
    """Stage 2 writeback with auto-normalize first, claude review second.

    Pipeline order (per project decision: hygiene fixes itself, doesn't reject):
      1. Read raw content from raw_latex_path
      2. Run hygiene_normalize.normalize() — mechanical fixes for `\\(\\)`/
         `\\mathsf{X}`/QED/sectioning/iteration vocab/`\\ref` etc.
      3. Write normalized content back to raw_latex_path (so next attempt
         sees fixed content)
      4. If hygiene_normalize reported `blocking_issues` (no theorem env,
         unbalanced begin/end, Chinese chars, etc.), claude reviews. These
         are the ONLY concerns claude judges now — not hygiene minutiae.
      5. If no blocking issues: bypass claude review entirely. Atomically
         append + run `make`. compile failure = automatic reject (rolled
         back). compile success = accept.
    """
    import hygiene_normalize

    raw_text = raw_latex_path.read_text(encoding="utf-8") if raw_latex_path.exists() else ""

    # Extract the LaTeX block from raw_text. Oracle output may have
    # surrounding prose / `Insertion target:` line. We split before
    # normalizing.
    fenced = re.search(r"```(?:latex)?\s*(.*?)```", raw_text, re.DOTALL)
    if fenced:
        latex_body = fenced.group(1)
    else:
        # Heuristic: take from first \begin{theorem|lemma|...} to last \end of same.
        first = re.search(r"\\begin\{(?:theorem|lemma|proposition|corollary|definition)\}", raw_text)
        if first:
            latex_body = raw_text[first.start():]
        else:
            latex_body = raw_text

    # ── Step 1-3: auto-normalize ──
    norm = hygiene_normalize.normalize(
        latex_body,
        preamble_path=REPO_ROOT / "papers" / "bedc" / "preamble.tex",
    )

    # Persist normalized content back so corrective retries (or human
    # inspection) see the fixed version.
    if norm.changed:
        # Replace the LaTeX block in raw_text, preserving any surrounding
        # `Insertion target:` line.
        if fenced:
            new_raw = raw_text.replace(fenced.group(0),
                                        f"```latex\n{norm.content}\n```")
        else:
            # If we extracted by env-detect, only persist if difference is meaningful
            new_raw = norm.content if not raw_text.endswith(latex_body) else \
                      raw_text[: -len(latex_body)] + norm.content
        try:
            raw_latex_path.write_text(new_raw, encoding="utf-8")
        except OSError:
            pass

    # ── Step 3.5: scan for dangling \autoref / \ref ──
    # This is repo-aware (needs to grep all paper labels), so it lives
    # here rather than inside hygiene_normalize. Missing refs ALWAYS
    # force the claude review path so the gate has a chance to either
    # fix typos via Grep or reject with a precise rejection reason.
    dangling_refs = _detect_dangling_autorefs(norm.content)
    extra_blocking_issues: list[str] = []
    if dangling_refs:
        extra_blocking_issues.append(
            "dangling autoref(s): the following \\autoref / \\ref citations "
            "have no \\label{X} anywhere under papers/bedc/parts/: "
            + ", ".join(dangling_refs[:8])
            + (f" (and {len(dangling_refs) - 8} more)" if len(dangling_refs) > 8 else "")
        )

    # ── Step 4: claude review when blocking issues remain ──
    # Blocking issues are things normalize cannot mechanically fix:
    # missing environment, unbalanced begin/end, Chinese chars, dangling
    # autorefs, BEDC-relation-as-function misuses, transport-without-citation.
    rejection_reasons: list[str] = []
    all_blocking = list(norm.blocking_issues) + extra_blocking_issues
    if all_blocking:
        # Heavy review path: blocking issue exists, ask claude to assess
        # whether content is salvageable or needs to escalate.
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
        # Append the normalize report so claude knows what's already been
        # mechanically fixed and only sees the residual issues.
        prompt += "\n\n## Auto-normalize report (already applied)\n"
        for t in norm.transformations:
            prompt += f"- {t}\n"
        prompt += "\n## Blocking issues (require your judgement)\n"
        for b in all_blocking:
            prompt += f"- {b}\n"
        log_tag = f"writeback_{target_id}"
        ok, stdout, rc = claude_exec(prompt, log_tag=log_tag)
        if not ok:
            fallback_ok, parsed, fallback_stdout, fallback_error = codex_json_fallback(
                prompt,
                log_tag=log_tag,
                role_note=(
                    "Claude is unavailable for the BEDC killo-golden writeback "
                    "gate; run the same hygiene and safety gate as an independent "
                    "Codex fallback."
                ),
            )
            if not fallback_ok:
                return WritebackResult(False, "error", "", False, False, [],
                                        error=(
                                            f"claude exec rc={rc}: {stdout[:400]}; "
                                            f"codex fallback: {fallback_error[:400]}"
                                        ))
            stdout = fallback_stdout
        else:
            parsed = _extract_json_object(stdout)
        if not parsed:
            fallback_ok, parsed, fallback_stdout, fallback_error = codex_json_fallback(
                prompt,
                log_tag=log_tag,
                role_note=(
                    "Claude returned non-JSON for the BEDC killo-golden writeback "
                    "gate; run the same hygiene and safety gate as an independent "
                    "Codex fallback."
                ),
            )
            if not fallback_ok:
                return WritebackResult(False, "error", "", False, False, [],
                                        error=f"claude output was not JSON; codex fallback: {fallback_error[:400]}")
            stdout = fallback_stdout
        verdict = str(parsed.get("verdict", "")).lower()
        rejection_reasons = parsed.get("rejection_reasons") or []
        if verdict != "accept":
            return WritebackResult(True, "reject", "", False, False, list(rejection_reasons))
        # Use claude's content (might have additional cleanup) if present.
        content = str(parsed.get("content") or norm.content)
        tex_rel = str(parsed.get("tex_file") or suggested_target_tex)
    else:
        # Fast path: normalize handled everything, go straight to append+make.
        # The suggested_target_tex from upstream (codex track or oracle) is
        # used as the destination. claude is bypassed entirely.
        content = norm.content
        tex_rel = suggested_target_tex

    # ── Step 5: atomic append + make verify ──

    target = _resolve_target_tex(tex_rel)
    if target is None:
        return WritebackResult(False, "reject", tex_rel, False, False,
                                ["resolved tex_file is not a concrete body file"])

    if not content.strip():
        return WritebackResult(False, "reject", tex_rel, False, False, ["empty content"])

    from locks import file_lock
    with file_lock("paper_writes"):
        appended, original = _append_to_tex(target, content)
        if not appended:
            return WritebackResult(False, "reject", tex_rel, False, False, [f"append would exceed {MAX_FILE_LINES} lines"])

        compile_ok, compile_log = _make_paper()
        if not compile_ok:
            tmp = target.with_suffix(target.suffix + ".rollback.tmp")
            tmp.write_text(original, encoding="utf-8")
            tmp.replace(target)
            log_path = LOG_DIR / f"compile_fail_{target_id}_{_now_tag()}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            log_path.write_text(compile_log, encoding="utf-8")
            errors = _extract_compile_errors(compile_log)
            return WritebackResult(
                True, "compile_failed",
                str(target.relative_to(REPO_ROOT)),
                False, False, [],
                compile_errors=errors,
            )

    tex_result = str(target.relative_to(REPO_ROOT))
    closure_review: dict = {}
    try:
        import closure_candidate

        closure_review = closure_candidate.analyze(
            target_id=target_id,
            target_title=target_title,
            tex_file=tex_result,
            appended_content=content,
        )
    except Exception as exc:
        closure_review = {
            "ok": False,
            "action": "error",
            "error": f"closure_candidate failed: {exc}",
        }

    return WritebackResult(True, "accept", tex_result, True, True, [], closure_candidate=closure_review)


def _extract_compile_errors(compile_log: str) -> list[str]:
    """Pluck real pdflatex errors out of the noisy compile log.

    Returns a deduplicated list of error lines + their line context (`l.NNN`
    line) suitable to feed back to codex as rejection_reasons. Filters out
    Overfull/Underfull hbox warnings and font diagnostics that aren't real
    errors."""
    if not compile_log:
        return []
    out: list[str] = []
    seen: set[str] = set()
    lines = compile_log.splitlines()
    skip_prefixes = (
        "Overfull \\hbox", "Underfull \\hbox", "Overfull \\vbox", "Underfull \\vbox",
        "LaTeX Font Warning",
    )
    for i, line in enumerate(lines):
        stripped = line.strip()
        if not stripped.startswith("!"):
            continue
        # Skip font-related ! diagnostics (those long OML/lmm lines)
        if any(s in line for s in ("OML/lmm", "OT1/lmr", "OMS/lmsy", "OMX/lmex")):
            continue
        if any(stripped.startswith(p) for p in skip_prefixes):
            continue
        # Get the next 1-2 lines for context (often `l.NNN ...` location)
        ctx = []
        for j in range(i + 1, min(i + 3, len(lines))):
            cl = lines[j].strip()
            if cl.startswith("l.") or "Undefined" in cl or "Missing" in cl:
                ctx.append(cl[:200])
        msg = (stripped + " | " + " ; ".join(ctx))[:400]
        if msg not in seen:
            seen.add(msg)
            out.append(msg)
            if len(out) >= 8:  # cap; codex doesn't need 50 errors
                break
    return out


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
        "closure_candidate": result.closure_candidate or {},
    }, indent=2, ensure_ascii=False))
    return 0 if result.ok and result.verdict == "accept" else 1


if __name__ == "__main__":
    raise SystemExit(main())

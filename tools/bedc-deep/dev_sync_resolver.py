#!/usr/bin/env python3
"""dev_sync_resolver — auto-merge origin/dev with claude-driven conflict resolution.

Replaces the supervisor's bare `git_sync_dev` (which aborted on any conflict)
with a flow that:

  1. Acquire paper_writes lock so Stage 2 append never races with the merge
  2. fetch origin/dev
  3. attempt git merge --no-edit origin/dev
     ├─ ff success → commit + push
     └─ conflict:
        a. capture conflict files + hunks
        b. spawn claude with project conventions + each conflict block
        c. apply claude's resolved content
        d. validation gauntlet (lake build / check-axioms / bedc_ci audit)
        e. hard reset on any failure; commit + push on full pass

Hard rules:
- Never auto-resolves conflicts in lean4/ (those go to human_inbox)
- Always validates with project's CI gates before commit
- On any validation failure, git reset --hard ORIG_HEAD (back to pre-merge)
- All git ops happen under paper_writes lock so Stage 2 sees a consistent tree
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
LOG_DIR = SCRIPT_DIR / "state" / "dev_sync_logs"
PROMPTS_DIR = SCRIPT_DIR / "prompts"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
CLAUDE_RESOLVE_TIMEOUT = 1800   # 30 minutes for whole resolution
CLAUDE_RESOLVE_PER_FILE_TIMEOUT = 600

VALIDATION_TIMEOUTS = {
    "lake": 600,
    "check_axioms": 60,
    "bedc_ci": 120,
}

# Files we will NOT auto-resolve. Anything in lean4/ is too high stakes;
# papers/bedc/main.tex / preamble.tex / Makefile etc. are infra files
# that need human review.
PROTECTED_PATTERNS = [
    re.compile(r"^lean4/"),
    re.compile(r"^papers/bedc/main\.tex$"),
    re.compile(r"^papers/bedc/preamble\.tex$"),
    re.compile(r"^papers/bedc/Makefile$"),
    re.compile(r"^\.github/"),
    re.compile(r"^lakefile\.lean$"),
    re.compile(r"^lake-manifest\.json$"),
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_iso() -> str:
    return datetime.now().isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _git(args: list[str], capture: bool = True, check: bool = False, timeout: int = 30) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args],
        capture_output=capture,
        text=True,
        cwd=str(REPO_ROOT),
        timeout=timeout,
        check=check,
    )


def _is_protected(path: str) -> bool:
    return any(p.search(path) for p in PROTECTED_PATTERNS)


def _claude_exec(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    (LOG_DIR / f"{log_tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, cwd=str(REPO_ROOT), env=env, encoding="utf-8", errors="replace",
        start_new_session=True,
    )
    stdout = ""; stderr = ""; rc = -1
    hard_killed = {"flag": False}
    def _hard_kill() -> None:
        hard_killed["flag"] = True
        try: os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError): pass
    watchdog = threading.Timer(timeout + 60, _hard_kill); watchdog.daemon = True; watchdog.start()
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid, 9)
        except ProcessLookupError: pass
        try: stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""; stderr = stderr or ""
        rc = -9
    finally:
        watchdog.cancel()
    if hard_killed["flag"] and rc == 0:
        rc = -9
    (LOG_DIR / f"{log_tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (LOG_DIR / f"{log_tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)


# ---------------------------------------------------------------------------
# Conflict parsing
# ---------------------------------------------------------------------------


@dataclass
class ConflictFile:
    path: str
    has_protected: bool = False  # path matches PROTECTED_PATTERNS
    raw_content: str = ""        # current file content with conflict markers


def _conflicted_files() -> list[str]:
    """Return files in conflict state per `git diff --name-only --diff-filter=U`."""
    res = _git(["diff", "--name-only", "--diff-filter=U"], timeout=10)
    return [line.strip() for line in res.stdout.splitlines() if line.strip()]


def _read_conflict_file(path: str) -> ConflictFile:
    cf = ConflictFile(path=path, has_protected=_is_protected(path))
    full = REPO_ROOT / path
    try:
        cf.raw_content = full.read_text(encoding="utf-8", errors="replace")
    except OSError:
        cf.raw_content = ""
    return cf


# ---------------------------------------------------------------------------
# Claude conflict resolver
# ---------------------------------------------------------------------------


def _build_resolve_prompt(cf: ConflictFile, project_conventions: str) -> str:
    return f"""You are resolving a single git merge conflict in the BEDC pipeline's
auto-sync workflow. Output ONLY the fully-resolved file content — no markdown
fences, no explanation, no diff format. Pure file content that will replace
the conflicted version on disk.

Project conventions you MUST respect:
{project_conventions}

File path: {cf.path}

Current file content (with conflict markers `<<<<<<< HEAD`, `=======`,
`>>>>>>> origin/dev`):

{cf.raw_content}

Resolution rules:
1. PRESERVE BOTH SIDES' real mathematical content unless they are literal
   duplicates. If our side adds a theorem and dev's side adds a different
   theorem, KEEP BOTH (typically as adjacent blocks).
2. NEVER drop a `\\label{{...}}`, `\\leanchecked{{...}}`, or paper macro that
   appears on either side — those are load-bearing references.
3. If the conflict is a clean append on both sides (each side just appended
   different theorems to the same file end), the resolution is to put dev's
   appends FIRST, then our appends, separated by a blank line.
4. If the conflict spans the SAME theorem with different proofs, prefer the
   side with more cited dependencies / longer proof body / explicit
   `\\autoref` cross-references. Reject ad-hoc subscript notation if either
   side uses it (`\\sim_R`, `\\cdot_R`, etc.) and the other side uses
   parametrically named macros.
5. NEVER introduce iteration vocabulary ("we extend", "新增", "patch",
   "previously", "vNNN-", etc.).
6. Math delimiters: project uses `$...$` and `$$...$$` exclusively. Reject
   `\\(...\\)` / `\\[...\\]` if used and rewrite to `$ / $$`.
7. If you encounter a conflict you genuinely cannot resolve responsibly
   (semantic disagreement on definitions, contradictory constructions, etc.),
   output exactly the literal string `ABORT_CONFLICT` and nothing else.
   The supervisor will surface this conflict to human_inbox.

Output the resolved file content NOW, starting from the very first character
of the file. No preamble, no JSON, no markers. If you output ABORT_CONFLICT
that string must be the entire output and nothing else.
"""


def _project_conventions_blob() -> str:
    """Read CLAUDE.md + AGENTS.md + key sections of preamble.tex; condense."""
    parts = []
    for fname in ("CLAUDE.md", "AGENTS.md"):
        p = REPO_ROOT / fname
        if not p.exists():
            continue
        try:
            text = p.read_text(encoding="utf-8")
        except OSError:
            continue
        parts.append(f"# === {fname} ===\n{text[:6000]}\n")
    return "\n".join(parts)


def _resolve_one_conflict(cf: ConflictFile, project_conventions: str) -> tuple[bool, str]:
    """Returns (ok, error_msg). On ok=True, file has been overwritten with
    claude's resolved content."""
    prompt = _build_resolve_prompt(cf, project_conventions)
    log_tag = f"resolve_{cf.path.replace('/', '_')}"
    ok, stdout, rc = _claude_exec(
        prompt,
        timeout=CLAUDE_RESOLVE_PER_FILE_TIMEOUT,
        log_tag=log_tag,
    )
    if not ok:
        return (False, f"claude exec rc={rc}: {stdout[:200]}")

    resolved = (stdout or "").strip()
    if not resolved:
        return (False, "claude returned empty resolution")
    if resolved == "ABORT_CONFLICT":
        return (False, "claude declared ABORT_CONFLICT (cannot responsibly resolve)")

    # Defensive: ensure no conflict markers remain in claude's output
    if any(m in resolved for m in ("<<<<<<< HEAD", "=======", ">>>>>>> origin/dev")):
        return (False, "claude output still contains conflict markers")

    target_path = REPO_ROOT / cf.path
    try:
        # Atomic write
        tmp = target_path.with_suffix(target_path.suffix + ".tmp")
        tmp.write_text(resolved, encoding="utf-8")
        tmp.replace(target_path)
    except OSError as exc:
        return (False, f"failed to write resolved file: {exc}")

    # Stage the resolved file
    add_res = _git(["add", cf.path], timeout=10)
    if add_res.returncode != 0:
        return (False, f"git add failed: {add_res.stderr[:200]}")

    return (True, "")


# ---------------------------------------------------------------------------
# Validation gauntlet
# ---------------------------------------------------------------------------


@dataclass
class ValidationResult:
    passed: bool
    failures: list[str] = field(default_factory=list)
    summary: str = ""


def _validate_post_resolution() -> ValidationResult:
    """Run the project's CI gates. Returns pass/fail + which gate failed.

    Note: pdflatex is NOT in the gauntlet here — it's slow and Stage 2 will
    catch any compile breakage on its next append cycle, then roll back."""
    failures: list[str] = []

    # Lake build (Lean correctness)
    try:
        proc = subprocess.run(
            ["lake", "build"],
            cwd=str(REPO_ROOT / "lean4"),
            capture_output=True,
            text=True,
            timeout=VALIDATION_TIMEOUTS["lake"],
        )
        if proc.returncode != 0:
            tail = (proc.stdout or "")[-1500:] + (proc.stderr or "")[-500:]
            failures.append(f"lake build failed:\n{tail}")
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        failures.append(f"lake build infra error: {exc}")

    # Axiom audit
    try:
        proc = subprocess.run(
            ["python3", "tools/check-axioms.py"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=VALIDATION_TIMEOUTS["check_axioms"],
        )
        if proc.returncode != 0:
            failures.append(f"check-axioms failed:\n{(proc.stdout or '')[-800:]}")
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        failures.append(f"check-axioms infra error: {exc}")

    # bedc_ci audit
    try:
        proc = subprocess.run(
            ["python3", "lean4/scripts/bedc_ci.py", "audit"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=VALIDATION_TIMEOUTS["bedc_ci"],
        )
        if proc.returncode != 0:
            failures.append(f"bedc_ci audit failed:\n{(proc.stdout or '')[-800:]}")
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        failures.append(f"bedc_ci audit infra error: {exc}")

    summary = "all 3 gates passed" if not failures else f"{len(failures)} gate(s) failed"
    return ValidationResult(passed=not failures, failures=failures, summary=summary)


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


@dataclass
class SyncResult:
    """Outcome of a single sync attempt."""
    status: str  # "up_to_date" | "ff_merged" | "auto_resolved" | "aborted_protected" | "aborted_validation" | "skipped_dirty" | "error"
    n_dev_commits: int = 0
    conflict_files: list[str] = field(default_factory=list)
    resolved_files: list[str] = field(default_factory=list)
    failed_files: list[dict] = field(default_factory=list)
    validation: Optional[ValidationResult] = None
    branch: str = ""
    error: str = ""


def sync_with_resolution(allowed_branch: str = "bedc-claim-packet-pipeline") -> SyncResult:
    """Fetch + merge origin/dev with claude-driven conflict resolution.

    This is the supervisor's main hook. Locks paper_writes to keep Stage 2
    consistent throughout merge + validate + commit + push.
    """
    branch_res = _git(["branch", "--show-current"], timeout=5)
    branch = branch_res.stdout.strip()
    if branch != allowed_branch:
        return SyncResult(
            status="error",
            branch=branch,
            error=f"branch {branch!r} != {allowed_branch!r}; refusing to act",
        )

    # Pre-flight: must be on clean working tree (we hold the lock during
    # the entire flow, so anything dirty here means human-driven changes
    # we shouldn't touch).
    from locks import file_lock
    with file_lock("paper_writes"):
        status_res = _git(["status", "--porcelain"], timeout=10)
        if status_res.stdout.strip():
            return SyncResult(status="skipped_dirty", branch=branch,
                               error="working tree dirty; sync deferred")

        # Fetch
        fetch_res = _git(["fetch", "origin", "dev"], capture=False, timeout=30)
        if fetch_res.returncode != 0:
            return SyncResult(status="error", branch=branch,
                               error="git fetch origin dev failed")

        # Count incoming commits
        behind_res = _git(["rev-list", "--count", "HEAD..origin/dev"], timeout=10)
        n_behind = int((behind_res.stdout.strip() or "0"))
        if n_behind == 0:
            return SyncResult(status="up_to_date", branch=branch)

        # Attempt merge
        merge_res = _git(["merge", "--no-edit", "origin/dev"], timeout=120)
        if merge_res.returncode == 0:
            # FF or clean merge succeeded; push.
            push_res = _git(["push", "origin", branch], capture=False, timeout=60)
            if push_res.returncode != 0:
                return SyncResult(
                    status="error", branch=branch, n_dev_commits=n_behind,
                    error=f"clean merge but push failed rc={push_res.returncode}",
                )
            return SyncResult(status="ff_merged", branch=branch, n_dev_commits=n_behind)

        # Conflict path
        conflicts = _conflicted_files()
        if not conflicts:
            # Merge failed without classic conflicts (rare). Abort to ORIG_HEAD.
            _git(["merge", "--abort"], capture=False, timeout=10)
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                error="merge failed without listed conflicts",
            )

        # Check for protected paths — abort if any
        protected = [p for p in conflicts if _is_protected(p)]
        if protected:
            _git(["merge", "--abort"], capture=False, timeout=10)
            return SyncResult(
                status="aborted_protected", branch=branch, n_dev_commits=n_behind,
                conflict_files=conflicts,
                error=f"protected files in conflict: {protected}; aborted, route to human_inbox",
            )

        # Resolve each conflict via claude
        project_conventions = _project_conventions_blob()
        resolved: list[str] = []
        failed: list[dict] = []
        for path in conflicts:
            cf = _read_conflict_file(path)
            ok, err = _resolve_one_conflict(cf, project_conventions)
            if ok:
                resolved.append(path)
            else:
                failed.append({"path": path, "error": err})

        if failed:
            _git(["merge", "--abort"], capture=False, timeout=10)
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                conflict_files=conflicts, resolved_files=resolved, failed_files=failed,
                error=f"{len(failed)} file(s) could not be resolved; merge aborted",
            )

        # All conflicts resolved + staged; run validation
        validation = _validate_post_resolution()
        if not validation.passed:
            # Abort merge by hard reset (since we already staged files)
            _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
            return SyncResult(
                status="aborted_validation", branch=branch,
                n_dev_commits=n_behind, conflict_files=conflicts,
                resolved_files=resolved, validation=validation,
                error=validation.summary,
            )

        # Commit the merge
        commit_msg = (
            f"Auto-merge origin/dev ({n_behind} commits) — "
            f"{len(resolved)} conflict(s) resolved by dev_sync_resolver\n\n"
            f"Resolved files:\n" + "\n".join(f"  - {p}" for p in resolved) +
            f"\n\nValidation: {validation.summary}"
        )
        commit_res = _git(["commit", "--no-edit", "-m", commit_msg], timeout=30)
        if commit_res.returncode != 0:
            _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                conflict_files=conflicts, resolved_files=resolved,
                validation=validation,
                error=f"git commit failed: {commit_res.stderr[:200]}",
            )

        # Push
        push_res = _git(["push", "origin", branch], capture=False, timeout=60)
        if push_res.returncode != 0:
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                conflict_files=conflicts, resolved_files=resolved,
                validation=validation,
                error=f"merge committed locally but push failed rc={push_res.returncode}",
            )

        return SyncResult(
            status="auto_resolved", branch=branch, n_dev_commits=n_behind,
            conflict_files=conflicts, resolved_files=resolved, validation=validation,
        )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser(description="dev_sync_resolver standalone run")
    parser.add_argument("--allowed-branch", default="bedc-claim-packet-pipeline")
    args = parser.parse_args()

    result = sync_with_resolution(allowed_branch=args.allowed_branch)
    print(json.dumps({
        "status": result.status,
        "branch": result.branch,
        "n_dev_commits": result.n_dev_commits,
        "conflict_files": result.conflict_files,
        "resolved_files": result.resolved_files,
        "failed_files": result.failed_files,
        "validation": ({
            "passed": result.validation.passed,
            "summary": result.validation.summary,
            "failures": result.validation.failures[:3],
        } if result.validation else None),
        "error": result.error,
    }, ensure_ascii=False, indent=2))
    return 0 if result.status in ("up_to_date", "ff_merged", "auto_resolved") else 1


if __name__ == "__main__":
    raise SystemExit(main())

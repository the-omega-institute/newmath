#!/usr/bin/env python3
"""dev_sync_resolver — auto-merge UPSTREAM_REF with gate-aware boundaries.

UPSTREAM_REF is currently `origin/auto-dev`.  BEDC must stay synchronized
with the integration branch so it does not duplicate work already produced by
the shared auto-dev/loning lanes.  The safety boundary is not "do not sync";
it is "sync through path protection, conflict handling, and post-merge gates".

Replaces the supervisor's bare `git_sync_dev` (which aborted on any conflict)
with a flow that:

  1. Acquire paper_writes lock so Stage 2 append never races with the merge
  2. fetch UPSTREAM_REF
  3. attempt git merge --no-edit UPSTREAM_REF
     ├─ ff success → commit + push
     └─ conflict:
        a. capture conflict files + hunks
        b. spawn Codex with project conventions + each conflict block
        c. apply Codex's resolved content
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
import subprocess
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
LOG_DIR = SCRIPT_DIR / "state" / "dev_sync_logs"

# Upstream integration branch we sync into bedc-claim-packet-pipeline.
# This follows the shared integration trunk so BEDC does not rediscover or
# rewrite work already landed by auto-dev/loning.  Path protection and gates
# below decide what may be merged or auto-resolved.
UPSTREAM_BRANCH = os.environ.get("BEDC_SYNC_UPSTREAM_BRANCH", "auto-dev")
UPSTREAM_REF = f"origin/{UPSTREAM_BRANCH}"

CODEX_RESOLVE_PER_FILE_TIMEOUT = 600

VALIDATION_TIMEOUTS = {
    "paper_provenance": 120,
    "paper_check": 600,
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
    re.compile(r"^papers/bedc/scripts/"),
    re.compile(r"^tools/automath_newmath_bridge/review_packets/"),
    re.compile(r"^tools/automath_newmath_bridge/inbox/"),
    re.compile(r"^tools/automath_newmath_bridge/out/"),
    re.compile(r"^tools/automath_newmath_bridge/state/"),
    re.compile(r"^tools/bedc-deep/BOARD(?:\.completed)?\.md$"),
    re.compile(r"^tools/bedc-deep/state/"),
    re.compile(r"^\.github/"),
    re.compile(r"^lakefile\.lean$"),
    re.compile(r"^lake-manifest\.json$"),
]
LOCAL_ONLY_STATE_PATTERNS = [
    re.compile(r"^tools/bedc-deep/BOARD(?:\.completed)?\.md$"),
]
OURS_ON_CONFLICT_PATTERNS = [
    re.compile(r"^tools/bedc-deep/prompts/codex_track_attempt\.txt$"),
    re.compile(r"^tools/bedc-deep/prompts/oracle_initial\.txt$"),
]
POST_MERGE_PROTECTED_PATTERNS = [
    re.compile(r"^tools/automath_newmath_bridge/review_packets/"),
    re.compile(r"^tools/automath_newmath_bridge/inbox/"),
    re.compile(r"^tools/automath_newmath_bridge/out/"),
    re.compile(r"^tools/automath_newmath_bridge/state/"),
    re.compile(r"^tools/bedc-deep/BOARD(?:\.completed)?\.md$"),
]
OURS_ON_CLEAN_MERGE_PATTERNS = [
    re.compile(r"^tools/bedc-deep/prompts/codex_track_attempt\.txt$"),
    re.compile(r"^tools/bedc-deep/prompts/oracle_initial\.txt$"),
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


def _is_local_only_state(path: str) -> bool:
    return any(p.search(path) for p in LOCAL_ONLY_STATE_PATTERNS)


def _is_ours_on_conflict(path: str) -> bool:
    return any(p.search(path) for p in OURS_ON_CONFLICT_PATTERNS)


def _is_post_merge_protected(path: str) -> bool:
    return any(p.search(path) for p in POST_MERGE_PROTECTED_PATTERNS)


def _is_ours_on_clean_merge(path: str) -> bool:
    return any(p.search(path) for p in OURS_ON_CLEAN_MERGE_PATTERNS)


def _codex_exec_text(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    import codex_orchestrator

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    (LOG_DIR / f"{log_tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    result = codex_orchestrator.codex_exec(prompt, timeout=timeout, log_tag=log_tag)
    (LOG_DIR / f"{log_tag}_{ts}.stdout.txt").write_text(result.raw_output or "", encoding="utf-8")
    (LOG_DIR / f"{log_tag}_{ts}.stderr.txt").write_text(result.error or "", encoding="utf-8")
    return (result.ok, result.raw_output, result.rc)


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


def _changed_files_against(ref: str) -> list[str]:
    res = _git(["diff", "--name-only", ref, "HEAD"], timeout=30)
    return [line.strip() for line in res.stdout.splitlines() if line.strip()]


def _post_merge_boundary_failure(before_ref: str) -> str:
    changed = _changed_files_against(before_ref)
    protected = [
        path for path in changed
        if _is_post_merge_protected(path) and not _is_local_only_state(path)
    ]
    if protected:
        return "post_merge_protected_paths:" + ",".join(protected[:20])
    return ""


def _settle_clean_merge_boundaries(before_ref: str) -> list[str]:
    """Re-apply BEDC local boundaries after a non-conflicting merge.

    A remote commit can change local-only BOARD files or older prompt policy
    without producing a textual conflict.  Those changes must not survive just
    because Git considered the merge clean.
    """

    changed = _changed_files_against(before_ref)
    settled: list[str] = []
    for path in changed:
        if _is_local_only_state(path):
            _git(["rm", "--cached", "--ignore-unmatch", path], capture=False, timeout=10)
            settled.append(path)
            continue
        if _is_ours_on_clean_merge(path):
            checkout = _git(["checkout", before_ref, "--", path], capture=False, timeout=10)
            if checkout.returncode == 0:
                _git(["add", path], capture=False, timeout=10)
                settled.append(path)
    return settled


def _settle_local_only_state_conflicts(conflicts: list[str]) -> tuple[list[str], list[str]]:
    """Remove local runtime-state files from the merge result.

    BOARD files are execution queue state, not source.  If auto-dev still has
    historical tracked copies, they must not block source sync and must not be
    resurrected into the BEDC commit.
    """

    settled: list[str] = []
    remaining: list[str] = []
    for path in conflicts:
        if not _is_local_only_state(path):
            remaining.append(path)
            continue
        # If the file exists in the worktree, keep the working file but remove
        # it from the merge index; if it does not exist, this records deletion.
        _git(["rm", "--cached", "--ignore-unmatch", path], capture=False, timeout=10)
        settled.append(path)
    return settled, remaining


def _settle_ours_on_conflict(conflicts: list[str]) -> tuple[list[str], list[str]]:
    """Keep locally hardened prompts when auto-dev has an older boundary.

    These files encode the Automath / bridge evidence boundary.  If they
    conflict during sync and the interactive resolver is unavailable, the
    conservative merge is to preserve the local hardened prompt while still
    importing the rest of auto-dev.
    """

    settled: list[str] = []
    remaining: list[str] = []
    for path in conflicts:
        if not _is_ours_on_conflict(path):
            remaining.append(path)
            continue
        checkout = _git(["checkout", "--ours", "--", path], capture=False, timeout=10)
        if checkout.returncode != 0:
            remaining.append(path)
            continue
        add = _git(["add", path], capture=False, timeout=10)
        if add.returncode != 0:
            remaining.append(path)
            continue
        settled.append(path)
    return settled, remaining


def _read_conflict_file(path: str) -> ConflictFile:
    cf = ConflictFile(path=path, has_protected=_is_protected(path))
    full = REPO_ROOT / path
    try:
        cf.raw_content = full.read_text(encoding="utf-8", errors="replace")
    except OSError:
        cf.raw_content = ""
    return cf


# ---------------------------------------------------------------------------
# Codex conflict resolver
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
`>>>>>>> {UPSTREAM_REF}`):

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
    Codex's resolved content."""
    prompt = _build_resolve_prompt(cf, project_conventions)
    log_tag = f"resolve_{cf.path.replace('/', '_')}"
    ok, stdout, rc = _codex_exec_text(
        prompt,
        timeout=CODEX_RESOLVE_PER_FILE_TIMEOUT,
        log_tag=log_tag,
    )
    if not ok:
        return (False, f"codex exec rc={rc}: {stdout[:200]}")

    resolved = (stdout or "").strip()
    if not resolved:
        return (False, "codex returned empty resolution")
    if resolved == "ABORT_CONFLICT":
        return (False, "codex declared ABORT_CONFLICT (cannot responsibly resolve)")

    # Defensive: ensure no conflict markers remain in Codex's output.
    if any(m in resolved for m in ("<<<<<<< HEAD", "=======", f">>>>>>> {UPSTREAM_REF}")):
        return (False, "codex output still contains conflict markers")

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


def _validate_post_resolution(*, changed_files: list[str] | None = None) -> ValidationResult:
    """Run the project's CI gates. Returns pass/fail + which gate failed.

    Note: pdflatex is NOT in the gauntlet here — it's slow and Stage 2 will
    catch any compile breakage on its next append cycle, then roll back."""
    failures: list[str] = []
    changed = changed_files or []

    # BEDC paper provenance gate: no external source paths / bridge packets
    # may leak into paper body after sync.
    try:
        proc = subprocess.run(
            ["python3", "scripts/check_external_provenance.py"],
            cwd=str(REPO_ROOT / "papers" / "bedc"),
            capture_output=True,
            text=True,
            timeout=VALIDATION_TIMEOUTS["paper_provenance"],
        )
        if proc.returncode != 0:
            tail = (proc.stdout or "")[-1000:] + (proc.stderr or "")[-1000:]
            failures.append(f"paper provenance failed:\n{tail}")
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        failures.append(f"paper provenance infra error: {exc}")

    # Paper build/check gate catches bad LaTeX and phase paper gates.
    if any(path.startswith("papers/bedc/") for path in changed):
        try:
            proc = subprocess.run(
                ["make", "check"],
                cwd=str(REPO_ROOT / "papers" / "bedc"),
                capture_output=True,
                text=True,
                timeout=VALIDATION_TIMEOUTS["paper_check"],
            )
            if proc.returncode != 0:
                tail = (proc.stdout or "")[-1500:] + (proc.stderr or "")[-800:]
                failures.append(f"paper make check failed:\n{tail}")
        except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
            failures.append(f"paper make check infra error: {exc}")

    if not any(path.startswith("lean4/") or path.startswith("tools/check-axioms.py") for path in changed):
        summary = "paper gates passed" if not failures else f"{len(failures)} gate(s) failed"
        return ValidationResult(passed=not failures, failures=failures, summary=summary)

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

    summary = "paper + lean gates passed" if not failures else f"{len(failures)} gate(s) failed"
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
    """Fetch + merge UPSTREAM_REF with Codex-driven conflict resolution.

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
        fetch_res = _git(["fetch", "origin", UPSTREAM_BRANCH], capture=False, timeout=30)
        if fetch_res.returncode != 0:
            return SyncResult(status="error", branch=branch,
                               error=f"git fetch origin {UPSTREAM_BRANCH} failed")

        # Count incoming commits
        behind_res = _git(["rev-list", "--count", f"HEAD..{UPSTREAM_REF}"], timeout=10)
        n_behind = int((behind_res.stdout.strip() or "0"))
        if n_behind == 0:
            return SyncResult(status="up_to_date", branch=branch)
        before_head = _git(["rev-parse", "HEAD"], timeout=10).stdout.strip()

        # Attempt merge
        merge_res = _git(["merge", "--no-edit", UPSTREAM_REF], timeout=120)
        if merge_res.returncode == 0:
            settled_clean = _settle_clean_merge_boundaries(before_head)
            changed = _changed_files_against(before_head)
            boundary_failure = _post_merge_boundary_failure(before_head)
            if boundary_failure:
                _git(["reset", "--hard", before_head], capture=False, timeout=20)
                return SyncResult(
                    status="aborted_validation",
                    branch=branch,
                    n_dev_commits=n_behind,
                    validation=ValidationResult(
                        passed=False,
                        failures=[boundary_failure],
                        summary="post-merge boundary gate failed",
                    ),
                    error=boundary_failure,
                )
            validation = _validate_post_resolution(changed_files=changed)
            if not validation.passed:
                _git(["reset", "--hard", before_head], capture=False, timeout=20)
                return SyncResult(
                    status="aborted_validation",
                    branch=branch,
                    n_dev_commits=n_behind,
                    validation=validation,
                    error=validation.summary,
                )
            if settled_clean:
                commit_res = _git([
                    "commit",
                    "--no-edit",
                    "-m",
                    (
                        f"Auto-merge {UPSTREAM_REF} ({n_behind} commits) — "
                        "post-merge boundaries settled\n\n"
                        "Settled local boundaries:\n"
                        + "\n".join(f"  - {p}" for p in settled_clean)
                        + f"\n\nValidation: {validation.summary}"
                    ),
                ], timeout=30)
                if commit_res.returncode != 0:
                    _git(["reset", "--hard", before_head], capture=False, timeout=20)
                    return SyncResult(
                        status="error",
                        branch=branch,
                        n_dev_commits=n_behind,
                        validation=validation,
                        error=f"git commit failed after boundary settle: {commit_res.stderr[:200]}",
                    )
            # FF or clean merge succeeded and gates passed; push.
            push_res = _git(["push", "origin", branch], capture=False, timeout=60)
            if push_res.returncode != 0:
                return SyncResult(
                    status="error", branch=branch, n_dev_commits=n_behind,
                    error=f"clean merge but push failed rc={push_res.returncode}",
                )
            return SyncResult(
                status="ff_merged",
                branch=branch,
                n_dev_commits=n_behind,
                resolved_files=settled_clean,
            )

        # Conflict path
        conflicts = _conflicted_files()
        if not conflicts:
            # Merge failed without classic conflicts (rare). Abort to ORIG_HEAD.
            _git(["merge", "--abort"], capture=False, timeout=10)
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                error="merge failed without listed conflicts",
            )
        settled_local_only, conflicts = _settle_local_only_state_conflicts(conflicts)
        settled_ours, conflicts = _settle_ours_on_conflict(conflicts)
        pre_resolved = settled_local_only + settled_ours
        if not conflicts:
            changed = _changed_files_against(before_head)
            boundary_failure = _post_merge_boundary_failure(before_head)
            if boundary_failure:
                _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
                return SyncResult(
                    status="aborted_validation",
                    branch=branch,
                    n_dev_commits=n_behind,
                    conflict_files=pre_resolved,
                    validation=ValidationResult(
                        passed=False,
                        failures=[boundary_failure],
                        summary="post-merge boundary gate failed",
                    ),
                    error=boundary_failure,
                )
            validation = _validate_post_resolution(changed_files=changed)
            if not validation.passed:
                _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
                return SyncResult(
                    status="aborted_validation",
                    branch=branch,
                    n_dev_commits=n_behind,
                    conflict_files=pre_resolved,
                    validation=validation,
                    error=validation.summary,
                )
            commit_msg = (
                f"Auto-merge {UPSTREAM_REF} ({n_behind} commits) — "
                "pre-gated conflicts settled\n\n"
                "Pre-gated resolved files:\n"
                + "\n".join(f"  - {p}" for p in pre_resolved)
                + f"\n\nValidation: {validation.summary}"
            )
            commit_res = _git(["commit", "-m", commit_msg], timeout=30)
            if commit_res.returncode != 0:
                _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
                return SyncResult(
                    status="error",
                    branch=branch,
                    n_dev_commits=n_behind,
                    conflict_files=pre_resolved,
                    validation=validation,
                    error=f"git commit failed: {commit_res.stderr[:200]}",
                )
            push_res = _git(["push", "origin", branch], capture=False, timeout=60)
            if push_res.returncode != 0:
                return SyncResult(
                    status="error",
                    branch=branch,
                    n_dev_commits=n_behind,
                    conflict_files=settled_local_only,
                    validation=validation,
                    error=f"merge committed locally but push failed rc={push_res.returncode}",
                )
            return SyncResult(
                status="auto_resolved",
                branch=branch,
                n_dev_commits=n_behind,
                conflict_files=pre_resolved,
                resolved_files=pre_resolved,
                validation=validation,
            )

        # Check for protected paths — abort if any
        protected = [p for p in conflicts if _is_protected(p)]
        if protected:
            _git(["merge", "--abort"], capture=False, timeout=10)
            return SyncResult(
                status="aborted_protected", branch=branch, n_dev_commits=n_behind,
                conflict_files=pre_resolved + conflicts,
                error=f"protected files in conflict: {protected}; aborted, route to human_inbox",
            )

        # Resolve each conflict via Codex.
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
                conflict_files=pre_resolved + conflicts,
                resolved_files=pre_resolved + resolved,
                failed_files=failed,
                error=f"{len(failed)} file(s) could not be resolved; merge aborted",
            )

        # All conflicts resolved + staged; run validation
        changed = _changed_files_against(before_head)
        boundary_failure = _post_merge_boundary_failure(before_head)
        if boundary_failure:
            _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
            return SyncResult(
                status="aborted_validation", branch=branch,
                n_dev_commits=n_behind,
                conflict_files=pre_resolved + conflicts,
                resolved_files=pre_resolved + resolved,
                validation=ValidationResult(
                    passed=False,
                    failures=[boundary_failure],
                    summary="post-merge boundary gate failed",
                ),
                error=boundary_failure,
            )
        validation = _validate_post_resolution(changed_files=changed)
        if not validation.passed:
            # Abort merge by hard reset (since we already staged files)
            _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
            return SyncResult(
                status="aborted_validation", branch=branch,
                n_dev_commits=n_behind,
                conflict_files=pre_resolved + conflicts,
                resolved_files=pre_resolved + resolved,
                validation=validation,
                error=validation.summary,
            )

        # Commit the merge
        commit_msg = (
            f"Auto-merge {UPSTREAM_REF} ({n_behind} commits) — "
            f"{len(pre_resolved) + len(resolved)} conflict(s) resolved by dev_sync_resolver\n\n"
            f"Resolved files:\n" + "\n".join(f"  - {p}" for p in resolved) +
            (
                "\nPre-gated resolved files:\n"
                + "\n".join(f"  - {p}" for p in pre_resolved)
                if pre_resolved else ""
            ) +
            f"\n\nValidation: {validation.summary}"
        )
        commit_res = _git(["commit", "--no-edit", "-m", commit_msg], timeout=30)
        if commit_res.returncode != 0:
            _git(["reset", "--hard", "ORIG_HEAD"], capture=False, timeout=20)
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                conflict_files=pre_resolved + conflicts,
                resolved_files=pre_resolved + resolved,
                validation=validation,
                error=f"git commit failed: {commit_res.stderr[:200]}",
            )

        # Push
        push_res = _git(["push", "origin", branch], capture=False, timeout=60)
        if push_res.returncode != 0:
            return SyncResult(
                status="error", branch=branch, n_dev_commits=n_behind,
                conflict_files=pre_resolved + conflicts,
                resolved_files=pre_resolved + resolved,
                validation=validation,
                error=f"merge committed locally but push failed rc={push_res.returncode}",
            )

        return SyncResult(
            status="auto_resolved", branch=branch, n_dev_commits=n_behind,
            conflict_files=pre_resolved + conflicts,
            resolved_files=pre_resolved + resolved,
            validation=validation,
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

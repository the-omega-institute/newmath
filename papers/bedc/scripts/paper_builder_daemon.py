#!/usr/bin/env python3
"""Background full-PDF build daemon for the BEDC paper.

Round-level codex_revise rounds only run `make check` (single-pass
draftmode pdflatex) so PDF builds don't dominate round wall time and
trigger 600s timeouts. The full double-pass `make` that resolves
`\\autoref` page numbers and produces the typeset PDFs is handled
here instead — asynchronously, against the codex-auto-dev tip, in a
dedicated `_paper_builder` git worktree so it never touches a round
worktree.

This mirrors the lean side, where the analogous bg_builder thread
handles the full `lake build` outside the round pipeline.

Design:
- Single instance enforced via fcntl flock on .paper_builder.lock.
- Poll codex-auto-dev tip every POLL_SECONDS.
- On new SHA: checkout it in `.worktrees/_paper_builder`, run
  both PDF targets, log result.
- The daemon owns the `_paper_builder` worktree exclusively. Round
  workers never touch it.
- On build fail: invoke codex inside `_paper_builder` with the
  build-log tail and `prompts/paper_builder_fix.txt`. Codex edits
  `papers/bedc/`, commits with `paper-builder-fix:` prefix, and pushes
  back to `codex-auto-dev`. Tracks per-SHA/target fix attempts in
  `BROKEN_SHAS_FILE` so the same broken commit is not retried more
  than MAX_FIX_ATTEMPTS times. Mirrors lean's `_builder_codex_fix`.

Start (matches the bedc-codex-auto-dev skill style):

    mkdir -p papers/bedc/scripts/logs && \\
    nohup python3 papers/bedc/scripts/paper_builder_daemon.py \\
      >> papers/bedc/scripts/logs/paper_builder_daemon.log 2>&1 &
    disown

Stop:

    kill $(cat .paper_builder.lock 2>/dev/null) 2>/dev/null
    rm -f .paper_builder.lock

"""

from __future__ import annotations

import fcntl
import os
import signal
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
BUILDER_DIR = REPO_ROOT / ".worktrees" / "_paper_builder"
LAST_BUILT_FILE = (
    REPO_ROOT / "papers" / "bedc" / "scripts" / ".last_built_sha"
)
LOG_FILE = (
    REPO_ROOT / "papers" / "bedc" / "scripts" / "logs" / "paper_builder_daemon.log"
)
LOCK_FILE = REPO_ROOT / ".paper_builder.lock"

POLL_SECONDS = 60
BUILD_TIMEOUT_S = 1800
BASE_BRANCH = "codex-auto-dev"

CODEX_FIX_TIMEOUT_S = 1800
MAX_FIX_ATTEMPTS = 3
PDF_TARGETS = ("main", "concrete_instances")
BROKEN_SHAS_FILE = (
    REPO_ROOT / "papers" / "bedc" / "scripts" / ".broken_shas.txt"
)
PROMPT_PATH = (
    REPO_ROOT / "papers" / "bedc" / "scripts" / "prompts" / "paper_builder_fix.txt"
)


def log(msg: str) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {msg}\n"
    with LOG_FILE.open("a", encoding="utf-8") as f:
        f.write(line)
    # Also echo to stderr so nohup-redirected stdout has it.
    sys.stderr.write(line)
    sys.stderr.flush()


def run_git(*args: str, cwd: Path | None = None, timeout: int = 120) -> tuple[int, str]:
    r = subprocess.run(
        ["git", *args], cwd=str(cwd) if cwd else None,
        capture_output=True, text=True, timeout=timeout,
    )
    return r.returncode, (r.stdout + r.stderr).strip()


def ensure_builder_worktree() -> None:
    BUILDER_DIR.parent.mkdir(parents=True, exist_ok=True)
    if BUILDER_DIR.exists():
        return
    log(f"creating builder worktree at {BUILDER_DIR}")
    # Use a private throwaway branch name. The daemon will keep
    # detached-HEAD on it most of the time.
    rc, out = run_git(
        "-C", str(REPO_ROOT), "worktree", "add", "-f",
        "--detach", str(BUILDER_DIR), BASE_BRANCH,
    )
    if rc != 0:
        log(f"worktree create failed (rc={rc}): {out}")


def latest_remote_sha() -> str | None:
    rc, out = run_git("-C", str(REPO_ROOT), "fetch", "origin",
                       BASE_BRANCH, "--quiet")
    if rc != 0:
        log(f"fetch failed: {out[:200]}")
    rc, out = run_git("-C", str(REPO_ROOT), "rev-parse",
                       f"origin/{BASE_BRANCH}")
    if rc != 0:
        log(f"rev-parse failed: {out[:200]}")
        return None
    return out.split("\n")[0].strip()


def checkout(sha: str) -> bool:
    rc, out = run_git("-C", str(BUILDER_DIR), "fetch", "origin",
                       BASE_BRANCH, "--quiet")
    if rc != 0:
        log(f"builder fetch failed: {out[:200]}")
    rc, out = run_git("-C", str(BUILDER_DIR), "checkout", "--detach", sha)
    if rc != 0:
        log(f"checkout {sha[:8]} failed: {out[:200]}")
        return False
    return True


def last_built() -> str:
    if not LAST_BUILT_FILE.exists():
        return ""
    return LAST_BUILT_FILE.read_text().strip()


def write_last_built(sha: str) -> None:
    LAST_BUILT_FILE.parent.mkdir(parents=True, exist_ok=True)
    LAST_BUILT_FILE.write_text(sha + "\n")


def run_full_build(target: str) -> tuple[bool, str, float]:
    paper_dir = BUILDER_DIR / "papers" / "bedc"
    if not paper_dir.exists():
        return False, f"{paper_dir} missing", 0.0
    start = time.time()
    try:
        r = subprocess.run(
            ["make", f"{target}.pdf"],
            cwd=str(paper_dir),
            capture_output=True, text=True, errors="replace",
            timeout=BUILD_TIMEOUT_S,
        )
        elapsed = time.time() - start
        ok = r.returncode == 0
        tail = (r.stdout + r.stderr)[-2000:]
        return ok, tail, elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        return False, f"make {target}.pdf timed out after {BUILD_TIMEOUT_S}s", elapsed
    except Exception as exc:
        elapsed = time.time() - start
        return False, f"make raised {exc!r}", elapsed


def fix_attempts_for(sha: str, target: str) -> int:
    if not BROKEN_SHAS_FILE.exists():
        return 0
    n = 0
    for line in BROKEN_SHAS_FILE.read_text(encoding="utf-8").splitlines():
        fields = line.strip().split()
        if fields == [sha] or fields == [sha, target]:
            n += 1
    return n


def record_fix_attempt(sha: str, target: str) -> None:
    BROKEN_SHAS_FILE.parent.mkdir(parents=True, exist_ok=True)
    with BROKEN_SHAS_FILE.open("a", encoding="utf-8") as f:
        f.write(f"{sha} {target}\n")


def codex_fix(sha: str, target: str, log_tail: str, elapsed: float) -> bool:
    """Invoke codex inside _paper_builder worktree to repair a broken build.

    Returns True if codex left a committed-and-pushed fix on
    `codex-auto-dev`; the daemon's next tick picks up the new tip
    and re-runs `make`."""
    if not PROMPT_PATH.exists():
        log(f"codex_fix: prompt {PROMPT_PATH} missing, skipping")
        return False
    try:
        prompt_template = PROMPT_PATH.read_text(encoding="utf-8")
    except Exception as exc:
        log(f"codex_fix: prompt read failed: {exc!r}")
        return False
    prompt = prompt_template.format(
        sha=sha[:8],
        target=target,
        elapsed=elapsed,
        log_tail=log_tail[-6000:],
    )
    pre_tip = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "rev-parse", f"origin/{BASE_BRANCH}"],
        capture_output=True, text=True,
    ).stdout.strip()
    log(f"codex_fix: invoking codex on {sha[:8]} target={target} (origin tip {pre_tip[:8]})")
    try:
        subprocess.run(
            [
                "codex", "exec", "--dangerously-bypass-approvals-and-sandbox",
                "-C", str(BUILDER_DIR), prompt,
            ],
            timeout=CODEX_FIX_TIMEOUT_S,
            check=False,
        )
    except subprocess.TimeoutExpired:
        log(f"codex_fix: timed out after {CODEX_FIX_TIMEOUT_S}s on {sha[:8]} target={target}")
        return False
    except Exception as exc:
        log(f"codex_fix: codex invocation raised {exc!r}")
        return False
    # Re-fetch origin and check whether the tip advanced — if codex
    # pushed a fix commit, the tip moved. We don't trust the worktree's
    # local state because codex may have left it in odd shape; the
    # daemon will checkout the new origin tip on next loop iteration.
    rc, _ = run_git("-C", str(REPO_ROOT), "fetch", "origin",
                     BASE_BRANCH, "--quiet")
    post_tip = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "rev-parse", f"origin/{BASE_BRANCH}"],
        capture_output=True, text=True,
    ).stdout.strip()
    if post_tip and post_tip != pre_tip:
        log(f"codex_fix: tip advanced {pre_tip[:8]} -> {post_tip[:8]}")
        return True
    log(f"codex_fix: tip did not advance, codex produced no pushed commit")
    return False


def _build_sha_once(sha: str, consecutive_fail: int = 0) -> tuple[bool, int]:
    """Build all PDF targets for one checked remote SHA.

    Returns `(tip_moved, consecutive_fail)`. When a repair advances the
    remote tip, `LAST_BUILT_FILE` is intentionally left unchanged so the
    next daemon tick picks up the new SHA.
    """
    if not checkout(sha):
        log("checkout failed, will retry next tick")
        return False, consecutive_fail

    for target in PDF_TARGETS:
        ok, tail, elapsed = run_full_build(target)
        if ok:
            log(f"build OK {sha[:8]} target={target} in {elapsed:.0f}s")
            consecutive_fail = 0
            continue
        consecutive_fail += 1
        log(
            f"build FAIL {sha[:8]} target={target} in {elapsed:.0f}s "
            f"(consecutive_fail={consecutive_fail}); tail:\n"
            f"{tail[-1200:]}"
        )
        attempts_so_far = fix_attempts_for(sha, target)
        if attempts_so_far < MAX_FIX_ATTEMPTS:
            record_fix_attempt(sha, target)
            log(
                f"codex repair: attempt "
                f"{attempts_so_far + 1}/{MAX_FIX_ATTEMPTS} on {sha[:8]} target={target}"
            )
            if codex_fix(sha, target, tail, elapsed):
                return True, consecutive_fail
            log(
                f"codex repair: no fix pushed on {sha[:8]} target={target}; "
                f"daemon will retry on next merged tip"
            )
        else:
            log(
                f"codex repair: max attempts "
                f"({MAX_FIX_ATTEMPTS}) exhausted for {sha[:8]} target={target}; "
                f"giving up until tip moves"
            )

    write_last_built(sha)
    return False, consecutive_fail


def acquire_lock() -> int | None:
    fd = os.open(str(LOCK_FILE), os.O_CREAT | os.O_RDWR, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return None
    # Write PID so external tooling can find us.
    os.lseek(fd, 0, os.SEEK_SET)
    os.ftruncate(fd, 0)
    os.write(fd, str(os.getpid()).encode())
    return fd


def handle_signal(signum, frame):  # pragma: no cover
    log(f"caught signal {signum}, exiting")
    sys.exit(0)


def main() -> int:
    signal.signal(signal.SIGTERM, handle_signal)
    signal.signal(signal.SIGINT, handle_signal)

    fd = acquire_lock()
    if fd is None:
        sys.stderr.write("paper_builder_daemon: another instance is running\n")
        return 1
    log(f"daemon started pid={os.getpid()}")

    ensure_builder_worktree()

    consecutive_fail = 0
    while True:
        try:
            sha = latest_remote_sha()
            if sha and sha != last_built():
                log(f"new SHA {sha[:8]}, starting full build")
                _, consecutive_fail = _build_sha_once(sha, consecutive_fail)
        except Exception as exc:
            log(f"loop error: {exc!r}")
        time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    raise SystemExit(main())

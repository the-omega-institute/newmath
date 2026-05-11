#!/usr/bin/env python3
"""Background full-PDF build daemon for the BEDC paper.

Round-level codex_revise rounds only run `make check` (single-pass
draftmode pdflatex) so PDF builds don't dominate round wall time and
trigger 600s timeouts. The full double-pass `make` that resolves
`\\autoref` page numbers and produces the typeset main.pdf is handled
here instead — asynchronously, against the codex-auto-dev tip, in a
dedicated `_paper_builder` git worktree so it never touches a round
worktree.

This mirrors the lean side, where the analogous bg_builder thread
handles the full `lake build` outside the round pipeline.

Design:
- Single instance enforced via fcntl flock on .paper_builder.lock.
- Poll codex-auto-dev tip every POLL_SECONDS.
- On new SHA: checkout it in `.worktrees/_paper_builder`, run
  `make` (double-pass), log result.
- The daemon owns the `_paper_builder` worktree exclusively. Round
  workers never touch it.
- No codex repair invocation yet — on build fail we just log; later
  we can add a codex-exec hook similar to lean's `_builder_codex_fix`.

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


def run_full_build() -> tuple[bool, str, float]:
    paper_dir = BUILDER_DIR / "papers" / "bedc"
    if not paper_dir.exists():
        return False, f"{paper_dir} missing", 0.0
    start = time.time()
    try:
        r = subprocess.run(
            ["make"],  # full main.pdf double-pass via slot-gated pdflatex
            cwd=str(paper_dir),
            capture_output=True, text=True,
            timeout=BUILD_TIMEOUT_S,
        )
        elapsed = time.time() - start
        ok = r.returncode == 0
        tail = (r.stdout + r.stderr)[-2000:]
        return ok, tail, elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        return False, f"make timed out after {BUILD_TIMEOUT_S}s", elapsed
    except Exception as exc:
        elapsed = time.time() - start
        return False, f"make raised {exc!r}", elapsed


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
                if not checkout(sha):
                    log("checkout failed, will retry next tick")
                else:
                    ok, tail, elapsed = run_full_build()
                    if ok:
                        log(
                            f"build OK {sha[:8]} in {elapsed:.0f}s"
                        )
                        consecutive_fail = 0
                    else:
                        consecutive_fail += 1
                        log(
                            f"build FAIL {sha[:8]} in {elapsed:.0f}s "
                            f"(consecutive_fail={consecutive_fail}); tail:\n"
                            f"{tail[-1200:]}"
                        )
                    # Even on fail, advance last_built so we don't loop
                    # forever on a broken commit. The next merged commit
                    # will trigger a fresh build attempt and (usually)
                    # supersede the failure.
                    write_last_built(sha)
        except Exception as exc:
            log(f"loop error: {exc!r}")
        time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    raise SystemExit(main())

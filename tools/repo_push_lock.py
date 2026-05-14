"""Cross-process advisory lock for serializing pushes to a shared git branch.

The BEDC pipeline runs three daemons that all push to `origin/codex-auto-dev`:

  - `lean4/scripts/codex_formalize.py`   (R-side orchestrator)
  - `papers/bedc/scripts/codex_revise.py` (P-side orchestrator)
  - `tools/sync_with_auto_dev.py`        (bidirectional auto-dev sync)

Each daemon's `merge_worktree_to_base` (or equivalent) is wrapped in a
`threading.Lock`, which serializes the daemon's OWN worker threads but
does NOT prevent the OTHER daemons from concurrently fetching + pushing
to the same remote branch. The result is `ff update of <branch> failed`
and `Merge failed — non-fast-forward` cascades (24h sample: 47% of all
R-round FAILs are ff update failures).

`acquire_push_lock(branch)` returns a context manager that holds an
exclusive advisory `fcntl.flock` on a shared lockfile under
`.git/<branch>.push.lock`. Three daemons all wrapping their
merge-to-base sequence in this CM gives system-wide push serialization.

stdlib only (project rule).

Usage:

    from tools.repo_push_lock import acquire_push_lock

    with acquire_push_lock("codex-auto-dev", timeout=300):
        # fetch + merge + push, no other daemon can push during this block
        ...

Timeout > 0 raises `TimeoutError` after that many seconds of waiting.
Timeout == 0 polls once and raises `BlockingIOError` if held by another
process. Timeout is `None` (default) for unbounded wait — appropriate
for a daemon that must eventually push.
"""

from __future__ import annotations

import contextlib
import errno
import fcntl
import os
import subprocess
import time
from pathlib import Path
from typing import Iterator


def _repo_root() -> Path:
    """Locate the repo's .git directory by walking up from this file."""
    here = Path(__file__).resolve().parent
    for candidate in (here, *here.parents):
        if (candidate / ".git").exists():
            return candidate
    # Fallback: use `git rev-parse --show-toplevel` from cwd
    out = subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True
    )
    return Path(out.strip())


def _lock_path(branch: str) -> Path:
    """Per-branch lockfile under .git/. Lives inside .git/ so it does not
    pollute the working tree and is automatically scoped per checkout."""
    root = _repo_root()
    git_dir = root / ".git"
    safe_branch = branch.replace("/", "__")
    return git_dir / f"{safe_branch}.push.lock"


@contextlib.contextmanager
def acquire_push_lock(
    branch: str, *, timeout: float | None = None
) -> Iterator[Path]:
    """Acquire an exclusive advisory `flock` on `.git/<branch>.push.lock`.

    `timeout`:
      - `None` (default): unbounded wait. Suitable for daemon workers.
      - `0`: poll once, raise `BlockingIOError` if held.
      - `>0`: wait up to `timeout` seconds, raise `TimeoutError`.

    On macOS, `fcntl.flock` is per-process: re-acquiring in the same
    process re-uses the existing lock (no blocking). For cross-process
    serialization (the use case here), each daemon process holds its own
    fd, and the kernel arbitrates contention.
    """
    path = _lock_path(branch)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Open in append mode so concurrent processes don't truncate each other's lockfile.
    fd = os.open(str(path), os.O_RDWR | os.O_CREAT, 0o644)
    try:
        deadline = None if timeout is None else time.monotonic() + timeout
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError as exc:
                if exc.errno not in (errno.EWOULDBLOCK, errno.EAGAIN):
                    raise
                if timeout == 0:
                    raise BlockingIOError(
                        f"push lock for branch {branch!r} held by another "
                        f"process; lockfile {path}"
                    ) from exc
                if deadline is not None and time.monotonic() >= deadline:
                    raise TimeoutError(
                        f"push lock for branch {branch!r} held for "
                        f"more than {timeout}s by another process"
                    ) from exc
                time.sleep(0.5)
        try:
            # Record who's holding for post-mortem.
            os.ftruncate(fd, 0)
            os.write(fd, f"pid={os.getpid()} held_at={int(time.time())}\n".encode())
            yield path
        finally:
            try:
                fcntl.flock(fd, fcntl.LOCK_UN)
            except OSError:
                pass
    finally:
        os.close(fd)

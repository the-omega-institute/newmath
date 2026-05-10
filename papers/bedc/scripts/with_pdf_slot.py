#!/usr/bin/env python3
"""Run a command holding one of N flock-protected pdf-build slots.

Used by papers/bedc/Makefile to cap concurrent pdflatex invocations
across every worktree + the main checkout. Without this gate, parallel
paper rounds dogpile pdflatex: 10+ concurrent pdflatex invocations on
a 16-core MBP push Load avg above 60, single-build time stretches from
~75s to >600s, and rounds time out.

Slot files live under git's common-dir (.git/.pdf-build-gate/), which
is the same physical directory across every worktree of this repo.
Permit count is read from .pipeline_parallel.json key "pdf_build"
(default 2). Concurrency from `make` callers in any worktree (including
the orchestrator's per-round paper_PXXXX worktrees) is therefore
serialised through the same N slots.

Usage:
    with_pdf_slot.py -- pdflatex ...
    with_pdf_slot.py -- bash -c 'pdflatex ... && pdflatex ...'

Exit codes are pass-through from the wrapped command. 124 on slot wait
timeout (1200s default).
"""

from __future__ import annotations

import fcntl
import json
import os
import subprocess
import sys
import time
from pathlib import Path

WAIT_TIMEOUT_S = 1200
DEFAULT_PERMITS = 2


def _git_common_dir() -> Path:
    out = subprocess.run(
        ["git", "rev-parse", "--git-common-dir"],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    return Path(out).resolve()


def _read_permits(main_checkout: Path) -> int:
    cfg = main_checkout / ".pipeline_parallel.json"
    try:
        return int(json.loads(cfg.read_text()).get("pdf_build", DEFAULT_PERMITS))
    except Exception:
        return DEFAULT_PERMITS


def main(argv: list[str]) -> int:
    if not argv:
        print("with_pdf_slot.py: missing command", file=sys.stderr)
        return 2
    if argv[0] == "--":
        argv = argv[1:]
    if not argv:
        print("with_pdf_slot.py: missing command after --", file=sys.stderr)
        return 2

    common = _git_common_dir()
    main_checkout = common.parent
    gate_dir = common / ".pdf-build-gate"
    gate_dir.mkdir(parents=True, exist_ok=True)
    permits = max(1, _read_permits(main_checkout))

    deadline = time.time() + WAIT_TIMEOUT_S
    backoff = 0.5
    while True:
        for i in range(permits):
            slot = gate_dir / f"slot{i}.lock"
            fd = os.open(str(slot), os.O_RDWR | os.O_CREAT, 0o644)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(fd)
                continue
            try:
                start = time.time()
                rc = subprocess.call(argv)
                elapsed = time.time() - start
                # Best-effort observability: prepend a marker to slot file so
                # ls -lt under .pdf-build-gate/ shows recency.
                try:
                    os.utime(str(slot), None)
                except Exception:
                    pass
                return rc
            finally:
                try:
                    fcntl.flock(fd, fcntl.LOCK_UN)
                finally:
                    os.close(fd)
        if time.time() >= deadline:
            print(
                f"with_pdf_slot.py: timeout waiting for one of {permits} "
                f"pdf-build slots after {WAIT_TIMEOUT_S}s",
                file=sys.stderr,
            )
            return 124
        time.sleep(backoff)
        backoff = min(backoff * 1.5, 5.0)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

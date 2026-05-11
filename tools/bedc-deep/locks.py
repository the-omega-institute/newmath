#!/usr/bin/env python3
"""File-based mutexes for cross-process coordination in bedc-deep.

Used by parallel oracle_client workers to serialize:
- BOARD.md append (Stage 1.5 fan-out)
- papers/bedc make (Stage 2 paper compile)
- target picking (avoid two workers grabbing the same B-XX)

stdlib-only. Uses `fcntl` on POSIX and `msvcrt` on Windows.
"""

from __future__ import annotations

import os
import sys
from contextlib import contextmanager
from pathlib import Path

if sys.platform == "win32":
    import msvcrt
else:
    import fcntl

SCRIPT_DIR = Path(__file__).resolve().parent
LOCKS_DIR = SCRIPT_DIR / "state" / "locks"


@contextmanager
def file_lock(name: str):
    """Exclusive file-backed lock. Blocks until acquired."""
    LOCKS_DIR.mkdir(parents=True, exist_ok=True)
    lock_path = LOCKS_DIR / f"{name}.lock"
    fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o644)
    try:
        if sys.platform == "win32":
            msvcrt.locking(fd, msvcrt.LK_LOCK, 1)
        else:
            fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        try:
            if sys.platform == "win32":
                os.lseek(fd, 0, os.SEEK_SET)
                msvcrt.locking(fd, msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)

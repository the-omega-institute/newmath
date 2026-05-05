#!/usr/bin/env python3
"""Hot-reloadable per-paper-label claim mechanism.

Modeled after the existing `claim_targets` in-process registry but lives as a
subprocess invocation so codex Phase B / Phase REVIEW can call it from the
prompt without requiring an orchestrator-body change.

State file lives in the shared `.git` common dir (visible across linked
worktrees) so concurrent rounds in different worktrees see a single source of
truth — same anchoring trick as `critical_path.py`'s LOCKS_FILE.

Usage:
    claim_paper_label.py claim --round R<N> --labels thm:foo,def:bar
        Atomically claim each label for round R<N>. Returns JSON
        `{"kept": [...], "dropped": [...]}` listing labels successfully
        claimed vs already-claimed-by-someone-else (or already on disk).

    claim_paper_label.py release --round R<N>
        Release all labels held by round R<N>.

    claim_paper_label.py inspect
        Print current claim file content as JSON.

Claims expire after CLAIM_TTL_SECONDS so a crashed round eventually frees its
labels. Tree-presence check: if a label already exists somewhere in
`papers/bedc/parts/`, the claim is rejected immediately (round must drop the
target — the label is taken by a previous round whose work is already merged).
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PAPER_PARTS = ROOT / "papers" / "bedc" / "parts"
CLAIM_TTL_SECONDS = 1800  # 30 min — slightly above max codex round duration


def _resolve_claims_file() -> Path:
    """Anchor the claim file in the repo's shared `.git` common dir so all
    linked worktrees see a single shared file (matches critical_path.py)."""
    fallback = Path(__file__).resolve().parent / ".paper_label_claims.json"
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--git-common-dir"],
            cwd=str(Path(__file__).resolve().parent),
            capture_output=True, text=True, check=True, timeout=5,
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError, subprocess.TimeoutExpired):
        return fallback
    if not out:
        return fallback
    common = Path(out)
    if not common.is_absolute():
        common = (Path(__file__).resolve().parent / common).resolve()
    return common / "bedc-paper-label-claims.json"


CLAIMS_FILE = _resolve_claims_file()
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


def _label_present_on_disk(label: str) -> bool:
    """Return True if any .tex under papers/bedc/parts/ already has \\label{<label>}."""
    pat = f"\\label{{{label}}}"
    try:
        r = subprocess.run(
            ["grep", "-rlF", pat, str(PAPER_PARTS)],
            capture_output=True, text=True, timeout=15,
        )
        return r.returncode == 0 and bool(r.stdout.strip())
    except Exception:
        return False


def _open_locked():
    fd = os.open(CLAIMS_FILE, os.O_RDWR | os.O_CREAT, 0o644)
    fcntl.flock(fd, fcntl.LOCK_EX)
    return fd


def _read_state(fd: int) -> dict:
    os.lseek(fd, 0, 0)
    raw = os.read(fd, 1 << 20).decode("utf-8") or "{}"
    try:
        return json.loads(raw)
    except Exception:
        return {}


def _write_state(fd: int, state: dict) -> None:
    os.lseek(fd, 0, 0)
    os.ftruncate(fd, 0)
    os.write(fd, json.dumps(state, indent=2).encode("utf-8"))


def _expire(state: dict, now: float) -> dict:
    """Drop expired entries in place. State shape: {label: {round, expires_at}}."""
    return {
        k: v for k, v in state.items()
        if isinstance(v, dict) and float(v.get("expires_at", 0)) > now
    }


def claim(round_id: str, labels: list[str]) -> dict:
    """Atomic claim. Returns {kept: [...], dropped: [{label, reason}]}."""
    now = time.time()
    kept: list[str] = []
    dropped: list[dict] = []
    fd = _open_locked()
    try:
        state = _expire(_read_state(fd), now)
        for label in labels:
            label = label.strip()
            if not label:
                continue
            if _label_present_on_disk(label):
                dropped.append({"label": label, "reason": "already_on_disk"})
                continue
            holder = state.get(label)
            if holder and holder.get("round") != round_id:
                dropped.append({"label": label, "reason": f"claimed_by_{holder['round']}"})
                continue
            state[label] = {"round": round_id,
                            "expires_at": now + CLAIM_TTL_SECONDS}
            kept.append(label)
        _write_state(fd, state)
    finally:
        try: fcntl.flock(fd, fcntl.LOCK_UN)
        except Exception: pass
        os.close(fd)
    return {"kept": kept, "dropped": dropped}


def release(round_id: str) -> dict:
    """Release all labels held by round_id."""
    fd = _open_locked()
    released: list[str] = []
    try:
        state = _read_state(fd)
        for label in list(state.keys()):
            if isinstance(state[label], dict) and state[label].get("round") == round_id:
                released.append(label)
                del state[label]
        _write_state(fd, state)
    finally:
        try: fcntl.flock(fd, fcntl.LOCK_UN)
        except Exception: pass
        os.close(fd)
    return {"released": released}


def inspect() -> dict:
    fd = _open_locked()
    try:
        state = _expire(_read_state(fd), time.time())
        _write_state(fd, state)
        return state
    finally:
        try: fcntl.flock(fd, fcntl.LOCK_UN)
        except Exception: pass
        os.close(fd)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p1 = sub.add_parser("claim")
    p1.add_argument("--round", required=True)
    p1.add_argument("--labels", required=True,
                    help="comma-separated label list (e.g. thm:foo,def:bar)")
    p2 = sub.add_parser("release")
    p2.add_argument("--round", required=True)
    sub.add_parser("inspect")

    args = ap.parse_args()
    if args.cmd == "claim":
        labels = [s for s in args.labels.split(",") if s.strip()]
        out = claim(args.round, labels)
        print(json.dumps(out, indent=2))
        return 1 if out["dropped"] else 0
    if args.cmd == "release":
        print(json.dumps(release(args.round), indent=2))
        return 0
    if args.cmd == "inspect":
        print(json.dumps(inspect(), indent=2))
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())

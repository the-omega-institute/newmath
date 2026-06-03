#!/usr/bin/env python3
"""Shared structural-DNA executable readiness checks for BEDC daemons."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from typing import Callable

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO_ROOT / "lean4"
STRUCTURAL_DNA_EXE = LEAN_ROOT / ".lake" / "build" / "bin" / "structural_dna"
STRUCTURAL_DNA_MAIN = LEAN_ROOT / "scripts" / "structural_dna" / "Main.lean"
STRUCTURAL_DNA_BUILD_TIMEOUT = 1200
STRUCTURAL_DNA_PROBE_TIMEOUT = 1200
PROBE_IMPORTS = ["scripts.structural_dna.TestTargets"]
PROBE_DECLS = ["BEDC.StructuralDna.TestTargets.AlphaLamA"]


def short_process_output(process: subprocess.CompletedProcess[str], limit: int = 1200) -> str:
    combined = ((process.stdout or "") + (process.stderr or "")).strip()
    if len(combined) <= limit:
        return combined
    return combined[-limit:]


def run_lake_build(target: str = "structural_dna") -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "build", target],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        timeout=STRUCTURAL_DNA_BUILD_TIMEOUT,
    )


def structural_dna_probe() -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", str(STRUCTURAL_DNA_EXE)],
        cwd=LEAN_ROOT,
        input=json.dumps({"imports": PROBE_IMPORTS, "decls": PROBE_DECLS}),
        capture_output=True,
        text=True,
        timeout=STRUCTURAL_DNA_PROBE_TIMEOUT,
    )


def structural_dna_source_newer_than_exe() -> bool:
    if not STRUCTURAL_DNA_EXE.exists():
        return True
    try:
        return STRUCTURAL_DNA_MAIN.stat().st_mtime > STRUCTURAL_DNA_EXE.stat().st_mtime
    except OSError:
        return True


def probe_has_canonical_payload(process: subprocess.CompletedProcess[str]) -> bool:
    if process.returncode != 0:
        return False
    try:
        payload = json.loads(process.stdout or "{}")
    except json.JSONDecodeError:
        return False
    if not isinstance(payload, dict):
        return False
    for decl in PROBE_DECLS:
        item = payload.get(decl)
        if isinstance(item, dict) and str(item.get("canonical_reduced_payload") or "").strip():
            return True
    return False


def ensure_structural_dna_build(
    *,
    append_log: Callable[[str], None] | None = None,
    label: str = "structural_dna",
) -> str | None:
    def log(message: str) -> None:
        if append_log is not None:
            append_log(message)

    def build_once(reason: str) -> str | None:
        try:
            build = run_lake_build("structural_dna")
        except subprocess.TimeoutExpired:
            detail = f"structural_dna build timed out after {STRUCTURAL_DNA_BUILD_TIMEOUT}s"
            log(f"[{label}] [WARNING] {detail}")
            return detail
        except Exception as exc:
            detail = f"structural_dna build could not start: {type(exc).__name__}: {exc}"
            log(f"[{label}] [WARNING] {detail}")
            return detail
        if build.returncode != 0:
            detail = f"structural_dna build failed exit={build.returncode}"
            log(f"[{label}] [WARNING] {detail}: {short_process_output(build)}")
            return detail
        log(f"[{label}] structural_dna build ok ({reason})")
        return None

    if structural_dna_source_newer_than_exe():
        failure = build_once("source newer than executable")
        if failure is not None:
            return failure

    try:
        probe = structural_dna_probe()
    except subprocess.TimeoutExpired:
        detail = f"structural_dna canonical-payload probe timed out after {STRUCTURAL_DNA_PROBE_TIMEOUT}s"
        log(f"[{label}] [WARNING] {detail}")
        return detail
    except Exception as exc:
        detail = f"structural_dna canonical-payload probe could not start: {type(exc).__name__}: {exc}"
        log(f"[{label}] [WARNING] {detail}")
        return detail
    if probe_has_canonical_payload(probe):
        return None

    failure = build_once("canonical payload probe empty")
    if failure is not None:
        return failure
    try:
        retry = structural_dna_probe()
    except subprocess.TimeoutExpired:
        detail = (
            "structural_dna canonical-payload probe timed out after forced rebuild "
            f"after {STRUCTURAL_DNA_PROBE_TIMEOUT}s"
        )
        log(f"[{label}] [WARNING] {detail}")
        return detail
    except Exception as exc:
        detail = (
            "structural_dna canonical-payload probe could not start after forced rebuild: "
            f"{type(exc).__name__}: {exc}"
        )
        log(f"[{label}] [WARNING] {detail}")
        return detail
    if probe_has_canonical_payload(retry):
        return None
    detail = "structural_dna canonical-payload probe returned empty after forced rebuild"
    log(f"[{label}] [WARNING] {detail}: {short_process_output(retry)}")
    return detail

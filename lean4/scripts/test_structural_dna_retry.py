#!/usr/bin/env python3

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
from pathlib import Path
from typing import Callable


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import bedc_ci  # noqa: E402


class _FakeExe:
    def exists(self) -> bool:
        return True

    def __str__(self) -> str:
        return "/tmp/fake-structural-dna"


def _completed(returncode: int, stdout: str = "", stderr: str = "") -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(
        ["lake", "env", "/tmp/fake-structural-dna"],
        returncode,
        stdout=stdout,
        stderr=stderr,
    )


def _success_payload() -> str:
    return json.dumps({
        "BEDC.Target": {
            "fingerprint": "fp",
            "type_fp": "ty",
            "value_fp": "val",
        }
    })


def _with_patched_runner(
    results: list[subprocess.CompletedProcess[str]],
    body: Callable[[], object],
) -> tuple[object, str, int]:
    old_run = bedc_ci.subprocess.run
    old_sleep = bedc_ci.time.sleep
    old_exe = bedc_ci.STRUCTURAL_DNA_EXE
    calls: list[list[str]] = []

    def fake_run(cmd: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
        calls.append(cmd)
        assert results, "unexpected subprocess.run call"
        return results.pop(0)

    try:
        bedc_ci.subprocess.run = fake_run
        bedc_ci.time.sleep = lambda _seconds: None
        bedc_ci.STRUCTURAL_DNA_EXE = _FakeExe()
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            value = body()
        return value, stderr.getvalue(), len(calls)
    finally:
        bedc_ci.subprocess.run = old_run
        bedc_ci.time.sleep = old_sleep
        bedc_ci.STRUCTURAL_DNA_EXE = old_exe


def test_expr_fingerprint_retry_succeeds() -> None:
    value, stderr, call_count = _with_patched_runner(
        [
            _completed(1, stderr="transient lake failure"),
            _completed(0, stdout=_success_payload()),
        ],
        lambda: bedc_ci._run_structural_dna_expr_fingerprints(["BEDC.Target"]),
    )
    assert call_count == 2
    assert set(value) == {"BEDC.Target"}
    assert "structural_dna expr-fingerprints-rc: rc=1" in stderr


def test_expr_fingerprint_double_failure_returns_empty_with_diagnostic() -> None:
    value, stderr, call_count = _with_patched_runner(
        [
            _completed(1, stderr="first failure"),
            _completed(1, stderr="second failure"),
        ],
        lambda: bedc_ci._run_structural_dna_expr_fingerprints(["BEDC.Target"]),
    )
    assert value == {}
    assert call_count == 2
    assert "first failure" in stderr
    assert "second failure" in stderr


def test_expr_fingerprint_success_does_not_retry() -> None:
    value, stderr, call_count = _with_patched_runner(
        [_completed(0, stdout=_success_payload())],
        lambda: bedc_ci._run_structural_dna_expr_fingerprints(["BEDC.Target"]),
    )
    assert call_count == 1
    assert set(value) == {"BEDC.Target"}
    assert stderr == ""


def main() -> int:
    test_expr_fingerprint_retry_succeeds()
    test_expr_fingerprint_double_failure_returns_empty_with_diagnostic()
    test_expr_fingerprint_success_does_not_retry()
    print("OK: structural_dna retry diagnostics")
    return 0


if __name__ == "__main__":
    sys.exit(main())

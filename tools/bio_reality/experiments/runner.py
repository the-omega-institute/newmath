#!/usr/bin/env python3
"""Subprocess runner for BioReality experiment scripts."""

from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


VALID_STATUSES = {"passed", "failed", "needs_data", "error", "timeout"}
SCRIPT_ROOT = Path("tools/bio_reality/experiments")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _tail(value: str, limit: int = 1000) -> str:
    return value[-limit:]


def _safe_load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def load_experiments_registry(repo_root: Path) -> list[dict[str, Any]]:
    data = _safe_load_json(repo_root / "tools/bio_reality/registries/experiments.json")
    experiments = data.get("experiments")
    return [item for item in experiments if isinstance(item, dict)] if isinstance(experiments, list) else []


def load_claims_registry(repo_root: Path) -> dict[str, dict[str, Any]]:
    data = _safe_load_json(repo_root / "tools/bio_reality/registries/claims.json")
    claims = data.get("claims")
    if not isinstance(claims, list):
        return {}
    return {
        str(item.get("claim_id")): item
        for item in claims
        if isinstance(item, dict) and item.get("claim_id")
    }


def _resolve_script_path(repo_root: Path, script_path: str) -> Path | None:
    if not script_path:
        return None
    relative = Path(script_path)
    if relative.is_absolute():
        return None
    parts = relative.parts
    if len(parts) < 4 or Path(*parts[:3]) != SCRIPT_ROOT:
        return None
    if not relative.name.startswith("run_") or relative.suffix != ".py":
        return None
    try:
        resolved = (repo_root / relative).resolve()
        experiments_dir = (repo_root / SCRIPT_ROOT).resolve()
        resolved.relative_to(experiments_dir)
    except (OSError, ValueError):
        return None
    return resolved


def _last_json_object(stdout: str) -> tuple[dict[str, Any] | None, str]:
    last_line = ""
    for line in reversed(stdout.splitlines()):
        if line.strip():
            last_line = line.strip()
            break
    if not last_line:
        return None, ""
    try:
        data = json.loads(last_line)
    except json.JSONDecodeError:
        return None, last_line
    return (data if isinstance(data, dict) else None), last_line


def _checks(raw: Any) -> list[dict[str, Any]]:
    if not isinstance(raw, list):
        return []
    return [item for item in raw if isinstance(item, dict)]


def _apply_acceptance(result: dict[str, Any], acceptance: dict[str, Any]) -> None:
    if result.get("status") != "passed":
        return
    required = acceptance.get("required_checks") if isinstance(acceptance, dict) else []
    if not isinstance(required, list):
        required = []
    checks = _checks(result.get("checks"))
    checks_by_name = {str(check.get("name") or ""): check for check in checks}
    missing_or_failed: list[str] = []
    for name in required:
        check = checks_by_name.get(str(name))
        if check is None:
            missing_or_failed.append(f"{name}: missing")
        elif check.get("passed") is not True:
            reason = str(check.get("reason") or "passed is not true")
            missing_or_failed.append(f"{name}: {reason}")
    if not missing_or_failed:
        return
    result["status"] = "failed"
    checks.append(
        {
            "name": "acceptance.required",
            "passed": False,
            "reason": "; ".join(missing_or_failed),
        }
    )
    result["checks"] = checks


def _base_result(experiment_spec: dict[str, Any], started_at: str) -> dict[str, Any]:
    return {
        "experiment_id": str(experiment_spec.get("experiment_id") or ""),
        "claim_id": str(experiment_spec.get("claim_id") or ""),
        "started_at": started_at,
        "completed_at": now_iso(),
        "status": "error",
        "checks": [],
        "result": {},
        "stdout_tail": "",
        "stderr_tail": "",
        "returncode": None,
    }


def run_experiment(experiment_spec: dict[str, Any], *, timeout_seconds: int = 300, repo_root: Path) -> dict[str, Any]:
    """
    Run one registered BioReality experiment and normalize its JSON result.

    The experiment script may print human-readable lines, but its last non-empty
    stdout line must be a single JSON object.
    """
    started_at = now_iso()
    normalized = _base_result(experiment_spec, started_at)
    script = _resolve_script_path(repo_root, str(experiment_spec.get("script_path") or ""))
    if script is None:
        normalized["stderr_tail"] = "invalid experiment script_path"
        return normalized
    try:
        completed = subprocess.run(
            [sys.executable, str(script)],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        normalized["completed_at"] = now_iso()
        normalized["status"] = "timeout"
        normalized["stdout_tail"] = _tail(exc.stdout if isinstance(exc.stdout, str) else "")
        normalized["stderr_tail"] = _tail(exc.stderr if isinstance(exc.stderr, str) else "")
        return normalized
    except OSError as exc:
        normalized["completed_at"] = now_iso()
        normalized["stderr_tail"] = str(exc)
        return normalized

    stdout = completed.stdout or ""
    stderr = completed.stderr or ""
    raw_result, last_line = _last_json_object(stdout)
    normalized["completed_at"] = now_iso()
    normalized["stdout_tail"] = _tail(stdout)
    normalized["stderr_tail"] = _tail(stderr)
    normalized["returncode"] = completed.returncode
    if raw_result is None:
        message = f"stdout last line not JSON: {last_line}"
        normalized["stderr_tail"] = _tail(f"{stderr}\n{message}" if stderr else message)
        normalized["status"] = "error"
        return normalized

    status = str(raw_result.get("status") or "")
    normalized["status"] = status if status in VALID_STATUSES else "error"
    normalized["checks"] = _checks(raw_result.get("checks"))
    raw_payload = raw_result.get("result")
    normalized["result"] = raw_payload if isinstance(raw_payload, dict) else raw_result
    for key in ("started_at", "completed_at"):
        if isinstance(raw_result.get(key), str) and raw_result.get(key):
            normalized[key] = str(raw_result[key])
    _apply_acceptance(normalized, experiment_spec.get("acceptance") if isinstance(experiment_spec.get("acceptance"), dict) else {})
    return normalized

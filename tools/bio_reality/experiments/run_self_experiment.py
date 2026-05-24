#!/usr/bin/env python3
"""Run the BioReality self experiment for claim self.claim."""
from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def run_check(name: str, args: list[str]) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    check: dict[str, object] = {
        "name": name,
        "passed": completed.returncode == 0,
        "returncode": completed.returncode,
    }
    if completed.returncode != 0:
        check["stdout_tail"] = (completed.stdout or "")[-1000:]
        check["stderr_tail"] = (completed.stderr or "")[-1000:]
    return check


def main() -> int:
    started_at = now_iso()
    result: dict[str, object] = {
        "experiment_id": "self_experiment",
        "claim_id": "self.claim",
        "started_at": started_at,
    }
    try:
        checks = [
            run_check("deepening_gates_self_test", ["tools/bio_reality/deepening_gates.py", "--self-test"]),
            run_check("bio_reality_loop_self_test", ["tools/bio_reality/bio_reality_loop.py", "--self-test"]),
            run_check("agent_bus_self_test", ["tools/bio_reality/agent_bus.py", "--self-test"]),
        ]
        checks.append(
            {
                "name": "self_check",
                "passed": all(check.get("passed") is True for check in checks),
            }
        )
        result.update(
            {
                "status": "passed" if all(check.get("passed") is True for check in checks) else "failed",
                "completed_at": now_iso(),
                "checks": checks,
                "result": {
                    "boundary": "BioReality self-check only; no codon geometry is promoted across biological layers.",
                    "checked_gate_count": len(checks) - 1,
                },
            }
        )
    except Exception as exc:
        result.update(
            {
                "status": "error",
                "completed_at": now_iso(),
                "checks": [],
                "result": {},
                "notes": str(exc),
            }
        )
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

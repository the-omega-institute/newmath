#!/usr/bin/env python3
"""Verify the pinned automath F-A2 certificate snapshot."""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


EXPECTED_COMMIT = "caa043a7733205c0152ec685d9e1870697077b70"
EXPECTED_LEAN_PATH = "lean4/Omega/GroupUnification/Window6ModpstarSpectralCollision.lean"
EXPECTED_OBJECT = "paper_window6_modpstar_spectral_collision"
SNAPSHOT_PATH = (
    "tools/fibonacci_reality/data/"
    "automath_cert_window6_modpstar_571_spectral_collision.json"
)


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": passed, "reason": reason}


def main() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    snapshot_path = repo_root / SNAPSHOT_PATH
    if not snapshot_path.exists():
        print(json.dumps({"status": "needs_data", "checks": [], "result": {"missing": str(snapshot_path)}}))
        return

    try:
        snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"status": "error", "checks": [], "result": {"error": str(exc)}}))
        return

    excerpt = str(snapshot.get("captured_excerpt") or "")
    object_name = str(snapshot.get("object") or "")
    theorem_present = f"theorem {object_name}" in excerpt or f"lemma {object_name}" in excerpt
    has_forbidden_token = re.search(r"\bsorry\b|\badmit\b", excerpt) is not None
    certificate_ok = theorem_present and not has_forbidden_token

    ref_ok = (
        snapshot.get("object") == EXPECTED_OBJECT
        and snapshot.get("lean_path") == EXPECTED_LEAN_PATH
        and snapshot.get("commit") == EXPECTED_COMMIT
    )

    checks = [
        check(
            "automath_certificate_present_sorry_free",
            certificate_ok,
            "certificate theorem is present and no sorry/admit token appears"
            if certificate_ok
            else "certificate theorem is absent or contains a sorry/admit token",
        ),
        check(
            "automath_certificate_ref_matches",
            ref_ok,
            "snapshot object, Lean path, and commit match the pinned certificate"
            if ref_ok
            else "snapshot object, Lean path, or commit differs from the pinned certificate",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "status": status,
        "checks": checks,
        "result": {
            "snapshot": SNAPSHOT_PATH,
            "object": EXPECTED_OBJECT,
            "lean_path": EXPECTED_LEAN_PATH,
            "commit": EXPECTED_COMMIT,
        },
    }
    print(json.dumps(result, ensure_ascii=False))


if __name__ == "__main__":
    main()

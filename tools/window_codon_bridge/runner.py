#!/usr/bin/env python3
"""Lean experiment runner for the Window6<->codon-Q6 bridge daemon.

Runs a bridge derivation script as a subprocess (cwd=repo_root), parses the last
JSON line it prints, and returns the verdict. Bridge verdict vocabulary:
certified / refuted / coincidence / needs_derivation.
"""
from __future__ import annotations
import json, subprocess, sys
from pathlib import Path

VALID = {"certified", "refuted", "coincidence", "needs_derivation"}


def run_experiment(spec: dict, repo_root: Path, timeout_seconds: int = 600) -> dict:
    script = spec.get("script_path")
    if not script:
        return {"status": "needs_derivation", "reason": "no script_path (derivation not yet authored)",
                "experiment_id": spec.get("experiment_id"), "claim_id": spec.get("claim_id")}
    path = repo_root / script
    if not path.exists():
        return {"status": "needs_derivation", "reason": f"script missing: {script}",
                "experiment_id": spec.get("experiment_id"), "claim_id": spec.get("claim_id")}
    try:
        proc = subprocess.run([sys.executable, str(path)], cwd=str(repo_root),
                              capture_output=True, text=True, timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        return {"status": "needs_derivation", "reason": "timeout", "experiment_id": spec.get("experiment_id")}
    out = (proc.stdout or "").strip().splitlines()
    parsed = None
    for line in reversed(out):
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                parsed = json.loads(line); break
            except Exception:
                continue
    if parsed is None:
        return {"status": "needs_derivation", "reason": "no JSON verdict emitted",
                "experiment_id": spec.get("experiment_id"), "stderr_tail": (proc.stderr or "")[-400:],
                "returncode": proc.returncode}
    if parsed.get("status") not in VALID:
        parsed["status"] = "needs_derivation"
        parsed.setdefault("reason", "emitted status not in bridge vocabulary")
    parsed["returncode"] = proc.returncode
    return parsed


if __name__ == "__main__":
    # ad-hoc: run one experiment by script path
    rr = Path(__file__).resolve().parents[2]
    spec = {"experiment_id": "adhoc", "script_path": sys.argv[1]} if len(sys.argv) > 1 else {}
    print(json.dumps(run_experiment(spec, rr), ensure_ascii=False, indent=1))

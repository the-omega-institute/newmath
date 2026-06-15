#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

from store import LeWMStore, dedup_by_key


SCRIPT_DIR = Path(__file__).resolve().parent
SURVEY_DIR = SCRIPT_DIR.parent
ROOT = SURVEY_DIR / "code"
STATUS_PATH = SURVEY_DIR / "reports" / "g2n_integrated_a100_closure_status.json"
DEFAULT_INTERVAL_SECONDS = 300
G2N_HYPOTHESIS_IDS = (
    "fi-018.g2n-a100-strongest-paired",
    "fi-019.g2n-a100-selective-sweep",
    "fi-020.g2n-a100-permutation-guard",
)


def run_step(cmd: list[str], *, cwd: Path) -> dict[str, Any]:
    proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    return {
        "cmd": cmd,
        "returncode": int(proc.returncode),
        "stdout_tail": (proc.stdout or "")[-1600:],
        "stderr_tail": (proc.stderr or "")[-1600:],
    }


def sync_seed_hypotheses() -> dict[str, Any]:
    store = LeWMStore()
    g2n_ids = set(G2N_HYPOTHESIS_IDS)
    seed = [item for item in store.load_seed_hypotheses() if str(item.get("hypothesis_id") or "") in g2n_ids]
    current = store.load_hypotheses()
    current = [item for item in current if str(item.get("hypothesis_id") or "") not in g2n_ids]
    before = len(current)
    combined = dedup_by_key(current + seed, "hypothesis_id")
    store.write_hypotheses(combined)
    return {"before": before, "after": len(combined), "seed": len(seed)}


def run_once(args: argparse.Namespace) -> dict[str, Any]:
    sync = sync_seed_hypotheses()
    closure_cmd = [sys.executable, str(ROOT / "_g2n_a100_closure_pipeline.py")]
    if bool(args.pull_remote):
        closure_cmd.append("--pull-remote")
    if bool(args.no_analyses):
        closure_cmd.append("--no-analyses")
    closure = run_step(closure_cmd, cwd=SURVEY_DIR)
    executor_cmd = [sys.executable, str(SCRIPT_DIR / "executor.py"), "--max-workers", str(int(args.max_workers))]
    for hypothesis_id in G2N_HYPOTHESIS_IDS:
        executor_cmd.extend(["--hypothesis-id", hypothesis_id])
    executor = run_step(executor_cmd, cwd=SURVEY_DIR)
    canonical = run_step([sys.executable, str(SCRIPT_DIR / "canonical_adapter.py")], cwd=SURVEY_DIR)
    status: dict[str, Any] | None = None
    if STATUS_PATH.exists():
        loaded = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
        if isinstance(loaded, dict):
            status = loaded.get("overall") if isinstance(loaded.get("overall"), dict) else loaded
    return {
        "sync_seed_hypotheses": sync,
        "closure_pipeline": closure,
        "executor": executor,
        "canonical_adapter": canonical,
        "closure_status": status,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Run the G2N target-oriented autoresearch loop")
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL_SECONDS)
    parser.add_argument("--pull-remote", action="store_true")
    parser.add_argument("--no-analyses", action="store_true")
    parser.add_argument("--max-workers", type=int, default=1)
    args = parser.parse_args()

    while True:
        result = run_once(args)
        print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)
        failed = [
            key
            for key in ("closure_pipeline", "executor", "canonical_adapter")
            if int(result[key]["returncode"]) != 0
        ]
        if failed:
            return 1
        if bool(args.once):
            return 0
        time.sleep(max(1.0, float(args.interval_seconds)))


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Cadence supervisor for the LeWM autoresearch loop."""

from __future__ import annotations

import argparse
import json
import signal
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

try:
    import lanes
    from framework import LoopState, LoopUnit, NestedLoopRunner
    from store import LeWMPaths, LeWMStore, write_jsonl
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import lanes
    from framework import LoopState, LoopUnit, NestedLoopRunner
    from store import LeWMPaths, LeWMStore, write_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "state"
LOG_DIR = STATE_DIR / "supervisor_logs"
STOP_FILE = SCRIPT_DIR / ".stop"
DEFAULT_INTERVAL_SECONDS = 300
_STOP_REQUESTED = False


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def supervisor_log(message: str) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{now_iso()}] {message}"
    print(line, flush=True)
    with (LOG_DIR / "supervisor.log").open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _handle_signal(_signum: int, _frame: object) -> None:
    global _STOP_REQUESTED
    _STOP_REQUESTED = True


def should_stop() -> bool:
    return _STOP_REQUESTED or STOP_FILE.exists()


def build_runner(paths: LeWMPaths) -> NestedLoopRunner:
    store = LeWMStore(paths)
    return NestedLoopRunner(
        [
            LoopUnit("lewm_H_hypothesis", lambda: lanes.run_hypothesis_lane(store)),
            LoopUnit("lewm_E_experiment", lambda: lanes.run_experiment_lane(store)),
            LoopUnit("lewm_V_stub_verdict", lambda: lanes.run_stub_verdict_lane(store)),
            LoopUnit("lewm_G_gate", lambda: lanes.run_gate_lane(store)),
            LoopUnit("lewm_W_writeback", lambda: lanes.run_writeback_lane(store)),
        ],
        LoopState(paths.loop_state),
    )


def _paths_from_root(root: Path) -> LeWMPaths:
    return LeWMPaths(
        root=root,
        hypotheses=root / "state" / "hypotheses.jsonl",
        seed_hypotheses=root / "seed_hypotheses.jsonl",
        experiments=root / "state" / "experiments.jsonl",
        contacts=root / "state" / "reality_contacts.jsonl",
        verdicts=root / "state" / "verdicts.jsonl",
        gate_results=root / "state" / "gate_results.jsonl",
        verified_findings=root / "state" / "verified_findings.jsonl",
        events=root / "state" / "events.jsonl",
        agent_tasks=root / "state" / "agent_tasks.jsonl",
        dispatch_results=root / "state" / "dispatch_results.jsonl",
        dispatch_results_archive=root / "state" / "dispatch_results.archive.jsonl",
        lane_dashboard=root / "state" / "lane_dashboard.md",
        loop_state=root / "state" / "loop_state.json",
    )


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        paths = _paths_from_root(root)
        write_jsonl(
            paths.seed_hypotheses,
            [
                {
                    "hypothesis_id": "fi-001.cvar-tail",
                    "predicate": "CVaR tail objective can reduce allocation_delta.",
                    "failure_surface": "allocation_delta",
                    "horizon": {"steps": [1, 4, 8]},
                    "perturbation_family": "tail-risk weighting",
                    "carrier": "pusht_latent_large.npz",
                    "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
                    "reality_contact_refs": ["pusht.phase2c.export"],
                    "status": "open",
                }
            ],
        )
        runner = build_runner(paths)
        results = runner.run_once()
        if not all(result.status == "ok" for result in results):
            print(json.dumps([result.__dict__ for result in results], indent=2), file=sys.stderr)
            return 1
        if not paths.loop_state.exists() or not paths.gate_results.exists():
            print(json.dumps({"loop_state": paths.loop_state.exists(), "gate_results": paths.gate_results.exists()}), file=sys.stderr)
            return 1
    print("[lewm-supervisor] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the LeWM autoresearch supervisor")
    parser.add_argument("--once", action="store_true", help="Run one cycle and exit")
    parser.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL_SECONDS)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()

    signal.signal(signal.SIGINT, _handle_signal)
    signal.signal(signal.SIGTERM, _handle_signal)
    paths = LeWMPaths()
    runner = build_runner(paths)
    supervisor_log("starting LeWM autoresearch supervisor")
    while not should_stop():
        results = runner.run_once()
        summary = [{"name": result.name, "status": result.status, "summary": result.summary} for result in results]
        lanes.write_dashboard(LeWMStore(paths), [item["summary"] for item in summary if isinstance(item.get("summary"), dict)])
        supervisor_log(f"cycle {json.dumps(summary, sort_keys=True)}")
        if args.once:
            return 0 if all(result.status in {"ok", "skipped"} for result in results) else 1
        time.sleep(max(1.0, float(args.interval_seconds)))
    supervisor_log("stopping LeWM autoresearch supervisor")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

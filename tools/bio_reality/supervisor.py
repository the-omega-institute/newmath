#!/usr/bin/env python3
"""BioReality supervisor for repeated conjecture-deepening loops."""

from __future__ import annotations

import argparse
import json
import signal
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

try:
    import lanes
    from framework import LoopState, LoopUnit, NestedLoopRunner
    from store import BioRealityPaths, BioRealityStore
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import lanes
    from framework import LoopState, LoopUnit, NestedLoopRunner
    from store import BioRealityPaths, BioRealityStore


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


def build_runner(paths: BioRealityPaths, *, execute_codex: bool = True, max_dispatch: int = 1) -> NestedLoopRunner:
    store = BioRealityStore(paths)

    def packet_targets() -> dict[str, object]:
        return lanes.run_packet_lane(store)

    def vision_intake() -> dict[str, object]:
        return lanes.run_vision_lane(store)

    def gate_and_plan() -> dict[str, object]:
        return lanes.run_gate_lane(store)

    def agent_dispatch() -> dict[str, object]:
        return lanes.run_agent_lane(store, execute_codex=execute_codex, max_dispatch=max_dispatch)

    def writeback_paper() -> dict[str, object]:
        return lanes.run_writeback_lane(store)

    def quality_hardening() -> dict[str, object]:
        return lanes.run_quality_lane(store)

    def assimilate_signals() -> dict[str, object]:
        return lanes.run_assimilation_lane(paths)

    return NestedLoopRunner(
        [
            LoopUnit("bio_P_packet_targets", packet_targets),
            LoopUnit("bio_V_vision_intake", vision_intake),
            LoopUnit("bio_G_gate_and_plan", gate_and_plan),
            LoopUnit("bio_R_agent_dispatch", agent_dispatch),
            LoopUnit("bio_W_writeback_paper", writeback_paper),
            LoopUnit("bio_Q_quality_hardening", quality_hardening),
            LoopUnit("bio_A_assimilate_signals", assimilate_signals),
        ],
        LoopState(STATE_DIR / "loop_state.json"),
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run the BioReality deepening supervisor")
    parser.add_argument("--once", action="store_true", help="Run one cycle and exit")
    parser.add_argument("--interval-seconds", type=float, default=DEFAULT_INTERVAL_SECONDS)
    parser.add_argument("--plan-only", action="store_true", help="Plan agent tasks without invoking Codex")
    parser.add_argument("--max-dispatch", type=int, default=1, help="Maximum Codex tasks to dispatch in one cycle")
    parser.add_argument("--conjectures", default=str(BioRealityPaths.conjectures))
    parser.add_argument("--contacts", default=str(BioRealityPaths.contacts))
    parser.add_argument("--probes", default=str(BioRealityPaths.probes))
    parser.add_argument("--mismatches", default=str(BioRealityPaths.mismatches))
    parser.add_argument("--gate-results", default=str(BioRealityPaths.gate_results))
    parser.add_argument("--deepening-tasks", default=str(BioRealityPaths.deepening_tasks))
    parser.add_argument("--review-queue", default=str(BioRealityPaths.review_queue))
    parser.add_argument("--packet-targets", default=str(BioRealityPaths.packet_targets))
    parser.add_argument("--events", default=str(BioRealityPaths.events))
    parser.add_argument("--agent-tasks", default=str(BioRealityPaths.agent_tasks))
    parser.add_argument("--agent-reviews", default=str(BioRealityPaths.agent_reviews))
    parser.add_argument("--dispatch-results", default=str(BioRealityPaths.dispatch_results))
    parser.add_argument("--hardening-targets", default=str(BioRealityPaths.hardening_targets))
    parser.add_argument("--lane-dashboard", default=str(BioRealityPaths.lane_dashboard))
    parser.add_argument("--vision-dir", default=str(BioRealityPaths.vision_dir))
    parser.add_argument("--vision-ledger", default=str(BioRealityPaths.vision_ledger))
    parser.add_argument("--paper-main", default=str(BioRealityPaths.paper_main))
    parser.add_argument("--paper-part", default=str(BioRealityPaths.paper_part))
    args = parser.parse_args(argv)

    signal.signal(signal.SIGINT, _handle_signal)
    signal.signal(signal.SIGTERM, _handle_signal)
    paths = BioRealityPaths(
        root=SCRIPT_DIR,
        conjectures=Path(args.conjectures),
        contacts=Path(args.contacts),
        probes=Path(args.probes),
        mismatches=Path(args.mismatches),
        gate_results=Path(args.gate_results),
        deepening_tasks=Path(args.deepening_tasks),
        review_queue=Path(args.review_queue),
        packet_targets=Path(args.packet_targets),
        events=Path(args.events),
        agent_tasks=Path(args.agent_tasks),
        agent_reviews=Path(args.agent_reviews),
        dispatch_results=Path(args.dispatch_results),
        hardening_targets=Path(args.hardening_targets),
        lane_dashboard=Path(args.lane_dashboard),
        vision_dir=Path(args.vision_dir),
        vision_ledger=Path(args.vision_ledger),
        paper_main=Path(args.paper_main),
        paper_part=Path(args.paper_part),
    )

    runner = build_runner(paths, execute_codex=not args.plan_only, max_dispatch=max(0, args.max_dispatch))
    supervisor_log("starting BioReality supervisor")
    while not should_stop():
        results = runner.run_once()
        summary = [
            {"name": result.name, "status": result.status, "summary": result.summary}
            for result in results
        ]
        supervisor_log(f"cycle {json.dumps(summary, sort_keys=True)}")
        if args.once:
            return 0 if all(result.status in {"ok", "skipped"} for result in results) else 1
        time.sleep(max(1.0, float(args.interval_seconds)))
    supervisor_log("stopping BioReality supervisor")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

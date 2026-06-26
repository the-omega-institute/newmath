#!/usr/bin/env python3
"""Restartable nested-loop spine for LeWM autoresearch lanes.

This is the domain-neutral part of BioReality's loop framework: each lane has
its own checkpoint record, failures are localized to the failing lane, and a
later run can resume from the JSON checkpoint without replay assumptions.
"""

from __future__ import annotations

import argparse
import json
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "state"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


@dataclass(frozen=True)
class LoopResult:
    name: str
    status: str
    summary: dict[str, Any]


@dataclass(frozen=True)
class LoopUnit:
    name: str
    runner: Callable[[], dict[str, Any]]
    cooldown_seconds: float = 0.0


class LoopState:
    def __init__(self, path: Path | None = None) -> None:
        self.path = path or (STATE_DIR / "loop_state.json")
        self.data = self._load()

    def _load(self) -> dict[str, Any]:
        if not self.path.exists():
            return {"loops": {}}
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            return {"loops": {}}
        return data if isinstance(data, dict) else {"loops": {}}

    def save(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(self.data, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def loop_record(self, name: str) -> dict[str, Any]:
        loops = self.data.setdefault("loops", {})
        record = loops.setdefault(name, {})
        if not isinstance(record, dict):
            loops[name] = {}
            return loops[name]
        return record

    def should_run(self, unit: LoopUnit, now: float | None = None) -> bool:
        if unit.cooldown_seconds <= 0:
            return True
        record = self.loop_record(unit.name)
        last_ts = float(record.get("last_attempt_ts") or 0.0)
        return (now if now is not None else time.time()) - last_ts >= unit.cooldown_seconds

    def mark_ok(self, name: str, summary: dict[str, Any]) -> None:
        record = self.loop_record(name)
        record.update(
            {
                "last_status": "ok",
                "last_ok_at": now_iso(),
                "last_attempt_ts": time.time(),
                "last_summary": summary,
                "failure_count": 0,
            }
        )
        self.save()

    def mark_skip(self, name: str, reason: str) -> None:
        record = self.loop_record(name)
        record.update(
            {
                "last_status": "skipped",
                "last_skip_at": now_iso(),
                "last_attempt_ts": time.time(),
                "last_skip_reason": reason,
            }
        )
        self.save()

    def mark_error(self, name: str, error: Exception) -> None:
        record = self.loop_record(name)
        failure_count = int(record.get("failure_count") or 0) + 1
        record.update(
            {
                "last_status": "error",
                "last_error_at": now_iso(),
                "last_attempt_ts": time.time(),
                "last_error": str(error),
                "failure_count": failure_count,
            }
        )
        self.save()


class NestedLoopRunner:
    def __init__(self, units: list[LoopUnit], state: LoopState | None = None) -> None:
        self.units = units
        self.state = state or LoopState()

    def run_once(self) -> list[LoopResult]:
        results: list[LoopResult] = []
        now = time.time()
        for unit in self.units:
            if not self.state.should_run(unit, now):
                self.state.mark_skip(unit.name, "cooldown")
                results.append(LoopResult(unit.name, "skipped", {"reason": "cooldown"}))
                continue
            try:
                summary = unit.runner()
            except Exception as exc:
                self.state.mark_error(unit.name, exc)
                results.append(LoopResult(unit.name, "error", {"error": str(exc)}))
                continue
            self.state.mark_ok(unit.name, summary)
            results.append(LoopResult(unit.name, "ok", summary))
        return results


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        state = LoopState(Path(tmp) / "loop_state.json")
        calls: list[str] = []

        def ok_lane() -> dict[str, Any]:
            calls.append("ok")
            return {"ran": True}

        def failing_lane() -> dict[str, Any]:
            calls.append("fail")
            raise RuntimeError("fixture failure")

        def after_failure_lane() -> dict[str, Any]:
            calls.append("after")
            return {"continued": True}

        runner = NestedLoopRunner(
            [
                LoopUnit("ok_lane", ok_lane),
                LoopUnit("failing_lane", failing_lane),
                LoopUnit("after_failure_lane", after_failure_lane),
                LoopUnit("cooldown_lane", ok_lane, cooldown_seconds=3600),
            ],
            state,
        )
        first = runner.run_once()
        second = runner.run_once()
        reloaded = LoopState(Path(tmp) / "loop_state.json")
        loops = reloaded.data.get("loops", {})
        checks = [
            [result.status for result in first] == ["ok", "error", "ok", "ok"],
            [result.status for result in second] == ["ok", "error", "ok", "skipped"],
            loops["failing_lane"]["failure_count"] == 2,
            loops["after_failure_lane"]["last_status"] == "ok",
            loops["cooldown_lane"]["last_status"] == "skipped",
            calls.count("after") == 2,
        ]
        if not all(checks):
            print(json.dumps({"first": [r.__dict__ for r in first], "second": [r.__dict__ for r in second], "loops": loops}, indent=2))
            return 1
    print("[lewm-framework] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="LeWM autoresearch nested-loop framework")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    print("[lewm-framework] import this module or run --self-test")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

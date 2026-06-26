#!/usr/bin/env python3
"""Nested-loop framework for BioReality pipeline components."""

from __future__ import annotations

import json
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
        return record if isinstance(record, dict) else {}

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

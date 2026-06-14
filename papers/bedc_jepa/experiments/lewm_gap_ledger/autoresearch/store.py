#!/usr/bin/env python3
"""JSONL store helpers for LeWM autoresearch state."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROLLING_ACTIVE_LIMIT = 200


@dataclass(frozen=True)
class LeWMPaths:
    root: Path = SCRIPT_DIR
    hypotheses: Path = SCRIPT_DIR / "state" / "hypotheses.jsonl"
    seed_hypotheses: Path = SCRIPT_DIR / "seed_hypotheses.jsonl"
    experiments: Path = SCRIPT_DIR / "state" / "experiments.jsonl"
    contacts: Path = SCRIPT_DIR / "state" / "reality_contacts.jsonl"
    verdicts: Path = SCRIPT_DIR / "state" / "verdicts.jsonl"
    gate_results: Path = SCRIPT_DIR / "state" / "gate_results.jsonl"
    verified_findings: Path = SCRIPT_DIR / "state" / "verified_findings.jsonl"
    deepening_tasks: Path = SCRIPT_DIR / "state" / "deepening_tasks.jsonl"
    review_queue: Path = SCRIPT_DIR / "state" / "review_queue.jsonl"
    events: Path = SCRIPT_DIR / "state" / "events.jsonl"
    agent_tasks: Path = SCRIPT_DIR / "state" / "agent_tasks.jsonl"
    dispatch_results: Path = SCRIPT_DIR / "state" / "dispatch_results.jsonl"
    dispatch_results_archive: Path = SCRIPT_DIR / "state" / "dispatch_results.archive.jsonl"
    lane_dashboard: Path = SCRIPT_DIR / "state" / "lane_dashboard.md"
    loop_state: Path = SCRIPT_DIR / "state" / "loop_state.json"


def read_jsonl(path: Path, *, allow_missing: bool = True) -> list[dict[str, Any]]:
    if not path.exists():
        if allow_missing:
            return []
        raise FileNotFoundError(path)
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                data = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object")
            records.append(data)
    return records


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def append_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    if not records:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def stable_record_key(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if value is not None:
        return str(value)
    return json.dumps(record, ensure_ascii=True, sort_keys=True)


def dedup_by_key(records: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for record in records:
        value = stable_record_key(record, key)
        if value in seen:
            continue
        seen.add(value)
        out.append(record)
    return out


def upsert_by_key(records: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    by_key: dict[str, dict[str, Any]] = {}
    for record in records:
        by_key[stable_record_key(record, key)] = record
    return list(by_key.values())


class LeWMStore:
    def __init__(self, paths: LeWMPaths | None = None) -> None:
        self.paths = paths or LeWMPaths()

    def load_hypotheses(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.hypotheses)

    def write_hypotheses(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.hypotheses, records)

    def load_seed_hypotheses(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.seed_hypotheses)

    def load_experiments(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.experiments)

    def write_experiments(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.experiments, records)

    def load_contacts(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.contacts)

    def write_contacts(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.contacts, records)

    def load_verdicts(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.verdicts)

    def write_verdicts(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.verdicts, records)

    def load_gate_results(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.gate_results)

    def write_gate_results(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.gate_results, records)

    def load_verified_findings(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.verified_findings)

    def write_verified_findings(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.verified_findings, records)

    def load_deepening_tasks(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.deepening_tasks)

    def write_deepening_tasks(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.deepening_tasks, records)

    def load_review_queue(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.review_queue)

    def write_review_queue(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.review_queue, records)

    def load_events(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.events)

    def write_events(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.events, records)

    def load_agent_tasks(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.agent_tasks)

    def write_agent_tasks(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.agent_tasks, records)

    def append_dispatch_results(self, records: list[dict[str, Any]]) -> None:
        self._upsert_rolling(self.paths.dispatch_results, self.paths.dispatch_results_archive, records, key="task_id")

    def _upsert_rolling(self, active_path: Path, archive_path: Path, records: list[dict[str, Any]], *, key: str) -> None:
        active = read_jsonl(active_path)
        combined = upsert_by_key(active + records, key)
        if len(combined) <= ROLLING_ACTIVE_LIMIT:
            if records:
                write_jsonl(active_path, combined)
            return
        overflow = combined[:-ROLLING_ACTIVE_LIMIT]
        keep = combined[-ROLLING_ACTIVE_LIMIT:]
        append_jsonl(archive_path, overflow)
        write_jsonl(active_path, keep)

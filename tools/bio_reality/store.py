#!/usr/bin/env python3
"""JSONL store helpers for the BioReality deepening loop."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
ROLLING_ACTIVE_LIMIT = 200


@dataclass(frozen=True)
class BioRealityPaths:
    root: Path = SCRIPT_DIR
    conjectures: Path = SCRIPT_DIR / "inbox" / "conjectures.jsonl"
    contacts: Path = SCRIPT_DIR / "inbox" / "reality_contacts.jsonl"
    probes: Path = SCRIPT_DIR / "inbox" / "probes.jsonl"
    mismatches: Path = SCRIPT_DIR / "inbox" / "mismatches.jsonl"
    gate_results: Path = SCRIPT_DIR / "out" / "gate_results.jsonl"
    deepening_tasks: Path = SCRIPT_DIR / "out" / "deepening_tasks.jsonl"
    review_queue: Path = SCRIPT_DIR / "out" / "review_queue.jsonl"
    packet_targets: Path = SCRIPT_DIR / "out" / "packet_targets.jsonl"
    events: Path = SCRIPT_DIR / "out" / "events.jsonl"
    agent_tasks: Path = SCRIPT_DIR / "out" / "agent_tasks.jsonl"
    agent_reviews: Path = SCRIPT_DIR / "out" / "agent_reviews.jsonl"
    agent_reviews_archive: Path = SCRIPT_DIR / "out" / "agent_reviews.archive.jsonl"
    dispatch_results: Path = SCRIPT_DIR / "out" / "dispatch_results.jsonl"
    dispatch_results_archive: Path = SCRIPT_DIR / "out" / "dispatch_results.archive.jsonl"
    hardening_targets: Path = SCRIPT_DIR / "out" / "hardening_targets.jsonl"
    lane_dashboard: Path = SCRIPT_DIR / "out" / "lane_dashboard.md"
    claims_registry: Path = SCRIPT_DIR / "registries" / "claims.json"
    experiments_registry: Path = SCRIPT_DIR / "registries" / "experiments.json"
    experiment_runs: Path = SCRIPT_DIR / "state" / "experiment_runs.jsonl"
    keep_lane_log: Path = SCRIPT_DIR / "state" / "keep_lane.log"
    keep_lane_state: Path = SCRIPT_DIR / "state" / "keep_lane.json"
    sync_lane_state: Path = SCRIPT_DIR / "state" / "sync_lane.json"
    sync_lane_log: Path = SCRIPT_DIR / "state" / "sync_lane.log"
    loning_intelligence: Path = SCRIPT_DIR / "state" / "loning_intelligence.jsonl"
    experiments_dir: Path = SCRIPT_DIR / "experiments"
    data_dir: Path = SCRIPT_DIR / "data"
    vision_dir: Path = SCRIPT_DIR / "vision"
    vision_ledger: Path = SCRIPT_DIR / "vision" / "ledger" / "intake_evaluations.jsonl"
    paper_main: Path = SCRIPT_DIR.parent.parent / "papers" / "bio_reality" / "main.tex"
    paper_part: Path = SCRIPT_DIR.parent.parent / "papers" / "bio_reality" / "parts" / "codon_window_reality_boundary.tex"


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


def _record_key(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if value is not None:
        return str(value)
    return json.dumps(record, ensure_ascii=True, sort_keys=True)


def _dedup_by_key(records: list[dict[str, Any]], key: str) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for record in records:
        value = _record_key(record, key)
        if value in seen:
            continue
        seen.add(value)
        out.append(record)
    return out


class BioRealityStore:
    def __init__(self, paths: BioRealityPaths | None = None) -> None:
        self.paths = paths or BioRealityPaths()

    def load_conjectures(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.conjectures)

    def load_contacts(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.contacts)

    def load_probes(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.probes)

    def load_mismatches(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.mismatches)

    def write_conjectures(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.conjectures, records)

    def write_contacts(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.contacts, records)

    def write_probes(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.probes, records)

    def write_mismatches(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.mismatches, records)

    def write_gate_results(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.gate_results, records)

    def write_deepening_tasks(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.deepening_tasks, records)

    def write_review_queue(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.review_queue, records)

    def write_packet_targets(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.packet_targets, records)

    def load_events(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.events)

    def write_events(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.events, records)

    def load_agent_tasks(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.agent_tasks)

    def write_agent_tasks(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.agent_tasks, records)

    def load_agent_reviews(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.agent_reviews)

    def write_agent_reviews(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.agent_reviews, records)

    def append_agent_reviews(self, records: list[dict[str, Any]]) -> None:
        archive = read_jsonl(self.paths.agent_reviews_archive)
        active = _dedup_by_key(read_jsonl(self.paths.agent_reviews), "review_id")
        seen = {_record_key(record, "review_id") for record in archive + active}
        fresh = [record for record in records if _record_key(record, "review_id") not in seen]
        self._append_rolling(self.paths.agent_reviews, self.paths.agent_reviews_archive, fresh, active_records=active)

    def load_dispatch_results(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.dispatch_results)

    def write_dispatch_results(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.dispatch_results, records)

    def append_dispatch_result(self, record: dict[str, Any]) -> None:
        self.append_dispatch_results([record])

    def append_dispatch_results(self, records: list[dict[str, Any]]) -> None:
        self._append_rolling(self.paths.dispatch_results, self.paths.dispatch_results_archive, records)

    def load_hardening_targets(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.hardening_targets)

    def write_hardening_targets(self, records: list[dict[str, Any]]) -> None:
        write_jsonl(self.paths.hardening_targets, records)

    def load_vision_ledger(self) -> list[dict[str, Any]]:
        return read_jsonl(self.paths.vision_ledger)

    def _append_rolling(
        self,
        active_path: Path,
        archive_path: Path,
        records: list[dict[str, Any]],
        *,
        active_records: list[dict[str, Any]] | None = None,
    ) -> None:
        active = list(active_records) if active_records is not None else read_jsonl(active_path)
        combined = active + records
        if len(combined) <= ROLLING_ACTIVE_LIMIT:
            if records or active_records is not None:
                write_jsonl(active_path, combined)
            return
        overflow = combined[:-ROLLING_ACTIVE_LIMIT]
        keep = combined[-ROLLING_ACTIVE_LIMIT:]
        append_jsonl(archive_path, overflow)
        write_jsonl(active_path, keep)

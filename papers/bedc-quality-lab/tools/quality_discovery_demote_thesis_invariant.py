#!/usr/bin/env python3
"""Audit checked-in discovery artifacts for demote-thesis escaped positives."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
SCHEMA_ID = "bedc-quality-lab:demote-thesis-invariant-audit"
ARTIFACT_ID = "bedc-quality-lab:demote-thesis-invariant-audit"
PRODUCER = "tools/quality_discovery_demote_thesis_invariant.py"
SIDECAR_ARTIFACT = "reports/canonical/demote_thesis_invariant_audit.json"
SCOPE_PATHS = (
    "reports/**/*.json",
    "reports/**/*.jsonl",
    "runs/**/*.json",
    "runs/**/*.jsonl",
)

POSITIVE_DISCOVERY_LEVELS = {"D4", "D5"}
NON_POSITIVE_DISCOVERY_LEVELS = {"DN", "DR", "D0", "D1", "D2", "D3"}
POSITIVE_TERMINAL_VALUES = {
    "positive",
    "positive-discovery",
    "positive_discovery",
    "terminal-positive",
    "terminal_positive",
    "discovery_candidate",
    "certified_discovery",
    "accepted_positive",
    "accepted-positive",
}
NON_POSITIVE_TERMINAL_VALUES = {
    "rejected",
    "demoted",
    "ledger-only",
    "ledger_only",
    "not-positive",
    "not_positive",
    "negative",
    "negative-discovery",
    "negative_discovery",
    "observed-negative",
    "observed_negative",
    "audit-improvement-only",
    "audit_improvement_only",
    "rejected-due-to-hidden-debt",
    "rejected_due_to_hidden_debt",
    "rejected-due-to-scope-laundering",
    "rejected_due_to_scope_laundering",
    "revoked-due-to-fresh-evidence",
    "revoked_due_to_fresh_evidence",
    "non-positive",
    "non_positive",
    "fail",
    "failed",
}
TERMINAL_FIELDS = {
    "main_claim_status",
    "final_main_claim_status",
    "verdict",
    "terminal_verdict",
    "claim_verdict",
    "status",
    "result_status",
    "new_status",
}
EVIDENCE_CONTAINER_KEYS = {
    "audit",
    "basis",
    "claim_gate",
    "delta_vs_baseline",
    "deltas",
    "dominance",
    "evidence_basis",
    "frontier",
    "gate_basis",
    "gate_basis_summary",
    "hardgate",
    "hardgate_basis",
    "result",
}
FORBIDDEN_SIDECAR_FIELDS = {
    "certificate_payload",
    "evidence_payload",
    "pseudo_payload",
    "payload",
    "quality_scorecard",
    "scorecard",
    "source_payload",
}
FORBIDDEN_SCORE_FIELDS = {"total_score", "rank", "grade", "hidden_cost_weight"}
FORBIDDEN_POSITIVE_CLAIM_TERMS = {
    "full-lejepa",
    "global-quality",
    "full-tensor-namecert",
    "llm-behavior",
}


@dataclass(frozen=True)
class Frame:
    value: Any
    pointer: str


@dataclass(frozen=True)
class PositiveSignal:
    pointer: str
    signal: str


@dataclass(frozen=True)
class TradeoffEvidence:
    pointer: str
    kind: str
    reason: str


@dataclass(frozen=True)
class ScanDocument:
    relative_path: str
    pointer_prefix: str
    data: Any


def _json_pointer_child(pointer: str, key: str | int) -> str:
    if isinstance(key, int):
        return f"{pointer}[{key}]"
    if pointer == "$":
        return f"$.{key}"
    return f"{pointer}.{key}"


def _walk_frames(value: Any, pointer: str = "$", ancestors: tuple[Frame, ...] = ()) -> Iterable[tuple[Frame, tuple[Frame, ...]]]:
    frame = Frame(value=value, pointer=pointer)
    yield frame, ancestors
    next_ancestors = ancestors + (frame,)
    if isinstance(value, Mapping):
        for key, cell in value.items():
            yield from _walk_frames(cell, _json_pointer_child(pointer, str(key)), next_ancestors)
    elif isinstance(value, list):
        for index, cell in enumerate(value):
            yield from _walk_frames(cell, _json_pointer_child(pointer, index), next_ancestors)


def _walk_keys(value: Any) -> Iterable[str]:
    if isinstance(value, Mapping):
        for key, cell in value.items():
            yield str(key)
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _normalized_text(value: Any) -> str | None:
    if isinstance(value, str):
        return value.strip().lower()
    return None


def _is_positive_terminal(value: Any) -> bool:
    normalized = _normalized_text(value)
    if normalized is None:
        return False
    if normalized in NON_POSITIVE_TERMINAL_VALUES:
        return False
    return normalized in POSITIVE_TERMINAL_VALUES or "positive" in normalized


def _is_non_positive_terminal(value: Any) -> bool:
    normalized = _normalized_text(value)
    return normalized in NON_POSITIVE_TERMINAL_VALUES if normalized is not None else False


def _positive_signal(value: Mapping[str, Any], pointer: str) -> PositiveSignal | None:
    if value.get("positive") is True:
        return PositiveSignal(_json_pointer_child(pointer, "positive"), "positive=true")
    if value.get("positive_discovery") is True:
        return PositiveSignal(_json_pointer_child(pointer, "positive_discovery"), "positive_discovery=true")
    for field in sorted(TERMINAL_FIELDS):
        if _is_positive_terminal(value.get(field)):
            return PositiveSignal(_json_pointer_child(pointer, field), f"{field}={value.get(field)}")
    if value.get("discovery_level") in POSITIVE_DISCOVERY_LEVELS:
        return PositiveSignal(_json_pointer_child(pointer, "discovery_level"), f"discovery_level={value.get('discovery_level')}")
    return None


def _has_explicit_non_positive(value: Any) -> bool:
    if not isinstance(value, Mapping):
        return False
    if value.get("positive") is False or value.get("positive_discovery") is False:
        return True
    if value.get("discovery_level") in NON_POSITIVE_DISCOVERY_LEVELS:
        return True
    return any(_is_non_positive_terminal(value.get(field)) for field in TERMINAL_FIELDS)


def _basis_scoped_child(parent_pointer: str, child_pointer: str) -> bool:
    if parent_pointer == "$":
        suffix = child_pointer[1:]
    else:
        suffix = child_pointer.removeprefix(parent_pointer)
    parts = suffix.replace("[", ".[").split(".")
    return any(part in EVIDENCE_CONTAINER_KEYS or part.endswith("_basis") for part in parts)


def _guarded_by_non_positive_ancestor(frame: Frame, ancestors: Sequence[Frame]) -> str | None:
    for ancestor in ancestors:
        if not _has_explicit_non_positive(ancestor.value):
            continue
        if _basis_scoped_child(ancestor.pointer, frame.pointer):
            return ancestor.pointer
    return None


def _to_number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int | float):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return None
    return None


def _direct_tradeoff_evidence(value: Mapping[str, Any], pointer: str) -> TradeoffEvidence | None:
    for key in ("audit_improvement_tradeoff", "training_audit_improvement_tradeoff"):
        if value.get(key) is True:
            evidence_pointer = _json_pointer_child(pointer, key)
            return TradeoffEvidence(evidence_pointer, key, f"{key}=true")

    has_debt_delta = "debt_delta" in value
    has_benefit_delta = "benefit_delta" in value
    if has_debt_delta and has_benefit_delta:
        debt_delta = _to_number(value.get("debt_delta"))
        benefit_delta = _to_number(value.get("benefit_delta"))
        if debt_delta is None or benefit_delta is None:
            return TradeoffEvidence(pointer, "malformed_numeric_tradeoff", "debt_delta and benefit_delta must be numeric")
        if debt_delta < 0 and benefit_delta < 0:
            return TradeoffEvidence(pointer, "debt_delta_and_benefit_delta_down", "debt_delta<0 and benefit_delta<0")

    if value.get("debt_down") is True and value.get("benefit_down") is True:
        return TradeoffEvidence(pointer, "debt_down_and_benefit_down", "debt_down=true and benefit_down=true")

    return None


def _search_tradeoff_evidence(value: Any, pointer: str, *, recursive: bool) -> TradeoffEvidence | None:
    if isinstance(value, Mapping):
        direct = _direct_tradeoff_evidence(value, pointer)
        if direct is not None:
            return direct
        for key, cell in value.items():
            key_text = str(key)
            if recursive:
                evidence = _search_tradeoff_evidence(cell, _json_pointer_child(pointer, key_text), recursive=True)
                if evidence is not None:
                    return evidence
            elif key_text in EVIDENCE_CONTAINER_KEYS or key_text.endswith("_basis"):
                evidence = _search_tradeoff_evidence(cell, _json_pointer_child(pointer, key_text), recursive=True)
                if evidence is not None:
                    return evidence
    elif isinstance(value, list) and recursive:
        for index, cell in enumerate(value):
            evidence = _search_tradeoff_evidence(cell, _json_pointer_child(pointer, index), recursive=recursive)
            if evidence is not None:
                return evidence
    return None


def _tradeoff_evidence_for_candidate(frame: Frame, ancestors: Sequence[Frame]) -> TradeoffEvidence | None:
    candidate_evidence = _search_tradeoff_evidence(frame.value, frame.pointer, recursive=True)
    if candidate_evidence is not None:
        return candidate_evidence
    for ancestor in reversed(ancestors):
        evidence = _search_tradeoff_evidence(ancestor.value, ancestor.pointer, recursive=False)
        if evidence is not None:
            return evidence
    return None


def _candidate_paths(root: Path, sidecar_path: Path) -> list[Path]:
    excluded = {
        (root / SIDECAR_ARTIFACT).resolve(),
        sidecar_path.resolve(),
    }
    paths: set[Path] = set()
    for pattern in SCOPE_PATHS:
        for path in root.glob(pattern):
            if path.resolve() in excluded:
                continue
            if path.is_file():
                paths.add(path)
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix())


def _read_documents(root: Path, path: Path) -> list[ScanDocument]:
    relative_path = path.relative_to(root).as_posix()
    if path.suffix == ".jsonl":
        documents = []
        for index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
            if not line.strip():
                continue
            documents.append(
                ScanDocument(
                    relative_path=relative_path,
                    pointer_prefix=f"$[{index}]",
                    data=json.loads(line),
                )
            )
        return documents
    return [ScanDocument(relative_path=relative_path, pointer_prefix="$", data=json.loads(path.read_text(encoding="utf-8")))]


def audit_root(root: Path, *, sidecar_artifact: str = SIDECAR_ARTIFACT, generated_at: str | None = None) -> dict[str, Any]:
    base = root.resolve()
    sidecar_path = (base / sidecar_artifact).resolve()
    files = _candidate_paths(base, sidecar_path)
    parsed_document_count = 0
    parsed_object_count = 0
    positive_rows: list[dict[str, Any]] = []
    escaped_positive_rows: list[dict[str, Any]] = []

    for path in files:
        for document in _read_documents(base, path):
            parsed_document_count += 1
            for frame, ancestors in _walk_frames(document.data, document.pointer_prefix):
                if isinstance(frame.value, Mapping):
                    parsed_object_count += 1
                else:
                    continue
                signal = _positive_signal(frame.value, frame.pointer)
                if signal is None:
                    continue
                if _has_explicit_non_positive(frame.value):
                    continue
                guarded_by = _guarded_by_non_positive_ancestor(frame, ancestors)
                if guarded_by is not None:
                    continue
                positive_rows.append(
                    {
                        "file": document.relative_path,
                        "json_pointer": frame.pointer,
                        "positive_signal": signal.signal,
                    }
                )
                evidence = _tradeoff_evidence_for_candidate(frame, ancestors)
                if evidence is None:
                    continue
                escaped_positive_rows.append(
                    {
                        "file": document.relative_path,
                        "json_pointer": frame.pointer,
                        "positive_signal": signal.signal,
                        "tradeoff_evidence_pointer": evidence.pointer,
                        "evidence_kind": evidence.kind,
                        "reason": evidence.reason,
                    }
                )

    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "producer": PRODUCER,
        "scope_paths": list(SCOPE_PATHS),
        "scanned_counts": {
            "files": len(files),
            "documents": parsed_document_count,
            "objects": parsed_object_count,
        },
        "positive_candidate_count": len(positive_rows),
        "escaped_positive_count": len(escaped_positive_rows),
        "status": "fail" if escaped_positive_rows else "pass",
        "escaped_positive_rows": escaped_positive_rows,
        "not_claimed": (
            "This audit only rejects demote-thesis escaped positives and does not certify "
            "positive records or replace producer-local gates."
        ),
    }
    assert_pointer_only_boundary(payload)
    return payload


def assert_pointer_only_boundary(payload: Mapping[str, Any]) -> None:
    keys = set(_walk_keys(payload))
    forbidden = sorted((keys & FORBIDDEN_SIDECAR_FIELDS) | (keys & FORBIDDEN_SCORE_FIELDS))
    if forbidden:
        raise RuntimeError(f"demote-thesis sidecar contains forbidden fields: {forbidden}")
    text = json.dumps(payload, sort_keys=True)
    for forbidden_text in FORBIDDEN_POSITIVE_CLAIM_TERMS:
        if forbidden_text in text:
            raise RuntimeError(f"demote-thesis sidecar contains forbidden positive claim term: {forbidden_text}")


def write_sidecar(root: Path, payload: Mapping[str, Any], *, sidecar_artifact: str = SIDECAR_ARTIFACT) -> Path:
    target = (root / sidecar_artifact).resolve()
    allowed = (root / SIDECAR_ARTIFACT).resolve()
    if target != allowed:
        raise ValueError(f"sidecar may only write {SIDECAR_ARTIFACT}")
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(target)
    return target


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Lab root containing reports/ and runs/.")
    parser.add_argument("--no-write-sidecar", action="store_true", help="Audit without writing the fixed sidecar.")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    payload = audit_root(root)
    if not args.no_write_sidecar:
        write_sidecar(root, payload)
    print(
        "demote-thesis invariant audit "
        f"status={payload['status']} "
        f"files={payload['scanned_counts']['files']} "
        f"positive_candidates={payload['positive_candidate_count']} "
        f"escaped_positive_rows={payload['escaped_positive_count']}"
    )
    return 1 if payload["status"] == "fail" else 0


if __name__ == "__main__":
    raise SystemExit(main())

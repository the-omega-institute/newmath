"""Canonical artifact freshness helpers."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

from bedc_quality_lab.verdict import _scorecard_readiness


SCORECARD_POINTER = "reports/canonical/quality-scorecard.json:$.rows"
SCORECARD_ARTIFACT = "reports/canonical/quality-scorecard.json"
FORMAL_HARDENING_ARTIFACT = "reports/canonical/formal_hardening.json"


@dataclass(frozen=True)
class ArtifactSnapshot:
    path: str
    generated_at: str | None
    sha256: str


@dataclass(frozen=True)
class ScorecardSnapshot:
    scorecard_pointer: str
    scorecard_hash: str
    scorecard_ready: bool
    formal_hardening_ready: bool


def canonical_artifact_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_artifact_snapshot(root: Path, artifact: str) -> ArtifactSnapshot:
    path = root / artifact
    payload = _load_json_object(path)
    generated_at = payload.get("generated_at") if payload is not None and isinstance(payload.get("generated_at"), str) else None
    return ArtifactSnapshot(
        path=artifact,
        generated_at=generated_at,
        sha256=canonical_artifact_hash(path) if path.exists() else "",
    )


def _load_json_object(path: Path) -> Mapping[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, Mapping) else None


def _scorecard_ready(payload: Mapping[str, Any] | None) -> bool:
    if payload is None:
        return False
    ready, _detail = _scorecard_readiness({"quality_scorecard": payload})
    return ready is True


def _formal_hardening_ready(payload: Mapping[str, Any] | None) -> bool:
    if payload is None:
        return False
    return (
        payload.get("ready") is True
        and payload.get("recorded") == payload.get("required")
        and payload.get("gap_count") == 0
    )


def load_scorecard_snapshot(root: Path) -> ScorecardSnapshot:
    scorecard_path = root / SCORECARD_ARTIFACT
    formal_hardening_path = root / FORMAL_HARDENING_ARTIFACT
    scorecard_payload = _load_json_object(scorecard_path)
    formal_hardening_payload = _load_json_object(formal_hardening_path)
    scorecard_hash = canonical_artifact_hash(scorecard_path) if scorecard_path.exists() else ""
    return ScorecardSnapshot(
        scorecard_pointer=SCORECARD_POINTER,
        scorecard_hash=scorecard_hash,
        scorecard_ready=_scorecard_ready(scorecard_payload),
        formal_hardening_ready=_formal_hardening_ready(formal_hardening_payload),
    )

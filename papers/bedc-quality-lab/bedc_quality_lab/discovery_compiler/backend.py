"""Backend interface for discovery compilation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Protocol, Sequence


@dataclass(frozen=True)
class TheoryBackend:
    name: str
    scope_kind: str
    assumptions: tuple[str, ...]
    metrics: tuple[str, ...]
    theorem_rows: tuple[Mapping[str, Any], ...]
    ledger_rows: tuple[Mapping[str, Any], ...]
    hardgates: tuple[Mapping[str, Any], ...]
    not_claimed: tuple[str, ...]


class BackendEvidenceAdapter(Protocol):
    backend: TheoryBackend

    def build_source_spec(self) -> Mapping[str, Any]:
        ...

    def build_pattern_spec(self) -> Mapping[str, Any]:
        ...

    def build_classifier_spec(self) -> Mapping[str, Any]:
        ...

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        ...

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        ...

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        ...

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        ...

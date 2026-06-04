"""Current lab backend adapter for discovery compilation."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.discovery_compiler import projection
from scripts.run_canonical_reports import CANONICAL_REPORTS


class CurrentLabBackendEvidenceAdapter:
    backend = TheoryBackend(
        name="current-lab",
        scope_kind="canonical-lab-reports",
        assumptions=("canonical artifacts are JSON objects",),
        metrics=("discovery_level", "audit_status"),
        theorem_rows=(),
        ledger_rows=(),
        hardgates=(),
        not_claimed=("global model quality",),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {"canonical_reports": [spec.name for spec in CANONICAL_REPORTS]}

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"status": "pointer-only"}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"levels": list(projection.DISCOVERY_LEVELS)}

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        return projection.write_discovery_map(generated_at=generated_at, root=root, canonical_reports=CANONICAL_REPORTS)

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return projection.build_discovery_map(generated_at=generated_at, root=root, canonical_reports=CANONICAL_REPORTS)["rows"]

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)

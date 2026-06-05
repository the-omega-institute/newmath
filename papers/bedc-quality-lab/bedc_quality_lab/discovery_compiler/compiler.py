"""Discovery compiler orchestration."""

from __future__ import annotations

from datetime import datetime, timezone
import importlib
from pathlib import Path
from typing import Any, Mapping

from .backend import BackendEvidenceAdapter
from .negative_reports import write_negative_discovery_reports, write_negative_witness_summary


def _timestamp(generated_at: str | None) -> str:
    return generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()


def load_adapter(path: str) -> BackendEvidenceAdapter:
    module_name, _, object_name = path.partition(":")
    if not module_name or not object_name:
        raise ValueError("adapter path must use module:object form")
    module = importlib.import_module(module_name)
    factory = getattr(module, object_name)
    adapter = factory() if isinstance(factory, type) else factory
    return adapter


def compile_discovery(
    *,
    root: Path,
    generated_at: str | None = None,
    adapter: BackendEvidenceAdapter,
    write_reports: bool = True,
    require_required_negative_reports: bool = True,
) -> Mapping[str, Any]:
    timestamp = _timestamp(generated_at)
    active = adapter
    negative_rows = active.derive_negative_discovery_rows(root=root, generated_at=timestamp)
    negative_payload = {}
    if write_reports:
        negative_payload = write_negative_discovery_reports(
            root=root,
            generated_at=timestamp,
            discovery_rows=negative_rows,
            require_required_ids=require_required_negative_reports,
        )
    map_payload = active.compute_metrics(root=root, generated_at=timestamp)
    summary_payload = write_negative_witness_summary(root=root, generated_at=timestamp) if write_reports else {}
    return {
        "generated_at": timestamp,
        "backend": active.backend.name,
        "discovery_map": map_payload,
        "negative_discovery_reports": negative_payload,
        "negative_witness_summary": summary_payload,
    }

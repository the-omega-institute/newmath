from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Literal, Mapping


MANIFEST_SCHEMA_ID = "bedc-quality-lab:admission-manifest"
HASHES_SCHEMA_ID = "bedc-quality-lab:admission-artifact-hashes"
CONFLICTS_SCHEMA_ID = "bedc-quality-lab:admission-conflicts"
LEDGER_ROW_SCHEMA_ID = "bedc-quality-lab:admission-ledger-row"
ADMISSION_MANIFEST = Path("reports/canonical/admission_manifest.json")
ADMISSION_ARTIFACT_HASHES = Path("reports/canonical/admission_artifact_hashes.json")
ADMISSION_CONFLICTS = Path("reports/canonical/admission_conflicts.json")
ADMISSION_LEDGER = Path("reports/canonical/admission_ledger.jsonl")
ALLOWED_ADMISSION_STATUSES = frozenset({"accepted", "bounded_negative", "bounded-negative"})

ReconciliationStatus = Literal["applied", "unchanged", "would-change", "conflict"]


class AdmissionReconciliationError(ValueError):
    pass


@dataclass(frozen=True)
class AdmissionEntry:
    artifact_id: str
    artifact_path: str
    artifact_sha256: str
    admission_status: str

    def to_payload(self) -> dict[str, Any]:
        return {
            "admission_status": self.admission_status,
            "artifact_id": self.artifact_id,
            "artifact_path": self.artifact_path,
            "artifact_sha256": self.artifact_sha256,
        }


@dataclass(frozen=True)
class AdmissionReconciliationResult:
    status: ReconciliationStatus
    artifact_id: str
    artifact_path: str
    artifact_sha256: str
    conflicts: tuple[dict[str, Any], ...] = ()

    def to_payload(self) -> dict[str, Any]:
        return {
            "status": self.status,
            "artifact_id": self.artifact_id,
            "artifact_path": self.artifact_path,
            "artifact_sha256": self.artifact_sha256,
            "conflicts": [dict(conflict) for conflict in self.conflicts],
        }


def reconcile_admission_artifact(
    artifact_path: str | Path,
    *,
    root: str | Path = ".",
    dry_run: bool = False,
) -> AdmissionReconciliationResult:
    root_path = Path(root).resolve()
    artifact = _resolve_artifact_path(root_path, Path(artifact_path))
    payload, raw = _load_artifact_payload(artifact)
    entry = _entry_from_artifact(root_path, artifact, payload, raw)
    current_entries = _load_manifest_entries(root_path)
    _assert_hash_sidecar_matches(root_path, current_entries)
    audit_admission_ledger(root_path)

    conflicts = _conflicts_for_entry(entry, current_entries)
    if conflicts:
        result = AdmissionReconciliationResult(
            status="conflict",
            artifact_id=entry.artifact_id,
            artifact_path=entry.artifact_path,
            artifact_sha256=entry.artifact_sha256,
            conflicts=tuple(conflicts),
        )
        if not dry_run:
            _write_json(root_path / ADMISSION_CONFLICTS, _conflicts_payload(conflicts))
        return result

    existing = {item.artifact_id: item for item in current_entries}.get(entry.artifact_id)
    if existing is not None:
        return AdmissionReconciliationResult(
            status="unchanged",
            artifact_id=entry.artifact_id,
            artifact_path=entry.artifact_path,
            artifact_sha256=entry.artifact_sha256,
        )

    next_entries = tuple(sorted((*current_entries, entry), key=lambda item: (item.artifact_id, item.artifact_path)))
    if dry_run:
        return AdmissionReconciliationResult(
            status="would-change",
            artifact_id=entry.artifact_id,
            artifact_path=entry.artifact_path,
            artifact_sha256=entry.artifact_sha256,
        )

    _write_json(root_path / ADMISSION_MANIFEST, _manifest_payload(next_entries))
    _write_json(root_path / ADMISSION_ARTIFACT_HASHES, _hashes_payload(next_entries))
    _write_json(root_path / ADMISSION_CONFLICTS, _conflicts_payload(()))
    _append_ledger_row(root_path, entry)
    audit_admission_ledger(root_path)
    return AdmissionReconciliationResult(
        status="applied",
        artifact_id=entry.artifact_id,
        artifact_path=entry.artifact_path,
        artifact_sha256=entry.artifact_sha256,
    )


def audit_admission_ledger(root: str | Path = ".") -> tuple[dict[str, Any], ...]:
    root_path = Path(root).resolve()
    rows = _read_ledger_rows(root_path)
    previous_hash: str | None = None
    entries: list[AdmissionEntry] = []
    for index, row in enumerate(rows, start=1):
        if row.get("sequence") != index:
            raise AdmissionReconciliationError(f"ledger sequence mismatch at row {index}")
        if row.get("previous_row_sha256") != previous_hash:
            raise AdmissionReconciliationError(f"ledger chain mismatch at row {index}")
        observed_hash = row.get("row_sha256")
        if not isinstance(observed_hash, str) or observed_hash != _row_hash(row):
            raise AdmissionReconciliationError(f"ledger row hash mismatch at row {index}")
        entry = _entry_from_ledger_row(row, index)
        entries.append(entry)
        previous_hash = observed_hash

    manifest_path = root_path / ADMISSION_MANIFEST
    if manifest_path.exists():
        manifest_entries = _load_manifest_entries(root_path)
        if _sorted_entry_payloads(tuple(entries)) != _sorted_entry_payloads(manifest_entries):
            raise AdmissionReconciliationError("ledger entries do not match admission manifest")
    return tuple(rows)


def _resolve_artifact_path(root: Path, artifact: Path) -> Path:
    resolved = artifact if artifact.is_absolute() else root / artifact
    resolved = resolved.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise AdmissionReconciliationError(f"artifact path escapes root: {artifact}") from exc
    if not resolved.exists() or not resolved.is_file():
        raise AdmissionReconciliationError(f"artifact path does not exist: {artifact}")
    return resolved


def _load_artifact_payload(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    try:
        payload = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise AdmissionReconciliationError(f"malformed admission artifact: {path}") from exc
    if not isinstance(payload, dict):
        raise AdmissionReconciliationError("admission artifact root must be an object")
    return payload, raw


def _entry_from_artifact(root: Path, path: Path, payload: Mapping[str, Any], raw: bytes) -> AdmissionEntry:
    artifact_id = _required_text(payload, "artifact_id")
    artifact_path = _required_text(payload, "artifact_path")
    admission_status = _normalize_status(_required_text(payload, "admission_status"))
    declared_path = _safe_relative_path(artifact_path, field="artifact_path")
    observed_path = path.relative_to(root).as_posix()
    if declared_path != observed_path:
        raise AdmissionReconciliationError(
            f"artifact_path does not match artifact location: {artifact_path} != {observed_path}"
        )
    return AdmissionEntry(
        artifact_id=artifact_id,
        artifact_path=declared_path,
        artifact_sha256=hashlib.sha256(raw).hexdigest(),
        admission_status=admission_status,
    )


def _required_text(payload: Mapping[str, Any], key: str) -> str:
    value = payload.get(key)
    if not isinstance(value, str) or not value:
        raise AdmissionReconciliationError(f"admission artifact missing {key}")
    return value


def _normalize_status(value: str) -> str:
    if value not in ALLOWED_ADMISSION_STATUSES:
        raise AdmissionReconciliationError(f"unsupported admission_status: {value}")
    return "bounded_negative" if value == "bounded-negative" else value


def _safe_relative_path(value: str, *, field: str) -> str:
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not value:
        raise AdmissionReconciliationError(f"{field} must be a repo-relative path")
    return path.as_posix()


def _load_manifest_entries(root: Path) -> tuple[AdmissionEntry, ...]:
    path = root / ADMISSION_MANIFEST
    if not path.exists():
        return ()
    payload = _load_json_object(path, "admission manifest")
    if payload.get("schema_id") != MANIFEST_SCHEMA_ID:
        raise AdmissionReconciliationError("admission manifest schema_id mismatch")
    entries = payload.get("entries")
    if not isinstance(entries, list):
        raise AdmissionReconciliationError("admission manifest entries must be a list")
    result = tuple(_entry_from_manifest_row(row, index + 1) for index, row in enumerate(entries))
    if tuple(sorted(result, key=lambda item: (item.artifact_id, item.artifact_path))) != result:
        raise AdmissionReconciliationError("admission manifest entries are not sorted")
    return result


def _entry_from_manifest_row(row: Any, row_number: int) -> AdmissionEntry:
    if not isinstance(row, Mapping):
        raise AdmissionReconciliationError(f"admission manifest row {row_number} must be an object")
    artifact_id = _required_text(row, "artifact_id")
    artifact_path = _safe_relative_path(_required_text(row, "artifact_path"), field="artifact_path")
    artifact_sha256 = _sha256_text(row.get("artifact_sha256"), f"admission manifest row {row_number}")
    admission_status = _normalize_status(_required_text(row, "admission_status"))
    return AdmissionEntry(
        artifact_id=artifact_id,
        artifact_path=artifact_path,
        artifact_sha256=artifact_sha256,
        admission_status=admission_status,
    )


def _entry_from_ledger_row(row: Mapping[str, Any], row_number: int) -> AdmissionEntry:
    artifact_id = _required_text(row, "artifact_id")
    artifact_path = _safe_relative_path(_required_text(row, "artifact_path"), field="artifact_path")
    artifact_sha256 = _sha256_text(row.get("artifact_sha256"), f"admission ledger row {row_number}")
    admission_status = _normalize_status(_required_text(row, "admission_status"))
    return AdmissionEntry(
        artifact_id=artifact_id,
        artifact_path=artifact_path,
        artifact_sha256=artifact_sha256,
        admission_status=admission_status,
    )


def _sha256_text(value: Any, context: str) -> str:
    if not isinstance(value, str) or len(value) != 64:
        raise AdmissionReconciliationError(f"{context} has invalid sha256")
    try:
        int(value, 16)
    except ValueError as exc:
        raise AdmissionReconciliationError(f"{context} has invalid sha256") from exc
    return value


def _load_json_object(path: Path, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise AdmissionReconciliationError(f"malformed {label}: {path}") from exc
    if not isinstance(payload, dict):
        raise AdmissionReconciliationError(f"{label} root must be an object")
    return payload


def _assert_hash_sidecar_matches(root: Path, entries: tuple[AdmissionEntry, ...]) -> None:
    path = root / ADMISSION_ARTIFACT_HASHES
    if not path.exists():
        if entries:
            raise AdmissionReconciliationError("admission hash sidecar missing for non-empty manifest")
        return
    payload = _load_json_object(path, "admission artifact hash sidecar")
    if payload.get("schema_id") != HASHES_SCHEMA_ID:
        raise AdmissionReconciliationError("admission artifact hash sidecar schema_id mismatch")
    expected = _hashes_payload(entries)
    if payload != expected:
        raise AdmissionReconciliationError("admission artifact hash sidecar does not match manifest")


def _conflicts_for_entry(entry: AdmissionEntry, entries: tuple[AdmissionEntry, ...]) -> list[dict[str, Any]]:
    by_id = {item.artifact_id: item for item in entries}
    by_path = {item.artifact_path: item for item in entries}
    conflicts: list[dict[str, Any]] = []
    same_id = by_id.get(entry.artifact_id)
    if same_id is not None:
        if same_id.artifact_sha256 != entry.artifact_sha256:
            conflicts.append(
                {
                    "kind": "artifact_id_hash_mismatch",
                    "artifact_id": entry.artifact_id,
                    "artifact_path": entry.artifact_path,
                    "existing_artifact_path": same_id.artifact_path,
                    "existing_sha256": same_id.artifact_sha256,
                    "observed_sha256": entry.artifact_sha256,
                }
            )
        elif same_id.artifact_path != entry.artifact_path:
            conflicts.append(
                {
                    "kind": "artifact_id_path_mismatch",
                    "artifact_id": entry.artifact_id,
                    "artifact_path": entry.artifact_path,
                    "existing_artifact_path": same_id.artifact_path,
                    "artifact_sha256": entry.artifact_sha256,
                }
            )
    same_path = by_path.get(entry.artifact_path)
    if same_path is not None and same_path.artifact_id != entry.artifact_id:
        conflicts.append(
            {
                "kind": "artifact_path_reuse",
                "artifact_path": entry.artifact_path,
                "existing_artifact_id": same_path.artifact_id,
                "observed_artifact_id": entry.artifact_id,
                "existing_sha256": same_path.artifact_sha256,
                "observed_sha256": entry.artifact_sha256,
            }
        )
    return conflicts


def _manifest_payload(entries: tuple[AdmissionEntry, ...]) -> dict[str, Any]:
    return {
        "artifact_id": "bedc-quality-lab:admission-manifest",
        "canonical_role": "admission_sidecar_not_in_CANONICAL_REPORTS",
        "entry_count": len(entries),
        "entries": [entry.to_payload() for entry in entries],
        "schema_id": MANIFEST_SCHEMA_ID,
    }


def _sorted_entry_payloads(entries: tuple[AdmissionEntry, ...]) -> list[dict[str, Any]]:
    return [
        entry.to_payload()
        for entry in sorted(entries, key=lambda item: (item.artifact_id, item.artifact_path))
    ]


def _hashes_payload(entries: tuple[AdmissionEntry, ...]) -> dict[str, Any]:
    return {
        "artifact_hashes": {entry.artifact_id: entry.artifact_sha256 for entry in entries},
        "path_hashes": {entry.artifact_path: entry.artifact_sha256 for entry in entries},
        "schema_id": HASHES_SCHEMA_ID,
    }


def _conflicts_payload(conflicts: Any) -> dict[str, Any]:
    conflict_rows = [dict(conflict) for conflict in conflicts]
    return {
        "conflict_count": len(conflict_rows),
        "conflicts": conflict_rows,
        "schema_id": CONFLICTS_SCHEMA_ID,
        "status": "conflict" if conflict_rows else "clean",
    }


def _append_ledger_row(root: Path, entry: AdmissionEntry) -> None:
    rows = _read_ledger_rows(root)
    previous_hash = rows[-1]["row_sha256"] if rows else None
    row: dict[str, Any] = {
        "admission_status": entry.admission_status,
        "artifact_id": entry.artifact_id,
        "artifact_path": entry.artifact_path,
        "artifact_sha256": entry.artifact_sha256,
        "previous_row_sha256": previous_hash,
        "schema_id": LEDGER_ROW_SCHEMA_ID,
        "sequence": len(rows) + 1,
    }
    row["row_sha256"] = _row_hash(row)
    path = root / ADMISSION_LEDGER
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n")


def _read_ledger_rows(root: Path) -> tuple[dict[str, Any], ...]:
    path = root / ADMISSION_LEDGER
    if not path.exists():
        return ()
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                row = json.loads(stripped)
            except json.JSONDecodeError as exc:
                raise AdmissionReconciliationError(f"malformed admission ledger row {line_number}") from exc
            if not isinstance(row, dict):
                raise AdmissionReconciliationError(f"admission ledger row {line_number} must be an object")
            if row.get("schema_id") != LEDGER_ROW_SCHEMA_ID:
                raise AdmissionReconciliationError(f"admission ledger row {line_number} schema_id mismatch")
            rows.append(row)
    return tuple(rows)


def _row_hash(row: Mapping[str, Any]) -> str:
    payload = {key: value for key, value in row.items() if key != "row_sha256"}
    return hashlib.sha256(_canonical_json_bytes(payload)).hexdigest()


def _canonical_json_bytes(payload: Mapping[str, Any]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


__all__ = [
    "AdmissionReconciliationError",
    "AdmissionReconciliationResult",
    "audit_admission_ledger",
    "reconcile_admission_artifact",
]

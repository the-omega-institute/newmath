"""Content-addressed cache for canonical training cell blobs."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field, is_dataclass
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
from typing import Any, Literal, Mapping


CELL_CACHE_INPUT_SCHEMA_ID = "bedc-quality-lab:canonical-cell-cache-input"
CELL_CACHE_MANIFEST_SCHEMA_ID = "bedc-quality-lab:canonical-cell-cache-manifest"
CELL_CACHE_KEY_ALGORITHM_ID = "sha256:canonical-json:v1"


@dataclass
class CellInputRecord:
    producer_id: str
    producer_command: tuple[str, ...]
    report_artifacts: Mapping[str, str]
    producer_source_closure: tuple[Mapping[str, str], ...] = ()
    extra_input_paths: tuple[str, ...] = ()
    config_payload: Mapping[str, Any] = field(default_factory=dict)
    seed_protocol: Mapping[str, Any] = field(default_factory=dict)
    source_artifact_digests: Mapping[str, str] = field(default_factory=dict)
    requested_device: str = "unspecified"
    resolved_device: str = "unspecified"
    runtime_abi: Mapping[str, str] = field(default_factory=dict)
    schema_id: str = CELL_CACHE_INPUT_SCHEMA_ID
    key_algorithm_id: str = CELL_CACHE_KEY_ALGORITHM_ID


@dataclass
class CachedBlob:
    logical_path: str
    blob_sha256: str
    byte_size: int
    media_role: str


@dataclass
class CellCacheManifest:
    schema_id: str
    producer_id: str
    cell_input_digest: str
    cell_output_digest: str
    blobs: tuple[CachedBlob, ...]
    created_metadata: Mapping[str, Any]
    manifest_digest_inputs: Mapping[str, Any]
    key_algorithm_id: str = CELL_CACHE_KEY_ALGORITHM_ID


@dataclass
class CellCacheLookup:
    status: Literal["hit", "miss", "corrupt"]
    reason: str
    manifest_path: Path
    verified_blob_paths: Mapping[str, Path] = field(default_factory=dict)


def _canonical_payload(payload: Any) -> Any:
    if is_dataclass(payload):
        return _canonical_payload(asdict(payload))
    if isinstance(payload, Path):
        return payload.as_posix()
    if isinstance(payload, Mapping):
        return {str(key): _canonical_payload(value) for key, value in sorted(payload.items(), key=lambda item: str(item[0]))}
    if isinstance(payload, (list, tuple)):
        return [_canonical_payload(value) for value in payload]
    return payload


def canonical_digest(payload: Any) -> str:
    canonical = json.dumps(
        _canonical_payload(payload),
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _checked_cache_root(path: Path) -> Path:
    root = path.expanduser()
    if ".refactor-loop" in root.parts:
        raise ValueError("canonical cell cache root must not live under .refactor-loop")
    return root


def default_cache_root() -> Path:
    override = os.environ.get("BEDC_QUALITY_LAB_CACHE_DIR")
    if override:
        return _checked_cache_root(Path(override))
    xdg = os.environ.get("XDG_CACHE_HOME")
    base = Path(xdg).expanduser() if xdg else Path.home() / ".cache"
    return _checked_cache_root(base / "bedc-quality-lab" / "canonical-cells")


def _root(cache_root: Path | str | None) -> Path:
    return _checked_cache_root(Path(cache_root)) if cache_root is not None else default_cache_root()


def _safe_component(value: str) -> str:
    if not value or "/" in value or "\\" in value or value in {".", ".."}:
        raise ValueError(f"unsafe cache path component: {value!r}")
    return value


def _safe_logical_path(value: str) -> Path:
    path = Path(value)
    if path.is_absolute() or ".." in path.parts or not path.parts:
        raise ValueError(f"unsafe logical blob path: {value!r}")
    return path


def _is_sha256(value: str) -> bool:
    return len(value) == 64 and all(char in "0123456789abcdef" for char in value)


def _record_payload(record: CellInputRecord) -> dict[str, Any]:
    payload = _canonical_payload(record)
    if not isinstance(payload, dict):
        raise TypeError("cell input record did not serialize to an object")
    if payload.get("schema_id") != CELL_CACHE_INPUT_SCHEMA_ID:
        raise ValueError("cell input record schema id mismatch")
    if payload.get("key_algorithm_id") != CELL_CACHE_KEY_ALGORITHM_ID:
        raise ValueError("cell input record key algorithm mismatch")
    return payload


def cell_input_digest(record: CellInputRecord) -> str:
    return canonical_digest(_record_payload(record))


def _entry_manifest_path(record: CellInputRecord, cache_root: Path | str | None) -> Path:
    return _root(cache_root) / _safe_component(record.producer_id) / cell_input_digest(record) / "manifest.json"


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _blob_from_payload(row: Mapping[str, Any]) -> CachedBlob:
    logical_path = str(row.get("logical_path", ""))
    blob_sha256 = str(row.get("blob_sha256", ""))
    byte_size = int(row.get("byte_size", -1))
    media_role = str(row.get("media_role", ""))
    _safe_logical_path(logical_path)
    if not _is_sha256(blob_sha256):
        raise ValueError("cached blob sha256 is invalid")
    if byte_size < 0:
        raise ValueError("cached blob byte size is invalid")
    if not media_role:
        raise ValueError("cached blob media role is missing")
    return CachedBlob(
        logical_path=logical_path,
        blob_sha256=blob_sha256,
        byte_size=byte_size,
        media_role=media_role,
    )


def _manifest_payload(manifest: CellCacheManifest) -> dict[str, Any]:
    payload = _canonical_payload(manifest)
    if not isinstance(payload, dict):
        raise TypeError("cell cache manifest did not serialize to an object")
    payload["blobs"] = sorted(payload["blobs"], key=lambda row: row["logical_path"])
    return payload


def _manifest_digest_inputs(
    *,
    producer_id: str,
    cell_input: str,
    cell_output: str,
    blobs: tuple[CachedBlob, ...],
) -> dict[str, Any]:
    blob_payload = sorted((asdict(blob) for blob in blobs), key=lambda row: row["logical_path"])
    return {
        "schema_id": CELL_CACHE_MANIFEST_SCHEMA_ID,
        "key_algorithm_id": CELL_CACHE_KEY_ALGORITHM_ID,
        "producer_id": producer_id,
        "cell_input_digest": cell_input,
        "cell_output_digest": cell_output,
        "blobs": blob_payload,
    }


def _manifest_from_payload(payload: Mapping[str, Any]) -> CellCacheManifest:
    if payload.get("schema_id") != CELL_CACHE_MANIFEST_SCHEMA_ID:
        raise ValueError("cell cache manifest schema id mismatch")
    if payload.get("key_algorithm_id") != CELL_CACHE_KEY_ALGORITHM_ID:
        raise ValueError("cell cache manifest key algorithm mismatch")
    blobs_payload = payload.get("blobs")
    if not isinstance(blobs_payload, list) or not blobs_payload:
        raise ValueError("cell cache manifest has no blobs")
    blobs = tuple(_blob_from_payload(row) for row in blobs_payload if isinstance(row, Mapping))
    if len(blobs) != len(blobs_payload):
        raise ValueError("cell cache manifest blob row is not an object")
    logical_paths = [blob.logical_path for blob in blobs]
    if len(set(logical_paths)) != len(logical_paths):
        raise ValueError("cell cache manifest has duplicate logical paths")
    cell_input = str(payload.get("cell_input_digest", ""))
    cell_output = str(payload.get("cell_output_digest", ""))
    if not _is_sha256(cell_input) or not _is_sha256(cell_output):
        raise ValueError("cell cache manifest digest is invalid")
    created_metadata = payload.get("created_metadata")
    manifest_digest_inputs = payload.get("manifest_digest_inputs")
    if not isinstance(created_metadata, Mapping) or not isinstance(manifest_digest_inputs, Mapping):
        raise ValueError("cell cache manifest metadata is invalid")
    return CellCacheManifest(
        schema_id=str(payload["schema_id"]),
        producer_id=str(payload.get("producer_id", "")),
        cell_input_digest=cell_input,
        cell_output_digest=cell_output,
        blobs=blobs,
        created_metadata=dict(created_metadata),
        manifest_digest_inputs=dict(manifest_digest_inputs),
        key_algorithm_id=str(payload["key_algorithm_id"]),
    )


def verify_cell_manifest(record: CellInputRecord, manifest_path: Path | str) -> CellCacheLookup:
    path = Path(manifest_path)
    expected_digest = cell_input_digest(record)
    if not path.exists():
        return CellCacheLookup("miss", "manifest-missing", path)
    try:
        if path.name != "manifest.json":
            raise ValueError("cell cache manifest filename mismatch")
        if path.parent.name != expected_digest or path.parent.parent.name != _safe_component(record.producer_id):
            raise ValueError("cell cache manifest path does not match input digest")
        manifest = _manifest_from_payload(_read_json(path))
        if manifest.producer_id != record.producer_id:
            raise ValueError("cell cache manifest producer id mismatch")
        if manifest.cell_input_digest != expected_digest:
            raise ValueError("cell cache manifest input digest mismatch")
        expected_output = canonical_digest({"blobs": sorted((asdict(blob) for blob in manifest.blobs), key=lambda row: row["logical_path"])})
        if manifest.cell_output_digest != expected_output:
            raise ValueError("cell cache manifest output digest mismatch")
        expected_manifest_inputs = _manifest_digest_inputs(
            producer_id=manifest.producer_id,
            cell_input=manifest.cell_input_digest,
            cell_output=manifest.cell_output_digest,
            blobs=manifest.blobs,
        )
        if _canonical_payload(manifest.manifest_digest_inputs) != _canonical_payload(expected_manifest_inputs):
            raise ValueError("cell cache manifest digest inputs mismatch")
        verified: dict[str, Path] = {}
        blob_root = path.parent / "blobs"
        for blob in manifest.blobs:
            blob_path = blob_root / blob.blob_sha256
            if not blob_path.exists() or not blob_path.is_file():
                raise ValueError(f"cached blob missing: {blob.logical_path}")
            data = blob_path.read_bytes()
            if hashlib.sha256(data).hexdigest() != blob.blob_sha256:
                raise ValueError(f"cached blob digest mismatch: {blob.logical_path}")
            if len(data) != blob.byte_size:
                raise ValueError(f"cached blob byte size mismatch: {blob.logical_path}")
            verified[blob.logical_path] = blob_path
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
        return CellCacheLookup("corrupt", str(exc), path)
    return CellCacheLookup("hit", "manifest-and-blobs-verified", path, verified)


def load_cell_entry(record: CellInputRecord, *, cache_root: Path | str | None = None) -> CellCacheLookup:
    manifest_path = _entry_manifest_path(record, cache_root)
    if not manifest_path.exists():
        return CellCacheLookup("miss", "manifest-missing", manifest_path)
    return verify_cell_manifest(record, manifest_path)


def _coerce_blob_source(logical_path: str, value: Any) -> tuple[Path, str]:
    if isinstance(value, (str, Path)):
        return Path(value), Path(logical_path).suffix.lstrip(".") or "bytes"
    if isinstance(value, tuple) and len(value) == 2:
        return Path(value[0]), str(value[1])
    if isinstance(value, Mapping):
        if "path" not in value:
            raise ValueError(f"cached blob source missing path: {logical_path}")
        return Path(str(value["path"])), str(value.get("media_role") or Path(logical_path).suffix.lstrip(".") or "bytes")
    raise TypeError(f"unsupported cached blob source: {logical_path}")


def store_cell_entry(
    record: CellInputRecord,
    blobs: Mapping[str, Any],
    *,
    cache_root: Path | str | None = None,
) -> CellCacheManifest:
    if not blobs:
        raise ValueError("cannot store a cell cache entry without blobs")
    manifest_path = _entry_manifest_path(record, cache_root)
    entry_root = manifest_path.parent
    blob_root = entry_root / "blobs"
    blob_root.mkdir(parents=True, exist_ok=True)
    rows: list[CachedBlob] = []
    for logical_path, source_value in sorted(blobs.items()):
        logical = str(logical_path)
        _safe_logical_path(logical)
        source_path, media_role = _coerce_blob_source(logical, source_value)
        data = source_path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        target = blob_root / digest
        if not target.exists() or hashlib.sha256(target.read_bytes()).hexdigest() != digest:
            target.write_bytes(data)
        rows.append(
            CachedBlob(
                logical_path=logical,
                blob_sha256=digest,
                byte_size=len(data),
                media_role=media_role,
            )
        )
    blob_payload = sorted((asdict(row) for row in rows), key=lambda row: row["logical_path"])
    cell_output_digest = canonical_digest({"blobs": blob_payload})
    input_digest = cell_input_digest(record)
    manifest_digest_inputs = _manifest_digest_inputs(
        producer_id=record.producer_id,
        cell_input=input_digest,
        cell_output=cell_output_digest,
        blobs=tuple(rows),
    )
    manifest = CellCacheManifest(
        schema_id=CELL_CACHE_MANIFEST_SCHEMA_ID,
        producer_id=record.producer_id,
        cell_input_digest=input_digest,
        cell_output_digest=cell_output_digest,
        blobs=tuple(rows),
        created_metadata={
            "created_at": datetime.now(timezone.utc).isoformat(),
            "writer": "bedc_quality_lab.canonical_cell_cache",
        },
        manifest_digest_inputs=manifest_digest_inputs,
    )
    entry_root.mkdir(parents=True, exist_ok=True)
    payload = _manifest_payload(manifest)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=entry_root, delete=False) as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
        temp_name = handle.name
    Path(temp_name).replace(manifest_path)
    lookup = verify_cell_manifest(record, manifest_path)
    if lookup.status != "hit":
        raise RuntimeError(f"stored cell cache entry did not verify: {lookup.reason}")
    return manifest


def materialize_cell_entry(lookup: CellCacheLookup, destination_root: Path | str) -> dict[str, Path]:
    if lookup.status != "hit":
        raise ValueError(f"cannot materialize non-hit cell cache entry: {lookup.status}")
    destination = Path(destination_root)
    materialized: dict[str, Path] = {}
    for logical_path, source_path in sorted(lookup.verified_blob_paths.items()):
        relative = _safe_logical_path(logical_path)
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, target)
        materialized[logical_path] = target
    return materialized


__all__ = [
    "CELL_CACHE_INPUT_SCHEMA_ID",
    "CELL_CACHE_KEY_ALGORITHM_ID",
    "CELL_CACHE_MANIFEST_SCHEMA_ID",
    "CachedBlob",
    "CellCacheLookup",
    "CellCacheManifest",
    "CellInputRecord",
    "canonical_digest",
    "cell_input_digest",
    "default_cache_root",
    "load_cell_entry",
    "materialize_cell_entry",
    "store_cell_entry",
    "verify_cell_manifest",
]

"""JSON pointer helpers for canonical artifact cells."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


def pointer_value(payload: Mapping[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(cursor, Mapping) or key not in cursor:
                    return None
                cursor = cursor[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(cursor, list):
                return None
            index = int(index_text)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            part = ""
        if not part:
            continue
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        elif isinstance(cursor, list) and part.isdigit() and int(part) < len(cursor):
            cursor = cursor[int(part)]
        else:
            return None
    return cursor


def normalize_artifact_pointer(cell: str) -> str | None:
    if ":" not in cell:
        return None
    artifact, pointer = cell.split(":", 1)
    if not artifact:
        return None
    if artifact.endswith(".jsonl") and pointer.isdigit():
        return f"{artifact}:$.lines[{pointer}]"
    if pointer.startswith("$"):
        return f"{artifact}:{pointer}"
    return None


def split_artifact_pointer(cell: str) -> tuple[str, str] | None:
    normalized = normalize_artifact_pointer(cell)
    if normalized is None:
        return None
    artifact, pointer = normalized.split(":", 1)
    return artifact, pointer


def _jsonl_pointer_value(path: Path, pointer: str) -> Any:
    if not pointer.startswith("$.lines[") or not pointer.endswith("]"):
        return None
    index_text = pointer.removeprefix("$.lines[").removesuffix("]")
    if not index_text.isdigit():
        return None
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]
    index = int(index_text)
    return rows[index] if index < len(rows) else None


def resolve_artifact_pointer(root: Path, cell: str) -> Any:
    split = split_artifact_pointer(cell)
    if split is None:
        return None
    artifact, pointer = split
    path = root / artifact
    if not path.exists():
        return None
    if artifact.endswith(".jsonl"):
        try:
            return _jsonl_pointer_value(path, pointer)
        except json.JSONDecodeError:
            return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer) if isinstance(payload, Mapping) else None


def is_resolvable_artifact_pointer(root: Path, cell: str) -> bool:
    return resolve_artifact_pointer(root, cell) is not None

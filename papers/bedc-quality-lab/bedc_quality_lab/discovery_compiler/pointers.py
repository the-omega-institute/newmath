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


def split_artifact_pointer(cell: str) -> tuple[str, str] | None:
    if ":$" not in cell:
        return None
    artifact, pointer = cell.split(":", 1)
    if not artifact or not pointer.startswith("$"):
        return None
    return artifact, pointer


def resolve_artifact_pointer(root: Path, cell: str) -> Any:
    split = split_artifact_pointer(cell)
    if split is None:
        return None
    artifact, pointer = split
    path = root / artifact
    if not path.exists():
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

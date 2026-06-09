"""Shared canonical JSON digest helpers."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping


def canonical_json_digest(payload: Mapping[str, Any]) -> str:
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()

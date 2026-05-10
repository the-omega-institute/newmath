#!/usr/bin/env python3
"""Glossary loader + writer for the per-term TOML layout.

The dossier glossary is split into one TOML file per term plus a single
`_meta.toml` for cross-cutting metadata (categories, exempt_macros,
label_identical_ok). This module exposes a single ``load_glossary``
that reassembles the same dict shape the legacy monolithic JSON used,
so consumers (`check_glossary.py`, `build_dossier_status.py`) can stay
mostly unchanged.

Layout::

    docs/dossier/data_source/glossary/
        _meta.toml             # description, categories, exempt_macros, label_identical_ok
        Ask.toml               # per-term: [en]/[zh] tables + optional aliases
        AbelianCat.toml
        ...

Returned shape (matches the old monolithic JSON one-for-one)::

    {
        "_meta": {...},
        "Ask": {"en": {"label": ..., "desc": ...}, "zh": {...}},
        ...
    }

stdlib only (project rule).
"""

from __future__ import annotations

import tomllib
from pathlib import Path

GLOSSARY_DIR = Path(__file__).resolve().parents[1] / "docs" / "dossier" / "data_source" / "glossary"
META_FILE = GLOSSARY_DIR / "_meta.toml"


def load_glossary() -> dict:
    """Read every per-term TOML plus _meta.toml and return the merged
    dict in the legacy shape.

    The canonical key for each entry is the ``key`` field inside the
    TOML body, which lets us coexist with a case-insensitive
    filesystem (Bundle vs bundle): we suffix the filename with
    ``_region``/``_macro`` only as a disk-level disambiguator and
    still surface the original key to consumers."""
    if not GLOSSARY_DIR.is_dir():
        raise FileNotFoundError(f"glossary dir missing: {GLOSSARY_DIR}")
    out: dict = {}
    if META_FILE.exists():
        with META_FILE.open("rb") as fh:
            out["_meta"] = tomllib.load(fh)
    for path in sorted(GLOSSARY_DIR.glob("*.toml")):
        if path.name == "_meta.toml":
            continue
        with path.open("rb") as fh:
            data = tomllib.load(fh)
        key = data.pop("key", None) or path.stem
        if key in out:
            raise ValueError(
                f"duplicate glossary key '{key}' from {path.name}"
            )
        out[key] = data
    return out


# Filename slug rule: by default use the literal key. When the key
# differs only in case from another key (the Bundle/bundle pair), the
# lowercase one gets a `_region` suffix and the uppercase one stays
# plain — purely to keep the on-disk filenames distinct on
# case-insensitive filesystems.
def filename_for_key(key: str, all_keys: list[str]) -> str:
    lc = key.lower()
    siblings = [k for k in all_keys if k.lower() == lc]
    if len(siblings) > 1 and key == lc:
        return f"{key}_region.toml"
    return f"{key}.toml"


# ---------- TOML emitter (write side; needed for migration + future tools) ----------

def _is_safe_literal(s: str) -> bool:
    return "'" not in s and "\n" not in s and "\r" not in s


def _is_safe_multiline_literal(s: str) -> bool:
    return "'''" not in s


def _emit_string(s: str) -> str:
    """Emit a TOML string literal that round-trips ``s``. Prefers
    literal forms (no escaping) so authored macros / dollars stay
    legible; falls back to basic strings only when the content
    contains forbidden quote patterns."""
    if "\n" in s or "\r" in s:
        if _is_safe_multiline_literal(s):
            return "'''\n" + s + "'''"
        # Multi-line basic string: escape \ and " (newlines preserved literally).
        escaped = s.replace("\\", "\\\\").replace('"""', '\\"""').replace('"', '\\"')
        return '"""\n' + escaped + '"""'
    if _is_safe_literal(s):
        return "'" + s + "'"
    # Single-line basic string: must escape \ and ".
    escaped = s.replace("\\", "\\\\").replace('"', '\\"')
    return '"' + escaped + '"'


def _emit_array_of_strings(items: list[str]) -> str:
    return "[" + ", ".join(_emit_string(x) for x in items) + "]"


def emit_entry(key: str, entry: dict) -> str:
    """Render a single per-term TOML file body. Always writes a
    ``key = "..."`` field so the canonical key stays in the file
    independent of disk casing."""
    lines: list[str] = ["key = " + _emit_string(key), ""]
    if "aliases" in entry and entry["aliases"]:
        lines.append("aliases = " + _emit_array_of_strings(list(entry["aliases"])))
        lines.append("")
    if "constructive_story_zh" in entry and entry["constructive_story_zh"]:
        lines.append("constructive_story_zh = " + _emit_string(entry["constructive_story_zh"]))
        lines.append("")
    for lang in ("en", "zh"):
        if lang not in entry:
            continue
        sub = entry[lang] or {}
        lines.append(f"[{lang}]")
        for fld in ("label", "desc"):
            if fld in sub:
                lines.append(f"{fld} = " + _emit_string(sub[fld] or ""))
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def emit_meta(meta: dict) -> str:
    """Render `_meta.toml`. Recognised fields: ``description`` (str),
    ``categories`` (list[str]), ``exempt_macros`` (list[str]),
    ``label_identical_ok`` (list[str])."""
    lines: list[str] = ["# Cross-cutting metadata for the per-term glossary.", ""]
    if "description" in meta:
        lines.append("description = " + _emit_string(meta["description"]))
        lines.append("")
    for fld in ("categories", "exempt_macros", "label_identical_ok"):
        if fld in meta and meta[fld]:
            arr = list(meta[fld])
            if len(arr) <= 6 and all(len(x) < 20 for x in arr):
                lines.append(f"{fld} = " + _emit_array_of_strings(arr))
            else:
                # Multi-line array for readability.
                lines.append(f"{fld} = [")
                for x in arr:
                    lines.append(f"    {_emit_string(x)},")
                lines.append("]")
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"

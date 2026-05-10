#!/usr/bin/env python3
"""One-shot migration: split docs/dossier/data_source/glossary.json
into one TOML file per term plus _meta.toml.

After this script runs successfully, the legacy JSON file is removed
(via git rm in the migration commit). Re-running is safe: it
overwrites whatever is in data_source/glossary/.

stdlib only. Reads the legacy JSON; writes TOML using the emitter in
``_glossary_loader``.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from _glossary_loader import GLOSSARY_DIR, emit_entry, emit_meta, filename_for_key

ROOT = Path(__file__).resolve().parents[1]
LEGACY_JSON = ROOT / "docs" / "dossier" / "data_source" / "glossary.json"


def main() -> int:
    if not LEGACY_JSON.exists():
        print(f"[migrate] legacy file already removed: {LEGACY_JSON}", file=sys.stderr)
        return 1
    with LEGACY_JSON.open(encoding="utf-8") as fh:
        legacy = json.load(fh)

    GLOSSARY_DIR.mkdir(parents=True, exist_ok=True)

    n_meta = 0
    n_entries = 0
    if "_meta" in legacy:
        meta_path = GLOSSARY_DIR / "_meta.toml"
        meta_path.write_text(emit_meta(legacy["_meta"]), encoding="utf-8")
        n_meta = 1

    all_keys = [k for k in legacy if not k.startswith("_")]
    for key, entry in legacy.items():
        if key.startswith("_"):
            continue
        out_path = GLOSSARY_DIR / filename_for_key(key, all_keys)
        out_path.write_text(emit_entry(key, entry), encoding="utf-8")
        n_entries += 1

    print(
        f"[migrate] wrote {GLOSSARY_DIR.relative_to(ROOT)}/ "
        f"-- {n_meta} meta + {n_entries} entries",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

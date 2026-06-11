#!/usr/bin/env python3
"""Produce the DGT model card canonical projection."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.dgt_model_card import DEFAULT_GENERATED_AT, write_dgt_model_card


def _default_generated_at(root: Path) -> str:
    index_path = root / "reports" / "canonical" / "index.json"
    if index_path.exists():
        try:
            payload = json.loads(index_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            payload = {}
        generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
        if isinstance(generated_at, str) and generated_at:
            return generated_at
    return DEFAULT_GENERATED_AT


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=None)
    args = parser.parse_args(argv)
    card = write_dgt_model_card(root=args.root, generated_at=args.generated_at or _default_generated_at(args.root))
    print(
        json.dumps(
            {
                "card_id": card["card_id"],
                "status": card["status"],
                "missing_source_refs": card["missing_source_refs"],
                "hardgate_status": card["card_hardgates"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

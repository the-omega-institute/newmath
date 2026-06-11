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


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    args = parser.parse_args(argv)
    card = write_dgt_model_card(root=args.root, generated_at=args.generated_at)
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

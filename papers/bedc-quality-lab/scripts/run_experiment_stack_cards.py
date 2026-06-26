#!/usr/bin/env python3
"""Write the finite experiment-stack card auxiliary report."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.experiment_stack import write_experiment_stack_cards


def _generated_at() -> str:
    return datetime.now(timezone.utc).isoformat()


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    parser.add_argument("--generated-at", default=None, help="Stable timestamp for reproducible regeneration.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = write_experiment_stack_cards(
        root=args.root,
        generated_at=args.generated_at or _generated_at(),
    )
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "status": payload["status"],
                "card_count": payload["card_count"],
                "blocked_card_count": len(payload["blocked_card_ids"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

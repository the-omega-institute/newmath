#!/usr/bin/env python3
"""Write the canonical pointer-only claim graph sidecar."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_graph import CLAIM_GRAPH_JSON_ARTIFACT, write_claim_graph


def _reusable_generated_at(root: Path) -> str | None:
    path = root / "reports/canonical/index.json"
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_claim_graph(root=args.root, generated_at=_reusable_generated_at(args.root))
    print(f"wrote {payload['node_count']} claim graph nodes to {CLAIM_GRAPH_JSON_ARTIFACT}")


if __name__ == "__main__":
    main()

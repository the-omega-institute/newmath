#!/usr/bin/env python3
"""Replay or refresh the discovery negative witness ledger."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.quality_discovery_adversarial_generator import (
    LEDGER_ARTIFACT,
    replay_checked_in_ledger,
    write_witness_ledger,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--refresh",
        action="store_true",
        help=f"Rewrite only {LEDGER_ARTIFACT}; default mode is replay/check-only.",
    )
    args = parser.parse_args(argv)
    if args.refresh:
        payload = write_witness_ledger(ROOT / LEDGER_ARTIFACT)
        mode = "refresh"
    else:
        payload = replay_checked_in_ledger(ROOT / LEDGER_ARTIFACT)
        mode = "replay"
    print(f"{mode} ok: {len(payload['witnesses'])} discovery negative witnesses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

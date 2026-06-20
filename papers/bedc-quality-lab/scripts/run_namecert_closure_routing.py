#!/usr/bin/env python3
"""Run the NameCert closure-routing profile."""

from __future__ import annotations

from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.namecert_closure_routing import run_and_write
from scripts.run_namecert_closure_verify import parse_common_args, print_summary


def main(argv: list[str] | None = None) -> int:
    args = parse_common_args(argv, description=__doc__)
    payload = run_and_write(
        "smoke_closure_routing",
        root=args.root,
        device=args.device,
        generated_at=args.generated_at,
        train_max_depth=args.train_max_depth,
        epochs=args.epochs,
        write_markdown=not args.no_markdown,
    )
    print_summary(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

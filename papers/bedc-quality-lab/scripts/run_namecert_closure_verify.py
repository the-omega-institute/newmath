#!/usr/bin/env python3
"""Run the NameCert closure-verify profile."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.namecert_closure_routing import run_and_write


def parse_common_args(argv: Sequence[str] | None = None, *, description: str | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--device", default="auto", choices=("auto", "cpu", "cuda"))
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--train-max-depth", type=int, default=None)
    parser.add_argument("--epochs", type=int, default=None)
    parser.add_argument("--no-markdown", action="store_true")
    return parser.parse_args(argv)


def print_summary(payload: Mapping[str, Any]) -> None:
    print(
        json.dumps(
            {
                "artifact_id": payload["artifact_id"],
                "profile_id": payload["profile"]["profile_id"],
                "json_artifact": payload["json_artifact"],
                "admission_gate": payload["admission"]["admission_gate"],
                "hardgate_status": {
                    key: row["status"]
                    for key, row in payload["hardgates"].items()
                },
            },
            sort_keys=True,
        )
    )


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_common_args(argv, description=__doc__)
    payload = run_and_write(
        "smoke_closure_verify",
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

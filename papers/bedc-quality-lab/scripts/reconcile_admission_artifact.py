#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.admission_reconciler import (  # noqa: E402
    AdmissionReconciliationError,
    reconcile_admission_artifact,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Reconcile one admission artifact into admission-only sidecars.")
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true", help="report whether sidecars would change without writing them")
    args = parser.parse_args(argv)

    try:
        result = reconcile_admission_artifact(args.artifact, root=args.root, dry_run=args.check)
    except AdmissionReconciliationError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    payload = result.to_payload()
    if args.check and result.status == "unchanged":
        payload["check_status"] = "clean"
    print(json.dumps(payload, sort_keys=True))
    if result.status == "conflict":
        return 2
    if args.check and result.status == "would-change":
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

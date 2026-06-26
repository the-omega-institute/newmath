#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.release_manifest_sidecar import write_release_manifest_sidecar


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--tag-ref", default=None)
    args = parser.parse_args()
    sidecar = write_release_manifest_sidecar(
        root=Path(args.root),
        generated_at=args.generated_at,
        tag_ref=args.tag_ref,
    )
    print(sidecar.to_payload()["release_bundle_status"])


if __name__ == "__main__":
    main()

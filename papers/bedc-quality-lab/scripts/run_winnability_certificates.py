#!/usr/bin/env python3
"""Produce canonical winnability certificate artifacts."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.winnability import GENERATED_AT, build_payload, write_artifacts


def write_winnability_certificates(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, object]:
    payload = build_payload(root=root, generated_at=generated_at or GENERATED_AT)
    write_artifacts(payload, root=root)
    return payload


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = write_winnability_certificates(root=args.root, generated_at=args.generated_at)
    audit = payload["audit"]
    hardgates = payload["hardgates"]
    summary = {
        "artifact_id": payload["artifact_id"],
        "audit_status": audit["status"],
        "certificate_count": audit["certificate_count"],
        "fail_closed_count": audit["fail_closed_count"],
        "ORACLE-HG1": hardgates["ORACLE-HG1"]["status"],
        "ORACLE-HG2": hardgates["ORACLE-HG2"]["status"],
    }
    print(json.dumps(summary, sort_keys=True))
    return 0 if hardgates["ORACLE-HG1"]["status"] == "pass" and hardgates["ORACLE-HG2"]["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())

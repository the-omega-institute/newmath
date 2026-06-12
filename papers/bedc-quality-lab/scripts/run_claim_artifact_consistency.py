#!/usr/bin/env python3
"""Write the canonical claim/artifact consistency audit."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_artifact_consistency import (
    DGT_CLAIM_ID,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    audit_claim_artifact_consistency,
    render_claim_artifact_consistency_markdown,
)


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


def write_claim_artifact_consistency(
    *,
    root: Path = ROOT,
    claim_id: str = DGT_CLAIM_ID,
    generated_at: str | None = None,
) -> dict[str, object]:
    report = audit_claim_artifact_consistency(
        root,
        claim_id=claim_id,
        generated_at=generated_at if generated_at is not None else _reusable_generated_at(root) or "reusable",
    )
    payload = report.to_json()
    json_path = root / JSON_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path = root / MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_claim_artifact_consistency_markdown(report), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    parser.add_argument("--claim-id", default=DGT_CLAIM_ID, help="Claim id to audit.")
    parser.add_argument("--check", action="store_true", help="Exit nonzero when any consistency hardgate fails.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = write_claim_artifact_consistency(root=args.root, claim_id=args.claim_id)
    print(json.dumps({"artifact": JSON_ARTIFACT, "status": payload["status"]}, sort_keys=True))
    return 1 if args.check and payload["status"] != "pass" else 0


if __name__ == "__main__":
    raise SystemExit(main())

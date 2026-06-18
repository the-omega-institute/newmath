#!/usr/bin/env python3
"""Run the JEPA-WM-L1 admission report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.tasks.jepa_wm_l1 import (  # noqa: E402
    ARTIFACT_ID,
    GENERATED_AT,
    build_payload,
    load_observation,
    write_artifacts,
)


def _relative(root: Path, path: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--input", type=Path, required=True, help="runtime observation JSON")
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--margin", type=float, default=0.0)
    args = parser.parse_args(argv)

    observation = load_observation(args.input, root=args.root)
    payload = build_payload(
        observation,
        generated_at=args.generated_at,
        margin=args.margin,
    )
    artifacts = write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "artifact_id": ARTIFACT_ID,
                "run_id": payload["run_id"],
                "status": payload["decision"]["status"],
                "failed_gates": payload["decision"]["failed_gates"],
                "admission_artifact": _relative(args.root, artifacts["admission"]),
                "source_observation": payload["source_observation"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

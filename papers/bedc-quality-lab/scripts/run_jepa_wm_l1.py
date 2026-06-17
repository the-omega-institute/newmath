#!/usr/bin/env python3
<<<<<<< HEAD
"""Run the JEPA-WM-L1 admission task."""
=======
"""Run the JEPA-WM-L1 admission report."""
>>>>>>> origin/paper-bedc-quality-lab

from __future__ import annotations

import argparse
<<<<<<< HEAD
import json
from pathlib import Path
import sys
from typing import Sequence
=======
from pathlib import Path
import sys
>>>>>>> origin/paper-bedc-quality-lab


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

<<<<<<< HEAD
from bedc_quality_lab.tasks.jepa_wm_l1 import GENERATED_AT, ARTIFACT_ID, build_payload, load_observation, write_artifacts


def _relative(root: Path, path: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--input", type=Path, required=True, help="runtime observation JSON")
    parser.add_argument("--generated-at", default=GENERATED_AT)
    parser.add_argument("--margin", type=float, default=0.0)
    args = parser.parse_args(argv)

    observation = load_observation(args.input)
    payload = build_payload(observation, generated_at=args.generated_at, margin=args.margin)
    artifacts = write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "artifact_id": ARTIFACT_ID,
                "run_id": payload["run_id"],
                "status": payload["decision"]["status"],
                "failed_gates": payload["decision"]["failed_gates"],
                "admission_artifact": _relative(args.root, artifacts["admission"]),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
=======
from bedc_quality_lab.tasks.jepa_wm_l1 import (  # noqa: E402
    DEFAULT_BOOTSTRAP_RESAMPLES,
    DEFAULT_CASE_COUNT,
    FINGERPRINT_ARTIFACT,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    write_artifacts,
)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--case-count", type=int, default=DEFAULT_CASE_COUNT)
    parser.add_argument("--bootstrap-resamples", type=int, default=DEFAULT_BOOTSTRAP_RESAMPLES)
    parser.add_argument("--device", default="cpu")
    args = parser.parse_args(argv)
    payload = write_artifacts(
        root=ROOT,
        json_path=ROOT / JSON_ARTIFACT,
        markdown_path=ROOT / MARKDOWN_ARTIFACT,
        fingerprint_path=ROOT / FINGERPRINT_ARTIFACT,
        generated_at=args.generated_at,
        case_count=args.case_count,
        bootstrap_resamples=args.bootstrap_resamples,
        device=args.device,
    )
    print(f"wrote {JSON_ARTIFACT} status={payload['execution_status']}")


if __name__ == "__main__":
    main()
>>>>>>> origin/paper-bedc-quality-lab

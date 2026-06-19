#!/usr/bin/env python3
"""Write, run, or validate the MiniGrid DoorKey OOD adjudication records."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.minigrid_doorkey_ood_adjudication import (  # noqa: E402
    DEFAULT_REPORT,
    DEFAULT_RUN_ID,
    JSON_ARTIFACT,
    build_payload,
    load_and_validate_report,
    write_artifacts,
    write_report,
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--execution-mode",
        choices=("fixture-smoke", "publication-bearing"),
        default="fixture-smoke",
        help="Evidence mode for the canonical emitted report.",
    )
    parser.add_argument("--output", type=Path, default=ROOT / JSON_ARTIFACT)
    parser.add_argument("--markdown-output", type=Path, default=None)
    parser.add_argument("--fingerprint-output", type=Path, default=None)
    parser.add_argument("--observations-json", type=Path, default=None)
    parser.add_argument("--report", default=None)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--seeds", default="101,102,103")
    parser.add_argument("--updates", type=int, default=80000)
    parser.add_argument("--eval-episodes", type=int, default=500)
    parser.add_argument("--batch-size", type=int, default=256)
    parser.add_argument("--device", default="cuda", choices=("cpu", "cuda", "mps", "auto"))
    parser.add_argument("--amp", action="store_true")
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--generated-at", default=None)
    return parser.parse_args(argv)


def _uses_bounded_report(args: argparse.Namespace) -> bool:
    return bool(
        args.report is not None
        or args.validate_only
        or args.smoke
        or args.run_id != DEFAULT_RUN_ID
        or args.seeds != "101,102,103"
        or args.updates != 80000
        or args.eval_episodes != 500
        or args.batch_size != 256
        or args.device != "cuda"
        or args.amp
    )


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if _uses_bounded_report(args):
        report_arg = args.report or DEFAULT_REPORT
        report_path = Path(report_arg)
        if args.validate_only:
            target = report_path if report_path.is_absolute() else ROOT / report_path
            payload = load_and_validate_report(target, root=ROOT)
            print(f"validated {report_arg} status={payload['verdict']['status']}")
            return 0
        payload = write_report(
            root=ROOT,
            report_path=report_path,
            run_id=args.run_id,
            seeds=args.seeds,
            updates=args.updates,
            eval_episodes=args.eval_episodes,
            batch_size=args.batch_size,
            device=args.device,
            amp=args.amp,
            smoke=args.smoke,
            generated_at=args.generated_at,
        )
        print(f"wrote {report_arg} status={payload['verdict']['status']}")
        return 0

    observations = None
    if args.observations_json is not None:
        observations = json.loads(args.observations_json.read_text(encoding="utf-8"))
    payload = build_payload(observations=observations, execution_mode=args.execution_mode)
    if args.execution_mode == "publication-bearing" and payload["claim_boundary"]["status"] != "publication-bearing":
        print(
            "publication-bearing mode requires 3 arms, 3 seeds per arm, and 500 fresh F3 episodes per arm",
            file=sys.stderr,
        )
        return 2
    write_artifacts(
        root=ROOT,
        json_path=args.output,
        markdown_path=args.markdown_output,
        fingerprint_path=args.fingerprint_output,
        execution_mode=args.execution_mode,
        observations=observations,
        generated_at=args.generated_at,
    )
    try:
        display_path = args.output.relative_to(ROOT)
    except ValueError:
        display_path = args.output
    print(f"wrote {display_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run or validate the bounded MiniGrid DoorKey OOD adjudication report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.minigrid_doorkey_ood_adjudication import (  # noqa: E402
    DEFAULT_REPORT,
    DEFAULT_RUN_ID,
    load_and_validate_report,
    write_report,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", default=DEFAULT_REPORT)
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
    return parser


def main(argv: list[str] | None = None) -> None:
    args = _parser().parse_args(argv)
    report_path = Path(args.report)
    if args.validate_only:
        target = report_path if report_path.is_absolute() else ROOT / report_path
        payload = load_and_validate_report(target, root=ROOT)
        print(f"validated {args.report} status={payload['verdict']['status']}")
        return
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
    print(f"wrote {args.report} status={payload['verdict']['status']}")


if __name__ == "__main__":
    main()

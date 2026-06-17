#!/usr/bin/env python3
"""Run the MiniGrid architecture tournament."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


LAB_ROOT = Path(__file__).resolve().parents[1]
if str(LAB_ROOT) not in sys.path:
    sys.path.insert(0, str(LAB_ROOT))

from bedc_quality_lab.mg_cap_tournament import (
    TournamentConfig,
    honest_summary,
    run_tournament,
    write_report_json,
    write_report_markdown,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--demo-episodes", type=int, default=800)
    parser.add_argument("--validation-demo-episodes", type=int, default=96)
    parser.add_argument("--eval-episodes", type=int, default=256)
    parser.add_argument("--train-steps", type=int, default=6000)
    parser.add_argument("--batch-size", type=int, default=96)
    parser.add_argument("--context-length", type=int, default=32)
    parser.add_argument("--hidden-dim", type=int, default=64)
    parser.add_argument("--learning-rate", type=float, default=2.0e-4)
    parser.add_argument("--eval-interval", type=int, default=1500)
    parser.add_argument("--balanced-batch-fraction", type=float, default=0.35)
    parser.add_argument("--off-expert-rate", type=float, default=0.15)
    parser.add_argument("--bootstrap-resamples", type=int, default=1000)
    parser.add_argument("--device", default="auto", choices=("auto", "cpu", "mps", "cuda"))
    parser.add_argument("--seeds", default="0,1,2")
    parser.add_argument("--skip-priority2", action="store_true")
    parser.add_argument("--max-episode-steps", type=int, default=None)
    parser.add_argument("--json-out", default="reports/mg_cap_tournament.json")
    parser.add_argument("--md-out", default="reports/mg_cap_tournament.md")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    seeds = tuple(int(part) for part in str(args.seeds).split(",") if part.strip())
    config = TournamentConfig(
        seeds=seeds,
        demo_episodes=args.demo_episodes,
        validation_demo_episodes=args.validation_demo_episodes,
        eval_episodes=args.eval_episodes,
        train_steps=args.train_steps,
        batch_size=args.batch_size,
        context_length=args.context_length,
        hidden_dim=args.hidden_dim,
        learning_rate=args.learning_rate,
        eval_interval=args.eval_interval,
        balanced_batch_fraction=args.balanced_batch_fraction,
        off_expert_rate=args.off_expert_rate,
        bootstrap_resamples=args.bootstrap_resamples,
        requested_device=args.device,
        run_priority2=not args.skip_priority2,
        max_episode_steps=args.max_episode_steps,
    )
    payload = run_tournament(config)
    write_report_json(payload, Path(args.json_out))
    write_report_markdown(payload, Path(args.md_out))
    print(honest_summary(payload))


if __name__ == "__main__":
    main()

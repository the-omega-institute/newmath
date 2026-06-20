#!/usr/bin/env python3
"""Run the q-source CIT stratum."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.cit_causal_transfer import CITConfig, run_q_arm


RESULT_PATH = Path("/tmp/cit-stratum.json")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--result-path", type=Path, default=RESULT_PATH)
    parser.add_argument("--seed", type=int, default=1726)
    parser.add_argument("--q", type=int, default=3)
    parser.add_argument("--train-n", type=int, default=2048)
    parser.add_argument("--eval-n", type=int, default=2048)
    parser.add_argument("--epochs", type=int, default=240)
    parser.add_argument("--device", default="cuda")
    return parser.parse_args(argv)


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    config = CITConfig(
        seed=args.seed,
        q=args.q,
        train_n=args.train_n,
        eval_n=args.eval_n,
        epochs=args.epochs,
        device=args.device,
    )
    return {
        "schema_id": "bedc-quality-lab:cit-stratum",
        "result_path": str(args.result_path),
        "runner": "scripts/run_cit_stratum.py",
        "result": run_q_arm(config),
    }


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = build_payload(args)
    _write_json(args.result_path, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

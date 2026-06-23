#!/usr/bin/env python3
"""Run controlled active gap-ledger curriculum arms."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab import torch_bedc_jepa
from bedc_quality_lab.model import choose_device


REPORT_PATH = ROOT / "reports" / "active_gap_ledger_controlled.json"


def _parse_seeds(raw: str) -> tuple[int, ...]:
    seeds = tuple(int(part.strip()) for part in raw.split(",") if part.strip())
    if not seeds:
        raise argparse.ArgumentTypeError("at least one seed is required")
    return seeds


def _format(value: float) -> str:
    return f"{value:.6f}"


def _print_result(packet: dict[str, object]) -> None:
    arms = packet["arms"]  # type: ignore[index]
    decision = packet["decision"]  # type: ignore[index]
    print("=== CONTROLLED RESULT ===")
    print("arm gap_auc coverage_delta r2_delta debt_delta")
    for arm in ("real", "coverage_preserving", "placebo"):
        summary = arms[arm]["summary"]  # type: ignore[index]
        print(
            " ".join(
                [
                    arm,
                    _format(float(summary["gap_detection_auc"]["mean"])),
                    _format(float(summary["certified_coverage_delta"]["mean"])),
                    _format(float(summary["linear_identifiability_r2_delta"]["mean"])),
                    _format(float(summary["bedc_debt_score_delta"]["mean"])),
                ]
            )
        )
    print(
        "VERDICT "
        f"{decision['verdict']}: "
        f"placebo_auc={float(decision['placebo_gap_detection_auc']):.6f}, "
        f"placebo_coverage_delta={float(decision['placebo_certified_coverage_delta']):.6f}, "
        f"placebo_r2_delta={float(decision['placebo_linear_identifiability_r2_delta']):.6f}, "
        f"qualifying_arms={decision['qualifying_arms']}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seeds", type=_parse_seeds, default=(4242, 4259, 4276))
    parser.add_argument("--epochs", type=int, default=80)
    parser.add_argument("--initial-train-count", type=int, default=512)
    parser.add_argument("--pool-count", type=int, default=1536)
    parser.add_argument("--test-count", type=int, default=512)
    parser.add_argument("--active-budget", type=int, default=192)
    parser.add_argument("--preserve-fraction", type=float, default=0.5)
    args = parser.parse_args()

    device = choose_device("cuda")
    if device.resolved_device != "cuda":
        raise RuntimeError(f"controlled active gap-ledger requires cuda, got {device.resolved_device}")

    config = torch_bedc_jepa.ActiveGapLedgerConfig(
        initial_train_count=args.initial_train_count,
        pool_count=args.pool_count,
        test_count=args.test_count,
        active_budget=args.active_budget,
        epochs=args.epochs,
        gap_auc_floor=0.0,
        gap_auc_min_delta=-1.0,
        latent_r2_min_delta=-1.0,
        unlogged_error_ceiling=1.0,
        coverage_min_delta=-1.0,
    )
    packet = torch_bedc_jepa.run_active_gap_ledger_controlled(
        seeds=args.seeds,
        config=config,
        preserve_fraction=args.preserve_fraction,
    )
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {REPORT_PATH.relative_to(ROOT)}")
    _print_result(packet)


if __name__ == "__main__":
    main()

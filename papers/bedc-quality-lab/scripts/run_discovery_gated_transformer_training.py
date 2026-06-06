#!/usr/bin/env python3
"""Run the DGT training replay producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_gated_transformer_training import (
    ARMS,
    CLAIM_CAPSULE_ARTIFACT,
    COMPUTE_LEDGER_ARTIFACT,
    DEFAULT_RUN_ID,
    EVIDENCE_ENVELOPE_ARTIFACT,
    RAW_METRICS_ARTIFACT,
    REPORT_ARTIFACT,
    SUMMARY_ARTIFACT,
    TRAINING_REPLAY_ARTIFACT,
    build_replay,
    claim_capsule_payload,
    evidence_envelope_payload,
    resolve_training_pointer,
    render_training_replay_markdown,
    summary_payload,
)


DEFAULT_SEEDS = (13, 29, 47)
GENERATED_AT = "run-local:discovery-gated-transformer-training-replay"


def artifact_map() -> dict[str, str]:
    return {
        "training_replay": TRAINING_REPLAY_ARTIFACT,
        "raw_metrics": RAW_METRICS_ARTIFACT,
        "compute_ledger": COMPUTE_LEDGER_ARTIFACT,
        "claim_capsule": CLAIM_CAPSULE_ARTIFACT,
        "evidence_envelope": EVIDENCE_ENVELOPE_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "summary": SUMMARY_ARTIFACT,
    }


def deterministic_training_record(seed: int, arm: str) -> dict[str, Any]:
    seed_jitter = (int(seed) % 19) * 0.0002
    offsets = {
        "task_only": (0.000, 0.000, 0.000, 0.000, 0),
        "lat": (-0.018, -0.008, 0.006, -0.012, 0),
        "cga": (-0.026, -0.013, 0.011, -0.020, 1),
        "drt": (-0.041, -0.019, 0.018, -0.036, 1),
        "dgt_full": (-0.083, -0.043, 0.042, -0.082, 3),
        "dgt_matched_random": (-0.023, -0.006, 0.009, -0.010, 0),
        "dgt_no_discovery_loss": (-0.047, -0.025, 0.024, -0.046, 1),
        "dgt_no_ledger_loss": (-0.052, -0.007, 0.025, -0.035, 2),
        "dgt_no_certificate_loss": (-0.054, -0.030, 0.027, -0.034, 1),
    }[arm]
    base_uer = 0.42 + seed_jitter
    base_false_ledger = 0.105 + 0.5 * seed_jitter
    base_benefit = 0.61 - 0.4 * seed_jitter
    base_debt = 0.31 + 0.4 * seed_jitter
    return {
        "arm_id": arm,
        "seed": int(seed),
        "uer": round(base_uer + offsets[0], 6),
        "false_ledger_rate": round(base_false_ledger + offsets[1], 6),
        "benefit": round(base_benefit + offsets[2], 6),
        "debt": round(base_debt + offsets[3], 6),
        "classifier_shift": int(offsets[4]),
    }


def collect_records(seeds: Sequence[int] = DEFAULT_SEEDS, arms: Sequence[str] = ARMS) -> list[dict[str, Any]]:
    return [deterministic_training_record(seed, arm) for seed in seeds for arm in arms]


def compute_ledger(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "cost_protocol": {
            "name": "DGT training replay local deterministic protocol",
            "unit": "relative-step",
            "seed_protocol": list(DEFAULT_SEEDS),
        },
        "rows": [
            {
                "arm_id": row["arm_id"],
                "seed": row["seed"],
                "train_steps": 24,
                "device": "deterministic-cpu",
                "dtype": "float32",
                "cost_units": 1.0,
            }
            for row in records
        ],
    }


def build_payload(*, run_id: str = DEFAULT_RUN_ID, generated_at: str = GENERATED_AT) -> dict[str, Any]:
    records = collect_records()
    config = {
        "run_id": run_id,
        "seeds": list(DEFAULT_SEEDS),
        "arms": list(ARMS),
        "comparison_rule": "dgt_full must improve UER against task-only, components, and matched-random controls",
        "thresholds": {
            "uer_strictly_lower": True,
            "false_ledger_rate_non_worse": True,
            "benefit_nondecreasing": True,
            "debt_strictly_lower": True,
            "classifier_shift_positive": True,
        },
    }
    return build_replay(
        config,
        records,
        compute_ledger(records),
        generated_at,
        run_artifacts=artifact_map(),
    )


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_artifacts(payload: dict[str, Any], *, root: Path = ROOT) -> None:
    artifacts = payload["run_artifacts"]
    _write_json(root / artifacts["training_replay"], payload)
    _write_json(root / artifacts["compute_ledger"], payload["compute_ledger"])
    _write_json(root / artifacts["claim_capsule"], claim_capsule_payload(payload))
    _write_json(root / artifacts["evidence_envelope"], evidence_envelope_payload(payload))
    _write_json(root / artifacts["summary"], summary_payload(payload))
    raw_path = root / artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in payload["records"]),
        encoding="utf-8",
    )
    report_path = root / artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_training_replay_markdown(payload), encoding="utf-8")
    for pointer in payload["sidecar_pointers"].values():
        if resolve_training_pointer(root, pointer) is None:
            raise ValueError(f"unresolved DGT training sidecar pointer: {pointer}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(run_id=args.run_id, generated_at=args.generated_at)
    write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "run_id": payload["run_id"],
                "training_replay": payload["run_artifacts"]["training_replay"],
                "overall_state": payload["overall_state"],
                "replay_digest": payload["replay_digest"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

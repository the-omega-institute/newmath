#!/usr/bin/env python3
"""Run the LeJEPA mini-grid backend evidence producer."""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.lejepa_mini_grid import (
    DEFAULT_ALIGNMENT_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    LeJEPAMiniGridProjection,
    NEGATIVE_DIAGNOSIS_ARTIFACT,
    build_lejepa_mini_grid_negative_diagnosis,
    default_grid,
    validate_lejepa_mini_grid_negative_diagnosis,
)
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID, CLAIM_CAPSULE_SCHEMA_ID
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from scripts import run_gaussian_ou_lejepa
from scripts.run_sigreg_gaussianity_reproduction import GuardThresholds, SlicedCFGaussianityProbe


DEFAULT_RUN_ID = "lejepa-mini-grid"
DEFAULT_SAMPLE_COUNT = 384
DEFAULT_DIRECTIONS = 16
DEFAULT_FREQUENCIES = (0.5, 1.0, 1.5, 2.0)
NEGATIVE_WITNESS_OWNER_POINTER = "$.run_local.negative_witness[0]"
NEGATIVE_WITNESS_KEYS = (
    "witness_id",
    "source_artifact",
    "source_pointer",
    "bedc_gap_field",
    "demotion_rule",
    "regression_test",
    "evidence_pointer",
    "status",
    "reason",
)
NEGATIVE_WITNESS_REGRESSION_TEST = (
    "tests/test_lejepa_mini_grid.py::test_lejepa_run_local_negative_witness_records_d2_hg2_failure"
)
MIXING_ALIASES = {
    "spiral": "spiral",
    "parabolic": "parabolic_shear",
    "realnvp": "realnvp_coupling",
}


def _artifact_map(run_id: str) -> dict[str, str]:
    run_dir = f"reports/runs/{run_id}"
    return {
        "summary": f"{run_dir}/summary.json",
        "claim_capsule": f"{run_dir}/claim_capsule.json",
        "raw_metrics": f"{run_dir}/raw_metrics.jsonl",
        "report": f"{run_dir}/report.md",
    }


def _negative_witness_owner_ref(run_id: str) -> dict[str, str]:
    return {
        "artifact": _artifact_map(run_id)["claim_capsule"],
        "pointer": NEGATIVE_WITNESS_OWNER_POINTER,
    }


def _build_lejepa_run_local_negative_witness(capsule_artifact: str) -> dict[str, Any]:
    return {
        "witness_id": "lejepa-mini-grid:lambda-rho-trend-hardgate-failure",
        "source_artifact": capsule_artifact,
        "source_pointer": "$.failed_gate",
        "bedc_gap_field": "lambda_rho_trend_gap",
        "demotion_rule": "demote_to_DN_on_D2_HG2_failure",
        "regression_test": NEGATIVE_WITNESS_REGRESSION_TEST,
        "evidence_pointer": f"{capsule_artifact}:$.hardgates.D2-HG2",
        "status": "fail",
        "reason": "D2-HG2 records failed lambda/rho trend evidence for the LeJEPA mini-grid claim capsule.",
    }


def resolve_claim_capsule_pointer(payload: Mapping[str, Any], pointer: str) -> Any:
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _validate_lejepa_run_local_negative_witness(row: Mapping[str, Any], capsule_payload: Mapping[str, Any]) -> bool:
    if set(row) != set(NEGATIVE_WITNESS_KEYS):
        return False
    capsule_artifact = str(row.get("source_artifact", ""))
    if not capsule_artifact:
        return False
    source_value = resolve_claim_capsule_pointer(
        capsule_payload,
        str(row.get("source_pointer", "")),
    )
    evidence_value = None
    evidence_pointer = str(row.get("evidence_pointer", ""))
    if evidence_pointer.startswith(f"{capsule_artifact}:$"):
        _, pointer = evidence_pointer.split(":", 1)
        evidence_value = resolve_claim_capsule_pointer(capsule_payload, pointer)
    regression_test = str(row.get("regression_test", ""))
    regression_resolved = False
    if "::" in regression_test:
        test_file, test_name = regression_test.split("::", 1)
        test_path = ROOT / test_file
        regression_resolved = test_path.exists() and f"def {test_name}" in test_path.read_text(encoding="utf-8")
    return (
        source_value == "D2-HG2"
        and isinstance(evidence_value, Mapping)
        and evidence_value.get("status") == "fail"
        and evidence_value.get("lambda_collapse_rate_increasing") is False
        and evidence_value.get("lambda_quality_q_decreasing") is False
        and evidence_value.get("rho_linear_identifiability_r2_increasing") is False
        and regression_resolved
    )


def finalize_negative_witness_projection(projection: Mapping[str, Any], *, run_id: str) -> dict[str, Any]:
    finalized = copy.deepcopy(dict(projection))
    summary = dict(finalized["summary_payload"])
    capsule = dict(finalized["claim_capsule_payload"])
    artifacts = dict(summary["run_artifacts"])
    capsule_artifact = str(artifacts["claim_capsule"])
    row = _build_lejepa_run_local_negative_witness(capsule_artifact)
    if not _validate_lejepa_run_local_negative_witness(row, capsule):
        raise ValueError("LeJEPA negative witness source, evidence, or regression pointer is not foldable")
    hardgates = {
        "NW-HG1": {
            "status": "pass" if set(row) == set(NEGATIVE_WITNESS_KEYS) else "fail",
            "evidence_pointer": "$.run_local.negative_witness.0",
        },
        "NW-HG2": {
            "status": "pass" if row["status"] == "fail" else "fail",
            "evidence_pointer": row["source_pointer"],
        },
        "NW-HG3": {
            "status": "pass" if row["status"] == "fail" else "fail",
            "evidence_pointer": row["evidence_pointer"],
        },
    }
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    capsule["schema_id"] = CLAIM_CAPSULE_SCHEMA_ID
    if capsule.get("schema_id") != CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID:
        capsule["run_local_schema_id"] = CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
    capsule["run_local"] = {
        "negative_witness": [row],
        "negative_witness_hardgates": {
            "status": "pass" if not failed else "fail",
            "failed_gates": failed,
            "gates": hardgates,
        },
    }
    owner_ref = _negative_witness_owner_ref(run_id)
    summary["claim_capsule"] = {
        "artifact": capsule_artifact,
        "pointer": "$",
    }
    summary["negative_diagnosis"] = {
        "artifact": NEGATIVE_DIAGNOSIS_ARTIFACT,
        "pointer": "$",
        "diagnosis_ref": owner_ref,
    }
    finalized["summary_payload"] = summary
    finalized["claim_capsule_payload"] = capsule
    return finalized


def _collapse_rate(envelope: Any) -> float:
    cov_trace = float(envelope.metrics.get("covariance_trace", 0.0))
    r2 = float(envelope.metrics.get("linear_identifiability_r2", 0.0))
    return float(max(0.0, min(1.0, (1.0 - min(1.0, max(0.0, r2))) + max(0.0, 0.25 - cov_trace) / 0.25)))


def run_single_arm(
    *,
    alignment_lambda: float,
    rho: float,
    mixing: str,
    seed: int,
    sample_count: int,
    directions: int,
    frequencies: Sequence[float],
    use_torch: bool,
) -> dict[str, Any]:
    source_mixing = MIXING_ALIASES.get(str(mixing), str(mixing))
    envelope = run_gaussian_ou_lejepa.run_experiment(
        use_torch=use_torch,
        sample_count=int(sample_count),
        seed=int(seed),
        rho=float(rho),
        mixing=source_mixing,
        alignment_lambda=float(alignment_lambda),
        run_id=f"lejepa-mini-grid-arm-{seed}",
        envelope_artifact="reports/runs/lejepa-mini-grid/arm-envelope.json",
        report_artifact="reports/runs/lejepa-mini-grid/arm-report.md",
    )
    probe = SlicedCFGaussianityProbe(
        directions=int(directions),
        frequencies=tuple(float(value) for value in frequencies),
        guard_thresholds=GuardThresholds(
            cov_to_identity_max=10.0,
            min_cov_eigenvalue_floor=1.0e-8,
            min_projected_variance_floor=1.0e-8,
        ),
    )
    base = np.asarray(
        [
            [float(envelope.metrics.get("linear_identifiability_r2", 0.0)), float(envelope.metrics.get("quality_q", 0.0))],
            [float(envelope.metrics.get("actual_recovery_mse", 0.0)), float(envelope.metrics.get("theorem3_bound_mse", 0.0))],
            [float(envelope.metrics.get("alignment_loss_mse", 0.0)), float(envelope.metrics.get("covariance_deviation", 0.0))],
        ],
        dtype=np.float64,
    )
    score = probe.score(base, seed=int(seed), directions=min(2, int(directions)), frequencies=tuple(float(value) for value in frequencies))
    return {
        "alignment_lambda": float(alignment_lambda),
        "rho": float(rho),
        "mixing": str(mixing),
        "source_mixing": source_mixing,
        "seed": int(seed),
        "sample_count": int(sample_count),
        "alignment_loss": float(envelope.metrics.get("alignment_loss_mse", 0.0)),
        "sigreg_sliced_cf": float(score["sigreg_penalty"]),
        "covariance_proxy": float(envelope.metrics.get("covariance_deviation", envelope.metrics.get("whitening_deviation_epsilon", 0.0))),
        "linear_identifiability_r2": float(envelope.metrics.get("linear_identifiability_r2", 0.0)),
        "actual_recovery_mse": float(envelope.metrics.get("actual_recovery_mse", 0.0)),
        "theorem3_bound_mse": float(envelope.metrics.get("theorem3_bound_mse", 0.0)),
        "collapse_rate": _collapse_rate(envelope),
        "quality_q": float(envelope.metrics.get("quality_q", 0.0)),
        "source_run_id": str(envelope.run_id),
    }


def collect_records(
    *,
    sample_count: int,
    directions: int,
    frequencies: Sequence[float],
    use_torch: bool,
    alignment_lambdas: Sequence[float] = DEFAULT_ALIGNMENT_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
) -> list[dict[str, Any]]:
    records = []
    grid = (
        default_grid()
        if tuple(float(value) for value in alignment_lambdas) == DEFAULT_ALIGNMENT_LAMBDAS
        and tuple(float(value) for value in rhos) == DEFAULT_RHOS
        and tuple(str(value) for value in mixings) == DEFAULT_MIXINGS
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        else tuple(
            {
                "alignment_lambda": float(alignment_lambda),
                "rho": float(rho),
                "mixing": str(mixing),
                "seed": int(seed),
            }
            for alignment_lambda in alignment_lambdas
            for rho in rhos
            for mixing in mixings
            for seed in seeds
        )
    )
    for cell in grid:
        records.append(
            run_single_arm(
                alignment_lambda=float(cell["alignment_lambda"]),
                rho=float(cell["rho"]),
                mixing=str(cell["mixing"]),
                seed=int(cell["seed"]),
                sample_count=int(sample_count),
                directions=int(directions),
                frequencies=frequencies,
                use_torch=bool(use_torch),
            )
        )
    return records


def build_projection(
    *,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str | None = None,
    sample_count: int = DEFAULT_SAMPLE_COUNT,
    directions: int = DEFAULT_DIRECTIONS,
    frequencies: Sequence[float] = DEFAULT_FREQUENCIES,
    use_torch: bool = False,
    alignment_lambdas: Sequence[float] = DEFAULT_ALIGNMENT_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    full_lejepa_claim: bool = False,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    records = collect_records(
        sample_count=sample_count,
        directions=directions,
        frequencies=frequencies,
        use_torch=use_torch,
        alignment_lambdas=alignment_lambdas,
        rhos=rhos,
        mixings=mixings,
        seeds=seeds,
    )
    artifacts = _artifact_map(run_id)
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "sample_count": int(sample_count),
        "directions": int(directions),
        "frequencies": [float(value) for value in frequencies],
        "alignment_lambdas": [float(value) for value in alignment_lambdas],
        "rhos": [float(value) for value in rhos],
        "mixings": [str(value) for value in mixings],
        "seeds": [int(value) for value in seeds],
        "use_torch": bool(use_torch),
        "full_lejepa_claim": bool(full_lejepa_claim),
    }
    projection = LeJEPAMiniGridProjection(
        config=config,
        records=records,
        generated_at=timestamp,
        run_artifacts=artifacts,
    ).project()
    return finalize_negative_witness_projection(projection, run_id=run_id)


def write_artifacts(projection: Mapping[str, Any], *, root: Path) -> None:
    summary = dict(projection["summary_payload"])
    capsule_payload = dict(projection["claim_capsule_payload"])
    negative_witness = capsule_payload.get("run_local", {}).get("negative_witness")
    if capsule_payload.get("schema_id") != CLAIM_CAPSULE_SCHEMA_ID or not isinstance(negative_witness, list) or len(negative_witness) != 1:
        raise ValueError("LeJEPA mini-grid projection is not finalized")
    if not _validate_lejepa_run_local_negative_witness(negative_witness[0], capsule_payload):
        raise ValueError("LeJEPA negative witness source, evidence, or regression pointer is not foldable")
    artifacts = summary["run_artifacts"]
    paths = {
        "summary": root / artifacts["summary"],
        "claim_capsule": root / artifacts["claim_capsule"],
        "raw_metrics": root / artifacts["raw_metrics"],
        "report": root / artifacts["report"],
        "negative_diagnosis": root / NEGATIVE_DIAGNOSIS_ARTIFACT,
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)
    paths["summary"].write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["claim_capsule"].write_text(json.dumps(capsule_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["raw_metrics"].write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in projection["raw_rows"]),
        encoding="utf-8",
    )
    paths["report"].write_text(str(projection["report_markdown"]), encoding="utf-8")
    diagnosis = build_lejepa_mini_grid_negative_diagnosis(
        summary_payload=summary,
        claim_capsule_payload=capsule_payload,
        generated_at=str(summary.get("generated_at", "")),
    )
    validate_lejepa_mini_grid_negative_diagnosis(diagnosis, root=root)
    paths["negative_diagnosis"].write_text(json.dumps(diagnosis, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _parse_float_list(value: str) -> tuple[float, ...]:
    result = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one float is required")
    return result


def _parse_int_list(value: str) -> tuple[int, ...]:
    result = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one integer is required")
    return result


def _parse_str_list(value: str) -> tuple[str, ...]:
    result = tuple(item.strip() for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one string is required")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--directions", type=int, default=DEFAULT_DIRECTIONS)
    parser.add_argument("--frequencies", type=_parse_float_list, default=DEFAULT_FREQUENCIES)
    parser.add_argument("--alignment-lambdas", type=_parse_float_list, default=DEFAULT_ALIGNMENT_LAMBDAS)
    parser.add_argument("--rhos", type=_parse_float_list, default=DEFAULT_RHOS)
    parser.add_argument("--mixings", type=_parse_str_list, default=DEFAULT_MIXINGS)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--use-torch", action="store_true")
    parser.add_argument("--full-lejepa-claim", action="store_true")
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        sample_count=args.sample_count,
        directions=args.directions,
        frequencies=args.frequencies,
        use_torch=args.use_torch,
        alignment_lambdas=args.alignment_lambdas,
        rhos=args.rhos,
        mixings=args.mixings,
        seeds=args.seeds,
        full_lejepa_claim=args.full_lejepa_claim,
    )
    write_artifacts(projection, root=args.root)
    summary = projection["summary_payload"]
    print(
        json.dumps(
            {
                "run_id": summary["run_id"],
                "summary": summary["run_artifacts"]["summary"],
                "claim_capsule": summary["run_artifacts"]["claim_capsule"],
                "result": summary["result"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

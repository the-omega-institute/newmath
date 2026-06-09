import inspect
import math

from bedc_quality_lab.latent_distribution import CANONICAL_LATENT_DISTRIBUTION_ARMS
from scripts import run_nongaussian_distribution_sweep as sweep


def _fixture_record(key, seed, r2):
    return {
        "distribution_key": key,
        "distribution": key.split(":", 1)[0],
        "shape_parameter": None,
        "seed": seed,
        "paired_seed_id": seed,
        "linear_identifiability_r2": float(r2),
        "actual_recovery_mse": 0.1,
        "theorem3_bound_mse": 1.0,
        "latent_distribution_debt": 0.0 if key == "gaussian" else 0.16,
        "quality_q": 0.2,
        "source_spec": {
            "latent_distribution": {"family": key.split(":", 1)[0], "coverage_key": key},
        },
        "debt_items": [
            "kind=source; residue=distribution-family-coverage; severity=none; status=closed; score=0.000000"
        ],
    }


def test_nongaussian_sweep_uses_canonical_arm_tuple():
    source = inspect.getsource(sweep)

    assert sweep.CANONICAL_LATENT_DISTRIBUTION_ARMS is CANONICAL_LATENT_DISTRIBUTION_ARMS
    assert "CANONICAL_LATENT_DISTRIBUTION_ARMS = (" not in source


def test_nongaussian_sweep_uses_paired_seeds():
    seeds = [11, 22]
    records = [
        _fixture_record(spec.distribution_family_key(), seed, 0.9)
        for seed in seeds
        for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
    ]

    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        selected = [
            record["paired_seed_id"]
            for record in records
            if record["distribution_key"] == spec.distribution_family_key()
        ]
        assert selected == seeds


def test_run_arm_record_nongaussian_production_path():
    sample_count = 32
    seed = sweep.derive_seeds(base_seed=123, count=1)[0]
    spec = next(
        spec
        for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
        if spec.distribution_family_key() == "laplace"
    )
    gaussian_spec = CANONICAL_LATENT_DISTRIBUTION_ARMS[0]

    record = sweep.run_arm_record(spec, seed=seed, sample_count=sample_count)
    gaussian_record = sweep.run_arm_record(gaussian_spec, seed=seed, sample_count=sample_count)

    assert record["distribution_key"] == spec.distribution_family_key()
    for metric_name in sweep.METRIC_NAMES:
        assert math.isfinite(record["metrics"][metric_name])
    for metric_name in (
        "linear_identifiability_r2",
        "actual_recovery_mse",
        "theorem3_bound_mse",
        "latent_distribution_debt",
        "quality_q",
    ):
        assert math.isfinite(record[metric_name])

    assert record["source_spec"]["sample_count"] == sample_count
    assert record["source_spec"]["latent_dim"] == spec.latent_dim
    assert record["source_spec"]["latent_distribution"] == spec.to_source_spec()

    classifier_spec = record["classifier_spec"]
    assert classifier_spec["train_count"] + classifier_spec["eval_count"] == sample_count
    assert classifier_spec["train_count"] > 0
    assert classifier_spec["eval_count"] > 0
    assert classifier_spec["overlap_count"] == 0

    latent_debt = record["latent_distribution_debt_item"]
    gaussian_debt = gaussian_record["latent_distribution_debt_item"]
    assert latent_debt["residue"] == "latent-distribution-gaussianity"
    assert latent_debt["status"] == "open"
    assert float(latent_debt["score"]) > 0.0
    assert gaussian_debt["status"] == "closed"
    assert float(gaussian_debt["score"]) == 0.0

    coverage_debt = record["distribution_family_coverage_debt_item"]
    assert coverage_debt["residue"] == "distribution-family-coverage"
    assert coverage_debt["status"] == "closed"


def test_payload_generates_one_record_per_arm_per_seed():
    sample_count = 24
    seeds = sweep.derive_seeds(base_seed=321, count=2)
    records = [
        sweep.run_arm_record(spec, seed=seed, sample_count=sample_count)
        for seed in seeds
        for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
    ]

    payload = sweep._payload(records, seeds)
    arm_keys = [spec.distribution_family_key() for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS]

    assert len(records) == len(CANONICAL_LATENT_DISTRIBUTION_ARMS) * len(seeds)
    assert sorted({record["distribution_key"] for record in records}) == sorted(arm_keys)
    for key in arm_keys:
        selected = [record for record in records if record["distribution_key"] == key]
        assert [record["paired_seed_id"] for record in selected] == seeds

    assert payload["records"] == records
    assert payload["coverage_item"]["covered_distribution_keys"] == arm_keys
    assert payload["coverage_item"]["missing_distribution_keys"] == []
    assert set(payload["family_aggregates"]) == set(arm_keys)
    assert set(payload["claim_gate"]["cells"]) == set(arm_keys) - {"gaussian"}

    expected_report_keys = {
        "distribution",
        "shape_parameter",
        "linear_identifiability_r2",
        "actual_recovery_mse",
        "theorem3_bound_mse",
        "latent_distribution_debt",
        "quality_q",
        "not_claimed",
    }
    for record in payload["records"]:
        assert expected_report_keys <= record.keys()
    markdown = sweep._render_markdown(payload)
    for key in {
        "distribution",
        "shape_parameter",
        "linear_identifiability_r2",
        "actual_recovery_mse",
        "theorem3_bound_mse",
        "latent_distribution_debt",
        "quality_q",
    }:
        assert key in markdown
    assert "not claimed" in markdown.lower()


def test_ci_gate_controls_gaussian_optimality_claim():
    records = [
        _fixture_record("gaussian", 1, 0.80),
        _fixture_record("gaussian", 2, 0.80),
        _fixture_record("laplace", 1, 0.79),
        _fixture_record("laplace", 2, 0.79),
    ]
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        key = spec.distribution_family_key()
        if key not in {"gaussian", "laplace"}:
            records.extend([_fixture_record(key, 1, 0.80), _fixture_record(key, 2, 0.80)])

    gate = sweep._claim_gate(records)

    assert gate["status"] == "observed-debt-pipeline-only"
    assert gate["cells"]["laplace"]["ci"]["supported"] is True
    assert gate["cells"]["laplace"]["supports_gaussian_optimality"] is False


def test_no_drop_emits_negative_result_ledger():
    records = [
        _fixture_record("gaussian", 1, 0.80),
        _fixture_record("gaussian", 2, 0.80),
        _fixture_record("laplace", 1, 0.82),
        _fixture_record("laplace", 2, 0.79),
    ]
    for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS:
        key = spec.distribution_family_key()
        if key not in {"gaussian", "laplace"}:
            records.extend([_fixture_record(key, 1, 0.70), _fixture_record(key, 2, 0.70)])

    ledger = sweep._negative_result_ledger(records)

    assert any(entry["distribution_key"] == "laplace" for entry in ledger)
    assert all("not evidence" in entry["not_claimed"] for entry in ledger)


def test_markdown_renders_from_payload_only():
    payload = {
        "generated_at": "fixture-time",
        "config": {
            "seed_count": 2,
            "sample_count": 32,
            "rho": 0.82,
            "arms": [spec.to_source_spec() for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS],
        },
        "main_claim_status": "observed-debt-pipeline-only",
        "not_claimed": "Observed-debt-only fixture.",
        "coverage_item": {
            "kind": "source",
            "residue": "distribution-family-coverage",
            "covered_distribution_keys": [spec.distribution_family_key() for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS],
            "missing_distribution_keys": [],
            "debt_item": {"status": "closed", "score": "0.000000"},
        },
        "family_aggregates": {
            spec.distribution_family_key(): {
                "distribution": spec.family,
                "shape_parameter": spec.shape_parameter,
                "metrics": {
                    "linear_identifiability_r2": {"mean": 0.5},
                    "actual_recovery_mse": {"mean": 0.4},
                    "theorem3_bound_mse": {"mean": 1.2},
                    "latent_distribution_debt": {"mean": 0.1},
                    "quality_q": {"mean": -0.2},
                },
            }
            for spec in CANONICAL_LATENT_DISTRIBUTION_ARMS
        },
        "claim_gate": {
            "status": "observed-debt-pipeline-only",
            "minimum_r2_drop": 0.01,
            "not_claimed": "Fixture gate.",
            "cells": {
                "laplace": {
                    "ci": {"supported": False, "reason": "fixture"},
                    "supports_gaussian_optimality": False,
                }
            },
        },
        "negative_result_ledger": [
            {
                "distribution_key": "laplace",
                "paired_seed_ids": [1],
                "not_claimed": "Fixture not claimed.",
            }
        ],
    }

    markdown = sweep._render_markdown(payload)

    assert "fixture-time" in markdown
    assert "observed-debt-pipeline-only" in markdown
    assert "non-Gaussian always fails" not in markdown
    assert "always fail" not in markdown

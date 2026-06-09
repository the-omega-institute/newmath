import math

import pytest

from bedc_quality_lab.mixing import canonical_mixing_families
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts import run_mixing_family_sweep as sweep


def make_envelope(*, mixing, seed, metric_base=1.0):
    metrics = {
        name: float(metric_base + index)
        for index, name in enumerate(sweep.METRIC_NAMES)
    }
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=f"fixture-{mixing}-{seed}",
        source_spec={
            "name": "gaussian-ou-toy-world",
            "latent_dim": 2,
            "sample_count": 8,
            "rho": sweep.RHO,
            "rho_by_axis": [sweep.RHO, sweep.RHO],
            "latent_distribution": "gaussian",
            "mixing": mixing,
            "transition_kernel": {"isotropic": True, "anisotropy_gap": 0.0},
        },
        pattern_spec={"name": "latent-linear-recovery"},
        classifier_spec={
            "name": "standardized-nonlinear-observation",
            "output_dim": 2,
            "training": "deterministic-standardization",
        },
        stability_spec={"name": "fixed-seed-single-source", "seed": seed},
        metrics=metrics,
        ledger_gaps=[
            "kind=source; residue=mixing-family-coverage; severity=high; status=open"
        ],
        debt_items=[
            "kind=source; residue=mixing-family-coverage; severity=high; status=open; score=0.220000"
        ],
        artifacts={"envelope": "reports/mixing_family_sweep.json"},
    )


def test_derive_seeds_has_deterministic_floor_grid():
    assert sweep._derive_seeds(498, 6) == [498, 1530, 2644, 3840, 5118, 6478]
    assert sweep._derive_seeds(17, 0) == []


def test_run_record_passes_family_seed_and_artifact_arguments(monkeypatch):
    calls = []

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return make_envelope(mixing=kwargs["mixing"], seed=kwargs["seed"], metric_base=2.0)

    monkeypatch.setattr(sweep, "run_experiment", fake_run_experiment)

    record = sweep._run_record(mixing="spiral", seed=1530, sample_count=16)

    assert record["status"] == "ok"
    assert record["mixing"] == "spiral"
    assert record["source_mixing"] == "spiral"
    assert record["metrics"]["quality_q"] == pytest.approx(8.0)
    assert record["envelope_projection"]["schema_id"] == SCHEMA_ID
    assert calls == [
        {
            "use_torch": False,
            "sample_count": 16,
            "seed": 1530,
            "rho": sweep.RHO,
            "mixing": "spiral",
            "run_id": "mixing-family-spiral-seed-1530",
            "envelope_artifact": "reports/mixing_family_sweep.json",
            "report_artifact": "reports/mixing_family_sweep.md",
        }
    ]


def test_aggregate_and_payload_derive_canonical_only_coverage():
    records = []
    for index, family in enumerate(canonical_mixing_families()):
        for seed in (498, 1530):
            records.append(
                {
                    "mixing": family,
                    "seed": seed,
                    "status": "ok",
                    "source_mixing": family,
                    "mixing_debt_item": {
                        "kind": "source",
                        "residue": "mixing-family-coverage",
                        "status": "open",
                        "score": "0.220000",
                    },
                    "metrics": {
                        name: float(index + offset)
                        for offset, name in enumerate(sweep.METRIC_NAMES)
                    },
                }
            )

    payload = sweep._payload(records, [498, 1530])

    assert payload["coverage_item"]["covered_families"] == list(canonical_mixing_families())
    assert payload["coverage_item"]["missing_families"] == []
    assert payload["coverage_item"]["debt_item"]["status"] == "closed"
    assert payload["coverage_item"]["debt_item"]["score"] == "0.000000"
    assert payload["config"]["seed_floor"] == sweep.SEED_COUNT
    assert payload["source_artifacts"]["mixing_surface"] == "bedc_quality_lab/mixing.py"
    assert "non-canonical mixing closure" in payload["applicability_boundary"]["not_claimed"]
    assert payload["family_aggregates"]["spiral"]["ok_count"] == 2
    assert payload["family_aggregates"]["spiral"]["metrics"]["quality_q"]["n"] == 2


def test_coverage_item_stays_partial_or_open_without_all_canonical_families():
    family_a, family_b, family_c, family_d = canonical_mixing_families()

    open_item = sweep._coverage_item([family_a, "not-canonical"])
    partial_item = sweep._coverage_item([family_a, family_b, family_c, "not-canonical"])
    closed_item = sweep._coverage_item([family_a, family_b, family_c, family_d, "not-canonical"])
    anti_close_item = sweep._coverage_item(["a", "b", "c", "d", "e"])

    assert open_item["debt_item"]["status"] == "open"
    assert partial_item["debt_item"]["status"] == "partial"
    assert closed_item["debt_item"]["status"] == "closed"
    assert anti_close_item["debt_item"]["status"] == "open"


def test_render_markdown_projects_json_payload():
    records = []
    for index, family in enumerate(canonical_mixing_families()):
        records.append(
            {
                "mixing": family,
                "seed": 498,
                "status": "ok",
                "source_mixing": family,
                "mixing_debt_item": {
                    "kind": "source",
                    "residue": "mixing-family-coverage",
                    "status": "open",
                    "score": "0.220000",
                },
                "metrics": {
                    name: float(index + offset)
                    for offset, name in enumerate(sweep.METRIC_NAMES)
                },
            }
        )
    payload = sweep._payload(records, [498])

    report = sweep._render_markdown(payload)

    assert "# Canonical nonlinear mixing-family sweep" in report
    assert "Row: `source/mixing-family-coverage`" in report
    assert "Status: `closed`" in report
    assert "| `spiral` | 1 | `498` |" in report
    assert "## Applicability boundary" in report
    assert "non-canonical mixing closure" in report
    assert not math.isnan(payload["family_aggregates"]["spiral"]["metrics"]["quality_q"]["mean"])

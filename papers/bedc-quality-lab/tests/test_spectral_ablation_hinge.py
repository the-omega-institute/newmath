import json

import pytest

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.transition import TransitionKernelSpec
from scripts import run_spectral_ablation_hinge as hinge


def make_envelope(*, run_id, rho_by_axis, mixing, metrics):
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=run_id,
        source_spec={
            "name": "gaussian-ou-toy-world",
            "latent_dim": 2,
            "sample_count": 8,
            "rho": sum(rho_by_axis) / len(rho_by_axis),
            "rho_by_axis": list(rho_by_axis),
            "latent_distribution": "gaussian",
            "mixing": mixing,
            "transition_kernel": TransitionKernelSpec(rho_by_axis=rho_by_axis).to_source_spec(),
            "transition_isotropic": TransitionKernelSpec(rho_by_axis=rho_by_axis).is_isotropic(),
            "transition_anisotropy_gap": TransitionKernelSpec(rho_by_axis=rho_by_axis).anisotropy_gap(),
        },
        pattern_spec={"name": "latent-linear-recovery"},
        classifier_spec={"name": "fixture", "output_dim": 2, "training": "fixture"},
        stability_spec={"name": "fixed-seed-single-source"},
        metrics=metrics,
        ledger_gaps=[],
        debt_items=[],
        artifacts={"envelope": "reports/spectral_ablation_hinge.json"},
    )


def metrics(*, identifiability, error, margin, quality):
    return {
        "linear_identifiability_r2": identifiability,
        "actual_recovery_error": error,
        "theorem3_bound": 1.0,
        "bound_margin": margin,
        "quality_q": quality,
        "quality_margin": quality,
    }


def test_hinge_ledger_reads_only_transition_fields():
    spec = TransitionKernelSpec(rho_by_axis=(0.92, 0.64))
    ledger_before = hinge._build_hinge_ledger(spec)

    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(
            hinge,
            "run_experiment",
            lambda **kwargs: make_envelope(
                run_id=kwargs["run_id"],
                rho_by_axis=tuple(kwargs["transition_kernel"].rho_by_axis),
                mixing=kwargs["mixing"],
                metrics=metrics(identifiability=-10.0, error=99.0, margin=-50.0, quality=-20.0),
            ),
        )
        payload = hinge._payload()
    ledger_after = payload["hinge_ledger"]

    assert [row["deletion"]["axes"] for row in ledger_after] == [
        row["deletion"]["axes"] for row in ledger_before
    ]
    assert [row["hinge_rank"] for row in ledger_after] == [1, 2, 3]
    assert payload["hinge_ledger"][0]["deletion"]["axes"] == [0]
    assert "linear_identifiability_r2" not in json.dumps(payload["hinge_ledger"])
    assert "actual_recovery_error" not in json.dumps(payload["hinge_ledger"])


def test_apply_axis_damp_preserves_source_spec_and_valid_rho():
    source = TransitionKernelSpec(rho_by_axis=(0.92, 0.64))
    damped = hinge._apply_axis_damp(source, (0,), 0.38)

    assert source.rho_by_axis == (0.92, 0.64)
    assert damped.rho_by_axis == pytest.approx((0.3496, 0.64))
    assert all(-1.0 < value < 1.0 for value in damped.rho_by_axis)


def test_matched_random_controls_preserve_strength():
    ledger = hinge._build_hinge_ledger(TransitionKernelSpec(rho_by_axis=(0.92, 0.64)))
    controls = hinge._matched_random_controls(ledger, seed=7)

    single = controls[0]
    module = controls[1]

    assert single.name == "matched-random-single-axis"
    assert single.deletion_axes == (1,)
    assert single.damp_factor == pytest.approx(hinge.DAMP_FACTOR)
    assert module.name == "matched-random-module"
    assert len(module.deletion_axes) == 2
    assert module.damp_factor == pytest.approx(hinge.DAMP_FACTOR)


def test_rank_correlation_uses_observed_degradation_without_reordering():
    ledger = hinge._build_hinge_ledger(TransitionKernelSpec(rho_by_axis=(0.92, 0.64)))
    original_order = [row["deletion"]["axes"][:] for row in ledger]
    arms = [
        {
            "name": "hinge-ranked-treatment",
            "family": "hinge-ranked-treatment",
            "deletion_axes": [0],
            "observed_degradation_score": 0.1,
        },
        {
            "name": "tail-mixing-perturbation",
            "family": "tail-mixing-perturbation",
            "deletion_axes": [0],
            "observed_degradation_score": 0.2,
        },
        {
            "name": "two-axis-module-analogue",
            "family": "hinge-ranked-treatment",
            "deletion_axes": [0, 1],
            "observed_degradation_score": 0.8,
        },
    ]

    correlation = hinge._rank_correlation(ledger, arms)

    assert [row["deletion"]["axes"] for row in ledger] == original_order
    assert correlation["n"] == 3
    assert correlation["pairs"][0]["arm"] == "hinge-ranked-treatment"
    assert correlation["pairs"][0]["ledger_row_id"] == "delete-0"
    assert correlation["pairs"][0]["deletion_axes"] == [0]
    assert correlation["pairs"][0]["hinge_rank"] == 1
    assert correlation["pairs"][0]["observed_degradation_score"] == pytest.approx(0.1)
    assert "do not alter hinge ledger rank" in correlation["ordering_note"]


def test_negative_result_ledger_records_open_status():
    by_family = {
        "baseline": metrics(identifiability=1.0, error=0.0, margin=1.0, quality=1.0),
        "hinge-ranked-treatment": metrics(identifiability=0.98, error=0.01, margin=0.98, quality=0.98),
        "two-axis-module-analogue": metrics(identifiability=0.97, error=0.02, margin=0.97, quality=0.97),
        "tail-mixing-perturbation": metrics(identifiability=0.97, error=0.02, margin=0.97, quality=0.97),
        "matched-random-control": metrics(identifiability=0.50, error=0.40, margin=0.50, quality=0.50),
    }

    def fake_run_experiment(**kwargs):
        run_id = kwargs["run_id"]
        if "vanilla" in run_id:
            family = "baseline"
        elif "matched-random" in run_id:
            family = "matched-random-control"
        else:
            family = next(name for name in by_family if name in run_id)
        return make_envelope(
            run_id=run_id,
            rho_by_axis=tuple(kwargs["transition_kernel"].rho_by_axis),
            mixing=kwargs["mixing"],
            metrics=by_family[family],
        )

    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(hinge, "run_experiment", fake_run_experiment)
        payload = hinge._payload()
    report = hinge._render_markdown(json.loads(json.dumps(payload)))

    assert payload["ledger_summary"]["status"] == "open-or-partial"
    assert payload["negative_control_summary"]["treatment_better_than_all_controls"] is False
    assert "Ledger status: `open-or-partial`" in report


def test_payload_records_hardening_coverage_cell():
    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(
            hinge,
            "run_experiment",
            lambda **kwargs: make_envelope(
                run_id=kwargs["run_id"],
                rho_by_axis=tuple(kwargs["transition_kernel"].rho_by_axis),
                mixing=kwargs["mixing"],
                metrics=metrics(identifiability=0.9, error=0.1, margin=0.8, quality=0.7),
            ),
        )
        payload = hinge._payload()

    coverage = payload["ledger_summary"]["basis"]["hardening_coverage"]

    assert set(coverage) == {"recorded", "required", "items"}
    assert coverage["required"] == 4
    assert 0 <= coverage["recorded"] <= coverage["required"]
    assert [item["name"] for item in coverage["items"]] == [
        "sameClass equivalence",
        "margin stability",
        "finite ledger coverage",
        "missing-row negative example",
    ]


def test_duplicate_rank_pairs_do_not_cover_missing_ledger_row():
    ledger = hinge._build_hinge_ledger(TransitionKernelSpec(rho_by_axis=(0.92, 0.64)))
    arms = [
        {
            "name": "hinge-ranked-treatment",
            "family": "hinge-ranked-treatment",
            "deletion_axes": [0],
            "metrics": metrics(identifiability=0.9, error=0.1, margin=0.8, quality=0.7),
            "observed_degradation_score": 0.4,
        },
        {
            "name": "two-axis-module-analogue",
            "family": "hinge-ranked-treatment",
            "deletion_axes": [0, 1],
            "metrics": metrics(identifiability=0.8, error=0.2, margin=0.7, quality=0.6),
            "observed_degradation_score": 0.6,
        },
        {
            "name": "tail-mixing-perturbation",
            "family": "tail-mixing-perturbation",
            "deletion_axes": [0],
            "metrics": metrics(identifiability=0.7, error=0.3, margin=0.6, quality=0.5),
            "observed_degradation_score": 0.5,
        },
    ]
    rank_correlation = hinge._rank_correlation(ledger, arms)

    coverage = hinge._hardening_coverage(
        arms=arms,
        hinge_ledger=ledger,
        rank_correlation=rank_correlation,
        negative_control={
            "control_count": 1,
            "treatment_better_than_all_controls": False,
        },
    )
    coverage_items = {item["name"]: item for item in coverage["items"]}

    assert rank_correlation["n"] == len(ledger)
    assert [pair["deletion_axes"] for pair in rank_correlation["pairs"]] == [[0], [0, 1], [0]]
    assert coverage_items["finite ledger coverage"]["recorded"] is False
    assert coverage["recorded"] == 3


def test_payload_keeps_schema_id_unchanged():
    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(
            hinge,
            "run_experiment",
            lambda **kwargs: make_envelope(
                run_id=kwargs["run_id"],
                rho_by_axis=tuple(kwargs["transition_kernel"].rho_by_axis),
                mixing=kwargs["mixing"],
                metrics=metrics(identifiability=0.9, error=0.1, margin=0.8, quality=0.7),
            ),
        )
        payload = hinge._payload()

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert payload["config"]["schema_id"] == SCHEMA_ID
    assert payload["report_schema_id"] == "bedc-quality-lab:spectral-ablation-hinge-report"
    assert all(arm["envelope_projection"]["schema_id"] == SCHEMA_ID for arm in payload["arms"])

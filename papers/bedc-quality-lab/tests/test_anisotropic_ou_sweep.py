import json

import pytest

from bedc_quality_lab.schema import SCHEMA_ID
from bedc_quality_lab.transition import TransitionKernelSpec
from scripts import run_anisotropic_ou_sweep as sweep


def test_grid_and_seed_count_define_baseline_only_transition_cells():
    assert sweep.RHO_BY_AXIS_GRID == ((0.9, 0.9), (0.9, 0.6), (0.95, 0.3), (0.99, 0.5))
    assert sweep.SEED_COUNT >= 20
    assert sweep._derive_seeds(497, 3) == [497, 1523, 2607]


def test_run_record_calls_canonical_runner_with_transition_spec(monkeypatch):
    calls = []

    class Envelope:
        schema_id = SCHEMA_ID
        source_spec = {
            "transition_kernel": TransitionKernelSpec(rho_by_axis=(0.9, 0.6)).to_source_spec(),
        }
        classifier_spec = {"name": "standardized-nonlinear-observation"}
        debt_items = [
            "kind=source; residue=transition-isotropy; severity=medium; status=partial; score=0.072000"
        ]
        ledger_gaps = ["kind=source; residue=transition-isotropy; severity=medium; status=partial"]
        metrics = {name: float(index) for index, name in enumerate(sweep.METRIC_NAMES)}

        def to_dict(self):
            return {
                "schema_id": self.schema_id,
                "source_spec": self.source_spec,
                "classifier_spec": self.classifier_spec,
                "metrics": self.metrics,
            }

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return Envelope()

    monkeypatch.setattr(sweep, "run_experiment", fake_run_experiment)

    record = sweep._run_record(rho_by_axis=(0.9, 0.6), seed=11, sample_count=32)

    assert calls[0]["use_torch"] is False
    assert calls[0]["sample_count"] == 32
    assert calls[0]["seed"] == 11
    assert calls[0]["rho"] == pytest.approx(0.75)
    assert calls[0]["transition_kernel"] == TransitionKernelSpec(rho_by_axis=(0.9, 0.6))
    assert "latent_batch" not in calls[0]
    assert "latent_source_spec" not in calls[0]
    assert record["latent_distribution"] == "gaussian"
    assert record["transition_debt_item"]["score"] == "0.072000"
    assert record["transition_ledger_gaps"] == [
        "kind=source; residue=transition-isotropy; severity=medium; status=partial"
    ]


def test_payload_records_transition_debt_switch_and_boundary():
    records = []
    for rho_by_axis, score in (((0.9, 0.9), "0.000000"), ((0.9, 0.6), "0.072000")):
        records.append(
            {
                "rho_by_axis": list(rho_by_axis),
                "rho_key": sweep._rho_key(rho_by_axis),
                "seed": 1,
                "status": "ok",
                "transition_source_spec": TransitionKernelSpec(rho_by_axis=rho_by_axis).to_source_spec(),
                "transition_debt_item": {"score": score},
                "metrics": {name: 1.0 for name in sweep.METRIC_NAMES},
            }
        )
    payload = sweep._payload(records, [1])

    isotropic = payload["transition_debt_by_grid"][sweep._rho_key((0.9, 0.9))]
    anisotropic = payload["transition_debt_by_grid"][sweep._rho_key((0.9, 0.6))]

    assert isotropic["status"] == "closed"
    assert isotropic["debt_score_mean"] == pytest.approx(0.0)
    assert anisotropic["status"] == "open-or-partial"
    assert anisotropic["debt_score_mean"] == pytest.approx(0.072)
    assert payload["applicability_boundary"]["claimed_scope"] == "Gaussian latent + anisotropic transition"
    assert "non-Gaussian" in payload["applicability_boundary"]["not_claimed"]


def test_markdown_is_projection_from_payload_and_preserves_negative_result():
    records = []
    for rho_by_axis, quality_q in (((0.9, 0.9), 1.0), ((0.9, 0.6), 0.5)):
        records.append(
            {
                "rho_by_axis": list(rho_by_axis),
                "rho_key": sweep._rho_key(rho_by_axis),
                "seed": 1,
                "status": "ok",
                "transition_source_spec": TransitionKernelSpec(rho_by_axis=rho_by_axis).to_source_spec(),
                "transition_debt_item": {"score": "0.000000" if rho_by_axis == (0.9, 0.9) else "0.072000"},
                "metrics": {name: quality_q for name in sweep.METRIC_NAMES},
            }
        )
    payload = sweep._payload(records, [1])
    report = sweep._render_markdown(json.loads(json.dumps(payload)))

    assert "Gaussian latent + anisotropic transition" in report
    assert "Transition noise family: `gaussian`" in report
    assert "`(0.9, 0.6)` | -0.500000 | `True`" in report
    assert "0.072000" in report

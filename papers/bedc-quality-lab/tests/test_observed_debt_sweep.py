import math
from pathlib import Path

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts import run_observed_debt_sweep as runner


def make_envelope(*, run_id, axis_value, row, metric_value):
    kind, residue = row.split("/", 1)
    closed = axis_value in {2, 2000, 4096, True}
    status = "closed" if closed else "open"
    severity = "none" if closed else "high"
    score = 0.0 if closed else 0.2
    gap = [] if closed else [f"kind={kind}; residue={residue}; severity={severity}; status={status}"]
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=run_id,
        source_spec={"name": "fixture", "latent_dim": 2},
        pattern_spec={"name": "fixture"},
        classifier_spec={"name": "fixture", "output_dim": 2},
        stability_spec={"name": "fixture"},
        metrics={
            "linear_identifiability_r2": float(metric_value),
            "quality_debt": 0.0 if closed else 0.2,
        },
        ledger_gaps=gap,
        debt_items=[
            f"kind={kind}; residue={residue}; severity={severity}; status={status}; score={score:.6f}"
        ],
        artifacts={"envelope": runner.JSON_ARTIFACT, "report": runner.REPORT_ARTIFACT},
        bedc_refs=[],
    )


def patch_lightweight_records(monkeypatch):
    def fake_lejepa_cell(**kwargs):
        axis_value = kwargs["axis_value"]
        row = kwargs["row"]
        records = []
        for seed_index, seed in enumerate(kwargs["seeds"]):
            value = 0.82
            if kwargs["axis"] == "baseline":
                value = 0.80
            elif kwargs["axis"] == "C1" and axis_value in {1, 4}:
                value = 0.45
            elif kwargs["axis"] == "C2" and axis_value < 100:
                value = 0.50
            elif kwargs["axis"] == "C3" and axis_value < 512:
                value = 0.52
            envelope = make_envelope(
                run_id=f"fixture-{kwargs['axis']}-{axis_value}-{seed}",
                axis_value=axis_value,
                row=row,
                metric_value=value,
            )
            records.append(
                runner._metric_record(
                    envelope=envelope,
                    axis=kwargs["axis"],
                    axis_label=kwargs["axis_label"],
                    axis_value=axis_value,
                    seed=seed,
                    seed_index=seed_index,
                    row=row,
                    metric=kwargs["metric"],
                )
            )
        return tuple(records)

    def fake_action_cell(**kwargs):
        return fake_lejepa_cell(**kwargs)

    monkeypatch.setattr(runner, "_run_lejepa_cell", fake_lejepa_cell)
    monkeypatch.setattr(runner, "_run_action_transition_cell", fake_action_cell)


def test_c1_grid_is_encoder_dim_set_and_each_cell_has_dimension_row(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    c1 = [cell for cell in payload["cells"] if cell["axis"] == "C1"]

    assert {cell["axis_value"] for cell in c1} == {1, 2, 3, 4}
    assert all(cell["row"] == "source/dimension-match" for cell in c1)
    assert all(all(record["row_present"] for record in cell["records"]) for cell in c1)


def test_c2_grid_is_training_step_set_and_each_cell_has_optimizer_row(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    c2 = [cell for cell in payload["cells"] if cell["axis"] == "C2"]

    assert {cell["axis_value"] for cell in c2} == {10, 20, 50, 100, 500, 2000}
    assert all(cell["row"] == "classifier/optimizer-certificate" for cell in c2)
    assert all(all(record["row_present"] for record in cell["records"]) for cell in c2)


def test_c3_grid_is_sample_count_set_and_each_cell_has_finite_sample_row(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    c3 = [cell for cell in payload["cells"] if cell["axis"] == "C3"]

    assert {cell["axis_value"] for cell in c3} == {128, 256, 512, 1024, 4096}
    assert all(cell["row"] == "source/finite-sample-support" for cell in c3)
    assert all(all(record["row_present"] for record in cell["records"]) for cell in c3)


def test_c4_enabled_has_action_transition_row(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    c4 = [cell for cell in payload["cells"] if cell["axis"] == "C4"]

    assert {cell["axis_value"] for cell in c4} == {False, True}
    assert all(cell["row"] == "source/action-transition-identification" for cell in c4)
    assert all(not cell["skipped"] for cell in c4)


def test_c4_disabled_records_skipped_reason(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (False, "planning missing"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    c4 = [cell for cell in payload["cells"] if cell["axis"] == "C4"]

    assert all(cell["skipped"] for cell in c4)
    assert all(cell["skip_reason"] == "planning missing" for cell in c4)
    assert all(cell["verdict"]["verdict"] == "observed-debt-pipeline-only" for cell in c4)


def test_effect_summary_reports_baseline_cell_delta_ci_for_each_cell(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")

    for cell in payload["cells"]:
        effect = cell["effect"]
        assert effect["effect_reported"] is True
        assert effect["baseline"]["n"] == 1
        assert effect["cell"]["n"] == 1
        assert math.isfinite(effect["baseline"]["mean"])
        assert math.isfinite(effect["cell"]["mean"])
        assert "delta" in effect
        assert "delta_ci95_half_width" in effect


def test_non_significant_effect_is_pipeline_only():
    stats = {"n": 4, "mean": 0.8, "std": 0.1, "ci95_half_width": 0.2, "ci95_low": 0.6, "ci95_high": 1.0}
    effect = runner.effect_from_baseline("linear_identifiability_r2", stats, stats)
    verdict = runner.verdict_for_cell("source/dimension-match", effect, "fixture")

    assert effect.significant is False
    assert verdict.verdict == "observed-debt-pipeline-only"


def test_significant_negative_effect_can_be_observed_debt_without_global_claim():
    baseline = {"n": 10, "mean": 0.8, "std": 0.01, "ci95_half_width": 0.01, "ci95_low": 0.79, "ci95_high": 0.81}
    cell = {"n": 10, "mean": 0.4, "std": 0.01, "ci95_half_width": 0.01, "ci95_low": 0.39, "ci95_high": 0.41}
    effect = runner.effect_from_baseline("linear_identifiability_r2", baseline, cell)
    verdict = runner.verdict_for_cell("source/dimension-match", effect, "fixture")

    assert effect.significant is True
    assert effect.delta < 0.0
    assert verdict.verdict == "observed-debt"
    assert verdict.global_claim_flag is False


def test_rendered_markdown_is_pointer_only(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")
    markdown = runner.render_markdown(payload)

    assert "report_schema_id" not in markdown
    assert "report_kind" not in markdown
    assert '"records"' not in markdown
    assert '"payload"' not in markdown
    assert "$.cells" in markdown


def test_runner_does_not_read_host_env():
    source = Path(runner.__file__).read_text(encoding="utf-8")

    assert ".refactor-loop/host.env" not in source
    assert "host.env" not in source


def test_generated_envelope_records_keep_schema_id(monkeypatch):
    patch_lightweight_records(monkeypatch)
    monkeypatch.setattr(runner, "_planning_axis_available", lambda: (True, "ok"))

    payload = runner.build_payload(smoke=True, generated_at="fixture-time")

    assert payload["schema_id"] == "bedc-quality-lab:evidence-envelope"
    assert all(
        record["schema_id"] == "bedc-quality-lab:evidence-envelope"
        for cell in payload["cells"]
        for record in cell["records"]
    )

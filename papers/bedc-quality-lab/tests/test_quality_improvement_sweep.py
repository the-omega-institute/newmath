import json

from scripts import run_quality_improvement as improvement
from scripts import run_gaussian_ou_lejepa as runner
from scripts import run_quality_improvement_sweep as sweep


def record(arm, index, *, delta_q, debt_reduction, target_score_reduction):
    delta_debt = -debt_reduction
    delta_target_score = -target_score_reduction
    return {
        "arm": arm,
        "seed_index": index,
        "master_seed": 101,
        "before_seed": 200 + index,
        "after_seed": 300 + index if arm == "improvement" else 200 + index,
        "before_sample_count": 8,
        "after_sample_count": 16 if arm == "improvement" else 8,
        "before_run_id": f"{arm}-{index}-before",
        "after_run_id": f"{arm}-{index}-after",
        "before_status": "open",
        "after_status": "closed" if arm == "improvement" else "open",
        "before_score": 0.2,
        "after_score": 0.0 if arm == "improvement" else 0.2,
        "before_quality_q": 0.1,
        "after_quality_q": 0.1 + delta_q,
        "before_quality_debt": 0.9,
        "after_quality_debt": 0.9 + delta_debt,
        "before_linear_identifiability_r2": 0.91,
        "after_linear_identifiability_r2": 0.93,
        "before_approx_identifiability_proxy": 0.82,
        "after_approx_identifiability_proxy": 0.86,
        "metrics": {
            "delta_q": delta_q,
            "delta_debt": delta_debt,
            "delta_target_score": delta_target_score,
            "debt_reduction": debt_reduction,
            "target_score_reduction": target_score_reduction,
        },
    }


def synthetic_records():
    return [
        record("improvement", 0, delta_q=0.20, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 0, delta_q=0.00, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 1, delta_q=0.21, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 1, delta_q=0.00, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 2, delta_q=0.22, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 2, delta_q=0.00, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 3, delta_q=0.23, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 3, delta_q=0.00, debt_reduction=0.00, target_score_reduction=0.00),
    ]


def failing_records():
    return [
        record("improvement", 0, delta_q=0.00, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 0, delta_q=0.04, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 1, delta_q=0.01, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 1, delta_q=0.04, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 2, delta_q=0.00, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 2, delta_q=0.04, debt_reduction=0.00, target_score_reduction=0.00),
        record("improvement", 3, delta_q=0.01, debt_reduction=0.20, target_score_reduction=0.20),
        record("control", 3, delta_q=0.04, debt_reduction=0.00, target_score_reduction=0.00),
    ]


def test_child_seed_is_deterministic_and_stream_separated():
    first = [sweep._child_seed(101, index, 0) for index in range(4)]
    second = [sweep._child_seed(101, index, 0) for index in range(4)]
    alternate_stream = [sweep._child_seed(101, index, 1) for index in range(4)]

    assert first == second
    assert first != alternate_stream
    assert len(set(first)) == len(first)
    assert all(0 <= seed <= 0xFFFFFFFF for seed in first + alternate_stream)


def test_aggregate_summarizes_arms_and_significance_from_records():
    aggregate = sweep._aggregate(synthetic_records())

    assert aggregate["metrics"] == list(sweep.METRICS)
    assert aggregate["summaries"]["improvement"]["delta_q"]["n"] == 4.0
    assert aggregate["summaries"]["control"]["delta_q"]["mean"] == 0.0
    assert aggregate["summaries"]["improvement"]["delta_q"]["mean"] == 0.215
    assert aggregate["summaries"]["improvement"]["debt_reduction"]["ci95_low"] > 0.0
    assert aggregate["comparisons"]["delta_q"]["mean_difference"] == 0.215
    assert aggregate["comparisons"]["delta_q"]["separated_ci95"]
    assert aggregate["comparisons"]["debt_reduction"]["separated_ci95"]
    assert aggregate["comparisons"]["target_score_reduction"]["separated_ci95"]
    assert aggregate["significance_pass"]


def test_aggregate_fails_closed_when_required_condition_fails():
    aggregate = sweep._aggregate(failing_records())

    assert aggregate["summaries"]["improvement"]["delta_q"]["ci95_low"] <= 0.0
    assert not aggregate["comparisons"]["delta_q"]["separated_ci95"]
    assert aggregate["comparisons"]["debt_reduction"]["separated_ci95"]
    assert aggregate["comparisons"]["target_score_reduction"]["separated_ci95"]
    assert aggregate["significance_pass"] is False


def test_render_report_contains_both_arms_and_seed_rows():
    records = synthetic_records()
    report = sweep._render_report(records, sweep._aggregate(records))

    assert "# BEDC Quality Lab Quality Improvement Sweep" in report
    assert "Improvement arm after sample count" in report
    assert "Control arm after sample count" in report
    assert "Significance result: `pass`" in report
    assert "| improvement | `delta_q` |" in report
    assert "| control | `delta_q` |" in report
    assert "| `debt_reduction` |" in report
    assert "| 0 | 200 | 300 | 200 | +0.200000 | +0.000000 | +0.200000 | +0.000000 |" in report


def test_render_report_marks_failed_significance():
    records = failing_records()
    report = sweep._render_report(records, sweep._aggregate(records))

    assert "Significance result: `fail`" in report
    assert "| `delta_q` | +0.005000 | +0.040000 | -0.035000 | no |" in report


def test_main_writes_json_and_report_payload_shape(monkeypatch, tmp_path):
    monkeypatch.setattr(sweep, "ROOT", tmp_path)
    monkeypatch.setattr(sweep, "_records", synthetic_records)

    sweep.main()

    payload = json.loads((tmp_path / sweep.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / sweep.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == sweep.JSON_ARTIFACT
    assert payload["report"] == sweep.REPORT_ARTIFACT
    assert len(payload["records"]) == 8
    assert payload["aggregate"]["significance_pass"]
    assert payload["aggregate"]["comparisons"]["target_score_reduction"]["separated_ci95"]
    assert "## Arm Comparison" in report
    assert "## Seed Distribution" in report


def test_main_writes_failed_significance_payload(monkeypatch, tmp_path):
    monkeypatch.setattr(sweep, "ROOT", tmp_path)
    monkeypatch.setattr(sweep, "_records", failing_records)

    sweep.main()

    payload = json.loads((tmp_path / sweep.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / sweep.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["aggregate"]["significance_pass"] is False
    assert payload["aggregate"]["comparisons"]["delta_q"]["separated_ci95"] is False
    assert "Significance result: `fail`" in report


def test_canonical_gaussian_ou_producer_and_delta_are_shared_api():
    before = runner.run_experiment(
        use_torch=False,
        sample_count=32,
        seed=7,
        run_id="quality-improvement-test-before",
        envelope_artifact="reports/test_before_envelope.json",
        report_artifact=sweep.REPORT_ARTIFACT,
    )
    after = runner.run_experiment(
        use_torch=False,
        sample_count=96,
        seed=7,
        run_id="quality-improvement-test-after",
        envelope_artifact="reports/test_after_envelope.json",
        report_artifact=sweep.REPORT_ARTIFACT,
    )
    delta = improvement.quality_delta(before, after)

    assert before.run_id == "quality-improvement-test-before"
    assert after.run_id == "quality-improvement-test-after"
    assert before.source_spec["sample_count"] == 32
    assert after.source_spec["sample_count"] == 96
    assert delta["target_residue"] == "finite-sample-support"
    assert set(delta) == {
        "target_residue",
        "before_status",
        "after_status",
        "before_score",
        "after_score",
        "delta_target_score",
        "delta_q",
        "delta_debt",
    }

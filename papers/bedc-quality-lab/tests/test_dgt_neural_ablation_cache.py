import json
from pathlib import Path

import pytest

from bedc_quality_lab import dgt_neural_ablation as owner
from bedc_quality_lab.canonical_cell_cache import cell_input_digest, load_cell_entry, store_cell_entry


def _fixture_row(*, arm, seed, train_steps, task_id, generation):
    arm_index = owner.ARM_IDS.index(arm.arm_id)
    task_bonus = 0.01 if task_id == "scope_boundary_pressure" else 0.0
    generation_bonus = generation * 0.001
    scope_metrics = {
        "scope_pressure_accuracy": 0.68 + task_bonus + generation_bonus,
        "scope_refusal_precision": 0.64 + task_bonus,
        "scope_refusal_recall": 0.63 + task_bonus,
        "over_claim_false_positive_rate": 0.05,
        "scope_leak_rate": 0.04,
        "boundary_margin": 0.42,
        "scope_gate_sensitivity": 0.22,
        "slice_metrics": {
            scope_slice: {
                "accuracy": 0.66 + task_bonus + generation_bonus,
                "count": 4,
            }
            for scope_slice in owner.SCOPE_SLICES
        },
    }
    if arm.arm_id == "DGT_without_scope_seal":
        scope_metrics = {
            **scope_metrics,
            "scope_pressure_accuracy": scope_metrics["scope_pressure_accuracy"] - 0.03,
            "scope_leak_rate": scope_metrics["scope_leak_rate"] + 0.03,
            "boundary_margin": scope_metrics["boundary_margin"] - 0.08,
            "scope_gate_sensitivity": scope_metrics["scope_gate_sensitivity"] - 0.06,
            "slice_metrics": {
                scope_slice: {**row, "accuracy": row["accuracy"] - 0.04}
                for scope_slice, row in scope_metrics["slice_metrics"].items()
            },
        }
    outcome = owner.TrainingOutcome(
        arm_id=arm.arm_id,
        seed=seed,
        train_steps=train_steps,
        task_id=task_id,
        split="eval",
        initial_loss=1.0 + arm_index * 0.01,
        final_loss=0.58 + arm_index * 0.005 - generation_bonus,
        loss_drop=0.42 + generation_bonus,
        accuracy=0.70 + task_bonus + generation_bonus,
        balanced_accuracy=0.69 + task_bonus + generation_bonus,
        margin_mean=0.31,
        margin_p05=0.19,
        ece=0.06,
        prediction_entropy=0.72,
        parameter_delta_l2=0.10 + arm_index * 0.001 + generation_bonus,
        gradient_update_steps=train_steps,
        prediction_distribution={"accept": 0.54, "refuse": 0.18, "revise": 0.16, "defer": 0.12},
        scope_pressure_metrics=scope_metrics,
        UER=0.07,
        FalseLedgerRate=0.03,
        JetCoverage=0.71,
        negative_witness_hits=0,
        compute_cost=0.01,
    )
    derived = owner.derive_training_metrics(outcome, owner.METRIC_PROTOCOL)
    return {
        **outcome.__dict__,
        "disabled_component": arm.disabled_component,
        "requested_training_backend": "torch",
        "requested_device": "cpu",
        "resolved_device": "cpu",
        "device": "cpu",
        "optimizer": "Adam",
        "optimizer_steps": train_steps,
        "compute_units": owner._compute_units(train_steps=train_steps, feature_dim=owner.INPUT_DIM),
        "parameter_count": 128 + arm_index,
        "wall_time_proxy": round(train_steps * (128 + arm_index) / 1000000.0, 6),
        "metric_protocol_id": owner.SCHEMA_ID + ":metric-protocol",
        "metrics": derived["metrics"],
        "metric_diagnostics": derived["metric_diagnostics"],
        "sample_schema": {
            "input_tokens": "float tensor",
            "target_label": "class index",
            "scope_class": list(owner.SCOPE_CLASSES),
            "claim_allowed": "bool",
            "expected_boundary_action": "string",
            "negative_witness_tag": "string",
        },
    }


def _fixture_records(run_spec, *, generation):
    rows = []
    for train_steps in run_spec.step_grid:
        for seed in run_spec.seed_list:
            for arm in owner.arm_registry():
                for task_id in owner.TASK_IDS:
                    rows.append(
                        _fixture_row(
                            arm=arm,
                            seed=seed,
                            train_steps=train_steps,
                            task_id=task_id,
                            generation=generation,
                        )
                    )
    return rows


@pytest.fixture
def cache_harness(tmp_path, monkeypatch):
    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", (tmp_path / "cache").as_posix())
    events = []
    generation = {"value": 0}

    def train_grid(torch, *, run_spec, device_name):
        generation["value"] += 1
        return _fixture_records(run_spec, generation=generation["value"])

    previous_observer = owner.CELL_CACHE_EVENT_OBSERVER
    owner.CELL_CACHE_EVENT_OBSERVER = events.append
    monkeypatch.setattr(owner, "_train_grid", train_grid)
    monkeypatch.setattr(owner, "_callable_digest", lambda function: "fixture-trainer-digest")
    try:
        yield {"events": events, "generation": generation, "root": tmp_path}
    finally:
        owner.CELL_CACHE_EVENT_OBSERVER = previous_observer


def _quick_spec(**overrides):
    values = {
        "step_grid": (8,),
        "seed_count": 2,
        "seed_list": owner.DEFAULT_SEEDS[:2],
        "requested_device": "cpu",
        "paired_ci_min_seeds": 2,
    }
    values.update(overrides)
    return owner.DgtNeuralAblationRunSpec(**values)


def _record(run_spec):
    torch = __import__("torch")
    return owner._cell_input_record(torch, requested_device="cpu", device_name="cpu", run_spec=run_spec)


def _cached_raw_blob_path(run_spec):
    record = _record(run_spec)
    lookup = load_cell_entry(record)
    assert lookup.status == "hit"
    return lookup.verified_blob_paths["raw_metrics.jsonl"]


def test_neural_ablation_cache_hit_skips_training(cache_harness, monkeypatch):
    run_spec = _quick_spec()
    first = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)

    def fail_train_grid(torch, *, run_spec, device_name):
        raise AssertionError("cache hit must not train")

    def fail_train_arm_seed(*args, **kwargs):
        raise AssertionError("cache hit must not train an arm seed")

    monkeypatch.setattr(owner, "_train_grid", fail_train_grid)
    monkeypatch.setattr(owner, "_train_arm_seed", fail_train_arm_seed)
    second = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)

    assert first["records"] == second["records"]
    assert cache_harness["generation"]["value"] == 1
    assert any(event["event"] == "cache-return" and event["status"] == "hit" for event in cache_harness["events"])


def test_corrupt_raw_object_blob_forces_retrain(cache_harness):
    run_spec = _quick_spec()
    first = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)
    raw_path = _cached_raw_blob_path(run_spec)
    bad_rows = [json.loads(line) for line in raw_path.read_text(encoding="utf-8").splitlines()]
    bad_rows[0] = ["not", "an", "object"]
    bad_source = cache_harness["root"] / "bad_raw_metrics.jsonl"
    bad_source.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in bad_rows), encoding="utf-8")
    store_cell_entry(_record(run_spec), {"raw_metrics.jsonl": {"path": bad_source, "media_role": "raw_metrics_jsonl"}})

    second = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)

    assert second["training_protocol"]["status"] != "unavailable"
    assert cache_harness["generation"]["value"] == 2
    assert first["records"] != second["records"]
    assert any(event["event"] == "cache-rejected" and event["status"] == "corrupt" for event in cache_harness["events"])


def test_non_seed_input_changes_miss_and_change_cell_input_digest(cache_harness):
    base = _quick_spec(paired_ci_min_seeds=2)
    changed = _quick_spec(paired_ci_min_seeds=3, seed_count=3, seed_list=owner.DEFAULT_SEEDS[:3])

    base_digest = cell_input_digest(_record(base))
    changed_digest = cell_input_digest(_record(changed))
    assert base_digest != changed_digest

    owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=base)
    event_count = len(cache_harness["events"])
    owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=changed)
    changed_events = cache_harness["events"][event_count:]

    assert cache_harness["generation"]["value"] == 2
    assert any(event["event"] == "lookup" and event["status"] == "miss" for event in changed_events)
    assert not any(event["event"] == "cache-return" and event["status"] == "hit" for event in changed_events)


def test_cache_hit_overwrites_stale_derived_report_from_records(cache_harness, monkeypatch):
    run_spec = _quick_spec()
    first = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)
    output_root = Path(cache_harness["root"]) / "out"
    owner.write_artifacts(first, root=output_root, generated_at="fixture")
    stale_summary = output_root / first["run_artifacts"]["summary"]
    stale_summary.write_text('{"stale": true}\n', encoding="utf-8")
    stale_report = output_root / first["run_artifacts"]["report"]
    stale_report.write_text("stale report\n", encoding="utf-8")

    def fail_train_grid(torch, *, run_spec, device_name):
        raise AssertionError("cache hit must derive artifacts from records without training")

    monkeypatch.setattr(owner, "_train_grid", fail_train_grid)
    second = owner.build_payload(generated_at="fixture", requested_device="cpu", run_spec=run_spec)
    owner.write_artifacts(second, root=output_root, generated_at="fixture")

    summary = json.loads(stale_summary.read_text(encoding="utf-8"))
    report_text = stale_report.read_text(encoding="utf-8")
    assert summary["records"] == first["records"]
    assert summary.get("stale") is None
    assert report_text.startswith("# DGT neural ablation")
    assert "stale report" not in report_text

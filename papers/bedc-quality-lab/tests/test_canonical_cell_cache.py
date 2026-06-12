import json
from pathlib import Path

import pytest

from bedc_quality_lab.canonical_cell_cache import (
    CELL_CACHE_INPUT_SCHEMA_ID,
    CELL_CACHE_KEY_ALGORITHM_ID,
    CellInputRecord,
    canonical_digest,
    cell_input_digest,
    default_cache_root,
    load_cell_entry,
    materialize_cell_entry,
    store_cell_entry,
    verify_cell_manifest,
)


def _record(**overrides):
    fields = {
        "producer_id": "fixture-producer",
        "producer_command": ("python3", "scripts/run_fixture.py"),
        "report_artifacts": {
            "canonical_json": "reports/canonical/fixture.json",
            "raw_metrics": "reports/runs/fixture/raw_metrics.jsonl",
        },
        "producer_source_closure": (
            {"path": "scripts/run_fixture.py", "sha256": "a" * 64},
            {"path": "bedc_quality_lab/fixture.py", "sha256": "b" * 64},
        ),
        "extra_input_paths": ("reports/canonical/upstream.json",),
        "config_payload": {"steps": 4, "arms": ["candidate", "control"]},
        "seed_protocol": {"seeds": [1, 2]},
        "source_artifact_digests": {"reports/canonical/upstream.json": "c" * 64},
        "requested_device": "cpu",
        "resolved_device": "cpu",
        "runtime_abi": {"python": "3.12", "numpy": "2.0", "torch": "2.5"},
    }
    fields.update(overrides)
    return CellInputRecord(**fields)


def test_canonical_digest_is_order_stable():
    left = {"b": [2, {"z": 1, "a": 3}], "a": {"k": "v"}}
    right = {"a": {"k": "v"}, "b": [2, {"a": 3, "z": 1}]}

    assert canonical_digest(left) == canonical_digest(right)
    assert canonical_digest(left) != canonical_digest({"a": {"k": "changed"}, "b": [2]})


def test_cell_input_digest_changes_with_source_closure():
    base = _record()
    changed = _record(
        producer_source_closure=(
            {"path": "scripts/run_fixture.py", "sha256": "d" * 64},
            {"path": "bedc_quality_lab/fixture.py", "sha256": "b" * 64},
        )
    )

    assert base.schema_id == CELL_CACHE_INPUT_SCHEMA_ID
    assert base.key_algorithm_id == CELL_CACHE_KEY_ALGORITHM_ID
    assert cell_input_digest(base) == cell_input_digest(_record())
    assert cell_input_digest(base) != cell_input_digest(changed)


def test_default_cache_root_prefers_env_and_rejects_refactor_loop(monkeypatch, tmp_path):
    explicit = tmp_path / "cache"
    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", str(explicit))
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "xdg"))

    assert default_cache_root() == explicit

    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", str(tmp_path / ".refactor-loop" / "cells"))
    with pytest.raises(ValueError, match="refactor-loop"):
        default_cache_root()

    monkeypatch.delenv("BEDC_QUALITY_LAB_CACHE_DIR")
    assert default_cache_root() == tmp_path / "xdg" / "bedc-quality-lab" / "canonical-cells"


def test_cache_hit_miss_corrupt_and_blob_round_trip(tmp_path):
    record = _record()
    cache_root = tmp_path / "cache"
    source = tmp_path / "raw_metrics.jsonl"
    source.write_text('{"metric":1}\n', encoding="utf-8")

    miss = load_cell_entry(record, cache_root=cache_root)
    assert miss.status == "miss"
    assert miss.reason == "manifest-missing"

    manifest = store_cell_entry(
        record,
        {"raw_metrics.jsonl": {"path": source, "media_role": "raw_metrics_jsonl"}},
        cache_root=cache_root,
    )
    assert manifest.cell_input_digest == cell_input_digest(record)

    hit = load_cell_entry(record, cache_root=cache_root)
    assert hit.status == "hit"
    assert set(hit.verified_blob_paths) == {"raw_metrics.jsonl"}

    out = materialize_cell_entry(hit, tmp_path / "materialized")
    assert out["raw_metrics.jsonl"].read_text(encoding="utf-8") == '{"metric":1}\n'

    blob_path = next(iter(hit.verified_blob_paths.values()))
    blob_path.write_text("tampered\n", encoding="utf-8")
    corrupt = load_cell_entry(record, cache_root=cache_root)
    assert corrupt.status == "corrupt"
    assert "digest mismatch" in corrupt.reason


def test_verify_manifest_fail_closed_on_manifest_tamper(tmp_path):
    record = _record()
    source = tmp_path / "raw_metrics.jsonl"
    source.write_text('{"metric":1}\n', encoding="utf-8")
    manifest = store_cell_entry(record, {"raw_metrics.jsonl": source}, cache_root=tmp_path / "cache")
    manifest_path = tmp_path / "cache" / record.producer_id / manifest.cell_input_digest / "manifest.json"
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    payload["cell_input_digest"] = "0" * 64
    manifest_path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    lookup = verify_cell_manifest(record, manifest_path)

    assert lookup.status == "corrupt"
    assert "input digest mismatch" in lookup.reason


def test_verify_manifest_fail_closed_on_manifest_digest_inputs_tamper(tmp_path):
    record = _record()
    source = tmp_path / "raw_metrics.jsonl"
    source.write_text('{"metric":1}\n', encoding="utf-8")
    manifest = store_cell_entry(record, {"raw_metrics.jsonl": source}, cache_root=tmp_path / "cache")
    manifest_path = tmp_path / "cache" / record.producer_id / manifest.cell_input_digest / "manifest.json"
    payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    payload["manifest_digest_inputs"]["producer_id"] = "forged-producer"
    payload["manifest_digest_inputs"]["cell_input_digest"] = "0" * 64
    payload["manifest_digest_inputs"]["blobs"] = []
    manifest_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lookup = verify_cell_manifest(record, manifest_path)

    assert lookup.status == "corrupt"
    assert "digest inputs mismatch" in lookup.reason


def test_dgt_l0_training_cell_cache_reuses_raw_records(tmp_path, monkeypatch):
    from bedc_quality_lab import dgt_l0_controls as l0

    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", str(tmp_path / "cells"))
    first = l0.build_payload(generated_at="fixture", requested_device="cpu")
    expected_records = first["_raw_records"]
    trainer_digest = l0._callable_digest(l0._train_arm)

    def fail_train(*_args, **_kwargs):
        raise AssertionError("cache hit should avoid training")

    monkeypatch.setattr(l0, "_train_arm", fail_train)
    monkeypatch.setattr(l0, "_callable_digest", lambda _function: trainer_digest)
    second = l0.build_payload(generated_at="fixture", requested_device="cpu")

    assert second["_raw_records"] == expected_records
    assert second["l0_toy_projection"]["review_status"] == first["l0_toy_projection"]["review_status"]


def test_dgt_l1_training_cell_cache_reuses_raw_records(tmp_path, monkeypatch):
    from bedc_quality_lab import dgt_l1_controls as l1

    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", str(tmp_path / "cells"))
    config = l1.L1TrainingConfig(
        seeds=(1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189),
        training_steps=8,
        step_grid=(8, 16),
        train_examples=32,
        eval_examples=64,
    )
    first = l1.build_payload(generated_at="fixture", requested_device="cpu", config=config)
    expected_records = first["_raw_records"]

    def fail_grid(*_args, **_kwargs):
        raise AssertionError("cache hit should avoid training")

    monkeypatch.setattr(l1, "_train_l1_grid", fail_grid)
    second = l1.build_payload(generated_at="fixture", requested_device="cpu", config=config)

    assert second["_raw_records"] == expected_records
    assert second["review_status"] == "pass"


def test_cell_cache_hit_does_not_satisfy_report_fingerprint_verify(tmp_path, monkeypatch):
    from bedc_quality_lab import dgt_l0_controls as l0
    from scripts import run_canonical_reports as canonical

    monkeypatch.setenv("BEDC_QUALITY_LAB_CACHE_DIR", str(tmp_path / "cells"))
    first = l0.build_payload(generated_at="fixture", requested_device="cpu")
    trainer_digest = l0._callable_digest(l0._train_arm)

    def fail_train(*_args, **_kwargs):
        raise AssertionError("cache hit should avoid training")

    monkeypatch.setattr(l0, "_train_arm", fail_train)
    monkeypatch.setattr(l0, "_callable_digest", lambda _function: trainer_digest)
    payload = l0.build_payload(generated_at="fixture", requested_device="cpu")
    assert payload["_raw_records"] == first["_raw_records"]
    l0.write_artifacts(payload, root=tmp_path, generated_at="fixture")

    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["dgt-l0-controls"]

    result = canonical._run_spec(spec, mode="verify")

    assert result["status"] == "error"
    assert "missing fingerprint sidecar" in result["error"]

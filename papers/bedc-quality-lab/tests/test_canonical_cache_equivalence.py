import json
from pathlib import Path

import pytest

from bedc_quality_lab import canonical_cache_equivalence as cce


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_surface_manifest_uses_sha256_and_multi_file_digest(tmp_path):
    root = tmp_path
    _write(root / "a.json", '{"x":1}\n')
    _write(root / "b.jsonl", '{"row":1}\n')
    _write(root / "c.jsonl", '{"row":2}\n')

    single = cce.surface_manifest(root, cce.SurfaceSpec("json", "single", ("a.json",)))
    multi = cce.surface_manifest(root, cce.SurfaceSpec("raw", "multi", ("b.jsonl", "c.jsonl")))
    changed = cce.surface_manifest(root, cce.SurfaceSpec("raw", "multi", ("c.jsonl", "b.jsonl")))

    assert single["algorithm"] == "sha256"
    assert len(single["files"][0]["sha256"]) == 64
    assert multi["algorithm"] == "sha256"
    assert len(multi["sha256"]) == 64
    assert multi["sha256"] != changed["sha256"]


def test_cache_root_policy_rejects_refactor_loop(tmp_path):
    assert cce.cache_root_policy(tmp_path / "cache")["status"] == "pass"
    rejected = cce.cache_root_policy(tmp_path / ".refactor-loop" / "cache")

    assert rejected["status"] == "fail"
    assert rejected["hardgate_id"] == "CACHE-HG3"


def test_hardgate_fold_fails_on_surface_mismatch_and_missing_hit():
    target = cce.CACHE_BACKED_TARGETS[0]
    cold = {
        "canonical_json": {"status": "present", "algorithm": "sha256", "sha256": "a" * 64},
        "raw_metrics": {"status": "present", "algorithm": "sha256", "sha256": "b" * 64},
        "summary": {"status": "present", "algorithm": "sha256", "sha256": "c" * 64},
        "fingerprint": {"status": "present", "algorithm": "sha256", "sha256": "d" * 64},
    }
    cached = dict(cold)
    cached["raw_metrics"] = {"status": "present", "algorithm": "sha256", "sha256": "e" * 64}

    row = cce.fold_target_row(
        target,
        cold_result={"status": "pass"},
        cache_result={"status": "pass"},
        cold_surfaces=cold,
        cache_surfaces=cached,
        events=[],
    )

    assert row["status"] == "fail"
    assert "surface mismatch: raw_metrics" in row["failure_reasons"]
    assert "cache leg did not observe a producer cache hit" in row["failure_reasons"]


def test_owner_schema_rejects_unsupported_pass():
    payload = cce.build_owner_payload(
        generated_at="fixture",
        target_rows=[
            {
                "target_id": "not-cache-backed",
                "status": "pass",
                "cache_backed": False,
                "surfaces": {},
                "cache_observation": {"cache_hit_observed": False, "events": []},
                "failure_reasons": [],
            }
        ],
        policy={"status": "pass"},
        cache_root_source="temporary",
        selected_targets=["not-cache-backed"],
    )

    with pytest.raises(ValueError, match="unsupported target cannot pass"):
        cce.validate_owner_payload(payload)


def test_run_equivalence_audit_recomputes_and_detects_cache_hit(tmp_path):
    target = cce.CACHE_BACKED_TARGETS[0]
    root = tmp_path

    def run_target(target_row, leg, _generated_at, _cache_root, events):
        _write(root / target_row.json_artifact, '{"owner":1}\n')
        _write(root / target_row.fingerprint_artifact, '{"fingerprint":1}\n')
        _write(root / target_row.summary_artifact, '{"summary":1}\n')
        _write(root / target_row.raw_artifacts[0], '{"raw":1}\n')
        if leg == "cache":
            events.append({"leg": "cache", "event": "cache-return", "status": "hit"})
        return {"status": "pass", "producer_status": "completed", "fingerprint_status": "match"}

    payload = cce.run_equivalence_audit(
        root=root,
        generated_at="fixture",
        targets=(target,),
        cache_root=tmp_path / "cache",
        cache_root_source="temporary",
        run_target=run_target,
    )

    assert payload["status"] == "pass"
    assert payload["hardgates"]["CACHE-HG1"]["status"] == "pass"
    assert payload["hardgates"]["CACHE-HG2"]["status"] == "pass"
    assert payload["targets"][0]["cache_observation"]["cache_hit_observed"] is True


def test_unsupported_target_fails_closed(tmp_path):
    payload = cce.run_equivalence_audit(
        root=tmp_path,
        generated_at="fixture",
        targets=(),
        unsupported_targets=("plain-target",),
        cache_root=tmp_path / "cache",
        cache_root_source="temporary",
        run_target=lambda *_args: {},
    )

    assert payload["status"] == "fail"
    assert payload["targets"][0]["status"] == "unsupported"
    assert payload["summary"]["pass_count"] == 0

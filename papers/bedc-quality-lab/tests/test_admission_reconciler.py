from __future__ import annotations

import json
from pathlib import Path

import pytest

from bedc_quality_lab.admission_reconciler import (
    AdmissionReconciliationError,
    audit_admission_ledger,
    reconcile_admission_artifact,
)


def _write_json(path: Path, payload: object) -> bytes:
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    path.write_text(raw, encoding="utf-8")
    return raw.encode("utf-8")


def _artifact(root: Path, rel_path: str, artifact_id: str, status: str = "accepted", **extra: object) -> Path:
    path = root / rel_path
    payload = {
        "schema_id": "fixture:admission-artifact",
        "artifact_id": artifact_id,
        "artifact_path": rel_path,
        "admission_status": status,
        **extra,
    }
    _write_json(path, payload)
    return path


def _load_json(root: Path, rel_path: str) -> dict[str, object]:
    return json.loads((root / rel_path).read_text(encoding="utf-8"))


def _ledger_rows(root: Path) -> list[dict[str, object]]:
    path = root / "reports/canonical/admission_ledger.jsonl"
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def test_reconcile_writes_deterministically_sorted_manifest_and_hash_maps(tmp_path: Path) -> None:
    second = _artifact(tmp_path, "reports/admissions/z.json", "bedc-quality-lab:zeta-admission")
    first = _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:alpha-admission")

    reconcile_admission_artifact(second, root=tmp_path)
    reconcile_admission_artifact(first, root=tmp_path)

    manifest = _load_json(tmp_path, "reports/canonical/admission_manifest.json")
    hashes = _load_json(tmp_path, "reports/canonical/admission_artifact_hashes.json")

    assert [entry["artifact_id"] for entry in manifest["entries"]] == [
        "bedc-quality-lab:alpha-admission",
        "bedc-quality-lab:zeta-admission",
    ]
    assert list(hashes["artifact_hashes"]) == [
        "bedc-quality-lab:alpha-admission",
        "bedc-quality-lab:zeta-admission",
    ]
    assert list(hashes["path_hashes"]) == [
        "reports/admissions/a.json",
        "reports/admissions/z.json",
    ]


def test_same_hash_idempotence_does_not_append_ledger_or_rewrite_sidecars(tmp_path: Path) -> None:
    artifact = _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:stable-admission")
    reconcile_admission_artifact(artifact, root=tmp_path)
    sidecar_paths = sorted((tmp_path / "reports/canonical").iterdir())
    before = {path.name: path.read_bytes() for path in sidecar_paths}

    result = reconcile_admission_artifact(artifact, root=tmp_path)
    after = {path.name: path.read_bytes() for path in sidecar_paths}

    assert result.status == "unchanged"
    assert len(_ledger_rows(tmp_path)) == 1
    assert after == before


def test_same_artifact_id_with_different_hash_writes_conflict_without_manifest_change(tmp_path: Path) -> None:
    artifact = _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:conflict-admission", claim="one")
    reconcile_admission_artifact(artifact, root=tmp_path)
    before_manifest = (tmp_path / "reports/canonical/admission_manifest.json").read_bytes()
    before_ledger = (tmp_path / "reports/canonical/admission_ledger.jsonl").read_bytes()
    _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:conflict-admission", claim="two")

    result = reconcile_admission_artifact(artifact, root=tmp_path)
    conflicts = _load_json(tmp_path, "reports/canonical/admission_conflicts.json")

    assert result.status == "conflict"
    assert conflicts["status"] == "conflict"
    assert conflicts["conflicts"][0]["kind"] == "artifact_id_hash_mismatch"
    assert (tmp_path / "reports/canonical/admission_manifest.json").read_bytes() == before_manifest
    assert (tmp_path / "reports/canonical/admission_ledger.jsonl").read_bytes() == before_ledger


def test_artifact_path_reuse_writes_conflict_without_ledger_append(tmp_path: Path) -> None:
    artifact = _artifact(tmp_path, "reports/admissions/shared.json", "bedc-quality-lab:first-admission")
    reconcile_admission_artifact(artifact, root=tmp_path)
    _artifact(tmp_path, "reports/admissions/shared.json", "bedc-quality-lab:second-admission")

    result = reconcile_admission_artifact(artifact, root=tmp_path)
    conflicts = _load_json(tmp_path, "reports/canonical/admission_conflicts.json")

    assert result.status == "conflict"
    assert conflicts["conflicts"][0]["kind"] == "artifact_path_reuse"
    assert len(_ledger_rows(tmp_path)) == 1


def test_malformed_artifact_fails_closed_without_sidecar_writes(tmp_path: Path) -> None:
    malformed = tmp_path / "reports/admissions/malformed.json"
    _write_json(
        malformed,
        {
            "schema_id": "fixture:admission-artifact",
            "artifact_path": "reports/admissions/malformed.json",
            "admission_status": "accepted",
        },
    )

    with pytest.raises(AdmissionReconciliationError, match="artifact_id"):
        reconcile_admission_artifact(malformed, root=tmp_path)

    assert not (tmp_path / "reports/canonical/admission_manifest.json").exists()
    assert not (tmp_path / "reports/canonical/admission_ledger.jsonl").exists()


def test_bounded_negative_artifact_appends_a_content_addressed_ledger_row(tmp_path: Path) -> None:
    artifact = _artifact(
        tmp_path,
        "reports/admissions/bounded.json",
        "bedc-quality-lab:bounded-negative-admission",
        status="bounded_negative",
    )

    reconcile_admission_artifact(artifact, root=tmp_path)
    rows = _ledger_rows(tmp_path)

    assert len(rows) == 1
    assert rows[0]["admission_status"] == "bounded_negative"
    assert rows[0]["artifact_id"] == "bedc-quality-lab:bounded-negative-admission"
    assert isinstance(rows[0]["row_sha256"], str)


def test_tamper_and_reorder_ledger_audit_rejects(tmp_path: Path) -> None:
    first = _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:a-admission")
    second = _artifact(tmp_path, "reports/admissions/b.json", "bedc-quality-lab:b-admission")
    reconcile_admission_artifact(first, root=tmp_path)
    reconcile_admission_artifact(second, root=tmp_path)
    ledger_path = tmp_path / "reports/canonical/admission_ledger.jsonl"
    original_lines = ledger_path.read_text(encoding="utf-8").splitlines()

    ledger_path.write_text("\n".join(reversed(original_lines)) + "\n", encoding="utf-8")
    with pytest.raises(AdmissionReconciliationError, match="ledger"):
        audit_admission_ledger(tmp_path)

    tampered = [json.loads(line) for line in original_lines]
    tampered[0]["artifact_sha256"] = "0" * 64
    ledger_path.write_text("\n".join(json.dumps(row, sort_keys=True) for row in tampered) + "\n", encoding="utf-8")
    with pytest.raises(AdmissionReconciliationError, match="ledger"):
        audit_admission_ledger(tmp_path)


def test_reconcile_preserves_existing_canonical_index_and_fingerprint_bytes(tmp_path: Path) -> None:
    index_bytes = _write_json(
        tmp_path / "reports/canonical/index.json",
        {"schema_id": "bedc-quality-lab:canonical-report-index", "reports": []},
    )
    fingerprint_bytes = _write_json(
        tmp_path / "reports/canonical/toy.fingerprint.json",
        {"schema_id": "bedc-quality-lab:canonical-report-fingerprint", "sha256": "abc"},
    )
    artifact = _artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:a-admission")

    reconcile_admission_artifact(artifact, root=tmp_path)

    assert (tmp_path / "reports/canonical/index.json").read_bytes() == index_bytes
    assert (tmp_path / "reports/canonical/toy.fingerprint.json").read_bytes() == fingerprint_bytes

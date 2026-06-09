import json
from pathlib import Path

import pytest

from bedc_quality_lab import release_namecert_candidate as candidate
from scripts import release_manifest_sidecar as sidecar
from scripts import run_canonical_reports as canonical
from scripts import run_release_namecert_candidate as runner


GENERATED_AT = "2030-01-01T00:00:00+00:00"


def _write_fixture_root(root: Path) -> None:
    (root / "reports" / "canonical").mkdir(parents=True, exist_ok=True)
    (root / "docs" / "lit").mkdir(parents=True, exist_ok=True)
    (root / "reports" / "canonical" / "index.json").write_text(
        json.dumps({"schema_id": canonical.INDEX_SCHEMA_ID, "reports": [{"status": "pass"}]}) + "\n",
        encoding="utf-8",
    )
    (root / "reports" / "canonical" / "index.md").write_text(
        "# Canonical Report Index\n\n## Fixture\n",
        encoding="utf-8",
    )
    (root / "docs" / "artifact_manifest.md").write_text(
        "# Artifact Manifest\n\n"
        "## Quality Baseline Surfaces\n\n"
        "| artifact id | path | discovery_level pointer | pointer status |\n"
        "| --- | --- | --- | --- |\n"
        "| `bedc-quality-lab:artifact-manifest` | `docs/artifact_manifest.md` | "
        "`## Quality Baseline Surfaces` | pointer-only |\n",
        encoding="utf-8",
    )
    (root / "docs" / "lit" / "literature_ledger.yaml").write_text(
        json.dumps({"records": [{"id": "lit-artifact-release-navigation"}]}) + "\n",
        encoding="utf-8",
    )
    (root / "VERSION").write_text("0.0.1\n", encoding="utf-8")


def _write_sidecar(root: Path, payload: dict | None = None) -> dict:
    if payload is None:
        written = sidecar.write_release_manifest_sidecar(root, generated_at=GENERATED_AT)
        return written.to_payload()
    path = root / sidecar.JSON_ARTIFACT
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _candidate_payload(root: Path) -> dict:
    _write_fixture_root(root)
    _write_sidecar(root)
    return runner.write_release_namecert_candidate(
        root=root,
        generated_at=GENERATED_AT,
        make_check_passed=True,
    )


def test_sidecar_derived_projection_is_pointer_only_and_audit_clean(tmp_path):
    payload = _candidate_payload(tmp_path)
    audit = candidate.audit_release_namecert_candidate(payload)
    source_spec = payload["source_spec"]
    classifier_spec = payload["classifier_spec"]

    assert audit["status"] == "pass"
    assert payload["schema_id"] == candidate.SCHEMA_ID
    assert payload["artifact_id"] == candidate.ARTIFACT_ID
    assert payload["release_id"] == {
        "identity": "bedc-quality-lab:release-manifest-sidecar@0.0.1:non-publishable",
        "source_artifact_id": "bedc-quality-lab:release-manifest-sidecar",
        "source_version": "0.0.1",
        "tag_status_pointer": "$.source_spec.tag_status",
        "publishable": False,
        "tag_claim": "none",
        "tag_absent": True,
    }
    assert source_spec["sidecar_path"] == sidecar.JSON_ARTIFACT
    assert source_spec["sidecar_schema_id"] == sidecar.SCHEMA_ID
    assert source_spec["sidecar_artifact_id"] == sidecar.ARTIFACT_ID
    assert len(source_spec["sidecar_digest"]) == 64
    assert source_spec["release_bundle_status"] == "ready"
    assert source_spec["tag_status"] == "absent"
    assert source_spec["required_pointer_count"] == 6
    assert source_spec["resolved_pointer_count"] == 6
    assert source_spec["sidecar_cell_pointers"]["required_pointer_rows"] == "$.required_pointers"
    assert classifier_spec["classifier"] == "release-ready vs not"
    assert classifier_spec["release_manifest_ready"] is True
    assert classifier_spec["publishable_tag_claim"] is False
    assert classifier_spec["scientific_claim"] is False
    assert classifier_spec["model_quality_proof"] is False
    assert classifier_spec["bedc_theory_closure"] is False
    assert classifier_spec["release_closure"] == "candidate-only"
    assert payload["revoke_if"] == payload["ledger_policy"]["revoke_if"]


@pytest.mark.parametrize(
    ("label", "mutate", "message"),
    [
        (
            "malformed",
            lambda root: (root / sidecar.JSON_ARTIFACT).write_text("{not-json}\n", encoding="utf-8"),
            "malformed release manifest sidecar",
        ),
        (
            "schema",
            lambda root: _write_sidecar(root, {**json.loads((root / sidecar.JSON_ARTIFACT).read_text()), "schema_id": "wrong"}),
            "schema mismatch",
        ),
        (
            "unresolved",
            lambda root: _write_sidecar(
                root,
                {
                    **json.loads((root / sidecar.JSON_ARTIFACT).read_text()),
                    "required_pointers": [
                        {
                            **json.loads((root / sidecar.JSON_ARTIFACT).read_text())["required_pointers"][0],
                            "status": "missing",
                        }
                    ],
                },
            ),
            "unresolved required pointers",
        ),
        (
            "missing-revoke",
            lambda root: _write_sidecar(
                root,
                {
                    key: value
                    for key, value in json.loads((root / sidecar.JSON_ARTIFACT).read_text()).items()
                    if key != "revoke_if"
                },
            ),
            "lacks revoke_if",
        ),
    ],
)
def test_runner_fails_closed_for_invalid_sidecar(tmp_path, label, mutate, message):
    _write_fixture_root(tmp_path)
    if label != "malformed":
        _write_sidecar(tmp_path)
    else:
        (tmp_path / "reports").mkdir(parents=True, exist_ok=True)
    mutate(tmp_path)

    with pytest.raises(ValueError, match=message):
        runner.write_release_namecert_candidate(
            root=tmp_path,
            generated_at=GENERATED_AT,
            make_check_passed=True,
        )

    assert not (tmp_path / candidate.JSON_ARTIFACT).exists()
    assert not (tmp_path / candidate.MARKDOWN_ARTIFACT).exists()


def test_runner_fails_closed_for_missing_sidecar(tmp_path):
    with pytest.raises(ValueError, match="missing release manifest sidecar"):
        runner.write_release_namecert_candidate(
            root=tmp_path,
            generated_at=GENERATED_AT,
            make_check_passed=True,
        )


def test_audit_rejects_overclaim_fields(tmp_path):
    payload = _candidate_payload(tmp_path)
    payload["classifier_spec"]["scientific_claim"] = True
    payload["classifier_spec"]["publishable_tag_claim"] = True
    payload["classifier_spec"]["model_quality_proof"] = True
    payload["classifier_spec"]["bedc_theory_closure"] = True
    payload["classifier_spec"]["release_closure"] = "theoryclosure"

    audit = candidate.audit_release_namecert_candidate(payload)

    assert audit["status"] == "fail"
    assert "classifier_spec.scientific_claim" in audit["failures"]
    assert "classifier_spec.publishable_tag_claim" in audit["failures"]
    assert "classifier_spec.model_quality_proof" in audit["failures"]
    assert "classifier_spec.bedc_theory_closure" in audit["failures"]
    assert "classifier_spec.release_closure" in audit["failures"]
    assert audit["hardgates"] == {
        "G-HG1": False,
        "G-HG2": False,
        "G-HG3": True,
        "G-HG4": False,
    }


def test_candidate_stays_out_of_canonical_reports_and_index_is_pointer_only(tmp_path, monkeypatch):
    _candidate_payload(tmp_path)
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    section = canonical._release_namecert_candidate_index_section()
    payload = canonical._index([], generated_at=GENERATED_AT)
    markdown = canonical._render_index_markdown(payload)

    assert candidate.JSON_ARTIFACT not in {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    assert candidate.MARKDOWN_ARTIFACT not in {spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS}
    assert section == {
        "status": "pointer-only",
        "artifact_id": candidate.ARTIFACT_ID,
        "json_artifact": candidate.JSON_ARTIFACT,
        "markdown_artifact": candidate.MARKDOWN_ARTIFACT,
        "owner_artifact": sidecar.ARTIFACT_ID,
        "candidate_status": "ready-candidate",
        "ledger_policy_pointer": "$.ledger_policy",
        "revoke_if_pointer": "$.ledger_policy.revoke_if",
        "source_sidecar_digest": section["source_sidecar_digest"],
        "tag_absent_policy": "active",
    }
    assert len(section["source_sidecar_digest"]) == 64
    assert payload["release_namecert_candidate"] == section
    assert "Release NameCert candidate" in markdown
    assert "required_pointers" not in json.dumps(payload["release_namecert_candidate"])
    assert "release_namecert_candidate" not in json.dumps(payload["discovery_map"])


def test_single_fact_source_invariant_rejects_forbidden_copies(tmp_path):
    payload = _candidate_payload(tmp_path)
    payload["source_spec"]["required_pointers"] = [{"id": "copied"}]
    payload["canonical_reports"] = ["copied"]
    payload["closurestatus"] = "copied"

    audit = candidate.audit_release_namecert_candidate(payload)

    assert audit["status"] == "fail"
    assert "forbidden_keys" in audit["failures"]
    assert set(audit["forbidden_keys"]) == {"canonical_reports", "closurestatus", "required_pointers"}

import json
from pathlib import Path

from bedc_quality_lab import schema
from scripts import release_manifest_sidecar as sidecar
from scripts import run_canonical_reports as canonical


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


def test_current_release_sidecar_resolves_required_pointers():
    resolved = sidecar.resolve_release_manifest(canonical.ROOT)
    rows = {row.id: row for row in resolved.required_pointers}

    assert set(rows) == {
        "canonical-index",
        "artifact-manifest-navigation",
        "literature-ledger-release-navigation",
        "version-file",
        "canonical-index-markdown",
        "artifact-manifest-self-row",
    }
    assert all(row.status == "resolved" for row in rows.values())
    assert resolved.release_bundle_status == "ready"


def test_missing_required_pointer_marks_not_ready(tmp_path):
    _write_fixture_root(tmp_path)
    (tmp_path / "reports" / "canonical" / "index.md").unlink()

    resolved = sidecar.resolve_release_manifest(tmp_path)
    row = next(item for item in resolved.required_pointers if item.id == "canonical-index-markdown")

    assert resolved.release_bundle_status == "not-ready"
    assert row.to_payload() == {
        "id": "canonical-index-markdown",
        "path": "reports/canonical/index.md",
        "pointer": "# Canonical Report Index",
        "status": "missing",
        "failure": "missing path: reports/canonical/index.md",
    }


def test_tag_status_is_falsifiable_metadata(tmp_path, monkeypatch):
    _write_fixture_root(tmp_path)

    def fake_git_present(self, *args):
        if args[:2] == ("rev-parse", "--verify"):
            return "abc"
        if args == ("rev-parse", "HEAD"):
            return "abc"
        return None

    monkeypatch.setattr(sidecar.ReleasePointerResolver, "_git_stdout", fake_git_present)
    present = sidecar.resolve_release_manifest(tmp_path, tag_ref="release-tag")
    assert present.tag_status == "present"
    assert present.release_bundle_status == "ready"

    def fake_git_stale(self, *args):
        if args[:2] == ("rev-parse", "--verify"):
            return "abc"
        if args == ("rev-parse", "HEAD"):
            return "def"
        return None

    monkeypatch.setattr(sidecar.ReleasePointerResolver, "_git_stdout", fake_git_stale)
    stale = sidecar.resolve_release_manifest(tmp_path, tag_ref="release-tag")
    assert stale.tag_status == "stale"
    assert stale.release_bundle_status == "not-ready"

    def fake_git_absent(self, *args):
        return None

    monkeypatch.setattr(sidecar.ReleasePointerResolver, "_git_stdout", fake_git_absent)
    absent = sidecar.resolve_release_manifest(tmp_path, tag_ref="release-tag")
    payload = absent.to_payload()
    assert absent.tag_status == "absent"
    assert absent.release_bundle_status == "ready"
    assert "quality_scorecard" not in payload
    assert "formal_hardening" not in payload
    assert "discovery_map" not in payload


def test_sidecar_schema_is_local(tmp_path):
    _write_fixture_root(tmp_path)
    resolved = sidecar.resolve_release_manifest(tmp_path)

    assert resolved.schema_id == "bedc-quality-lab:release-manifest-sidecar"
    assert resolved.artifact_id == "bedc-quality-lab:release-manifest-sidecar"
    assert schema.SCHEMA_ID == "bedc-quality-lab:evidence-envelope"


def test_no_host_env_or_manifest_status_copy(tmp_path):
    _write_fixture_root(tmp_path)
    (tmp_path / ".refactor-loop").mkdir()
    (tmp_path / ".refactor-loop" / "host.env").write_text("TAG_REF=release-tag\n", encoding="utf-8")
    (tmp_path / "reports" / "canonical" / "index.json").write_text(
        json.dumps({"schema_id": canonical.INDEX_SCHEMA_ID, "reports": [{"status": "fail"}]}) + "\n",
        encoding="utf-8",
    )

    resolved = sidecar.resolve_release_manifest(tmp_path)
    payload = resolved.to_payload()

    assert resolved.tag_ref is None
    assert all(set(row) == {"id", "path", "pointer", "status", "failure"} for row in payload["required_pointers"])
    assert all(row["status"] != "fail" for row in payload["required_pointers"])
    assert all("report_status" not in row for row in payload["required_pointers"])


def test_canonical_index_summarizes_release_sidecar_without_canonical_expansion(tmp_path, monkeypatch):
    _write_fixture_root(tmp_path)
    written = sidecar.write_release_manifest_sidecar(
        tmp_path,
        generated_at="2026-01-02T03:04:05+00:00",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    payload = canonical._index([], generated_at="2026-01-02T03:04:05+00:00")
    markdown = canonical._render_index_markdown(payload)

    assert payload["release_manifest_sidecar"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:release-manifest-sidecar",
        "json_artifact": "reports/release_manifest_sidecar.json",
        "markdown_artifact": "reports/release_manifest_sidecar.md",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "release_bundle_status": written.release_bundle_status,
        "tag_status": written.tag_status,
        "version": written.version,
    }
    assert "Release manifest sidecar" in markdown
    assert "release_manifest_sidecar" not in [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "release_manifest_sidecar" not in json.dumps(payload["discovery_map"])
    assert "required_pointers" not in payload["release_manifest_sidecar"]

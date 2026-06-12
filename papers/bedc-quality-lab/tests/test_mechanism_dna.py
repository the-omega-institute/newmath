from __future__ import annotations

import json
from pathlib import Path

import pytest

from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.mechanism_dna import (
    DEFAULT_DETERMINISTIC_SEED,
    FORBIDDEN_ALIAS_KEYS,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    REQUIRED_REF_FIELDS,
    audit_mechanism_dna,
    build_mechanism_dna,
    mechanism_dna_artifacts,
    render_mechanism_dna_markdown,
    stable_json,
)
from scripts import run_mechanism_dna


ROOT = Path(__file__).resolve().parents[1]


def _payloads() -> dict[str, dict[str, object]]:
    payloads: dict[str, dict[str, object]] = {}
    for artifact in mechanism_dna_artifacts():
        payloads[artifact] = json.loads((ROOT / artifact).read_text(encoding="utf-8"))
    return payloads


def _mechanism_payload() -> dict[str, object]:
    return build_mechanism_dna(
        _payloads(),
        generated_at="2030-01-01T00:00:00+00:00",
        deterministic_seed=DEFAULT_DETERMINISTIC_SEED,
    )


def test_mechanism_dna_rows_expose_canonical_pointer_schema():
    payload = _mechanism_payload()
    row = payload["rows"][0]

    assert set(REQUIRED_REF_FIELDS).issubset(row)
    for field in REQUIRED_REF_FIELDS:
        ref = row[field]
        assert tuple(ref) == ("artifact", "pointer", "owner_pointer")
        assert ref["owner_pointer"] == f"{ref['artifact']}:{ref['pointer']}"
    assert "terminal_verdict" not in row
    assert pointer_value(payload, "$.hardgate.status") == "pass"


def test_mechanism_dna_refs_resolve_against_sources():
    source_payloads = _payloads()
    payload = _mechanism_payload()

    assert audit_mechanism_dna(payload, source_payloads)["status"] == "pass"
    for row in payload["rows"]:
        for field in (*REQUIRED_REF_FIELDS, "source_level_ref", "source_status_ref"):
            ref = row[field]
            assert pointer_value(source_payloads[ref["artifact"]], ref["pointer"]) is not None


def test_mechanism_dna_missing_required_ref_fails_closed():
    source_payloads = _payloads()
    payload = _mechanism_payload()
    mutated = json.loads(json.dumps(payload))
    mutated["rows"][0]["component_ref"]["pointer"] = "$.missing_component"
    mutated["rows"][0]["row_hardgate"]["status"] = "fail-closed"

    audit = audit_mechanism_dna(mutated, source_payloads)

    assert audit["status"] == "fail"
    assert "row-0-component_ref" in audit["failed_gates"]


def test_mechanism_dna_writer_blocks_failed_audit_before_artifact_write(tmp_path, monkeypatch):
    def failing_audit(payload, source_payloads):
        return {"status": "fail", "failed_gates": ["row-0-component_ref"], "row_count": 1}

    monkeypatch.setattr(run_mechanism_dna, "audit_mechanism_dna", failing_audit)

    with pytest.raises(SystemExit, match="mechanism-dna audit failed: row-0-component_ref"):
        run_mechanism_dna.write_mechanism_dna(
            root=tmp_path,
            generated_at="2030-01-01T00:00:00+00:00",
        )

    assert not (tmp_path / JSON_ARTIFACT).exists()
    assert not (tmp_path / run_mechanism_dna.MARKDOWN_ARTIFACT).exists()


def test_mechanism_dna_writer_publishes_json_and_markdown(tmp_path):
    for artifact, payload in _payloads().items():
        path = tmp_path / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    payload = run_mechanism_dna.write_mechanism_dna(
        root=tmp_path,
        generated_at="2030-01-01T00:00:00+00:00",
        deterministic_seed=935,
    )
    json_path = tmp_path / JSON_ARTIFACT
    markdown_path = tmp_path / MARKDOWN_ARTIFACT

    assert json_path.exists()
    assert markdown_path.exists()
    assert json.loads(json_path.read_text(encoding="utf-8")) == payload
    assert payload["generated_at"] == "2030-01-01T00:00:00+00:00"
    assert payload["deterministic_seed"] == 935
    assert audit_mechanism_dna(payload, run_mechanism_dna.load_source_payloads(tmp_path))["status"] == "pass"
    markdown = markdown_path.read_text(encoding="utf-8")
    assert markdown == render_mechanism_dna_markdown(payload)
    assert "| row | mechanism | component | causal path | intervention | ablation | negative witness | status |" in (
        markdown
    )


def test_mechanism_dna_has_no_terminal_verdict_alias_surface():
    payload = _mechanism_payload()
    serialized = json.dumps(payload, sort_keys=True)

    for key in FORBIDDEN_ALIAS_KEYS:
        assert key not in serialized


def test_mechanism_dna_deterministic_seed_is_byte_stable():
    source_payloads = _payloads()
    first = build_mechanism_dna(
        source_payloads,
        generated_at="2030-01-01T00:00:00+00:00",
        deterministic_seed=935,
    )
    second = build_mechanism_dna(
        source_payloads,
        generated_at="2030-01-01T00:00:00+00:00",
        deterministic_seed=935,
    )

    assert first["deterministic_seed"] == 935
    assert stable_json(first) == stable_json(second)
    assert JSON_ARTIFACT == "reports/canonical/mechanism_dna.json"

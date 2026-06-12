import json
from pathlib import Path

from bedc_quality_lab import experiment_stack
from bedc_quality_lab.experiment_stack import (
    EXPERIMENT_STACK_CARDS,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    OWNER_BACKED_CARD_IDS,
    build_experiment_stack_payload,
    validate_experiment_stack_specs,
    write_experiment_stack_cards,
)


def test_all_fourteen_cards_have_owner_schema_hg_demotion_and_source_pointer():
    assert validate_experiment_stack_specs() == ()
    assert len(EXPERIMENT_STACK_CARDS) == 14

    for spec in EXPERIMENT_STACK_CARDS:
        assert spec.card_id
        assert spec.canonical_owner_issue
        assert spec.owner_artifact.endswith(".json")
        assert spec.schema_id.startswith("bedc-quality-lab:")
        assert spec.hardgate_prefixes
        assert spec.demotion_rule_pointer.startswith(f"{spec.owner_artifact}:")
        assert spec.source_pointer.startswith(f"{spec.owner_artifact}:")
        assert spec.summary_pointer.startswith(f"{spec.owner_artifact}:")


def test_existing_owner_cards_are_pointer_only():
    owner_specs = {
        spec.card_id: spec
        for spec in EXPERIMENT_STACK_CARDS
        if spec.card_id in OWNER_BACKED_CARD_IDS
    }

    assert set(owner_specs) == set(OWNER_BACKED_CARD_IDS)
    assert owner_specs["feature-access-card"].canonical_owner_issue == "1209"
    assert owner_specs["ood-solvability-card"].canonical_owner_issue == "1209,1203"
    assert owner_specs["metric-provenance-card"].canonical_owner_issue == "1201"
    assert owner_specs["artifact-reproducibility-card"].canonical_owner_issue == "1213"
    assert owner_specs["model-card"].canonical_owner_issue == "1220"

    for spec in owner_specs.values():
        payload = spec.to_json()
        serialized = json.dumps(payload, sort_keys=True)
        assert "gate semantics" not in serialized.lower()
        assert "pass because" not in serialized.lower()
        assert spec.source_pointer.startswith(f"{spec.owner_artifact}:")
        assert spec.summary_pointer.startswith(f"{spec.owner_artifact}:")


def test_missing_owner_artifact_fails_closed(tmp_path):
    payload = build_experiment_stack_payload(root=tmp_path, generated_at="fixture")

    assert payload["status"] == "blocked"
    assert payload["card_count"] == 14
    assert payload["blocked_card_ids"]
    first = payload["cards"][0]
    assert first["status"] == "blocked"
    assert first["hardgates"]["STACK-HG1"]["status"] == "fail"
    assert "owner-artifact-missing" in first["failure_reasons"]


def test_regen_idempotent_experiment_stack_cards(tmp_path):
    first = write_experiment_stack_cards(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    first_json = (tmp_path / JSON_ARTIFACT).read_text(encoding="utf-8")
    first_markdown = (tmp_path / MARKDOWN_ARTIFACT).read_text(encoding="utf-8")

    second = write_experiment_stack_cards(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert second == first
    assert (tmp_path / JSON_ARTIFACT).read_text(encoding="utf-8") == first_json
    assert (tmp_path / MARKDOWN_ARTIFACT).read_text(encoding="utf-8") == first_markdown


def test_standard_alignment_is_pointer_only():
    doc = Path("docs/experiment_stack_standard_alignment.md").read_text(encoding="utf-8")

    for name in ("NeurIPS checklist", "Papers with Code", "ACM artifact badging", "Model Cards", "NIST AI RMF"):
        assert name in doc
    assert JSON_ARTIFACT in doc
    assert "https://" in doc
    assert "we recommend" not in doc.lower()
    assert "must include" not in doc.lower()
    assert "should include" not in doc.lower()
    assert "reproducibility checklist" not in doc.lower()


def test_committed_owner_backed_cards_resolve_without_stub_passes():
    payload = build_experiment_stack_payload(root=Path("."), generated_at="fixture")
    rows = {row["card_id"]: row for row in payload["cards"]}

    for card_id in OWNER_BACKED_CARD_IDS:
        row = rows[card_id]
        assert row["owner_artifact_status"] == "resolved"
        assert row["owner_schema_status"] == "matched"
        assert row["source_pointer_status"] == "resolved"
        assert row["summary_pointer_status"] == "resolved"

    assert rows["claim-card"]["status"] == "blocked"
    assert "owner-artifact-missing" in rows["claim-card"]["failure_reasons"]
    assert "claim-card" in payload["blocked_card_ids"]

import json

from bedc_quality_lab.fair_alignment_control_ledger import (
    ARTIFACT_ID,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    SCHEMA_ID,
    FairAlignmentControlLedger,
    FairAlignmentControlRow,
    build_default_rows,
    render_markdown,
)
from scripts.run_fair_alignment_control_ledger import write_artifacts


def _row(**overrides):
    values = {
        "producer_id": "fixture-producer",
        "claim_id": "fixture-claim",
        "task_identity": "gaussian-ou:learned-h-gap-detection",
        "fair_control_identity": "matched-random-gap-head",
        "candidate_artifact": "reports/canonical/fixture.json",
        "candidate_pointer": "$.candidate",
        "control_artifact": "reports/canonical/fixture.json",
        "control_pointer": "$.control",
        "positive_claim_pointer": "$.claim",
        "base_over_chance_gate_pointer": "reports/canonical/fair-l1-decision.json:$.hardgates.FL1-HG3",
        "match_axes": {
            "parameter_match": True,
            "compute_match": True,
            "threshold_match": True,
            "surface_distribution_match": True,
        },
        "anti_triviality_pointers": {
            "scale_only": "$.anti_triviality.scale_only",
            "metadata_only": "$.anti_triviality.metadata_only",
            "matched_random": "$.anti_triviality.matched_random",
            "forbidden_column": "$.anti_triviality.forbidden_column",
        },
        "evidence_pointers": {
            "raw_evidence": "reports/canonical/fixture.json:$.records",
            "control_protocol": "reports/canonical/fixture.json:$.control",
        },
    }
    values.update(overrides)
    return FairAlignmentControlRow(**values)


def test_ledger_rows_are_pointer_only_and_pass_when_shared_controls_match():
    ledger = FairAlignmentControlLedger(generated_at="fixture-time", rows=(_row(),))
    payload = ledger.to_payload()

    assert payload["schema_id"] == SCHEMA_ID
    assert payload["artifact_id"] == ARTIFACT_ID
    assert payload["json_artifact"] == JSON_ARTIFACT
    assert payload["markdown_artifact"] == MARKDOWN_ARTIFACT
    assert payload["status"] == "pass"
    assert payload["hardgate"]["status"] == "pass"
    assert payload["rows"][0]["row_status"] == "pass"
    assert payload["rows"][0]["candidate_pointer"] == "reports/canonical/fixture.json:$.candidate"
    assert payload["rows"][0]["control_pointer"] == "reports/canonical/fixture.json:$.control"
    assert "candidate_metrics" not in payload["rows"][0]
    assert "control_metrics" not in payload["rows"][0]
    assert "metric_values" not in payload["rows"][0]


def test_ledger_fails_closed_when_match_axis_or_base_gate_is_missing():
    ledger = FairAlignmentControlLedger(
        generated_at="fixture-time",
        rows=(
            _row(
                match_axes={
                    "parameter_match": True,
                    "compute_match": True,
                    "threshold_match": True,
                    "surface_distribution_match": False,
                }
            ),
            _row(producer_id="missing-base-gate", base_over_chance_gate_pointer=""),
        ),
    )

    payload = ledger.to_payload()

    assert payload["status"] == "fail"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG3"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG4"]["status"] == "fail"
    assert payload["rows"][0]["row_status"] == "fail"
    assert "surface_distribution_match" in payload["rows"][0]["failed_checks"]
    assert payload["rows"][1]["row_status"] == "fail"
    assert "base_over_chance_gate_pointer" in payload["rows"][1]["failed_checks"]


def test_default_gap_head_and_drt_rows_share_canonical_schema():
    rows = build_default_rows()
    payload = FairAlignmentControlLedger(generated_at="fixture-time", rows=rows).to_payload()
    producers = {row["producer_id"]: row for row in payload["rows"]}

    assert set(producers) == {"gap-head-on-h", "discovery-regularized-training"}
    assert producers["gap-head-on-h"]["fair_control_identity"] == "matched-random-gap-head"
    assert producers["discovery-regularized-training"]["fair_control_identity"] == "matched-random-structural-control"
    assert producers["gap-head-on-h"]["ledger_row_pointer"] == (
        "reports/canonical/fair-alignment-control-ledger.json:$.rows[?producer_id=gap-head-on-h]"
    )
    assert producers["discovery-regularized-training"]["ledger_row_pointer"] == (
        "reports/canonical/fair-alignment-control-ledger.json:$.rows[?producer_id=discovery-regularized-training]"
    )
    assert payload["producer_adapters"]["gap-head-on-h"]["adapter_role"] == "pointer-only"
    assert payload["producer_adapters"]["discovery-regularized-training"]["adapter_role"] == "pointer-only"


def test_markdown_renders_pointer_table_without_metric_bodies():
    payload = FairAlignmentControlLedger(generated_at="fixture-time", rows=(_row(),)).to_payload()
    markdown = render_markdown(payload)

    assert "# Fair Alignment Control Ledger" in markdown
    assert "reports/canonical/fixture.json:$.candidate" in markdown
    assert "reports/canonical/fixture.json:$.control" in markdown
    assert "candidate_metrics" not in markdown
    assert "control_metrics" not in markdown


def test_writer_preserves_payload_timestamp_and_renders_artifacts(tmp_path):
    payload = write_artifacts(root=tmp_path, generated_at="fixture-time")
    json_payload = json.loads((tmp_path / JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / MARKDOWN_ARTIFACT).read_text(encoding="utf-8")

    assert payload["generated_at"] == "fixture-time"
    assert json_payload["generated_at"] == "fixture-time"
    assert json_payload["status"] == "pass"
    assert json_payload["row_count"] == 2
    assert "- Generated at: `fixture-time`" in markdown
    assert "- Status: `pass`" in markdown
    assert "- Rows: `2`" in markdown
    assert "`gap-head-on-h`" in markdown
    assert "`discovery-regularized-training`" in markdown

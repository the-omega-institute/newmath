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
        "claim_id_pointer": "reports/canonical/fixture.json:$.fair_alignment_control_ledger.claim_id",
        "task_identity_pointer": "reports/canonical/fixture.json:$.fair_alignment_control_ledger.task_identity",
        "fair_control_identity_pointer": (
            "reports/canonical/fixture.json:$.fair_alignment_control_ledger.fair_control_identity"
        ),
        "candidate_pointer": "reports/canonical/fixture.json:$.candidate",
        "control_pointer": "reports/canonical/fixture.json:$.control",
        "positive_claim_pointer": "reports/canonical/fixture.json:$.claim",
        "base_over_chance_gate_pointer": "reports/canonical/fair-l1-decision.json:$.hardgates.FAIR-L1-HG3",
        "match_axis_pointers": {
            "parameter_match": "reports/canonical/fixture.json:$.control_protocol.parameter_match",
            "compute_match": "reports/canonical/fixture.json:$.control_protocol.compute_match",
            "threshold_match": "reports/canonical/fixture.json:$.control_protocol.threshold_match",
            "surface_distribution_match": "reports/canonical/fixture.json:$.control_protocol.surface_distribution_match",
        },
        "anti_triviality_pointers": {
            "scale_only": "reports/canonical/fixture.json:$.anti_triviality_gate_evidence.scale_only",
            "metadata_only": "reports/canonical/fixture.json:$.anti_triviality_gate_evidence.metadata_only",
            "matched_random": "reports/canonical/fixture.json:$.anti_triviality_gate_evidence.matched_random",
            "forbidden_column": "reports/canonical/fixture.json:$.anti_triviality_gate_evidence.forbidden_column",
        },
        "evidence_pointers": {
            "raw_evidence": "reports/canonical/fixture.json:$.records",
            "control_protocol": "reports/canonical/fixture.json:$.control_protocol",
        },
    }
    values.update(overrides)
    return FairAlignmentControlRow(**values)


def _source_payloads():
    return {
        "reports/canonical/fixture.json": {
            "fair_alignment_control_ledger": {
                "claim_id": "fixture-claim",
                "task_identity": "gaussian-ou:learned-h-gap-detection",
                "fair_control_identity": "matched-random-gap-head",
            },
            "candidate": {"positive": True},
            "control": {"positive": False},
            "claim": {"status": "source-evidence-only"},
            "records": [{"seed": 1}],
            "control_protocol": {
                "parameter_match": True,
                "compute_match": True,
                "threshold_match": True,
                "surface_distribution_match": True,
            },
            "anti_triviality_gate_evidence": {
                "scale_only": {"status": "pass"},
                "metadata_only": {"status": "pass"},
                "matched_random": {"status": "pass"},
                "forbidden_column": {"status": "pass"},
            },
        },
        "reports/canonical/fair-l1-decision.json": {
            "hardgates": {
                "FAIR-L1-HG3": {"status": "pass"},
            },
        },
        "reports/canonical/gap-head-on-h.json": {
            "fair_alignment_control_ledger": {
                "claim_id": "gap-head-on-h:main-claim",
                "task_identity": "gaussian-ou:learned-h-gap-detection",
                "fair_control_identity": "matched-random-gap-head",
            },
            "treatment_verdict": {"positive": True},
            "control_verdict": {"positive": False},
            "main_claim_status": "source_evidence_only",
            "records": [{"seed": 1}],
            "control_protocol": {
                "parameter_match": True,
                "compute_match": True,
                "threshold_match": True,
                "surface_distribution_match": True,
            },
            "anti_triviality_gate_evidence": {
                "scale_only": {"status": "pass"},
                "metadata_only": {"status": "pass"},
                "matched_random": {"status": "pass"},
                "forbidden_column": {"status": "pass"},
            },
        },
        "reports/canonical/discovery-regularized-training.json": {
            "fair_alignment_control_ledger": {
                "claim_id": "discovery-regularized-training:positive-claim",
                "task_identity": "gaussian-ou:discovery-regularized-replay",
                "fair_control_identity": "matched-random-structural-control",
            },
            "surface_registry": {
                "quality": {
                    "by_arm": {
                        "DGT_full": {"row_count": 180},
                    },
                },
            },
            "matched_random_control": {"control_positive": False},
            "positive_claim": {"status": "source-evidence-only"},
            "records": {"raw_rows_pointer": "reports/runs/discovery-regularized-training/raw_metrics.jsonl"},
            "fair_control_protocol": {
                "parameter_match": True,
                "compute_match": True,
                "threshold_match": True,
                "surface_distribution_match": True,
            },
            "anti_triviality_gate_evidence": {
                "scale_only": {"status": "pass"},
                "metadata_only": {"status": "pass"},
                "matched_random": {"status": "pass"},
                "forbidden_column": {"status": "pass"},
            },
        },
    }


def _write_source_payloads(root, payloads=None):
    for artifact, payload in (payloads or _source_payloads()).items():
        path = root / artifact
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def test_ledger_rows_are_pointer_only_and_pass_when_shared_controls_match():
    ledger = FairAlignmentControlLedger(generated_at="fixture-time", rows=(_row(),), source_payloads=_source_payloads())
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
    assert payload["rows"][0]["resolved_sources"]["candidate_pointer"]["resolved"] is True
    assert payload["rows"][0]["match_axis_evidence"]["parameter_match"]["status"] == "pass"
    assert payload["rows"][0]["anti_triviality_evidence"]["scale_only"]["status"] == "pass"
    assert "candidate_metrics" not in payload["rows"][0]
    assert "control_metrics" not in payload["rows"][0]
    assert "metric_values" not in payload["rows"][0]


def test_ledger_fails_closed_when_match_axis_or_base_gate_is_missing():
    source_payloads = _source_payloads()
    source_payloads["reports/canonical/fixture.json"]["control_protocol"]["surface_distribution_match"] = False
    source_payloads["reports/canonical/fair-l1-decision.json"]["hardgates"]["FAIR-L1-HG3"]["status"] = "fail"
    ledger = FairAlignmentControlLedger(
        generated_at="fixture-time",
        rows=(
            _row(),
        ),
        source_payloads=source_payloads,
    )

    payload = ledger.to_payload()

    assert payload["status"] == "fail"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG3"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG4"]["status"] == "fail"
    assert payload["rows"][0]["row_status"] == "fail"
    assert "surface_distribution_match" in payload["rows"][0]["failed_checks"]
    assert "base_over_chance_gate_pointer" in payload["rows"][0]["failed_checks"]


def test_ledger_fails_closed_when_identity_sources_are_missing():
    source_payloads = _source_payloads()
    del source_payloads["reports/canonical/fixture.json"]["fair_alignment_control_ledger"]["task_identity"]

    payload = FairAlignmentControlLedger(
        generated_at="fixture-time",
        rows=(_row(),),
        source_payloads=source_payloads,
    ).to_payload()

    assert payload["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG1"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG1"]["failed_producers"] == ["fixture-producer"]
    assert payload["rows"][0]["producer_id"] == "fixture-producer"
    assert payload["rows"][0]["row_status"] == "fail"
    assert "task_identity" in payload["rows"][0]["failed_checks"]


def test_ledger_fails_closed_when_claim_pointers_do_not_resolve():
    source_payloads = _source_payloads()
    del source_payloads["reports/canonical/fixture.json"]["claim"]

    payload = FairAlignmentControlLedger(
        generated_at="fixture-time",
        rows=(_row(),),
        source_payloads=source_payloads,
    ).to_payload()

    assert payload["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG2"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG2"]["failed_producers"] == ["fixture-producer"]
    assert payload["rows"][0]["row_status"] == "fail"
    assert "positive_claim_pointer" in payload["rows"][0]["failed_checks"]


def test_ledger_fails_closed_when_anti_triviality_status_is_not_pass():
    source_payloads = _source_payloads()
    source_payloads["reports/canonical/fixture.json"]["anti_triviality_gate_evidence"]["matched_random"]["status"] = "fail"

    payload = FairAlignmentControlLedger(
        generated_at="fixture-time",
        rows=(_row(),),
        source_payloads=source_payloads,
    ).to_payload()

    assert payload["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG4"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["FACL-HG4"]["failed_producers"] == ["fixture-producer"]
    assert payload["rows"][0]["row_status"] == "fail"
    assert "anti_triviality:matched_random" in payload["rows"][0]["failed_checks"]


def test_default_gap_head_and_drt_rows_share_canonical_schema():
    rows = build_default_rows()
    payload = FairAlignmentControlLedger(generated_at="fixture-time", rows=rows, source_payloads=_source_payloads()).to_payload()
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
    payload = FairAlignmentControlLedger(generated_at="fixture-time", rows=(_row(),), source_payloads=_source_payloads()).to_payload()
    markdown = render_markdown(payload)

    assert "# Fair Alignment Control Ledger" in markdown
    assert "reports/canonical/fixture.json:$.candidate" in markdown
    assert "reports/canonical/fixture.json:$.control" in markdown
    assert "candidate_metrics" not in markdown
    assert "control_metrics" not in markdown


def test_writer_preserves_payload_timestamp_and_renders_artifacts(tmp_path):
    _write_source_payloads(tmp_path)
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

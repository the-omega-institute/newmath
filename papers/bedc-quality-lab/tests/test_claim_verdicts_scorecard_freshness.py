import json

from bedc_quality_lab.artifact_freshness import load_scorecard_snapshot
from scripts import run_canonical_reports as canonical
from scripts import run_claim_verdict_demo as claim_verdict_demo


ROW_KEYS = {
    "claim_id",
    "claim_graph_node_id",
    "claim_verdict",
    "reason",
    "source",
    "ledger_pointer",
    "scorecard_pointer",
    "scorecard_hash",
    "scorecard_ready",
    "formal_hardening_ready",
}
DN_ROW_KEYS = {
    "claim_id",
    "claim_graph_node_id",
    "claim_verdict",
    "reason",
    "negative_report_pointer",
}


def _read_claim_rows():
    path = canonical.ROOT / canonical.CLAIM_VERDICTS_JSONL_ARTIFACT
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def test_checked_in_claim_verdicts_match_current_scorecard_snapshot_before_rewrite():
    index_payload = json.loads(canonical.INDEX_ARTIFACT.read_text(encoding="utf-8"))
    timestamp = index_payload["generated_at"]
    committed_rows = _read_claim_rows()
    generated_rows = claim_verdict_demo.compile_claim_verdicts(canonical.ROOT, generated_at=timestamp)
    snapshot = load_scorecard_snapshot(canonical.ROOT)

    assert committed_rows == generated_rows
    assert committed_rows
    assert index_payload["claim_verdicts"]["row_count"] == len(committed_rows)
    for row in committed_rows:
        if row["claim_verdict"] == "negative_discovery":
            assert set(row) == DN_ROW_KEYS
            assert row["claim_graph_node_id"].startswith("terminal:")
            assert row["negative_report_pointer"].startswith("reports/canonical/negative_discovery_reports.json:$.")
            continue
        assert set(row) == ROW_KEYS
        assert row["claim_graph_node_id"].startswith("terminal:")
        assert row["scorecard_pointer"] == snapshot.scorecard_pointer
        assert row["scorecard_hash"] == snapshot.scorecard_hash
        assert row["scorecard_ready"] is snapshot.scorecard_ready
        assert row["formal_hardening_ready"] is snapshot.formal_hardening_ready

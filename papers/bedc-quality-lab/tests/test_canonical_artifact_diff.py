import json
from pathlib import Path

from scripts.canonical_artifact_diff import audit_canonical_artifact_diff


def _write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_jsonl(path: Path, rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(json.dumps(row, sort_keys=True) for row in rows) + "\n", encoding="utf-8")


def _index(*, status: str = "pass") -> dict[str, object]:
    return {
        "generated_at": "fixture",
        "claim_verdicts": {
            "artifact_id": "bedc-quality-lab:claim-verdicts",
            "jsonl_artifact": "reports/canonical/claim_verdicts.jsonl",
            "status": "pointer-only",
        },
        "discovery_map": {
            "artifact_id": "bedc-quality-lab:discovery-map",
            "json_artifact": "reports/canonical/discovery_map.json",
            "status": "pointer-only",
        },
        "toy_report": {
            "artifact_id": "bedc-quality-lab:toy-report",
            "json_artifact": "reports/canonical/toy-report.json",
            "fingerprint_artifact": "reports/canonical/toy-report.fingerprint.json",
            "status": status,
        },
    }


def _claim_row(claim_id: str, verdict: str) -> dict[str, object]:
    return {"claim_id": claim_id, "claim_verdict": verdict, "source": "fixture:$"}


def _discovery_map(cell: dict[str, object] | None = None) -> dict[str, object]:
    return {
        "artifact_id": "bedc-quality-lab:discovery-map",
        "coverage_matrix": {
            "status": "pointer-only",
            "cells": [
                cell
                or {
                    "component_id": "C1",
                    "discovery_level_pointer": "reports/canonical/a.json:$.level",
                    "claim_verdict_pointer": "reports/canonical/a.json:$.verdict",
                    "hardgate_status": "pass",
                }
            ],
        },
    }


def _fixture_tree(tmp_path: Path, *, base_rows: list[dict[str, object]], head_rows: list[dict[str, object]]) -> tuple[Path, Path]:
    base = tmp_path / "base"
    head = tmp_path / "head"
    for root, rows in ((base, base_rows), (head, head_rows)):
        _write_json(root / "reports/canonical/index.json", _index())
        _write_json(root / "reports/canonical/discovery_map.json", _discovery_map())
        _write_json(root / "reports/canonical/toy-report.json", {"status": "pass"})
        _write_json(root / "reports/canonical/toy-report.fingerprint.json", {"sha256": "same"})
        _write_jsonl(root / "reports/canonical/claim_verdicts.jsonl", rows)
    return base / "reports/canonical/index.json", head / "reports/canonical/index.json"


def _declaration(claim_id: str, from_verdict: str | None, to_verdict: str | None) -> str:
    from_cell = "null" if from_verdict is None else from_verdict
    to_cell = "null" if to_verdict is None else to_verdict
    return (
        "```canonical-diff\n"
        "claim_id | from | to | reason\n"
        f"{claim_id} | {from_cell} | {to_cell} | reviewed canonical pointer change\n"
        "```\n"
    )


def test_audit_reports_added_deleted_changed_canonical_rows(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
        head_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
    )
    base_payload = json.loads(base_index.read_text())
    head_payload = json.loads(head_index.read_text())
    del head_payload["toy_report"]
    head_payload["new_report"] = {"json_artifact": "reports/canonical/new.json", "status": "pass"}
    head_payload["discovery_map"] = {**head_payload["discovery_map"], "status": "changed"}
    _write_json(head_index, head_payload)

    result = audit_canonical_artifact_diff(base_index, head_index)

    assert result["hardgate"]["status"] == "pass"
    by_name = {row["name"]: row for row in result["index_row_transitions"]}
    assert by_name["toy_report"]["kind"] == "deleted"
    assert by_name["new_report"]["kind"] == "added"
    assert by_name["discovery_map"]["kind"] == "changed"
    assert {row["status"] for row in result["index_row_transitions"]} == {"diagnostic"}


def test_changed_claim_verdict_without_declaration_fails_closed(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:gap-head-discovery", "projected_discovery_required")],
        head_rows=[_claim_row("claim:gap-head-discovery", "accepted_positive_discovery")],
    )

    result = audit_canonical_artifact_diff(base_index, head_index)

    assert result["hardgate"]["status"] == "fail"
    assert result["hardgate"]["failed_gates"] == ["ADIFF-HG1", "ADIFF-HG5"]
    assert result["claim_verdict_transitions"][0]["gate"] == "ADIFF-HG1"


def test_changed_claim_verdict_with_plain_block_declaration_passes(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:gap-head-discovery", "projected_discovery_required")],
        head_rows=[_claim_row("claim:gap-head-discovery", "accepted_positive_discovery")],
    )

    result = audit_canonical_artifact_diff(
        base_index,
        head_index,
        pr_body=_declaration("claim:gap-head-discovery", "projected_discovery_required", "accepted_positive_discovery"),
    )

    assert result["hardgate"]["status"] == "pass"
    assert result["hardgate"]["failed_gates"] == []


def test_added_claim_verdict_row_requires_declaration(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[],
        head_rows=[_claim_row("claim:new-canonical-claim", "raw_operational_evidence_pass")],
    )

    blocked = audit_canonical_artifact_diff(base_index, head_index)
    allowed = audit_canonical_artifact_diff(
        base_index,
        head_index,
        pr_body=_declaration("claim:new-canonical-claim", None, "raw_operational_evidence_pass"),
    )

    assert blocked["hardgate"]["status"] == "fail"
    assert "ADIFF-HG2" in blocked["hardgate"]["failed_gates"]
    assert blocked["claim_verdict_transitions"][0]["from"] is None
    assert allowed["hardgate"]["status"] == "pass"


def test_deleted_claim_verdict_row_requires_declaration(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:removed-canonical-claim", "negative_discovery")],
        head_rows=[],
    )

    blocked = audit_canonical_artifact_diff(base_index, head_index)
    allowed = audit_canonical_artifact_diff(
        base_index,
        head_index,
        pr_body=_declaration("claim:removed-canonical-claim", "negative_discovery", None),
    )

    assert blocked["hardgate"]["status"] == "fail"
    assert "ADIFF-HG3" in blocked["hardgate"]["failed_gates"]
    assert blocked["claim_verdict_transitions"][0]["to"] is None
    assert allowed["hardgate"]["status"] == "pass"


def test_coverage_cell_transition_is_diagnostic_only(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
        head_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
    )
    _write_json(
        head_index.parent / "discovery_map.json",
        _discovery_map(
            {
                "component_id": "C1",
                "discovery_level_pointer": "reports/canonical/a.json:$.new_level",
                "claim_verdict_pointer": "reports/canonical/a.json:$.verdict",
                "hardgate_status": "fail",
            }
        ),
    )

    result = audit_canonical_artifact_diff(base_index, head_index)

    assert result["hardgate"]["status"] == "pass"
    assert result["coverage_transitions"][0]["gate"] == "ADIFF-HG4"
    assert result["coverage_transitions"][0]["status"] == "diagnostic"
    assert result["diagnostics"]["ADIFF-HG4"]["status"] == "diagnostic"


def test_malformed_or_missing_canonical_diff_block_fails_closed_for_verdict_transition(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:a", "projected_discovery_required")],
        head_rows=[_claim_row("claim:a", "accepted_positive_discovery")],
    )
    malformed_bodies = [
        "",
        "```canonical-diff\nclaim_id | from | to | reason\nclaim:a | projected_discovery_required | accepted_positive_discovery | ok\n```\n```canonical-diff\nclaim_id | from | to | reason\nclaim:b | x | y | ok\n```\n",
        "```canonical-diff\nclaim_id | from | to\nclaim:a | projected_discovery_required | accepted_positive_discovery\n```\n",
        "```canonical-diff\nclaim_id | from | to | reason\nclaim:a | projected_discovery_required | accepted_positive_discovery | \n```\n",
        "claim:a projected_discovery_required accepted_positive_discovery",
        "```json\n{\"claim_id\": \"claim:a\"}\n```\n",
        "```yaml\nclaim_id: claim:a\n```\n",
    ]

    for body in malformed_bodies:
        result = audit_canonical_artifact_diff(base_index, head_index, pr_body=body)
        assert result["hardgate"]["status"] == "fail"
        assert "ADIFF-HG5" in result["hardgate"]["failed_gates"]


def test_refactor_loop_and_durable_report_paths_are_not_inputs(tmp_path):
    base_index, head_index = _fixture_tree(
        tmp_path,
        base_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
        head_rows=[_claim_row("claim:a", "raw_operational_evidence_pass")],
    )
    head_payload = json.loads(head_index.read_text())
    head_payload["host_env"] = {"json_artifact": ".refactor-loop/host.env", "status": "ignored"}
    head_payload["durable_report"] = {
        "json_artifact": "reports/canonical/artifact-diff-audit.json",
        "markdown_artifact": "reports/canonical/artifact-diff-audit.md",
        "status": "ignored",
    }
    _write_json(head_index, head_payload)

    result = audit_canonical_artifact_diff(base_index, head_index)
    rendered = json.dumps(result, sort_keys=True)

    assert result["hardgate"]["status"] == "pass"
    assert ".refactor-loop/host.env" not in rendered
    assert "artifact-diff-audit" not in rendered
    assert "durable report" not in rendered

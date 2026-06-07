from __future__ import annotations

import json
from pathlib import Path

import pytest

from bedc_quality_lab.discovery_compiler.architecture_mutation import (
    ARCHITECTURE_MUTATION_DRAFT_RUN_LOCAL_SCHEMA_ID,
    CANONICAL_ROLE,
    build_architecture_mutation_drafts,
    is_architecture_mutation_candidate,
    require_witness_basis,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


def _write_json(root: Path, artifact: str, payload: dict) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fixture_root(tmp_path: Path) -> Path:
    _write_json(tmp_path, "reports/runs/source/claim_capsule.json", {"run_local": {"negative_witness": [{"status": "blocked"}]}})
    _write_json(tmp_path, "reports/canonical/claim_capsule.json", {"status": "complete"})
    return tmp_path


def test_valid_pointer_builds_run_local_draft_with_resolvable_pointers(tmp_path: Path) -> None:
    root = _fixture_root(tmp_path)
    rows = [
        {
            "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0]",
            "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
            "hardgate_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0].status",
        }
    ]

    payload = build_architecture_mutation_drafts(root, "fixture-time", rows, {}, {})

    assert payload["schema_id"] == ARCHITECTURE_MUTATION_DRAFT_RUN_LOCAL_SCHEMA_ID
    assert payload["canonical_role"] == CANONICAL_ROLE
    assert payload["status"] == "pass"
    assert payload["queue_admissible_count"] == 1
    row = payload["rows"][0]
    assert row["status"] == "queue_admissible"
    for pointer_key in ("witness_basis_pointer", "claim_capsule_pointer", "hardgate_pointer"):
        assert resolve_artifact_pointer(root, row[pointer_key]) is not None
    assert {gate["status"] for gate in row["hardgates"].values()} == {"pass"}


def test_missing_or_unresolvable_witness_basis_blocks_draft(tmp_path: Path) -> None:
    root = _fixture_root(tmp_path)
    rows = [
        {
            "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[9]",
            "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
            "hardgate_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0].status",
        }
    ]

    payload = build_architecture_mutation_drafts(root, "fixture-time", rows, {}, {})

    assert payload["status"] == "blocked"
    assert payload["queue_admissible_rows"] == []
    row = payload["rows"][0]
    assert row["hardgates"]["AMB-HG1"]["status"] == "fail"
    gate = require_witness_basis(row, root)
    assert gate.status == "fail"
    assert gate.reason == "AMB-HG1"


def test_claim_capsule_pointer_alone_is_not_architecture_mutation_candidate() -> None:
    assert not is_architecture_mutation_candidate(
        {
            "kind": "ordinary_packet",
            "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
        }
    )
    assert not is_architecture_mutation_candidate(
        {
            "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
            "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0]",
        }
    )
    assert is_architecture_mutation_candidate({"kind": "architecture_mutation"})
    assert is_architecture_mutation_candidate({"architecture_mutation_draft": {}})


@pytest.mark.parametrize(
    "row_claim_capsule",
    [
        None,
        "not-an-artifact-pointer",
        "reports/canonical/missing_claim_capsule.json:$",
    ],
)
def test_unusable_claim_capsule_blocks_draft_after_witness_basis_resolves(
    tmp_path: Path,
    row_claim_capsule: str | None,
) -> None:
    root = tmp_path
    _write_json(root, "reports/runs/source/claim_capsule.json", {"run_local": {"negative_witness": [{"status": "blocked"}]}})
    row = {
        "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0]",
        "hardgate_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0].status",
    }
    if row_claim_capsule is not None:
        row["claim_capsule_pointer"] = row_claim_capsule

    payload = build_architecture_mutation_drafts(root, "fixture-time", [row], {}, {})

    assert payload["status"] == "blocked"
    assert payload["queue_admissible_rows"] == []
    assert payload["queue_admissible_count"] == 0
    draft = payload["rows"][0]
    assert draft["status"] == "blocked"
    assert draft["hardgates"]["AMB-HG1"]["status"] == "pass"
    assert draft["hardgates"]["AMB-HG2"]["status"] == "fail"
    gate = require_witness_basis({"kind": "architecture_mutation", **row}, root)
    assert gate.status == "fail"
    assert gate.reason == "AMB-HG2"


def test_draft_payload_is_pointer_only_and_rejects_copied_witness_cells(tmp_path: Path) -> None:
    root = _fixture_root(tmp_path)
    row = {
        "witness_basis_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0]",
        "claim_capsule_pointer": "reports/canonical/claim_capsule.json:$",
        "hardgate_pointer": "reports/runs/source/claim_capsule.json:$.run_local.negative_witness[0].status",
        "what_was_learned": "copied witness prose",
        "classifier_reasons": ["copied classifier reason"],
        "raw_metrics": {"loss": 1.0},
        "effective_level": "DN",
        "terminal_verdict": "negative_discovery",
        "negative_witness_body": {"copied": True},
    }

    payload = build_architecture_mutation_drafts(root, "fixture-time", [row], {}, {})

    draft = payload["rows"][0]
    assert payload["queue_admissible_rows"] == []
    assert draft["hardgates"]["AMB-HG3"]["status"] == "fail"
    rendered = json.dumps(draft, sort_keys=True)
    for forbidden in (
        "what_was_learned",
        "classifier_reasons",
        "raw_metrics",
        "effective_level",
        "terminal_verdict",
        "negative_witness_body",
        "copied witness prose",
    ):
        assert forbidden not in rendered
    gate = require_witness_basis({"kind": "architecture_mutation", **row}, root)
    assert gate.status == "fail"
    assert gate.reason == "AMB-HG3"

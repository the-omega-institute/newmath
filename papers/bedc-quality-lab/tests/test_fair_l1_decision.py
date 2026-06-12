import json

import pytest

from bedc_quality_lab import fair_l1_decision as fair
from scripts import run_canonical_reports as canonical
from scripts import run_fair_l1_decision as runner


ROOT = fair.LAB_ROOT


def _copy_source(root, artifact):
    target = root / artifact
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((ROOT / artifact).read_bytes())


def _write_sources(root):
    for artifact in (
        fair.DGT_L1_CONTROLS_ARTIFACT,
        fair.DGT_BASE_UNDERTRAINING_ARTIFACT,
        fair.INPUT_ACCESSIBILITY_ARTIFACT,
        "reports/canonical/order-k-benchmark.json",
    ):
        _copy_source(root, artifact)


def _payload(root):
    _write_sources(root)
    return fair.build_payload(root=root, generated_at="fixture-time")


def test_fair_l1_decision_projects_bounded_negative_from_current_l1_evidence(tmp_path):
    payload = _payload(tmp_path)

    assert payload["decision"]["allowed_statuses"] == ["blocked", "bounded-negative", "scaling-evidence-eligible"]
    assert payload["decision"]["status"] == "bounded-negative"
    assert payload["ladder_state_projection"]["allowed_states"] == [
        "l1-scaling-blocked",
        "l1-bounded-negative",
        "l1-scaling-evidence-eligible",
    ]
    assert payload["ladder_state_projection"]["state"] == "l1-bounded-negative"
    assert payload["hardgates"]["FAIR-L1-HG1"]["status"] == "pass"
    assert payload["hardgates"]["FAIR-L1-HG2"]["status"] == "fail"
    assert payload["hardgates"]["FAIR-L1-HG3"]["status"] == "fail"
    assert payload["hardgates"]["FAIR-L1-HG6"]["status"] == "fail"
    assert [row["comparison_id"] for row in payload["fair_alignment"]["comparison_rows"]] == list(fair.REQUIRED_COMPARISONS)
    assert payload["fair_alignment"]["comparison_rows"][-1]["status"] == "missing"
    assert any(row["gate_id"] == "FAIR-L1-HG3" for row in payload["boundary_ledger"])
    assert "unblocked" not in json.dumps(payload, sort_keys=True)
    assert "scoped-boundary" not in json.dumps(payload, sort_keys=True)


def test_fair_l1_decision_missing_source_blocks_instead_of_stub(tmp_path):
    _write_sources(tmp_path)
    (tmp_path / fair.DGT_L1_CONTROLS_ARTIFACT).unlink()
    payload = fair.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["decision"]["status"] == "blocked"
    assert payload["ladder_state_projection"]["state"] == "l1-scaling-blocked"
    assert payload["hardgates"]["FAIR-L1-HG1"]["status"] == "fail"
    assert payload["source_artifacts"]["l1_projection"]["status"] == "missing"


def test_fair_l1_claim_capsule_is_pointer_only(tmp_path):
    payload = _payload(tmp_path)
    capsule = payload["decision"]["claim_capsule"]
    text = json.dumps(capsule, sort_keys=True)

    assert capsule["status"] == "pointer-only"
    assert f"{fair.CANONICAL_JSON_ARTIFACT}:$.ladder_state_projection" in capsule["projection_pointers"]
    assert all(isinstance(pointer, str) and ":" in pointer for pointer in capsule["evidence_pointers"])
    assert "comparison_rows" not in text
    assert "construct_validity_projection" not in text
    assert "fair_alignment" not in text


def test_fair_l1_decision_cli_writes_canonical_artifacts(tmp_path, capsys):
    _write_sources(tmp_path)

    assert runner.main(["--root", str(tmp_path), "--generated-at", "fixture-time"]) == 0
    summary = json.loads(capsys.readouterr().out)
    payload = json.loads((tmp_path / fair.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert summary["artifact_id"] == fair.ARTIFACT_ID
    assert summary["status"] == payload["decision"]["status"] == "bounded-negative"
    assert summary["ladder_state"] == payload["ladder_state_projection"]["state"] == "l1-bounded-negative"
    assert (tmp_path / fair.CANONICAL_MARKDOWN_ARTIFACT).exists()
    assert not (tmp_path / fair.CANONICAL_FINGERPRINT_ARTIFACT).exists()


def test_fair_l1_decision_canonical_spec_is_unique_and_before_consumers():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "fair-l1-decision"]
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    assert len(specs) == 1
    spec = specs[0]
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_fair_l1_decision.py")
    assert spec.json_artifact == fair.CANONICAL_JSON_ARTIFACT
    assert spec.markdown_artifact == fair.CANONICAL_MARKDOWN_ARTIFACT
    assert spec.required_json_keys.count("ladder_state_projection") == 1
    assert names.index("dgt-l1-controls") < names.index("fair-l1-decision")
    assert names.index("dgt-base-undertraining-audit") < names.index("fair-l1-decision")
    assert names.index("fair-l1-decision") < names.index("discovery-gated-transformer")


def test_fair_l1_decision_rejects_public_alias_mutation(tmp_path):
    payload = _payload(tmp_path)
    payload["decision"]["status"] = "unblocked"

    with pytest.raises(ValueError, match="status domain"):
        fair.validate_payload(payload, root=tmp_path)

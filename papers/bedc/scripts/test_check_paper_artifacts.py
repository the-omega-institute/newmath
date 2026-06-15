import json
from pathlib import Path

from check_paper_artifacts import check_paper_artifacts


def _write_json(path: Path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _owner_payload(*, paper_literal: str = "0.125", artifact_pointer: str = "reports/canonical/owner.json:$"):
    return {
        "schema_id": "bedc-quality-lab:claim-artifact-consistency",
        "status": "pass",
        "paper_surfaces": [
            {
                "surface_id": "surface-a",
                "surface_type": "table",
                "artifact_pointer": artifact_pointer,
                "claim_pointer": "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
                "hardgate_pointer": "reports/canonical/owner.json:$.hardgate.status",
                "not_claimed_pointer": "reports/canonical/owner.json:$.not_claimed",
                "values": [
                    {
                        "value_id": "metric-a",
                        "artifact_pointer": "reports/canonical/owner.json:$.metric",
                        "paper_literal": paper_literal,
                        "transform": "number",
                        "tolerance": 0.0,
                    }
                ],
            }
        ],
    }


def _paper_root(tmp_path: Path) -> Path:
    root = tmp_path / "paper"
    _write_json(root / "paper_artifact_sources.json", {"schema_id": "bedc-paper-artifact-sources", "source_roots": ["parts"]})
    parts = root / "parts"
    parts.mkdir(parents=True)
    return root


def _owner_root(tmp_path: Path, *, include_owner: bool = True) -> Path:
    root = tmp_path / "owner"
    if include_owner:
        _write_json(
            root / "reports/canonical/owner.json",
            {
                "hardgate": {"status": "pass"},
                "metric": 0.125,
                "not_claimed": ["fixture boundary"],
            },
        )
        _write_json(
            root / "reports/canonical/claim_verdicts.json",
            {"lines": [{"claim_id": "fixture"}]},
        )
        claim_verdicts = root / "reports/canonical/claim_verdicts.jsonl"
        claim_verdicts.parent.mkdir(parents=True, exist_ok=True)
        claim_verdicts.write_text(json.dumps({"claim_id": "fixture"}) + "\n", encoding="utf-8")
    return root


def test_check_paper_artifacts_accepts_owner_backed_marker(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")

    findings = check_paper_artifacts(root, owner_payload=_owner_payload(), owner_root=owner_root)

    assert findings == []


def test_check_paper_artifacts_requires_owner_value_marker(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text("", encoding="utf-8")

    findings = check_paper_artifacts(root, owner_payload=_owner_payload(), owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "owner value has no paper marker"
    assert findings[0].surface_id == "surface-a"
    assert findings[0].value_id == "metric-a"


def test_check_paper_artifacts_rejects_non_pass_owner(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")
    payload = _owner_payload()
    payload["status"] = "fail"

    findings = check_paper_artifacts(root, owner_payload=payload, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "owner status is not pass"


def test_check_paper_artifacts_fails_when_owner_artifact_is_missing(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = tmp_path / "missing-owner"

    findings = check_paper_artifacts(root, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "owner artifact is missing"
    assert findings[0].pointer == "reports/canonical/claim-artifact-consistency.json:$"


def test_check_paper_artifacts_rejects_stale_displayed_value(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.126}" + "\n", encoding="utf-8")

    findings = check_paper_artifacts(root, owner_payload=_owner_payload(paper_literal="0.126"), owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "paper literal mismatch"
    assert findings[0].surface_id == "surface-a"


def test_check_paper_artifacts_rejects_marker_literal_that_differs_from_owner_row(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")

    findings = check_paper_artifacts(root, owner_payload=_owner_payload(paper_literal="0.124"), owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "paper marker literal differs from owner literal"
    assert findings[0].expected == "0.124"
    assert findings[0].actual == "0.125"


def test_check_paper_artifacts_rejects_forbidden_owner_pointer(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")

    findings = check_paper_artifacts(
        root,
        owner_payload=_owner_payload(artifact_pointer="https://example.test/owner.json:$"),
        owner_root=owner_root,
    )

    assert len(findings) == 1
    assert findings[0].reason == "forbidden artifact pointer"


def test_check_paper_artifacts_rejects_invalid_value_transform(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")
    payload = _owner_payload()
    payload["paper_surfaces"][0]["values"][0]["transform"] = "percent"

    findings = check_paper_artifacts(root, owner_payload=payload, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "invalid owner value transform"
    assert findings[0].value_id == "metric-a"


def test_check_paper_artifacts_rejects_invalid_value_tolerance(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")
    payload = _owner_payload()
    payload["paper_surfaces"][0]["values"][0]["tolerance"] = "wide"

    findings = check_paper_artifacts(root, owner_payload=payload, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "invalid owner value tolerance"
    assert findings[0].value_id == "metric-a"


def test_check_paper_artifacts_rejects_unresolved_owner_pointer(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path, include_owner=False)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")

    findings = check_paper_artifacts(
        root,
        owner_payload=_owner_payload(artifact_pointer="reports/canonical/missing.json:$"),
        owner_root=owner_root,
    )

    assert {finding.reason for finding in findings} == {"unresolved artifact pointer"}
    assert any(finding.pointer == "reports/canonical/missing.json:$" for finding in findings)


def test_check_paper_artifacts_rejects_duplicate_source_markers(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(
        "\n".join(
            [
                r"\paperartifact{surface-a}{metric-a}{0.125}",
                r"\paperartifact{surface-a}{metric-a}{0.125}",
            ]
        )
        + "\n",
        encoding="utf-8",
    )

    findings = check_paper_artifacts(root, owner_payload=_owner_payload(), owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "duplicate paper artifact marker"


def test_check_paper_artifacts_rejects_malformed_owner_values(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    payload = _owner_payload()
    payload["paper_surfaces"][0]["values"] = {"metric-a": "reports/canonical/owner.json:$.metric"}

    findings = check_paper_artifacts(root, owner_payload=payload, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "missing owner surface values"
    assert findings[0].surface_id == "surface-a"


def test_check_paper_artifacts_rejects_invalid_surface_type(tmp_path):
    root = _paper_root(tmp_path)
    owner_root = _owner_root(tmp_path)
    (root / "parts" / "claim.tex").write_text(r"\paperartifact{surface-a}{metric-a}{0.125}" + "\n", encoding="utf-8")
    payload = _owner_payload()
    payload["paper_surfaces"][0]["surface_type"] = "appendix"

    findings = check_paper_artifacts(root, owner_payload=payload, owner_root=owner_root)

    assert len(findings) == 1
    assert findings[0].reason == "invalid owner paper surface type"
    assert findings[0].expected == "figure, main_claim_chain, table"

import json
from pathlib import Path

from scripts import literature_ledger


ROOT = Path(__file__).resolve().parents[1]


def _record(record_id: str, role: str) -> dict:
    return {
        "id": record_id,
        "pointer": "docs/source.md",
        "role": role,
        "used_by": ["reports/canonical/index.json:$.literature_ledger"],
        "claim_boundary": f"Pointer boundary for {record_id}.",
        "not_claimed": f"No literature conclusion is restated for {record_id}.",
        "revoke_if": f"Revoke {record_id} if the pointer stops resolving.",
    }


def _payload(records: list[dict] | None = None) -> dict:
    return {
        "schema_id": literature_ledger.SCHEMA_ID,
        "status": "ready",
        "ready_when": "Validator requirements pass.",
        "not_claimed": "Pointer-only citation ledger.",
        "revoke_if": "Revoke on pointer or wording failure.",
        "records": records
        if records is not None
        else [
            _record(f"lit-{role}", role)
            for role in literature_ledger.REQUIRED_ROLES
        ],
    }


def _write_root(tmp_path: Path, payload: dict) -> Path:
    (tmp_path / "docs" / "lit").mkdir(parents=True)
    (tmp_path / "docs" / "source.md").parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / "docs" / "source.md").write_text("source pointer\n", encoding="utf-8")
    (tmp_path / "reports" / "canonical").mkdir(parents=True)
    (tmp_path / "reports" / "canonical" / "index.json").write_text(
        json.dumps({"literature_ledger": {"status": "ready"}}) + "\n",
        encoding="utf-8",
    )
    (tmp_path / literature_ledger.LEDGER_POINTER).write_text(
        json.dumps(payload, indent=2) + "\n",
        encoding="utf-8",
    )
    return tmp_path


def test_current_literature_ledger_is_valid():
    summary = literature_ledger.validate_literature_ledger(ROOT)

    assert summary["status"] == "ready"
    assert summary["record_count"] >= literature_ledger.REQUIRED_RECORD_COUNT
    assert set(summary["required_roles"]) == set(literature_ledger.REQUIRED_ROLES)
    assert summary["failures"] == []


def test_missing_file_is_not_ready(tmp_path):
    summary = literature_ledger.validate_literature_ledger(tmp_path)

    assert summary["status"] == "not-ready"
    assert summary["record_count"] == 0
    assert "missing ledger file" in summary["failures"][0]


def test_less_than_six_records_is_not_ready(tmp_path):
    root = _write_root(tmp_path, _payload(records=[_record("lit-one", literature_ledger.REQUIRED_ROLES[0])]))

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("below required" in failure for failure in summary["failures"])


def test_missing_required_field_is_not_ready(tmp_path):
    payload = _payload()
    del payload["records"][0]["claim_boundary"]
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("missing required field: claim_boundary" in failure for failure in summary["failures"])


def test_duplicate_id_is_not_ready(tmp_path):
    payload = _payload()
    payload["records"][1]["id"] = payload["records"][0]["id"]
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("duplicate record id" in failure for failure in summary["failures"])


def test_invalid_pointer_is_not_ready(tmp_path):
    payload = _payload()
    payload["records"][0]["used_by"] = ["reports/canonical/index.json:$.missing"]
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("JSON pointer is missing" in failure for failure in summary["failures"])


def test_forbidden_term_is_not_ready(tmp_path):
    payload = _payload()
    payload["records"][0]["not_claimed"] = "No full-lejepa claim."
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("forbidden positive claim term" in failure for failure in summary["failures"])


def test_copied_bedc_body_marker_is_not_ready(tmp_path):
    payload = _payload()
    payload["records"][0]["claim_boundary"] = "Do not copy \\leanchecked markers."
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)

    assert summary["status"] == "not-ready"
    assert any("copied BEDC body marker" in failure for failure in summary["failures"])


def test_summary_is_redacted(tmp_path):
    payload = _payload()
    payload["records"][0]["claim_boundary"] = "private citation prose that must not leak"
    root = _write_root(tmp_path, payload)

    summary = literature_ledger.validate_literature_ledger(root)
    rendered = json.dumps(summary)

    assert summary["status"] == "ready"
    assert "private citation prose" not in rendered
    assert "claim_boundary" not in rendered
    assert "not_claimed" not in rendered
    assert "revoke_if" not in rendered

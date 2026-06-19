import importlib.util
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
VALIDATOR_PATH = ROOT / "tools" / "automath_newmath_bridge" / "validate_bridge_manifest.py"
SCHEMA_PATH = ROOT / "tools" / "automath_newmath_bridge" / "bridge_manifest.schema.json"

spec = importlib.util.spec_from_file_location("validate_bridge_manifest", VALIDATOR_PATH)
validator = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(validator)


def bridge_record():
    return {
        "id": "bridge:test",
        "record_version": 1,
        "created_at": "2026-06-18T00:00:00Z",
        "source_repo": "the-omega-institute/newmath",
        "source_branch_or_ref": "main",
        "source_path": "papers/bedc/README.md",
        "source_commit": "abcdef1",
        "source_artifact_kind": "paper_claim",
        "destination_repo": "the-omega-institute/automath",
        "destination_branch_or_ref": "main",
        "destination_path": "docs/bridge.md",
        "destination_artifact_kind": "review_packet",
        "bridge_direction": "newmath_to_automath",
        "status": "candidate",
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "external_publication_risk": "low",
        "notes": "operator-visible context",
        "next_action": "operator review",
    }


def test_schema_required_matches_validator_safety_set():
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))

    assert set(schema["required"]) == validator.SAFETY_CRITICAL_REQUIRED
    assert validator.REQUIRED is validator.SAFETY_CRITICAL_REQUIRED
    assert schema["$id"] == (
        "https://github.com/the-omega-institute/automath/"
        "tools/automath_newmath_bridge/bridge_manifest.schema.json"
    )
    assert "notes" not in schema["required"]
    assert "next_action" not in schema["required"]
    assert schema["properties"]["notes"]["default"] == validator.COMPATIBLE_DEFAULTS["notes"]
    assert (
        schema["properties"]["next_action"]["default"]
        == validator.COMPATIBLE_DEFAULTS["next_action"]
    )


def test_validate_record_accepts_missing_compatible_fields_with_defaults():
    record = bridge_record()
    record.pop("notes")
    record.pop("next_action")

    normalized, warnings = validator.normalize_record(record)

    assert validator.validate_record(record) == []
    assert normalized["notes"] == ""
    assert normalized["next_action"] == "operator review"
    assert warnings == [
        "defaulted compatible missing field: notes",
        "defaulted compatible missing field: next_action",
    ]


def test_validate_record_keeps_taste_gate_fail_closed_with_defaulted_notes():
    record = bridge_record()
    record["taste_gate_required"] = True
    record.pop("notes")

    issues = validator.validate_record(record)

    assert issues == [
        "taste_gate_required=true should name the TasteGate boundary in notes or audit_boundary"
    ]

    record["audit_boundary"] = "BEDC TasteGate witness"
    assert validator.validate_record(record) == []

    record.pop("audit_boundary")
    record["notes"] = "BEDC TasteGate witness"
    assert validator.validate_record(record) == []


def test_validate_record_hard_fails_safety_critical_missing_field():
    record = bridge_record()
    record.pop("source_repo")

    issues = validator.validate_record(record)

    assert issues == ["missing required field: source_repo"]


def test_cli_reports_visible_warnings_for_compatible_defaults(tmp_path):
    record = bridge_record()
    record.pop("notes")
    record.pop("next_action")
    manifest = tmp_path / "manifest.jsonl"
    manifest.write_text(json.dumps(record) + "\n", encoding="utf-8")

    result = subprocess.run(
        [sys.executable, str(VALIDATOR_PATH), str(manifest)],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert "warning: defaulted compatible missing field: notes" in result.stderr
    assert "warning: defaulted compatible missing field: next_action" in result.stderr
    assert "[bridge-validate] ok: 1 record(s)" in result.stdout

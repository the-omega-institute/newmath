import json
from pathlib import Path
import subprocess
import sys

from bedc_quality_lab import metric_purity


def _write_config(tmp_path, row, *, allowlist_rows=None):
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(
        json.dumps({"schema_id": metric_purity.TARGETS_SCHEMA_ID, "targets": [row], "hardgate_mutations": []}) + "\n",
        encoding="utf-8",
    )
    allowlist_path.write_text(
        json.dumps({"schema_id": metric_purity.ALLOWLIST_SCHEMA_ID, "rows": list(allowlist_rows or [])}) + "\n",
        encoding="utf-8",
    )
    return targets_path, allowlist_path


def _target(module, *, target_id=None, kind="metric", report_artifact="", evidence_pointer=None, allowlist_refs=()):
    leaf = module.rsplit(".", 1)[-1]
    return {
        "id": target_id or leaf,
        "kind": kind,
        "module": module,
        "callable": "metric_projection",
        "owner_pointer": f"{module}:metric_projection",
        "report_artifact": report_artifact,
        "evidence_pointer": evidence_pointer if evidence_pointer is not None else f"{module}:metric_projection",
        "empirical_metric_keys": ["quality_q"] if kind == "metric" else [],
        "mutation_contract_refs": [],
        "allowlist_refs": list(allowlist_refs),
    }


def _audit_codes(tmp_path, row, *, allowlist_rows=None):
    targets_path, allowlist_path = _write_config(tmp_path, row, allowlist_rows=allowlist_rows)
    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)
    return payload, {finding["code"] for finding in payload["findings"]}


def test_ast_hg1_flags_arm_identity_branch(tmp_path):
    payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.arm_identity_branch"))

    assert "AST-HG1" in codes
    assert "METPURE-HG1" in codes
    assert payload["status"] == "fail"


def test_ast_hg1_flags_feature_mode_branch(tmp_path):
    _payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.feature_mode_branch"))

    assert "AST-HG1" in codes


def test_feature_target_uses_same_ast_purity_scan(tmp_path):
    payload, codes = _audit_codes(
        tmp_path,
        _target("tests.fixtures.metric_purity.arm_identity_branch", target_id="arm_identity_branch_feature", kind="feature"),
    )

    assert "AST-HG1" in codes
    assert payload["status"] == "fail"


def test_ast_hg1_flags_component_name_dispatch(tmp_path):
    _payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.component_dispatch"))

    assert "AST-HG1" in codes


def test_ast_hg2_flags_arm_key_lookup_and_constant_table(tmp_path):
    _payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.per_arm_constant_table"))

    assert "AST-HG2" in codes
    assert "METPURE-HG1" in codes


def test_ast_hg3_flags_label_intermediate_read(tmp_path):
    _payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.label_intermediate_read"))

    assert "AST-HG3" in codes


def test_ast_hg4_flags_indirect_helper_call(tmp_path):
    _payload, codes = _audit_codes(tmp_path, _target("tests.fixtures.metric_purity.indirect_helper_call"))

    assert "AST-HG4" in codes


def test_registered_safe_metric_helper_passes(tmp_path):
    payload, codes = _audit_codes(
        tmp_path,
        _target("tests.fixtures.metric_purity.safe_metric_helper", allowlist_refs=("registered_average",)),
    )

    assert codes == set()
    assert payload["status"] == "pass"


def test_registered_evidence_pointer_must_resolve(tmp_path):
    artifact = tmp_path / "definitely_missing_pointer_fixture.json"
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_text(json.dumps({"present": {"value": None}}, sort_keys=True) + "\n", encoding="utf-8")

    payload, codes = _audit_codes(
        tmp_path,
        _target(
            "tests.fixtures.metric_purity.safe_metric_helper",
            target_id="definitely_missing_pointer",
            report_artifact=artifact.as_posix(),
            evidence_pointer=f"{artifact.as_posix()}:$.definitely_missing_pointer",
            allowlist_refs=("registered_average",),
        )
    )

    assert "REG-HG4" in codes
    assert payload["status"] == "fail"
    assert any("segment is missing" in finding["reason"] for finding in payload["findings"])


def test_exact_allowlist_matching_marks_finding_without_broad_match(tmp_path):
    row = _target("tests.fixtures.metric_purity.arm_identity_branch")
    first_payload, _codes = _audit_codes(tmp_path, row)
    finding = next(item for item in first_payload["findings"] if item["code"] == "METPURE-HG1")
    allowlist_row = {
        "target_id": finding["target_id"],
        "code": finding["code"],
        "path": finding["path"],
        "lineno": finding["lineno"],
        "symbol": finding["symbol"],
        "rationale": "fixture exercises exact allowlist cells",
        "owner_pointer": finding["owner_pointer"],
    }

    payload, codes = _audit_codes(tmp_path, row, allowlist_rows=[allowlist_row])

    assert "METPURE-HG1" in codes
    assert any(item["allowlisted"] for item in payload["findings"] if item["code"] == "METPURE-HG1")
    assert payload["allowlist_hits"] == [allowlist_row]


def test_stale_allowlist_row_fails_closed(tmp_path):
    row = _target("tests.fixtures.metric_purity.safe_metric_helper", allowlist_refs=("registered_average",))
    stale_row = {
        "target_id": row["id"],
        "code": "AST-HG1",
        "path": "tests/fixtures/metric_purity/safe_metric_helper.py",
        "lineno": 999,
        "symbol": "metric_projection",
        "rationale": "stale fixture",
        "owner_pointer": row["owner_pointer"],
    }

    payload, _codes = _audit_codes(tmp_path, row, allowlist_rows=[stale_row])

    assert payload["status"] == "fail"
    assert payload["allowlist_misses"][0]["reason"] == "allowlist row did not match a current finding"


def test_registry_schema_mismatch_fails_closed(tmp_path):
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(json.dumps({"schema_id": "wrong.schema", "targets": [], "hardgate_mutations": []}) + "\n", encoding="utf-8")
    allowlist_path.write_text(json.dumps({"schema_id": "wrong.allow", "rows": []}) + "\n", encoding="utf-8")

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert payload["status"] == "fail"
    assert {
        (finding["code"], finding["path"], finding["symbol"])
        for finding in payload["findings"]
    } >= {
        ("REG-HG1", targets_path.as_posix(), "schema_id"),
        ("REG-HG5", allowlist_path.as_posix(), "schema_id"),
    }


def test_registry_schema_missing_fails_closed(tmp_path):
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    targets_path.write_text(json.dumps({"targets": [], "hardgate_mutations": []}) + "\n", encoding="utf-8")
    allowlist_path.write_text(json.dumps({"rows": []}) + "\n", encoding="utf-8")

    payload = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert payload["status"] == "fail"
    assert [finding["symbol"] for finding in payload["findings"]].count("schema_id") == 2


def test_metric_purity_cli_rejects_wrong_registry_schema(tmp_path):
    targets_path = tmp_path / "targets.json"
    allowlist_path = tmp_path / "allowlist.json"
    output_path = tmp_path / "out.json"
    targets_path.write_text(json.dumps({"schema_id": "wrong.schema", "targets": [], "hardgate_mutations": []}) + "\n", encoding="utf-8")
    allowlist_path.write_text(json.dumps({"schema_id": "wrong.allow", "rows": []}) + "\n", encoding="utf-8")

    result = subprocess.run(
        [
            sys.executable,
            "scripts/check_metric_purity.py",
            "--targets",
            targets_path.as_posix(),
            "--allowlist",
            allowlist_path.as_posix(),
            "--json",
            output_path.as_posix(),
        ],
        check=False,
        text=True,
        capture_output=True,
    )
    payload = json.loads(output_path.read_text(encoding="utf-8"))

    assert result.returncode == 1
    assert payload["status"] == "fail"
    assert any(finding["symbol"] == "schema_id" for finding in payload["findings"])


def test_metric_purity_audit_is_deterministic(tmp_path):
    row = _target("tests.fixtures.metric_purity.arm_identity_branch")
    targets_path, allowlist_path = _write_config(tmp_path, row)

    first = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)
    second = metric_purity.run_metric_purity_audit(Path.cwd(), targets_path, allowlist_path)

    assert first == second

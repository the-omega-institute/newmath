import json
from pathlib import Path

import pytest

from bedc_quality_lab.evidence_provenance import (
    DISCOVERY_EVIDENCE_TYPES,
    METRIC_SOURCE_TYPES,
    build_evidence_provenance,
    evidence_provenance_pointer_for_report,
    resolve_owner_pointer,
    validate_evidence_provenance_payload,
)
from scripts import run_canonical_reports as canonical


def _spec(name: str, artifact: str, command=("python3", "scripts/run_fixture.py")):
    return canonical.CanonicalReportSpec(
        name=name,
        command=command,
        json_artifact=artifact,
        markdown_artifact=artifact.replace(".json", ".md"),
        required_json_keys=("positive",),
        estimated_seconds=1,
        bundle_role="hg_p_core",
        scope_pointer="$.scope",
        cost_pointer="$.cost",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive",
        control_pointer="$.control",
        no_control_rationale_pointer=None,
    )


def _write_json(root: Path, artifact: str, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _write_source(root: Path, relative: str, body: str = "def main():\n    return None\n"):
    path = root / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")


def _sync_discovery_row_by_report(payload: dict, index: int = 0) -> None:
    row = payload["discovery_rows"][index]
    payload["discovery_rows_by_report"][row["report"]] = row


def _discovery_map_row(report: str, *, level: str = "D1", index: int = 0) -> dict[str, object]:
    row: dict[str, object] = {
        "report": report,
        "json_artifact": f"reports/canonical/{report}.json",
        "markdown_artifact": f"reports/canonical/{report}.md",
        "discovery_level": level,
        "projection_status": "projected",
        "evidence_pointer": "$.positive",
        "audit_status": "valid",
        "audit_reason": "",
        "evidence_type": "boundary_negative" if level == "DN" else "deterministic_projection",
        "evidence_provenance_pointer": evidence_provenance_pointer_for_report(report),
    }
    if level == "DN":
        row.pop("evidence_pointer")
        row["negative_report_pointer"] = f"reports/canonical/negative_discovery_reports.json:$.rows[{index}]"
    return row


def _write_discovery_map(root: Path, rows: list[dict[str, object]]) -> None:
    _write_json(root, "reports/canonical/discovery_map.json", {"rows": rows})


def test_owner_vocabularies_are_maintainer_sets():
    assert METRIC_SOURCE_TYPES == (
        "measured_training",
        "deterministic_projection",
        "declared_constant",
        "arm_branch",
        "protocol_field",
    )
    assert DISCOVERY_EVIDENCE_TYPES == (
        "empirical_training_clean",
        "empirical_training_tainted",
        "deterministic_projection",
        "protocol_artifact",
        "boundary_negative",
    )


def test_every_canonical_report_gets_one_producer_audit_and_metric_row(tmp_path):
    specs = (
        _spec("order-k-benchmark", "reports/canonical/order-k-benchmark.json"),
        _spec("dgt-l0-controls", "reports/canonical/dgt-l0-controls.json"),
    )
    _write_source(tmp_path, "scripts/run_fixture.py")
    for spec in specs:
        _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name) for spec in specs])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=specs, generated_at="fixture")

    assert [row["report"] for row in payload["producer_audits"]] == [spec.name for spec in specs]
    assert [row["source_type"] for row in payload["metric_rows"]] == ["deterministic_projection", "arm_branch"]
    assert all(row["allowed_for_empirical_claim"] is False for row in payload["metric_rows"])
    assert all(row["evidence_type"] != "empirical_training_clean" for row in payload["discovery_rows"])


def test_model_comparison_owner_class_is_deterministic_projection(tmp_path):
    spec = _spec("model-comparison", "reports/canonical/model-comparison.json", command=("python3", "scripts/run_model_comparison.py"))
    _write_source(tmp_path, "scripts/run_model_comparison.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name)])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")

    assert payload["metric_rows"][0]["source_type"] == "deterministic_projection"
    assert payload["discovery_rows"][0]["evidence_type"] == "deterministic_projection"
    assert payload["discovery_rows"][0]["allowed_claim_kinds"] == ["projection_only"]


def test_clean_training_requires_backward_and_optimizer_step(tmp_path):
    spec = _spec("training-report", "reports/canonical/training-report.json")
    _write_source(
        tmp_path,
        "scripts/run_fixture.py",
        "def train(loss, optimizer):\n    loss.backward()\n    optimizer.step()\n",
    )
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name)])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")

    assert payload["producer_audits"][0]["training_evidence_status"] == "empirical_training_clean"
    assert payload["metric_rows"][0]["source_type"] == "measured_training"
    assert payload["metric_rows"][0]["allowed_for_empirical_claim"] is True
    assert payload["discovery_rows"][0]["evidence_type"] == "empirical_training_clean"


def test_optimizer_constructor_without_step_keeps_empirical_claim_gate_closed(tmp_path):
    spec = _spec("training-report", "reports/canonical/training-report.json")
    _write_source(
        tmp_path,
        "scripts/run_fixture.py",
        "def train(loss, torch):\n"
        "    optimizer = torch.optim.Adam([])\n"
        "    loss.backward()\n"
        "    return optimizer\n",
    )
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name)])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    audit = payload["producer_audits"][0]
    metric = payload["metric_rows"][0]
    discovery = payload["discovery_rows"][0]

    assert audit["backward_pointers"] == ["scripts/run_fixture.py:L3"]
    assert audit["optimizer_step_pointers"] == []
    assert audit["training_evidence_status"] != "empirical_training_clean"
    assert metric["source_type"] == "deterministic_projection"
    assert metric["allowed_for_empirical_claim"] is False
    assert discovery["evidence_type"] != "empirical_training_clean"
    assert "empirical_superiority" not in discovery["allowed_claim_kinds"]


def test_imported_non_training_scanner_code_does_not_certify_training(tmp_path):
    spec = _spec("imported-scanner", "reports/canonical/imported-scanner.json")
    _write_source(
        tmp_path,
        "scripts/run_fixture.py",
        "from bedc_quality_lab.evidence_provenance import build_evidence_provenance\n\n"
        "def main():\n"
        "    return build_evidence_provenance\n",
    )
    _write_source(
        tmp_path,
        "bedc_quality_lab/evidence_provenance.py",
        "def scan(line):\n"
        "    if '.backward(' in line:\n"
        "        return 'backward'\n"
        "    if '.step(' in line and 'optimizer' in line:\n"
        "        return 'step'\n"
        "    return None\n",
    )
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name)])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    audit = payload["producer_audits"][0]

    assert audit["training_evidence_status"] == "training_evidence_absent"
    assert audit["backward_pointers"] == []
    assert audit["optimizer_step_pointers"] == []
    assert payload["metric_rows"][0]["source_type"] == "deterministic_projection"
    assert payload["discovery_rows"][0]["evidence_type"] == "deterministic_projection"


@pytest.mark.parametrize(
    ("module_path", "import_line", "expected_backward", "expected_step"),
    [
        (
            "bedc_quality_lab/training_loop.py",
            "from bedc_quality_lab.training_loop import train_model",
            "bedc_quality_lab/training_loop.py:L2",
            "bedc_quality_lab/training_loop.py:L3",
        ),
        (
            "bedc_quality_lab/runner.py",
            "from bedc_quality_lab.runner import train_model",
            "bedc_quality_lab/runner.py:L2",
            "bedc_quality_lab/runner.py:L3",
        ),
    ],
)
def test_directly_imported_local_source_can_certify_training(
    tmp_path,
    module_path,
    import_line,
    expected_backward,
    expected_step,
):
    spec = _spec("delegated-training", "reports/canonical/delegated-training.json")
    _write_source(
        tmp_path,
        "scripts/run_fixture.py",
        f"{import_line}\n\n"
        "def main(loss, optimizer):\n"
        "    return train_model(loss, optimizer)\n",
    )
    _write_source(
        tmp_path,
        module_path,
        "def train_model(loss, optimizer):\n"
        "    loss.backward()\n"
        "    optimizer.step()\n",
    )
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(tmp_path, [_discovery_map_row(spec.name)])

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    audit = payload["producer_audits"][0]

    assert audit["training_evidence_status"] == "empirical_training_clean"
    assert audit["backward_pointers"] == [expected_backward]
    assert audit["optimizer_step_pointers"] == [expected_step]
    assert payload["metric_rows"][0]["source_type"] == "measured_training"
    assert payload["discovery_rows"][0]["evidence_type"] == "empirical_training_clean"


def test_missing_measurement_is_null_with_reason_not_new_enum(tmp_path):
    spec = _spec("missing-metric", "reports/canonical/missing-metric.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"scope": {}, "cost": {}, "not_claimed": [], "control": {}})

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    row = payload["metric_rows"][0]

    assert row["source_type"] in METRIC_SOURCE_TYPES
    assert row["value"] is None
    assert row["not_measurable_reason"] == "source artifact pointer is unresolved"
    assert row["allowed_for_empirical_claim"] is False


def test_validation_rejects_non_owner_vocabularies(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["metric_rows"][0]["source_type"] = "not_measurable"

    with pytest.raises(ValueError, match="source_type"):
        validate_evidence_provenance_payload(payload)


@pytest.mark.parametrize(
    ("collection", "field"),
    [
        ("metric_rows", "source_artifact_pointer"),
        ("metric_rows", "not_claimed"),
        ("producer_audits", "producer_command"),
        ("producer_audits", "backward_pointers"),
        ("producer_audits", "not_claimed"),
        ("discovery_rows", "allowed_claim_kinds"),
        ("discovery_rows", "not_claimed"),
        ("discovery_rows", "discovery_map_pointer"),
    ],
)
def test_validation_rejects_missing_dataclass_row_fields(tmp_path, collection, field):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload[collection][0].pop(field)
    if collection == "discovery_rows":
        _sync_discovery_row_by_report(payload)

    with pytest.raises(ValueError, match=f"{collection}\\[0\\] requires fields: {field}"):
        validate_evidence_provenance_payload(payload)


@pytest.mark.parametrize("replacement", [None, ""])
def test_validation_rejects_null_or_empty_discovery_evidence_type(tmp_path, replacement):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0]["evidence_type"] = replacement
    _sync_discovery_row_by_report(payload)

    with pytest.raises(ValueError, match="evidence_type is unsupported"):
        validate_evidence_provenance_payload(payload)


def test_validation_rejects_missing_discovery_evidence_type(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0].pop("evidence_type")
    _sync_discovery_row_by_report(payload)

    with pytest.raises(ValueError, match="discovery_rows\\[0\\] requires fields: evidence_type"):
        validate_evidence_provenance_payload(payload)


def test_evidence_provenance_pointer_is_report_owner_pointer():
    assert evidence_provenance_pointer_for_report("dgt-l0-controls") == (
        "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.dgt-l0-controls"
    )


def test_owner_payload_rejects_missing_discovery_row_map(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload.pop("discovery_rows_by_report")

    with pytest.raises(ValueError, match="discovery_rows_by_report"):
        validate_evidence_provenance_payload(payload)


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (lambda row: row.pop("evidence_type"), "requires owner evidence_type"),
        (lambda row: row.update({"evidence_type": None}), "requires owner evidence_type"),
        (
            lambda row: row.update(
                {
                    "evidence_provenance_pointer": (
                        "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.missing"
                    )
                }
            ),
            "requires owner evidence provenance pointer",
        ),
    ],
)
def test_build_evidence_provenance_validates_committed_discovery_map(tmp_path, mutate, message):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    row = _discovery_map_row(spec.name)
    mutate(row)
    _write_discovery_map(tmp_path, [row])

    with pytest.raises(ValueError, match=message):
        build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")


def test_sidecar_discovery_row_uses_null_training_audit_pointer(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(
        tmp_path,
        [
            _discovery_map_row(spec.name),
            _discovery_map_row("sidecar-boundary", level="DN", index=0),
        ],
    )

    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    sidecar = payload["discovery_rows_by_report"]["sidecar-boundary"]

    assert sidecar["producer_training_audit_pointer"] is None
    assert sidecar["metric_provenance_pointers"] == []


def test_validation_rejects_empty_training_audit_pointer(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0]["producer_training_audit_pointer"] = ""
    payload["discovery_rows_by_report"]["fixture"] = payload["discovery_rows"][0]

    with pytest.raises(ValueError, match="pointer field must not be empty"):
        validate_evidence_provenance_payload(payload)


@pytest.mark.parametrize(
    ("replacement", "message"),
    [
        (None, "producer_training_audit_pointer must be a non-empty owner pointer or null"),
        (
            "reports/canonical/index.json:$.evidence_provenance.producer_audits[99]",
            "producer_training_audit_pointer does not resolve",
        ),
    ],
)
def test_validation_rejects_metric_training_audit_pointer_mutations(tmp_path, replacement, message):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["metric_rows"][0]["producer_training_audit_pointer"] = replacement

    with pytest.raises(ValueError, match=message):
        validate_evidence_provenance_payload(payload)


def test_validation_rejects_missing_metric_training_audit_pointer(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["metric_rows"][0].pop("producer_training_audit_pointer")

    with pytest.raises(ValueError, match="metric_rows\\[0\\] requires fields: producer_training_audit_pointer"):
        validate_evidence_provenance_payload(payload)


def test_validation_rejects_null_training_audit_pointer_for_producer_report(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0]["producer_training_audit_pointer"] = None
    _sync_discovery_row_by_report(payload)

    with pytest.raises(ValueError, match="producer_training_audit_pointer is required"):
        validate_evidence_provenance_payload(payload)


def test_validation_rejects_missing_training_audit_pointer_for_producer_report(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0].pop("producer_training_audit_pointer")
    _sync_discovery_row_by_report(payload)

    with pytest.raises(ValueError, match="discovery_rows\\[0\\] requires fields: producer_training_audit_pointer"):
        validate_evidence_provenance_payload(payload)


def test_validation_rejects_unresolved_training_audit_pointer(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    payload["discovery_rows"][0]["producer_training_audit_pointer"] = (
        "reports/canonical/index.json:$.evidence_provenance.producer_audits[99]"
    )
    payload["discovery_rows_by_report"]["fixture"] = payload["discovery_rows"][0]

    with pytest.raises(ValueError, match="does not resolve"):
        validate_evidence_provenance_payload(payload)


def test_validation_requires_explicit_null_sidecar_training_audit_pointer(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    _write_discovery_map(
        tmp_path,
        [
            _discovery_map_row(spec.name),
            _discovery_map_row("sidecar-boundary", level="DN", index=0),
        ],
    )
    payload = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    sidecar = payload["discovery_rows_by_report"]["sidecar-boundary"]

    assert sidecar["producer_training_audit_pointer"] is None
    assert validate_evidence_provenance_payload(payload)["discovery_rows"][1] == sidecar

    malformed = dict(sidecar)
    malformed.pop("producer_training_audit_pointer")
    payload["discovery_rows"][1] = malformed
    payload["discovery_rows_by_report"]["sidecar-boundary"] = malformed

    with pytest.raises(ValueError, match="discovery_rows\\[1\\] requires fields: producer_training_audit_pointer"):
        validate_evidence_provenance_payload(payload)


def test_report_owner_pointer_resolves_through_generic_resolver(tmp_path):
    spec = _spec("fixture", "reports/canonical/fixture.json")
    _write_source(tmp_path, "scripts/run_fixture.py")
    _write_json(tmp_path, spec.json_artifact, {"positive": 1, "scope": {}, "cost": {}, "not_claimed": [], "control": {}})
    section = build_evidence_provenance(root=tmp_path, canonical_reports=(spec,), generated_at="fixture")
    _write_json(
        tmp_path,
        "reports/canonical/index.json",
        {
            "schema_id": "bedc-quality-lab:canonical-report-index",
            "generated_at": "fixture",
            "evidence_provenance": section,
        },
    )

    pointer = evidence_provenance_pointer_for_report("fixture")

    assert resolve_owner_pointer(tmp_path, pointer) == section["discovery_rows_by_report"]["fixture"]

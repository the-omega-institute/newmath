from bedc_quality_lab.discovery_compiler.schema_admission import (
    SCHEMA_ADMISSION_HARDGATE_IDS,
    SchemaAdmissionRow,
    validate_schema_admission,
)


def test_schema_admission_row_dict_exposes_only_public_contract_keys():
    row = SchemaAdmissionRow(
        schema_id="bedc-quality-lab:fixture",
        primitive_basis=True,
        owner_pointer="reports/canonical/fixture.json:$",
        validator_ref="bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
        downgrade_policy="fail-closed",
        status="pass",
        reason="schema admission fields are present",
    )

    assert list(row.as_dict()) == [
        "schema_id",
        "primitive_basis",
        "owner_pointer",
        "validator_ref",
        "downgrade_policy",
        "status",
        "reason",
    ]


def test_schema_admission_result_has_sibling_hardgates_with_row_indexes():
    result = validate_schema_admission(
        [
            {
                "schema_id": "bedc-quality-lab:ready",
                "primitive_basis": True,
                "owner_pointer": "reports/canonical/ready.json:$",
                "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
                "downgrade_policy": "fail-closed",
            },
            {
                "schema_id": "bedc-quality-lab:blocked",
                "primitive_basis": False,
                "owner_pointer": "",
                "validator_ref": "",
                "downgrade_policy": "",
            },
        ]
    )

    payload = result.as_dict()
    assert list(payload) == ["status", "rows", "hardgates"]
    assert payload["status"] == "fail"
    assert [row["schema_id"] for row in payload["rows"]] == [
        "bedc-quality-lab:ready",
        "bedc-quality-lab:blocked",
    ]
    assert "hardgates" not in payload["rows"][0]
    assert list(payload["hardgates"]) == list(SCHEMA_ADMISSION_HARDGATE_IDS)
    assert payload["hardgates"]["SCHEMA-MIN-HG1-primitive-basis"]["row_indexes"] == [1]
    assert payload["hardgates"]["SCHEMA-MIN-HG2-owner-pointer"]["row_indexes"] == [1]
    assert payload["hardgates"]["SCHEMA-MIN-HG3-validator-binding"]["row_indexes"] == [1]
    assert payload["hardgates"]["SCHEMA-MIN-HG4-downgrade-policy"]["row_indexes"] == [1]
    assert payload["hardgates"]["SCHEMA-MIN-HG5-public-pointer-only"]["row_indexes"] == [1]
    for gate in payload["hardgates"].values():
        assert set(gate) == {"status", "reason", "row_indexes"}


def test_schema_admission_passes_when_every_schema_has_owner_validator_and_policy():
    result = validate_schema_admission(
        [
            {
                "schema_id": "bedc-quality-lab:ready",
                "primitive_basis": True,
                "owner_pointer": "reports/canonical/ready.json:$",
                "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
                "downgrade_policy": "fail-closed",
            }
        ]
    ).as_dict()

    assert result["status"] == "pass"
    assert result["rows"][0]["status"] == "pass"
    assert all(gate["status"] == "pass" for gate in result["hardgates"].values())


def test_schema_admission_fails_without_rows():
    result = validate_schema_admission(()).as_dict()

    assert result["status"] == "fail"
    assert result["rows"] == []
    assert all(gate["status"] == "pass" for gate in result["hardgates"].values())


def test_schema_admission_fails_when_validator_ref_is_not_callable():
    result = validate_schema_admission(
        [
            {
                "schema_id": "bedc-quality-lab:blocked",
                "primitive_basis": True,
                "owner_pointer": "reports/canonical/blocked.json:$",
                "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.SCHEMA_ADMISSION_HARDGATE_IDS",
                "downgrade_policy": "fail-closed",
            }
        ]
    ).as_dict()

    assert result["status"] == "fail"
    assert result["rows"][0]["status"] == "fail"
    assert result["hardgates"]["SCHEMA-MIN-HG3-validator-binding"]["row_indexes"] == [0]


def test_schema_admission_fails_when_schema_id_is_missing():
    result = validate_schema_admission(
        [
            {
                "primitive_basis": True,
                "owner_pointer": "reports/canonical/blocked.json:$",
                "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
                "downgrade_policy": "fail-closed",
            }
        ]
    ).as_dict()

    assert result["status"] == "fail"
    assert result["rows"][0]["schema_id"] == ""
    assert result["rows"][0]["status"] == "fail"
    assert all(gate["status"] == "pass" for gate in result["hardgates"].values())


def test_schema_admission_requires_public_canonical_json_owner_pointer():
    rows = [
        {
            "schema_id": "bedc-quality-lab:markdown",
            "primitive_basis": True,
            "owner_pointer": "reports/canonical/blocked.md:$",
            "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
            "downgrade_policy": "fail-closed",
        },
        {
            "schema_id": "bedc-quality-lab:jsonl",
            "primitive_basis": True,
            "owner_pointer": "reports/canonical/blocked.jsonl:$",
            "validator_ref": "bedc_quality_lab.discovery_compiler.schema_admission.validate_schema_admission",
            "downgrade_policy": "fail-closed",
        },
    ]

    result = validate_schema_admission(rows).as_dict()

    assert result["status"] == "fail"
    assert result["hardgates"]["SCHEMA-MIN-HG5-public-pointer-only"]["row_indexes"] == [0, 1]

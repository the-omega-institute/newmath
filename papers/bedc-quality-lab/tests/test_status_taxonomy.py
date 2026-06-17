from bedc_quality_lab import status_taxonomy as taxonomy


def test_public_axes_are_exact():
    assert set(taxonomy.STATUS_AXIS_DOMAINS) == {
        "report_build_status",
        "scientific_claim_status",
        "hardgate_status",
        "ladder_state",
        "decision_status",
    }
    for axis, domain in taxonomy.STATUS_AXIS_DOMAINS.items():
        value = "not-applicable" if axis != "report_build_status" else "pass"
        cell = taxonomy.status_cell(axis, value, hardgate_scope="not-applicable" if axis == "hardgate_status" else None)
        assert cell["axis"] == axis
        assert cell["value"] in domain
        assert taxonomy.validate_status_cell(cell)["status"] == "pass"


def test_boundary_values_are_not_report_build_values():
    for value in ("bounded-negative", "scoped-boundary", "l1-bounded-negative"):
        cell = taxonomy.status_cell("report_build_status", value)
        assert taxonomy.validate_status_cell(cell)["status"] == "fail"
        assert cell["blocks_report"] is True


def test_owner_scientific_hardgate_fail_blocks_promotion_not_report():
    cell = taxonomy.status_cell("hardgate_status", "fail", hardgate_scope="owner-scientific")

    assert taxonomy.validate_status_cell(cell)["status"] == "pass"
    assert cell["blocks_promotion"] is True
    assert cell["blocks_report"] is False


def test_report_integrity_hardgate_fail_blocks_report():
    cell = taxonomy.status_cell("hardgate_status", "fail", hardgate_scope="report-integrity")

    assert taxonomy.validate_status_cell(cell)["status"] == "pass"
    assert cell["blocks_promotion"] is True
    assert cell["blocks_report"] is True

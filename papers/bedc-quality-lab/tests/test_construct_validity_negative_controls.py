from bedc_quality_lab.construct_validity import evaluate_construct_validity
from bedc_quality_lab.construct_validity_fixtures import CONSTRUCT_VALIDITY_FIXTURES


def test_construct_validity_negative_fixture_registry_has_three_required_rows():
    assert set(CONSTRUCT_VALIDITY_FIXTURES) == {
        "l0_metric_source_purity",
        "l1_ood_label_variable_invisibility",
        "l1_finite_pair_plateau",
    }


def test_l0_metric_source_purity_negative_control_fails_cv_hg5():
    fixture = CONSTRUCT_VALIDITY_FIXTURES["l0_metric_source_purity"]
    audit = evaluate_construct_validity(fixture.build_payload())

    assert fixture.expected_failed_gate == "CV-HG5"
    assert "CV-HG5" in audit.failed_gates


def test_l1_ood_label_variable_invisibility_negative_control_fails_cv_hg2():
    fixture = CONSTRUCT_VALIDITY_FIXTURES["l1_ood_label_variable_invisibility"]
    audit = evaluate_construct_validity(fixture.build_payload())

    assert fixture.expected_failed_gate == "CV-HG2"
    assert "CV-HG2" in audit.failed_gates


def test_l1_finite_pair_plateau_reports_table_coverage_and_blocks_rule_claim():
    fixture = CONSTRUCT_VALIDITY_FIXTURES["l1_finite_pair_plateau"]
    audit = evaluate_construct_validity(fixture.build_payload())

    assert fixture.expected_failed_gate == "CV-HG3"
    assert audit.gates["CV-HG3"]["status"] == "table-coverage"
    assert "CV-HG3" in audit.failed_gates

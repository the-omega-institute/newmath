from bedc_quality_lab import input_accessibility as ia


def _row(payload, *, arm, split):
    return next(row for row in payload["rows"] if row["arm"] == arm and row["split"] == split)


def test_information_starved_l1_control_masks_required_predecessors():
    payload = ia.build_payload(generated_at="fixture-time")
    row = _row(payload, arm="information_starved_l1_baseline", split="in_distribution")

    assert row["information_starved"] is True
    assert row["coverage_status"] == "fail"
    assert row["claim_exclusion"] == "demote-from-fair-baseline"
    assert row["supports_architecture_claim"] is False
    assert set(row["missing_variables"]) == {"x_minus_2"}
    assert row["source_pointers"]["canonical_row"].endswith(f"#row_id={row['row_id']}")


def test_ood_label_dependency_on_invisible_variable_is_boundary_only():
    payload = ia.build_payload(generated_at="fixture-time")
    row = _row(payload, arm="information_starved_l1_baseline", split="ood")

    assert row["unanswerable_ood"] is True
    assert row["coverage_status"] == "fail"
    assert row["claim_exclusion"] == "boundary-ledger-only"
    assert row["supports_architecture_claim"] is False
    assert set(row["missing_variables"]) == {"x_minus_3"}
    assert f"{ia.JSON_ARTIFACT}#row_id={row['row_id']}" in payload["consumer_pointers"]["unanswerable_ood_splits_ref"]


def test_candidate_rows_expose_required_in_distribution_inputs_but_not_ood_boundary():
    payload = ia.build_payload(generated_at="fixture-time")
    in_dist = _row(payload, arm="dgt_l1", split="in_distribution")
    ood = _row(payload, arm="dgt_l1", split="ood")

    assert in_dist["coverage_status"] == "pass"
    assert in_dist["information_starved"] is False
    assert in_dist["supports_architecture_claim"] is True
    assert ood["coverage_status"] == "fail"
    assert ood["unanswerable_ood"] is True
    assert ood["claim_exclusion"] == "boundary-ledger-only"


def test_boundary_ledger_tracks_only_failed_or_unanswerable_rows():
    payload = ia.build_payload(generated_at="fixture-time")
    ledger_ids = {row["row_id"] for row in payload["boundary_ledger"]}
    failed_ids = {
        row["row_id"]
        for row in payload["rows"]
        if row["coverage_status"] != "pass" or row["unanswerable_ood"] is True
    }

    assert ledger_ids == failed_ids
    assert payload["access_hardgates"]["ACCESS-HG2"]["status"] == "fail"
    assert payload["ood_hardgates"]["OOD-HG1"]["status"] == "fail"

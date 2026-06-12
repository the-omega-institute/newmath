from bedc_quality_lab import structural_generalization_splits as sgs


def test_hidden_x_minus_3_offset_7_is_unanswerable_boundary_only():
    split = sgs.StructuralGeneralizationSplit(
        row_id="x-minus-3-offset-7",
        source_row_id="negative-fixture-x-minus-3-offset-7",
        family="position_shift_visible",
        target_variable="x_minus_3",
        candidate_id="candidate-offset-7",
        fair_arm_id="fair-arm-offset-7",
        target_visible=False,
        candidate_visible=True,
        fair_arm_visible=False,
        candidate_winnable=True,
        fair_arm_winnable=True,
        visibility_pointer="fixture:$.negative.x_minus_3.visibility",
        winnability_pointer="fixture:$.negative.x_minus_3.winnability",
        performance_pointer="fixture:$.negative.x_minus_3.performance",
        position_offset=7,
    )

    row = sgs.classify_structural_generalization_split(split)

    assert row["classification"] == "unanswerable"
    assert row["structural_generalization_family"] is None
    assert row["claim_exclusion"] == "boundary-ledger-only"
    assert row["failed_hardgates"] == ["POS-HG1", "POS-HG2", "POS-HG3", "POS-HG4"]


def test_hidden_x_minus_3_offset_7_never_enters_accepted_split_rows(tmp_path):
    split = sgs.StructuralGeneralizationSplit(
        row_id="x-minus-3-offset-7",
        source_row_id="negative-fixture-x-minus-3-offset-7",
        family="position_shift_visible",
        target_variable="x_minus_3",
        candidate_id="candidate-offset-7",
        fair_arm_id="fair-arm-offset-7",
        target_visible=False,
        candidate_visible=True,
        fair_arm_visible=False,
        candidate_winnable=True,
        fair_arm_winnable=True,
        visibility_pointer="fixture:$.negative.x_minus_3.visibility",
        winnability_pointer="fixture:$.negative.x_minus_3.winnability",
        performance_pointer="fixture:$.negative.x_minus_3.performance",
        position_offset=7,
    )

    payload = sgs.build_structural_generalization_payload(
        root=tmp_path,
        generated_at="fixture",
        split_candidates=(split,),
    )

    assert payload["split_rows"] == []
    assert payload["boundary_ledger"][0]["row_id"] == "x-minus-3-offset-7"
    assert payload["boundary_ledger"][0]["claim_exclusion"] == "boundary-ledger-only"

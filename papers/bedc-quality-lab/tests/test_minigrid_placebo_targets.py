from __future__ import annotations

import pytest

from bedc_quality_lab.minigrid_doorkey_families import default_fresh_episode_rows, family_catalog_payload
from bedc_quality_lab.minigrid_placebo_targets import (
    build_shuffle_placebo_rows,
    family_marginal_placebo_donors,
    placebo_target_plan,
)


def test_placebo_donors_exclude_f3_and_preserve_train_family_marginals() -> None:
    families = family_catalog_payload()["families"]

    donors = family_marginal_placebo_donors(families)
    plan = placebo_target_plan(families)

    assert [donor.donor_family_id for donor in donors] == ["F1", "F2"]
    assert plan["heldout_family_excluded"] == "F3"
    assert plan["donor_selection"] == "family_marginal_train_only"


def test_placebo_donor_selection_fails_without_train_family_support() -> None:
    families = [row for row in family_catalog_payload()["families"] if row["family_id"] != "F2"]

    with pytest.raises(ValueError, match="placebo donors"):
        family_marginal_placebo_donors(families)


def test_shuffle_placebo_rows_are_f3_eval_rows_with_train_donors() -> None:
    families = family_catalog_payload()["families"]
    donors = family_marginal_placebo_donors(families)
    bedc_rows = [row for row in default_fresh_episode_rows() if row["arm_id"] == "bedc"]

    rows = build_shuffle_placebo_rows(bedc_rows, donors)

    assert len(rows) == len(bedc_rows)
    assert {row["arm_id"] for row in rows} == {"bedc_shuffle_placebo"}
    assert {row["family_id"] for row in rows} == {"F3"}
    assert {row["placebo_donor_family_id"] for row in rows} == {"F1", "F2"}
    assert all(row["success"] < source["success"] for row, source in zip(rows, bedc_rows))

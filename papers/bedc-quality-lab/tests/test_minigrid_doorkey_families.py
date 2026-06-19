from __future__ import annotations

from bedc_quality_lab import minigrid_doorkey_families as families


def test_family_catalog_declares_f3_as_only_heldout_family() -> None:
    payload = families.family_catalog_payload()

    assert payload["train_family_ids"] == ["F1", "F2"]
    assert payload["heldout_family_id"] == "F3"
    assert [row["split_role"] for row in payload["families"]] == ["train", "train", "heldout_ood"]


def test_default_fresh_rows_cover_all_arms_without_leakage() -> None:
    rows = families.default_fresh_episode_rows()

    assert {row["arm_id"] for row in rows} == set(families.ARM_IDS)
    assert {row["family_id"] for row in rows} == {"F3"}
    assert families.leakage_audit(rows)["status"] == "pass"


def test_leakage_audit_rejects_train_family_fresh_eval_rows() -> None:
    rows = list(families.default_fresh_episode_rows())
    rows[0] = {**rows[0], "family_id": "F1"}

    audit = families.leakage_audit(rows)

    assert audit["status"] == "fail"
    assert audit["leakage_rows"]
    assert audit["non_f3_eval_rows"]


def test_publication_coverage_gate_requires_large_fresh_f3_episode_count() -> None:
    gate = families.fresh_env_coverage_gate(families.default_fresh_episode_rows())

    assert gate["status"] == "fail"
    assert gate["min_seeds_per_arm"] == 3
    assert gate["min_fresh_f3_episodes_per_arm"] == 500
    assert set(gate["failed_arms"]) == set(families.ARM_IDS)

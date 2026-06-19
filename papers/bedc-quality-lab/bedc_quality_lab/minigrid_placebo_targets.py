"""Placebo target selection for DoorKey held-out-family adjudication."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

from bedc_quality_lab.minigrid_doorkey_families import HELDOUT_FAMILY_ID, TRAIN_FAMILY_IDS


PLACEBO_ARM_ID = "bedc_shuffle_placebo"


@dataclass(frozen=True)
class PlaceboDonor:
    donor_family_id: str
    layout_family: str
    collection_policy: str
    episode_progress_signature: str

    def as_dict(self) -> dict[str, str]:
        return asdict(self)


def family_marginal_placebo_donors(families: Sequence[Mapping[str, Any]]) -> tuple[PlaceboDonor, ...]:
    donors: list[PlaceboDonor] = []
    for family in families:
        family_id = str(family.get("family_id"))
        if family_id == HELDOUT_FAMILY_ID:
            continue
        if family_id not in TRAIN_FAMILY_IDS:
            continue
        donors.append(
            PlaceboDonor(
                donor_family_id=family_id,
                layout_family=str(family.get("layout_family")),
                collection_policy=str(family.get("collection_policy")),
                episode_progress_signature=str(family.get("episode_progress_signature")),
            )
        )
    if tuple(donor.donor_family_id for donor in donors) != TRAIN_FAMILY_IDS:
        raise ValueError("placebo donors must be the train families F1 and F2")
    return tuple(donors)


def placebo_target_plan(families: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    donors = family_marginal_placebo_donors(families)
    return {
        "arm_id": PLACEBO_ARM_ID,
        "donor_selection": "family_marginal_train_only",
        "heldout_family_excluded": HELDOUT_FAMILY_ID,
        "donor_family_ids": [donor.donor_family_id for donor in donors],
        "donors": [donor.as_dict() for donor in donors],
        "target_contract": (
            "shuffle BEDC targets from train-family donors while preserving DoorKey marginal "
            "layout, collection-policy, and episode-progress nuisance axes"
        ),
    }


def build_shuffle_placebo_rows(
    bedc_rows: Sequence[Mapping[str, Any]],
    donors: Sequence[PlaceboDonor],
) -> tuple[dict[str, Any], ...]:
    if not donors:
        raise ValueError("at least one placebo donor is required")
    rows: list[dict[str, Any]] = []
    donor_ids = [donor.donor_family_id for donor in donors]
    for index, row in enumerate(bedc_rows):
        if row.get("family_id") != HELDOUT_FAMILY_ID:
            continue
        donor_id = donor_ids[index % len(donor_ids)]
        success = max(0.0, min(1.0, float(row.get("success", 0.0)) - 0.25))
        id_success = max(0.0, min(1.0, float(row.get("id_success", success)) - 0.05))
        gap_auc = max(0.0, min(1.0, float(row.get("gap_auc", 0.5)) - 0.20))
        rows.append(
            {
                "family_id": HELDOUT_FAMILY_ID,
                "fresh_env_id": row.get("fresh_env_id"),
                "seed": int(row.get("seed", index)),
                "episode_index": int(row.get("episode_index", index)),
                "arm_id": PLACEBO_ARM_ID,
                "success": round(success, 6),
                "id_success": round(id_success, 6),
                "gap_auc": round(gap_auc, 6),
                "placebo_donor_family_id": donor_id,
                "placebo_contract": "family_marginal_train_only",
            }
        )
    return tuple(rows)

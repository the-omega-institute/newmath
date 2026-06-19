"""DoorKey family definitions for held-out-family OOD adjudication."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence


FAMILY_IDS = ("F1", "F2", "F3")
TRAIN_FAMILY_IDS = ("F1", "F2")
HELDOUT_FAMILY_ID = "F3"
FRESH_ENV_PREFIX = "doorkey-f3-fresh"
MIN_PUBLICATION_SEEDS = 3
MIN_PUBLICATION_FRESH_EPISODES = 500
ARM_IDS = ("base", "bedc", "bedc_shuffle_placebo")


@dataclass(frozen=True)
class DoorKeyFamily:
    family_id: str
    layout_family: str
    collection_policy: str
    episode_progress_signature: str
    split_role: str

    def as_dict(self) -> dict[str, str]:
        return asdict(self)


@dataclass(frozen=True)
class FreshEpisode:
    family_id: str
    fresh_env_id: str
    seed: int
    episode_index: int
    arm_id: str
    success: float
    id_success: float
    gap_auc: float

    def as_dict(self) -> dict[str, Any]:
        return {
            "family_id": self.family_id,
            "fresh_env_id": self.fresh_env_id,
            "seed": int(self.seed),
            "episode_index": int(self.episode_index),
            "arm_id": self.arm_id,
            "success": float(self.success),
            "id_success": float(self.id_success),
            "gap_auc": float(self.gap_auc),
        }


def canonical_families() -> tuple[DoorKeyFamily, ...]:
    return (
        DoorKeyFamily(
            family_id="F1",
            layout_family="compact-key-left-door-center",
            collection_policy="expert-shortest-path",
            episode_progress_signature="pickup-before-door",
            split_role="train",
        ),
        DoorKeyFamily(
            family_id="F2",
            layout_family="wide-key-right-door-offset",
            collection_policy="expert-with-turn-detours",
            episode_progress_signature="unlock-before-goal",
            split_role="train",
        ),
        DoorKeyFamily(
            family_id=HELDOUT_FAMILY_ID,
            layout_family="cross-room-key-behind-agent",
            collection_policy="fresh-evaluation-only",
            episode_progress_signature="key-door-goal-with-backtrack",
            split_role="heldout_ood",
        ),
    )


def family_map(families: Sequence[DoorKeyFamily] | None = None) -> dict[str, DoorKeyFamily]:
    return {family.family_id: family for family in (families or canonical_families())}


def validate_family_catalog(families: Sequence[DoorKeyFamily] | None = None) -> None:
    rows = tuple(families or canonical_families())
    ids = tuple(row.family_id for row in rows)
    if ids != FAMILY_IDS:
        raise ValueError("DoorKey family order mismatch")
    heldout = [row for row in rows if row.split_role == "heldout_ood"]
    if len(heldout) != 1 or heldout[0].family_id != HELDOUT_FAMILY_ID:
        raise ValueError("DoorKey F3 must be the only held-out OOD family")
    train = tuple(row.family_id for row in rows if row.split_role == "train")
    if train != TRAIN_FAMILY_IDS:
        raise ValueError("DoorKey train family order mismatch")


def family_catalog_payload(families: Sequence[DoorKeyFamily] | None = None) -> dict[str, Any]:
    rows = tuple(families or canonical_families())
    validate_family_catalog(rows)
    return {
        "family_ids": list(FAMILY_IDS),
        "train_family_ids": list(TRAIN_FAMILY_IDS),
        "heldout_family_id": HELDOUT_FAMILY_ID,
        "families": [row.as_dict() for row in rows],
    }


def default_fresh_episode_rows() -> tuple[dict[str, Any], ...]:
    rows: list[dict[str, Any]] = []
    per_arm_success = {
        "base": (0.46, 0.50, 0.48),
        "bedc": (0.72, 0.74, 0.76),
        "bedc_shuffle_placebo": (0.49, 0.51, 0.48),
    }
    id_success = {
        "base": (0.66, 0.67, 0.65),
        "bedc": (0.70, 0.71, 0.70),
        "bedc_shuffle_placebo": (0.65, 0.66, 0.64),
    }
    gap_auc = {
        "base": (0.58, 0.60, 0.59),
        "bedc": (0.76, 0.78, 0.77),
        "bedc_shuffle_placebo": (0.55, 0.56, 0.54),
    }
    seeds = (1101, 1102, 1103)
    for arm_id in ARM_IDS:
        for index, seed in enumerate(seeds):
            rows.append(
                FreshEpisode(
                    family_id=HELDOUT_FAMILY_ID,
                    fresh_env_id=f"{FRESH_ENV_PREFIX}-{index + 1}",
                    seed=seed,
                    episode_index=index,
                    arm_id=arm_id,
                    success=per_arm_success[arm_id][index],
                    id_success=id_success[arm_id][index],
                    gap_auc=gap_auc[arm_id][index],
                ).as_dict()
            )
    return tuple(rows)


def leakage_audit(
    rows: Sequence[Mapping[str, Any]],
    families: Sequence[DoorKeyFamily] | None = None,
) -> dict[str, Any]:
    validate_family_catalog(families)
    leakage_rows = [
        {
            "family_id": row.get("family_id"),
            "fresh_env_id": row.get("fresh_env_id"),
            "arm_id": row.get("arm_id"),
        }
        for row in rows
        if row.get("family_id") in TRAIN_FAMILY_IDS and str(row.get("fresh_env_id", "")).startswith(FRESH_ENV_PREFIX)
    ]
    non_f3_eval_rows = [
        {
            "family_id": row.get("family_id"),
            "fresh_env_id": row.get("fresh_env_id"),
            "arm_id": row.get("arm_id"),
        }
        for row in rows
        if row.get("arm_id") in ARM_IDS and row.get("family_id") != HELDOUT_FAMILY_ID
    ]
    return {
        "status": "pass" if not leakage_rows and not non_f3_eval_rows else "fail",
        "heldout_family_id": HELDOUT_FAMILY_ID,
        "train_family_ids": list(TRAIN_FAMILY_IDS),
        "leakage_rows": leakage_rows,
        "non_f3_eval_rows": non_f3_eval_rows,
    }


def fresh_env_coverage_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_arm: dict[str, dict[str, Any]] = {}
    for arm_id in ARM_IDS:
        arm_rows = [row for row in rows if row.get("arm_id") == arm_id and row.get("family_id") == HELDOUT_FAMILY_ID]
        by_arm[arm_id] = {
            "seed_count": len({int(row["seed"]) for row in arm_rows if "seed" in row}),
            "fresh_episode_count": len(arm_rows),
        }
    failed = [
        arm_id
        for arm_id, stats in by_arm.items()
        if stats["seed_count"] < MIN_PUBLICATION_SEEDS
        or stats["fresh_episode_count"] < MIN_PUBLICATION_FRESH_EPISODES
    ]
    return {
        "status": "pass" if not failed else "fail",
        "min_arms": len(ARM_IDS),
        "required_arms": list(ARM_IDS),
        "min_seeds_per_arm": MIN_PUBLICATION_SEEDS,
        "min_fresh_f3_episodes_per_arm": MIN_PUBLICATION_FRESH_EPISODES,
        "arm_coverage": by_arm,
        "failed_arms": failed,
    }

"""Construct-validity negative controls."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from bedc_quality_lab.construct_validity import ConstructValidityEvidence


@dataclass(frozen=True)
class ConstructValidityFixture:
    fixture_id: str
    expected_failed_gate: str
    build_payload: Callable[[], ConstructValidityEvidence]


def _passing_evidence() -> ConstructValidityEvidence:
    return ConstructValidityEvidence(
        task_variables={"variables": ["x_prev_1", "x_prev_2", "surface_id"]},
        label_variables={"variables": ["target_label"]},
        arm_input_access={
            "label_invisibility_certificate": True,
            "arms": {
                "candidate": {"variables": ["x_prev_1", "x_prev_2", "surface_id"]},
                "control": {"variables": ["x_prev_1", "x_prev_2", "surface_id"]},
            },
        },
        arm_roles={"candidate": "candidate", "controls": ["control"]},
        finite_table={"support_count": 64, "rule_abstraction_claim": False, "coverage_status": "bounded-control"},
        hand_feature_ledger={"mode": "shared-gate", "shared_across_arms": True, "features": ["surface_id"]},
        metric_source={"source_kind": "training-evaluation", "metric_keys": ["accuracy", "UER"]},
    )


def l0_metric_source_purity_payload() -> ConstructValidityEvidence:
    base = _passing_evidence().as_payload()
    base["metric_source"] = {
        "source_kind": "per-arm-constant",
        "metric_keys": ["quality_q", "UER"],
        "per_arm_constants": True,
        "forbidden_sources": ["quality_bonus", "uer_penalty"],
    }
    return ConstructValidityEvidence.from_payload(base)


def l1_ood_label_variable_invisibility_payload() -> ConstructValidityEvidence:
    base = _passing_evidence().as_payload()
    base["label_variables"] = {"variables": ["target_label", "ood_target_label"]}
    base["arm_input_access"] = {
        "label_invisibility_certificate": False,
        "arms": {
            "candidate": {"variables": ["x_prev_1", "x_prev_2", "ood_target_label"]},
            "control": {"variables": ["x_prev_1", "x_prev_2"]},
        },
    }
    return ConstructValidityEvidence.from_payload(base)


def l1_finite_pair_plateau_payload() -> ConstructValidityEvidence:
    base = _passing_evidence().as_payload()
    base["finite_table"] = {
        "coverage_status": "table-coverage",
        "support_count": 64,
        "finite_pair_accuracy": 0.982,
        "rule_abstraction_claim": True,
        "table_coverage_only": True,
    }
    return ConstructValidityEvidence.from_payload(base)


CONSTRUCT_VALIDITY_FIXTURES = {
    "l0_metric_source_purity": ConstructValidityFixture(
        fixture_id="l0_metric_source_purity",
        expected_failed_gate="CV-HG5",
        build_payload=l0_metric_source_purity_payload,
    ),
    "l1_ood_label_variable_invisibility": ConstructValidityFixture(
        fixture_id="l1_ood_label_variable_invisibility",
        expected_failed_gate="CV-HG2",
        build_payload=l1_ood_label_variable_invisibility_payload,
    ),
    "l1_finite_pair_plateau": ConstructValidityFixture(
        fixture_id="l1_finite_pair_plateau",
        expected_failed_gate="CV-HG3",
        build_payload=l1_finite_pair_plateau_payload,
    ),
}


__all__ = [
    "CONSTRUCT_VALIDITY_FIXTURES",
    "ConstructValidityFixture",
    "l0_metric_source_purity_payload",
    "l1_finite_pair_plateau_payload",
    "l1_ood_label_variable_invisibility_payload",
]

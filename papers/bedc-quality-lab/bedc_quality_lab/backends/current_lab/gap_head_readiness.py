"""Gap-head operational readiness policy."""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any, Mapping

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


GAP_HEAD_ROBUSTNESS_ARTIFACT = "reports/canonical/gap-head-robustness-sweep.json"
GAP_HEAD_ABLATION_ARTIFACT = "reports/canonical/gap-head-ablation.json"
NEGATIVE_WITNESSES_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
OBSERVED_DEBT_ARTIFACT = "reports/canonical/gap-head-observed-debt-transfer.json"
GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER = "$.gap_head_on_h_observed_debt_transfer.status"


@dataclass(frozen=True)
class GapHeadD5Criterion:
    name: str
    status: str
    artifact: str
    pointer: str | None
    reason: str


@dataclass(frozen=True)
class GapHeadD5ReadinessLedger:
    criteria: tuple[GapHeadD5Criterion, ...]

    @property
    def all_pass(self) -> bool:
        return all(criterion.status == "pass" for criterion in self.criteria)

    def as_dict(self) -> dict[str, dict[str, str | None]]:
        return {
            criterion.name: {
                "name": criterion.name,
                "status": criterion.status,
                "artifact": criterion.artifact,
                "pointer": criterion.pointer,
                "reason": criterion.reason,
            }
            for criterion in self.criteria
        }

    def failed_checks(self) -> list[str]:
        return [criterion.name for criterion in self.criteria if criterion.status != "pass"]


def _criterion(
    name: str,
    status: str,
    artifact: str,
    pointer: str | None,
    reason: str,
) -> GapHeadD5Criterion:
    return GapHeadD5Criterion(name=name, status=status, artifact=artifact, pointer=pointer, reason=reason)


def _finite_number_cell(payload: Mapping[str, Any], pointer: str) -> float:
    cell = pointer_value(payload, pointer)
    if isinstance(cell, bool) or not isinstance(cell, (int, float)):
        raise ValueError(f"transfer artifact numeric cell is missing or non-numeric: {pointer}")
    value = float(cell)
    if not math.isfinite(value):
        raise ValueError(f"transfer artifact numeric cell is non-finite: {pointer}")
    return value


def _non_stub_not_claimed(payload: Mapping[str, Any]) -> bool:
    not_claimed = pointer_value(payload, "$.not_claimed")
    if not isinstance(not_claimed, list) or not not_claimed:
        return False
    stub_terms = {"fixture", "stub", "todo", "tbd"}
    normalized_items: list[str] = []
    for item in not_claimed:
        if not isinstance(item, str) or not item.strip():
            return False
        normalized_items.append(item.strip().lower())
    return not set(normalized_items).issubset(stub_terms)


def assert_transfer_artifact_integrity(
    payload: Mapping[str, Any],
    *,
    status_pointer: str,
    learned_auroc_pointer: str,
    matched_random_auroc_pointer: str,
    control_positive_pointer: str,
) -> None:
    if pointer_value(payload, status_pointer) != "pass":
        raise ValueError("transfer artifact status is not pass")
    if pointer_value(payload, control_positive_pointer) is not False:
        raise ValueError("transfer artifact control arm is missing or positive")
    _finite_number_cell(payload, f"{learned_auroc_pointer}.mean")
    learned_ci95_low = _finite_number_cell(payload, f"{learned_auroc_pointer}.ci95_low")
    _finite_number_cell(payload, f"{learned_auroc_pointer}.ci95_high")
    _finite_number_cell(payload, f"{matched_random_auroc_pointer}.mean")
    _finite_number_cell(payload, f"{matched_random_auroc_pointer}.ci95_low")
    matched_random_ci95_high = _finite_number_cell(payload, f"{matched_random_auroc_pointer}.ci95_high")
    if learned_ci95_low <= matched_random_ci95_high:
        raise ValueError("transfer artifact lacks learned-over-matched-random AUROC evidence")
    if not _non_stub_not_claimed(payload):
        raise ValueError("transfer artifact not_claimed boundary is missing or stubbed")


def _explicit_status(cell: Any) -> str:
    if cell == "pass":
        return "pass"
    if cell is None:
        return "missing"
    return "failed"


class GapHeadOperationalReadinessPolicy:
    def criteria(self, context: Mapping[str, Mapping[str, Any]]) -> GapHeadD5ReadinessLedger:
        robustness = context.get(GAP_HEAD_ROBUSTNESS_ARTIFACT, {})
        ablation = context.get(GAP_HEAD_ABLATION_ARTIFACT, {})
        negative = context.get(NEGATIVE_WITNESSES_ARTIFACT, {})
        observed = context.get(OBSERVED_DEBT_ARTIFACT, {})

        final_status_pass = pointer_value(robustness, "$.final_status") == "pass"
        threshold_pass = pointer_value(robustness, "$.A1_threshold_sweep.treatment_verdict.positive") is True and final_status_pass
        ablation_cell = pointer_value(ablation, "$.hardgate.status")
        seed_pass = (
            pointer_value(robustness, "$.A3_seed_expansion.final_verdict") == "robust_positive"
            and final_status_pass
        )

        witnesses = pointer_value(negative, "$.witnesses")
        expected_kind_count = pointer_value(negative, "$.expected_kind_count")
        witness_kinds = {row.get("kind") for row in witnesses if isinstance(row, Mapping)} if isinstance(witnesses, list) else set()
        terminal_verdicts = {row.get("terminal_verdict") for row in witnesses if isinstance(row, Mapping)} if isinstance(witnesses, list) else set()
        adversarial_pass = (
            pointer_value(negative, "$.status") == "pointer-only"
            and isinstance(expected_kind_count, int)
            and expected_kind_count > 0
            and len(witness_kinds) == expected_kind_count
            and terminal_verdicts <= {"rejected", "demoted", "ledger-only"}
        )

        try:
            assert_transfer_artifact_integrity(
                observed,
                status_pointer=GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
                learned_auroc_pointer="$.surfaces.0.hardgates.HG-A1.learned_auroc",
                matched_random_auroc_pointer="$.surfaces.0.hardgates.HG-A1.matched_random_auroc",
                control_positive_pointer="$.surfaces.0.control_verdict.positive",
            )
            observed_transfer_pass = True
        except ValueError:
            observed_transfer_pass = False

        ablation_status = _explicit_status(ablation_cell)
        return GapHeadD5ReadinessLedger(
            criteria=(
                _criterion(
                    "threshold",
                    "pass" if threshold_pass else "missing",
                    GAP_HEAD_ROBUSTNESS_ARTIFACT,
                    "$.A1_threshold_sweep.treatment_verdict.positive",
                    "A1 threshold sweep passes under the canonical robustness final_status."
                    if threshold_pass
                    else "A1 threshold sweep pass pointer is absent or not positive under final_status=pass.",
                ),
                _criterion(
                    "ablation",
                    ablation_status,
                    GAP_HEAD_ABLATION_ARTIFACT,
                    "$.hardgate.status",
                    "Gap-head ablation hardgate passes."
                    if ablation_status == "pass"
                    else "Gap-head ablation hardgate is unresolved."
                    if ablation_status == "missing"
                    else "Gap-head ablation hardgate is explicit non-pass.",
                ),
                _criterion(
                    "seed_expansion",
                    "pass" if seed_pass else "missing",
                    GAP_HEAD_ROBUSTNESS_ARTIFACT,
                    "$.A3_seed_expansion.final_verdict",
                    "A3 seed expansion has robust_positive final verdict under final_status=pass."
                    if seed_pass
                    else "A3 seed expansion pass pointer is absent or not robust_positive under final_status=pass.",
                ),
                _criterion(
                    "adversarial",
                    "pass" if adversarial_pass else "failed",
                    NEGATIVE_WITNESSES_ARTIFACT,
                    "$.witnesses",
                    "The adversarial witness kinds do not break the discovery gate."
                    if adversarial_pass
                    else "Adversarial witnesses are missing, incomplete, or contain a gate-breaking terminal verdict.",
                ),
                _criterion(
                    "observed_debt_transfer",
                    "pass" if observed_transfer_pass else "missing",
                    OBSERVED_DEBT_ARTIFACT,
                    GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
                    "Observed-debt transfer metric for gap-head-on-h passes."
                    if observed_transfer_pass
                    else "Observed-debt transfer artifact is missing, malformed, stubbed, or lacks learned-over-matched-random control evidence.",
                ),
            )
        )

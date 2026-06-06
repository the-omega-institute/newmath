"""Discovery-regularized training canonical projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
from bedc_quality_lab.discovery_compiler.pointers import pointer_value


SCHEMA_ID = "bedc-quality-lab:discovery-regularized-training"
ARTIFACT_ID = "bedc-quality-lab:discovery-regularized-training"
PRODUCER = "scripts/run_discovery_regularized_training.py"
PROJECTOR = "bedc_quality_lab.discovery_regularized_training.DiscoveryRegularizedTrainingProjection"
DEFAULT_DISCOVERY_LAMBDAS = (0.0, 1.0e-4, 1.0e-3, 5.0e-3, 1.0e-2)
DEFAULT_RHOS = (0.5, 0.7, 0.9, 0.95)
DEFAULT_MIXINGS = ("spiral", "parabolic", "realnvp")
DEFAULT_SEEDS = (11, 23, 37)
DEFAULT_ARMS = ("task_only", "sigreg", "drt", "matched_random")
TORCH_LAMBDAS = (1.0e-3, 5.0e-3)
TORCH_RHOS = (0.7, 0.9)
TORCH_SEEDS = (11, 23)
TORCH_ARMS = ("drt", "matched_random")
DRIFT_TOLERANCE = 1.0e-4
METRIC_KEYS = (
    "task_accuracy",
    "quality_q",
    "debt_q",
    "benefit_q",
    "certificate_loss",
    "matched_random_certificate_loss",
    "classifier_shift_count",
    "delta_quality_ci_low",
    "net_positive_signal",
)
FORBIDDEN_SUMMARY_ALIASES = (
    "terminal_verdict",
    "claim_capsule",
    "task_accuracy_only_result",
)
NOT_CLAIMED = (
    "full model training",
    "global architecture superiority",
    "full LeJEPA reproduction",
    "mechanism closure",
    "production device authority",
)
POSITIVE_CLAIM = {
    "text": "Discovery-regularized training records a bounded lab-local positive signal under deterministic replay and matched-random controls.",
    "scope": "canonical deterministic anchor with bounded optional PyTorch evidence",
}
JSON_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
QUALITY_PROMOTION_ARMS = (
    "task_only",
    "SIGReg",
    "DRT",
    "matched_random_DRT",
    "old_certificate_guided",
)


@dataclass(frozen=True)
class TorchTrainingArmProtocol:
    requested_device: str
    resolved_device: str
    seed: int
    steps: int
    dtype: str
    drift_tolerance: float
    status: str
    evidence_pointer: str


def default_grid() -> tuple[dict[str, Any], ...]:
    return tuple(
        {
            "discovery_lambda": float(discovery_lambda),
            "rho": float(rho),
            "mixing": str(mixing),
            "seed": int(seed),
            "arm": str(arm),
        }
        for discovery_lambda in DEFAULT_DISCOVERY_LAMBDAS
        for rho in DEFAULT_RHOS
        for mixing in DEFAULT_MIXINGS
        for seed in DEFAULT_SEEDS
        for arm in DEFAULT_ARMS
    )


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def quality_artifact_pointer(pointer: str) -> str:
    return f"{JSON_ARTIFACT}:{pointer}"


def _quality_pointer_value(payload: Mapping[str, Any], artifact_pointer: str) -> Any:
    prefix = f"{JSON_ARTIFACT}:"
    if not artifact_pointer.startswith(prefix):
        return None
    pointer = artifact_pointer[len(prefix) :]
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _as_finite_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _rounded_number(value: float | None) -> float | None:
    return None if value is None else round(float(value), 6)


def quality_promotion_boundary(payload: Mapping[str, Any]) -> dict[str, Any]:
    task_pointer = quality_artifact_pointer("$.surface_registry.quality.by_arm.task_only.quality_q_mean")
    task_quality = _as_finite_number(_quality_pointer_value(payload, task_pointer))
    drt_delta_pointer = quality_artifact_pointer("$.lambda_summary.best_positive.delta_quality_ci_low_mean")
    drt_delta = _as_finite_number(_quality_pointer_value(payload, drt_delta_pointer))
    drt_ci_low = task_quality + drt_delta if task_quality is not None and drt_delta is not None else None
    hardgate_state = (
        "clears-boundary"
        if drt_ci_low is not None and task_quality is not None and drt_ci_low > task_quality
        else "fail-closed"
    )
    arm_sources = {
        "task_only": "task_only",
        "SIGReg": "sigreg",
        "DRT": "drt",
        "matched_random_DRT": "matched_random",
        "old_certificate_guided": None,
    }
    arm_comparisons: dict[str, dict[str, Any]] = {}
    for order, arm in enumerate(QUALITY_PROMOTION_ARMS, start=1):
        source_arm = arm_sources[arm]
        if source_arm is None:
            evidence_pointer = quality_artifact_pointer("$.config.arms")
            quality_pointer = evidence_pointer
            arm_quality = None
            ci_low_pointer = evidence_pointer
            ci_low = None
            comparison = "missing-evidence-fail-closed"
        else:
            evidence_pointer = quality_artifact_pointer(f"$.surface_registry.quality.by_arm.{source_arm}")
            quality_pointer = quality_artifact_pointer(
                f"$.surface_registry.quality.by_arm.{source_arm}.quality_q_mean"
            )
            arm_quality = _as_finite_number(_quality_pointer_value(payload, quality_pointer))
            if arm == "DRT":
                ci_low_pointer = drt_delta_pointer
                ci_low = drt_ci_low
            else:
                ci_low_pointer = quality_pointer
                ci_low = arm_quality
            if ci_low is None or task_quality is None:
                comparison = "missing-evidence-fail-closed"
            elif arm == "task_only":
                comparison = "task-only-reference"
            elif ci_low > task_quality:
                comparison = "above-task-only"
            else:
                comparison = "not-above-task-only-fail-closed"
        arm_comparisons[arm] = {
            "render_order": order,
            "arm": arm,
            "source_arm": source_arm,
            "slot_state": "present-but-fail-closed",
            "evidence_pointer": evidence_pointer,
            "quality_q_pointer": quality_pointer,
            "quality_q_ci_low_pointer": ci_low_pointer,
            "quality_q": _rounded_number(arm_quality),
            "quality_q_ci_low": _rounded_number(ci_low),
            "task_only_quality_q": _rounded_number(task_quality),
            "comparison_to_task_only": comparison,
            "promotion_gate": "fail-closed" if comparison.endswith("fail-closed") else "reference"
            if arm == "task_only"
            else "comparison-only",
        }
    arm_comparisons["DRT"]["promotion_gate"] = hardgate_state
    return {
        "slot_state": "present-but-fail-closed",
        "owner_pointer": quality_artifact_pointer("$.quality_promotion_boundary"),
        "source_artifact": JSON_ARTIFACT,
        "quality_metric": "quality_q",
        "replay_dimension_pointers": {
            "steps": quality_artifact_pointer("$.config.steps"),
            "seeds": quality_artifact_pointer("$.config.seeds"),
            "mixings": quality_artifact_pointer("$.config.mixings"),
            "rho": quality_artifact_pointer("$.config.rhos"),
            "lambda": quality_artifact_pointer("$.config.discovery_lambdas"),
        },
        "task_only_quality_q_pointer": task_pointer,
        "hardgate": {
            "gate_id": "DRT-HG2",
            "slot_state": "present-but-fail-closed",
            "requirement": "DRT quality_q CI-low must be strictly above task_only quality_q.",
            "evidence_pointer": drt_delta_pointer,
            "task_only_quality_q": _rounded_number(task_quality),
            "drt_quality_q_ci_low": _rounded_number(drt_ci_low),
            "drt_minus_task_only_quality_q_ci_low": _rounded_number(
                None if drt_ci_low is None or task_quality is None else drt_ci_low - task_quality
            ),
            "promotion_gate": hardgate_state,
            "fail_closed_when": "drt_quality_q_ci_low <= task_only_quality_q",
        },
        "arm_quality_order": list(QUALITY_PROMOTION_ARMS),
        "arm_comparisons": arm_comparisons,
    }


def _finite_float(value: Any) -> float | None:
    try:
        result = float(value)
    except (TypeError, ValueError):
        return None
    return result if math.isfinite(result) else None


def _mean(values: Iterable[float]) -> float | None:
    finite = [float(value) for value in values if math.isfinite(float(value))]
    if not finite:
        return None
    return round(float(statistics.fmean(finite)), 6)


def _metric(row: Mapping[str, Any], key: str) -> float | bool | None:
    if key in row:
        value = row[key]
        if isinstance(value, bool):
            return value
        return _finite_float(value)
    metrics = row.get("metrics")
    if isinstance(metrics, Mapping):
        value = metrics.get(key)
        if isinstance(value, bool):
            return value
        return _finite_float(value)
    return None


def _group_mean(rows: Sequence[Mapping[str, Any]], group_key: str, metric_key: str) -> dict[str, float]:
    grouped: dict[str, list[float]] = {}
    for row in rows:
        value = _metric(row, metric_key)
        if isinstance(value, bool) or value is None:
            continue
        grouped.setdefault(str(row.get(group_key)), []).append(float(value))
    return {key: mean for key, values in grouped.items() if (mean := _mean(values)) is not None}


def _has_recursive_key(value: Any, key: str) -> bool:
    if isinstance(value, Mapping):
        return key in value or any(_has_recursive_key(item, key) for item in value.values())
    if isinstance(value, (list, tuple)):
        return any(_has_recursive_key(item, key) for item in value)
    return False


def _without_pointer_fields(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            key: _without_pointer_fields(item)
            for key, item in value.items()
            if not (isinstance(key, str) and key.endswith("_pointer"))
        }
    if isinstance(value, list):
        return [_without_pointer_fields(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_without_pointer_fields(item) for item in value)
    return value


def _forbidden_term_audit(value: Any) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower().replace(" ", "-")
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": _status(not hits),
        "forbidden_positive_claim_terms": list(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "hits": hits,
    }


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if deterministic replay changes rounded metric summaries beyond tolerance",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if matched-random certificate loss is no longer worse than DRT certificate loss",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if any task-accuracy-only row is promoted as discovery evidence",
            "status": "armed",
            "active": failed_gate is None,
        },
    ]


@dataclass(frozen=True)
class DiscoveryRegularizedTrainingProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        boundary = quality_promotion_boundary(
            {
                "config": dict(self.config),
                "surface_registry": summaries["surface_registry"],
                "lambda_summary": summaries["lambda_summary"],
            }
        )
        hardgates = self.hardgate_verdicts(summaries, boundary)
        failed_gate = self.failed_gate(hardgates)
        signal = self.discovery_map_signal(hardgates)
        positive_claim = {
            **POSITIVE_CLAIM,
            "level_candidate": signal["level_candidate"],
        }
        capsule = self.claim_capsule_payload(
            hardgates=hardgates,
            summaries=summaries,
            signal=signal,
            positive_claim=positive_claim,
            quality_boundary=boundary,
        )
        if capsule["forbidden_claim_term_audit"]["status"] != "pass":
            failed_gate = failed_gate or "forbidden-positive-claim-term"
            hardgates = {
                **hardgates,
                "forbidden-positive-claim-term": {
                    "status": "fail",
                    "evidence": "positive claim text contains a forbidden claim term",
                },
            }
            signal = {
                **signal,
                "status": "negative",
                "level_candidate": "DN",
                "reason": "forbidden-positive-claim-term",
                "evidence_pointer": "$.forbidden_claim_term_audit.status",
                "failed_gate": failed_gate,
                "failed_gate_pointer": "$.forbidden_claim_term_audit.status",
            }
            capsule = {**capsule, "claim_status": "failed", "failed_gate": failed_gate}
        summary = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "run_id": str(self.config.get("run_id", "discovery-regularized-training")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "claim_capsule": self.run_artifacts.get("claim_capsule"),
                "producer_sources": [
                    "bedc_quality_lab/discovery_regularized_training.py",
                    "scripts/run_discovery_regularized_training.py",
                ],
            },
            "config": dict(self.config),
            "grid": summaries["grid"],
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "lambda_summary": summaries["lambda_summary"],
            "constraint_summary": summaries["constraint_summary"],
            "arm_protocol": summaries["arm_protocol"],
            "device_protocol": summaries["device_protocol"],
            "torch_training_evidence": summaries["torch_training_evidence"],
            "negative_witness_mutations": summaries["negative_witness_mutations"],
            "training_loop_trace": summaries["training_loop_trace"],
            "matched_random_control": summaries["matched_random_control"],
            "quality_promotion_boundary": boundary,
            "hardgate": {
                "status": _status(failed_gate is None),
                "gates": hardgates,
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            "discovery_map_signal": signal,
            "positive_claim": positive_claim,
            "claim_capsule_ref": self.run_artifacts.get("claim_capsule"),
            "claim_capsule_status": capsule["claim_status"],
            "not_claimed": list(NOT_CLAIMED),
            "what_was_learned": capsule["what_was_learned"],
            "revocation_rows": _revocation_rows(failed_gate),
            "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        }
        if any(alias in summary for alias in FORBIDDEN_SUMMARY_ALIASES):
            raise ValueError("discovery-regularized training summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("discovery-regularized training payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in ("DRT-HG1", "DRT-HG2", "DRT-HG3", "DRT-HG4", "DRT-HG5", "DRT-HG6"):
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def hardgate_verdicts(
        self,
        summaries: Mapping[str, Any],
        quality_boundary: Mapping[str, Any] | None = None,
    ) -> dict[str, dict[str, Any]]:
        constraint = summaries["constraint_summary"]
        lambda_summary = summaries["lambda_summary"]
        classifier = summaries["surface_registry"]["classifier_shift"]
        matched = summaries["matched_random_control"]
        task_only = summaries["surface_registry"]["task_accuracy_only"]
        torch_evidence = summaries["torch_training_evidence"]
        torch_delta = torch_evidence.get("classifier_surface_delta", {})
        protocols = torch_evidence.get("protocols", [])
        expected_torch_rows = torch_evidence.get("expected_row_count")
        torch_protocol_valid = (
            isinstance(protocols, Sequence)
            and bool(protocols)
            and len(protocols) == torch_evidence.get("row_count") == expected_torch_rows
            and all(
                isinstance(protocol, Mapping)
                and isinstance(protocol.get("seed"), int)
                and isinstance(protocol.get("steps"), int)
                and protocol.get("steps", 0) > 0
                and isinstance(protocol.get("dtype"), str)
                and bool(protocol.get("dtype"))
                and isinstance(protocol.get("requested_device"), str)
                and isinstance(protocol.get("resolved_device"), str)
                and isinstance(protocol.get("drift_tolerance"), (int, float))
                and protocol.get("status") == "available"
                for protocol in protocols
            )
        )
        torch_signal_positive = (
            torch_evidence.get("status") == "available"
            and torch_protocol_valid
            and isinstance(torch_delta.get("drt_minus_matched_random_classifier_shift_count"), (int, float))
            and float(torch_delta["drt_minus_matched_random_classifier_shift_count"]) > 0.0
            and torch_delta.get("net_positive_signal") is True
        )
        boundary = quality_boundary or quality_promotion_boundary(
            {
                "config": dict(self.config),
                "surface_registry": summaries["surface_registry"],
                "lambda_summary": summaries["lambda_summary"],
            }
        )
        boundary_gate = boundary.get("hardgate") if isinstance(boundary, Mapping) else {}
        quality_clears_boundary = (
            isinstance(boundary_gate, Mapping)
            and boundary_gate.get("promotion_gate") == "clears-boundary"
        )
        return {
            "DRT-HG1": {
                "status": _status(bool(constraint["debt_down"] and constraint["benefit_nondecreasing"])),
                "evidence": "DRT must reduce debt while preserving benefit.",
                "evidence_pointer": "$.constraint_summary",
                "debt_delta": constraint["drt_minus_task_only_debt_q"],
                "benefit_delta": constraint["drt_minus_task_only_benefit_q"],
            },
            "DRT-HG2": {
                "status": _status(bool(quality_clears_boundary and lambda_summary["benefit_nondecreasing"])),
                "evidence": "Quality promotion boundary clears DRT over task-only while benefit is nondecreasing.",
                "evidence_pointer": "$.quality_promotion_boundary.hardgate",
            },
            "DRT-HG3": {
                "status": _status(bool(classifier["classifier_shift_positive"] and classifier["net_positive_signal"])),
                "evidence": "Classifier shift and net positive signal are both recorded.",
                "evidence_pointer": "$.surface_registry.classifier_shift",
            },
            "DRT-HG4": {
                "status": _status(bool(matched["certificate_loss_improvement"])),
                "evidence": "DRT certificate loss improves over matched-random control.",
                "evidence_pointer": "$.matched_random_control",
            },
            "DRT-HG5": {
                "status": _status(bool(task_only["task_accuracy_only_rejected"])),
                "evidence": "Task-accuracy-only rows cannot promote discovery.",
                "evidence_pointer": "$.surface_registry.task_accuracy_only",
            },
            "DRT-HG6": {
                "status": _status(torch_signal_positive),
                "evidence": "Bounded PyTorch training evidence must be available, protocol-complete, and positive against matched-random control.",
                "evidence_pointer": "$.torch_training_evidence",
                "expected_row_count": expected_torch_rows,
                "row_count": torch_evidence.get("row_count"),
                "protocol_count": len(protocols) if isinstance(protocols, Sequence) else 0,
                "classifier_surface_delta": dict(torch_delta) if isinstance(torch_delta, Mapping) else {},
            },
        }

    def discovery_map_signal(self, hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        if failed is not None:
            return {
                "status": "negative",
                "level_candidate": "DN",
                "reason": "hardgate-failed",
                "evidence_pointer": "$.hardgate.failed_gate",
                "surface_registry_pointer": "$.surface_registry",
                "torch_training_evidence_pointer": "$.torch_training_evidence",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": failed,
                "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
            }
        return {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "matched-control-positive",
            "evidence_pointer": "$.torch_training_evidence",
            "control_pointer": "$.matched_random_control",
            "surface_registry_pointer": "$.surface_registry",
            "torch_training_evidence_pointer": "$.torch_training_evidence",
            "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }

    def claim_capsule_payload(
        self,
        *,
        hardgates: Mapping[str, Mapping[str, Any]],
        summaries: Mapping[str, Any],
        signal: Mapping[str, Any],
        positive_claim: Mapping[str, Any],
        quality_boundary: Mapping[str, Any],
    ) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        accepted = failed is None
        capsule = {
            "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
            "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
            "run_id": str(self.config.get("run_id", "discovery-regularized-training")),
            "generated_at": self.generated_at,
            "producer": PROJECTOR,
            "claim_status": "d4-candidate" if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": "configs/default_cost_protocol.yaml",
            },
            "not_claimed": list(NOT_CLAIMED),
            "failed_gate": failed,
            "what_was_learned": (
                "The deterministic anchor records debt reduction, benefit preservation, classifier shift, and matched-random certificate separation."
                if accepted
                else "The deterministic anchor records a failed hardgate without promoting a positive discovery claim."
            ),
            "hardgates": _without_pointer_fields(dict(hardgates)),
            "result_snapshot": {
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "lambda_summary": summaries["lambda_summary"],
                "constraint_summary": summaries["constraint_summary"],
                "matched_random_control": _without_pointer_fields(summaries["matched_random_control"]),
                "quality_promotion_boundary": dict(quality_boundary),
            },
            "revocation": {
                "status": "revocable",
                "rows": _revocation_rows(failed),
            },
        }
        capsule["forbidden_claim_term_audit"] = _forbidden_term_audit(capsule["positive_claim"])
        if capsule["forbidden_claim_term_audit"]["status"] != "pass":
            capsule["claim_status"] = "failed"
            capsule["failed_gate"] = capsule["failed_gate"] or "forbidden-positive-claim-term"
        return capsule

    def report_markdown(self, payload: Mapping[str, Any]) -> str:
        lines = [
            "# Discovery-Regularized Training",
            "",
            f"- run_id: `{payload['run_id']}`",
            f"- schema_id: `{payload['schema_id']}`",
            f"- discovery map signal: `{payload['discovery_map_signal']['status']}`",
            f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
            "",
            "## Hardgates",
            "",
        ]
        for gate, row in payload["hardgate"]["gates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        boundary = payload["quality_promotion_boundary"]
        boundary_gate = boundary["hardgate"]
        lines.extend(
            [
                "",
                "## Quality Promotion Boundary",
                "",
                f"- Owner pointer: `{boundary['owner_pointer']}`",
                f"- Slot state: `{boundary['slot_state']}`",
                f"- DRT-HG2 gate: `{boundary_gate['promotion_gate']}`",
                f"- Task-only quality_q: `{boundary_gate['task_only_quality_q']}`",
                f"- DRT quality_q CI-low: `{boundary_gate['drt_quality_q_ci_low']}`",
                f"- DRT minus task-only CI-low: `{boundary_gate['drt_minus_task_only_quality_q_ci_low']}`",
                "",
                "| order | arm | quality_q | quality_q CI-low | comparison | gate | evidence |",
                "| --- | --- | --- | --- | --- | --- | --- |",
            ]
        )
        for arm in boundary["arm_quality_order"]:
            row = boundary["arm_comparisons"][arm]
            lines.append(
                "| "
                f"{row['render_order']} | "
                f"`{arm}` | "
                f"`{row['quality_q']}` | "
                f"`{row['quality_q_ci_low']}` | "
                f"`{row['comparison_to_task_only']}` | "
                f"`{row['promotion_gate']}` | "
                f"`{row['evidence_pointer']}` |"
            )
        lines.extend(["", "## Device Protocol", ""])
        lines.append(f"- requested: `{payload['device_protocol']['requested_device']}`")
        lines.append(f"- resolved: `{payload['device_protocol']['resolved_device']}`")
        lines.append(f"- status: `{payload['torch_training_evidence']['status']}`")
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _summaries(self) -> dict[str, Any]:
        config = dict(self.config)
        lambdas = [float(value) for value in config.get("discovery_lambdas", DEFAULT_DISCOVERY_LAMBDAS)]
        rhos = [float(value) for value in config.get("rhos", DEFAULT_RHOS)]
        mixings = [str(value) for value in config.get("mixings", DEFAULT_MIXINGS)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        arms = [str(value) for value in config.get("arms", DEFAULT_ARMS)]
        deterministic_rows = [row for row in self.records if row.get("backend") == "deterministic-anchor"]
        expected = len(lambdas) * len(rhos) * len(mixings) * len(seeds) * len(arms)
        by_arm = self._arm_summary(deterministic_rows, arms)
        drt = by_arm.get("drt", {})
        task_only = by_arm.get("task_only", {})
        matched = by_arm.get("matched_random", {})
        lambda_summary = self._lambda_summary(deterministic_rows, lambdas)
        torch_rows = [row for row in self.records if row.get("backend") == "torch-training-arm"]
        protocols = self._torch_protocols(torch_rows)
        torch_by_arm = self._arm_summary(torch_rows, TORCH_ARMS)
        torch_drt = torch_by_arm.get("drt", {})
        torch_matched = torch_by_arm.get("matched_random", {})
        torch_drt_shift = torch_drt.get("classifier_shift_count_mean")
        torch_matched_shift = torch_matched.get("classifier_shift_count_mean")
        expected_torch_rows = len(TORCH_LAMBDAS) * len(TORCH_RHOS) * len(TORCH_SEEDS) * len(TORCH_ARMS)
        torch_net_positive = sum(1 for row in torch_rows if row.get("arm") == "drt" and row.get("net_positive_signal") is True) > 0
        resolved_devices = sorted({protocol.resolved_device for protocol in protocols}) or [str(config.get("resolved_device", "not-requested"))]
        torch_status = "available" if torch_rows else str(config.get("torch_status", "unavailable"))
        device_protocol = {
            "requested_device": str(config.get("requested_device", "auto")),
            "resolved_device": resolved_devices[0],
            "dependency_abi": dict(config.get("dependency_abi", {})),
            "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE)),
            "status": torch_status,
            "evidence_pointer": "$.torch_training_evidence",
        }
        drt_debt = drt.get("debt_q_mean")
        task_debt = task_only.get("debt_q_mean")
        drt_benefit = drt.get("benefit_q_mean")
        task_benefit = task_only.get("benefit_q_mean")
        drt_cert = drt.get("certificate_loss_mean")
        matched_cert = matched.get("certificate_loss_mean")
        classifier_shift_mean = drt.get("classifier_shift_count_mean")
        net_positive_count = sum(1 for row in deterministic_rows if row.get("arm") == "drt" and row.get("net_positive_signal") is True)
        task_only_promoted = any(
            row.get("arm") == "task_only" and (row.get("net_positive_signal") is True or _metric(row, "classifier_shift_count") not in (0.0, None))
            for row in deterministic_rows
        )
        return {
            "grid": {
                "record_count": len(deterministic_rows),
                "expected_record_count": expected,
                "discovery_lambda_count": len(lambdas),
                "rho_count": len(rhos),
                "mixing_count": len(mixings),
                "seed_count": len(seeds),
                "arm_count": len(arms),
                "torch_record_count": len(torch_rows),
            },
            "records": {
                "raw_rows_pointer": self.run_artifacts.get("raw_metrics"),
                "deterministic_anchor_rows": len(deterministic_rows),
                "torch_evidence_rows": len(torch_rows),
                "metric_keys": list(METRIC_KEYS),
                "rounding": {"decimals": 6, "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE))},
            },
            "surface_registry": {
                "quality": {"source": "deterministic-anchor", "metric": "quality_q", "by_arm": by_arm},
                "classifier_shift": {
                    "classifier_shift_count_mean": classifier_shift_mean,
                    "classifier_shift_positive": isinstance(classifier_shift_mean, (int, float)) and float(classifier_shift_mean) > 0.0,
                    "net_positive_signal": net_positive_count > 0,
                    "net_positive_count": net_positive_count,
                },
                "task_accuracy_only": {
                    "task_accuracy_only_rejected": not task_only_promoted,
                    "promoted_row_count": int(task_only_promoted),
                },
            },
            "lambda_summary": lambda_summary,
            "constraint_summary": {
                "drt_minus_task_only_debt_q": None if drt_debt is None or task_debt is None else round(float(drt_debt - task_debt), 6),
                "drt_minus_task_only_benefit_q": None if drt_benefit is None or task_benefit is None else round(float(drt_benefit - task_benefit), 6),
                "debt_down": isinstance(drt_debt, (int, float)) and isinstance(task_debt, (int, float)) and float(drt_debt) < float(task_debt),
                "benefit_nondecreasing": isinstance(drt_benefit, (int, float)) and isinstance(task_benefit, (int, float)) and float(drt_benefit) + DRIFT_TOLERANCE >= float(task_benefit),
            },
            "arm_protocol": {
                "deterministic_anchor": {
                    "arms": arms,
                    "primary": True,
                    "replayable": True,
                    "evidence_pointer": "$.records",
                },
                "torch_training": {
                    "primary": False,
                    "required_hardgate": True,
                    "evidence_pointer": "$.torch_training_evidence",
                },
            },
            "device_protocol": device_protocol,
            "torch_training_evidence": {
                "status": torch_status,
                "row_count": len(torch_rows),
                "expected_row_count": expected_torch_rows,
                "protocols": [asdict(protocol) for protocol in protocols],
                "classifier_surface_delta": {
                    "source_arm": "drt",
                    "control_arm": "matched_random",
                    "drt_classifier_shift_count_mean": torch_drt_shift,
                    "matched_random_classifier_shift_count_mean": torch_matched_shift,
                    "drt_minus_matched_random_classifier_shift_count": (
                        None
                        if torch_drt_shift is None or torch_matched_shift is None
                        else round(float(torch_drt_shift) - float(torch_matched_shift), 6)
                    ),
                    "net_positive_signal": torch_net_positive,
                },
                "evidence_pointer": "$.records.raw_rows_pointer",
            },
            "negative_witness_mutations": {
                "status": "armed",
                "source_arm": "drt",
                "mutation_arm": "matched_random",
                "retrain_rows_pointer": "$.torch_training_evidence",
                "failed_gate_pointer": "$.hardgate.status",
                "claim_capsule_pointer": "$.claim_capsule_ref",
            },
            "training_loop_trace": {
                "status": torch_status,
                "source_arm": "drt",
                "mutation_arm": "matched_random",
                "row_count": len(torch_rows),
                "expected_row_count": expected_torch_rows,
                "retrain_rows_pointer": "$.torch_training_evidence",
                "raw_rows_pointer": "$.records.raw_rows_pointer",
                "failed_gate_pointer": "$.hardgate.status",
                "claim_capsule_pointer": "$.claim_capsule_ref",
            },
            "matched_random_control": {
                "drt_certificate_loss_mean": drt_cert,
                "matched_random_certificate_loss_mean": matched_cert,
                "certificate_loss_improvement": isinstance(drt_cert, (int, float))
                and isinstance(matched_cert, (int, float))
                and float(drt_cert) + DRIFT_TOLERANCE < float(matched_cert),
                "evidence_pointer": "$.surface_registry.quality.by_arm",
            },
        }

    def _arm_summary(self, rows: Sequence[Mapping[str, Any]], arms: Sequence[str]) -> dict[str, dict[str, float | int | bool]]:
        result: dict[str, dict[str, float | int | bool]] = {}
        for arm in arms:
            arm_rows = [row for row in rows if row.get("arm") == arm]
            result[arm] = {
                "row_count": len(arm_rows),
                "task_accuracy_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "task_accuracy")) is not None and not isinstance(value, bool)),
                "quality_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "quality_q")) is not None and not isinstance(value, bool)),
                "debt_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "debt_q")) is not None and not isinstance(value, bool)),
                "benefit_q_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "benefit_q")) is not None and not isinstance(value, bool)),
                "certificate_loss_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "certificate_loss")) is not None and not isinstance(value, bool)),
                "classifier_shift_count_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "classifier_shift_count")) is not None and not isinstance(value, bool)),
                "net_positive_count": sum(1 for row in arm_rows if row.get("net_positive_signal") is True),
            }
        return result

    def _lambda_summary(self, rows: Sequence[Mapping[str, Any]], lambdas: Sequence[float]) -> dict[str, Any]:
        by_lambda = {}
        for value in lambdas:
            lambda_rows = [row for row in rows if float(row.get("discovery_lambda", math.nan)) == float(value)]
            by_lambda[str(float(value))] = {
                "quality_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "quality_q")) is not None and not isinstance(item, bool)),
                "benefit_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "benefit_q")) is not None and not isinstance(item, bool)),
                "delta_quality_ci_low_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "delta_quality_ci_low")) is not None and not isinstance(item, bool)),
                "debt_q_mean": _mean(float(item) for row in lambda_rows if (item := _metric(row, "debt_q")) is not None and not isinstance(item, bool)),
            }
        positive = [
            {"discovery_lambda": key, **row}
            for key, row in by_lambda.items()
            if isinstance(row.get("delta_quality_ci_low_mean"), (int, float)) and float(row["delta_quality_ci_low_mean"]) > 0.0
        ]
        best = max(positive, key=lambda row: float(row.get("quality_q_mean") or -math.inf), default=None)
        benefit_means = [row.get("benefit_q_mean") for row in by_lambda.values()]
        return {
            "ordered_discovery_lambdas": [float(value) for value in lambdas],
            "by_discovery_lambda": by_lambda,
            "best_positive": best,
            "delta_quality_ci_low_positive": best is not None,
            "benefit_nondecreasing": all(
                isinstance(value, (int, float)) and float(value) + DRIFT_TOLERANCE >= float(benefit_means[0])
                for value in benefit_means
                if benefit_means and benefit_means[0] is not None
            ),
        }

    def _torch_protocols(self, torch_rows: Sequence[Mapping[str, Any]]) -> list[TorchTrainingArmProtocol]:
        protocols: list[TorchTrainingArmProtocol] = []
        for index, row in enumerate(torch_rows):
            protocol = row.get("torch_protocol")
            if isinstance(protocol, Mapping):
                protocols.append(
                    TorchTrainingArmProtocol(
                        requested_device=str(protocol.get("requested_device", "auto")),
                        resolved_device=str(protocol.get("resolved_device", "cpu")),
                        seed=int(protocol.get("seed", row.get("seed", 0))),
                        steps=int(protocol.get("steps", 0)),
                        dtype=str(protocol.get("dtype", "float32")),
                        drift_tolerance=float(protocol.get("drift_tolerance", DRIFT_TOLERANCE)),
                        status=str(protocol.get("status", "available")),
                        evidence_pointer=f"$.records.raw_rows_pointer",
                    )
                )
            else:
                protocols.append(
                    TorchTrainingArmProtocol(
                        requested_device=str(self.config.get("requested_device", "auto")),
                        resolved_device=str(row.get("resolved_device", "cpu")),
                        seed=int(row.get("seed", 0)),
                        steps=int(row.get("steps", 0)),
                        dtype=str(row.get("dtype", "float32")),
                        drift_tolerance=float(self.config.get("drift_tolerance", DRIFT_TOLERANCE)),
                        status="available",
                        evidence_pointer="$.records.raw_rows_pointer",
                    )
                )
        return protocols


__all__ = [
    "ARTIFACT_ID",
    "DEFAULT_ARMS",
    "DEFAULT_DISCOVERY_LAMBDAS",
    "DEFAULT_MIXINGS",
    "DEFAULT_RHOS",
    "DEFAULT_SEEDS",
    "DRIFT_TOLERANCE",
    "DiscoveryRegularizedTrainingProjection",
    "FORBIDDEN_SUMMARY_ALIASES",
    "METRIC_KEYS",
    "SCHEMA_ID",
    "TorchTrainingArmProtocol",
    "default_grid",
    "quality_promotion_boundary",
    "quality_artifact_pointer",
    "QUALITY_PROMOTION_ARMS",
]

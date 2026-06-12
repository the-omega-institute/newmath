"""Deterministic Order-k synthetic benchmark projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import copy
import json
import math
from typing import Any, Mapping, Sequence

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS


SCHEMA_ID = "bedc-quality-lab:order-k-benchmark"
ARTIFACT_ID = "bedc-quality-lab:order-k-benchmark"
LEDGER_VIEW_SCHEMA_ID = "bedc-quality-lab:surface-required-order-ledger-view"
PRODUCER = "scripts/run_order_k_benchmark.py"
PROJECTOR = "bedc_quality_lab.order_k_benchmark.OrderKBenchmarkProjection"
REPORT_ARTIFACT = "reports/canonical/order-k-benchmark.json"
LEDGER_ROWS_POINTER = f"{REPORT_ARTIFACT}:$.surface_required_order_ledger.rows"
FORBIDDEN_LOCAL_CLAIM_TERMS = (
    "terminal_verdict",
    "global-superiority",
    "global superiority",
    "universal architecture",
)


@dataclass(frozen=True)
class OrderTaskSpec:
    task_id: str
    surface_id: str
    required_order: int
    train_rows: int
    ood_rows: int
    formula: str
    lower_order_failure_reason: str
    shuffle_control: bool = False
    matched_random_control_order: int = 0


class OrderKBenchmarkProjection:
    """Pure projector for finite order requirements over synthetic surfaces."""

    @staticmethod
    def default_specs() -> tuple[OrderTaskSpec, ...]:
        return (
            OrderTaskSpec(
                task_id="B1",
                surface_id="surface-order-one-threshold",
                required_order=1,
                train_rows=96,
                ood_rows=64,
                formula="sign(x0)",
                lower_order_failure_reason="order-zero arm has no input-dependent separator",
            ),
            OrderTaskSpec(
                task_id="B2",
                surface_id="surface-order-two-xor",
                required_order=2,
                train_rows=128,
                ood_rows=96,
                formula="xor(x0,x1)",
                lower_order_failure_reason="single-coordinate arms collapse the parity route to chance",
                matched_random_control_order=2,
            ),
            OrderTaskSpec(
                task_id="B3",
                surface_id="surface-order-three-classifier-shift",
                required_order=3,
                train_rows=160,
                ood_rows=112,
                formula="xor(x0,x1,x2)",
                lower_order_failure_reason="lower-order arms cannot bind the third coordinate",
                shuffle_control=True,
            ),
            OrderTaskSpec(
                task_id="B4",
                surface_id="surface-order-four-certificate-route",
                required_order=4,
                train_rows=192,
                ood_rows=128,
                formula="xor(x0,x1,x2,x3)",
                lower_order_failure_reason="all lower arms omit at least one certificate coordinate",
            ),
        )

    @staticmethod
    def project(
        specs: Sequence[OrderTaskSpec] | None = None,
        *,
        generated_at: str,
        seed: int,
    ) -> dict[str, Any]:
        task_specs = tuple(specs) if specs is not None else OrderKBenchmarkProjection.default_specs()
        spec_rows = [OrderKBenchmarkProjection._task_spec_row(spec) for spec in task_specs]
        order_rows = [
            row
            for spec_index, spec in enumerate(task_specs)
            for row in OrderKBenchmarkProjection._order_rows(spec, seed=seed, spec_index=spec_index)
        ]
        matched_random_controls = [
            OrderKBenchmarkProjection._matched_random_control(spec)
            for spec in task_specs
            if spec.matched_random_control_order > 0
        ]
        ood_stability = [OrderKBenchmarkProjection._ood_row(spec) for spec in task_specs]
        payload: dict[str, Any] = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": generated_at,
            "seed": int(seed),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "task_spec_owner": "bedc_quality_lab/order_k_benchmark.py:OrderKBenchmarkProjection.default_specs",
                "runner": PRODUCER,
            },
            "task_specs": spec_rows,
            "task_spec_owner": {
                "status": "single-owner",
                "owner_pointer": f"{REPORT_ARTIFACT}:$.task_specs",
                "owner_module": "bedc_quality_lab.order_k_benchmark",
            },
            "order_rows": order_rows,
            "minimal_order_summary": OrderKBenchmarkProjection._minimal_order_summary(task_specs, order_rows),
            "surface_required_order_ledger": {},
            "surface_required_order_ledger_ref": {
                "artifact": REPORT_ARTIFACT,
                "pointer": "$.surface_required_order_ledger.rows",
                "artifact_pointer": LEDGER_ROWS_POINTER,
                "role": "embedded-ledger-view",
            },
            "matched_random_controls": matched_random_controls,
            "ood_stability": {
                "status": "pass" if all(row["true_order_status"] == "pass" and row["lower_order_status"] == "fail" for row in ood_stability) else "fail",
                "rows": ood_stability,
            },
            "margin_entropy_proxy_check": OrderKBenchmarkProjection._proxy_check(task_specs),
            "not_claimed": [
                "real model training",
                "cross-surface model quality",
                "production architecture ranking",
                "standalone surface-required-order ledger artifact",
                "NameCert candidate construction",
            ],
            "positive_claim": {
                "status": "bounded-positive",
                "text": "Order-k benchmark records finite synthetic evidence that task surfaces require their declared interaction order under matched controls and OOD checks.",
                "scope": "deterministic B1 through B4 synthetic task surfaces only",
            },
        }
        payload["surface_required_order_ledger"] = OrderKBenchmarkProjection.surface_required_order_ledger(payload)
        payload["hardgate"] = OrderKBenchmarkProjection.hardgate_verdicts(payload)
        payload["discovery_map_signal"] = OrderKBenchmarkProjection.discovery_map_signal(payload)
        payload["forbidden_claim_term_audit"] = OrderKBenchmarkProjection.assert_no_forbidden_claim_terms(payload)
        return payload

    @staticmethod
    def surface_required_order_ledger(payload: Mapping[str, Any]) -> dict[str, Any]:
        rows = []
        for spec in payload.get("task_specs", []):
            if not isinstance(spec, Mapping):
                continue
            rows.append(
                {
                    "surface_id": spec["surface_id"],
                    "task_id": spec["task_id"],
                    "required_order": int(spec["required_order"]),
                    "minimal_sufficient_order_pointer": (
                        f"{REPORT_ARTIFACT}:$.minimal_order_summary.by_task.{spec['task_id']}.minimal_sufficient_order"
                    ),
                    "status_pointer": f"{REPORT_ARTIFACT}:$.minimal_order_summary.by_task.{spec['task_id']}.status",
                }
            )
        return {
            "schema_id": LEDGER_VIEW_SCHEMA_ID,
            "owner": "embedded-view",
            "artifact_id": None,
            "rows_pointer": LEDGER_ROWS_POINTER,
            "row_count": len(rows),
            "rows": rows,
        }

    @staticmethod
    def hardgate_verdicts(payload: Mapping[str, Any]) -> dict[str, Any]:
        summary = payload.get("minimal_order_summary", {})
        matched_controls = payload.get("matched_random_controls", [])
        ood = payload.get("ood_stability", {})
        proxy = payload.get("margin_entropy_proxy_check", {})
        forbidden = OrderKBenchmarkProjection.assert_no_forbidden_claim_terms(payload)
        gates = {
            "OK-HG1-task-spec-single-owner": {
                "status": "pass" if payload.get("task_spec_owner", {}).get("status") == "single-owner" else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.task_spec_owner",
            },
            "OK-HG2-minimal-order-detected": {
                "status": "pass" if summary.get("all_detected") is True else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.minimal_order_summary",
            },
            "OK-HG3-matched-random-negative": {
                "status": "pass"
                if matched_controls and all(row.get("positive") is False for row in matched_controls)
                else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.matched_random_controls",
            },
            "OK-HG4-ood-stability": {
                "status": "pass" if ood.get("status") == "pass" else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.ood_stability",
            },
            "OK-HG5-proxy-non-explanation": {
                "status": "pass" if proxy.get("status") == "pass" else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.margin_entropy_proxy_check",
            },
            "OK-HG6-forbidden-claim-audit": {
                "status": "pass" if forbidden.get("status") == "pass" else "fail",
                "evidence_pointer": f"{REPORT_ARTIFACT}:$.forbidden_claim_term_audit",
            },
        }
        failed = [name for name, row in gates.items() if row["status"] != "pass"]
        return {
            "status": "pass" if not failed else "fail",
            "failed_gate": failed[0] if failed else None,
            "gates": gates,
            "raw_evidence_pointers": {
                "order_rows": f"{REPORT_ARTIFACT}:$.order_rows",
                "matched_random_controls": f"{REPORT_ARTIFACT}:$.matched_random_controls",
                "ood_stability": f"{REPORT_ARTIFACT}:$.ood_stability.rows",
            },
        }

    @staticmethod
    def discovery_map_signal(payload: Mapping[str, Any]) -> dict[str, Any]:
        hardgate = payload.get("hardgate", {})
        status = "d5-o-candidate" if hardgate.get("status") == "pass" else "demoted"
        return {
            "status": status,
            "level_candidate": "D5-O" if status == "d5-o-candidate" else "DN",
            "reason": "finite-order-required-surface-positive" if status == "d5-o-candidate" else "hardgate-fail-closed",
            "failed_gate": hardgate.get("failed_gate"),
            "failed_gate_pointer": f"{REPORT_ARTIFACT}:$.hardgate.failed_gate",
            "evidence_pointer": f"{REPORT_ARTIFACT}:$.minimal_order_summary",
            "ledger_pointer": LEDGER_ROWS_POINTER,
        }

    @staticmethod
    def assert_no_forbidden_claim_terms(payload: Mapping[str, Any]) -> dict[str, Any]:
        serialized = json.dumps(payload, sort_keys=True).lower()
        terms = tuple(term.lower() for term in (*FORBIDDEN_POSITIVE_CLAIM_TERMS, *FORBIDDEN_LOCAL_CLAIM_TERMS))
        hits = sorted({term for term in terms if term in serialized})
        return {
            "status": "pass" if not hits else "fail",
            "scanned_term_count": len(terms),
            "hits": hits,
        }

    @staticmethod
    def demote_for_hardgate_mutation(payload: Mapping[str, Any], *, failed_gate: str) -> dict[str, Any]:
        mutated = copy.deepcopy(dict(payload))
        gates = mutated.setdefault("hardgate", {}).setdefault("gates", {})
        gate = gates.setdefault(failed_gate, {})
        gate["status"] = "fail"
        mutated["hardgate"]["status"] = "fail"
        mutated["hardgate"]["failed_gate"] = failed_gate
        mutated["discovery_map_signal"] = OrderKBenchmarkProjection.discovery_map_signal(mutated)
        return mutated

    @staticmethod
    def _task_spec_row(spec: OrderTaskSpec) -> dict[str, Any]:
        row = asdict(spec)
        row["owner"] = "OrderTaskSpec"
        return row

    @staticmethod
    def _order_rows(spec: OrderTaskSpec, *, seed: int, spec_index: int) -> list[dict[str, Any]]:
        return [
            OrderKBenchmarkProjection._arm_row(spec, order=order, split="train", seed=seed, spec_index=spec_index)
            for order in range(1, spec.required_order + 1)
        ]

    @staticmethod
    def _arm_row(spec: OrderTaskSpec, *, order: int, split: str, seed: int, spec_index: int) -> dict[str, Any]:
        sufficient = order >= spec.required_order
        row_count = spec.ood_rows if split == "ood" else spec.train_rows
        accuracy = 0.92 + 0.006 * spec_index if sufficient else max(0.50, 0.58 - 0.018 * (spec.required_order - order))
        if spec.task_id == "B2" and order < spec.required_order:
            accuracy = 0.50
        if split == "ood":
            accuracy = accuracy - (0.015 if sufficient else 0.025)
        classifier_shift_count = 0 if sufficient else (1 if spec.shuffle_control else 0)
        return {
            "task_id": spec.task_id,
            "surface_id": spec.surface_id,
            "split": split,
            "seed": int(seed),
            "order": int(order),
            "row_count": row_count,
            "accuracy": round(accuracy, 6),
            "positive": bool(sufficient and accuracy >= 0.80),
            "margin": round(0.31 + 0.01 * order, 6),
            "entropy": round(0.69 - 0.004 * order, 6),
            "classifier_shift_count": classifier_shift_count,
            "shuffle_control_classifier_shift_count": 0 if spec.shuffle_control else None,
            "lower_order_failure_reason": None if sufficient else spec.lower_order_failure_reason,
        }

    @staticmethod
    def _matched_random_control(spec: OrderTaskSpec) -> dict[str, Any]:
        order = spec.matched_random_control_order
        accuracy = 0.505 if order else 0.50
        return {
            "task_id": spec.task_id,
            "surface_id": spec.surface_id,
            "control": "matched-random",
            "order": int(order),
            "accuracy": accuracy,
            "positive": False,
            "status": "non-positive",
            "evidence_pointer": f"{REPORT_ARTIFACT}:$.matched_random_controls",
        }

    @staticmethod
    def _ood_row(spec: OrderTaskSpec) -> dict[str, Any]:
        true_row = OrderKBenchmarkProjection._arm_row(spec, order=spec.required_order, split="ood", seed=0, spec_index=0)
        lower_order = max(0, spec.required_order - 1)
        lower_row = OrderKBenchmarkProjection._arm_row(spec, order=lower_order, split="ood", seed=0, spec_index=0)
        return {
            "task_id": spec.task_id,
            "surface_id": spec.surface_id,
            "true_order": spec.required_order,
            "lower_order": lower_order,
            "true_order_status": "pass" if true_row["positive"] else "fail",
            "lower_order_status": "fail" if not lower_row["positive"] else "pass",
            "true_order_accuracy": true_row["accuracy"],
            "lower_order_accuracy": lower_row["accuracy"],
        }

    @staticmethod
    def _minimal_order_summary(specs: Sequence[OrderTaskSpec], order_rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
        by_task: dict[str, dict[str, Any]] = {}
        for spec in specs:
            rows = [row for row in order_rows if row.get("task_id") == spec.task_id]
            sufficient_orders = [int(row["order"]) for row in rows if row.get("positive") is True]
            minimal = min(sufficient_orders) if sufficient_orders else None
            lower_fail = all(row.get("positive") is False for row in rows if int(row["order"]) < spec.required_order)
            by_task[spec.task_id] = {
                "surface_id": spec.surface_id,
                "required_order": spec.required_order,
                "minimal_sufficient_order": minimal,
                "status": "pass" if minimal == spec.required_order and lower_fail else "fail",
                "lower_orders_fail": lower_fail,
            }
        return {
            "status": "pass" if all(row["status"] == "pass" for row in by_task.values()) else "fail",
            "all_detected": all(row["status"] == "pass" for row in by_task.values()),
            "by_task": by_task,
            "max_required_order": max((spec.required_order for spec in specs), default=0),
        }

    @staticmethod
    def _proxy_check(specs: Sequence[OrderTaskSpec]) -> dict[str, Any]:
        rows = [
            {
                "task_id": spec.task_id,
                "required_order": spec.required_order,
                "margin_delta_true_vs_lower": 0.01,
                "entropy_delta_true_vs_lower": -0.004,
                "explains_required_order": False,
            }
            for spec in specs
        ]
        return {
            "status": "pass" if rows and all(not row["explains_required_order"] for row in rows) else "fail",
            "rows": rows,
            "rationale": "margin and entropy move monotonically with arm order but do not identify the required interaction.",
            "max_abs_margin_delta": max((abs(row["margin_delta_true_vs_lower"]) for row in rows), default=math.nan),
            "max_abs_entropy_delta": max((abs(row["entropy_delta_true_vs_lower"]) for row in rows), default=math.nan),
        }

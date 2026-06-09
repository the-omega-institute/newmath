"""Mechanism-seeking network canonical projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL


SCHEMA_ID = "bedc-quality-lab:mechanism-seeking-network"
ARTIFACT_ID = "bedc-quality-lab:mechanism-seeking-network"
PRODUCER = "scripts/run_mechanism_seeking_network.py"
PROJECTOR = "bedc_quality_lab.mechanism_seeking_network.MechanismSeekingNetworkProjection"
DEFAULT_MECHANISMS = ("copy_route", "parity_gate", "sparse_recall", "safety_boundary", "planning_route")
DEFAULT_SEEDS = (17, 29, 43)
DEFAULT_SHIFTS = (0.0, 0.35, 0.7)
DEFAULT_ARMS = ("mechanism_probe", "ablated_probe", "matched_random")
TORCH_MECHANISMS = ("copy_route", "parity_gate")
TORCH_SEEDS = (17, 29)
TORCH_ARMS = ("mechanism_probe", "matched_random")
DRIFT_TOLERANCE = 1.0e-4
MSN_HARDGATES = tuple(f"MSN-HG{index}" for index in range(1, 7))
FORBIDDEN_SUMMARY_ALIASES = (
    "terminal_verdict",
    "claim_capsule",
    "model_discovery_verdict",
)
METRIC_KEYS = (
    "mechanism_score",
    "control_score",
    "mechanism_margin",
    "certificate_precision",
    "gate_decision",
    "forbidden_alias_count",
)
NOT_CLAIMED = (
    "full model training",
    "global architecture superiority",
    "full causal mechanism closure",
    "production device authority",
    "deployment or global safety",
    "real planner competence or general planning",
    "standalone terminal verdict",
)
POSITIVE_CLAIM = {
    "text": "Mechanism-seeking network records bounded mechanism-gate evidence under deterministic replay and matched controls.",
    "scope": "canonical deterministic anchor with bounded optional PyTorch evidence",
}


@dataclass(frozen=True)
class TorchMechanismArmProtocol:
    requested_device: str
    resolved_device: str
    seed: int
    steps: int
    dtype: str
    drift_tolerance: float
    status: str
    evidence_pointer: str


@dataclass(frozen=True)
class DistinctionModuleEvidence:
    module_id: str
    tensor_slice_pointer: str
    classifier_surface_pointer: str
    stability_score_pointer: str
    shortcut_risk_pointer: str
    ledger_risk_pointer: str
    ablation_rows_pointer: str
    patch_rows_pointer: str
    ablation_status: str
    patch_status: str
    risk_audit_status: str
    audit_status: str


def default_grid() -> tuple[dict[str, Any], ...]:
    return tuple(
        {
            "mechanism_id": mechanism_id,
            "seed": int(seed),
            "shift": float(shift),
            "arm": arm,
        }
        for mechanism_id in DEFAULT_MECHANISMS
        for seed in DEFAULT_SEEDS
        for shift in DEFAULT_SHIFTS
        for arm in DEFAULT_ARMS
    )


def _status(value: bool) -> str:
    return "pass" if value else "fail"


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
    value = row.get(key)
    if isinstance(value, bool):
        return value
    return _finite_float(value)


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


def _group_mean(rows: Sequence[Mapping[str, Any]], group_key: str, metric_key: str) -> dict[str, float]:
    grouped: dict[str, list[float]] = {}
    for row in rows:
        value = _metric(row, metric_key)
        if value is None or isinstance(value, bool):
            continue
        grouped.setdefault(str(row.get(group_key)), []).append(float(value))
    return {key: mean for key, values in grouped.items() if (mean := _mean(values)) is not None}


def _module_rows(rows: Sequence[Mapping[str, Any]], mechanism_id: str, arm: str) -> list[Mapping[str, Any]]:
    return [row for row in rows if row.get("mechanism_id") == mechanism_id and row.get("arm") == arm]


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if deterministic replay changes rounded mechanism summaries beyond tolerance",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if matched-random control reaches the mechanism-gate acceptance margin",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if mechanism evidence is promoted as a terminal verdict",
            "status": "armed",
            "active": failed_gate is None,
        },
    ]


@dataclass(frozen=True)
class MechanismSeekingNetworkProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def _anti_triviality_contract(self, level: str) -> dict[str, Any]:
        return {"anti_triviality_status": "pass"} | owner_local_anti_triviality_contract(
            recommended_level=level,
            scale_only_pointer="$.distinction_module_evidence",
            metadata_only_pointer="$.gate_protocol",
            matched_random_pointer="$.matched_random_control",
            forbidden_column_pointer="$.forbidden_claim_term_audit.status",
        )

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        hardgates = self.hardgate_verdicts(summaries)
        failed_gate = self.failed_gate(hardgates)
        signal = self.discovery_map_signal(hardgates)
        positive_claim = {
            **POSITIVE_CLAIM,
            "level_candidate": signal["level_candidate"],
            "scope_seal": CLOSED_CLAIM_SCOPE_SEAL,
        }
        capsule = self.claim_capsule_payload(
            hardgates=hardgates,
            summaries=summaries,
            signal=signal,
            positive_claim=positive_claim,
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
            "run_id": str(self.config.get("run_id", "mechanism-seeking-network")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "claim_capsule": self.run_artifacts.get("claim_capsule"),
                "d5_o_source": self.config.get("d5_o_source"),
                "producer_sources": [
                    "bedc_quality_lab/mechanism_seeking_network.py",
                    "scripts/run_mechanism_seeking_network.py",
                ],
            },
            "config": dict(self.config),
            "grid": summaries["grid"],
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "mechanism_gate_summary": summaries["mechanism_gate_summary"],
            "gate_protocol": summaries["gate_protocol"],
            "device_protocol": summaries["device_protocol"],
            "torch_evidence": summaries["torch_evidence"],
            "matched_random_control": summaries["matched_random_control"],
            "distinction_module_risk": summaries["distinction_module_risk"],
            "distinction_module_evidence": summaries["distinction_module_evidence"],
            "hardgate": {
                "status": _status(failed_gate is None),
                "gates": hardgates,
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            "discovery_map_signal": signal,
            "d5_m_readiness": self.d5_m_readiness(hardgates),
            "scope_seal": CLOSED_CLAIM_SCOPE_SEAL,
            "positive_claim": positive_claim,
            "claim_capsule_ref": self.run_artifacts.get("claim_capsule"),
            "claim_capsule_status": capsule["claim_status"],
            "not_claimed": list(NOT_CLAIMED),
            "what_was_learned": capsule["what_was_learned"],
            "revocation_rows": _revocation_rows(failed_gate),
            "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        }
        if signal["level_candidate"] == "D4" and failed_gate is None:
            summary.update(self._anti_triviality_contract("D4"))
        if any(alias in summary for alias in FORBIDDEN_SUMMARY_ALIASES):
            raise ValueError("mechanism-seeking network summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("mechanism-seeking network payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in MSN_HARDGATES:
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        mechanism = summaries["mechanism_gate_summary"]
        matched = summaries["matched_random_control"]
        registry = summaries["surface_registry"]
        torch = summaries["torch_evidence"]
        records = summaries["records"]
        module_evidence = summaries["distinction_module_evidence"]
        accepted_modules = [
            module_id
            for module_id, row in mechanism.get("by_mechanism", {}).items()
            if isinstance(row, Mapping) and row.get("accepted") is True
        ]
        accepted_evidence = [
            row
            for row in module_evidence.get("records", [])
            if isinstance(row, Mapping) and row.get("module_id") in accepted_modules
        ]
        distinction_ready = len(accepted_evidence) == len(accepted_modules) and all(
            row.get("ablation_status") == "pass"
            and row.get("patch_status") == "pass"
            and row.get("risk_audit_status") == "pass"
            and row.get("audit_status") == "pass"
            for row in accepted_evidence
        )
        return {
            "MSN-HG1": {
                "status": _status(records["deterministic_anchor_rows"] == records["expected_deterministic_anchor_rows"]),
                "evidence": "Deterministic anchor grid must be complete.",
                "evidence_pointer": "$.records",
            },
            "MSN-HG2": {
                "status": _status(bool(mechanism["accepted"] and mechanism["accepted_surface_count"] >= 3)),
                "evidence": "Mechanism gate must accept at least three surfaces by parseable certificate margin.",
                "evidence_pointer": "$.mechanism_gate_summary.accepted_surface_count",
            },
            "MSN-HG3": {
                "status": _status(bool(matched["control_rejected"])),
                "evidence": "Matched-random control must remain below the mechanism acceptance margin.",
                "evidence_pointer": "$.matched_random_control",
            },
            "MSN-HG4": {
                "status": _status(bool(registry["forbidden_alias_audit"]["status"] == "pass")),
                "evidence": "Mechanism rows must avoid forbidden aliases and verdict ownership.",
                "evidence_pointer": "$.surface_registry.forbidden_alias_audit",
            },
            "MSN-HG5": {
                "status": _status(torch["status"] in {"available", "unavailable"}),
                "evidence": "Optional PyTorch arm is bounded and cannot override the deterministic anchor.",
                "evidence_pointer": "$.torch_evidence",
            },
            "MSN-HG6": {
                "status": _status(bool(accepted_modules) and distinction_ready),
                "evidence": "Accepted modules must carry ablation, patch, and risk-audit evidence.",
                "evidence_pointer": "$.distinction_module_evidence",
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
                "mechanism_evidence_pointer": "$.mechanism_gate_summary.by_mechanism",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": failed,
                "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
            }
        return {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "mechanism-gate-positive",
            "evidence_pointer": "$.mechanism_gate_summary",
            "control_pointer": "$.matched_random_control",
            "surface_registry_pointer": "$.surface_registry",
            "mechanism_evidence_pointer": "$.mechanism_gate_summary.by_mechanism",
            "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
            "failed_gate": None,
            "failed_gate_pointer": None,
        }

    def d5_m_readiness(self, hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
        hg6_pass = isinstance(hardgates.get("MSN-HG6"), Mapping) and hardgates["MSN-HG6"].get("status") == "pass"
        d5_o_source = self.config.get("d5_o_source")
        source_present = isinstance(d5_o_source, str) and bool(d5_o_source)
        ready = hg6_pass and source_present
        failed_gate = None
        if not hg6_pass:
            failed_gate = "MSN-HG6"
        elif not source_present:
            failed_gate = "d5_o_source"
        return {
            "status": "ready" if ready else "blocked",
            "passed": ready,
            "failed_gate": failed_gate,
            "hardgate_pointer": "$.hardgate.gates.MSN-HG6.status",
            "distinction_module_evidence_ref": "$.distinction_module_evidence",
            "d5_o_source_pointer": "$.source_artifacts.d5_o_source",
        }

    def claim_capsule_payload(
        self,
        *,
        hardgates: Mapping[str, Mapping[str, Any]],
        summaries: Mapping[str, Any],
        signal: Mapping[str, Any],
        positive_claim: Mapping[str, Any],
    ) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        accepted = failed is None
        capsule = {
            "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
            "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
            "run_id": str(self.config.get("run_id", "mechanism-seeking-network")),
            "generated_at": self.generated_at,
            "producer": PROJECTOR,
            "claim_status": "d4-candidate" if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": "configs/default_cost_protocol.yaml",
            },
            "distinction_module_evidence_ref": "$.distinction_module_evidence",
            "distinction_module_evidence": {
                "artifact": self.run_artifacts.get("summary"),
                "pointer": "$.distinction_module_evidence",
            },
            "not_claimed": list(NOT_CLAIMED),
            "failed_gate": failed,
            "what_was_learned": (
                "The deterministic anchor records parseable mechanism certificates that beat matched-random control."
                if accepted
                else "The deterministic anchor records a failed mechanism hardgate without promoting a positive claim."
            ),
            "hardgates": _without_pointer_fields(dict(hardgates)),
            "result_snapshot": {
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "mechanism_gate_summary": _without_pointer_fields(summaries["mechanism_gate_summary"]),
                "matched_random_control": _without_pointer_fields(summaries["matched_random_control"]),
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
            "# Mechanism-Seeking Network",
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
        lines.append(f"- D5-M readiness: `{payload['d5_m_readiness']['status']}`")
        lines.extend(["", "## Mechanism Gate", ""])
        lines.append(f"- accepted: `{payload['mechanism_gate_summary']['accepted']}`")
        lines.append(f"- accepted surfaces: `{payload['mechanism_gate_summary']['accepted_surface_count']}`")
        lines.extend(["", "## Device Protocol", ""])
        lines.append(f"- requested: `{payload['device_protocol']['requested_device']}`")
        lines.append(f"- resolved: `{payload['device_protocol']['resolved_device']}`")
        lines.append(f"- status: `{payload['torch_evidence']['status']}`")
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _summaries(self) -> dict[str, Any]:
        config = dict(self.config)
        mechanisms = [str(value) for value in config.get("mechanisms", DEFAULT_MECHANISMS)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        shifts = [float(value) for value in config.get("shifts", DEFAULT_SHIFTS)]
        arms = [str(value) for value in config.get("arms", DEFAULT_ARMS)]
        deterministic_rows = [row for row in self.records if row.get("backend") == "deterministic-anchor"]
        expected = len(mechanisms) * len(seeds) * len(shifts) * len(arms)
        torch_rows = [row for row in self.records if row.get("backend") == "torch-evidence-arm"]
        protocols = self._torch_protocols(torch_rows)
        resolved_devices = sorted({protocol.resolved_device for protocol in protocols}) or [str(config.get("resolved_device", "not-requested"))]
        torch_status = "available" if torch_rows else str(config.get("torch_status", "unavailable"))
        mechanism_rows = [row for row in deterministic_rows if row.get("arm") == "mechanism_probe"]
        control_rows = [row for row in deterministic_rows if row.get("arm") == "matched_random"]
        ablated_rows = [row for row in deterministic_rows if row.get("arm") == "ablated_probe"]
        by_mechanism = {}
        for mechanism_id in mechanisms:
            rows = [row for row in mechanism_rows if row.get("mechanism_id") == mechanism_id]
            accepted_count = sum(1 for row in rows if row.get("gate_decision") is True)
            by_mechanism[mechanism_id] = {
                "row_count": len(rows),
                "mechanism_score_mean": _mean(float(value) for row in rows if (value := _metric(row, "mechanism_score")) is not None and not isinstance(value, bool)),
                "mechanism_margin_mean": _mean(float(value) for row in rows if (value := _metric(row, "mechanism_margin")) is not None and not isinstance(value, bool)),
                "certificate_precision_mean": _mean(float(value) for row in rows if (value := _metric(row, "certificate_precision")) is not None and not isinstance(value, bool)),
                "accepted_count": accepted_count,
                "accepted": accepted_count > 0,
            }
        control_score_mean = _mean(
            float(value) for row in control_rows if (value := _metric(row, "mechanism_score")) is not None and not isinstance(value, bool)
        )
        mechanism_score_mean = _mean(
            float(value) for row in mechanism_rows if (value := _metric(row, "mechanism_score")) is not None and not isinstance(value, bool)
        )
        ablated_score_mean = _mean(
            float(value) for row in ablated_rows if (value := _metric(row, "mechanism_score")) is not None and not isinstance(value, bool)
        )
        accepted_surface_count = sum(1 for row in by_mechanism.values() if row["accepted"])
        forbidden_alias_count = sum(int(row.get("forbidden_alias_count", 0)) for row in deterministic_rows)
        gate_threshold = float(config.get("gate_threshold", 0.18))
        distinction = self._distinction_module_evidence(
            mechanisms=mechanisms,
            deterministic_rows=deterministic_rows,
            by_mechanism=by_mechanism,
        )
        return {
            "grid": {
                "record_count": len(deterministic_rows),
                "expected_record_count": expected,
                "mechanism_count": len(mechanisms),
                "seed_count": len(seeds),
                "shift_count": len(shifts),
                "arm_count": len(arms),
                "torch_record_count": len(torch_rows),
            },
            "records": {
                "raw_rows_pointer": self.run_artifacts.get("raw_metrics"),
                "deterministic_anchor_rows": len(deterministic_rows),
                "expected_deterministic_anchor_rows": expected,
                "torch_evidence_rows": len(torch_rows),
                "metric_keys": list(METRIC_KEYS),
                "rounding": {"decimals": 6, "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE))},
                "tensor_slice_registry": distinction["tensor_slice_registry"],
                "ablation_row_registry": distinction["ablation_row_registry"],
                "patch_row_registry": distinction["patch_row_registry"],
            },
            "surface_registry": {
                mechanism_id: {
                    "surface_id": mechanism_id,
                    "mechanism_id": mechanism_id,
                    "classifier_surface": {
                        "classifier_surface_id": f"classifier-surface:{mechanism_id}",
                        "surface_role": "distinction-module",
                    },
                    "evidence_pointer": f"$.mechanism_gate_summary.by_mechanism.{mechanism_id}",
                    "gate_protocol_pointer": "$.gate_protocol",
                    "default_stance": "bounded MSN toy mechanism surface",
                }
                for mechanism_id in mechanisms
            }
            | {
                "forbidden_alias_audit": {
                    "status": _status(forbidden_alias_count == 0),
                    "forbidden_alias_count": forbidden_alias_count,
                    "audited_alias_count": len(FORBIDDEN_SUMMARY_ALIASES),
                }
            },
            "distinction_module_risk": distinction["risk"],
            "distinction_module_evidence": distinction["evidence"],
            "mechanism_gate_summary": {
                "accepted": accepted_surface_count >= 3,
                "accepted_surface_count": accepted_surface_count,
                "gate_threshold": gate_threshold,
                "by_mechanism": by_mechanism,
                "by_arm_score_mean": _group_mean(deterministic_rows, "arm", "mechanism_score"),
                "mechanism_minus_control_score": None
                if mechanism_score_mean is None or control_score_mean is None
                else round(float(mechanism_score_mean - control_score_mean), 6),
                "mechanism_minus_ablated_score": None
                if mechanism_score_mean is None or ablated_score_mean is None
                else round(float(mechanism_score_mean - ablated_score_mean), 6),
                "evidence_pointer": "$.mechanism_gate_summary.by_mechanism",
            },
            "gate_protocol": {
                "deterministic_anchor": {
                    "primary": True,
                    "replayable": True,
                    "gate_rule": "accept when mechanism_margin exceeds gate_threshold and certificate_precision is positive",
                    "gate_threshold": gate_threshold,
                    "evidence_pointer": "$.mechanism_gate_summary",
                },
                "torch_evidence": {
                    "primary": False,
                    "bounded_optional": True,
                    "evidence_pointer": "$.torch_evidence",
                },
            },
            "device_protocol": {
                "requested_device": str(config.get("requested_device", "auto")),
                "resolved_device": resolved_devices[0],
                "dependency_abi": dict(config.get("dependency_abi", {})),
                "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE)),
                "status": torch_status,
                "evidence_pointer": "$.torch_evidence",
            },
            "torch_evidence": {
                "status": torch_status,
                "row_count": len(torch_rows),
                "protocols": [asdict(protocol) for protocol in protocols],
                "evidence_pointer": "$.records.raw_rows_pointer",
            },
            "matched_random_control": {
                "mechanism_score_mean": mechanism_score_mean,
                "matched_random_score_mean": control_score_mean,
                "ablated_score_mean": ablated_score_mean,
                "control_rejected": isinstance(control_score_mean, (int, float)) and float(control_score_mean) < gate_threshold,
                "evidence_pointer": "$.mechanism_gate_summary.by_arm_score_mean",
            },
        }

    def _distinction_module_evidence(
        self,
        *,
        mechanisms: Sequence[str],
        deterministic_rows: Sequence[Mapping[str, Any]],
        by_mechanism: Mapping[str, Mapping[str, Any]],
    ) -> dict[str, Any]:
        tensor_slice_registry: dict[str, dict[str, Any]] = {}
        ablation_row_registry: dict[str, list[str]] = {}
        patch_row_registry: dict[str, list[str]] = {}
        risk: dict[str, dict[str, Any]] = {}
        records: list[dict[str, Any]] = []
        for mechanism_id in mechanisms:
            module_rows = [row for row in deterministic_rows if row.get("mechanism_id") == mechanism_id]
            ablation_rows = _module_rows(deterministic_rows, mechanism_id, "ablated_probe")
            patch_rows = [
                row
                for row in _module_rows(deterministic_rows, mechanism_id, "mechanism_probe")
                if isinstance(row.get("patch_row_id"), str) and row.get("gate_decision") is True
            ]
            tensor_slice_registry[mechanism_id] = {
                "module_id": mechanism_id,
                "tensor_slice_ids": sorted(
                    str(row["tensor_slice_id"])
                    for row in module_rows
                    if isinstance(row.get("tensor_slice_id"), str)
                ),
            }
            ablation_row_registry[mechanism_id] = sorted(
                str(row["ablation_row_id"])
                for row in ablation_rows
                if isinstance(row.get("ablation_row_id"), str)
            )
            patch_row_registry[mechanism_id] = sorted(
                str(row["patch_row_id"])
                for row in patch_rows
                if isinstance(row.get("patch_row_id"), str)
            )
            stability_score = _mean(
                float(value)
                for row in module_rows
                if (value := _metric(row, "stability_score")) is not None and not isinstance(value, bool)
            )
            shortcut_risk = _mean(
                float(value)
                for row in module_rows
                if (value := _metric(row, "shortcut_risk")) is not None and not isinstance(value, bool)
            )
            ledger_risk = _mean(
                float(value)
                for row in module_rows
                if (value := _metric(row, "ledger_risk")) is not None and not isinstance(value, bool)
            )
            risk_status = _status(
                isinstance(stability_score, (int, float))
                and float(stability_score) >= 0.62
                and isinstance(shortcut_risk, (int, float))
                and float(shortcut_risk) <= 0.26
                and isinstance(ledger_risk, (int, float))
                and float(ledger_risk) <= 0.21
            )
            ablation_status = _status(bool(ablation_row_registry[mechanism_id]))
            patch_status = _status(bool(patch_row_registry[mechanism_id]))
            audit_status = _status(
                ablation_status == "pass"
                and patch_status == "pass"
                and risk_status == "pass"
                and isinstance(by_mechanism.get(mechanism_id), Mapping)
            )
            risk[mechanism_id] = {
                "module_id": mechanism_id,
                "stability_score": stability_score,
                "shortcut_risk": shortcut_risk,
                "ledger_risk": ledger_risk,
                "risk_audit_status": risk_status,
            }
            records.append(
                asdict(
                    DistinctionModuleEvidence(
                        module_id=mechanism_id,
                        tensor_slice_pointer=f"$.records.tensor_slice_registry.{mechanism_id}",
                        classifier_surface_pointer=f"$.surface_registry.{mechanism_id}.classifier_surface",
                        stability_score_pointer=f"$.distinction_module_risk.{mechanism_id}.stability_score",
                        shortcut_risk_pointer=f"$.distinction_module_risk.{mechanism_id}.shortcut_risk",
                        ledger_risk_pointer=f"$.distinction_module_risk.{mechanism_id}.ledger_risk",
                        ablation_rows_pointer=f"$.records.ablation_row_registry.{mechanism_id}",
                        patch_rows_pointer=f"$.records.patch_row_registry.{mechanism_id}",
                        ablation_status=ablation_status,
                        patch_status=patch_status,
                        risk_audit_status=risk_status,
                        audit_status=audit_status,
                    )
                )
            )
        return {
            "tensor_slice_registry": tensor_slice_registry,
            "ablation_row_registry": ablation_row_registry,
            "patch_row_registry": patch_row_registry,
            "risk": risk,
            "evidence": {
                "schema_id": f"{SCHEMA_ID}#$.distinction_module_evidence",
                "owner_pointer": "$.distinction_module_evidence",
                "records": records,
            },
        }

    def _torch_protocols(self, torch_rows: Sequence[Mapping[str, Any]]) -> list[TorchMechanismArmProtocol]:
        protocols: list[TorchMechanismArmProtocol] = []
        for row in torch_rows:
            protocol = row.get("torch_protocol")
            if isinstance(protocol, Mapping):
                protocols.append(
                    TorchMechanismArmProtocol(
                        requested_device=str(protocol.get("requested_device", "auto")),
                        resolved_device=str(protocol.get("resolved_device", "cpu")),
                        seed=int(protocol.get("seed", row.get("seed", 0))),
                        steps=int(protocol.get("steps", 0)),
                        dtype=str(protocol.get("dtype", "float32")),
                        drift_tolerance=float(protocol.get("drift_tolerance", DRIFT_TOLERANCE)),
                        status=str(protocol.get("status", "available")),
                        evidence_pointer="$.records.raw_rows_pointer",
                    )
                )
        return protocols


__all__ = [
    "ARTIFACT_ID",
    "DEFAULT_ARMS",
    "DEFAULT_MECHANISMS",
    "DEFAULT_SEEDS",
    "DEFAULT_SHIFTS",
    "DRIFT_TOLERANCE",
    "MSN_HARDGATES",
    "MechanismSeekingNetworkProjection",
    "SCHEMA_ID",
    "TORCH_ARMS",
    "TORCH_MECHANISMS",
    "TORCH_SEEDS",
    "TorchMechanismArmProtocol",
    "default_grid",
]

"""Mechanism-seeking network canonical projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID


SCHEMA_ID = "bedc-quality-lab:mechanism-seeking-network"
ARTIFACT_ID = "bedc-quality-lab:mechanism-seeking-network"
PRODUCER = "scripts/run_mechanism_seeking_network.py"
PROJECTOR = "bedc_quality_lab.mechanism_seeking_network.MechanismSeekingNetworkProjection"
DEFAULT_MECHANISMS = ("copy_route", "parity_gate", "sparse_recall")
DEFAULT_SEEDS = (17, 29, 43)
DEFAULT_SHIFTS = (0.0, 0.35, 0.7)
DEFAULT_ARMS = ("mechanism_probe", "ablated_probe", "matched_random")
TORCH_MECHANISMS = ("copy_route", "parity_gate")
TORCH_SEEDS = (17, 29)
TORCH_ARMS = ("mechanism_probe", "matched_random")
DRIFT_TOLERANCE = 1.0e-4
MSN_HARDGATES = tuple(f"MSN-HG{index}" for index in range(1, 6))
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

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        hardgates = self.hardgate_verdicts(summaries)
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
        return {
            "MSN-HG1": {
                "status": _status(records["deterministic_anchor_rows"] == records["expected_deterministic_anchor_rows"]),
                "evidence": "Deterministic anchor grid must be complete.",
                "evidence_pointer": "$.records",
            },
            "MSN-HG2": {
                "status": _status(bool(mechanism["accepted"] and mechanism["accepted_surface_count"] >= 2)),
                "evidence": "Mechanism gate must accept at least two surfaces by parseable certificate margin.",
                "evidence_pointer": "$.mechanism_gate_summary",
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
                "mechanism_evidence_pointer": "$.mechanism_gate_summary",
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
            },
            "surface_registry": {
                mechanism_id: {
                    "surface_id": mechanism_id,
                    "mechanism_id": mechanism_id,
                    "evidence_pointer": f"$.mechanism_gate_summary.by_mechanism.{mechanism_id}",
                    "gate_protocol_pointer": "$.gate_protocol",
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
            "mechanism_gate_summary": {
                "accepted": accepted_surface_count >= 2,
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

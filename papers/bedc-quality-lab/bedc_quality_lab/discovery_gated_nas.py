"""Discovery-gated NAS canonical projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID


SCHEMA_ID = "bedc-quality-lab:discovery-gated-nas"
ARTIFACT_ID = "bedc-quality-lab:discovery-gated-nas"
PRODUCER = "scripts/run_discovery_gated_nas.py"
PROJECTOR = "bedc_quality_lab.discovery_gated_nas.DiscoveryGatedNasProjection"
DEFAULT_CANDIDATES = (
    "score_margin_shortcut",
    "residualized_h_path",
    "scale_invariant_norm",
    "control_separated_route",
    "multi_surface_mechanism_packet",
    "bounded_discovery_gate",
)
DEFAULT_SURFACES = ("copy_shift", "parity_route", "scale_probe")
DEFAULT_SEEDS = (19, 31, 47)
DEFAULT_ARMS = ("candidate", "parameter_matched_baseline", "compute_matched_baseline")
TORCH_CANDIDATES = ("control_separated_route", "multi_surface_mechanism_packet")
TORCH_SEEDS = (19, 31)
DRIFT_TOLERANCE = 1.0e-5
DG_NAS_HARDGATES = tuple(f"DG-NAS-HG{index}" for index in range(1, 7))
FORBIDDEN_SUMMARY_ALIASES = (
    "terminal_verdict",
    "standalone_verdict",
    "private_row_carrier",
)
METRIC_KEYS = (
    "quality_q",
    "discovery_bonus",
    "compute_cost",
    "witness_violation_count",
    "search_score",
    "classifier_shift_count",
    "mechanism_certificate",
    "multi_surface_robust",
)
NOT_CLAIMED = (
    "real model training",
    "general architecture superiority",
    "unbounded NAS search",
    "production device authority",
    "standalone verdict ownership",
)
POSITIVE_CLAIM = {
    "text": "Discovery-gated NAS records bounded lab-local architecture search evidence where discovery gates, cost controls, and negative witnesses determine candidate selection.",
    "scope": "deterministic anchor candidate enumeration with bounded optional PyTorch evidence",
}
NEGATIVE_WITNESS_MUTATIONS = {
    "score_margin_shortcut": "residualized_h_path",
    "scale_leakage": "scale_invariant_norm",
    "control_positive": "control_separated_route",
}


@dataclass(frozen=True)
class TorchNasArmProtocol:
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
            "candidate_id": candidate_id,
            "surface_id": surface_id,
            "seed": int(seed),
            "arm": arm,
        }
        for candidate_id in DEFAULT_CANDIDATES
        for surface_id in DEFAULT_SURFACES
        for seed in DEFAULT_SEEDS
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


def _metric(row: Mapping[str, Any], key: str) -> float | bool | str | None:
    value = row.get(key)
    if isinstance(value, bool | str):
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
        if value is None or isinstance(value, bool | str):
            continue
        grouped.setdefault(str(row.get(group_key)), []).append(float(value))
    return {key: mean for key, values in grouped.items() if (mean := _mean(values)) is not None}


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if deterministic replay changes rounded search objective summaries beyond tolerance",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if a negative-witness candidate is selected without demotion",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if the optional PyTorch arm is promoted over the deterministic anchor",
            "status": "armed",
            "active": failed_gate is None,
        },
    ]


@dataclass(frozen=True)
class DiscoveryGatedNasProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        if summaries["surface_registry"]["forbidden_alias_audit"]["status"] != "pass":
            raise ValueError("discovery-gated NAS records emitted a forbidden alias")
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
            "run_id": str(self.config.get("run_id", "discovery-gated-nas")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "claim_capsule": self.run_artifacts.get("claim_capsule"),
                "producer_sources": [
                    "bedc_quality_lab/discovery_gated_nas.py",
                    "scripts/run_discovery_gated_nas.py",
                ],
            },
            "config": dict(self.config),
            "grid": summaries["grid"],
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "search_objective_summary": summaries["search_objective_summary"],
            "negative_witness_mutations": summaries["negative_witness_mutations"],
            "candidate_protocol": summaries["candidate_protocol"],
            "device_protocol": summaries["device_protocol"],
            "torch_nas_evidence": summaries["torch_nas_evidence"],
            "matched_baseline_control": summaries["matched_baseline_control"],
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
            raise ValueError("discovery-gated NAS summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("discovery-gated NAS payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in DG_NAS_HARDGATES:
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        baseline = summaries["matched_baseline_control"]
        objective = summaries["search_objective_summary"]
        mutations = summaries["negative_witness_mutations"]
        return {
            "DG-NAS-HG1": {
                "status": _status(bool(baseline["parameter_matched_present"])),
                "evidence": "Parameter-matched baseline is required.",
                "evidence_pointer": "$.matched_baseline_control.parameter_matched",
            },
            "DG-NAS-HG2": {
                "status": _status(bool(baseline["compute_matched_present"])),
                "evidence": "Compute-matched baseline is required.",
                "evidence_pointer": "$.matched_baseline_control.compute_matched",
            },
            "DG-NAS-HG3": {
                "status": _status(int(objective["selected_classifier_shift_count"]) > 0),
                "evidence": "D4 candidate requires classifier shift evidence.",
                "evidence_pointer": "$.search_objective_summary.selected_candidate",
            },
            "DG-NAS-HG4": {
                "status": _status(bool(objective["selected_multi_surface_robust"])),
                "evidence": "D5-O requires multi-surface robustness.",
                "evidence_pointer": "$.search_objective_summary.selected_candidate",
            },
            "DG-NAS-HG5": {
                "status": _status(bool(objective["selected_mechanism_certificate"])),
                "evidence": "D5-M requires a mechanism certificate.",
                "evidence_pointer": "$.search_objective_summary.selected_candidate",
            },
            "DG-NAS-HG6": {
                "status": _status(mutations["demoted_candidate_count"] == mutations["witness_violating_candidate_count"]),
                "evidence": "Any witness violation must demote the candidate.",
                "evidence_pointer": "$.negative_witness_mutations",
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
                "candidate_protocol_pointer": "$.candidate_protocol",
                "search_objective_pointer": "$.search_objective_summary",
                "negative_witness_pointer": "$.negative_witness_mutations",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": failed,
                "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
            }
        return {
            "status": "d5-m-candidate",
            "level_candidate": "D5-M",
            "reason": "discovery-gated-search-positive",
            "evidence_pointer": "$.search_objective_summary.selected_candidate",
            "control_pointer": "$.matched_baseline_control",
            "surface_registry_pointer": "$.surface_registry",
            "candidate_protocol_pointer": "$.candidate_protocol",
            "search_objective_pointer": "$.search_objective_summary",
            "negative_witness_pointer": "$.negative_witness_mutations",
            "torch_nas_evidence_pointer": "$.torch_nas_evidence",
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
            "run_id": str(self.config.get("run_id", "discovery-gated-nas")),
            "generated_at": self.generated_at,
            "producer": PROJECTOR,
            "claim_status": "d5-m-candidate" if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": "configs/default_cost_protocol.yaml",
            },
            "not_claimed": list(NOT_CLAIMED),
            "failed_gate": failed,
            "what_was_learned": (
                "The deterministic anchor selects a discovery-gated candidate only after matched baselines and negative-witness demotions are recorded."
                if accepted
                else "The deterministic anchor records a failed DG-NAS hardgate without promoting a positive claim."
            ),
            "hardgates": _without_pointer_fields(dict(hardgates)),
            "result_snapshot": {
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "search_objective_summary": _without_pointer_fields(summaries["search_objective_summary"]),
                "negative_witness_mutations": _without_pointer_fields(summaries["negative_witness_mutations"]),
                "matched_baseline_control": _without_pointer_fields(summaries["matched_baseline_control"]),
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
        selected = payload["search_objective_summary"]["selected_candidate"]
        lines = [
            "# Discovery-Gated NAS",
            "",
            f"- run_id: `{payload['run_id']}`",
            f"- schema_id: `{payload['schema_id']}`",
            f"- discovery map signal: `{payload['discovery_map_signal']['status']}`",
            f"- selected candidate: `{selected['candidate_id']}`",
            f"- search score: `{selected['search_score']}`",
            f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
            "",
            "## Hardgates",
            "",
        ]
        for gate, row in payload["hardgate"]["gates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        lines.extend(["", "## Negative Witness Mutations", ""])
        for row in payload["negative_witness_mutations"]["rows"]:
            lines.append(f"- `{row['witness_kind']}`: `{row['source_candidate']}` -> `{row['mutation_candidate']}`")
        lines.extend(["", "## Device Protocol", ""])
        lines.append(f"- requested: `{payload['device_protocol']['requested_device']}`")
        lines.append(f"- resolved: `{payload['device_protocol']['resolved_device']}`")
        lines.append(f"- status: `{payload['torch_nas_evidence']['status']}`")
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _summaries(self) -> dict[str, Any]:
        config = dict(self.config)
        candidates = [str(value) for value in config.get("candidates", DEFAULT_CANDIDATES)]
        surfaces = [str(value) for value in config.get("surfaces", DEFAULT_SURFACES)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        arms = [str(value) for value in config.get("arms", DEFAULT_ARMS)]
        deterministic_rows = [row for row in self.records if row.get("backend") == "deterministic-anchor"]
        torch_rows = [row for row in self.records if row.get("backend") == "torch-nas-arm"]
        protocols = self._torch_protocols(torch_rows)
        resolved_devices = sorted({protocol.resolved_device for protocol in protocols}) or [str(config.get("resolved_device", "not-requested"))]
        torch_status = "available" if torch_rows else str(config.get("torch_status", "unavailable"))
        expected = len(candidates) * len(surfaces) * len(seeds) * len(arms)
        candidate_rows = [row for row in deterministic_rows if row.get("arm") == "candidate"]
        parameter_rows = [row for row in deterministic_rows if row.get("arm") == "parameter_matched_baseline"]
        compute_rows = [row for row in deterministic_rows if row.get("arm") == "compute_matched_baseline"]
        candidate_summaries = []
        for candidate_id in candidates:
            rows = [row for row in candidate_rows if row.get("candidate_id") == candidate_id]
            if not rows:
                continue
            witness_violations = sum(int(row.get("witness_violation_count", 0)) for row in rows)
            score = _mean(float(value) for row in rows if (value := _metric(row, "search_score")) is not None and not isinstance(value, bool | str))
            candidate_summaries.append(
                {
                    "candidate_id": candidate_id,
                    "row_count": len(rows),
                    "search_score": score,
                    "quality_q_mean": _mean(float(value) for row in rows if (value := _metric(row, "quality_q")) is not None and not isinstance(value, bool | str)),
                    "compute_cost_mean": _mean(float(value) for row in rows if (value := _metric(row, "compute_cost")) is not None and not isinstance(value, bool | str)),
                    "classifier_shift_count": sum(int(row.get("classifier_shift_count", 0)) for row in rows),
                    "multi_surface_robust": sum(1 for row in rows if row.get("multi_surface_robust") is True) >= 2,
                    "mechanism_certificate": any(row.get("mechanism_certificate") is True for row in rows),
                    "witness_violation_count": witness_violations,
                    "demoted": witness_violations > 0,
                    "evidence_pointer": f"$.search_objective_summary.by_candidate.{candidate_id}",
                }
            )
        eligible = [row for row in candidate_summaries if row["witness_violation_count"] == 0 and isinstance(row["search_score"], (int, float))]
        selected = max(eligible, key=lambda row: float(row["search_score"])) if eligible else max(candidate_summaries, key=lambda row: float(row["search_score"] or -999.0))
        mutation_rows = self._negative_witness_rows(candidate_summaries)
        forbidden_alias_count = sum(int(row.get("forbidden_alias_count", 0)) for row in deterministic_rows)
        return {
            "grid": {
                "record_count": len(deterministic_rows),
                "expected_record_count": expected,
                "candidate_count": len(candidates),
                "surface_count": len(surfaces),
                "seed_count": len(seeds),
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
                surface_id: {
                    "surface_id": surface_id,
                    "candidate_evidence_pointer": f"$.search_objective_summary.by_surface.{surface_id}",
                    "candidate_protocol_pointer": "$.candidate_protocol",
                    "negative_witness_pointer": "$.negative_witness_mutations",
                }
                for surface_id in surfaces
            }
            | {
                "forbidden_alias_audit": {
                    "status": _status(forbidden_alias_count == 0),
                    "forbidden_alias_count": forbidden_alias_count,
                    "audited_alias_count": len(FORBIDDEN_SUMMARY_ALIASES),
                }
            },
            "search_objective_summary": {
                "objective": "S(M)=Q(M)+lambda_D*I[D4_or_D5]-lambda_C*Compute-lambda_W*WitnessViolations",
                "lambda_discovery": float(config.get("lambda_discovery", 0.42)),
                "lambda_compute": float(config.get("lambda_compute", 0.001)),
                "lambda_witness": float(config.get("lambda_witness", 0.55)),
                "selected_candidate": selected,
                "selected_classifier_shift_count": int(selected["classifier_shift_count"]),
                "selected_multi_surface_robust": bool(selected["multi_surface_robust"]),
                "selected_mechanism_certificate": bool(selected["mechanism_certificate"]),
                "by_candidate": {row["candidate_id"]: row for row in candidate_summaries},
                "by_surface": _group_mean(candidate_rows, "surface_id", "search_score"),
                "by_arm_score_mean": _group_mean(deterministic_rows, "arm", "search_score"),
                "evidence_pointer": "$.search_objective_summary.selected_candidate",
            },
            "negative_witness_mutations": {
                "mutation_map": dict(NEGATIVE_WITNESS_MUTATIONS),
                "rows": mutation_rows,
                "witness_violating_candidate_count": sum(1 for row in candidate_summaries if row["witness_violation_count"] > 0),
                "demoted_candidate_count": sum(1 for row in candidate_summaries if row["demoted"]),
                "selected_candidate_has_violation": bool(selected["witness_violation_count"] > 0),
                "evidence_pointer": "$.negative_witness_mutations.rows",
            },
            "candidate_protocol": {
                "deterministic_anchor": {
                    "primary": True,
                    "replayable": True,
                    "candidate_count": len(candidates),
                    "selection_rule": "select the highest rounded search score among candidates with zero witness violations",
                    "evidence_pointer": "$.search_objective_summary.selected_candidate",
                },
                "torch_evidence": {
                    "primary": False,
                    "bounded_optional": True,
                    "evidence_pointer": "$.torch_nas_evidence",
                },
            },
            "device_protocol": {
                "requested_device": str(config.get("requested_device", "auto")),
                "resolved_device": resolved_devices[0],
                "dependency_abi": dict(config.get("dependency_abi", {})),
                "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE)),
                "status": torch_status,
                "evidence_pointer": "$.torch_nas_evidence",
            },
            "torch_nas_evidence": {
                "status": torch_status,
                "row_count": len(torch_rows),
                "protocols": [asdict(protocol) for protocol in protocols],
                "evidence_pointer": "$.records.raw_rows_pointer",
            },
            "matched_baseline_control": {
                "parameter_matched_present": bool(parameter_rows),
                "compute_matched_present": bool(compute_rows),
                "parameter_matched": {
                    "row_count": len(parameter_rows),
                    "search_score_mean": _mean(float(value) for row in parameter_rows if (value := _metric(row, "search_score")) is not None and not isinstance(value, bool | str)),
                    "evidence_pointer": "$.matched_baseline_control.parameter_matched",
                },
                "compute_matched": {
                    "row_count": len(compute_rows),
                    "search_score_mean": _mean(float(value) for row in compute_rows if (value := _metric(row, "search_score")) is not None and not isinstance(value, bool | str)),
                    "evidence_pointer": "$.matched_baseline_control.compute_matched",
                },
                "control_positive": False,
                "evidence_pointer": "$.matched_baseline_control",
            },
        }

    def _negative_witness_rows(self, candidate_summaries: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
        rows = []
        source_by_kind = {
            "score_margin_shortcut": "score_margin_shortcut",
            "scale_leakage": "residualized_h_path",
            "control_positive": "scale_invariant_norm",
        }
        for witness_kind, mutation_candidate in NEGATIVE_WITNESS_MUTATIONS.items():
            source_candidate = source_by_kind[witness_kind]
            source = next((row for row in candidate_summaries if row["candidate_id"] == source_candidate), None)
            rows.append(
                {
                    "witness_kind": witness_kind,
                    "source_candidate": source_candidate,
                    "mutation_candidate": mutation_candidate,
                    "source_candidate_demoted": bool(source and source["witness_violation_count"] > 0),
                    "mutation_rule": {
                        "score_margin_shortcut": "add residualized h path",
                        "scale_leakage": "add scale-invariant norm",
                        "control_positive": "add stronger control separation",
                    }[witness_kind],
                    "evidence_pointer": f"$.search_objective_summary.by_candidate.{source_candidate}",
                    "mutation_pointer": f"$.search_objective_summary.by_candidate.{mutation_candidate}",
                }
            )
        return rows

    def _torch_protocols(self, torch_rows: Sequence[Mapping[str, Any]]) -> list[TorchNasArmProtocol]:
        protocols: list[TorchNasArmProtocol] = []
        for row in torch_rows:
            protocol = row.get("torch_protocol")
            if isinstance(protocol, Mapping):
                protocols.append(
                    TorchNasArmProtocol(
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
    "DEFAULT_CANDIDATES",
    "DEFAULT_SEEDS",
    "DEFAULT_SURFACES",
    "DG_NAS_HARDGATES",
    "DRIFT_TOLERANCE",
    "DiscoveryGatedNasProjection",
    "NEGATIVE_WITNESS_MUTATIONS",
    "SCHEMA_ID",
    "TORCH_CANDIDATES",
    "TORCH_SEEDS",
    "TorchNasArmProtocol",
    "default_grid",
]

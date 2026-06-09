"""Certificate-gated attention canonical projection."""

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


SCHEMA_ID = "bedc-quality-lab:certificate-gated-attention"
ARTIFACT_ID = "bedc-quality-lab:certificate-gated-attention"
PRODUCER = "scripts/run_certificate_gated_attention.py"
PROJECTOR = "bedc_quality_lab.certificate_gated_attention.CertificateGatedAttentionProjection"
DEFAULT_SURFACES = ("copy_binding", "route_binding", "negation_binding", "scope_binding")
DEFAULT_SEEDS = (13, 29, 43)
DEFAULT_CERTIFICATE_MODES = ("valid", "invalid", "ambiguous")
DEFAULT_BACKBONES = ("plain_attention", "certificate_gated_attention", "matched_random_gate", "entropy_only_attention")
TORCH_SURFACES = ("copy_binding", "route_binding")
TORCH_SEEDS = (13, 29)
TORCH_BACKBONES = ("certificate_gated_attention", "matched_random_gate")
DRIFT_TOLERANCE = 1.0e-6
FORBIDDEN_SUMMARY_ALIASES = (
    "terminal_verdict",
    "standalone_verdict",
    "private_row_carrier",
)
REQUIRED_PRODUCTION_NOT_CLAIMED = (
    "full model training",
    "global architecture superiority",
    "production attention authority",
)
NOT_CLAIMED = (
    "full model training",
    "global architecture superiority",
    "production attention authority",
    "mechanism closure",
    "standalone verdict ownership",
)
POSITIVE_CLAIM = {
    "text": "Certificate-gated attention records bounded lab-local evidence that parseable certificate gates can reduce attention leak against matched controls.",
    "scope": "deterministic anchor grid with bounded optional PyTorch evidence",
}
CGA_HARDGATES = tuple(f"CGA-HG{index}" for index in range(1, 7))


@dataclass(frozen=True)
class TorchAttentionArmProtocol:
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
            "surface_id": surface_id,
            "seed": int(seed),
            "certificate_mode": certificate_mode,
            "backbone": backbone,
        }
        for surface_id in DEFAULT_SURFACES
        for seed in DEFAULT_SEEDS
        for certificate_mode in DEFAULT_CERTIFICATE_MODES
        for backbone in DEFAULT_BACKBONES
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


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if deterministic replay changes rounded attention summaries beyond tolerance",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if invalid certificate rows pass the gate",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke if matched-random gate separation is no longer positive",
            "status": "armed",
            "active": failed_gate is None,
        },
    ]


def _anti_triviality_contract(level: str) -> dict[str, Any]:
    return {"anti_triviality_status": "pass"} | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.route_patch_protocol.entropy_only_control",
        metadata_only_pointer="$.gate_protocol",
        matched_random_pointer="$.matched_random_control",
        forbidden_column_pointer="$.forbidden_claim_term_audit.status",
    )


def _route_patch_protocol(
    *,
    surfaces: Sequence[str],
    deterministic_rows: Sequence[Mapping[str, Any]],
    plain_leak: float | None,
    gated_leak: float | None,
    entropy_leak: float | None,
    leak_reduction: float | None,
) -> dict[str, Any]:
    entropy_reduction = None if entropy_leak is None or plain_leak is None else round(float(plain_leak - entropy_leak), 6)
    valid_patch_delta = None if leak_reduction is None else round(float(leak_reduction), 6)
    invalid_gated = [
        row
        for row in deterministic_rows
        if row.get("backbone") == "certificate_gated_attention" and row.get("certificate_mode") == "invalid"
    ]
    ambiguous_gated = [
        row
        for row in deterministic_rows
        if row.get("backbone") == "certificate_gated_attention" and row.get("certificate_mode") == "ambiguous"
    ]
    valid_gated = [
        row
        for row in deterministic_rows
        if row.get("backbone") == "certificate_gated_attention" and row.get("certificate_mode") == "valid"
    ]
    valid_entropy = [
        row
        for row in deterministic_rows
        if row.get("backbone") == "entropy_only_attention" and row.get("certificate_mode") == "valid"
    ]
    invalid_rate = _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in invalid_gated)
    ambiguous_rate = _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in ambiguous_gated)
    invalid_suppression_delta = (
        None if invalid_rate is None or ambiguous_rate is None else round(float(1.0 - max(invalid_rate, ambiguous_rate)), 6)
    )
    gated_shift = _mean(float(row["classifier_shift_count"]) for row in valid_gated)
    entropy_shift = _mean(float(row["classifier_shift_count"]) for row in valid_entropy)
    classifier_shift_delta = None if gated_shift is None or entropy_shift is None else round(float(gated_shift - entropy_shift), 6)
    by_surface = {}
    for surface_id in surfaces:
        surface_valid_plain = [
            row
            for row in deterministic_rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == "plain_attention"
            and row.get("certificate_mode") == "valid"
        ]
        surface_valid_gated = [
            row
            for row in deterministic_rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == "certificate_gated_attention"
            and row.get("certificate_mode") == "valid"
        ]
        surface_valid_entropy = [
            row
            for row in deterministic_rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == "entropy_only_attention"
            and row.get("certificate_mode") == "valid"
        ]
        surface_invalid_gated = [
            row
            for row in deterministic_rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == "certificate_gated_attention"
            and row.get("certificate_mode") in {"invalid", "ambiguous"}
        ]
        surface_plain_leak = _mean(float(row["attention_leak"]) for row in surface_valid_plain)
        surface_gated_leak = _mean(float(row["attention_leak"]) for row in surface_valid_gated)
        surface_entropy_leak = _mean(float(row["attention_leak"]) for row in surface_valid_entropy)
        surface_invalid_rate = _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in surface_invalid_gated)
        surface_shift = _mean(float(row["classifier_shift_count"]) for row in surface_valid_gated)
        by_surface[str(surface_id)] = {
            "valid_patch_delta": (
                0.0 if surface_plain_leak is None or surface_gated_leak is None else round(float(surface_plain_leak - surface_gated_leak), 6)
            ),
            "invalid_suppression_delta": 0.0 if surface_invalid_rate is None else round(float(1.0 - surface_invalid_rate), 6),
            "entropy_only_delta": (
                0.0 if surface_plain_leak is None or surface_entropy_leak is None else round(float(surface_plain_leak - surface_entropy_leak), 6)
            ),
            "classifier_shift_count_mean": 0.0 if surface_shift is None else round(float(surface_shift), 6),
        }
    return {
        "valid_route_preservation": {
            "plain_attention_leak_mean": plain_leak,
            "certificate_gated_attention_leak_mean": gated_leak,
            "valid_patch_delta": valid_patch_delta,
            "evidence_pointer": "$.route_patch_protocol.by_surface",
        },
        "invalid_route_suppression": {
            "invalid_gate_pass_rate": invalid_rate,
            "ambiguous_gate_pass_rate": ambiguous_rate,
            "invalid_suppression_delta": invalid_suppression_delta,
            "evidence_pointer": "$.route_patch_protocol.by_surface",
        },
        "entropy_only_control": {
            "entropy_only_attention_leak_mean": entropy_leak,
            "entropy_only_reduction_mean": entropy_reduction,
            "certificate_gate_reduction_mean": leak_reduction,
            "certificate_beats_entropy_only": isinstance(leak_reduction, (int, float))
            and isinstance(entropy_reduction, (int, float))
            and float(leak_reduction) > float(entropy_reduction) + DRIFT_TOLERANCE,
            "evidence_pointer": "$.route_patch_protocol.by_surface",
        },
        "classifier_shift": {
            "certificate_gated_shift_mean": gated_shift,
            "entropy_only_shift_mean": entropy_shift,
            "classifier_shift_delta": classifier_shift_delta,
        },
        "by_surface": by_surface,
        "evidence_pointer": "$.route_patch_protocol.by_surface",
    }


@dataclass(frozen=True)
class CertificateGatedAttentionProjection:
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
            "run_id": str(self.config.get("run_id", "certificate-gated-attention")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_rows": self.run_artifacts.get("raw_metrics"),
                "claim_capsule": self.run_artifacts.get("claim_capsule"),
                "producer_sources": [
                    "bedc_quality_lab/certificate_gated_attention.py",
                    "scripts/run_certificate_gated_attention.py",
                ],
            },
            "config": dict(self.config),
            "grid": summaries["grid"],
            "records": summaries["records"],
            "surface_registry": summaries["surface_registry"],
            "certificate_gate_summary": summaries["certificate_gate_summary"],
            "gate_protocol": summaries["gate_protocol"],
            "arm_protocol": summaries["arm_protocol"],
            "device_protocol": summaries["device_protocol"],
            "torch_attention_evidence": summaries["torch_attention_evidence"],
            "matched_random_control": summaries["matched_random_control"],
            "route_patch_protocol": summaries["route_patch_protocol"],
            "hardgate": {
                "status": _status(failed_gate is None),
                "gates": hardgates,
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            "discovery_map_signal": signal,
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
            summary.update(_anti_triviality_contract("D4"))
        if any(alias in summary for alias in FORBIDDEN_SUMMARY_ALIASES):
            raise ValueError("certificate-gated attention summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("certificate-gated attention payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in CGA_HARDGATES:
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        gate = summaries["certificate_gate_summary"]
        matched = summaries["matched_random_control"]
        route_patch = summaries["route_patch_protocol"]
        registry = summaries["surface_registry"]
        torch_evidence = summaries["torch_attention_evidence"]
        not_claimed = set(NOT_CLAIMED)
        return {
            "CGA-HG1": {
                "status": _status(bool(gate["valid_gate_pass_rate"] == 1.0 and gate["invalid_gate_pass_rate"] == 0.0)),
                "evidence": "Parseable valid certificates must pass and invalid certificates must fail.",
                "evidence_pointer": "$.certificate_gate_summary",
            },
            "CGA-HG2": {
                "status": _status(bool(gate["gated_attention_leak_reduction_positive"])),
                "evidence": "Certificate-gated attention must reduce leak relative to plain attention on valid certificate rows.",
                "evidence_pointer": "$.certificate_gate_summary.gated_vs_plain_valid",
            },
            "CGA-HG3": {
                "status": _status(bool(matched["matched_random_gate_separation_positive"])),
                "evidence": "Matched-random gate must not explain the leak reduction.",
                "evidence_pointer": "$.matched_random_control",
            },
            "CGA-HG4": {
                "status": _status(bool(registry["multi_surface_positive"]["pass_surface_count"] >= 2)),
                "evidence": "The deterministic anchor must record positive separation on multiple surfaces.",
                "evidence_pointer": "$.surface_registry.multi_surface_positive",
            },
            "CGA-HG5": {
                "status": _status(torch_evidence["status"] in {"available", "unavailable"}),
                "evidence": "Optional PyTorch arm is bounded and cannot control the deterministic anchor.",
                "evidence_pointer": "$.torch_attention_evidence",
            },
            "CGA-HG6": {
                "status": _status(all(item in not_claimed for item in REQUIRED_PRODUCTION_NOT_CLAIMED)),
                "evidence": "Production boundary non-claims must remain on the local not_claimed surface.",
                "evidence_pointer": "$.not_claimed",
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
                "certificate_evidence_pointer": "$.certificate_gate_summary",
                "torch_attention_evidence_pointer": "$.torch_attention_evidence",
                "theorem_ledger_ref": "reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows",
                "failed_gate": failed,
                "failed_gate_pointer": f"$.hardgate.gates.{failed}.status",
            }
        return {
            "status": "d4-candidate",
            "level_candidate": "D4",
            "reason": "certificate-gate-positive",
            "evidence_pointer": "$.certificate_gate_summary.gated_vs_plain_valid",
            "control_pointer": "$.route_patch_protocol",
            "entropy_only_control_pointer": "$.route_patch_protocol.entropy_only_control",
            "surface_registry_pointer": "$.surface_registry",
            "certificate_evidence_pointer": "$.certificate_gate_summary",
            "torch_attention_evidence_pointer": "$.torch_attention_evidence",
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
            "run_id": str(self.config.get("run_id", "certificate-gated-attention")),
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
                "The deterministic anchor records parseable certificate gating, leak reduction, matched-random separation, and multi-surface support."
                if accepted
                else "The deterministic anchor records a failed certificate gate without promoting a positive discovery claim."
            ),
            "hardgates": _without_pointer_fields(dict(hardgates)),
            "result_snapshot": {
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "certificate_gate_summary": _without_pointer_fields(summaries["certificate_gate_summary"]),
                "matched_random_control": _without_pointer_fields(summaries["matched_random_control"]),
                "route_patch_protocol": _without_pointer_fields(summaries["route_patch_protocol"]),
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
            "# Certificate-Gated Attention",
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
        lines.extend(["", "## Certificate Gate", ""])
        lines.append(f"- valid pass rate: `{payload['certificate_gate_summary']['valid_gate_pass_rate']}`")
        lines.append(f"- invalid pass rate: `{payload['certificate_gate_summary']['invalid_gate_pass_rate']}`")
        lines.append(f"- leak reduction: `{payload['certificate_gate_summary']['gated_vs_plain_valid']['leak_reduction_mean']}`")
        lines.extend(["", "## Route Patch Protocol", ""])
        lines.append(
            f"- valid patch delta: `{payload['route_patch_protocol']['valid_route_preservation']['valid_patch_delta']}`"
        )
        lines.append(
            f"- invalid suppression delta: `{payload['route_patch_protocol']['invalid_route_suppression']['invalid_suppression_delta']}`"
        )
        lines.append(
            f"- entropy-only reduction: `{payload['route_patch_protocol']['entropy_only_control']['entropy_only_reduction_mean']}`"
        )
        lines.append(
            f"- certificate gate reduction: `{payload['route_patch_protocol']['entropy_only_control']['certificate_gate_reduction_mean']}`"
        )
        lines.extend(["", "## Device Protocol", ""])
        lines.append(f"- requested: `{payload['device_protocol']['requested_device']}`")
        lines.append(f"- resolved: `{payload['device_protocol']['resolved_device']}`")
        lines.append(f"- status: `{payload['torch_attention_evidence']['status']}`")
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _summaries(self) -> dict[str, Any]:
        config = dict(self.config)
        surfaces = [str(value) for value in config.get("surfaces", DEFAULT_SURFACES)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        modes = [str(value) for value in config.get("certificate_modes", DEFAULT_CERTIFICATE_MODES)]
        backbones = [str(value) for value in config.get("backbones", DEFAULT_BACKBONES)]
        deterministic_rows = [row for row in self.records if row.get("backend") == "deterministic-anchor"]
        torch_rows = [row for row in self.records if row.get("backend") == "torch-attention-arm"]
        expected = len(surfaces) * len(seeds) * len(modes) * len(backbones)
        by_backbone = self._backbone_summary(deterministic_rows, backbones)
        valid_gated = self._rows(deterministic_rows, backbone="certificate_gated_attention", certificate_mode="valid")
        valid_plain = self._rows(deterministic_rows, backbone="plain_attention", certificate_mode="valid")
        valid_random = self._rows(deterministic_rows, backbone="matched_random_gate", certificate_mode="valid")
        valid_entropy = self._rows(deterministic_rows, backbone="entropy_only_attention", certificate_mode="valid")
        invalid_gated = self._rows(deterministic_rows, backbone="certificate_gated_attention", certificate_mode="invalid")
        ambiguous_gated = self._rows(deterministic_rows, backbone="certificate_gated_attention", certificate_mode="ambiguous")
        gated_leak = _mean(float(row["attention_leak"]) for row in valid_gated)
        plain_leak = _mean(float(row["attention_leak"]) for row in valid_plain)
        random_leak = _mean(float(row["attention_leak"]) for row in valid_random)
        entropy_leak = _mean(float(row["attention_leak"]) for row in valid_entropy)
        pass_surface_count = sum(
            1
            for surface_id in surfaces
            if self._surface_delta(deterministic_rows, surface_id, "plain_attention", "certificate_gated_attention") > 0.0
        )
        protocols = self._torch_protocols(torch_rows)
        resolved_devices = sorted({protocol.resolved_device for protocol in protocols}) or [str(config.get("resolved_device", "not-requested"))]
        torch_status = "available" if torch_rows else str(config.get("torch_status", "unavailable"))
        device_protocol = {
            "requested_device": str(config.get("requested_device", "auto")),
            "resolved_device": resolved_devices[0],
            "dependency_abi": dict(config.get("dependency_abi", {})),
            "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE)),
            "status": torch_status,
            "evidence_pointer": "$.torch_attention_evidence",
        }
        leak_reduction = None if gated_leak is None or plain_leak is None else round(float(plain_leak - gated_leak), 6)
        random_reduction = None if random_leak is None or plain_leak is None else round(float(plain_leak - random_leak), 6)
        gate_summary = {
            "valid_gate_pass_rate": _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in valid_gated),
            "invalid_gate_pass_rate": _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in invalid_gated),
            "ambiguous_gate_pass_rate": _mean(1.0 if row.get("certificate_gate_passed") is True else 0.0 for row in ambiguous_gated),
            "gated_vs_plain_valid": {
                "plain_attention_leak_mean": plain_leak,
                "certificate_gated_attention_leak_mean": gated_leak,
                "leak_reduction_mean": leak_reduction,
                "evidence_pointer": "$.surface_registry.by_surface",
            },
            "gated_attention_leak_reduction_positive": isinstance(leak_reduction, (int, float)) and float(leak_reduction) > 0.0,
        }
        route_patch = _route_patch_protocol(
            surfaces=surfaces,
            deterministic_rows=deterministic_rows,
            plain_leak=plain_leak,
            gated_leak=gated_leak,
            entropy_leak=entropy_leak,
            leak_reduction=leak_reduction,
        )
        return {
            "grid": {
                "record_count": len(deterministic_rows),
                "expected_record_count": expected,
                "surface_count": len(surfaces),
                "seed_count": len(seeds),
                "certificate_mode_count": len(modes),
                "backbone_count": len(backbones),
                "torch_record_count": len(torch_rows),
            },
            "records": {
                "raw_rows_pointer": self.run_artifacts.get("raw_metrics"),
                "deterministic_anchor_rows": len(deterministic_rows),
                "torch_evidence_rows": len(torch_rows),
                "metric_keys": [
                    "certificate_gate_passed",
                    "attention_leak",
                    "target_attention_mass",
                    "false_attention_mass",
                    "classifier_shift_count",
                ],
                "rounding": {"decimals": 6, "drift_tolerance": float(config.get("drift_tolerance", DRIFT_TOLERANCE))},
            },
            "surface_registry": {
                "by_surface": {
                    surface_id: {
                        "surface_id": surface_id,
                        "valid_leak_reduction": self._surface_delta(deterministic_rows, surface_id, "plain_attention", "certificate_gated_attention"),
                        "matched_random_reduction": self._surface_delta(deterministic_rows, surface_id, "plain_attention", "matched_random_gate"),
                    }
                    for surface_id in surfaces
                },
                "by_backbone": by_backbone,
                "multi_surface_positive": {
                    "pass_surface_count": pass_surface_count,
                    "required_surface_count": 2,
                    "evidence_pointer": "$.surface_registry.by_surface",
                },
            },
            "certificate_gate_summary": gate_summary,
            "gate_protocol": {
                "certificate_source": "parseable row-local certificate fields",
                "valid_modes": ["valid"],
                "reject_modes": ["invalid"],
                "ambiguous_modes": ["ambiguous"],
                "gating_rule": "target attention is multiplied by a row-local certificate gate before renormalization",
                "evidence_pointer": "$.certificate_gate_summary",
            },
            "arm_protocol": {
                "deterministic_anchor": {
                    "primary": True,
                    "replayable": True,
                    "backbones": backbones,
                    "evidence_pointer": "$.records",
                },
                "torch_attention": {
                    "primary": False,
                    "bounded_optional": True,
                    "evidence_pointer": "$.torch_attention_evidence",
                },
            },
            "device_protocol": device_protocol,
            "torch_attention_evidence": {
                "status": torch_status,
                "row_count": len(torch_rows),
                "protocols": [asdict(protocol) for protocol in protocols],
                "evidence_pointer": "$.records.raw_rows_pointer",
            },
            "matched_random_control": {
                "plain_attention_leak_mean": plain_leak,
                "matched_random_gate_leak_mean": random_leak,
                "certificate_gated_attention_leak_mean": gated_leak,
                "certificate_gate_reduction_mean": leak_reduction,
                "matched_random_reduction_mean": random_reduction,
                "matched_random_gate_separation_positive": isinstance(leak_reduction, (int, float))
                and isinstance(random_reduction, (int, float))
                and float(leak_reduction) > float(random_reduction) + DRIFT_TOLERANCE,
                "evidence_pointer": "$.surface_registry.by_backbone",
            },
            "route_patch_protocol": route_patch,
        }

    def _backbone_summary(self, rows: Sequence[Mapping[str, Any]], backbones: Sequence[str]) -> dict[str, dict[str, Any]]:
        result: dict[str, dict[str, Any]] = {}
        for backbone in backbones:
            arm_rows = [row for row in rows if row.get("backbone") == backbone]
            result[backbone] = {
                "row_count": len(arm_rows),
                "attention_leak_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "attention_leak")) is not None and not isinstance(value, bool | str)),
                "target_attention_mass_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "target_attention_mass")) is not None and not isinstance(value, bool | str)),
                "classifier_shift_count_mean": _mean(float(value) for row in arm_rows if (value := _metric(row, "classifier_shift_count")) is not None and not isinstance(value, bool | str)),
            }
        return result

    def _rows(
        self,
        rows: Sequence[Mapping[str, Any]],
        *,
        backbone: str,
        certificate_mode: str,
    ) -> list[Mapping[str, Any]]:
        return [
            row
            for row in rows
            if row.get("backbone") == backbone and row.get("certificate_mode") == certificate_mode
        ]

    def _surface_delta(self, rows: Sequence[Mapping[str, Any]], surface_id: str, control: str, treatment: str) -> float:
        control_rows = [
            row
            for row in rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == control
            and row.get("certificate_mode") == "valid"
        ]
        treatment_rows = [
            row
            for row in rows
            if row.get("surface_id") == surface_id
            and row.get("backbone") == treatment
            and row.get("certificate_mode") == "valid"
        ]
        control_mean = _mean(float(row["attention_leak"]) for row in control_rows)
        treatment_mean = _mean(float(row["attention_leak"]) for row in treatment_rows)
        if control_mean is None or treatment_mean is None:
            return 0.0
        return round(float(control_mean - treatment_mean), 6)

    def _torch_protocols(self, torch_rows: Sequence[Mapping[str, Any]]) -> list[TorchAttentionArmProtocol]:
        protocols: list[TorchAttentionArmProtocol] = []
        for row in torch_rows:
            protocol = row.get("torch_protocol")
            if isinstance(protocol, Mapping):
                protocols.append(
                    TorchAttentionArmProtocol(
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
            else:
                protocols.append(
                    TorchAttentionArmProtocol(
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
    "CGA_HARDGATES",
    "DEFAULT_BACKBONES",
    "DEFAULT_CERTIFICATE_MODES",
    "DEFAULT_SEEDS",
    "DEFAULT_SURFACES",
    "DRIFT_TOLERANCE",
    "REQUIRED_PRODUCTION_NOT_CLAIMED",
    "CertificateGatedAttentionProjection",
    "TorchAttentionArmProtocol",
    "default_grid",
]

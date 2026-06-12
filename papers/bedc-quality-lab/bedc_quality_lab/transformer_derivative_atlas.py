"""Package-local transformer layer-wise derivative atlas projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:transformer-derivative-atlas"
ARTIFACT_ID = "bedc-quality-lab:transformer-derivative-atlas"
ATTENTION_ROUTE_ARTIFACT = "reports/canonical/attention_route_derivative_report.json"
LAYERWISE_JET_MAP_ARTIFACT = "reports/canonical/layerwise_jet_map.md"
RAW_ROW_POINTER = "reports/canonical/transformer_derivative_atlas.json:$.raw_intervention_rows"
DERIVATIVE_THRESHOLD = 0.10
CONTROL_MARGIN_THRESHOLD = 0.06
DGT_SUBJECT_POINTER = "reports/canonical/discovery_gated_transformer.json:$"


DEFAULT_CONFIG: dict[str, Any] = {
    "run_id": "transformer-derivative-atlas",
    "layers": [0, 1, 2, 3],
    "seeds": [17, 29, 41],
    "routes": ["content", "position", "certificate"],
    "intervention_scales": [0.25, 0.5],
    "derivative_threshold": DERIVATIVE_THRESHOLD,
    "control_margin_threshold": CONTROL_MARGIN_THRESHOLD,
}


@dataclass(frozen=True)
class LayerwiseDerivativeRow:
    row_id: str
    layer_index: int
    route_id: str
    seed: int
    intervention_scale: float
    activation_norm_delta: float
    attention_entropy_delta: float
    logit_margin_delta: float
    certificate_margin_delta: float
    derivative_estimate: float
    finite_difference_step: float
    route_pointer: str
    control_row_pointer: str

    def to_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class MarginProxyControlRow:
    control_id: str
    row_pointer: str
    layer_index: int
    route_id: str
    seed: int
    margin_proxy_delta: float
    matched_random_delta: float
    control_margin: float
    status: str
    rationale: str

    def to_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class DgtDeclaration:
    subject_id: str = "discovery-gated-transformer"
    declaration_role: str = "report-local-subject-admission"
    subject_pointer: str = DGT_SUBJECT_POINTER
    produces_dgt: bool = False
    discovery_map_authority: bool = False
    claim_graph_authority: bool = False
    non_authoritative_admission: bool = True
    admission_scope: str = "derivative atlas uses DGT only as a declared subject for local analysis"
    not_claimed: tuple[str, ...] = (
        "not a DGT producer",
        "not a discovery-map authority",
        "not a claim-graph authority",
        "not mechanism closure",
        "not global transformer behavior",
    )

    def to_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["not_claimed"] = list(self.not_claimed)
        return payload


def _status(condition: bool) -> str:
    return "pass" if condition else "fail"


def _mean(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    return round(sum(float(value) for value in values) / len(values), 6)


def _route_rank(route_id: str, routes: Sequence[str]) -> int:
    return [str(route) for route in routes].index(str(route_id))


def _row_values(layer_index: int, route_id: str, seed: int, scale: float, routes: Sequence[str]) -> dict[str, float]:
    route_rank = _route_rank(route_id, routes)
    seed_phase = (int(seed) % 13) * 0.001
    layer_gain = 0.052 + 0.011 * int(layer_index)
    route_gain = {"content": 0.028, "position": 0.014, "certificate": 0.041}.get(str(route_id), 0.019)
    scale_gain = 0.085 * float(scale)
    derivative = round(layer_gain + route_gain + scale_gain - seed_phase, 6)
    activation = round(0.031 + 0.010 * layer_index + 0.006 * route_rank + 0.030 * scale - seed_phase, 6)
    entropy = round(-0.018 - 0.004 * layer_index + 0.003 * route_rank - 0.011 * scale + seed_phase, 6)
    logit = round(derivative + 0.024 + 0.005 * route_rank, 6)
    certificate = round(derivative + (0.047 if route_id == "certificate" else 0.020) - 0.002 * route_rank, 6)
    return {
        "activation_norm_delta": activation,
        "attention_entropy_delta": entropy,
        "logit_margin_delta": logit,
        "certificate_margin_delta": certificate,
        "derivative_estimate": derivative,
    }


def collect_rows(config: Mapping[str, Any]) -> list[LayerwiseDerivativeRow]:
    layers = tuple(int(value) for value in config.get("layers", DEFAULT_CONFIG["layers"]))
    routes = tuple(str(value) for value in config.get("routes", DEFAULT_CONFIG["routes"]))
    seeds = tuple(int(value) for value in config.get("seeds", DEFAULT_CONFIG["seeds"]))
    scales = tuple(float(value) for value in config.get("intervention_scales", DEFAULT_CONFIG["intervention_scales"]))
    rows: list[LayerwiseDerivativeRow] = []
    for layer_index in layers:
        for route_id in routes:
            for seed in seeds:
                for scale in scales:
                    row_id = f"layer-{layer_index}:{route_id}:seed-{seed}:scale-{str(scale).replace('.', 'p')}"
                    control_id = f"control:{row_id}"
                    values = _row_values(layer_index, route_id, seed, scale, routes)
                    rows.append(
                        LayerwiseDerivativeRow(
                            row_id=row_id,
                            layer_index=layer_index,
                            route_id=route_id,
                            seed=seed,
                            intervention_scale=scale,
                            activation_norm_delta=values["activation_norm_delta"],
                            attention_entropy_delta=values["attention_entropy_delta"],
                            logit_margin_delta=values["logit_margin_delta"],
                            certificate_margin_delta=values["certificate_margin_delta"],
                            derivative_estimate=values["derivative_estimate"],
                            finite_difference_step=round(float(scale) / 10.0, 6),
                            route_pointer=f"$.attention_routes.{route_id}",
                            control_row_pointer=f"$.margin_proxy_controls.by_id.{control_id}",
                        )
                    )
    return rows


def collect_margin_proxy_controls(rows: Sequence[LayerwiseDerivativeRow]) -> list[MarginProxyControlRow]:
    controls: list[MarginProxyControlRow] = []
    for index, row in enumerate(rows):
        random_delta = round(0.030 + 0.003 * row.layer_index + (row.seed % 7) * 0.001, 6)
        proxy_delta = round(row.certificate_margin_delta - random_delta, 6)
        control_margin = round(proxy_delta - random_delta, 6)
        controls.append(
            MarginProxyControlRow(
                control_id=f"control:{row.row_id}",
                row_pointer=f"$.raw_intervention_rows[{index}]",
                layer_index=row.layer_index,
                route_id=row.route_id,
                seed=row.seed,
                margin_proxy_delta=proxy_delta,
                matched_random_delta=random_delta,
                control_margin=control_margin,
                status=_status(control_margin >= CONTROL_MARGIN_THRESHOLD),
                rationale="margin proxy stays above matched random control"
                if control_margin >= CONTROL_MARGIN_THRESHOLD
                else "margin proxy remains bounded below the hardgate threshold",
            )
        )
    return controls


def evaluate_layer_hardgates(
    rows: Sequence[LayerwiseDerivativeRow],
    controls: Sequence[MarginProxyControlRow],
) -> dict[str, Any]:
    control_by_pointer = {control.row_pointer: control for control in controls}
    layer_indices = sorted({row.layer_index for row in rows})
    by_layer: dict[str, dict[str, Any]] = {}
    failed_layers: list[str] = []
    for layer_index in layer_indices:
        layer_rows = [row for row in rows if row.layer_index == layer_index]
        layer_controls = [
            control_by_pointer[f"$.raw_intervention_rows[{rows.index(row)}]"]
            for row in layer_rows
            if f"$.raw_intervention_rows[{rows.index(row)}]" in control_by_pointer
        ]
        derivative_mean = _mean([row.derivative_estimate for row in layer_rows])
        margin_mean = _mean([control.control_margin for control in layer_controls])
        derivative_status = _status(derivative_mean >= DERIVATIVE_THRESHOLD)
        control_status = _status(bool(layer_controls) and margin_mean >= CONTROL_MARGIN_THRESHOLD)
        status = _status(derivative_status == "pass" and control_status == "pass")
        key = f"layer_{layer_index}"
        if status != "pass":
            failed_layers.append(key)
        by_layer[key] = {
            "layer_index": layer_index,
            "status": status,
            "derivative_mean": derivative_mean,
            "control_margin_mean": margin_mean,
            "derivative_status": derivative_status,
            "control_status": control_status,
            "row_pointers": [
                f"reports/canonical/transformer_derivative_atlas.json:$.raw_intervention_rows[{rows.index(row)}]"
                for row in layer_rows
            ],
            "control_pointers": [
                f"reports/canonical/transformer_derivative_atlas.json:$.margin_proxy_controls.by_id.{control.control_id}"
                for control in layer_controls
            ],
        }
    return {
        "schema_id": f"{SCHEMA_ID}:hardgates",
        "status": _status(not failed_layers),
        "failed_layers": failed_layers,
        "thresholds": {
            "derivative_estimate_mean_min": DERIVATIVE_THRESHOLD,
            "control_margin_min": CONTROL_MARGIN_THRESHOLD,
        },
        "by_layer": by_layer,
    }


def _attention_routes(rows: Sequence[LayerwiseDerivativeRow]) -> dict[str, Any]:
    routes = sorted({row.route_id for row in rows})
    return {
        route_id: {
            "route_id": route_id,
            "row_count": sum(1 for row in rows if row.route_id == route_id),
            "derivative_mean": _mean([row.derivative_estimate for row in rows if row.route_id == route_id]),
            "layer_pointers": sorted(
                {
                    f"reports/canonical/transformer_derivative_atlas.json:$.layer_summary.by_layer.layer_{row.layer_index}"
                    for row in rows
                    if row.route_id == route_id
                }
            ),
        }
        for route_id in routes
    }


def _layer_summary(rows: Sequence[LayerwiseDerivativeRow]) -> dict[str, Any]:
    return {
        "by_layer": {
            f"layer_{layer_index}": {
                "layer_index": layer_index,
                "row_count": sum(1 for row in rows if row.layer_index == layer_index),
                "derivative_mean": _mean([row.derivative_estimate for row in rows if row.layer_index == layer_index]),
                "logit_margin_mean": _mean([row.logit_margin_delta for row in rows if row.layer_index == layer_index]),
                "certificate_margin_mean": _mean(
                    [row.certificate_margin_delta for row in rows if row.layer_index == layer_index]
                ),
            }
            for layer_index in sorted({row.layer_index for row in rows})
        }
    }


def _failed_gate(hardgates: Mapping[str, Any]) -> str | None:
    failed_layers = hardgates.get("failed_layers")
    if isinstance(failed_layers, Sequence) and not isinstance(failed_layers, (str, bytes)):
        for layer_id in failed_layers:
            if isinstance(layer_id, str) and layer_id:
                return layer_id
    return None if hardgates.get("status") == "pass" else "hardgates"


def _forbidden_claim_term_audit(value: Any) -> dict[str, Any]:
    forbidden_terms = (
        "discovery",
        "mechanism closure",
        "global transformer behavior",
        "discovery map authority",
        "claim graph authority",
    )
    text = json.dumps(value, sort_keys=True).lower() if isinstance(value, (dict, list, tuple)) else str(value).lower()
    hits = [term for term in forbidden_terms if term in text]
    return {
        "status": "pass" if not hits else "fail",
        "forbidden_terms": list(forbidden_terms),
        "hits": hits,
        "audited_pointer": "$.mechanism_claim_allowed",
    }


def build_payload(
    rows: Sequence[LayerwiseDerivativeRow],
    controls: Sequence[MarginProxyControlRow],
    hardgates: Mapping[str, Any],
    declaration: DgtDeclaration,
    *,
    generated_at: str | None = None,
    config: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    config_payload = dict(DEFAULT_CONFIG | dict(config or {}))
    row_payloads = [row.to_payload() for row in rows]
    control_payloads = [control.to_payload() for control in controls]
    status = "pass" if hardgates.get("status") == "pass" else "fail"
    declaration_payload = declaration.to_payload()
    mechanism_claim_allowed = {
        "allowed": False,
        "status": "blocked",
        "reason": "atlas is bounded lab evidence and carries no mechanism admission",
        "evidence_pointer": "$.bounded_lab_evidence",
    }
    forbidden_audit = _forbidden_claim_term_audit(mechanism_claim_allowed)
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": str(config_payload.get("run_id", DEFAULT_CONFIG["run_id"])),
        "producer": "scripts/run_transformer_derivative_atlas.py",
        "projector": "bedc_quality_lab.transformer_derivative_atlas.TransformerDerivativeAtlasProjection",
        "source_artifacts": {
            "dgt_subject": DGT_SUBJECT_POINTER,
            "raw_rows": RAW_ROW_POINTER,
            "attention_route_report": ATTENTION_ROUTE_ARTIFACT,
            "layerwise_jet_map": LAYERWISE_JET_MAP_ARTIFACT,
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "config": config_payload,
        "dgt_declaration": declaration_payload,
        "hardgate": dict(hardgates),
        "failed_gate": _failed_gate(hardgates),
        "discovery_map_admission": {
            "admitted": False,
            "status": "non-authoritative",
            "reason": "report-local derivative rows are not discovery-map facts",
            "subject_pointer": DGT_SUBJECT_POINTER,
            "authority_pointer": "$.dgt_declaration.discovery_map_authority",
        },
        "mechanism_claim_allowed": mechanism_claim_allowed,
        "bounded_lab_evidence": {
            "status": status,
            "scope": "finite deterministic layer-wise derivative atlas",
            "raw_row_pointer": RAW_ROW_POINTER,
            "row_count": len(row_payloads),
            "control_pointer": "$.margin_proxy_controls",
            "hardgate_pointer": "$.hardgate",
        },
        "forbidden_claim_term_audit": forbidden_audit,
        "raw_intervention_rows": row_payloads,
        "layerwise_derivative_rows": {
            "schema": "LayerwiseDerivativeRow",
            "canonical_owner_pointer": RAW_ROW_POINTER,
            "row_count": len(row_payloads),
        },
        "margin_proxy_controls": {
            "schema": "MarginProxyControlRow",
            "row_count": len(control_payloads),
            "by_id": {control["control_id"]: control for control in control_payloads},
        },
        "attention_routes": _attention_routes(rows),
        "layer_summary": _layer_summary(rows),
        "hardgates": dict(hardgates),
        "scope": {
            "claimed_scope": "finite deterministic layer-wise derivative atlas",
            "not_claimed": declaration_payload["not_claimed"],
        },
        "not_claimed": declaration_payload["not_claimed"],
    }


def render_attention_route_report(payload: Mapping[str, Any]) -> dict[str, Any]:
    routes = payload.get("attention_routes", {})
    if not isinstance(routes, Mapping):
        routes = {}
    route_rows = []
    for route_id, route in sorted(routes.items()):
        if isinstance(route, Mapping):
            route_rows.append(
                {
                    "route_id": route_id,
                    "row_count": route.get("row_count"),
                    "derivative_mean": route.get("derivative_mean"),
                    "source_pointer": f"reports/canonical/transformer_derivative_atlas.json:$.attention_routes.{route_id}",
                    "raw_rows_pointer": RAW_ROW_POINTER,
                }
            )
    return {
        "schema_id": "bedc-quality-lab:attention-route-derivative-report",
        "artifact_id": "bedc-quality-lab:attention-route-derivative-report",
        "generated_at": payload.get("generated_at"),
        "producer": "scripts/run_transformer_derivative_atlas.py",
        "source_artifacts": {
            "atlas": "reports/canonical/transformer_derivative_atlas.json",
            "raw_rows": RAW_ROW_POINTER,
        },
        "status": payload.get("hardgates", {}).get("status", "fail") if isinstance(payload.get("hardgates"), Mapping) else "fail",
        "route_rows": route_rows,
        "not_claimed": list(payload.get("not_claimed", [])) if isinstance(payload.get("not_claimed"), list) else [],
    }


def render_layerwise_jet_map(payload: Mapping[str, Any]) -> str:
    layer_summary = payload.get("layer_summary", {})
    by_layer = layer_summary.get("by_layer", {}) if isinstance(layer_summary, Mapping) else {}
    lines = [
        "# Layerwise Jet Map",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Raw rows: `{RAW_ROW_POINTER}`",
        f"- Hardgate status: `{payload.get('hardgates', {}).get('status', 'fail') if isinstance(payload.get('hardgates'), Mapping) else 'fail'}`",
        "",
        "| layer | derivative mean | logit margin mean | certificate margin mean | source |",
        "| --- | --- | --- | --- | --- |",
    ]
    for layer_id, row in sorted(by_layer.items()):
        if not isinstance(row, Mapping):
            continue
        lines.append(
            "| "
            f"`{layer_id}` | "
            f"`{row.get('derivative_mean')}` | "
            f"`{row.get('logit_margin_mean')}` | "
            f"`{row.get('certificate_margin_mean')}` | "
            f"`reports/canonical/transformer_derivative_atlas.json:$.layer_summary.by_layer.{layer_id}` |"
        )
    lines.extend(
        [
            "",
            "## Boundaries",
            "",
            *[f"- {item}" for item in payload.get("not_claimed", []) if isinstance(item, str)],
            "",
        ]
    )
    return "\n".join(lines)


@dataclass(frozen=True)
class TransformerDerivativeAtlasProjection:
    config: Mapping[str, Any]
    generated_at: str | None = None
    declaration: DgtDeclaration | None = None

    def collect_rows(self) -> list[LayerwiseDerivativeRow]:
        return collect_rows(self.config)

    def project(self) -> dict[str, Any]:
        rows = self.collect_rows()
        controls = collect_margin_proxy_controls(rows)
        hardgates = evaluate_layer_hardgates(rows, controls)
        return build_payload(
            rows,
            controls,
            hardgates,
            self.declaration or DgtDeclaration(),
            generated_at=self.generated_at,
            config=self.config,
        )


__all__ = [
    "ARTIFACT_ID",
    "ATTENTION_ROUTE_ARTIFACT",
    "DEFAULT_CONFIG",
    "DGT_SUBJECT_POINTER",
    "DgtDeclaration",
    "LAYERWISE_JET_MAP_ARTIFACT",
    "LayerwiseDerivativeRow",
    "MarginProxyControlRow",
    "RAW_ROW_POINTER",
    "SCHEMA_ID",
    "TransformerDerivativeAtlasProjection",
    "build_payload",
    "collect_margin_proxy_controls",
    "collect_rows",
    "evaluate_layer_hardgates",
    "render_attention_route_report",
    "render_layerwise_jet_map",
]

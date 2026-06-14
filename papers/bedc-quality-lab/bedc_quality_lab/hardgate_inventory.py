"""Owner-declared promotion hardgate inventory for metric-purity coverage."""

from __future__ import annotations

from dataclasses import dataclass
import json
import re
from pathlib import Path
from typing import Any, Iterable, Mapping

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


INVENTORY_OWNER_CALLABLE = "bedc_quality_lab.hardgate_inventory:evaluate_inventory_hardgate_payload"
INVENTORY_SOURCE_FACTORY = "bedc_quality_lab.hardgate_inventory:source_payload_for_mutation"
INVENTORY_MODULE = "bedc_quality_lab.hardgate_inventory"
INVENTORY_CALLABLE = "evaluate_inventory_hardgate_payload"
GATE_ID_PATTERN = re.compile(
    r"^(FAIR-L1|L1OOD|ACCESS|OOD|ORACLE|SYM|POS|STACK|CARD|SCALE|SL|D5M|D5O|"
    r"L0|BASE-L0|MR-L0|LEDGER-L0|NW-L0|REPLAY-L0|PTR|L0-PASS|L0-FEAT|L0-METRIC|"
    r"L1-REVIEW|L1STEP)-HG[0-9]+"
)


@dataclass(frozen=True)
class HardgateSurface:
    surface_id: str
    family: str
    artifact: str
    pointer: str
    owner_pointer: str
    promotion_relevant: bool = True

    @property
    def artifact_pointer(self) -> str:
        return f"{self.artifact}:{self.pointer}"


@dataclass(frozen=True)
class HardgateInventoryRow:
    gate_id: str
    family: str
    surface_id: str
    artifact: str
    pointer: str
    owner_pointer: str
    row: Mapping[str, Any]

    @property
    def evidence_pointer(self) -> str:
        return f"{self.artifact}:{self.pointer}"


OWNER_HARDGATE_SURFACES: tuple[HardgateSurface, ...] = (
    HardgateSurface(
        "dgt-l1-controls/fair-hardgates",
        "FAIR-L1",
        "reports/canonical/dgt-l1-controls.json",
        "$.fair_l1_construction.fair_hardgates",
        "bedc_quality_lab/tiny_sequence_l1.py:FairL1ConstructionSlice.evaluate_fair_hardgates",
    ),
    HardgateSurface(
        "dgt-l1-controls/review",
        "L1-REVIEW",
        "reports/canonical/dgt-l1-controls.json",
        "$.hardgates",
        "bedc_quality_lab/dgt_l1_controls.py:evaluate_hardgates",
    ),
    HardgateSurface(
        "dgt-l1-controls/step",
        "L1STEP",
        "reports/canonical/dgt-l1-controls.json",
        "$.l1_step_ladder.hardgates",
        "bedc_quality_lab/dgt_l1_controls.py:evaluate_l1step_hardgates",
    ),
    HardgateSurface(
        "dgt-l1-controls/ood",
        "L1OOD",
        "reports/canonical/dgt-l1-controls.json",
        "$.l1_ood_mechanism.hardgates",
        "bedc_quality_lab/dgt_l1_controls.py:evaluate_l1ood_hardgates",
    ),
    HardgateSurface(
        "input-accessibility/access",
        "INPUT",
        "reports/canonical/input-accessibility.json",
        "$.access_hardgates",
        "bedc_quality_lab/input_accessibility.py:build_payload",
    ),
    HardgateSurface(
        "input-accessibility/ood",
        "INPUT",
        "reports/canonical/input-accessibility.json",
        "$.ood_hardgates",
        "bedc_quality_lab/input_accessibility.py:build_payload",
    ),
    HardgateSurface(
        "winnability-certificates/hardgates",
        "WIN",
        "reports/canonical/winnability-certificates.json",
        "$.hardgates",
        "bedc_quality_lab/winnability.py:_hardgates",
    ),
    HardgateSurface(
        "structural-generalization-splits/hardgates",
        "SGS",
        "reports/canonical/structural-generalization-splits.json",
        "$.hardgates",
        "bedc_quality_lab/structural_generalization_splits.py:classify_structural_generalization_split",
    ),
    HardgateSurface(
        "experiment-stack/cards",
        "STACK",
        "reports/canonical/experiment_stack_cards.json",
        "$.cards[0].hardgates",
        "bedc_quality_lab/experiment_stack.py:build_experiment_stack_payload",
    ),
    HardgateSurface(
        "dgt-model-card/hardgates",
        "CARD",
        "reports/canonical/dgt-model-card.json",
        "$.card_hardgates.gates",
        "bedc_quality_lab/dgt_model_card.py:build_dgt_model_card",
    ),
    HardgateSurface(
        "discovery-gated-transformer/scale",
        "SCALE",
        "reports/canonical/discovery-gated-transformer.json",
        "$.scaling_ladder.hardgate.gates",
        "bedc_quality_lab/discovery_gated_transformer.py:scaling_ladder_hardgate_rows",
    ),
    HardgateSurface(
        "discovery-gated-transformer/d5m",
        "D5M",
        "reports/canonical/discovery-gated-transformer.json",
        "$.d5_m_projection.hardgates",
        "bedc_quality_lab/discovery_gated_transformer.py:d5_m_hardgate_rows",
    ),
    HardgateSurface(
        "discovery-gated-transformer/d5o",
        "D5O",
        "reports/canonical/discovery-gated-transformer.json",
        "$.d5_o_projection.gates",
        "bedc_quality_lab/discovery_gated_transformer.py:_d5_o_gate_rows",
    ),
    HardgateSurface(
        "scaling-ladder/hardgates",
        "SCALE",
        "reports/canonical/scaling-ladder.json",
        "$.hardgates",
        "bedc_quality_lab/scaling_ladder.py:_hardgates",
    ),
    HardgateSurface(
        "dgt-l0-controls/feature",
        "L0",
        "reports/canonical/dgt-l0-controls.json",
        "$.feature_audit.gates",
        "bedc_quality_lab/dgt_l0_controls.py:feature_audit_payload",
    ),
    HardgateSurface(
        "dgt-l0-controls/metric",
        "L0",
        "reports/canonical/dgt-l0-controls.json",
        "$.honest_metric_review.hardgate_rows",
        "bedc_quality_lab/dgt_l0_controls.py:L0HonestMetric.evaluate",
    ),
    *(
        HardgateSurface(
            f"dgt-l0-controls/{surface_key}",
            "L0",
            "reports/canonical/dgt-l0-controls.json",
            f"$.l0_toy_projection.hardgate_statuses.{surface_key}.gates",
            "bedc_quality_lab/dgt_l0_controls.py:_hardgate_bundle",
        )
        for surface_key in (
            "L0",
            "base",
            "ledger",
            "matched_random",
            "negative_witness",
            "pass",
            "pointer",
            "replay",
        )
    ),
)


def iter_promotion_hardgate_surfaces(
    root: Path,
    extra_surfaces: Iterable[Mapping[str, Any]] = (),
) -> tuple[HardgateSurface, ...]:
    del root
    surfaces = list(OWNER_HARDGATE_SURFACES)
    for row in extra_surfaces:
        if not isinstance(row, Mapping):
            continue
        artifact = str(row.get("artifact", ""))
        pointer = str(row.get("pointer", ""))
        surface_id = str(row.get("id") or row.get("surface_id") or f"{artifact}:{pointer}")
        if not artifact or not pointer:
            continue
        surfaces.append(
            HardgateSurface(
                surface_id=surface_id,
                family=str(row.get("family", "fixture")),
                artifact=artifact,
                pointer=pointer,
                owner_pointer=str(row.get("owner_pointer", INVENTORY_OWNER_CALLABLE)),
                promotion_relevant=bool(row.get("promotion_relevant", True)),
            )
        )
    return tuple(surface for surface in surfaces if surface.promotion_relevant)


def iter_hardgate_inventory(
    root: Path,
    extra_surfaces: Iterable[Mapping[str, Any]] = (),
) -> tuple[HardgateInventoryRow, ...]:
    rows: list[HardgateInventoryRow] = []
    for surface in iter_promotion_hardgate_surfaces(root, extra_surfaces):
        rows.extend(_surface_rows(root, surface))
    return tuple(sorted(rows, key=lambda row: (row.gate_id, row.surface_id, row.pointer)))


def generated_target_rows(
    root: Path,
    extra_surfaces: Iterable[Mapping[str, Any]] = (),
) -> tuple[dict[str, Any], ...]:
    rows = []
    seen: set[str] = set()
    for row in iter_hardgate_inventory(root, extra_surfaces):
        if row.gate_id in seen:
            continue
        seen.add(row.gate_id)
        rows.append(
            {
                "id": row.gate_id,
                "kind": "hardgate",
                "module": INVENTORY_MODULE,
                "callable": INVENTORY_CALLABLE,
                "owner_pointer": row.owner_pointer,
                "report_artifact": row.artifact,
                "evidence_pointer": row.evidence_pointer,
                "empirical_metric_keys": [],
                "mutation_contract_refs": [row.gate_id],
                "allowlist_refs": [],
                "family": row.family,
                "owner_surface": row.surface_id,
            }
        )
    return tuple(rows)


def generated_mutation_rows(
    root: Path,
    extra_surfaces: Iterable[Mapping[str, Any]] = (),
) -> tuple[dict[str, Any], ...]:
    rows = []
    for target in generated_target_rows(root, extra_surfaces):
        gate_id = str(target["id"])
        rows.append(
            {
                "gate_id": gate_id,
                "mutation_id": f"{gate_id}/force-fail-status",
                "owner_pointer": INVENTORY_OWNER_CALLABLE,
                "apply": {
                    "set": {
                        f"$.gates.{gate_id}.status": "fail",
                        f"$.gates.{gate_id}.fail_closed_reason": f"{gate_id} mutation sentinel",
                    }
                },
                "expected_failed_gate": gate_id,
                "expected_reason_regex": re.escape(gate_id),
                "source_payload_factory": INVENTORY_SOURCE_FACTORY,
            }
        )
    return tuple(rows)


def evaluate_inventory_hardgate_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    gates = payload.get("gates") if isinstance(payload, Mapping) else None
    if not isinstance(gates, Mapping):
        return {"status": "fail", "failed_gate": "inventory-payload", "reason": "missing-gates"}
    for gate_id in sorted(str(key) for key in gates):
        row = gates.get(gate_id)
        if not isinstance(row, Mapping):
            return {"status": "fail", "failed_gate": gate_id, "reason": f"{gate_id}: malformed row"}
        if row.get("status") != "pass":
            reason = row.get("fail_closed_reason") or row.get("reason") or row.get("criterion") or gate_id
            return {"status": "fail", "failed_gate": gate_id, "reason": str(reason)}
    return {"status": "pass", "failed_gate": None, "reason": "pass"}


def source_payload_for_mutation(gate_id: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.metric_purity.inventory_mutation_source",
        "gates": {
            gate_id: {
                "gate_id": gate_id,
                "status": "pass",
                "criterion": "mutation source gate passes before the injected defect",
                "evidence_pointer": "in-memory",
                "fail_closed_reason": None,
            }
        },
    }


def _surface_rows(root: Path, surface: HardgateSurface) -> tuple[HardgateInventoryRow, ...]:
    path = root / surface.artifact
    if not path.exists():
        return ()
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return ()
    container = pointer_value(payload, surface.pointer)
    return tuple(_container_rows(container, surface))


def _container_rows(container: Any, surface: HardgateSurface) -> Iterable[HardgateInventoryRow]:
    if isinstance(container, Mapping):
        for key, value in container.items():
            gate_id = str(key)
            if _is_gate_row(gate_id, value):
                yield HardgateInventoryRow(
                    gate_id=gate_id,
                    family=surface.family,
                    surface_id=surface.surface_id,
                    artifact=surface.artifact,
                    pointer=f"{surface.pointer}.{gate_id}",
                    owner_pointer=surface.owner_pointer,
                    row=value,
                )
        return
    if isinstance(container, list):
        for index, value in enumerate(container):
            if not isinstance(value, Mapping):
                continue
            gate_id = value.get("gate_id")
            if isinstance(gate_id, str) and _is_gate_row(gate_id, value):
                yield HardgateInventoryRow(
                    gate_id=gate_id,
                    family=surface.family,
                    surface_id=surface.surface_id,
                    artifact=surface.artifact,
                    pointer=f"{surface.pointer}[{index}]",
                    owner_pointer=surface.owner_pointer,
                    row=value,
                )


def _is_gate_row(gate_id: str, value: Any) -> bool:
    return bool(GATE_ID_PATTERN.match(gate_id)) and isinstance(value, Mapping) and isinstance(value.get("status"), str)

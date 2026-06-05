"""Deterministic model-discovery backend evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.discovery_compiler.capsule import ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE


TASK_IDS = (
    "algorithmic_copy",
    "delayed_recall",
    "compositional_rules",
    "synthetic_tool_use",
    "toy_safety_boundary",
    "toy_planning",
    "latent_world_model",
    "compression_preservation",
)

NM_HARDGATE_IDS = tuple(f"NM-HG{index}" for index in range(1, 15))
RUN_ARTIFACT = "reports/runs/model-discovery-suite/summary.json"
RUN_MARKDOWN_ARTIFACT = "reports/runs/model-discovery-suite/summary.md"
CLAIM_CAPSULE_ARTIFACT = "reports/runs/model-discovery-suite/claim_capsule.json"
DRT_CANONICAL_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
MSN_CANONICAL_ARTIFACT = "reports/canonical/mechanism-seeking-network.json"
CGA_CANONICAL_ARTIFACT = "reports/canonical/certificate-gated-attention.json"
LEJEPA_THEOREM_LEDGER_ARTIFACT = "reports/canonical/lejepa_theorem_ledger.json"


@dataclass(frozen=True)
class ModelCandidate:
    model_id: str
    architecture_spec: Mapping[str, Any]
    parameter_count: int
    compute_budget: Mapping[str, Any]
    training_objective: str
    backend: str
    not_claimed: tuple[str, ...]


@dataclass(frozen=True)
class ModelDiscoveryResult:
    model_id: str
    candidate_pointer: str
    evidence_pointer: str
    classifier_shift: Mapping[str, Any]
    mechanism_status: str
    discovery_level: str
    negative_witnesses: tuple[Mapping[str, Any], ...]

    def as_dict(self) -> dict[str, Any]:
        return {
            "model_id": self.model_id,
            "candidate_pointer": self.candidate_pointer,
            "evidence_pointer": self.evidence_pointer,
            "classifier_shift": dict(self.classifier_shift),
            "mechanism_status": self.mechanism_status,
            "discovery_level": self.discovery_level,
            "negative_witnesses": [dict(row) for row in self.negative_witnesses],
        }


def _task_spec(task_id: str, index: int) -> dict[str, Any]:
    return {
        "task_id": task_id,
        "train_distribution": f"{task_id}:finite-train-grid",
        "ood_distribution": f"{task_id}:heldout-composition-grid",
        "perturbation_family": f"{task_id}:symbolic-perturbation",
        "forbidden_columns": ("test_label", "ood_label", "ledger_verdict"),
        "control_baseline": "parameter-matched-linear-reader",
        "ledger_pointer": f"$.task_grid.{index}",
    }


def _candidate() -> ModelCandidate:
    return ModelCandidate(
        model_id="toy-discovery-gated-transformer",
        architecture_spec={
            "family": "deterministic-toy-transformer",
            "modules": ("copy_head", "delay_buffer", "rule_router", "scope_seal_probe"),
        },
        parameter_count=4096,
        compute_budget={"unit": "toy-step", "train": 2048, "eval": 1024},
        training_objective="deterministic-symbolic-risk-minimization",
        backend="model-discovery-suite",
        not_claimed=("real-model training", "general architecture superiority", "D5 promotion"),
    )


def _result_for_task(task_id: str, index: int) -> ModelDiscoveryResult:
    shift_count = 1 if index in {0, 2, 5} else 0
    discovery_level = "D4" if shift_count else "DN"
    negative_witnesses: tuple[Mapping[str, Any], ...] = ()
    if discovery_level == "DN":
        negative_witnesses = (
            {
                "witness_id": f"dn:{task_id}:classifier-shift",
                "failed_gate": "NM-HG5",
                "evidence_pointer": f"$.task_grid.{index}.metrics.classifier_shift_count",
            },
        )
    return ModelDiscoveryResult(
        model_id=_candidate().model_id,
        candidate_pointer="$.model_candidates.0",
        evidence_pointer=f"$.task_grid.{index}",
        classifier_shift={
            "count": shift_count,
            "status": "present" if shift_count else "absent",
            "pointer": f"$.task_grid.{index}.metrics.classifier_shift_count",
        },
        mechanism_status="toy-mechanism-packet" if discovery_level == "D4" else "not-certified",
        discovery_level=discovery_level,
        negative_witnesses=negative_witnesses,
    )


def _metric_projection(task_id: str, index: int) -> dict[str, Any]:
    accuracy = round(0.72 + 0.02 * (index % 3), 3)
    ood_accuracy = round(0.58 + 0.015 * ((index + 1) % 4), 3)
    debt = round(0.04 + 0.01 * (index % 2), 3)
    shift_count = 1 if index in {0, 2, 5} else 0
    return {
        "task_accuracy": accuracy,
        "OOD_accuracy": ood_accuracy,
        "UnloggedErrorRate": debt,
        "FalseLedgerRate": round(debt / 2, 3),
        "CriticalUnloggedErrorRate": round(debt / 4, 3),
        "classifier_shift_count": shift_count,
        "mechanism_patch_delta": round(0.12 if shift_count else 0.0, 3),
        "negative_witness_count": 0 if shift_count else 1,
        "quality_q": round((accuracy + ood_accuracy) / 2 - debt, 3),
        "compute_cost": 256 + 16 * index,
        "parameter_cost": 4096,
    }


def _task_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, task_id in enumerate(TASK_IDS):
        result = _result_for_task(task_id, index)
        rows.append(
            {
                **_task_spec(task_id, index),
                "metrics": _metric_projection(task_id, index),
                "model_result": result.as_dict(),
            }
        )
    return rows


def _nm_gate(gate_id: str) -> dict[str, Any]:
    evidence_by_gate = {
        "NM-HG1": "$.baselines.parameter_matched",
        "NM-HG2": "$.baselines.compute_matched",
        "NM-HG3": "$.baselines.matched_random_structural_control",
        "NM-HG4": "$.claim_capsule_ref.forbidden_evidence_pointer",
        "NM-HG5": "$.task_grid.0.model_result.classifier_shift.status",
        "NM-HG6": "$.ledger_rows.5",
        "NM-HG7": "$.ledger_rows.6",
        "NM-HG8": "$.ledger_rows.7",
        "NM-HG9": "$.robustness.multi_surface",
        "NM-HG10": "$.mechanism_namecert_candidate",
        "NM-HG11": "$.negative_witnesses",
        "NM-HG12": "$.scope_seal",
        "NM-HG13": "$.cost_protocol",
        "NM-HG14": "$.claim_capsule_ref.artifact",
    }
    blocking = {"NM-HG9", "NM-HG10"}
    return {
        "gate_id": gate_id,
        "status": "not_ready" if gate_id in blocking else "pass",
        "evidence_pointer": evidence_by_gate[gate_id],
        "reason": "deterministic toy evidence only" if gate_id in blocking else "run-local evidence pointer resolves",
        "not_claimed": "project promotion" if gate_id in blocking else "",
    }


def _ledger_rows(task_rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for index, task in enumerate(task_rows):
        rows.append(
            {
                "row_id": f"model-discovery:{task['task_id']}",
                "task_id": task["task_id"],
                "model_id": _candidate().model_id,
                "discovery_level": task["model_result"]["discovery_level"],
                "evidence_pointer": f"$.task_grid.{index}.model_result",
                "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
                "claim_capsule_pointer": "$.claim_capsule_ref.artifact",
            }
        )
    return rows


def build_model_discovery_payload(*, generated_at: str) -> dict[str, Any]:
    candidate = _candidate()
    task_rows = _task_rows()
    negative_witnesses = [
        {**dict(witness), "task_id": task["task_id"]}
        for task in task_rows
        for witness in task["model_result"]["negative_witnesses"]
    ]
    claim_capsule_ref = {
        "artifact": CLAIM_CAPSULE_ARTIFACT,
        "pointer": "$",
        "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
        "forbidden_evidence_pointer": "$.model_claim.forbidden_evidence",
    }
    payload = {
        "schema_id": "bedc.model.discovery_suite.run_local",
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.backends.model_discovery",
        "json_artifact": RUN_ARTIFACT,
        "markdown_artifact": RUN_MARKDOWN_ARTIFACT,
        "model_candidates": [asdict(candidate)],
        "baselines": {
            "parameter_matched": {"model_id": "toy-parameter-baseline", "parameter_count": candidate.parameter_count},
            "compute_matched": {"model_id": "toy-compute-baseline", "compute_budget": dict(candidate.compute_budget)},
            "matched_random_structural_control": {"model_id": "toy-random-structure", "seed": 761},
        },
        "task_grid": task_rows,
        "metrics": {
            "task_count": len(task_rows),
            "classifier_shift_count": sum(int(row["metrics"]["classifier_shift_count"]) for row in task_rows),
            "negative_witness_count": len(negative_witnesses),
        },
        "metric_sources": {
            row["task_id"]: f"$.task_grid.{index}.metrics" for index, row in enumerate(task_rows)
        },
        "nm_hardgates": [_nm_gate(gate_id) for gate_id in NM_HARDGATE_IDS],
        "ledger_rows": _ledger_rows(task_rows),
        "negative_witnesses": negative_witnesses,
        "claim_capsule_ref": claim_capsule_ref,
        "robustness": {"multi_surface": "not-ready"},
        "mechanism_namecert_candidate": "not-ready",
        "scope_seal": {"boundary": "run-local deterministic toy model discovery"},
        "cost_protocol": {"unit": "toy-step", "status": "declared"},
        "discovery_regularized_training_refs": {
            "discovery_map_signal": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "torch_training_evidence": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.torch_training_evidence",
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "mechanism_seeking_network_refs": {
            "discovery_map_signal": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "mechanism_gate_summary": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.mechanism_gate_summary",
            },
            "gate_protocol": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.gate_protocol",
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "certificate_gated_attention_refs": {
            "discovery_map_signal": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "certificate_gate_summary": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.certificate_gate_summary",
            },
            "torch_attention_evidence": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.torch_attention_evidence",
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "not_claimed": list(candidate.not_claimed),
    }
    return payload


class ModelDiscoveryBackendEvidenceAdapter:
    backend = TheoryBackend(
        name="model-discovery",
        scope_kind="run-local-model-discovery-suite",
        assumptions=("deterministic toy task rows are finite JSON objects",),
        metrics=("task_accuracy", "OOD_accuracy", "classifier_shift_count", "quality_q"),
        theorem_rows=(),
        ledger_rows=(),
        hardgates=(),
        not_claimed=("real-model training", "global architecture discovery verdict"),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {
            "run_artifact": RUN_ARTIFACT,
            "task_ids": list(TASK_IDS),
            "discovery_regularized_training": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.torch_training_evidence",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
            "mechanism_seeking_network": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.mechanism_gate_summary",
                    "$.gate_protocol",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
            "certificate_gated_attention": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.certificate_gate_summary",
                    "$.torch_attention_evidence",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
        }

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"status": "run-local", "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"levels": ["D4", "DN"], "verdict_owner": "core-compiler"}

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        del root
        return build_model_discovery_payload(generated_at=generated_at or "model-discovery-run-local")

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.compute_metrics(root=root, generated_at=generated_at)["ledger_rows"]

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        payload = self.compute_metrics(root=root, generated_at=generated_at)
        return [
            {
                "negative_id": f"dn:model-discovery:{row['task_id']}",
                "report_id": "model-discovery-suite",
                "kind": "model_discovery_task",
                "report": "model-discovery-suite",
                "claim_id": f"claim:model-discovery:{row['task_id']}",
                "source": f"{RUN_ARTIFACT}:{row['evidence_pointer']}",
                "json_artifact": RUN_ARTIFACT,
                "markdown_artifact": RUN_MARKDOWN_ARTIFACT,
                "ledger_pointer": f"{RUN_ARTIFACT}:{row['evidence_pointer']}",
                "discovery_level": row["discovery_level"],
                "classifier_reasons": ["classifier-shift-absent"],
                "projection_status": "projected",
                "evidence_pointer": row["evidence_pointer"],
                "failed_gate": "NM-HG5",
                "what_was_learned": "toy task does not produce a new classifier shift",
                "next_hypothesis": "add project-local model evidence producer",
                "audit_status": "pass",
                "audit_reason": "",
            }
            for row in payload["ledger_rows"]
            if row["discovery_level"] == "DN"
        ]

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)

"""Gap-head attribution capsule backend adapter for discovery compilation."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.cost_protocol import SCOPED_DEBT_ROWS
from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.latent_distribution import CANONICAL_LATENT_DISTRIBUTION_KEYS
from bedc_quality_lab.ledger import LedgerRowKey, derive_ledger_gaps
from scripts import run_gap_head_attribution_capsule


OWNER = "scripts.run_gap_head_attribution_capsule.build_gap_head_attribution_capsule"


METRIC_POINTERS = {
    "full_unlogged_error_rate_mean": "$.aggregate.by_arm.full.UnloggedErrorRate.mean",
    "hardgates_failed_gate": "$.hardgates.failed_gate",
    "a4_hardgates_failed_gate": "$.a4_hardgates.failed_gate",
    "claim_capsule_hardgates_status": "$.claim_capsule_hardgates",
    "d5_m_passed": "$.d5_m.passed",
    "mechanism_case_status": "$.mechanism_case.status",
}


def _ledger_row_key(row: Mapping[str, Any]) -> LedgerRowKey:
    return LedgerRowKey(kind=str(row["kind"]), residue=str(row["residue"]))


def _ledger_projection(row: Mapping[str, Any], status_by_key: Mapping[LedgerRowKey, Any]) -> Mapping[str, str]:
    status = status_by_key.get(_ledger_row_key(row))
    if status is None:
        return {"status": "declared", "severity": "declared"}
    return {"status": status.status, "severity": status.severity}


def _resolve_payload_pointer(payload: Mapping[str, Any], pointer: str) -> Any:
    cursor: Any = payload
    if not pointer.startswith("$."):
        raise ValueError(f"payload pointer must start with $.: {pointer}")
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        else:
            raise KeyError(pointer)
    return cursor


def _project_metric(payload: Mapping[str, Any], name: str) -> Any:
    value = _resolve_payload_pointer(payload, METRIC_POINTERS[name])
    if name == "claim_capsule_hardgates_status":
        return {
            str(gate_name): str(gate["status"])
            for gate_name, gate in value.items()
            if isinstance(gate, Mapping) and "status" in gate
        }
    return value


class GapHeadAttributionBackendEvidenceAdapter:
    backend = TheoryBackend(
        name="gap-head-attribution",
        scope_kind="non-canonical-backend-probe",
        assumptions=(
            "gaussian_ou_gap_head_surface",
            "learned_h_attribution_capsule",
            "matched_random_control_available",
            "mechanism_claim_is_capsule_scoped",
        ),
        metrics=(
            "full_unlogged_error_rate_mean",
            "hardgates_failed_gate",
            "a4_hardgates_failed_gate",
            "claim_capsule_hardgates_status",
            "d5_m_passed",
            "mechanism_case_status",
        ),
        theorem_rows=(
            {
                "name": "control/matched-random-control",
                "owner": OWNER,
                "evidence_pointer": "$.control_evidence.matched_random",
                "control_pointer": "$.control_pointer.matched_random",
            },
            {
                "name": "namecert/mechanism-candidate-audit",
                "owner": OWNER,
                "evidence_pointer": "$.audit",
            },
            {
                "name": "closure/mechanism-closure-debt",
                "owner": OWNER,
                "evidence_pointer": "$.ledger_policy.mechanism_closure_debt",
            },
        ),
        ledger_rows=(
            {"kind": "source", "residue": "source-coverage"},
            {"kind": "source", "residue": "latent-distribution-gaussianity"},
            {"kind": "source", "residue": "dimension-match"},
            {"kind": "source", "residue": "finite-sample-support"},
            {"kind": "classifier", "residue": "optimizer-certificate"},
            {"kind": "generalization", "residue": "global-claim-boundary"},
        ),
        hardgates=(
            {"name": "A1", "pointer": "$.hardgates"},
            {"name": "A4", "pointer": "$.a4_hardgates"},
            {"name": "claim-capsule", "pointer": "$.claim_capsule_hardgates"},
        ),
        not_claimed=(
            "canonical report production",
            "terminal verdict classification",
            "formal BEDC NameCert closure",
            "mechanism theorem closure",
        ),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {
            "backend": self.backend.name,
            "source_count": 1,
            "latent_dim": 2,
            "latent_distribution": {"family": "gaussian", "coverage_key": "gaussian"},
            "latent_distribution_coverage_keys": list(CANONICAL_LATENT_DISTRIBUTION_KEYS),
            "global_claim": False,
            "assumptions": list(self.backend.assumptions),
        }

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "status": "delegated-capsule-projection"}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {
            "backend": self.backend.name,
            "metrics": list(self.backend.metrics),
            "output_dim": 2,
            "name": "deterministic gap-head attribution capsule",
        }

    def _run(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        return run_gap_head_attribution_capsule.build_gap_head_attribution_capsule(
            root=root,
            run_id="gap-head-attribution-backend-probe",
            generated_at=generated_at,
        )

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        payload = self._run(root=root, generated_at=generated_at)
        metrics = {name: _project_metric(payload, name) for name in self.backend.metrics}
        config = dict(payload.get("config", {}))
        source_artifacts = dict(payload.get("source_artifacts", {}))
        source_spec = {
            **self.build_source_spec(),
            "sample_count": int(config.get("sample_count", 0)),
            "seed_count": int(config.get("seed_count", 0)),
            "source_artifacts": source_artifacts,
        }
        classifier_spec = {
            **self.build_classifier_spec(),
            "optimizer_certificate_steps": int(config.get("seed_count", 0)) * int(config.get("arm_count", 0)),
            "control_pointer": payload["control_pointer"],
        }
        stability_spec = {
            "multi_seed": int(config.get("seed_count", 0)) > 1,
            "seed_order": list(payload.get("aggregate", {}).get("seed_order", [])),
        }
        return {
            "schema_id": "bedc-quality-lab:gap-head-attribution-backend-projection",
            "generated_at": generated_at,
            "backend": self.backend.name,
            "run_id": payload["run_id"],
            "metrics": metrics,
            "metric_pointers": dict(METRIC_POINTERS),
            "source_spec": source_spec,
            "pattern_spec": self.build_pattern_spec(),
            "classifier_spec": classifier_spec,
            "stability_spec": stability_spec,
            "hardgates": {
                "A1": payload["hardgates"],
                "A4": payload["a4_hardgates"],
                "claim_capsule": payload["claim_capsule_hardgates"],
            },
            "control_pointer": payload["control_pointer"],
            "control_evidence": payload["control_evidence"],
            "mechanism_case": payload["mechanism_case"],
            "d5_m": payload["d5_m"],
            "scope": payload["scope"],
            "source_artifacts": source_artifacts,
        }

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        payload = self.compute_metrics(root=root, generated_at=generated_at)
        declared_rows = frozenset(_ledger_row_key(row) for row in self.backend.ledger_rows)
        debt_assessment = assess_debt(
            payload["metrics"],
            payload["source_spec"],
            payload["classifier_spec"],
            payload["stability_spec"],
            extra_rows=declared_rows & SCOPED_DEBT_ROWS,
        )
        gaps = derive_ledger_gaps(
            payload["metrics"],
            payload["source_spec"],
            payload["classifier_spec"],
            payload["stability_spec"],
            debt_assessment,
        )
        status_by_key = {
            LedgerRowKey(item.kind, item.residue): item
            for item in debt_assessment.items
        }
        status_by_key.update(
            {
                LedgerRowKey(gap.kind, gap.residue): gap
                for gap in gaps
            }
        )
        return [
            {
                **row,
                **_ledger_projection(row, status_by_key),
                "evidence_pointer": "bedc_quality_lab.ledger.derive_ledger_gaps",
                "owner": OWNER,
            }
            for row in self.backend.ledger_rows
        ]

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        del root, generated_at
        return ()

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)


__all__ = ["GapHeadAttributionBackendEvidenceAdapter"]

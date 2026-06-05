"""LeJEPA backend adapter for discovery compilation."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.cost_protocol import SCOPED_DEBT_ROWS
from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.ledger import LedgerRowKey, derive_ledger_gaps
from scripts import run_gaussian_ou_lejepa


def _ledger_row_key(row: Mapping[str, Any]) -> LedgerRowKey:
    return LedgerRowKey(kind=str(row["kind"]), residue=str(row["residue"]))


def _ledger_projection(row: Mapping[str, Any], status_by_key: Mapping[LedgerRowKey, Any]) -> Mapping[str, str]:
    status = status_by_key.get(_ledger_row_key(row))
    if status is None:
        return {"status": "declared", "severity": "declared"}
    return {"status": status.status, "severity": status.severity}


class LeJEPABackendEvidenceAdapter:
    backend = TheoryBackend(
        name="lejepa",
        scope_kind="non-canonical-backend-probe",
        assumptions=(
            "gaussian_latent",
            "ou_transition",
            "dimension_match_m_equals_n",
            "population_optimum_or_empirical_proxy",
        ),
        metrics=(
            "alignment_gap_delta_mse",
            "whitening_deviation_epsilon",
            "theorem3_bound_mse",
            "actual_recovery_mse",
            "linear_identifiability_r2",
        ),
        theorem_rows=({
            "name": "theorem3-bound-certificate",
            "owner": "scripts.run_gaussian_ou_lejepa.run_experiment",
            "pointer": "$.classifier_spec.cert_status",
        },),
        ledger_rows=(
            {"kind": "source", "residue": "latent-distribution-gaussianity"},
            {"kind": "source", "residue": "transition-isotropy"},
            {"kind": "source", "residue": "dimension-match"},
            {"kind": "source", "residue": "finite-sample-support"},
            {"kind": "classifier", "residue": "optimizer-certificate"},
        ),
        hardgates=(),
        not_claimed=("canonical report production", "terminal verdict classification"),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "assumptions": list(self.backend.assumptions)}

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "status": "delegated-envelope-projection"}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "metrics": list(self.backend.metrics)}

    def _run(self, *, root: Path) -> Any:
        del root
        return run_gaussian_ou_lejepa.run_experiment(
            run_id="lejepa-backend-probe",
            envelope_artifact="reports/backend-probes/lejepa/evidence-envelope.json",
            report_artifact="reports/backend-probes/lejepa/quality-report.md",
        )

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        envelope = self._run(root=root)
        return {
            "schema_id": "bedc-quality-lab:lejepa-backend-projection",
            "generated_at": generated_at,
            "backend": self.backend.name,
            "run_id": envelope.run_id,
            "metrics": {name: envelope.metrics[name] for name in self.backend.metrics if name in envelope.metrics},
            "source_spec": dict(envelope.source_spec),
            "pattern_spec": dict(envelope.pattern_spec),
            "classifier_spec": dict(envelope.classifier_spec),
            "stability_spec": dict(envelope.stability_spec),
            "ledger_gaps": list(envelope.ledger_gaps),
            "debt_items": list(envelope.debt_items),
            "artifacts": dict(envelope.artifacts),
            "bedc_refs": list(envelope.bedc_refs),
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
                "owner": "scripts.run_gaussian_ou_lejepa.run_experiment",
            }
            for row in self.backend.ledger_rows
        ]

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        del root, generated_at
        return ()

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)


__all__ = ["LeJEPABackendEvidenceAdapter"]

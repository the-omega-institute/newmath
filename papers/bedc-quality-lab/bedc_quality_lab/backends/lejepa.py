"""LeJEPA backend adapter for discovery compilation."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from scripts import run_gaussian_ou_lejepa


def _parse_ledger_gap(row: str) -> dict[str, str]:
    cells = {}
    for item in row.split(";"):
        key, _, value = item.strip().partition("=")
        if key and value:
            cells[key] = value
    return cells


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
        gap_by_key = {}
        for gap in payload["ledger_gaps"]:
            parsed = _parse_ledger_gap(gap)
            gap_by_key[f"{parsed.get('kind')}/{parsed.get('residue')}"] = parsed
        return [
            {
                **row,
                "status": gap_by_key.get(f"{row['kind']}/{row['residue']}", {}).get("status", "declared"),
                "severity": gap_by_key.get(f"{row['kind']}/{row['residue']}", {}).get("severity", "declared"),
                "evidence_pointer": "$.ledger_gaps",
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

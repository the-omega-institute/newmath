"""SIGReg backend adapter for discovery compilation."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.cost_protocol import SCOPED_DEBT_ROWS
from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.ledger import LedgerRowKey, derive_ledger_gaps
from scripts import run_sigreg_training_proxy


_METRIC_PROJECTIONS = (
    ("covariance_proxy_current_alignment_mean", "covariance_proxy_current", "alignment_mean"),
    ("covariance_proxy_current_sigreg_sliced_cf_mean", "covariance_proxy_current", "sigreg_sliced_cf_mean"),
    ("covariance_proxy_current_loss_mean", "covariance_proxy_current", "loss_mean"),
    ("true_sigreg_sliced_cf_alignment_mean", "true_sigreg_sliced_cf", "alignment_mean"),
    ("true_sigreg_sliced_cf_sigreg_sliced_cf_mean", "true_sigreg_sliced_cf", "sigreg_sliced_cf_mean"),
    ("true_sigreg_sliced_cf_loss_mean", "true_sigreg_sliced_cf", "loss_mean"),
    ("vicreg_like_covariance_alignment_mean", "vicreg_like_covariance", "alignment_mean"),
    ("vicreg_like_covariance_sigreg_sliced_cf_mean", "vicreg_like_covariance", "sigreg_sliced_cf_mean"),
    ("vicreg_like_covariance_loss_mean", "vicreg_like_covariance", "loss_mean"),
    ("alignment_only_alignment_mean", "alignment_only", "alignment_mean"),
    ("alignment_only_sigreg_sliced_cf_mean", "alignment_only", "sigreg_sliced_cf_mean"),
    ("alignment_only_loss_mean", "alignment_only", "loss_mean"),
)


def _ledger_row_key(row: Mapping[str, Any]) -> LedgerRowKey:
    return LedgerRowKey(kind=str(row["kind"]), residue=str(row["residue"]))


def _ledger_projection(row: Mapping[str, Any], status_by_key: Mapping[LedgerRowKey, Any]) -> Mapping[str, str]:
    status = status_by_key.get(_ledger_row_key(row))
    if status is None:
        return {"status": "declared", "severity": "declared"}
    return {"status": status.status, "severity": status.severity}


def _project_metrics(payload: Mapping[str, Any]) -> dict[str, float]:
    arm_summaries = payload["arm_summaries"]
    return {
        metric_name: float(arm_summaries[arm][field])
        for metric_name, arm, field in _METRIC_PROJECTIONS
    }


def _source_spec(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    config = payload["config"]
    return {
        "name": "sigreg-training-proxy",
        "source_count": 1,
        "latent_distribution": "gaussian",
        "latent_dim": 2,
        "sample_count": int(config["sample_count"]),
        "transition_kernel": {"name": "gaussian-ou", "isotropic": True, "rho": float(config["rho"])},
        "transition_isotropic": True,
        "global_claim": False,
    }


def _pattern_spec(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    return {
        "backend": "sigreg",
        "status": "delegated-arm-summary-projection",
        "arm_protocol": dict(payload["arm_protocol"]),
    }


def _classifier_spec(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    config = payload["config"]
    return {
        "name": "sigreg-sliced-cf-training-proxy",
        "training": "finite-step optimizer proxy",
        "output_dim": 2,
        "optimizer_certificate_steps": int(config["steps"]),
        "lambda_sigreg": float(config["lambda_sigreg"]),
        "arms": list(config["arms"]),
    }


def _stability_spec(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    seeds = tuple(int(seed) for seed in payload["config"]["seeds"])
    return {
        "name": "sigreg-training-proxy-seeds",
        "seed_count": len(seeds),
        "seeds": list(seeds),
        "multi_seed": len(seeds) > 1,
    }


class SIGRegBackendEvidenceAdapter:
    backend = TheoryBackend(
        name="sigreg",
        scope_kind="non-canonical-backend-probe",
        assumptions=(
            "gaussian_latent",
            "ou_transition",
            "dimension_match_m_equals_n",
            "finite_sample_training_proxy",
            "non_canonical_backend_probe",
        ),
        metrics=tuple(metric_name for metric_name, _, _ in _METRIC_PROJECTIONS),
        theorem_rows=(),
        ledger_rows=(
            {"kind": "source", "residue": "latent-distribution-gaussianity"},
            {"kind": "source", "residue": "transition-isotropy"},
            {"kind": "source", "residue": "dimension-match"},
            {"kind": "source", "residue": "finite-sample-support"},
            {"kind": "classifier", "residue": "optimizer-certificate"},
            {"kind": "generalization", "residue": "global-claim-boundary"},
        ),
        hardgates=(),
        not_claimed=("canonical report production", "terminal verdict classification"),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "assumptions": list(self.backend.assumptions)}

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "status": "delegated-arm-summary-projection"}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"backend": self.backend.name, "metrics": list(self.backend.metrics)}

    def _run(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        del root
        return run_sigreg_training_proxy.build_payload(
            run_id="sigreg-backend-probe",
            generated_at=generated_at,
            json_artifact="reports/backend-probes/sigreg/evidence-envelope.json",
            report_artifact="reports/backend-probes/sigreg/quality-report.md",
        )

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        payload = self._run(root=root, generated_at=generated_at)
        metrics = _project_metrics(payload)
        return {
            "schema_id": "bedc-quality-lab:sigreg-backend-projection",
            "generated_at": generated_at,
            "backend": self.backend.name,
            "run_id": payload["run_id"],
            "metrics": metrics,
            "metric_sources": {
                metric_name: f"$.arm_summaries.{arm}.{field}"
                for metric_name, arm, field in _METRIC_PROJECTIONS
            },
            "source_spec": dict(_source_spec(payload)),
            "pattern_spec": dict(_pattern_spec(payload)),
            "classifier_spec": dict(_classifier_spec(payload)),
            "stability_spec": dict(_stability_spec(payload)),
            "source_artifacts": dict(payload["source_artifacts"]),
            "not_claimed": list(self.backend.not_claimed),
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
                "owner": "scripts.run_sigreg_training_proxy.build_payload",
            }
            for row in self.backend.ledger_rows
        ]

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        del root, generated_at
        return ()

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)


__all__ = ["SIGRegBackendEvidenceAdapter"]

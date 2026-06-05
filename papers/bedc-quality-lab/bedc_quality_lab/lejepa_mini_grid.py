"""Run-local projection for the LeJEPA mini-grid evidence producer."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID


SCHEMA_ID = "bedc-quality-lab:lejepa-mini-grid"
ARTIFACT_ID = "bedc-quality-lab:lejepa-mini-grid"
PRODUCER = "scripts/run_lejepa_mini_grid.py"
PROJECTOR = "bedc_quality_lab.lejepa_mini_grid.LeJEPAMiniGridProjection"
DEFAULT_ALIGNMENT_LAMBDAS = (1.0e-5, 1.0e-4, 1.0e-3, 5.0e-3, 1.0e-2)
DEFAULT_RHOS = (0.5, 0.7, 0.9, 0.95)
DEFAULT_MIXINGS = ("spiral", "parabolic", "realnvp")
DEFAULT_SEEDS = (11, 23, 37, 53, 71)
METRIC_KEYS = (
    "alignment_loss",
    "sigreg_sliced_cf",
    "linear_identifiability_r2",
    "actual_recovery_mse",
    "theorem3_bound_mse",
    "collapse_rate",
    "quality_q",
)
NOT_CLAIMED = (
    "full LeJEPA reproduction",
    "global model quality",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M gate passes",
    "broad non-Gaussian mixing generalization",
)
POSITIVE_CLAIM = {
    "text": "D2 LeJEPA mini-grid evidence supports a lab-local lambda and rho trend under Gaussian-OU toy conditions.",
    "scope": "run-local LeJEPA mini-grid projection",
}
PROJECTOR_FORBIDDEN_TERMS = (*FORBIDDEN_POSITIVE_CLAIM_TERMS, "mechanism-closure-unless-D5-M")


def default_grid() -> tuple[dict[str, Any], ...]:
    return tuple(
        {
            "alignment_lambda": float(alignment_lambda),
            "rho": float(rho),
            "mixing": str(mixing),
            "seed": int(seed),
        }
        for alignment_lambda in DEFAULT_ALIGNMENT_LAMBDAS
        for rho in DEFAULT_RHOS
        for mixing in DEFAULT_MIXINGS
        for seed in DEFAULT_SEEDS
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
    return float(statistics.fmean(finite))


def _metric(row: Mapping[str, Any], key: str) -> float | None:
    if key in row:
        return _finite_float(row.get(key))
    metrics = row.get("metrics")
    if isinstance(metrics, Mapping):
        value = metrics.get(key)
        if isinstance(value, Mapping) and "mean" in value:
            return _finite_float(value.get("mean"))
        return _finite_float(value)
    evaluation = row.get("evaluation")
    if isinstance(evaluation, Mapping):
        if key == "alignment_loss":
            return _finite_float(evaluation.get("alignment"))
        return _finite_float(evaluation.get(key))
    return None


def _group_mean(rows: Sequence[Mapping[str, Any]], group_key: str, metric_key: str) -> dict[Any, float]:
    grouped: dict[Any, list[float]] = {}
    for row in rows:
        value = _metric(row, metric_key)
        if value is None:
            continue
        grouped.setdefault(row.get(group_key), []).append(value)
    result: dict[Any, float] = {}
    for key, values in grouped.items():
        mean_value = _mean(values)
        if mean_value is not None:
            result[key] = mean_value
    return result


def _strictly_ordered(values: Sequence[float], *, increasing: bool, tolerance: float = 1.0e-12) -> bool:
    if len(values) < 2:
        return False
    if any(value is None or not math.isfinite(float(value)) for value in values):
        return False
    pairs = zip(values, values[1:])
    if increasing:
        return all(right > left + tolerance for left, right in pairs)
    return all(right < left - tolerance for left, right in pairs)


def _forbidden_term_audit(value: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower().replace(" ", "-")
    hits = [term for term in PROJECTOR_FORBIDDEN_TERMS if term.lower() in text]
    return {
        "status": _status(not hits),
        "forbidden_positive_claim_terms": list(PROJECTOR_FORBIDDEN_TERMS),
        "hits": hits,
    }


def _revocation_rows(failed_gate: str | None) -> list[dict[str, Any]]:
    return [
        {
            "condition": "revoke if the mini-grid records are not reproducible from the run artifact raw rows",
            "status": "armed",
            "active": failed_gate is None,
        },
        {
            "condition": "revoke if SIGReg sliced-CF and covariance proxy reporting are collapsed into one metric",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke any D2 reading when the lambda or rho trend hardgate fails",
            "status": "armed",
            "active": True,
        },
    ]


@dataclass(frozen=True)
class LeJEPAMiniGridProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        d2_hardgates = self.d2_hardgate_verdicts(summaries)
        u_hardgates = self.u_hardgate_verdicts(summaries, d2_hardgates)
        hardgates = {**d2_hardgates, **u_hardgates}
        failed_gate = self.failed_gate(hardgates)
        positive_claim = {
            **POSITIVE_CLAIM,
            "level": "D2" if failed_gate is None else "DN",
        }
        capsule = self.claim_capsule_payload(hardgates=hardgates, summaries=summaries, positive_claim=positive_claim)
        if capsule["forbidden_claim_term_audit"]["status"] != "pass":
            failed_gate = failed_gate or "forbidden-positive-claim-term"
            hardgates["U-HG8"]["status"] = "fail"
            capsule["claim_status"] = "failed"
            capsule["failed_gate"] = failed_gate
            capsule["positive_claim"]["level"] = "DN"
        result_status = "d2-theory-consistent" if failed_gate is None and capsule["claim_status"] == "d2-pointer-accepted" else "negative"
        summary = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "run_id": str(self.config.get("run_id", "lejepa-mini-grid")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "config": dict(self.config),
            "grid": summaries["grid"],
            "metric_keys": list(METRIC_KEYS),
            "lambda_summary": summaries["lambda_summary"],
            "rho_summary": summaries["rho_summary"],
            "mixing_summary": summaries["mixing_summary"],
            "best_cell": summaries["best_cell"],
            "sigreg_covariance_proxy": summaries["sigreg_covariance_proxy"],
            "tradeoff_ledger": summaries["tradeoff_ledger"],
            "d2_hardgates": d2_hardgates,
            "u_hardgates": u_hardgates,
            "hardgate": {
                "status": _status(failed_gate is None and capsule["claim_status"] == "d2-pointer-accepted"),
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            "claim_capsule": capsule,
            "not_claimed": self.not_claimed(),
            "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
            "what_was_learned": capsule["what_was_learned"],
            "revocation_rows": _revocation_rows(failed_gate),
            "result": {
                "status": result_status,
                "terminal_verdict": "d2-pointer-accepted" if result_status == "d2-theory-consistent" else "rejected",
                "discovery_level": "D2" if result_status == "d2-theory-consistent" else "DN",
                "claim_capsule_status": capsule["claim_status"],
            },
        }
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def not_claimed(self) -> list[str]:
        return list(NOT_CLAIMED)

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name, row in hardgates.items():
            if row.get("status") != "pass":
                return name
        return None

    def d2_hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        grid = summaries["grid"]
        expected_cells = int(grid["expected_record_count"])
        actual_cells = int(grid["record_count"])
        lambda_values = summaries["lambda_summary"]["ordered_alignment_lambdas"]
        quality_by_lambda = [summaries["lambda_summary"]["by_alignment_lambda"][str(value)]["quality_q_mean"] for value in lambda_values]
        collapse_by_lambda = [summaries["lambda_summary"]["by_alignment_lambda"][str(value)]["collapse_rate_mean"] for value in lambda_values]
        rho_values = summaries["rho_summary"]["ordered_rhos"]
        r2_by_rho = [summaries["rho_summary"]["by_rho"][str(value)]["linear_identifiability_r2_mean"] for value in rho_values]
        best = summaries["best_cell"]
        high_rho = max(rho_values) if rho_values else None
        low_lambda_half = set(lambda_values[: max(1, len(lambda_values) // 2)])
        lambda_trend = _strictly_ordered(quality_by_lambda, increasing=False) and _strictly_ordered(collapse_by_lambda, increasing=True)
        rho_trend = _strictly_ordered(r2_by_rho, increasing=True)
        best_consistent = (
            high_rho is not None
            and best is not None
            and float(best["rho"]) == float(high_rho)
            and float(best["alignment_lambda"]) in low_lambda_half
        )
        return {
            "D2-HG1": {
                "status": _status(actual_cells == expected_cells and expected_cells == 300),
                "evidence": "default grid has exactly 300 predeclared cells",
                "record_count": actual_cells,
                "expected_record_count": expected_cells,
            },
            "D2-HG2": {
                "status": _status(lambda_trend and rho_trend and best_consistent),
                "evidence": "rho and lambda trends are read from observed metrics, not metadata-only variation",
                "lambda_quality_q_decreasing": _strictly_ordered(quality_by_lambda, increasing=False),
                "lambda_collapse_rate_increasing": _strictly_ordered(collapse_by_lambda, increasing=True),
                "rho_linear_identifiability_r2_increasing": rho_trend,
                "best_cell_low_lambda_high_rho": bool(best_consistent),
            },
            "D2-HG3": {
                "status": _status(bool(summaries["tradeoff_ledger"]["recorded"])),
                "evidence": "SIGReg Gaussianity and alignment tradeoff are ledgered separately",
                "tradeoff": summaries["tradeoff_ledger"],
            },
        }

    def u_hardgate_verdicts(
        self,
        summaries: Mapping[str, Any],
        d2_hardgates: Mapping[str, Mapping[str, Any]],
    ) -> dict[str, dict[str, Any]]:
        full_lejepa_claim = bool(self.config.get("full_lejepa_claim", False))
        positive_claim = {**POSITIVE_CLAIM, "level": "D2" if all(row["status"] == "pass" for row in d2_hardgates.values()) else "DN"}
        claim_audit = _forbidden_term_audit(positive_claim)
        non_gaussian_downgraded = summaries["mixing_summary"]["non_gaussian_broad_claim"] == "downgraded"
        return {
            "U-HG1": {
                "status": _status(bool(summaries["sigreg_covariance_proxy"]["separate_reported"])),
                "evidence": "SIGReg sliced-CF and covariance proxy have separate fields",
            },
            "U-HG2": {
                "status": _status(not full_lejepa_claim),
                "full_lejepa_claim": full_lejepa_claim,
                "required_boundary": "full LeJEPA reproduction remains not_claimed",
            },
            "U-HG3": {
                "status": _status(non_gaussian_downgraded),
                "non_gaussian_broad_claim": summaries["mixing_summary"]["non_gaussian_broad_claim"],
            },
            "U-HG4": {
                "status": _status(bool(self.not_claimed())),
                "not_claimed": self.not_claimed(),
            },
            "U-HG5": {
                "status": _status("summary" in self.run_artifacts and "claim_capsule" in self.run_artifacts),
                "run_artifacts": dict(self.run_artifacts),
            },
            "U-HG6": {
                "status": _status(bool(summaries["learning_fields"]["what_was_learned"])),
                "learning_fields": summaries["learning_fields"],
            },
            "U-HG7": {
                "status": _status(bool(_revocation_rows(None))),
                "revocation_rows": _revocation_rows(None),
            },
            "U-HG8": {
                "status": claim_audit["status"],
                "evidence": "positive claim text avoids forbidden full-scope terms",
                "forbidden_positive_claim_terms": claim_audit["forbidden_positive_claim_terms"],
                "hits": claim_audit["hits"],
            },
        }

    def claim_capsule_payload(
        self,
        *,
        hardgates: Mapping[str, Mapping[str, Any]],
        summaries: Mapping[str, Any],
        positive_claim: Mapping[str, Any],
    ) -> dict[str, Any]:
        failed = self.failed_gate(hardgates)
        accepted = failed is None
        capsule = {
            "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
            "run_id": str(self.config.get("run_id", "lejepa-mini-grid")),
            "generated_at": self.generated_at,
            "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
            "producer": PROJECTOR,
            "claim_status": "d2-pointer-accepted" if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_metrics": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": "configs/default_cost_protocol.yaml",
            },
            "not_claimed": self.not_claimed(),
            "failed_gate": failed,
            "what_was_learned": summaries["learning_fields"]["what_was_learned"] if accepted else summaries["learning_fields"]["negative_learning"],
            "hardgates": dict(hardgates),
            "result_snapshot": {
                "best_cell": summaries["best_cell"],
                "lambda_summary": summaries["lambda_summary"],
                "rho_summary": summaries["rho_summary"],
                "mixing_summary": summaries["mixing_summary"],
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
            "# LeJEPA Mini-Grid",
            "",
            f"- run_id: `{payload['run_id']}`",
            f"- schema_id: `{payload['schema_id']}`",
            f"- result: `{payload['result']['status']}`",
            f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
            "",
            "## Hardgates",
            "",
        ]
        for gate, row in payload["d2_hardgates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        for gate, row in payload["u_hardgates"].items():
            lines.append(f"- `{gate}`: `{row['status']}`")
        lines.extend(["", "## Best Cell", ""])
        best = payload["best_cell"]
        if best is None:
            lines.append("- none")
        else:
            lines.append(
                "- "
                f"lambda `{best['alignment_lambda']}`, rho `{best['rho']}`, mixing `{best['mixing']}`, "
                f"quality_q `{best['quality_q']:.8f}`"
            )
        lines.extend(["", "## Not Claimed", ""])
        lines.extend(f"- {item}" for item in payload["not_claimed"])
        lines.append("")
        return "\n".join(lines)

    def _summaries(self) -> dict[str, Any]:
        config = dict(self.config)
        alignment_lambdas = [float(value) for value in config.get("alignment_lambdas", DEFAULT_ALIGNMENT_LAMBDAS)]
        rhos = [float(value) for value in config.get("rhos", DEFAULT_RHOS)]
        mixings = [str(value) for value in config.get("mixings", DEFAULT_MIXINGS)]
        seeds = [int(value) for value in config.get("seeds", DEFAULT_SEEDS)]
        expected = len(alignment_lambdas) * len(rhos) * len(mixings) * len(seeds)
        best = self._best_cell()
        by_lambda = self._lambda_summary(alignment_lambdas)
        by_rho = self._rho_summary(rhos)
        by_mixing = self._mixing_summary(mixings)
        sigreg_values = [value for value in (_metric(row, "sigreg_sliced_cf") for row in self.records) if value is not None]
        cov_values = [value for value in (_metric(row, "covariance_proxy") for row in self.records) if value is not None]
        alignment_values = [value for value in (_metric(row, "alignment_loss") for row in self.records) if value is not None]
        low_lambda = min(alignment_lambdas) if alignment_lambdas else None
        high_lambda = max(alignment_lambdas) if alignment_lambdas else None
        low_rows = [row for row in self.records if low_lambda is not None and float(row.get("alignment_lambda", math.nan)) == low_lambda]
        high_rows = [row for row in self.records if high_lambda is not None and float(row.get("alignment_lambda", math.nan)) == high_lambda]
        low_sigreg = _mean(value for value in (_metric(row, "sigreg_sliced_cf") for row in low_rows) if value is not None)
        high_sigreg = _mean(value for value in (_metric(row, "sigreg_sliced_cf") for row in high_rows) if value is not None)
        low_alignment = _mean(value for value in (_metric(row, "alignment_loss") for row in low_rows) if value is not None)
        high_alignment = _mean(value for value in (_metric(row, "alignment_loss") for row in high_rows) if value is not None)
        improves_gaussianity = low_sigreg is not None and high_sigreg is not None and high_sigreg < low_sigreg
        hurts_alignment = low_alignment is not None and high_alignment is not None and high_alignment > low_alignment
        return {
            "grid": {
                "record_count": len(self.records),
                "expected_record_count": expected,
                "alignment_lambda_count": len(alignment_lambdas),
                "rho_count": len(rhos),
                "mixing_count": len(mixings),
                "seed_count": len(seeds),
            },
            "lambda_summary": {
                "ordered_alignment_lambdas": alignment_lambdas,
                "by_alignment_lambda": by_lambda,
            },
            "rho_summary": {
                "ordered_rhos": rhos,
                "by_rho": by_rho,
            },
            "mixing_summary": {
                "mixings": mixings,
                "by_mixing": by_mixing,
                "non_gaussian_broad_claim": "downgraded" if any(mixing != "spiral" for mixing in mixings) else "not_applicable",
            },
            "best_cell": best,
            "sigreg_covariance_proxy": {
                "separate_reported": bool(sigreg_values and cov_values),
                "sigreg_sliced_cf_mean": _mean(sigreg_values),
                "covariance_proxy_mean": _mean(cov_values),
            },
            "tradeoff_ledger": {
                "recorded": bool(sigreg_values and alignment_values),
                "sigreg_gaussianity_improves_with_lambda": improves_gaussianity,
                "alignment_hurt_with_lambda": hurts_alignment,
                "low_lambda_sigreg_sliced_cf_mean": low_sigreg,
                "high_lambda_sigreg_sliced_cf_mean": high_sigreg,
                "low_lambda_alignment_loss_mean": low_alignment,
                "high_lambda_alignment_loss_mean": high_alignment,
            },
            "learning_fields": {
                "what_was_learned": "The mini-grid supports a lab-local lambda/rho trend while keeping full LeJEPA reproduction outside scope.",
                "negative_learning": "The mini-grid recorded a failed gate without promoting a positive claim.",
            },
        }

    def _best_cell(self) -> dict[str, Any] | None:
        best_row: Mapping[str, Any] | None = None
        best_quality: float | None = None
        for row in self.records:
            quality = _metric(row, "quality_q")
            if quality is None:
                continue
            if best_quality is None or quality > best_quality:
                best_quality = quality
                best_row = row
        if best_row is None or best_quality is None:
            return None
        return {
            "alignment_lambda": float(best_row["alignment_lambda"]),
            "rho": float(best_row["rho"]),
            "mixing": str(best_row["mixing"]),
            "seed": int(best_row["seed"]),
            "quality_q": float(best_quality),
            "linear_identifiability_r2": float(_metric(best_row, "linear_identifiability_r2") or 0.0),
            "collapse_rate": float(_metric(best_row, "collapse_rate") or 0.0),
        }

    def _lambda_summary(self, alignment_lambdas: Sequence[float]) -> dict[str, dict[str, float | None]]:
        quality = _group_mean(self.records, "alignment_lambda", "quality_q")
        collapse = _group_mean(self.records, "alignment_lambda", "collapse_rate")
        sigreg = _group_mean(self.records, "alignment_lambda", "sigreg_sliced_cf")
        alignment = _group_mean(self.records, "alignment_lambda", "alignment_loss")
        return {
            str(float(value)): {
                "quality_q_mean": quality.get(float(value)),
                "collapse_rate_mean": collapse.get(float(value)),
                "sigreg_sliced_cf_mean": sigreg.get(float(value)),
                "alignment_loss_mean": alignment.get(float(value)),
            }
            for value in alignment_lambdas
        }

    def _rho_summary(self, rhos: Sequence[float]) -> dict[str, dict[str, float | None]]:
        r2 = _group_mean(self.records, "rho", "linear_identifiability_r2")
        quality = _group_mean(self.records, "rho", "quality_q")
        return {
            str(float(value)): {
                "linear_identifiability_r2_mean": r2.get(float(value)),
                "quality_q_mean": quality.get(float(value)),
            }
            for value in rhos
        }

    def _mixing_summary(self, mixings: Sequence[str]) -> dict[str, dict[str, float | None]]:
        quality = _group_mean(self.records, "mixing", "quality_q")
        collapse = _group_mean(self.records, "mixing", "collapse_rate")
        return {
            str(value): {
                "quality_q_mean": quality.get(str(value)),
                "collapse_rate_mean": collapse.get(str(value)),
            }
            for value in mixings
        }


__all__ = [
    "ARTIFACT_ID",
    "DEFAULT_ALIGNMENT_LAMBDAS",
    "DEFAULT_MIXINGS",
    "DEFAULT_RHOS",
    "DEFAULT_SEEDS",
    "LeJEPAMiniGridProjection",
    "METRIC_KEYS",
    "NOT_CLAIMED",
    "SCHEMA_ID",
    "default_grid",
]

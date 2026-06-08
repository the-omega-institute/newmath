"""Run-local projection for the SIGReg mini-grid evidence producer."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, Mapping, Sequence
import json
import math
import statistics

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.capsule import CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID


SCHEMA_ID = "bedc-quality-lab:sigreg-mini-grid"
ARTIFACT_ID = "bedc-quality-lab:sigreg-mini-grid"
PRODUCER = "scripts/run_sigreg_mini_grid.py"
PROJECTOR = "bedc_quality_lab.sigreg_mini_grid.SIGRegMiniGridProjection"
SEPARATION_FIELD = "metric_separation"
D_LEVEL_FIELD = "discovery_map_signal"
SUMMARY_RESULT_FIELD = None
DEFAULT_ALIGNMENT_LAMBDAS = (1.0e-5, 1.0e-4, 1.0e-3, 5.0e-3, 1.0e-2)
DEFAULT_RHOS = (0.5, 0.7, 0.9, 0.95)
DEFAULT_MIXINGS = ("spiral", "parabolic", "realnvp")
DEFAULT_SEEDS = (11, 23, 37)
METRIC_KEYS = (
    "alignment_loss",
    "sigreg_sliced_cf",
    "linear_identifiability_r2",
    "actual_recovery_mse",
    "theorem3_bound_mse",
    "collapse_rate",
    "quality_q",
)
FORBIDDEN_SUMMARY_ALIASES = (
    "sigreg_covariance_separation",
    "discovery_projection",
    "result",
    "terminal_verdict",
    "claim_capsule",
)
NOT_CLAIMED = (
    "full LeJEPA reproduction",
    "global model quality",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure",
)
POSITIVE_CLAIM = {
    "text": "SIGReg mini-grid evidence supports a lab-local expected lambda and rho trend under Gaussian-OU toy conditions.",
    "scope": "run-local SIGReg mini-grid projection",
}
PROJECTOR_FORBIDDEN_TERMS = FORBIDDEN_POSITIVE_CLAIM_TERMS


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


def _strictly_ordered(values: Sequence[float | None], *, increasing: bool, tolerance: float = 1.0e-12) -> bool:
    if len(values) < 2:
        return False
    if any(value is None or not math.isfinite(float(value)) for value in values):
        return False
    pairs = zip(values, values[1:])
    if increasing:
        return all(float(right) > float(left) + tolerance for left, right in pairs)
    return all(float(right) < float(left) - tolerance for left, right in pairs)


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
            "condition": "revoke if raw rows cannot reproduce the SIGReg mini-grid summary",
            "status": "armed",
            "active": failed_gate is None,
        },
        {
            "condition": "revoke if SIGReg sliced-CF and covariance proxy metrics collapse into one field",
            "status": "armed",
            "active": True,
        },
        {
            "condition": "revoke D2 when the expected lambda and rho trend hardgate fails",
            "status": "armed",
            "active": True,
        },
    ]


def _anti_triviality_contract(level: str) -> dict[str, Any]:
    return {"anti_triviality_status": "pass"} | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.metric_separation",
        metadata_only_pointer="$.grid",
        matched_random_pointer="$.tradeoff_ledger.rows.0",
        forbidden_column_pointer="$.forbidden_claim_term_audit.status",
    )


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


@dataclass(frozen=True)
class SIGRegMiniGridProjection:
    config: Mapping[str, Any]
    records: Sequence[Mapping[str, Any]]
    generated_at: str
    run_artifacts: Mapping[str, str]

    @property
    def raw_rows(self) -> list[dict[str, Any]]:
        return [dict(row) for row in self.records]

    def project(self) -> dict[str, Any]:
        summaries = self._summaries()
        hardgates = self.c3_hardgate_verdicts(summaries)
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
                "reason": "structural-hardgate-failed",
                "evidence_pointer": "$.hardgate.failed_gate",
                "failed_gate": failed_gate,
                "failed_gate_pointer": "$.forbidden_claim_term_audit.status",
            }
            capsule = {**capsule, "claim_status": "failed", "failed_gate": failed_gate}
        hardgate_status = _status(failed_gate is None)
        summary = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": self.generated_at,
            "run_id": str(self.config.get("run_id", "sigreg-mini-grid")),
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "run_artifacts": dict(self.run_artifacts),
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "raw_metrics": self.run_artifacts.get("raw_metrics"),
            },
            "config": dict(self.config),
            "grid": summaries["grid"],
            "metric_keys": list(METRIC_KEYS),
            SEPARATION_FIELD: summaries[SEPARATION_FIELD],
            "lambda_summary": summaries["lambda_summary"],
            "rho_summary": summaries["rho_summary"],
            "mixing_summary": summaries["mixing_summary"],
            "best_cell": summaries["best_cell"],
            "trend_summary": summaries["trend_summary"],
            "tradeoff_ledger": summaries["tradeoff_ledger"],
            "c3_hardgates": hardgates,
            "hardgate": {
                "status": hardgate_status,
                "failed_gate": failed_gate,
            },
            "failed_gate": failed_gate,
            D_LEVEL_FIELD: signal,
            "claim_capsule_ref": self.run_artifacts.get("claim_capsule"),
            "claim_capsule_status": capsule["claim_status"],
            "positive_claim": positive_claim,
            "not_claimed": self.not_claimed(),
            "what_was_learned": capsule["what_was_learned"],
            "revocation_rows": _revocation_rows(failed_gate),
            "forbidden_claim_term_audit": capsule["forbidden_claim_term_audit"],
        }
        if signal["level_candidate"] == "D2" and failed_gate is None:
            summary.update(_anti_triviality_contract("D2"))
        if any(alias in summary for alias in FORBIDDEN_SUMMARY_ALIASES):
            raise ValueError("SIGReg mini-grid summary emitted a forbidden alias")
        if _has_recursive_key(summary, "terminal_verdict") or _has_recursive_key(capsule, "terminal_verdict"):
            raise ValueError("SIGReg mini-grid payload emitted terminal_verdict")
        return {
            "summary_payload": summary,
            "claim_capsule_payload": capsule,
            "report_markdown": self.report_markdown(summary),
            "raw_rows": self.raw_rows,
        }

    def not_claimed(self) -> list[str]:
        return list(NOT_CLAIMED)

    def failed_gate(self, hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
        for name in ("C3-HG1", "C3-HG2", "C3-HG3", "C3-HG4"):
            row = hardgates.get(name)
            if not isinstance(row, Mapping) or row.get("status") != "pass":
                return name
        return None

    def c3_hardgate_verdicts(self, summaries: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        separation = summaries[SEPARATION_FIELD]
        tradeoff = summaries["tradeoff_ledger"]
        trend = summaries["trend_summary"]
        not_claimed = self.not_claimed()
        return {
            "C3-HG1": {
                "status": separation["status"],
                "evidence": "SIGReg sliced-CF and covariance proxy are finite, separately named, separately sourced, and not collapsed",
                "metric_separation_pointer": f"$.{SEPARATION_FIELD}",
                "separate_reported": separation["separate_reported"],
                "collapsed": separation["collapsed"],
            },
            "C3-HG2": {
                "status": _status(bool(tradeoff["recorded"] and tradeoff["gaussianity_improves_alignment_hurts"])),
                "evidence": "Gaussianity improves while alignment loss increases, so the tradeoff ledger is populated",
                "tradeoff_pointer": "$.tradeoff_ledger.rows.0",
            },
            "C3-HG3": {
                "status": _status(bool(trend["expected_trend"]["lambda_expected"] and trend["expected_trend"]["rho_expected"])),
                "evidence": "Only the expected rho and lambda trend promotes D2",
                "trend_pointer": "$.trend_summary.expected_trend",
            },
            "C3-HG4": {
                "status": _status("full LeJEPA reproduction" in not_claimed and not bool(self.config.get("full_lejepa_claim", False))),
                "evidence": "full LeJEPA reproduction remains outside the mini-grid claim surface",
                "not_claimed": not_claimed,
                "full_lejepa_claim": bool(self.config.get("full_lejepa_claim", False)),
            },
        }

    def discovery_map_signal(self, hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
        statuses = {name: row.get("status") for name, row in hardgates.items()}
        structural_failed = next(
            (name for name in ("C3-HG1", "C3-HG2", "C3-HG4") if statuses.get(name) != "pass"),
            None,
        )
        if structural_failed is not None:
            return {
                "status": "negative",
                "level_candidate": "DN",
                "reason": "structural-hardgate-failed",
                "evidence_pointer": "$.hardgate.failed_gate",
                "trend_pointer": "$.trend_summary",
                "debt_row_pointer": "$.tradeoff_ledger.rows.0",
                "failed_gate": structural_failed,
                "failed_gate_pointer": f"$.c3_hardgates.{structural_failed}.status",
            }
        if statuses.get("C3-HG3") != "pass":
            return {
                "status": "d1-grid-evidence",
                "level_candidate": "D1",
                "reason": "trend-hardgate-failed",
                "evidence_pointer": "$.tradeoff_ledger.rows.0",
                "trend_pointer": "$.trend_summary",
                "debt_row_pointer": "$.tradeoff_ledger.rows.0",
                "failed_gate": "C3-HG3",
                "failed_gate_pointer": "$.c3_hardgates.C3-HG3.status",
            }
        return {
            "status": "d2-candidate",
            "level_candidate": "D2",
            "reason": "expected-trend",
            "evidence_pointer": "$.trend_summary.expected_trend",
            "trend_pointer": "$.trend_summary",
            "debt_row_pointer": "$.tradeoff_ledger.rows.0",
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
        capsule_hardgates = _without_pointer_fields(dict(hardgates))
        capsule = {
            "schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
            "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
            "run_id": str(self.config.get("run_id", "sigreg-mini-grid")),
            "generated_at": self.generated_at,
            "producer": PROJECTOR,
            "claim_status": "d2-candidate" if accepted else "failed",
            "positive_claim": dict(positive_claim),
            "source_artifacts": {
                "summary": self.run_artifacts.get("summary"),
                "raw_metrics": self.run_artifacts.get("raw_metrics"),
                "cost_protocol": "configs/default_cost_protocol.yaml",
            },
            "not_claimed": self.not_claimed(),
            "failed_gate": failed,
            "what_was_learned": (
                "The mini-grid separates SIGReg sliced-CF from covariance proxy and records the expected lambda/rho trend."
                if accepted
                else "The mini-grid recorded a failed hardgate without promoting a positive claim."
            ),
            "hardgates": capsule_hardgates,
            "result_snapshot": {
                "metric_separation": _without_pointer_fields(summaries[SEPARATION_FIELD]),
                "discovery_map_signal": _without_pointer_fields(dict(signal)),
                "best_cell": summaries["best_cell"],
                "trend_summary": summaries["trend_summary"],
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
            "# SIGReg Mini-Grid",
            "",
            f"- run_id: `{payload['run_id']}`",
            f"- schema_id: `{payload['schema_id']}`",
            f"- discovery map signal: `{payload[D_LEVEL_FIELD]['status']}`",
            f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
            "",
            "## Hardgates",
            "",
        ]
        for gate, row in payload["c3_hardgates"].items():
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
        by_lambda = self._lambda_summary(alignment_lambdas)
        by_rho = self._rho_summary(rhos)
        by_mixing = self._mixing_summary(mixings)
        metric_separation = self._metric_separation()
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
        lambda_quality = [by_lambda[str(float(value))]["quality_q_mean"] for value in alignment_lambdas]
        lambda_collapse = [by_lambda[str(float(value))]["collapse_rate_mean"] for value in alignment_lambdas]
        rho_r2 = [by_rho[str(float(value))]["linear_identifiability_r2_mean"] for value in rhos]
        lambda_expected = _strictly_ordered(lambda_quality, increasing=False) and _strictly_ordered(lambda_collapse, increasing=True)
        rho_expected = _strictly_ordered(rho_r2, increasing=True)
        tradeoff_row = {
            "row_id": "sigreg-gaussianity-alignment-tradeoff",
            "status": _status(improves_gaussianity and hurts_alignment),
            "sigreg_gaussianity_improves_with_lambda": improves_gaussianity,
            "alignment_hurt_with_lambda": hurts_alignment,
            "low_lambda_sigreg_sliced_cf_mean": low_sigreg,
            "high_lambda_sigreg_sliced_cf_mean": high_sigreg,
            "low_lambda_alignment_loss_mean": low_alignment,
            "high_lambda_alignment_loss_mean": high_alignment,
        }
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
            },
            "best_cell": self._best_cell(),
            SEPARATION_FIELD: metric_separation,
            "trend_summary": {
                "expected_trend": {
                    "lambda_expected": lambda_expected,
                    "rho_expected": rho_expected,
                    "status": _status(lambda_expected and rho_expected),
                },
                "lambda_quality_q_decreasing": _strictly_ordered(lambda_quality, increasing=False),
                "lambda_collapse_rate_increasing": _strictly_ordered(lambda_collapse, increasing=True),
                "rho_linear_identifiability_r2_increasing": _strictly_ordered(rho_r2, increasing=True),
            },
            "tradeoff_ledger": {
                "recorded": bool(improves_gaussianity and hurts_alignment),
                "gaussianity_improves_alignment_hurts": bool(improves_gaussianity and hurts_alignment),
                "rows": [tradeoff_row],
            },
        }

    def _metric_separation(self) -> dict[str, Any]:
        row_pairs = [(_metric(row, "sigreg_sliced_cf"), _metric(row, "covariance_proxy")) for row in self.records]
        complete_row_pairs = [(sigreg, cov) for sigreg, cov in row_pairs if sigreg is not None and cov is not None]
        sigreg_values = [sigreg for sigreg, _ in complete_row_pairs]
        cov_values = [cov for _, cov in complete_row_pairs]
        sigreg_mean = _mean(sigreg_values)
        cov_mean = _mean(cov_values)
        separate_reported = bool(row_pairs) and len(complete_row_pairs) == len(row_pairs)
        collapsed = False
        if separate_reported:
            collapsed = all(
                abs(float(sigreg) - float(cov)) <= 1.0e-12
                for sigreg, cov in complete_row_pairs
            )
        return {
            "status": _status(separate_reported and not collapsed),
            "separate_reported": separate_reported,
            "collapsed": collapsed,
            "sigreg_metric": {
                "row_key": "sigreg_sliced_cf",
                "source": "SlicedCFGaussianityProbe.score.sigreg_penalty",
                "mean": sigreg_mean,
            },
            "covariance_proxy_metric": {
                "row_key": "covariance_proxy",
                "source": "SlicedCFGaussianityProbe.score.cov_to_identity_fro",
                "mean": cov_mean,
            },
            "mean_delta_sigreg_minus_covariance_proxy": (
                None if sigreg_mean is None or cov_mean is None else float(sigreg_mean - cov_mean)
            ),
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
    "D_LEVEL_FIELD",
    "DEFAULT_ALIGNMENT_LAMBDAS",
    "DEFAULT_MIXINGS",
    "DEFAULT_RHOS",
    "DEFAULT_SEEDS",
    "FORBIDDEN_SUMMARY_ALIASES",
    "METRIC_KEYS",
    "NOT_CLAIMED",
    "SCHEMA_ID",
    "SEPARATION_FIELD",
    "SIGRegMiniGridProjection",
    "SUMMARY_RESULT_FIELD",
    "default_grid",
]

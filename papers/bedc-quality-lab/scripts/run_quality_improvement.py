#!/usr/bin/env python3
"""Run a finite-sample quality improvement projection."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import classifier_certificate, metric_bundle, quality_components
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.toy_world import make_toy_batch

TARGET_DEBT_RESIDUE = "finite-sample-support"
BEFORE_ENVELOPE_ARTIFACT = "reports/improvement_before_envelope.json"
AFTER_ENVELOPE_ARTIFACT = "reports/improvement_after_envelope.json"
REPORT_ARTIFACT = "reports/quality_improvement_report.md"


def _parse_debt_row(row: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for part in row.split("; "):
        if "=" not in part:
            raise ValueError(f"malformed debt row: {row!r}")
        key, value = part.split("=", 1)
        if not key or not value:
            raise ValueError(f"malformed debt row: {row!r}")
        fields[key] = value

    required = {"kind", "residue", "severity", "status", "score"}
    if set(fields) != required:
        raise ValueError(f"malformed debt row: {row!r}")
    try:
        float(fields["score"])
    except ValueError as exc:
        raise ValueError(f"malformed debt row: {row!r}") from exc
    return fields


def _target_debt_row(envelope: QualityEvidenceEnvelope, residue: str = TARGET_DEBT_RESIDUE) -> dict[str, str]:
    matches = []
    for row in envelope.debt_items:
        fields = _parse_debt_row(row)
        if fields["residue"] == residue:
            matches.append(fields)

    if len(matches) != 1:
        raise ValueError(f"expected exactly one {residue!r} debt row, found {len(matches)}")
    return matches[0]


def quality_delta(
    before: QualityEvidenceEnvelope,
    after: QualityEvidenceEnvelope,
    *,
    target_residue: str = TARGET_DEBT_RESIDUE,
) -> dict[str, float | str]:
    before_row = _target_debt_row(before, target_residue)
    after_row = _target_debt_row(after, target_residue)
    before_score = float(before_row["score"])
    after_score = float(after_row["score"])
    return {
        "target_residue": target_residue,
        "before_status": before_row["status"],
        "after_status": after_row["status"],
        "before_score": before_score,
        "after_score": after_score,
        "delta_target_score": after_score - before_score,
        "delta_q": float(after.metrics["quality_q"]) - float(before.metrics["quality_q"]),
        "delta_debt": float(after.metrics["quality_debt"]) - float(before.metrics["quality_debt"]),
    }


def _format_signed(value: float) -> str:
    return f"{value:+.6f}"


def run_improvement_surface(
    *,
    sample_count: int,
    seed: int = 23,
    run_id: str,
    envelope_artifact: str,
    report_artifact: str = REPORT_ARTIFACT,
) -> QualityEvidenceEnvelope:
    rho = 0.82
    batch = make_toy_batch(sample_count, rho=rho, seed=seed)
    centered = batch.x - batch.x.mean(axis=0, keepdims=True)
    scale = centered.std(axis=0, keepdims=True)
    scale[scale <= 1e-12] = 1.0
    h = centered / scale
    metrics = metric_bundle(h, batch.z)
    certificate = classifier_certificate(metrics)
    source_spec = {
        "name": "gaussian-ou-toy-world",
        "latent_dim": 2,
        "sample_count": int(batch.z.shape[0]),
        "rho": rho,
        "mixing": "sinusoidal-parabolic-shear",
    }
    pattern_spec = {
        "name": "latent-linear-recovery",
        "target": "recover z from representation h by linear least squares",
    }
    classifier_spec = {
        "name": "standardized-nonlinear-observation",
        "output_dim": 2,
        "training": "deterministic-standardization",
        **certificate,
    }
    stability_spec = {
        "name": "fixed-seed-single-source",
        "seed": seed,
        "pair_process": "ornstein-uhlenbeck",
    }
    debt_assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec)
    ledger_gaps = derive_ledger_gaps(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        debt_assessment,
    )
    metrics = {
        **metrics,
        **quality_components(metrics, debt_assessment.debt_total, classifier_spec),
    }
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=run_id,
        source_spec=source_spec,
        pattern_spec=pattern_spec,
        classifier_spec=classifier_spec,
        stability_spec=stability_spec,
        metrics=metrics,
        ledger_gaps=format_ledger_gaps(ledger_gaps),
        debt_items=format_debt_items(debt_assessment),
        artifacts={
            "envelope": envelope_artifact,
            "report": report_artifact,
        },
        bedc_refs=[
            "papers/bedc/preamble.tex:closurestatus",
            "papers/bedc/parts/project_governance/theory_amendment_policy.tex",
        ],
    )


def _render_improvement_report(before: QualityEvidenceEnvelope, after: QualityEvidenceEnvelope) -> str:
    delta = quality_delta(before, after)
    lines = [
        "# BEDC Quality Lab 改进报告",
        "",
        "## 对照设置",
        "",
        f"- 目标 debt residue：`{delta['target_residue']}`",
        f"- 干预前运行：`{before.run_id}`",
        f"- 干预后运行：`{after.run_id}`",
        f"- 干预前 artifact：`{before.artifacts['envelope']}`",
        f"- 干预后 artifact：`{after.artifacts['envelope']}`",
        "",
        "## 指标变化",
        "",
        f"- `delta_q`：{_format_signed(float(delta['delta_q']))}",
        f"- `delta_debt`：{_format_signed(float(delta['delta_debt']))}",
        f"- `delta_target_score`：{_format_signed(float(delta['delta_target_score']))}",
        "",
        "## finite-sample residue",
        "",
        f"- 干预前 status：`{delta['before_status']}`；score：{float(delta['before_score']):.6f}",
        f"- 干预后 status：`{delta['after_status']}`；score：{float(delta['after_score']):.6f}",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    before = run_improvement_surface(
        sample_count=384,
        run_id="gaussian-ou-lejepa-finite-sample-before",
        envelope_artifact=BEFORE_ENVELOPE_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    after = run_improvement_surface(
        sample_count=2048,
        run_id="gaussian-ou-lejepa-finite-sample-after",
        envelope_artifact=AFTER_ENVELOPE_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )

    before_path = ROOT / BEFORE_ENVELOPE_ARTIFACT
    after_path = ROOT / AFTER_ENVELOPE_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    before.write_json(before_path)
    after.write_json(after_path)
    report_path.write_text(_render_improvement_report(before, after), encoding="utf-8")
    print(f"wrote {before_path.relative_to(ROOT)}")
    print(f"wrote {after_path.relative_to(ROOT)}")
    print(f"wrote {report_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

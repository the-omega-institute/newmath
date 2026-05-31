#!/usr/bin/env python3
"""Run the boundary-gated BEDC-JEPA protocol sketch."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_metrics import (
    bedc_debt_score,
    binary_accuracy,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    masked_binary_accuracy,
    unlogged_error_rate,
)
from bedc_quality_lab.bedc_jepa_world import (
    make_boundary_gated_batch,
    radial_distinction_score,
    radial_gap_score,
    standardize_observation,
)
from bedc_quality_lab.metrics import metric_bundle
from bedc_quality_lab.report import write_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope


def run_protocol() -> QualityEvidenceEnvelope:
    batch = make_boundary_gated_batch(768, rho=0.84, radius=1.0, gap_width=0.14, seed=41)
    h = standardize_observation(batch.x)
    distinction_scores = radial_distinction_score(h, radius=batch.radius)
    gap_scores = radial_gap_score(h, radius=batch.radius, gap_width=batch.gap_width)

    outside_gap = ~batch.gap
    distinction_accuracy = binary_accuracy(distinction_scores, batch.distinction)
    outside_gap_accuracy = masked_binary_accuracy(distinction_scores, batch.distinction, outside_gap)
    false_claim = false_claim_rate(distinction_scores, batch.distinction, batch.gap)
    gap_auc = gap_detection_auc(gap_scores, batch.gap)
    unlogged_error = unlogged_error_rate(distinction_scores, batch.distinction, gap_scores)
    certified = certified_coverage(gap_scores)
    debt = bedc_debt_score(
        unlogged_error=unlogged_error,
        false_claim=false_claim,
        gap_auc=gap_auc,
        certified=certified,
    )

    metrics = metric_bundle(h, batch.z)
    metrics.update(
        {
            "distinction_accuracy": distinction_accuracy,
            "distinction_accuracy_outside_gap": outside_gap_accuracy,
            "gap_detection_auc": gap_auc,
            "false_claim_rate_inside_gap": false_claim,
            "unlogged_error_rate": unlogged_error,
            "certified_coverage": certified,
            "bedc_debt_score": debt,
        }
    )

    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id="boundary-gated-bedc-jepa-protocol-seed-41",
        source_spec={
            "name": "boundary-gated-ou-world",
            "latent_dim": 2,
            "sample_count": int(batch.z.shape[0]),
            "rho": 0.84,
            "radius": batch.radius,
            "gap_width": batch.gap_width,
            "observation": "sinusoidal-parabolic-shear",
        },
        pattern_spec={
            "name": "latent-plus-distinction-plus-gap",
            "target": "learn continuous state, operational inside-boundary distinction, and boundary gap ledger",
        },
        classifier_spec={
            "name": "bedc-jepa-protocol-radial-distinction-gap-heads",
            "output_dim": 4,
            "training": "protocol-sketch-standardized-observation-no-gradient",
        },
        stability_spec={
            "name": "ou-continuation-boundary-scope",
            "seed": 41,
            "pair_process": "ornstein-uhlenbeck",
            "claim_boundary": "low-gap cases only",
        },
        metrics=metrics,
        ledger_gaps=[
            "no-gradient-bedc-jepa-training-yet",
            "one-boundary-family",
            "no-gap-aware-planning-rollout-yet",
        ],
        debt_items=[
            "model-debt: this artifact defines the BEDC-JEPA target protocol before training the full objective",
            "gap-debt: boundary-gated ledger is radial and synthetic only",
            "planning-debt: gap penalty theorem is specified in the directive but not experimentally tested here",
        ],
        artifacts={
            "envelope": "reports/bedc_jepa_boundary_envelope.json",
            "report": "reports/bedc_jepa_boundary_report.md",
        },
        bedc_refs=[
            "papers/bedc/preamble.tex:closurestatus",
            "papers/bedc/parts/project_governance/theory_amendment_policy.tex",
        ],
    )


def main() -> None:
    envelope = run_protocol()
    envelope_path = ROOT / "reports" / "bedc_jepa_boundary_envelope.json"
    report_path = ROOT / "reports" / "bedc_jepa_boundary_report.md"
    envelope.write_json(envelope_path)
    write_quality_report(envelope, report_path)
    print(f"wrote {envelope_path.relative_to(ROOT)}")
    print(f"wrote {report_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Run the Gaussian-OU LeJEPA toy evidence loop."""

from __future__ import annotations

from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import assess_debt, format_debt_items
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import classifier_certificate, metric_bundle, quality_components
from bedc_quality_lab.report import write_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.toy_world import make_toy_batch


def _fallback_encoder(x: np.ndarray) -> np.ndarray:
    centered = x - np.mean(x, axis=0, keepdims=True)
    scale = np.std(centered, axis=0, keepdims=True)
    scale = np.where(scale <= 1e-12, 1.0, scale)
    return centered / scale


def _torch_encoder(x: np.ndarray, x_pair: np.ndarray, *, seed: int) -> np.ndarray:
    from bedc_quality_lab.model import (
        build_tiny_encoder,
        choose_device,
        representation_loss,
        set_deterministic_seed,
    )

    import torch

    set_deterministic_seed(seed)
    device = choose_device()
    encoder = build_tiny_encoder().to(device)
    optimizer = torch.optim.AdamW(encoder.parameters(), lr=2e-3, weight_decay=1e-4)
    x_t = torch.as_tensor(x, dtype=torch.float32, device=device)
    x_pair_t = torch.as_tensor(x_pair, dtype=torch.float32, device=device)
    for _ in range(80):
        optimizer.zero_grad(set_to_none=True)
        h = encoder(x_t)
        h_pair = encoder(x_pair_t)
        loss = representation_loss(h, h_pair)
        loss.backward()
        optimizer.step()
    with torch.no_grad():
        return encoder(x_t).detach().cpu().numpy().astype(np.float64)


def run_experiment(
    *,
    use_torch: bool = True,
    sample_count: int = 384,
    seed: int = 23,
    rho: float = 0.82,
    run_id: str = "gaussian-ou-lejepa-seed-23",
    envelope_artifact: str = "reports/example_envelope.json",
    report_artifact: str = "reports/quality_report.md",
) -> QualityEvidenceEnvelope:
    batch = make_toy_batch(sample_count, rho=rho, seed=seed)
    encoder_name = "standardized-nonlinear-observation"

    if use_torch:
        try:
            h = _torch_encoder(batch.x, batch.x_pair, seed=seed)
            encoder_name = "tiny-mlp-2-128-128-2"
        except Exception:
            h = _fallback_encoder(batch.x)
    else:
        h = _fallback_encoder(batch.x)

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
        "name": encoder_name,
        "output_dim": 2,
        "training": "align-cov-mean" if encoder_name.startswith("tiny") else "deterministic-standardization",
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
    envelope = QualityEvidenceEnvelope(
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
    return envelope


def main() -> None:
    envelope = run_experiment(use_torch=True)
    envelope_path = ROOT / "reports" / "example_envelope.json"
    report_path = ROOT / "reports" / "quality_report.md"
    envelope.write_json(envelope_path)
    write_quality_report(envelope, report_path)
    print(f"wrote {envelope_path.relative_to(ROOT)}")
    print(f"wrote {report_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

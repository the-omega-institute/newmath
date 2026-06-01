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
from bedc_quality_lab.identifiability_bound import identifiability_bound_metrics
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import metric_bundle, quality_components_from_bound
from bedc_quality_lab.report import write_quality_report
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.theorem_bound_quality import theorem_bound_certificate
from bedc_quality_lab.mixing import DEFAULT_MIXING
from bedc_quality_lab.toy_world import make_toy_batch
from bedc_quality_lab.transition import TransitionKernelSpec


def _train_eval_split(sample_count: int, *, seed: int) -> tuple[np.ndarray, np.ndarray]:
    if sample_count < 4:
        raise ValueError("sample_count must be at least 4 for train/eval split")
    rng = np.random.default_rng(seed ^ 0xA5A5A5A5)
    indices = rng.permutation(sample_count)
    train_count = min(sample_count - 1, max(1, round(0.70 * sample_count)))
    train_idx = np.sort(indices[:train_count]).astype(np.int64)
    eval_idx = np.sort(indices[train_count:]).astype(np.int64)
    if np.intersect1d(train_idx, eval_idx).size != 0:
        raise ValueError("train/eval split must be disjoint")
    return train_idx, eval_idx


def _index_checksum(indices: np.ndarray) -> int:
    weights = np.arange(1, indices.shape[0] + 1, dtype=np.int64)
    return int(np.sum((indices.astype(np.int64) + 1) * weights))


def _fallback_encoder(
    train_x: np.ndarray,
    eval_x: np.ndarray,
    eval_x_pair: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    centered_train = train_x - np.mean(train_x, axis=0, keepdims=True)
    center = np.mean(train_x, axis=0, keepdims=True)
    scale = np.std(centered_train, axis=0, keepdims=True)
    scale = np.where(scale <= 1e-12, 1.0, scale)
    return (eval_x - center) / scale, (eval_x_pair - center) / scale


def _torch_encoder(
    train_x: np.ndarray,
    train_x_pair: np.ndarray,
    eval_x: np.ndarray,
    eval_x_pair: np.ndarray,
    *,
    seed: int,
) -> tuple[np.ndarray, np.ndarray]:
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
    x_t = torch.as_tensor(train_x, dtype=torch.float32, device=device)
    x_pair_t = torch.as_tensor(train_x_pair, dtype=torch.float32, device=device)
    for _ in range(80):
        optimizer.zero_grad(set_to_none=True)
        h = encoder(x_t)
        h_pair = encoder(x_pair_t)
        loss = representation_loss(h, h_pair)
        loss.backward()
        optimizer.step()
    with torch.no_grad():
        eval_t = torch.as_tensor(eval_x, dtype=torch.float32, device=device)
        eval_pair_t = torch.as_tensor(eval_x_pair, dtype=torch.float32, device=device)
        h = encoder(eval_t).detach().cpu().numpy().astype(np.float64)
        h_pair = encoder(eval_pair_t).detach().cpu().numpy().astype(np.float64)
        return h, h_pair


def run_experiment(
    *,
    use_torch: bool = True,
    sample_count: int = 384,
    seed: int = 23,
    rho: float = 0.82,
    transition_kernel: TransitionKernelSpec | None = None,
    mixing: str = DEFAULT_MIXING,
    run_id: str = "gaussian-ou-lejepa-seed-23",
    envelope_artifact: str = "reports/example_envelope.json",
    report_artifact: str = "reports/quality_report.md",
) -> QualityEvidenceEnvelope:
    spec = transition_kernel if transition_kernel is not None else TransitionKernelSpec.isotropic(rho, latent_dim=2)
    batch = make_toy_batch(sample_count, rho=rho, seed=seed, transition_kernel=spec, mixing=mixing)
    train_idx, eval_idx = _train_eval_split(batch.z.shape[0], seed=seed)
    train_x = batch.x[train_idx]
    train_x_pair = batch.x_pair[train_idx]
    eval_x = batch.x[eval_idx]
    eval_x_pair = batch.x_pair[eval_idx]
    eval_z = batch.z[eval_idx]
    encoder_name = "standardized-nonlinear-observation"

    if use_torch:
        try:
            h, h_pair = _torch_encoder(train_x, train_x_pair, eval_x, eval_x_pair, seed=seed)
            encoder_name = "tiny-mlp-2-128-128-2"
        except Exception:
            h, h_pair = _fallback_encoder(train_x, eval_x, eval_x_pair)
    else:
        h, h_pair = _fallback_encoder(train_x, eval_x, eval_x_pair)

    metrics = {
        **metric_bundle(h, eval_z),
        **identifiability_bound_metrics(h, h_pair, eval_z, rho),
    }
    certificate = theorem_bound_certificate(metrics)
    transition_source = spec.to_source_spec()
    source_spec = {
        "name": "gaussian-ou-toy-world",
        "latent_dim": 2,
        "sample_count": int(batch.z.shape[0]),
        "rho": rho,
        "rho_by_axis": list(spec.rho_by_axis),
        "latent_distribution": "gaussian",
        "mixing": mixing,
        "transition_kernel": transition_source,
        "transition_isotropic": transition_source["isotropic"],
        "transition_anisotropy_gap": transition_source["anisotropy_gap"],
    }
    pattern_spec = {
        "name": "latent-linear-recovery",
        "target": "recover z from representation h by linear least squares",
    }
    classifier_spec = {
        "name": encoder_name,
        "output_dim": 2,
        "training": "align-cov-mean" if encoder_name.startswith("tiny") else "deterministic-standardization",
        "split_policy": "train-eval-disjoint",
        "train_fraction": 0.70,
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "train_index_checksum": _index_checksum(train_idx),
        "eval_index_checksum": _index_checksum(eval_idx),
        "overlap_count": int(np.intersect1d(train_idx, eval_idx).shape[0]),
        **certificate,
    }
    stability_spec = {
        "name": "fixed-seed-single-source",
        "seed": seed,
        "pair_process": "ornstein-uhlenbeck",
        "transition_noise_family": spec.noise_family,
        "transition_eigenvalue_interleaving": transition_source["eigenvalue_interleaving"],
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
        **quality_components_from_bound(metrics, debt_assessment.debt_total, classifier_spec),
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

"""Markdown projection for quality evidence envelopes."""

from __future__ import annotations

from pathlib import Path

from .cost_protocol import CostProtocol, format_cost_protocol_lines, load_cost_protocol
from .schema import QualityEvidenceEnvelope
from .tensor_namecert_candidate import closure_status_rows, from_quality_evidence_envelope


_IDENTIFIABILITY_BOUND_MSE_KEYS = (
    "alignment_loss_mse",
    "covariance_trace",
    "alignment_gap_delta_mse",
    "normalized_gap_d_mse",
    "whitening_deviation_epsilon",
    "theorem3_bound_mse",
    "actual_recovery_mse",
    "bound_margin_mse",
    "cert_bound_margin_mse",
    "theorem_bound_benefit",
    "theorem_bound_gap_penalty",
    "theorem_bound_whitening_penalty",
    "theorem_bound_recovery_pressure",
)
_IDENTIFIABILITY_BOUND_NORMALIZED_KEYS = (
    "alignment_loss_normalized",
    "alignment_gap_delta_normalized",
    "actual_recovery_normalized",
    "theorem3_bound_normalized",
    "bound_margin_normalized",
)


def _format_metric(value: float) -> str:
    return f"{value:.6f}"


def render_quality_report(envelope: QualityEvidenceEnvelope, protocol: CostProtocol | None = None) -> str:
    metrics = envelope.metrics
    cost_protocol = load_cost_protocol() if protocol is None else protocol
    candidate = from_quality_evidence_envelope(envelope)
    lines = [
        "# BEDC Model Quality Lab 报告",
        "",
        f"- 运行 ID：`{envelope.run_id}`",
        f"- Schema：`{envelope.schema_id}`",
        f"- 数据源：`{envelope.source_spec.get('name', 'unknown')}`",
        f"- 模式：`{envelope.pattern_spec.get('name', 'unknown')}`",
        f"- 分类器：`{envelope.classifier_spec.get('name', 'unknown')}`",
        f"- 稳定性设置：`{envelope.stability_spec.get('name', 'unknown')}`",
        "",
        "## Tensor NameCert Candidate",
        "",
        f"- Candidate：`{candidate.name}`",
        f"- Evidence envelope：`{candidate.evidence_envelope_ref['schema_id']}:{candidate.evidence_envelope_ref['run_id']}`",
    ]
    for field, level, provenance in closure_status_rows(candidate):
        lines.append(
            f"- `{field}` lab-local candidate closure：`{level}` "
            f"(provenance: `{provenance}`)"
        )
    lines.extend(
        [
            f"- Scope seal：`{candidate.scope_seal['boundary']}`",
            "",
        ]
    )
    lines.extend(["## 指标", ""])
    quality_keys = [key for key in sorted(metrics) if key.startswith("quality_")]
    bound_mse_keys = [key for key in _IDENTIFIABILITY_BOUND_MSE_KEYS if key in metrics]
    bound_normalized_keys = [key for key in _IDENTIFIABILITY_BOUND_NORMALIZED_KEYS if key in metrics]
    bound_keys = set(bound_mse_keys) | set(bound_normalized_keys)
    for key in sorted(metrics):
        if key not in quality_keys and key not in bound_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

    if bound_mse_keys:
        lines.extend(["", "## Identifiability Bound: MSE Scale", ""])
        cert_status = envelope.classifier_spec.get("cert_status")
        if isinstance(cert_status, str) and cert_status:
            lines.append(f"- `cert_status`：`{cert_status}`")
        for key in bound_mse_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

    if bound_normalized_keys:
        lines.extend(["", "## Normalized Projection", ""])
        for key in bound_normalized_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

    if quality_keys:
        lines.extend(["", "## Q 投影", ""])
        for key in quality_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

    lines.extend(["", "## Cost Protocol", ""])
    lines.extend(format_cost_protocol_lines(cost_protocol))

    lines.extend(["", "## Ledger gaps", ""])
    if envelope.ledger_gaps:
        lines.extend(f"- {item}" for item in envelope.ledger_gaps)
    else:
        lines.append("- 无")

    lines.extend(["", "## Debt items", ""])
    if envelope.debt_items:
        lines.extend(f"- {item}" for item in envelope.debt_items)
    else:
        lines.append("- 无")

    lines.extend(["", "## Artifacts", ""])
    for key in sorted(envelope.artifacts):
        lines.append(f"- `{key}`：`{envelope.artifacts[key]}`")

    lines.extend(["", "## BEDC refs", ""])
    if envelope.bedc_refs:
        lines.extend(f"- `{item}`" for item in envelope.bedc_refs)
    else:
        lines.append("- 无")

    return "\n".join(lines) + "\n"


def write_quality_report(
    envelope: QualityEvidenceEnvelope,
    path: str | Path,
    protocol: CostProtocol | None = None,
) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(render_quality_report(envelope, protocol=protocol), encoding="utf-8")

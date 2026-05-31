"""Markdown projection for quality evidence envelopes."""

from __future__ import annotations

from pathlib import Path

from .schema import QualityEvidenceEnvelope


def _format_metric(value: float) -> str:
    return f"{value:.6f}"


def render_quality_report(envelope: QualityEvidenceEnvelope) -> str:
    metrics = envelope.metrics
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
        "## 指标",
        "",
    ]
    quality_keys = [key for key in sorted(metrics) if key.startswith("quality_")]
    for key in sorted(metrics):
        if key not in quality_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

    if quality_keys:
        lines.extend(["", "## Q 投影", ""])
        for key in quality_keys:
            lines.append(f"- `{key}`：{_format_metric(metrics[key])}")

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


def write_quality_report(envelope: QualityEvidenceEnvelope, path: str | Path) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(render_quality_report(envelope), encoding="utf-8")

#!/usr/bin/env python3
"""Run a finite-sample quality improvement projection."""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.schema import QualityEvidenceEnvelope
from scripts.run_gaussian_ou_lejepa import run_experiment

TARGET_DEBT_KIND = "finite-sample"
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


def _target_debt_row(envelope: QualityEvidenceEnvelope, kind: str = TARGET_DEBT_KIND) -> dict[str, str]:
    matches = []
    for row in envelope.debt_items:
        fields = _parse_debt_row(row)
        if fields["kind"] == kind:
            matches.append(fields)

    if len(matches) != 1:
        raise ValueError(f"expected exactly one {kind!r} debt row, found {len(matches)}")
    return matches[0]


def _quality_delta(
    before: QualityEvidenceEnvelope,
    after: QualityEvidenceEnvelope,
    *,
    target_kind: str = TARGET_DEBT_KIND,
) -> dict[str, float | str]:
    before_row = _target_debt_row(before, target_kind)
    after_row = _target_debt_row(after, target_kind)
    before_score = float(before_row["score"])
    after_score = float(after_row["score"])
    return {
        "target_kind": target_kind,
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


def _render_improvement_report(before: QualityEvidenceEnvelope, after: QualityEvidenceEnvelope) -> str:
    delta = _quality_delta(before, after)
    lines = [
        "# BEDC Quality Lab 改进报告",
        "",
        "## 对照设置",
        "",
        f"- 目标 debt kind：`{delta['target_kind']}`",
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
    before = run_experiment(
        use_torch=False,
        sample_count=384,
        run_id="gaussian-ou-lejepa-finite-sample-before",
        envelope_artifact=BEFORE_ENVELOPE_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    after = run_experiment(
        use_torch=False,
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

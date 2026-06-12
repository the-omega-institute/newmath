#!/usr/bin/env python3
"""Produce the discovery-gated transformer canonical report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_gated_transformer import (
    CANONICAL_JSON_ARTIFACT,
    CANONICAL_MARKDOWN_ARTIFACT,
    CLAIM_CAPSULE_ARTIFACT,
    EVIDENCE_ENVELOPE_ARTIFACT,
    JET_CERTIFICATE_ARTIFACT,
    MECHANISM_NAMECERT_ARTIFACT,
    MODEL_ID,
    SCALING_LADDER_LEVEL_IDS,
    SOURCE_REFS_ARTIFACT,
    _toy_seed_surface_summary,
    build_projection,
    build_d5_m_projection,
    build_scaling_ladder_projection,
    default_sidecars,
    render_markdown,
    validate_dgt_hardgate_evidence_bundle,
    validate_projection,
)


GENERATED_AT = "2026-06-07T00:00:00+00:00"
SIDECAR_ARTIFACTS = {
    "claim_capsule": CLAIM_CAPSULE_ARTIFACT,
    "evidence_envelope": EVIDENCE_ENVELOPE_ARTIFACT,
    "mechanism_namecert": MECHANISM_NAMECERT_ARTIFACT,
    "source_refs": SOURCE_REFS_ARTIFACT,
    "jet_certificate": JET_CERTIFICATE_ARTIFACT,
}
CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
HIGH_IMPACT_REVIEW_JSON_ARTIFACT = "reports/canonical/high-impact-review.json"


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_payload(
    *,
    generated_at: str = GENERATED_AT,
    component_refs: Mapping[str, Any] | None = None,
    robustness_source_payloads: Mapping[str, Mapping[str, Any]] | None = None,
    claim_verdict_rows: Sequence[Mapping[str, Any]] | None = None,
    high_impact_review_rows: Sequence[Mapping[str, Any]] | None = None,
    d5_o_surface_summary: Mapping[str, Any] | None = None,
    root: Path = ROOT,
) -> dict[str, Any]:
    return build_projection(
        generated_at=generated_at,
        component_refs=component_refs,
        robustness_source_payloads=robustness_source_payloads,
        claim_verdict_rows=claim_verdict_rows,
        high_impact_review_rows=high_impact_review_rows,
        d5_o_surface_summary=d5_o_surface_summary,
        root=root,
    )


def validate_payload(payload: Mapping[str, Any]) -> None:
    validate_projection(payload)


def build_run_sidecars(*, generated_at: str) -> dict[str, dict[str, Any]]:
    return default_sidecars(generated_at=generated_at)


def _read_claim_verdict_rows(root: Path) -> list[dict[str, Any]]:
    path = root / CLAIM_VERDICTS_JSONL_ARTIFACT
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if isinstance(row, dict):
            rows.append(row)
    return rows


def _read_high_impact_review_rows(root: Path) -> list[dict[str, Any]]:
    path = root / HIGH_IMPACT_REVIEW_JSON_ARTIFACT
    if not path.exists():
        return []
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("review_rows") if isinstance(payload, Mapping) else None
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, dict)]


def write_artifacts(payload: Mapping[str, Any], *, root: Path = ROOT) -> None:
    validate_projection(payload)
    sidecars = build_run_sidecars(generated_at=str(payload["generated_at"]))
    for name, artifact in SIDECAR_ARTIFACTS.items():
        _write_json(root / artifact, sidecars[name])
    _write_json(root / CANONICAL_JSON_ARTIFACT, dict(payload))
    validate_dgt_hardgate_evidence_bundle(payload, root=root)
    markdown_path = root / CANONICAL_MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    payload = build_payload(
        generated_at=args.generated_at,
        high_impact_review_rows=_read_high_impact_review_rows(args.root),
        root=args.root,
    )
    write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "model_id": MODEL_ID,
                "hardgate": payload["hardgate"]["status"],
                "discovery_level": payload["scaling_ladder"]["discovery_level"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Write the Boundary-Causal-Jet NameCert candidate owner and projections."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.jet_namecert_candidate import (
    CAUSAL_PATCH_SUITE_ARTIFACT,
    DGT_CANONICAL_ARTIFACT,
    DGT_JSON_ARTIFACT,
    DGT_RUN_JET_CERTIFICATE_ARTIFACT,
    GAP_HEAD_ATTRIBUTION_ARTIFACT,
    MARKDOWN_ARTIFACT,
    OWNER_JSON_ARTIFACT,
    TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT,
    JetNameCertCandidate,
    audit_dgt_jet_projection,
    audit_jet_namecert_candidate,
    build_dgt_jet_projection,
    render_boundary_causal_jet_certificate,
)


SOURCE_ARTIFACTS = {
    "dgt_payload": DGT_CANONICAL_ARTIFACT,
    "jet_certificate_payload": DGT_RUN_JET_CERTIFICATE_ARTIFACT,
    "derivative_payload": TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT,
    "causal_patch_payload": CAUSAL_PATCH_SUITE_ARTIFACT,
    "attribution_payload": GAP_HEAD_ATTRIBUTION_ARTIFACT,
}


def build_payload(*, root: Path | str | None = None, generated_at: str | None = None) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    sources = {name: _load_mapping(active_root / artifact) for name, artifact in SOURCE_ARTIFACTS.items()}
    candidate = JetNameCertCandidate.from_sources(generated_at=generated_at, **sources)
    payload = candidate.to_dict()
    audit = audit_jet_namecert_candidate(payload)
    if audit["status"] != "pass":
        raise ValueError(f"jet namecert candidate audit failed: {audit['failures']}")
    if payload.get("scope", {}).get("d5_m_claim") is True and audit["d5_m_ready"] is not True:
        raise ValueError("jet namecert candidate overclaims D5-M readiness")
    payload["audit"] = audit
    return payload


def write_jet_namecert_candidate(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    payload = build_payload(root=active_root, generated_at=generated_at)
    dgt_projection = build_dgt_jet_projection(payload)
    projection_audit = audit_dgt_jet_projection(dgt_projection)
    if projection_audit["status"] != "pass":
        raise ValueError(f"DGT jet projection audit failed: {projection_audit['failures']}")

    _write_json(active_root / OWNER_JSON_ARTIFACT, payload)
    _write_json(active_root / DGT_JSON_ARTIFACT, dgt_projection)
    _write_text(active_root / MARKDOWN_ARTIFACT, render_boundary_causal_jet_certificate(payload))
    return payload


def _load_mapping(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"artifact payload must be a JSON object: {path}")
    return payload


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT))
    parser.add_argument("--generated-at", default=None)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_jet_namecert_candidate(root=args.root, generated_at=args.generated_at)
    print(f"wrote {payload['json_artifact']}")
    print(f"wrote {payload['dgt_projection_artifact']}")
    print(f"wrote {payload['markdown_artifact']}")
    print(f"d5_m_ready {payload['audit']['d5_m_ready']}")


if __name__ == "__main__":
    main()

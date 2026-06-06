#!/usr/bin/env python3
"""Write the gap-head mechanism NameCert candidate sidecar."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.mechanism_namecert_candidate import (
    MechanismNameCertCandidate,
    audit_mechanism_namecert_candidate,
    render_mechanism_namecert_markdown,
)
from scripts import run_gap_head_attribution_capsule as a1


JSON_ARTIFACT = "reports/gap_head_mechanism_namecert.json"
REPORT_ARTIFACT = "reports/gap_head_mechanism_namecert.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-mechanism-namecert"
CANONICAL_ROLE = "sidecar_not_in_CANONICAL_REPORTS"
OPERATIONAL_ARTIFACT = "reports/canonical/gap-head-on-h.json"
ABLATION_ARTIFACT = "reports/canonical/gap-head-ablation.json"
ROBUSTNESS_ARTIFACT = "reports/canonical/gap-head-robustness-sweep.json"
STABILITY_ARTIFACT = "reports/gap_head_discovery_stability.json"


def _load_mapping(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"artifact payload must be a JSON object: {path}")
    return payload


def _load_a1_payload(root: Path) -> dict[str, Any]:
    path = root / a1.CANONICAL_JSON_ARTIFACT
    payload = _load_mapping(path)
    if payload is not None:
        return payload
    return {}


def build_gap_head_mechanism_namecert(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    candidate = MechanismNameCertCandidate.from_gap_head_sources(
        a1_capsule=_load_a1_payload(active_root),
        operational_payload=_load_mapping(active_root / OPERATIONAL_ARTIFACT),
        ablation_payload=_load_mapping(active_root / ABLATION_ARTIFACT),
        robustness_payload=_load_mapping(active_root / ROBUSTNESS_ARTIFACT),
        stability_payload=_load_mapping(active_root / STABILITY_ARTIFACT),
    )
    payload = candidate.to_dict()
    payload.update(
        {
            "schema_id": "bedc-quality-lab:mechanism-namecert-candidate",
            "artifact_id": ARTIFACT_ID,
            "json_artifact": JSON_ARTIFACT,
            "markdown_artifact": REPORT_ARTIFACT,
            "generated_at": timestamp,
            "canonical_role": CANONICAL_ROLE,
            "candidate_semantics": "lab-local candidate only",
            "source_artifacts": {
                "a1_capsule": a1.CANONICAL_JSON_ARTIFACT,
                "operational": OPERATIONAL_ARTIFACT,
                "ablation": ABLATION_ARTIFACT,
                "robustness": ROBUSTNESS_ARTIFACT,
                "stability": STABILITY_ARTIFACT,
            },
        }
    )
    payload["audit"] = audit_mechanism_namecert_candidate(payload)
    return payload


def write_gap_head_mechanism_namecert(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    payload = build_gap_head_mechanism_namecert(root=active_root, generated_at=generated_at)
    json_path = active_root / JSON_ARTIFACT
    report_path = active_root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_mechanism_namecert_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Repository root for artifacts.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_gap_head_mechanism_namecert(root=args.root)
    print(f"wrote {payload['json_artifact']}")
    print(f"wrote {payload['markdown_artifact']}")
    print(f"d5_m_ready {payload['audit']['d5_m_ready']}")


if __name__ == "__main__":
    main()

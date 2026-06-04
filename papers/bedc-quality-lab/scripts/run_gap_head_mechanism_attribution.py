#!/usr/bin/env python3
"""Write a compatibility projection of the A1 gap-head attribution capsule."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import run_gap_head_attribution_v3 as a1


JSON_ARTIFACT = "reports/gap_head_mechanism_attribution.json"
REPORT_ARTIFACT = "reports/gap_head_mechanism_attribution.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-mechanism-attribution"


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _row_l2_direction(h: np.ndarray) -> np.ndarray:
    value = np.asarray(h, dtype=np.float64)
    if value.ndim != 2 or value.shape[0] == 0:
        raise ValueError("h must be a non-empty matrix")
    if not np.all(np.isfinite(value)):
        raise ValueError("h contains non-finite values")
    norms = np.linalg.norm(value, axis=1, keepdims=True)
    return np.divide(value, norms, out=np.zeros_like(value, dtype=np.float64), where=norms > 0.0)


def _load_a1_payload(root: Path) -> dict[str, Any]:
    path = root / a1.CANONICAL_JSON_ARTIFACT
    if path.exists():
        payload = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(payload, dict):
            return payload
    return a1.write_gap_head_attribution_v3(root=root)


def _project_payload(a1_payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    mechanism_case = _mapping(a1_payload.get("mechanism_case"))
    d5_o = _mapping(a1_payload.get("d5_o"))
    d5_m = _mapping(a1_payload.get("d5_m"))
    config = _mapping(a1_payload.get("config"))
    hardgates = _mapping(a1_payload.get("hardgates"))
    scope = _mapping(a1_payload.get("scope"))
    return {
        "artifact_id": ARTIFACT_ID,
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": REPORT_ARTIFACT,
        "generated_at": generated_at,
        "sidecar_role": "compatibility_projection",
        "canonical_source": {
            "artifact_id": a1.ARTIFACT_ID,
            "json_artifact": a1.CANONICAL_JSON_ARTIFACT,
            "markdown_artifact": a1.CANONICAL_MARKDOWN_ARTIFACT,
            "run_id": a1_payload.get("run_id"),
        },
        "mechanism_status": mechanism_case.get("status", "missing"),
        "D5_target": {
            "operational": dict(d5_o),
            "mechanism": dict(d5_m),
        },
        "config": {
            "arm_count": config.get("arm_count"),
            "arm_order": config.get("arm_order"),
        },
        "HG_A1": {
            "status": hardgates.get("status", "missing"),
            "source_pointer": f"{a1.CANONICAL_JSON_ARTIFACT}:$.hardgates",
        },
        "not_claimed": scope.get("not_claimed", []),
    }


def _render_report(payload: Mapping[str, Any]) -> str:
    return "\n".join(
        [
            "# Gap-Head Mechanism Attribution Projection",
            "",
            f"- Generated at: `{payload['generated_at']}`",
            f"- Sidecar role: `{payload['sidecar_role']}`",
            f"- Canonical source: `{payload['canonical_source']['json_artifact']}`",
            f"- Source run id: `{payload['canonical_source']['run_id']}`",
            f"- Mechanism status: `{payload['mechanism_status']}`",
            f"- A1 hardgate source: `{payload['HG_A1']['source_pointer']}`",
            "",
        ]
    )


def _write_payload(payload: Mapping[str, Any], root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def build_gap_head_mechanism_attribution(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    return _project_payload(_load_a1_payload(active_root), generated_at=timestamp)


def write_gap_head_mechanism_attribution(
    *,
    root: Path | str | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    active_root = ROOT if root is None else Path(root)
    payload = build_gap_head_mechanism_attribution(root=active_root, generated_at=generated_at)
    _write_payload(payload, active_root)
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Repository root for artifacts.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_gap_head_mechanism_attribution(root=args.root)
    print(f"wrote {payload['json_artifact']}")
    print(f"wrote {payload['markdown_artifact']}")
    print(f"canonical_source {payload['canonical_source']['json_artifact']}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Write deterministic run-local model-discovery artifacts."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.backends.model_discovery import (
    CLAIM_CAPSULE_ARTIFACT,
    DG_NAS_CANONICAL_ARTIFACT,
    RUN_ARTIFACT,
    RUN_MARKDOWN_ARTIFACT,
    ModelDiscoveryBackendEvidenceAdapter,
)
from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    build_architecture_claim_capsule_payload,
)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_markdown(path: Path, payload: Mapping[str, Any]) -> None:
    metadata = payload["projection_metadata"]
    lines = [
        "# Model discovery suite",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}`",
        f"- Capsule subtype: `{payload['claim_capsule_ref']['capsule_subtype']}`",
        f"- Canonical owner: `{payload['canonical_owner']['artifact']}`",
        f"- Canonical level candidate: `{metadata['canonical_level_candidate']}`",
        f"- Canonical failed gate: `{metadata['canonical_failed_gate']}`",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_claim_capsule(summary: Mapping[str, Any]) -> dict[str, Any]:
    model_claim = {
        "model_id": "discovery-gated-nas-canonical-projection",
        "claim": "The run-local model-discovery suite projects canonical discovery-gated NAS evidence by pointer.",
        "baselines": [
            {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.matched_baseline_control"},
        ],
        "forbidden_evidence": ["test_label", "ood_label", "ledger_verdict"],
        "required_gates": [f"DG-NAS-HG{index}" for index in range(1, 7)],
        "candidate_pointer": {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.candidate_protocol"},
        "evidence_pointer": {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"},
    }
    return build_architecture_claim_capsule_payload(
        generated_at=str(summary["generated_at"]),
        claim_id="claim:model-discovery-suite",
        report="model-discovery-suite",
        source_artifact=RUN_ARTIFACT,
        source_pointer="$.claim_capsule_ref",
        model_claim=model_claim,
        not_claimed=summary["not_claimed"],
    )


def build_run_payload(*, generated_at: str) -> tuple[dict[str, Any], dict[str, Any]]:
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    summary = dict(adapter.compute_metrics(root=ROOT, generated_at=generated_at))
    capsule = build_claim_capsule(summary)
    capsule["json_artifact"] = CLAIM_CAPSULE_ARTIFACT
    capsule["source_evidence"] = {
        "artifact": RUN_ARTIFACT,
        "pointer": "$.claim_capsule_ref",
        "capsule_subtype": summary["claim_capsule_ref"]["capsule_subtype"],
    }
    summary["claim_capsule_ref"] = {
        **dict(summary["claim_capsule_ref"]),
        "schema_id": capsule["schema_id"],
        "capsule_subtype": capsule["capsule_subtype"],
    }
    if capsule["capsule_subtype"] != ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE:
        raise ValueError("architecture claim capsule subtype mismatch")
    return summary, capsule


def write_run(*, root: Path, generated_at: str) -> dict[str, Path]:
    summary, capsule = build_run_payload(generated_at=generated_at)
    summary_path = root / RUN_ARTIFACT
    capsule_path = root / CLAIM_CAPSULE_ARTIFACT
    markdown_path = root / RUN_MARKDOWN_ARTIFACT
    _write_json(summary_path, summary)
    _write_json(capsule_path, capsule)
    _write_markdown(markdown_path, summary)
    return {"summary": summary_path, "claim_capsule": capsule_path, "markdown": markdown_path}


def _reusable_generated_at(root: Path) -> str | None:
    path = root / RUN_ARTIFACT
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at")
    args = parser.parse_args()
    generated_at = args.generated_at or _reusable_generated_at(args.root) or datetime.now(timezone.utc).isoformat()
    paths = write_run(root=args.root, generated_at=generated_at)
    for name, path in paths.items():
        print(f"wrote {name}: {path.relative_to(args.root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

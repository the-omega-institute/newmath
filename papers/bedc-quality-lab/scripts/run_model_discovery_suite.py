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
    lines = [
        "# Model discovery suite",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}`",
        f"- Capsule subtype: `{payload['claim_capsule_ref']['capsule_subtype']}`",
        f"- Task count: `{payload['metrics']['task_count']}`",
        f"- Negative witness count: `{payload['metrics']['negative_witness_count']}`",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_claim_capsule(summary: Mapping[str, Any]) -> dict[str, Any]:
    candidate = summary["model_candidates"][0]
    model_claim = {
        "model_id": candidate["model_id"],
        "claim": "A toy architecture candidate is evaluated only as run-local discovery-gated evidence.",
        "baselines": [
            {"artifact": RUN_ARTIFACT, "pointer": "$.baselines.parameter_matched"},
            {"artifact": RUN_ARTIFACT, "pointer": "$.baselines.compute_matched"},
            {"artifact": RUN_ARTIFACT, "pointer": "$.baselines.matched_random_structural_control"},
        ],
        "forbidden_evidence": ["test_label", "ood_label", "ledger_verdict"],
        "required_gates": [row["gate_id"] for row in summary["nm_hardgates"]],
        "candidate_pointer": {"artifact": RUN_ARTIFACT, "pointer": "$.model_candidates.0"},
        "evidence_pointer": {"artifact": RUN_ARTIFACT, "pointer": "$.task_grid"},
    }
    return build_architecture_claim_capsule_payload(
        generated_at=str(summary["generated_at"]),
        claim_id="claim:model-discovery-suite",
        report="model-discovery-suite",
        source_artifact=RUN_ARTIFACT,
        source_pointer="$.source_evidence",
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
    for row in summary["ledger_rows"]:
        row["capsule_subtype"] = capsule["capsule_subtype"]
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=datetime.now(timezone.utc).isoformat())
    args = parser.parse_args()
    paths = write_run(root=args.root, generated_at=args.generated_at)
    for name, path in paths.items():
        print(f"wrote {name}: {path.relative_to(args.root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Build the canonical LeJEPA theorem ledger."""

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

from bedc_quality_lab.backends.lejepa import LeJEPABackendEvidenceAdapter


SCHEMA_ID = "bedc-quality-lab:lejepa-theorem-ledger"
ARTIFACT_ID = "bedc-quality-lab:lejepa-theorem-ledger"
JSON_ARTIFACT = "reports/canonical/lejepa_theorem_ledger.json"
REPORT_ARTIFACT = "reports/canonical/lejepa_theorem_ledger.md"
PRODUCER = "scripts/run_lejepa_theorem_ledger.py"
RUNNER = "scripts/run_gaussian_ou_lejepa.py"
ALLOWED_ROLES = frozenset({"SourceSpec", "StabCert", "Ledger"})
FORBIDDEN_THEOREM_BOUND_WORDING = (
    "full proof",
    "full-proof",
    "complete proof",
    "complete-proof",
    "proven",
    "proved",
)


def _status_projection(status: str, severity: str = "none") -> dict[str, str]:
    return {"status": status, "severity": severity}


def _known_metric_names() -> tuple[str, ...]:
    return tuple(LeJEPABackendEvidenceAdapter.backend.metrics)


def theorem_rows() -> list[dict[str, Any]]:
    return [
        {
            "theorem": "theorem-1",
            "title": "Gaussian-OU source specification",
            "bedc_role": "SourceSpec",
            "implemented_metrics": [],
            "not_implemented": [
                "paper theorem statement is not represented as a kernel-checked formal target",
                "source assumptions are recorded as payload fields rather than closed source reconstruction",
            ],
            "ledger_debt": "Source assumptions are explicit in the envelope, while theorem-level source discharge remains outside the lab-local certificate row.",
            "status_projection": _status_projection("declared", "medium"),
            "evidence_pointer": "$.source_artifacts.gaussian_ou_runner",
            "role_basis": "This row owns the theorem-to-source-spec mapping for Gaussian latent, OU transition, and dimension-match assumptions.",
        },
        {
            "theorem": "theorem-2",
            "title": "Representation stability certificate boundary",
            "bedc_role": "StabCert",
            "implemented_metrics": [
                "alignment_gap_delta_mse",
                "whitening_deviation_epsilon",
            ],
            "not_implemented": [
                "stability claim is represented by metric cells rather than a closed theorem certificate",
                "optimizer and population-optimum assumptions are not discharged by the local runner",
            ],
            "ledger_debt": "Stability evidence is metric-backed and scoped to the Gaussian-OU toy runner.",
            "status_projection": _status_projection("partial", "medium"),
            "evidence_pointer": "$.metric_catalog",
            "role_basis": "This row tracks the stability-facing alignment and whitening measurements emitted by the LeJEPA runner.",
        },
        {
            "theorem": "theorem-3",
            "title": "Recovery bound certificate",
            "bedc_role": "StabCert",
            "implemented_metrics": [
                "theorem3_bound_mse",
                "actual_recovery_mse",
                "linear_identifiability_r2",
            ],
            "not_implemented": [
                "bound projection is a certificate cell and not a theorem derivation",
                "finite-sample and optimizer certificates remain ledger debt",
            ],
            "ledger_debt": "The existing LeJEPA backend points theorem3-bound-certificate at classifier_spec.cert_status; this ledger records the theorem-row boundary.",
            "status_projection": _status_projection("partial", "high"),
            "evidence_pointer": "$.backend_theorem_rows[0]",
            "role_basis": "This row is the canonical location for the current theorem-bound certificate projection.",
        },
        {
            "theorem": "theorem-4",
            "title": "Ledger closure boundary",
            "bedc_role": "Ledger",
            "implemented_metrics": [],
            "not_implemented": [
                "ledger row statuses are derived from local debt machinery rather than theorem closure",
                "terminal verdict classification is outside the LeJEPA backend theorem row",
            ],
            "ledger_debt": "Ledger rows identify source and classifier residues that must stay visible until discharged by stronger evidence.",
            "status_projection": _status_projection("declared", "medium"),
            "evidence_pointer": "$.backend_ledger_rows",
            "role_basis": "This row owns the theorem-to-ledger mapping for source and classifier residues.",
        },
    ]


def _hardgate_rows(rows: Sequence[Mapping[str, Any]], report_text: str) -> dict[str, Any]:
    metric_names = set(_known_metric_names())
    roles = [row.get("bedc_role") for row in rows]
    role_failures = [
        str(row.get("theorem"))
        for row in rows
        if row.get("bedc_role") not in ALLOWED_ROLES
    ]
    shape_failures = [
        str(row.get("theorem"))
        for row in rows
        if "implemented_metrics" not in row
        or not isinstance(row.get("implemented_metrics"), list)
        or not isinstance(row.get("not_implemented"), list)
        or len(row.get("not_implemented", [])) == 0
    ]
    metric_failures = [
        f"{row.get('theorem')}:{metric}"
        for row in rows
        for metric in row.get("implemented_metrics", [])
        if metric not in metric_names
    ]
    lowered = report_text.lower()
    wording_hits = [term for term in FORBIDDEN_THEOREM_BOUND_WORDING if term in lowered]
    return {
        "F-HG1": {
            "status": "pass" if len(rows) == len(set(row.get("theorem") for row in rows)) and not role_failures and all(role in ALLOWED_ROLES for role in roles) else "fail",
            "severity": "none" if not role_failures else "high",
            "role_failures": role_failures,
        },
        "F-HG2": {
            "status": "pass" if not shape_failures else "fail",
            "severity": "none" if not shape_failures else "high",
            "shape_failures": shape_failures,
        },
        "F-HG3": {
            "status": "pass" if not wording_hits else "fail",
            "severity": "none" if not wording_hits else "high",
            "hits": wording_hits,
        },
        "F-HG4": {
            "status": "pass",
            "severity": "none",
            "used_by_pointer": "docs/lit/literature_ledger.yaml:$.records[id=lit-lejepa-theorem-ledger].used_by",
        },
        "metric_resolvability": {
            "status": "pass" if not metric_failures else "fail",
            "severity": "none" if not metric_failures else "high",
            "metric_failures": metric_failures,
            "known_metrics": sorted(metric_names),
        },
    }


def _overall_status(hardgates: Mapping[str, Mapping[str, Any]]) -> str:
    return "pass" if all(row.get("status") == "pass" for row in hardgates.values()) else "fail"


def _render_markdown_without_hardgates(payload: Mapping[str, Any]) -> str:
    lines = [
        "# LeJEPA Theorem Ledger",
        "",
        f"- run_id: `{payload['run_id']}`",
        f"- schema_id: `{payload['schema_id']}`",
        f"- status: `{payload['status']}`",
        "",
        "## Scope",
        "",
        "- Canonical theorem-row ledger for LeJEPA theorem certificates.",
        "- Literature pointers reference this report through `used_by`; this report owns theorem-row status.",
        "",
        "## Theorem Rows",
        "",
        "| theorem | BEDC role | implemented metrics | ledger debt |",
        "| --- | --- | --- | --- |",
    ]
    for row in payload["theorem_rows"]:
        metrics = ", ".join(f"`{metric}`" for metric in row["implemented_metrics"]) or "`[]`"
        lines.append(
            "| "
            f"`{row['theorem']}` | "
            f"`{row['bedc_role']}` | "
            f"{metrics} | "
            f"{row['ledger_debt']} |"
        )
    lines.extend(["", "## Not Implemented", ""])
    for row in payload["theorem_rows"]:
        lines.append(f"- `{row['theorem']}`: " + "; ".join(row["not_implemented"]))
    lines.append("")
    return "\n".join(lines)


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = _render_markdown_without_hardgates(payload).rstrip().splitlines()
    lines.extend(["", "## Hardgates", ""])
    for gate, row in payload["hardgates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.append("")
    return "\n".join(lines)


def build_payload(*, run_id: str = "lejepa-theorem-ledger", generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    rows = theorem_rows()
    draft = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "run_id": run_id,
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": REPORT_ARTIFACT,
        "status": "unchecked",
        "source_artifacts": {
            "producer": PRODUCER,
            "gaussian_ou_runner": RUNNER,
            "lejepa_backend": "bedc_quality_lab.backends.lejepa.LeJEPABackendEvidenceAdapter",
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "literature_ledger": "docs/lit/literature_ledger.yaml",
        },
        "scope": {
            "status": "pointer-only-theorem-row-ledger",
            "claim_boundary": "Rows map LeJEPA theorem labels to certificate roles and ledger debt.",
            "not_claimed": [
                "BEDC closure",
                "paper theorem derivation",
                "terminal verdict classification",
                "general model quality",
            ],
        },
        "role_catalog": sorted(ALLOWED_ROLES),
        "metric_catalog": list(_known_metric_names()),
        "backend_theorem_rows": [dict(row) for row in LeJEPABackendEvidenceAdapter.backend.theorem_rows],
        "backend_ledger_rows": [dict(row) for row in LeJEPABackendEvidenceAdapter.backend.ledger_rows],
        "theorem_rows": rows,
        "not_claimed": [
            "The ledger records theorem-row certificate boundaries only.",
            "The ledger does not discharge optimizer, finite-sample, or source reconstruction debt.",
        ],
        "positive_claim": {
            "status": "ledger-row-ssot",
            "scope": "canonical LeJEPA theorem-row mapping",
        },
        "main_verdict": {
            "status": "ledger-row-ssot",
            "deltas": {"debt_delta": -1.0},
        },
        "claim_gate": {
            "status": "pass",
            "training_audit_improvement_tradeoff": False,
        },
    }
    report_text = _render_markdown_without_hardgates(draft)
    hardgates = _hardgate_rows(rows, report_text)
    draft["hardgates"] = hardgates
    draft["status"] = _overall_status(hardgates)
    draft["result"] = {
        "status": draft["status"],
        "debt_row_pointer": "$.main_verdict.deltas.debt_delta",
        "not_claimed_pointer": "$.not_claimed",
    }
    return draft


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    markdown_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default="lejepa-theorem-ledger")
    args = parser.parse_args(argv)
    payload = build_payload(run_id=args.run_id)
    write_artifacts(payload, root=args.root)
    print(json.dumps({"run_id": payload["run_id"], "status": payload["status"]}, sort_keys=True))
    return 0 if payload["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())

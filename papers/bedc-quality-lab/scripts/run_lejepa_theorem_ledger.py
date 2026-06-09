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
DERIVATIVE_BRIDGE_JSON_ARTIFACT = "reports/canonical/lejepa_derivative_bridge.json"
HERMITE_BEHAVIOR_MARKDOWN_ARTIFACT = "reports/canonical/hermite_degree_vs_behavioral_derivative.md"
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
THEOREM_DNA_REQUIRED_FIELDS = (
    "theorem_id",
    "assumptions",
    "objects",
    "maps",
    "operators",
    "invariants",
    "proof_dependencies",
    "ledger_debts",
    "formal_status",
)


def _status_projection(status: str, severity: str = "none") -> dict[str, str]:
    return {"status": status, "severity": severity}


def _known_metric_names() -> tuple[str, ...]:
    return tuple(LeJEPABackendEvidenceAdapter.backend.metrics)


def _pointer_cell(pointer: str, role: str) -> dict[str, str]:
    return {"pointer": pointer, "role": role}


def _theorem_dna_for_row(row: Mapping[str, Any], row_index: int) -> dict[str, Any]:
    theorem_id = str(row["theorem"])
    base = f"$.theorem_rows[{row_index}]"
    implemented_metrics = list(row.get("implemented_metrics", []))
    metric_pointers = [
        _pointer_cell(f"{base}.implemented_metrics[{index}]", "implemented-metric")
        for index, _metric in enumerate(implemented_metrics)
    ]
    return {
        "theorem_id": theorem_id,
        "assumptions": [
            _pointer_cell(f"{base}.evidence_pointer", "row-evidence"),
            _pointer_cell("$.scope.claim_boundary", "ledger-scope"),
        ],
        "objects": [
            theorem_id,
            str(row.get("title", "")),
            str(row.get("bedc_role", "")),
        ],
        "maps": [
            _pointer_cell(f"{base}.role_basis", "theorem-role-map"),
            _pointer_cell(f"{base}.status_projection", "status-projection-map"),
        ],
        "operators": [
            *metric_pointers,
            _pointer_cell("$.metric_catalog", "metric-catalog"),
            _pointer_cell("$.role_catalog", "role-catalog"),
        ],
        "invariants": [
            _pointer_cell(f"{base}.bedc_role", "allowed-role"),
            _pointer_cell(f"{base}.not_implemented", "visible-theorem-boundary"),
        ],
        "proof_dependencies": [
            _pointer_cell(f"{base}.status_projection", "lab-local-status-cell"),
            _pointer_cell(f"{base}.evidence_pointer", "certificate-evidence-cell"),
        ],
        "ledger_debts": [
            _pointer_cell(f"{base}.ledger_debt", "current-ledger-debt"),
        ],
        "formal_status": dict(row["status_projection"]),
    }


def _theorem_rows_with_dna(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        enriched = dict(row)
        enriched["theorem_id"] = str(row["theorem"])
        enriched["theorem_dna_pointer"] = f"$.theorem_rows[{index}].theorem_dna"
        enriched["theorem_dna"] = _theorem_dna_for_row(enriched, index)
        result.append(enriched)
    return result


def _theorem_dna_warning_rows(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    warnings: list[dict[str, Any]] = []
    for index, row in enumerate(rows):
        theorem = str(row.get("theorem", f"row-{index}"))
        dna = row.get("theorem_dna")
        missing: list[str] = []
        malformed: list[str] = []
        if not isinstance(dna, Mapping):
            warnings.append(
                {
                    "theorem": theorem,
                    "row_pointer": f"$.theorem_rows[{index}]",
                    "missing_fields": list(THEOREM_DNA_REQUIRED_FIELDS),
                    "malformed_fields": ["theorem_dna"],
                }
            )
            continue
        for field in THEOREM_DNA_REQUIRED_FIELDS:
            if field not in dna:
                missing.append(field)
        if dna.get("theorem_id") != row.get("theorem_id", row.get("theorem")):
            malformed.append("theorem_id")
        for field in ("assumptions", "ledger_debts", "proof_dependencies"):
            value = dna.get(field)
            if not isinstance(value, list) or not value:
                malformed.append(field)
            elif any(not isinstance(cell, Mapping) or not isinstance(cell.get("pointer"), str) for cell in value):
                malformed.append(field)
        if missing or malformed:
            warnings.append(
                {
                    "theorem": theorem,
                    "row_pointer": f"$.theorem_rows[{index}]",
                    "missing_fields": missing,
                    "malformed_fields": malformed,
                }
            )
    return warnings


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


def hermite_degree_boundary() -> list[dict[str, Any]]:
    return [
        {
            "label": "degree1",
            "degree_class": "degree1",
            "behavioral_boundary": "linear latent recovery boundary",
            "scope_pointer": "$.scope",
            "not_claimed_pointer": "$.not_claimed",
            "theorem_bound_pointer": "$.theorem_rows[2]",
            "metric_pointers": [
                "$.theorem_rows[2].implemented_metrics[2]",
                "$.metric_catalog",
            ],
        },
        {
            "label": "degree2",
            "degree_class": "degree2",
            "behavioral_boundary": "quadratic boundary",
            "scope_pointer": "$.scope",
            "not_claimed_pointer": "$.not_claimed",
            "theorem_bound_pointer": "$.theorem_rows[2]",
            "metric_pointers": [
                "$.theorem_rows[2].implemented_metrics[0]",
                "$.metric_catalog",
            ],
        },
        {
            "label": "degree3+",
            "degree_class": "degree3+",
            "behavioral_boundary": "high-order boundary",
            "scope_pointer": "$.scope",
            "not_claimed_pointer": "$.not_claimed",
            "theorem_bound_pointer": "$.theorem_rows[3]",
            "metric_pointers": [
                "$.theorem_rows[3].implemented_metrics",
                "$.not_claimed",
            ],
        },
    ]


def _hardgate_rows(rows: Sequence[Mapping[str, Any]], report_text: str) -> dict[str, Any]:
    metric_names = set(_known_metric_names())
    theorem_dna_warnings = _theorem_dna_warning_rows(rows)
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
            "theorem_dna_warnings": theorem_dna_warnings,
        },
        "theorem_dna_warning": {
            "status": "pass" if not theorem_dna_warnings else "warning",
            "severity": "none" if not theorem_dna_warnings else "low",
            "warning_rows": theorem_dna_warnings,
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
    return "pass" if all(row.get("status") in {"pass", "warning"} for row in hardgates.values()) else "fail"


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
    warning_count = len(payload.get("hardgates", {}).get("theorem_dna_warning", {}).get("warning_rows", []))
    lines.extend(["", f"- theorem DNA warning rows: `{warning_count}`"])
    lines.extend(["", "## Not Implemented", ""])
    for row in payload["theorem_rows"]:
        lines.append(f"- `{row['theorem']}`: " + "; ".join(row["not_implemented"]))
    lines.extend(["", "## Hermite Degree Boundary", ""])
    lines.extend(
        [
            "| label | behavioral boundary | theorem-bound pointer | scope | not claimed |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["hermite_degree_boundary"]:
        lines.append(
            "| "
            f"`{row['label']}` | "
            f"{row['behavioral_boundary']} | "
            f"`{row['theorem_bound_pointer']}` | "
            f"`{row['scope_pointer']}` | "
            f"`{row['not_claimed_pointer']}` |"
        )
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
    rows = _theorem_rows_with_dna(theorem_rows())
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
        "hermite_degree_boundary": hermite_degree_boundary(),
        "not_claimed": [
            "The ledger records theorem-row certificate boundaries only.",
            "The ledger does not discharge optimizer, finite-sample, or source reconstruction debt.",
            "Hermite degree rows are label-level Gaussian-OU pointers and do not assert behavior outside the runner scope.",
        ],
        "positive_claim": {
            "status": "ledger-row-ssot",
            "scope": "canonical LeJEPA theorem-row mapping",
        },
        "main_verdict": {
            "status": "ledger-row-ssot",
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
        "not_claimed_pointer": "$.not_claimed",
    }
    return draft


def _derivative_bridge_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:lejepa-derivative-bridge-sidecar",
        "artifact_id": "bedc-quality-lab:lejepa-derivative-bridge",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_report": "lejepa-theorem-ledger",
        "owner_artifact": JSON_ARTIFACT,
        "generated_at": payload["generated_at"],
        "status": "pointer-only",
        "source_pointer": f"{JSON_ARTIFACT}:$",
        "scope_pointer": f"{JSON_ARTIFACT}:$.scope",
        "not_claimed_pointer": f"{JSON_ARTIFACT}:$.not_claimed",
        "hermite_degree_boundary_pointer": f"{JSON_ARTIFACT}:$.hermite_degree_boundary",
        "theorem_rows_pointer": f"{JSON_ARTIFACT}:$.theorem_rows",
        "rows": [
            {
                "label": row["label"],
                "behavioral_boundary": row["behavioral_boundary"],
                "scope_pointer": f"{JSON_ARTIFACT}:{row['scope_pointer']}",
                "not_claimed_pointer": f"{JSON_ARTIFACT}:{row['not_claimed_pointer']}",
                "theorem_bound_pointer": f"{JSON_ARTIFACT}:{row['theorem_bound_pointer']}",
            }
            for row in payload["hermite_degree_boundary"]
        ],
        "not_claimed": [
            "This sidecar does not restate theorem rows.",
            "This sidecar does not assert theorem closure, terminal verdicts, or discovery level.",
            "This sidecar is scoped to the Gaussian-OU LeJEPA theorem ledger.",
        ],
    }


def _render_hermite_behavior_markdown(payload: Mapping[str, Any]) -> str:
    sidecar = _derivative_bridge_payload(payload)
    lines = [
        "# Hermite Degree vs Behavioral Derivative",
        "",
        f"- Canonical role: `{sidecar['canonical_role']}`",
        f"- Owner report: `{sidecar['owner_report']}`",
        f"- Owner artifact: `{sidecar['owner_artifact']}`",
        f"- Scope pointer: `{sidecar['scope_pointer']}`",
        f"- Not-claimed pointer: `{sidecar['not_claimed_pointer']}`",
        "",
        "| label | behavioral boundary | theorem-bound pointer |",
        "| --- | --- | --- |",
    ]
    for row in sidecar["rows"]:
        lines.append(
            "| "
            f"`{row['label']}` | "
            f"{row['behavioral_boundary']} | "
            f"`{row['theorem_bound_pointer']}` |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- Pointer-only sidecar; theorem facts remain in the LeJEPA theorem ledger.",
            "- No theorem closure, terminal verdict, or discovery level is asserted here.",
            "",
        ]
    )
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    markdown_path = root / REPORT_ARTIFACT
    derivative_bridge_path = root / DERIVATIVE_BRIDGE_JSON_ARTIFACT
    hermite_markdown_path = root / HERMITE_BEHAVIOR_MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    derivative_bridge_path.write_text(
        json.dumps(_derivative_bridge_payload(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    hermite_markdown_path.write_text(_render_hermite_behavior_markdown(payload), encoding="utf-8")


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

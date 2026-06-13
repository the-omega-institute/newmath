#!/usr/bin/env python3
"""LeWM autoresearch packet schemas and lightweight validators."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ID_PATTERN = r"^[a-z0-9][a-z0-9.:-]*$"
ID_RE = re.compile(ID_PATTERN)
VERDICT_STATUSES = {"positive", "negative", "fail-closed", "unidentifiable"}
ACCEPTANCE_STATUSES = {"passed", "blocked", "pending"}
PROVENANCE_VALUES = {"stub", "executed"}
CRITERION_KINDS = {"auroc_ci_separation", "uer_ci_separation", "delta_ci_below_zero", "delta_ci_above_zero", "manual"}


@dataclass(frozen=True)
class SchemaSpec:
    name: str
    required: set[str]


HYPOTHESIS_SCHEMA = SchemaSpec(
    "Hypothesis",
    {
        "hypothesis_id",
        "predicate",
        "failure_surface",
        "horizon",
        "perturbation_family",
        "carrier",
        "criterion",
        "reality_contact_refs",
        "status",
    },
)
EXPERIMENT_SCHEMA = SchemaSpec(
    "Experiment",
    {
        "experiment_id",
        "hypothesis_ref",
        "script_name",
        "input_data",
        "criterion",
        "predeclared_thresholds",
        "required_contacts",
        "status",
    },
)
REALITY_CONTACT_SCHEMA = SchemaSpec(
    "RealityContact",
    {
        "contact_id",
        "source_kind",
        "checkpoint",
        "export_ref",
        "can_measure",
        "cannot_measure",
        "frozen_fields",
        "notes",
    },
)
VERDICT_SCHEMA = SchemaSpec(
    "Verdict",
    {
        "verdict_id",
        "experiment_ref",
        "contact_ref",
        "status",
        "reported_claim",
        "provenance",
        "acceptance",
        "metrics",
        "ci",
        "anchoring",
        "replicate_group",
        "run_fingerprint",
        "measured_scope",
    },
)


def nowless_schema_names() -> list[str]:
    return [HYPOTHESIS_SCHEMA.name, EXPERIMENT_SCHEMA.name, REALITY_CONTACT_SCHEMA.name, VERDICT_SCHEMA.name]


def is_id(value: Any) -> bool:
    return isinstance(value, str) and ID_RE.match(value) is not None


def _missing(record: dict[str, Any], spec: SchemaSpec) -> list[str]:
    return [f"missing required field: {field}" for field in sorted(spec.required - set(record))]


def _require_id(field: str, record: dict[str, Any], issues: list[str]) -> None:
    value = record.get(field)
    if not is_id(value):
        issues.append(f"{field} must match {ID_PATTERN}")


def _require_nonempty(field: str, record: dict[str, Any], issues: list[str]) -> None:
    if not isinstance(record.get(field), str) or not str(record.get(field)).strip():
        issues.append(f"{field} must be a nonempty string")


def _require_list(field: str, record: dict[str, Any], issues: list[str], *, min_items: int = 0) -> list[Any]:
    value = record.get(field)
    if not isinstance(value, list):
        issues.append(f"{field} must be an array")
        return []
    if len(value) < min_items:
        issues.append(f"{field} must contain at least {min_items} item(s)")
    return value


def validate_hypothesis(record: dict[str, Any]) -> list[str]:
    issues = _missing(record, HYPOTHESIS_SCHEMA)
    if issues:
        return issues
    _require_id("hypothesis_id", record, issues)
    for field in ("predicate", "failure_surface", "perturbation_family", "carrier", "status"):
        _require_nonempty(field, record, issues)
    horizon = record.get("horizon")
    if not isinstance(horizon, dict) or not horizon:
        issues.append("horizon must be a nonempty object")
    if not isinstance(record.get("criterion"), dict) or not record.get("criterion"):
        issues.append("criterion must be a nonempty object")
    refs = _require_list("reality_contact_refs", record, issues)
    for ref in refs:
        if not is_id(ref):
            issues.append(f"reality_contact_refs item must match {ID_PATTERN}: {ref}")
    return issues


def validate_experiment(record: dict[str, Any], hypothesis_ids: set[str] | None = None) -> list[str]:
    issues = _missing(record, EXPERIMENT_SCHEMA)
    if issues:
        return issues
    _require_id("experiment_id", record, issues)
    _require_id("hypothesis_ref", record, issues)
    if hypothesis_ids is not None and is_id(record.get("hypothesis_ref")) and record["hypothesis_ref"] not in hypothesis_ids:
        issues.append(f"hypothesis_ref not found: {record['hypothesis_ref']}")
    for field in ("script_name", "status"):
        _require_nonempty(field, record, issues)
    if not isinstance(record.get("input_data"), list):
        issues.append("input_data must be an array")
    criterion = record.get("criterion")
    if not isinstance(criterion, dict) or criterion.get("kind") not in CRITERION_KINDS:
        issues.append(f"criterion.kind must be one of {sorted(CRITERION_KINDS)}")
    if not isinstance(record.get("predeclared_thresholds"), dict):
        issues.append("predeclared_thresholds must be an object")
    _require_list("required_contacts", record, issues)
    return issues


def validate_contact(record: dict[str, Any]) -> list[str]:
    issues = _missing(record, REALITY_CONTACT_SCHEMA)
    if issues:
        return issues
    _require_id("contact_id", record, issues)
    for field in ("source_kind", "checkpoint", "export_ref"):
        _require_nonempty(field, record, issues)
    _require_list("can_measure", record, issues, min_items=1)
    _require_list("cannot_measure", record, issues)
    if not isinstance(record.get("frozen_fields"), dict):
        issues.append("frozen_fields must be an object of field -> frozen numeric value")
    return issues


def validate_verdict(record: dict[str, Any], experiment_ids: set[str] | None = None, contact_ids: set[str] | None = None) -> list[str]:
    issues = _missing(record, VERDICT_SCHEMA)
    if issues:
        return issues
    _require_id("verdict_id", record, issues)
    _require_id("experiment_ref", record, issues)
    _require_id("contact_ref", record, issues)
    if experiment_ids is not None and is_id(record.get("experiment_ref")) and record["experiment_ref"] not in experiment_ids:
        issues.append(f"experiment_ref not found: {record['experiment_ref']}")
    if contact_ids is not None and is_id(record.get("contact_ref")) and record["contact_ref"] not in contact_ids:
        issues.append(f"contact_ref not found: {record['contact_ref']}")
    if record.get("status") not in VERDICT_STATUSES:
        issues.append(f"status must be one of {sorted(VERDICT_STATUSES)}")
    if record.get("provenance") not in PROVENANCE_VALUES:
        issues.append(f"provenance must be one of {sorted(PROVENANCE_VALUES)}")
    acceptance = record.get("acceptance")
    if not isinstance(acceptance, dict):
        issues.append("acceptance must be an object")
    elif acceptance.get("status") not in ACCEPTANCE_STATUSES:
        issues.append(f"acceptance.status must be one of {sorted(ACCEPTANCE_STATUSES)}")
    for field in ("metrics", "ci", "anchoring"):
        if not isinstance(record.get(field), dict):
            issues.append(f"{field} must be an object")
    _require_nonempty("reported_claim", record, issues)
    _require_nonempty("replicate_group", record, issues)
    _require_nonempty("run_fingerprint", record, issues)
    _require_list("measured_scope", record, issues, min_items=1)
    return issues


def validate_all(
    hypotheses: list[dict[str, Any]],
    experiments: list[dict[str, Any]],
    contacts: list[dict[str, Any]],
    verdicts: list[dict[str, Any]],
) -> dict[str, list[dict[str, Any]]]:
    hypothesis_ids = {str(item.get("hypothesis_id")) for item in hypotheses if is_id(item.get("hypothesis_id"))}
    experiment_ids = {str(item.get("experiment_id")) for item in experiments if is_id(item.get("experiment_id"))}
    contact_ids = {str(item.get("contact_id")) for item in contacts if is_id(item.get("contact_id"))}
    return {
        "hypotheses": [{"id": item.get("hypothesis_id", f"row-{i}"), "issues": validate_hypothesis(item)} for i, item in enumerate(hypotheses, 1)],
        "experiments": [{"id": item.get("experiment_id", f"row-{i}"), "issues": validate_experiment(item, hypothesis_ids)} for i, item in enumerate(experiments, 1)],
        "contacts": [{"id": item.get("contact_id", f"row-{i}"), "issues": validate_contact(item)} for i, item in enumerate(contacts, 1)],
        "verdicts": [{"id": item.get("verdict_id", f"row-{i}"), "issues": validate_verdict(item, experiment_ids, contact_ids)} for i, item in enumerate(verdicts, 1)],
    }


def self_test() -> int:
    hypothesis = {
        "hypothesis_id": "fi-001.cvar-tail",
        "predicate": "CVaR tail objective reduces allocation harm.",
        "failure_surface": "allocation delta CI",
        "horizon": {"steps": [1, 4, 8]},
        "perturbation_family": "tail-risk weighting",
        "carrier": "pusht checkpoint export",
        "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
        "reality_contact_refs": ["pusht.phase2c.export"],
        "status": "open",
    }
    experiment = {
        "experiment_id": "exp.fi-001.cvar-tail",
        "hypothesis_ref": "fi-001.cvar-tail",
        "script_name": "_phase2c_ood_aware_gap.py",
        "input_data": ["pusht_latent_large.npz"],
        "criterion": {"kind": "delta_ci_below_zero", "metric": "allocation_delta"},
        "predeclared_thresholds": {"alpha": 0.05},
        "required_contacts": ["pusht.phase2c.export"],
        "status": "planned",
    }
    contact = {
        "contact_id": "pusht.phase2c.export",
        "source_kind": "checkpoint-export",
        "checkpoint": "pusht_latent_large.npz",
        "export_ref": "_phase2c_full_run.log",
        "can_measure": ["allocation_delta", "uer", "auroc"],
        "cannot_measure": ["real_robot_transfer"],
        "frozen_fields": {"anchor.metric": 0.123},
        "notes": "fixture",
    }
    verdict = {
        "verdict_id": "verdict.fi-001.cvar-tail.a",
        "experiment_ref": "exp.fi-001.cvar-tail",
        "contact_ref": "pusht.phase2c.export",
        "status": "positive",
        "reported_claim": "allocation_delta < 0",
        "provenance": "executed",
        "acceptance": {"status": "pending"},
        "metrics": {"anchor.metric": 0.123, "allocation_delta": -0.02},
        "ci": {"allocation_delta": {"low": -0.04, "high": -0.01}},
        "anchoring": {"anchor.metric": 0.123},
        "replicate_group": "rg.fixture",
        "run_fingerprint": "abc",
        "measured_scope": ["allocation_delta"],
    }
    results = validate_all([hypothesis], [experiment], [contact], [verdict])
    if any(row["issues"] for rows in results.values() for row in rows):
        print(json.dumps(results, indent=2))
        return 1
    print("[lewm-schemas] self-test ok")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="LeWM autoresearch schemas")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    print(json.dumps({"schemas": nowless_schema_names(), "id_pattern": ID_PATTERN}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

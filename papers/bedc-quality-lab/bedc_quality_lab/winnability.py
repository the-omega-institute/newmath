"""Winnability certificates for bounded lab split evidence."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
from typing import Any, Callable, Mapping, Protocol, Sequence


SCHEMA_ID = "bedc-quality-lab:winnability-certificates"
ARTIFACT_ID = "bedc-quality-lab:winnability-certificates"
PRODUCER = "scripts/run_winnability_certificates.py"
OWNER = "bedc_quality_lab.winnability"
JSON_ARTIFACT = "reports/canonical/winnability-certificates.json"
MARKDOWN_ARTIFACT = "reports/canonical/winnability-certificates.md"
INPUT_ACCESSIBILITY_ARTIFACT = "reports/canonical/input-accessibility.json"
DGT_L0_CONTROLS_ARTIFACT = "reports/canonical/dgt-l0-controls.json"
DGT_L1_CONTROLS_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
METHODS = frozenset({"analytic_bayes", "oracle_arm", "unresolved"})
STATUSES = frozenset({"pass", "fail"})
COVERAGE_CLASSIFICATIONS = frozenset(
    {"not-applicable", "table-coverage", "not-table-coverage", "unresolved"}
)
HARDGATE_IDS = ("ORACLE-HG1", "ORACLE-HG2", "ORACLE-HG3", "ORACLE-HG4", "ORACLE-HG5")
IDENTITY_FIELDS = (
    "experiment_id",
    "task_id",
    "split_id",
    "split_fingerprint",
    "label_function_ref",
    "visible_variables_ref",
    "required_variables_ref",
)
CERTIFICATE_REQUIRED_KEYS = (
    "row_id",
    "experiment_id",
    "task_id",
    "task_family",
    "split_id",
    "split_kind",
    "split_fingerprint",
    "source_evidence_ref",
    "label_function_ref",
    "visible_variables_ref",
    "required_variables_ref",
    "method",
    "derivation_ref",
    "oracle_run_ref",
    "chance_accuracy",
    "upper_bound_accuracy",
    "observed_accuracy",
    "epsilon",
    "winnable",
    "unwinnable",
    "coverage",
    "claim_permissions",
    "status",
    "failure_reasons",
    "not_claimed",
)
CLAIM_PERMISSION_KEYS = (
    "memorization_claim_allowed",
    "generalization_claim_allowed",
    "separation_claim_allowed",
    "architecture_claim_allowed",
    "rule_abstraction_claim_allowed",
)
COVERAGE_KEYS = (
    "train_pair_coverage",
    "seen_accuracy",
    "unseen_accuracy",
    "coverage_ceiling",
    "coverage_gap",
    "coverage_tolerance",
    "coverage_classification",
)
NOT_CLAIMED = (
    "Winnability certificates bound finite lab split evidence only.",
    "No oracle training is performed by this producer.",
    "A table-coverage certificate does not authorize generalization or rule-abstraction claims.",
    "An unresolved or unwinnable split remains barred from positive claim use.",
)


class WinnabilityResolver(Protocol):
    def __call__(
        self,
        split_evidence: Mapping[str, Any],
        *,
        input_accessibility: Mapping[str, Any] | None = None,
        oracle_runs: Sequence[Mapping[str, Any]] = (),
    ) -> Mapping[str, Any]:
        ...


@dataclass(frozen=True)
class WinnabilityCertificate:
    row_id: str
    experiment_id: str
    task_id: str
    task_family: str
    split_id: str
    split_kind: str
    split_fingerprint: str
    source_evidence_ref: str
    label_function_ref: str
    visible_variables_ref: str
    required_variables_ref: str
    method: str
    derivation_ref: str | None
    oracle_run_ref: str | None
    chance_accuracy: float
    upper_bound_accuracy: float
    observed_accuracy: float | None
    epsilon: float
    winnable: bool
    unwinnable: bool
    coverage: Mapping[str, Any]
    claim_permissions: Mapping[str, bool]
    status: str
    failure_reasons: Sequence[str]
    not_claimed: Sequence[str]

    def to_json(self) -> dict[str, Any]:
        return {
            "row_id": self.row_id,
            "experiment_id": self.experiment_id,
            "task_id": self.task_id,
            "task_family": self.task_family,
            "split_id": self.split_id,
            "split_kind": self.split_kind,
            "split_fingerprint": self.split_fingerprint,
            "source_evidence_ref": self.source_evidence_ref,
            "label_function_ref": self.label_function_ref,
            "visible_variables_ref": self.visible_variables_ref,
            "required_variables_ref": self.required_variables_ref,
            "method": self.method,
            "derivation_ref": self.derivation_ref,
            "oracle_run_ref": self.oracle_run_ref,
            "chance_accuracy": self.chance_accuracy,
            "upper_bound_accuracy": self.upper_bound_accuracy,
            "observed_accuracy": self.observed_accuracy,
            "epsilon": self.epsilon,
            "winnable": self.winnable,
            "unwinnable": self.unwinnable,
            "coverage": dict(self.coverage),
            "claim_permissions": dict(self.claim_permissions),
            "status": self.status,
            "failure_reasons": list(self.failure_reasons),
            "not_claimed": list(self.not_claimed),
        }


class WinnabilityRegistry:
    def __init__(self) -> None:
        self._resolvers: dict[str, WinnabilityResolver] = {}

    def register_family(self, family_id: str, resolver: WinnabilityResolver) -> "WinnabilityRegistry":
        if not family_id:
            raise ValueError("family_id must be non-empty")
        self._resolvers[family_id] = resolver
        return self

    def resolver_for(self, family_id: str) -> WinnabilityResolver | None:
        return self._resolvers.get(family_id)

    def family_registry(self) -> list[dict[str, str]]:
        rows = []
        for family_id, resolver in sorted(self._resolvers.items()):
            resolver_name = getattr(resolver, "__name__", resolver.__class__.__name__)
            rows.append(
                {
                    "family_id": family_id,
                    "resolver": resolver_name,
                    "metadata_only": "true",
                }
            )
        return rows


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _as_float(value: Any, default: float | None = None) -> float | None:
    if isinstance(value, bool):
        return default
    if isinstance(value, (int, float)):
        return float(value)
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _round(value: float | None) -> float | None:
    return None if value is None else round(value, 6)


def _pointer_value(payload: Any, pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        return None
    cursor = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        elif isinstance(cursor, Sequence) and not isinstance(cursor, (str, bytes)) and part.isdigit():
            index = int(part)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
        else:
            return None
    return cursor


def _load_json(root: Path, artifact: str) -> dict[str, Any] | None:
    path = root / artifact
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def row_id_for_split(split_evidence: Mapping[str, Any]) -> str:
    seed = "|".join(str(split_evidence.get(field, "")) for field in IDENTITY_FIELDS)
    return "win-" + hashlib.sha256(seed.encode("utf-8")).hexdigest()[:16]


def compact_winnability_ref(
    row_id: str,
    *,
    artifact: str = JSON_ARTIFACT,
) -> dict[str, str]:
    return {
        "artifact": artifact,
        "row_id": row_id,
        "pointer": f"{artifact}:$.certificates[?row_id=='{row_id}']",
    }


def _default_coverage(classification: str = "not-applicable") -> dict[str, Any]:
    return {
        "train_pair_coverage": None,
        "seen_accuracy": None,
        "unseen_accuracy": None,
        "coverage_ceiling": None,
        "coverage_gap": None,
        "coverage_tolerance": None,
        "coverage_classification": classification,
    }


def finite_table_ceiling(
    train_pairs: Sequence[Any] | int,
    eval_pairs: Sequence[Any] | int,
    label_cardinality: int,
    *,
    unseen_policy: str = "chance",
) -> dict[str, Any]:
    if label_cardinality <= 0:
        raise ValueError("label_cardinality must be positive")
    train_count = train_pairs if isinstance(train_pairs, int) else len(train_pairs)
    eval_count = eval_pairs if isinstance(eval_pairs, int) else len(eval_pairs)
    if train_count < 0 or eval_count <= 0:
        raise ValueError("pair counts must be nonnegative with a positive eval count")
    draws_per_eval_pair = train_count / eval_count
    seen_probability = 1.0 - math.exp(-draws_per_eval_pair)
    unseen_accuracy = 1.0 / label_cardinality if unseen_policy == "chance" else 0.0
    coverage_ceiling = seen_probability + (1.0 - seen_probability) * unseen_accuracy
    return {
        "train_pair_coverage": _round(seen_probability),
        "seen_accuracy": 1.0,
        "unseen_accuracy": _round(unseen_accuracy),
        "coverage_ceiling": _round(min(1.0, coverage_ceiling)),
        "coverage_gap": None,
        "coverage_tolerance": 0.01,
        "coverage_classification": "table-coverage",
    }


def _variables_from_accessibility(
    split_evidence: Mapping[str, Any],
    input_accessibility: Mapping[str, Any] | None,
    key: str,
) -> tuple[str, ...]:
    direct = split_evidence.get(key)
    if isinstance(direct, Sequence) and not isinstance(direct, (str, bytes)):
        return tuple(str(item) for item in direct)
    if not isinstance(input_accessibility, Mapping):
        return ()
    candidates = (
        split_evidence.get("row_id"),
        split_evidence.get("split_id"),
        split_evidence.get("task_id"),
    )
    for candidate in candidates:
        if not isinstance(candidate, str):
            continue
        row = input_accessibility.get(candidate)
        if isinstance(row, Mapping):
            value = row.get(key)
            if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
                return tuple(str(item) for item in value)
    rows = input_accessibility.get("rows")
    if isinstance(rows, Sequence) and not isinstance(rows, (str, bytes)):
        for row in rows:
            if not isinstance(row, Mapping):
                continue
            if row.get("split_id") == split_evidence.get("split_id"):
                value = row.get(key)
                if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
                    return tuple(str(item) for item in value)
    return ()


def _coverage_for_split(split_evidence: Mapping[str, Any], observed_accuracy: float | None) -> dict[str, Any]:
    label_cardinality = split_evidence.get("label_cardinality")
    train_pairs = split_evidence.get("train_pairs")
    eval_pairs = split_evidence.get("eval_pairs")
    if train_pairs is None:
        train_pairs = split_evidence.get("train_pair_count")
    if eval_pairs is None:
        eval_pairs = split_evidence.get("eval_pair_count")
    if not isinstance(label_cardinality, int) or label_cardinality <= 0:
        return _default_coverage()
    if train_pairs is None or eval_pairs is None:
        return _default_coverage()
    coverage = finite_table_ceiling(train_pairs, eval_pairs, label_cardinality)
    ceiling = _as_float(coverage["coverage_ceiling"])
    tolerance = _as_float(coverage["coverage_tolerance"], 0.01) or 0.01
    if observed_accuracy is not None and ceiling is not None:
        coverage["coverage_gap"] = _round(observed_accuracy - ceiling)
        if abs(observed_accuracy - ceiling) > tolerance:
            coverage["coverage_classification"] = "not-table-coverage"
    return coverage


def analytic_visibility_resolver(
    split_evidence: Mapping[str, Any],
    *,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> Mapping[str, Any]:
    del oracle_runs
    chance = _as_float(split_evidence.get("chance_accuracy"), 0.0) or 0.0
    observed = _as_float(split_evidence.get("observed_accuracy"))
    visible = set(_variables_from_accessibility(split_evidence, input_accessibility, "visible_variables"))
    required = set(_variables_from_accessibility(split_evidence, input_accessibility, "required_variables"))
    missing = sorted(required - visible)
    if missing:
        return {
            "method": "analytic_bayes",
            "derivation_ref": split_evidence.get("derivation_ref") or "bedc_quality_lab.winnability:analytic_visibility_resolver",
            "upper_bound_accuracy": chance,
            "failure_reasons": [f"hidden-required-variable:{name}" for name in missing],
            "coverage": _default_coverage(),
        }
    coverage = _coverage_for_split(split_evidence, observed)
    upper_bound = coverage.get("coverage_ceiling") if coverage["coverage_classification"] in {
        "table-coverage",
        "not-table-coverage",
    } else 1.0
    return {
        "method": "analytic_bayes",
        "derivation_ref": split_evidence.get("derivation_ref") or "bedc_quality_lab.winnability:analytic_visibility_resolver",
        "upper_bound_accuracy": upper_bound,
        "failure_reasons": [],
        "coverage": coverage,
    }


def unresolved_resolver(
    split_evidence: Mapping[str, Any],
    *,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> Mapping[str, Any]:
    del split_evidence, input_accessibility, oracle_runs
    return {
        "method": "unresolved",
        "derivation_ref": None,
        "upper_bound_accuracy": 0.0,
        "failure_reasons": ["resolver-unresolved"],
        "coverage": _default_coverage("unresolved"),
    }


def oracle_arm_resolver(
    split_evidence: Mapping[str, Any],
    *,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> Mapping[str, Any]:
    del input_accessibility, oracle_runs
    return {
        "method": "oracle_arm",
        "derivation_ref": split_evidence.get("derivation_ref"),
        "oracle_run_ref": split_evidence.get("oracle_run_ref"),
        "upper_bound_accuracy": split_evidence.get("upper_bound_accuracy"),
        "failure_reasons": [],
        "coverage": _default_coverage(),
    }


DEFAULT_REGISTRY = WinnabilityRegistry()
DEFAULT_REGISTRY.register_family("analytic-visibility", analytic_visibility_resolver)
DEFAULT_REGISTRY.register_family("analytic-table-coverage", analytic_visibility_resolver)
DEFAULT_REGISTRY.register_family("oracle-arm", oracle_arm_resolver)
DEFAULT_REGISTRY.register_family("unresolved", unresolved_resolver)


def register_family(family_id: str, resolver: WinnabilityResolver) -> WinnabilityRegistry:
    return DEFAULT_REGISTRY.register_family(family_id, resolver)


def _claim_permissions(*, status: str, winnable: bool, classification: str) -> dict[str, bool]:
    table_coverage = classification == "table-coverage"
    broad_allowed = status == "pass" and winnable and not table_coverage
    return {
        "memorization_claim_allowed": status == "pass" and winnable,
        "generalization_claim_allowed": broad_allowed,
        "separation_claim_allowed": broad_allowed,
        "architecture_claim_allowed": broad_allowed,
        "rule_abstraction_claim_allowed": broad_allowed,
    }


def _oracle_row_for_ref(
    oracle_run_ref: str | None,
    oracle_runs: Sequence[Mapping[str, Any]],
) -> Mapping[str, Any] | None:
    if not oracle_run_ref:
        return None
    for row in oracle_runs:
        if row.get("oracle_run_ref") == oracle_run_ref:
            return row
        artifact = row.get("artifact")
        pointer = row.get("pointer")
        if isinstance(artifact, str) and isinstance(pointer, str) and f"{artifact}:{pointer}" == oracle_run_ref:
            return row
    return None


def _oracle_failure_reasons(
    certificate: Mapping[str, Any],
    oracle_runs: Sequence[Mapping[str, Any]],
) -> list[str]:
    if certificate.get("method") != "oracle_arm":
        return []
    row = _oracle_row_for_ref(
        certificate.get("oracle_run_ref") if isinstance(certificate.get("oracle_run_ref"), str) else None,
        oracle_runs,
    )
    if row is None:
        return ["invalid-oracle-run-ref"]
    required = ("artifact", "metric_pointer", "split_fingerprint", "model_id", "seed", "measured_accuracy")
    missing = [field for field in required if field not in row or row[field] in (None, "")]
    if missing:
        return [f"invalid-oracle-run-ref:{field}" for field in missing]
    if row.get("split_fingerprint") != certificate.get("split_fingerprint"):
        return ["invalid-oracle-run-ref:split-fingerprint"]
    if _as_float(row.get("measured_accuracy")) is None:
        return ["invalid-oracle-run-ref:measured-accuracy"]
    return []


def evaluate_split(
    split_evidence: Mapping[str, Any],
    *,
    registry: WinnabilityRegistry | None = None,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> WinnabilityCertificate:
    active_registry = registry or DEFAULT_REGISTRY
    family_id = str(split_evidence.get("resolver_family") or split_evidence.get("task_family") or "unresolved")
    resolver = active_registry.resolver_for(family_id) or active_registry.resolver_for("unresolved")
    assert resolver is not None
    result = resolver(split_evidence, input_accessibility=input_accessibility, oracle_runs=oracle_runs)
    method = str(result.get("method") or "unresolved")
    if method not in METHODS:
        method = "unresolved"
    chance = _as_float(split_evidence.get("chance_accuracy"), 0.0) or 0.0
    observed = _as_float(split_evidence.get("observed_accuracy"))
    upper = _as_float(result.get("upper_bound_accuracy"), chance)
    if upper is None:
        upper = chance
    epsilon = _as_float(split_evidence.get("epsilon"), 1e-9) or 1e-9
    coverage = dict(result.get("coverage")) if isinstance(result.get("coverage"), Mapping) else _default_coverage()
    for key, value in _default_coverage().items():
        coverage.setdefault(key, value)
    classification = str(coverage.get("coverage_classification") or "unresolved")
    if classification not in COVERAGE_CLASSIFICATIONS:
        classification = "unresolved"
        coverage["coverage_classification"] = classification
    failure_reasons = [
        str(reason)
        for reason in result.get("failure_reasons", [])
        if isinstance(reason, str) and reason
    ]
    status = "pass"
    if method == "unresolved":
        status = "fail"
        if "resolver-unresolved" not in failure_reasons:
            failure_reasons.append("resolver-unresolved")
    if method == "oracle_arm":
        oracle_failures = _oracle_failure_reasons(
            {
                "method": method,
                "oracle_run_ref": result.get("oracle_run_ref"),
                "split_fingerprint": split_evidence.get("split_fingerprint"),
            },
            oracle_runs,
        )
        if oracle_failures:
            status = "fail"
            failure_reasons.extend(oracle_failures)
    if not (0.0 <= chance <= upper <= 1.0):
        status = "fail"
        failure_reasons.append("invalid-bounds")
    if observed is not None and not (0.0 <= observed <= 1.0):
        status = "fail"
        failure_reasons.append("invalid-observed-accuracy")
    winnable = status == "pass" and upper > chance + epsilon
    unwinnable = status == "pass" and upper <= chance + epsilon
    permissions = _claim_permissions(status=status, winnable=winnable, classification=classification)
    return WinnabilityCertificate(
        row_id=row_id_for_split(split_evidence),
        experiment_id=str(split_evidence.get("experiment_id") or ""),
        task_id=str(split_evidence.get("task_id") or ""),
        task_family=str(split_evidence.get("task_family") or ""),
        split_id=str(split_evidence.get("split_id") or ""),
        split_kind=str(split_evidence.get("split_kind") or ""),
        split_fingerprint=str(split_evidence.get("split_fingerprint") or ""),
        source_evidence_ref=str(split_evidence.get("source_evidence_ref") or ""),
        label_function_ref=str(split_evidence.get("label_function_ref") or ""),
        visible_variables_ref=str(split_evidence.get("visible_variables_ref") or ""),
        required_variables_ref=str(split_evidence.get("required_variables_ref") or ""),
        method=method,
        derivation_ref=result.get("derivation_ref") if isinstance(result.get("derivation_ref"), str) else None,
        oracle_run_ref=result.get("oracle_run_ref") if isinstance(result.get("oracle_run_ref"), str) else None,
        chance_accuracy=_round(chance) or 0.0,
        upper_bound_accuracy=_round(upper) or 0.0,
        observed_accuracy=_round(observed),
        epsilon=epsilon,
        winnable=winnable,
        unwinnable=unwinnable,
        coverage=coverage,
        claim_permissions=permissions,
        status=status,
        failure_reasons=tuple(dict.fromkeys(failure_reasons)),
        not_claimed=tuple(split_evidence.get("not_claimed") or NOT_CLAIMED),
    )


def evaluate_winnability(
    split_evidence_rows: Sequence[Mapping[str, Any]],
    *,
    registry: WinnabilityRegistry | None = None,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> list[dict[str, Any]]:
    return [
        evaluate_split(
            row,
            registry=registry,
            input_accessibility=input_accessibility,
            oracle_runs=oracle_runs,
        ).to_json()
        for row in split_evidence_rows
    ]


def _certificate_malformed(row: Mapping[str, Any]) -> list[str]:
    failures = []
    if "certificate_id" in row:
        failures.append("forbidden-certificate-id-alias")
    missing = [key for key in CERTIFICATE_REQUIRED_KEYS if key not in row]
    failures.extend(f"missing-key:{key}" for key in missing)
    method = row.get("method")
    status = row.get("status")
    if method not in METHODS:
        failures.append("invalid-method")
    if status not in STATUSES:
        failures.append("invalid-status")
    coverage = row.get("coverage")
    if not isinstance(coverage, Mapping):
        failures.append("invalid-coverage")
    else:
        missing_coverage = [key for key in COVERAGE_KEYS if key not in coverage]
        failures.extend(f"missing-coverage-key:{key}" for key in missing_coverage)
        if coverage.get("coverage_classification") not in COVERAGE_CLASSIFICATIONS:
            failures.append("invalid-coverage-classification")
    permissions = row.get("claim_permissions")
    if not isinstance(permissions, Mapping):
        failures.append("invalid-claim-permissions")
    else:
        missing_permissions = [key for key in CLAIM_PERMISSION_KEYS if key not in permissions]
        failures.extend(f"missing-claim-permission:{key}" for key in missing_permissions)
    chance = _as_float(row.get("chance_accuracy"))
    upper = _as_float(row.get("upper_bound_accuracy"))
    observed = _as_float(row.get("observed_accuracy"))
    if chance is None or upper is None or not (0.0 <= chance <= upper <= 1.0):
        failures.append("invalid-bounds")
    if row.get("observed_accuracy") is not None and (observed is None or not (0.0 <= observed <= 1.0)):
        failures.append("invalid-observed-accuracy")
    if row.get("method") == "analytic_bayes" and not isinstance(row.get("derivation_ref"), str):
        failures.append("bad-derivation")
    return failures


def audit_certificates(
    registered_splits: Sequence[Mapping[str, Any]],
    certificates: Sequence[Mapping[str, Any]],
    *,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> dict[str, Any]:
    expected_ids = [row_id_for_split(row) for row in registered_splits]
    by_id: dict[str, list[Mapping[str, Any]]] = {}
    for row in certificates:
        row_id = row.get("row_id")
        if isinstance(row_id, str):
            by_id.setdefault(row_id, []).append(row)
    missing_ids = [row_id for row_id in expected_ids if row_id not in by_id]
    duplicate_ids = [row_id for row_id, rows in by_id.items() if len(rows) > 1]
    failures: list[dict[str, Any]] = []
    failed_count = len(missing_ids) + sum(len(by_id[row_id]) - 1 for row_id in duplicate_ids)
    fail_closed_count = failed_count
    unresolved_count = 0
    unwinnable_count = 0
    table_coverage_count = 0
    for row_id in missing_ids:
        failures.append({"row_id": row_id, "reason": "missing-certificate"})
    for row_id in duplicate_ids:
        failures.append({"row_id": row_id, "reason": "duplicate-certificate"})
    for row in certificates:
        row_id = row.get("row_id") if isinstance(row.get("row_id"), str) else "missing-row-id"
        row_failures = _certificate_malformed(row)
        row_failures.extend(_oracle_failure_reasons(row, oracle_runs))
        status_fail = row.get("status") == "fail"
        unresolved = row.get("method") == "unresolved"
        unwinnable = row.get("unwinnable") is True
        coverage = row.get("coverage") if isinstance(row.get("coverage"), Mapping) else {}
        table_coverage = coverage.get("coverage_classification") == "table-coverage"
        if row_failures or status_fail:
            failed_count += 1
            failures.append(
                {
                    "row_id": row_id,
                    "reason": "row-failed",
                    "failure_reasons": list(dict.fromkeys([*row_failures, *row.get("failure_reasons", [])]))
                    if isinstance(row.get("failure_reasons"), list)
                    else row_failures,
                }
            )
        if unresolved:
            unresolved_count += 1
        if unwinnable:
            unwinnable_count += 1
        if table_coverage:
            table_coverage_count += 1
        if status_fail or unresolved or unwinnable or table_coverage:
            fail_closed_count += 1
    return {
        "status": "pass" if failed_count == 0 else "fail",
        "registered_split_count": len(registered_splits),
        "certificate_count": len(certificates),
        "missing_certificate_count": len(missing_ids),
        "duplicate_certificate_count": len(duplicate_ids),
        "unresolved_count": unresolved_count,
        "unwinnable_count": unwinnable_count,
        "table_coverage_count": table_coverage_count,
        "failed_count": failed_count,
        "fail_closed_count": fail_closed_count,
        "failures": failures,
    }


def _hardgates(
    certificates: Sequence[Mapping[str, Any]],
    audit: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    failures = audit.get("failures") if isinstance(audit.get("failures"), list) else []

    def rows_with(reason_prefix: str) -> list[str]:
        refs = []
        for failure in failures:
            if not isinstance(failure, Mapping):
                continue
            row_id = failure.get("row_id")
            text = json.dumps(failure, sort_keys=True)
            if reason_prefix in text and isinstance(row_id, str):
                refs.append(row_id)
        return refs

    permission_failures = []
    for row in certificates:
        permissions = row.get("claim_permissions")
        coverage = row.get("coverage") if isinstance(row.get("coverage"), Mapping) else {}
        if not isinstance(permissions, Mapping):
            continue
        if row.get("unwinnable") is True and any(permissions.get(key) is True for key in CLAIM_PERMISSION_KEYS):
            permission_failures.append(str(row.get("row_id")))
        if coverage.get("coverage_classification") == "table-coverage" and (
            permissions.get("generalization_claim_allowed") is True
            or permissions.get("rule_abstraction_claim_allowed") is True
        ):
            permission_failures.append(str(row.get("row_id")))
    schema_failures = rows_with("missing-key") + rows_with("forbidden-certificate-id-alias") + rows_with("invalid-")
    oracle_failures = rows_with("invalid-oracle-run-ref")
    bound_failures = rows_with("bad-derivation") + rows_with("invalid-bounds")
    hg1_failures = rows_with("missing-certificate") + rows_with("duplicate-certificate")
    gate_rows = {
        "ORACLE-HG1": hg1_failures,
        "ORACLE-HG2": oracle_failures,
        "ORACLE-HG3": permission_failures,
        "ORACLE-HG4": schema_failures,
        "ORACLE-HG5": bound_failures,
    }
    return {
        gate_id: {
            "status": "pass" if not failure_refs else "fail",
            "checked_count": len(certificates),
            "failed_count": len(failure_refs),
            "failure_refs": failure_refs,
        }
        for gate_id, failure_refs in gate_rows.items()
    }


def _source_artifact_status(root: Path, artifact: str) -> dict[str, str]:
    path = root / artifact
    return {
        "artifact": artifact,
        "status": "resolved" if path.exists() else "missing",
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else "missing",
    }


def load_input_accessibility(root: Path) -> dict[str, Any]:
    payload = _load_json(root, INPUT_ACCESSIBILITY_ARTIFACT)
    if payload is None:
        return {"status": "missing", "rows": []}
    return payload


def default_registered_splits(root: Path) -> list[dict[str, Any]]:
    l1 = _load_json(root, DGT_L1_CONTROLS_ARTIFACT) or {}
    final_accuracy = _pointer_value(l1, "$.l1_step_ladder.step_rows.4.metrics.dgt_accuracy_mean")
    first_accuracy = _pointer_value(l1, "$.training_arms.dgt_l1.metrics.accuracy_mean")
    ood_accuracy = _pointer_value(l1, "$.training_arms.dgt_l1.metrics.ood_accuracy_mean")
    chance = _pointer_value(l1, "$.training_arms.dgt_l1.metrics.chance_accuracy")
    chance_accuracy = _as_float(chance, 1.0 / 16.0) or (1.0 / 16.0)
    return [
        {
            "experiment_id": "dgt-controls",
            "task_id": "dgt-l1-hidden-lag",
            "task_family": "analytic-visibility",
            "resolver_family": "analytic-visibility",
            "split_id": "l1-ood-hidden-lag",
            "split_kind": "ood",
            "split_fingerprint": _json_digest({"artifact": DGT_L1_CONTROLS_ARTIFACT, "split": "l1-ood-hidden-lag"}),
            "source_evidence_ref": f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_tiny_sequence_projection.ood_boundary",
            "label_function_ref": "bedc_quality_lab.dgt_l1_controls:_make_sequences",
            "visible_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-ood-hidden-lag'].visible_variables",
            "required_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-ood-hidden-lag'].required_variables",
            "visible_variables": ["x_minus_1", "x_minus_2"],
            "required_variables": ["x_minus_3"],
            "chance_accuracy": chance_accuracy,
            "observed_accuracy": _as_float(ood_accuracy, chance_accuracy),
            "epsilon": 1e-9,
            "not_claimed": NOT_CLAIMED,
        },
        {
            "experiment_id": "dgt-controls",
            "task_id": "dgt-l1-finite-pair",
            "task_family": "analytic-table-coverage",
            "resolver_family": "analytic-table-coverage",
            "split_id": "l1-indist-finite-pair",
            "split_kind": "in-distribution",
            "split_fingerprint": _json_digest({"artifact": DGT_L1_CONTROLS_ARTIFACT, "split": "l1-indist-finite-pair"}),
            "source_evidence_ref": f"{DGT_L1_CONTROLS_ARTIFACT}:$.l1_step_ladder.step_rows[4]",
            "label_function_ref": "bedc_quality_lab.dgt_l1_controls:_make_sequences",
            "visible_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-indist-finite-pair'].visible_variables",
            "required_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-indist-finite-pair'].required_variables",
            "visible_variables": ["x_left", "x_right"],
            "required_variables": ["x_left", "x_right"],
            "chance_accuracy": chance_accuracy,
            "observed_accuracy": _as_float(final_accuracy, 0.981934),
            "epsilon": 1e-9,
            "train_pair_count": 1024,
            "eval_pair_count": 256,
            "label_cardinality": 16,
            "not_claimed": NOT_CLAIMED,
        },
        {
            "experiment_id": "dgt-controls",
            "task_id": "dgt-l1-held-out-pair",
            "task_family": "analytic-visibility",
            "resolver_family": "analytic-visibility",
            "split_id": "l1-held-out-pair",
            "split_kind": "held-out-pair",
            "split_fingerprint": _json_digest({"artifact": DGT_L1_CONTROLS_ARTIFACT, "split": "l1-held-out-pair"}),
            "source_evidence_ref": f"{DGT_L1_CONTROLS_ARTIFACT}:$.training_arms.dgt_l1.metrics.accuracy_mean",
            "label_function_ref": "bedc_quality_lab.dgt_l1_controls:_make_sequences",
            "visible_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-held-out-pair'].visible_variables",
            "required_variables_ref": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[?split_id=='l1-held-out-pair'].required_variables",
            "visible_variables": ["x_left", "x_right"],
            "required_variables": ["x_left", "x_right"],
            "chance_accuracy": chance_accuracy,
            "observed_accuracy": _as_float(first_accuracy, chance_accuracy),
            "epsilon": 1e-9,
            "not_claimed": NOT_CLAIMED,
        },
    ]


def build_payload(
    *,
    root: Path,
    generated_at: str | None = None,
    registered_splits: Sequence[Mapping[str, Any]] | None = None,
    registry: WinnabilityRegistry | None = None,
    input_accessibility: Mapping[str, Any] | None = None,
    oracle_runs: Sequence[Mapping[str, Any]] = (),
) -> dict[str, Any]:
    timestamp = generated_at or datetime.now(timezone.utc).isoformat()
    rows = list(registered_splits if registered_splits is not None else default_registered_splits(root))
    active_registry = registry or DEFAULT_REGISTRY
    accessibility = dict(input_accessibility or load_input_accessibility(root))
    certificates = evaluate_winnability(
        rows,
        registry=active_registry,
        input_accessibility=accessibility,
        oracle_runs=oracle_runs,
    )
    audit = audit_certificates(rows, certificates, oracle_runs=oracle_runs)
    hardgates = _hardgates(certificates, audit)
    registry_rows = active_registry.family_registry()
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": PRODUCER,
        "owner": OWNER,
        "source_artifacts": {
            "dgt_l0_controls": _source_artifact_status(root, DGT_L0_CONTROLS_ARTIFACT),
            "dgt_l1_controls": _source_artifact_status(root, DGT_L1_CONTROLS_ARTIFACT),
            "input_accessibility": _source_artifact_status(root, INPUT_ACCESSIBILITY_ARTIFACT),
        },
        "input_pointers": {
            "input_accessibility": f"{INPUT_ACCESSIBILITY_ARTIFACT}:$",
            "registered_splits": f"{JSON_ARTIFACT}:$.family_registry",
        },
        "family_registry": registry_rows,
        "registry_digest": _json_digest(registry_rows),
        "oracle_runs": list(oracle_runs),
        "certificates": certificates,
        "audit": audit,
        "hardgates": hardgates,
        "consumer_pointers": {
            "certificates_pointer": f"{JSON_ARTIFACT}:$.certificates",
            "audit_pointer": f"{JSON_ARTIFACT}:$.audit",
            "hardgates_pointer": f"{JSON_ARTIFACT}:$.hardgates",
        },
        "not_claimed": list(NOT_CLAIMED),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    audit = payload.get("audit") if isinstance(payload.get("audit"), Mapping) else {}
    lines = [
        "# Winnability Certificates",
        "",
        f"- Artifact: `{payload.get('artifact_id', ARTIFACT_ID)}`",
        f"- Owner: `{payload.get('owner', OWNER)}`",
        f"- Audit: `{audit.get('status', 'missing')}`",
        f"- Certificates: `{audit.get('certificate_count', 0)}`",
        f"- Fail-closed count: `{audit.get('fail_closed_count', 0)}`",
        "",
        "| row_id | split | method | status | upper bound | observed | coverage |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload.get("certificates", []):
        if not isinstance(row, Mapping):
            continue
        coverage = row.get("coverage") if isinstance(row.get("coverage"), Mapping) else {}
        lines.append(
            "| "
            f"`{row.get('row_id', '')}` | "
            f"`{row.get('split_id', '')}` | "
            f"`{row.get('method', '')}` | "
            f"`{row.get('status', '')}` | "
            f"`{row.get('upper_bound_accuracy', '')}` | "
            f"`{row.get('observed_accuracy', '')}` | "
            f"`{coverage.get('coverage_classification', '')}` |"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")

"""Structural generalization split owner for canonical pointer consumers."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Literal, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:structural-generalization-splits"
ARTIFACT_ID = "bedc-quality-lab:structural-generalization-splits"
PRODUCER = "scripts/run_structural_generalization_splits.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/structural-generalization-splits.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/structural-generalization-splits.md"
INPUT_ACCESSIBILITY_ARTIFACT = "reports/canonical/input-accessibility.json"
WINNABILITY_CERTIFICATES_ARTIFACT = "reports/canonical/winnability-certificates.json"
INPUT_ACCESSIBILITY_SCHEMA_ID = "bedc-quality-lab:input-accessibility"
WINNABILITY_CERTIFICATES_SCHEMA_ID = "bedc-quality-lab:winnability-certificates"
GENERATED_AT = "2026-06-12T00:00:00+00:00"
ACCEPTED_FAMILIES = ("symbol_remapping", "position_shift_visible")
CLASSIFICATIONS = ("accepted", "excluded", "unanswerable")
NOT_CLAIMED = (
    "Pointer-only structural generalization split registry.",
    "No held-out pair protocol is owned here.",
    "No cross-validation verdict is recomputed here.",
    "No local visibility extractor or winnability arithmetic is introduced here.",
    "No positive split claim is emitted without resolved upstream evidence pointers.",
)


SplitFamily = Literal["symbol_remapping", "position_shift_visible"]
Classification = Literal["accepted", "excluded", "unanswerable"]


@dataclass(frozen=True)
class StructuralGeneralizationSplit:
    source_row_id: str
    family: SplitFamily
    target_variable: str
    candidate_id: str
    fair_arm_id: str
    candidate_visible: bool
    fair_arm_visible: bool
    candidate_winnable: bool
    fair_arm_winnable: bool
    visibility_pointer: str
    winnability_pointer: str
    performance_pointer: str | None = None
    row_id: str | None = None
    target_visible: bool = True
    finite_remap: Mapping[str, str] | None = None
    position_offset: int | None = None

    @property
    def public_row_id(self) -> str:
        if self.row_id:
            return _stable_slug(self.row_id)
        digest_input = f"{self.family}:{self.source_row_id}:{self.target_variable}:{self.candidate_id}:{self.fair_arm_id}"
        return f"sgs-{_stable_slug(digest_input)}"


def _stable_slug(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    if slug:
        return slug
    return hashlib.sha256(value.encode("utf-8")).hexdigest()[:12]


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _load_source_artifact(root: Path, artifact: str, expected_schema_id: str) -> dict[str, Any]:
    path = root / artifact
    base = {
        "artifact": artifact,
        "pointer": "$",
        "owner_pointer": f"{artifact}:$",
        "expected_schema_id": expected_schema_id,
    }
    if not path.exists():
        return {**base, "status": "missing", "payload": None, "digest": None}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {**base, "status": "invalid", "payload": None, "digest": None}
    if not isinstance(payload, Mapping):
        return {**base, "status": "invalid", "payload": None, "digest": _json_digest(payload)}
    if payload.get("schema_id") != expected_schema_id:
        return {
            **base,
            "status": "schema-mismatch",
            "payload": dict(payload),
            "digest": _json_digest(payload),
            "observed_schema_id": payload.get("schema_id"),
        }
    return {**base, "status": "resolved", "payload": dict(payload), "digest": _json_digest(payload)}


def _row_id(row: Mapping[str, Any]) -> str | None:
    for key in ("row_id", "id", "split_id", "certificate_id"):
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def _row_map(payload: Mapping[str, Any] | None) -> dict[str, Mapping[str, Any]]:
    if payload is None:
        return {}
    rows: list[Any] = []
    for key in (
        "rows",
        "input_rows",
        "visibility_rows",
        "accessibility_rows",
        "certificate_rows",
        "winnability_rows",
        "split_rows",
        "registry",
    ):
        value = payload.get(key)
        if isinstance(value, list):
            rows.extend(value)
    indexed: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        if isinstance(row, Mapping):
            rid = _row_id(row)
            if rid is not None:
                indexed[rid] = row
    return indexed


def _bool_cell(row: Mapping[str, Any], keys: Sequence[str], default: bool = False) -> bool:
    for key in keys:
        value = row.get(key)
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            if value in {"pass", "resolved", "visible", "winnable", "true"}:
                return True
            if value in {"fail", "missing", "hidden", "unwinnable", "false"}:
                return False
    return default


def _int_cell(row: Mapping[str, Any], keys: Sequence[str]) -> int | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, int) and not isinstance(value, bool):
            return value
    return None


def _mapping_cell(row: Mapping[str, Any], keys: Sequence[str]) -> Mapping[str, str] | None:
    for key in keys:
        value = row.get(key)
        if isinstance(value, Mapping) and all(isinstance(k, str) and isinstance(v, str) for k, v in value.items()):
            return dict(value)
    return None


def _string_cell(row: Mapping[str, Any], keys: Sequence[str], default: str) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return default


def _candidate_from_rows(
    row_id: str,
    *,
    family: SplitFamily,
    visibility_rows: Mapping[str, Mapping[str, Any]],
    winnability_rows: Mapping[str, Mapping[str, Any]],
) -> StructuralGeneralizationSplit:
    visibility = visibility_rows.get(row_id, {})
    winnability = winnability_rows.get(row_id, {})
    return StructuralGeneralizationSplit(
        row_id=f"sgs-{row_id}",
        source_row_id=row_id,
        family=family,
        target_variable=_string_cell(visibility, ("target_variable", "target"), "target"),
        candidate_id=_string_cell(visibility, ("candidate_id", "candidate"), "candidate"),
        fair_arm_id=_string_cell(visibility, ("fair_arm_id", "fair_arm"), "fair-arm"),
        target_visible=_bool_cell(visibility, ("target_visible", "target_accessible"), False),
        candidate_visible=_bool_cell(visibility, ("candidate_visible", "visible_to_candidate", "candidate_target_visible"), False),
        fair_arm_visible=_bool_cell(visibility, ("fair_arm_visible", "visible_to_fair_arm", "fair_arm_target_visible"), False),
        candidate_winnable=_bool_cell(winnability, ("candidate_winnable", "candidate_can_win", "winnable"), False),
        fair_arm_winnable=_bool_cell(winnability, ("fair_arm_winnable", "fair_arm_can_win", "fair_control_winnable"), False),
        visibility_pointer=f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows[{row_id}]",
        winnability_pointer=f"{WINNABILITY_CERTIFICATES_ARTIFACT}:$.rows[{row_id}]",
        performance_pointer=_string_cell(visibility, ("performance_pointer", "evidence_pointer"), "")
        or _string_cell(winnability, ("performance_pointer", "evidence_pointer"), ""),
        finite_remap=_mapping_cell(visibility, ("finite_remap", "remap", "symbol_map")),
        position_offset=_int_cell(visibility, ("position_offset", "offset")),
    )


def default_split_candidates(
    *,
    visibility_rows: Mapping[str, Mapping[str, Any]] | None = None,
    winnability_rows: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[StructuralGeneralizationSplit, ...]:
    visibility_rows = visibility_rows or {}
    winnability_rows = winnability_rows or {}
    discovered: list[StructuralGeneralizationSplit] = []
    for row_id, row in visibility_rows.items():
        family = row.get("structural_generalization_family") or row.get("family")
        if family in ACCEPTED_FAMILIES:
            discovered.append(
                _candidate_from_rows(
                    row_id,
                    family=family,  # type: ignore[arg-type]
                    visibility_rows=visibility_rows,
                    winnability_rows=winnability_rows,
                )
            )
    if discovered:
        return tuple(discovered)
    return (
        StructuralGeneralizationSplit(
            row_id="sgs-symbol-remapping",
            source_row_id="symbol-remapping",
            family="symbol_remapping",
            target_variable="target_symbol",
            candidate_id="symbol-remap-candidate",
            fair_arm_id="symbol-remap-fair-arm",
            target_visible=False,
            candidate_visible=False,
            fair_arm_visible=False,
            candidate_winnable=False,
            fair_arm_winnable=False,
            visibility_pointer=f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows.symbol-remapping",
            winnability_pointer=f"{WINNABILITY_CERTIFICATES_ARTIFACT}:$.rows.symbol-remapping",
            performance_pointer=None,
            finite_remap={"x": "u", "y": "v"},
        ),
        StructuralGeneralizationSplit(
            row_id="sgs-position-shift-visible",
            source_row_id="position-shift-visible",
            family="position_shift_visible",
            target_variable="position_target",
            candidate_id="position-shift-candidate",
            fair_arm_id="position-shift-fair-arm",
            target_visible=False,
            candidate_visible=False,
            fair_arm_visible=False,
            candidate_winnable=False,
            fair_arm_winnable=False,
            visibility_pointer=f"{INPUT_ACCESSIBILITY_ARTIFACT}:$.rows.position-shift-visible",
            winnability_pointer=f"{WINNABILITY_CERTIFICATES_ARTIFACT}:$.rows.position-shift-visible",
            performance_pointer=None,
            position_offset=1,
        ),
    )


def _gate(gate_id: str, passed: bool, reason: str, evidence_pointer: str | None) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "pass" if passed else "fail",
        "reason": reason,
        "evidence_pointer": evidence_pointer,
    }


def evaluate_symbol_remapping_hardgates(
    split: StructuralGeneralizationSplit,
    *,
    root: Path | None = None,
) -> dict[str, dict[str, Any]]:
    remap = split.finite_remap or {}
    finite_remap = bool(remap) and all(k != v for k, v in remap.items())
    visibility = split.target_visible and split.candidate_visible and split.fair_arm_visible
    winnability = split.candidate_winnable and split.fair_arm_winnable
    performance = split.performance_pointer is not None and (
        root is None or resolve_artifact_pointer(root, split.performance_pointer) is not None
    )
    return {
        "SYM-HG1": _gate("SYM-HG1", finite_remap, "finite non-identity symbol remap", split.visibility_pointer),
        "SYM-HG2": _gate("SYM-HG2", visibility, "target visible to candidate and fair arm", split.visibility_pointer),
        "SYM-HG3": _gate("SYM-HG3", winnability, "candidate and fair arm are winnability-certified", split.winnability_pointer),
        "SYM-HG4": _gate("SYM-HG4", performance, "performance evidence pointer resolves", split.performance_pointer),
    }


def evaluate_position_shift_hardgates(
    split: StructuralGeneralizationSplit,
    *,
    root: Path | None = None,
) -> dict[str, dict[str, Any]]:
    bounded_offset = split.position_offset is not None and 0 < abs(split.position_offset) <= 4
    visibility = split.target_visible and split.candidate_visible and split.fair_arm_visible
    winnability = split.candidate_winnable and split.fair_arm_winnable
    performance = split.performance_pointer is not None and (
        root is None or resolve_artifact_pointer(root, split.performance_pointer) is not None
    )
    return {
        "POS-HG1": _gate("POS-HG1", bounded_offset, "bounded nonzero position offset", split.visibility_pointer),
        "POS-HG2": _gate("POS-HG2", visibility, "target visible to candidate and fair arm", split.visibility_pointer),
        "POS-HG3": _gate("POS-HG3", winnability, "candidate and fair arm are winnability-certified", split.winnability_pointer),
        "POS-HG4": _gate("POS-HG4", performance, "performance evidence pointer resolves", split.performance_pointer),
    }


def _hardgates(split: StructuralGeneralizationSplit, *, root: Path | None) -> dict[str, dict[str, Any]]:
    if split.family == "symbol_remapping":
        return evaluate_symbol_remapping_hardgates(split, root=root)
    return evaluate_position_shift_hardgates(split, root=root)


def classify_structural_generalization_split(
    split: StructuralGeneralizationSplit,
    *,
    root: Path | None = None,
    source_statuses: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    source_statuses = source_statuses or {}
    gates = _hardgates(split, root=root)
    failed = [gate_id for gate_id, row in gates.items() if row["status"] != "pass"]
    source_failures = {
        key: status
        for key, status in source_statuses.items()
        if status != "resolved"
    }
    if source_failures:
        classification: Classification = "excluded"
        claim_exclusion = "boundary-ledger-only"
        family: str | None = None
        reason = "required-source-artifact-unresolved"
    elif not (split.target_visible and split.candidate_visible and split.fair_arm_visible):
        classification = "unanswerable"
        claim_exclusion = "boundary-ledger-only"
        family = None
        reason = "target-variable-not-visible-to-all-required-arms"
    elif failed:
        classification = "excluded"
        claim_exclusion = "boundary-ledger-only"
        family = None
        reason = "hardgate-failed"
    else:
        classification = "accepted"
        claim_exclusion = None
        family = split.family
        reason = "hardgates-pass"
    return {
        "row_id": split.public_row_id,
        "source_row_id": split.source_row_id,
        "classification": classification,
        "structural_generalization_family": family,
        "claim_exclusion": claim_exclusion,
        "reason": reason,
        "target_variable": split.target_variable,
        "candidate_id": split.candidate_id,
        "fair_arm_id": split.fair_arm_id,
        "visibility_pointer": split.visibility_pointer,
        "winnability_pointer": split.winnability_pointer,
        "performance_pointer": split.performance_pointer,
        "failed_hardgates": failed,
        "hardgate_status": "pass" if not failed and not source_failures else "fail",
        "hardgates": gates,
    }


def _aggregate_hardgates(classifier_rows: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    gate_ids = ("SYM-HG1", "SYM-HG2", "SYM-HG3", "SYM-HG4", "POS-HG1", "POS-HG2", "POS-HG3", "POS-HG4")
    aggregate: dict[str, dict[str, Any]] = {}
    for gate_id in gate_ids:
        rows = [
            row
            for row in classifier_rows
            if isinstance(row.get("hardgates"), Mapping) and gate_id in row["hardgates"]
        ]
        failed_rows = [str(row["row_id"]) for row in rows if row["hardgates"][gate_id]["status"] != "pass"]
        aggregate[gate_id] = {
            "gate_id": gate_id,
            "status": "pass" if rows and not failed_rows else "fail",
            "row_ids": [str(row["row_id"]) for row in rows],
            "failed_row_ids": failed_rows,
        }
    return aggregate


def _boundary_ledger(classifier_rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    ledger: list[dict[str, Any]] = []
    for row in classifier_rows:
        if row.get("classification") == "accepted":
            continue
        ledger.append(
            {
                "row_id": row["row_id"],
                "classification": row["classification"],
                "claim_exclusion": row["claim_exclusion"],
                "reason": row["reason"],
                "failed_hardgates": row["failed_hardgates"],
                "visibility_pointer": row["visibility_pointer"],
                "winnability_pointer": row["winnability_pointer"],
                "performance_pointer": row["performance_pointer"],
            }
        )
    return ledger


def _source_artifacts(root: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    input_accessibility = _load_source_artifact(root, INPUT_ACCESSIBILITY_ARTIFACT, INPUT_ACCESSIBILITY_SCHEMA_ID)
    winnability = _load_source_artifact(root, WINNABILITY_CERTIFICATES_ARTIFACT, WINNABILITY_CERTIFICATES_SCHEMA_ID)
    return input_accessibility, winnability


def build_structural_generalization_payload(
    *,
    root: Path,
    generated_at: str | None = None,
    split_candidates: Sequence[StructuralGeneralizationSplit] | None = None,
) -> dict[str, Any]:
    input_accessibility, winnability = _source_artifacts(root)
    visibility_rows = _row_map(input_accessibility.get("payload"))
    winnability_rows = _row_map(winnability.get("payload"))
    candidates = tuple(split_candidates) if split_candidates is not None else default_split_candidates(
        visibility_rows=visibility_rows,
        winnability_rows=winnability_rows,
    )
    source_statuses = {
        "input_accessibility": str(input_accessibility["status"]),
        "winnability_certificates": str(winnability["status"]),
    }
    classifier_rows = [
        classify_structural_generalization_split(candidate, root=root, source_statuses=source_statuses)
        for candidate in candidates
    ]
    split_rows = [
        {
            "row_id": row["row_id"],
            "source_row_id": row["source_row_id"],
            "structural_generalization_family": row["structural_generalization_family"],
            "target_variable": row["target_variable"],
            "candidate_id": row["candidate_id"],
            "fair_arm_id": row["fair_arm_id"],
            "visibility_pointer": row["visibility_pointer"],
            "winnability_pointer": row["winnability_pointer"],
            "performance_pointer": row["performance_pointer"],
            "hardgate_status": row["hardgate_status"],
        }
        for row in classifier_rows
        if row["classification"] == "accepted"
    ]
    source_artifacts = {
        "input_accessibility": {k: v for k, v in input_accessibility.items() if k != "payload"},
        "winnability_certificates": {k: v for k, v in winnability.items() if k != "payload"},
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "producer": PRODUCER,
        "source_artifacts": source_artifacts,
        "split_registry": [
            {
                "family": "symbol_remapping",
                "accepted_classification": "accepted",
                "hardgate_ids": ["SYM-HG1", "SYM-HG2", "SYM-HG3", "SYM-HG4"],
            },
            {
                "family": "position_shift_visible",
                "accepted_classification": "accepted",
                "hardgate_ids": ["POS-HG1", "POS-HG2", "POS-HG3", "POS-HG4"],
            },
        ],
        "split_rows": split_rows,
        "classifier_rows": classifier_rows,
        "hardgates": _aggregate_hardgates(classifier_rows),
        "boundary_ledger": _boundary_ledger(classifier_rows),
        "consumer_pointers": {
            "splits_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.split_rows",
            "classifier_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.classifier_rows",
            "hardgates_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
            "boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.boundary_ledger",
        },
        "not_claimed": list(NOT_CLAIMED),
    }


def render_structural_generalization_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Structural Generalization Splits",
        "",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Accepted split rows: `{len(payload['split_rows'])}`",
        f"- Boundary rows: `{len(payload['boundary_ledger'])}`",
        "",
        "## Source Artifacts",
        "",
        "| source | status | artifact |",
        "| --- | --- | --- |",
    ]
    for source_id, source in payload["source_artifacts"].items():
        lines.append(f"| `{source_id}` | `{source['status']}` | `{source['artifact']}` |")
    lines.extend(
        [
            "",
            "## Classifier Rows",
            "",
            "| row | classification | family | reason |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in payload["classifier_rows"]:
        family = row["structural_generalization_family"] if row["structural_generalization_family"] is not None else ""
        lines.append(f"| `{row['row_id']}` | `{row['classification']}` | `{family}` | `{row['reason']}` |")
    lines.extend(["", "## Nonclaims", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    return "\n".join(lines) + "\n"


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    _write_json(root / CANONICAL_JSON_ARTIFACT, payload)
    (root / CANONICAL_MARKDOWN_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
    (root / CANONICAL_MARKDOWN_ARTIFACT).write_text(
        render_structural_generalization_markdown(payload),
        encoding="utf-8",
    )

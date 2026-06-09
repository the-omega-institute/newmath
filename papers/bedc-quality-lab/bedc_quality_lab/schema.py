"""Schema boundary for lab-local quality evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
import json
from pathlib import Path
from typing import Any, Mapping


SCHEMA_ID = "bedc-quality-lab:evidence-envelope"

_REQUIRED_MAPPING_FIELDS = (
    "source_spec",
    "pattern_spec",
    "classifier_spec",
    "stability_spec",
    "metrics",
    "artifacts",
    "source_artifact_hash",
    "claim_capsule_pointer",
    "cost_protocol_pointer",
    "negative_witness_sweep_pointer",
)

_PROHIBITED_BEDC_PROSE_MARKERS = (
    "closurestatus",
    "origin{",
    "\\origin",
    "NameCert",
    "ledger records",
    "theoryclosure",
    "formalstatus",
    "leanchecked",
    "scopeclosed",
    "upgradepath",
    "notclaimed",
    "BEDC has",
    "must use",
    "must not",
    "shall",
)

_PROHIBITED_PROVENANCE_MARKERS = (
    "terminal_verdict",
    "discovery_level",
    "D4",
    "D5-O",
    "D5-M",
    "payload",
    "raw_payload",
    "report_payload",
)


def _require_non_empty_string(value: Any, field_name: str) -> None:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{field_name} must be a non-empty string")


def _require_mapping(value: Any, field_name: str) -> None:
    if not isinstance(value, dict):
        raise ValueError(f"{field_name} must be a mapping")


def _require_list_of_strings(value: Any, field_name: str) -> None:
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise ValueError(f"{field_name} must be a list of strings")


def _contains_bedc_prose(value: Any) -> bool:
    if isinstance(value, str):
        if " " not in value and "\n" not in value and "\t" not in value:
            return False
        lowered = value.lower()
        return any(marker.lower() in lowered for marker in _PROHIBITED_BEDC_PROSE_MARKERS)
    if isinstance(value, Mapping):
        return any(_contains_bedc_prose(item) for item in value.values())
    if isinstance(value, list):
        return any(_contains_bedc_prose(item) for item in value)
    return False


def _contains_prohibited_provenance(value: Any) -> bool:
    if isinstance(value, str):
        lowered = value.lower()
        return any(marker.lower() in lowered for marker in _PROHIBITED_PROVENANCE_MARKERS)
    if isinstance(value, Mapping):
        return any(
            _contains_prohibited_provenance(key)
            or _contains_prohibited_provenance(item)
            for key, item in value.items()
        )
    if isinstance(value, list):
        return any(_contains_prohibited_provenance(item) for item in value)
    return False


def _require_pointer_mapping(
    value: Any,
    field_name: str,
    *,
    required_keys: tuple[str, ...] = ("artifact", "pointer"),
) -> None:
    _require_mapping(value, field_name)
    if not value:
        return
    if _contains_prohibited_provenance(value) or _contains_bedc_prose(value):
        raise ValueError(f"{field_name} must contain only opaque artifact pointers")
    if set(value) != set(required_keys):
        keys = ", ".join(required_keys)
        raise ValueError(f"{field_name} must contain exactly: {keys}")
    for key in required_keys:
        _require_non_empty_string(value[key], f"{field_name}.{key}")
    if "pointer" in required_keys and not value["pointer"].startswith("$"):
        raise ValueError(f"{field_name}.pointer must be a JSON pointer expression")


def _require_hash_mapping(value: Any, field_name: str) -> None:
    _require_mapping(value, field_name)
    if not value:
        return
    if set(value) != {"algorithm", "value"}:
        raise ValueError(f"{field_name} must contain exactly: algorithm, value")
    if value["algorithm"] != "sha256":
        raise ValueError(f"{field_name}.algorithm must be 'sha256'")
    _require_non_empty_string(value["value"], f"{field_name}.value")
    digest = value["value"]
    if len(digest) != 64 or any(char not in "0123456789abcdef" for char in digest):
        raise ValueError(f"{field_name}.value must be a lowercase sha256 hex digest")


@dataclass(frozen=True)
class QualityEvidenceEnvelope:
    """Lab evidence boundary consumed by reports and review tooling."""

    schema_id: str
    run_id: str
    source_spec: dict[str, Any]
    pattern_spec: dict[str, Any]
    classifier_spec: dict[str, Any]
    stability_spec: dict[str, Any]
    metrics: dict[str, float]
    ledger_gaps: list[str] = field(default_factory=list)
    debt_items: list[str] = field(default_factory=list)
    artifacts: dict[str, str] = field(default_factory=dict)
    bedc_refs: list[str] = field(default_factory=list)
    evidence_type: str = "unspecified"
    evidence_scope: str = "unspecified"
    backend_owner: str = "unspecified"
    source_artifact_hash: dict[str, Any] = field(default_factory=dict)
    claim_capsule_pointer: dict[str, Any] = field(default_factory=dict)
    cost_protocol_pointer: dict[str, Any] = field(default_factory=dict)
    negative_witness_sweep_pointer: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_non_empty_string(self.schema_id, "schema_id")
        if self.schema_id != SCHEMA_ID:
            raise ValueError(f"schema_id must be {SCHEMA_ID!r}")
        _require_non_empty_string(self.run_id, "run_id")
        _require_non_empty_string(self.evidence_type, "evidence_type")
        _require_non_empty_string(self.evidence_scope, "evidence_scope")
        _require_non_empty_string(self.backend_owner, "backend_owner")

        for field_name in _REQUIRED_MAPPING_FIELDS:
            _require_mapping(getattr(self, field_name), field_name)

        _require_list_of_strings(self.ledger_gaps, "ledger_gaps")
        _require_list_of_strings(self.debt_items, "debt_items")
        _require_list_of_strings(self.bedc_refs, "bedc_refs")

        if not self.metrics:
            raise ValueError("metrics must contain at least one measured value")
        for key, value in self.metrics.items():
            if not isinstance(key, str) or not key:
                raise ValueError("metric keys must be non-empty strings")
            if not isinstance(value, (int, float)):
                raise ValueError(f"metric {key} must be numeric")

        for key, value in self.artifacts.items():
            _require_non_empty_string(key, "artifact key")
            _require_non_empty_string(value, f"artifact {key}")

        if _contains_bedc_prose(self.bedc_refs):
            raise ValueError("bedc_refs must be opaque pointers, not copied BEDC rule prose")

        _require_hash_mapping(self.source_artifact_hash, "source_artifact_hash")
        _require_pointer_mapping(self.claim_capsule_pointer, "claim_capsule_pointer")
        _require_pointer_mapping(self.cost_protocol_pointer, "cost_protocol_pointer")
        _require_pointer_mapping(
            self.negative_witness_sweep_pointer,
            "negative_witness_sweep_pointer",
        )

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def to_json(self, *, indent: int = 2) -> str:
        return json.dumps(self.to_dict(), indent=indent, sort_keys=True)

    def write_json(self, path: str | Path) -> None:
        target = Path(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(self.to_json() + "\n", encoding="utf-8")

    @classmethod
    def from_dict(cls, data: Mapping[str, Any]) -> "QualityEvidenceEnvelope":
        kwargs = dict(data)
        return cls(**kwargs)

    @classmethod
    def read_json(cls, path: str | Path) -> "QualityEvidenceEnvelope":
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        return cls.from_dict(data)

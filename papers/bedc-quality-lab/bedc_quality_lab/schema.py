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

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_non_empty_string(self.schema_id, "schema_id")
        if self.schema_id != SCHEMA_ID:
            raise ValueError(f"schema_id must be {SCHEMA_ID!r}")
        _require_non_empty_string(self.run_id, "run_id")

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

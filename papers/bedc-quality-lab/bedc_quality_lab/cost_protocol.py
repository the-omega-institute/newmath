"""Cost protocol loader for lab-local quality debt accounting."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Iterable, Mapping, Any

from .ledger import LedgerRowKey
from .metrics import QUALITY_Q_FORMULA_ID, quality_formula_description


DEFAULT_COST_PROTOCOL_PATH = Path(__file__).resolve().parents[1] / "configs" / "default_cost_protocol.yaml"

REQUIRED_DEBT_ROWS = frozenset(
    {
        LedgerRowKey("source", "source-coverage"),
        LedgerRowKey("source", "mixing-family-coverage"),
        LedgerRowKey("source", "finite-sample-support"),
        LedgerRowKey("classifier", "optimizer-certificate"),
        LedgerRowKey("verification", "theorem3-bound-margin"),
        LedgerRowKey("generalization", "global-claim-boundary"),
    }
)

_ALLOWED_FORMULA_IDS = frozenset({QUALITY_Q_FORMULA_ID})
_ALLOWED_TOP_LEVEL_KEYS = frozenset({"name", "quality_formula", "row_weights", "not_claimed"})
_ALLOWED_FORMULA_KEYS = frozenset({"id", "text"})
_ALLOWED_NOT_CLAIMED_KEYS = frozenset({"global_boundary", "treatment"})


@dataclass(frozen=True)
class QualityFormula:
    id: str
    text: str


@dataclass(frozen=True)
class NotClaimedPolicy:
    global_boundary: tuple[str, ...]
    treatment: str


@dataclass(frozen=True)
class CostProtocol:
    name: str
    row_weights: Mapping[LedgerRowKey, float]
    quality_formula: QualityFormula
    not_claimed: NotClaimedPolicy

    def validate_required_rows(self, rows: Iterable[LedgerRowKey]) -> None:
        required = frozenset(rows)
        missing = required - frozenset(self.row_weights)
        if missing:
            keys = ", ".join(_format_row_key(row) for row in sorted(missing))
            raise ValueError(f"cost protocol missing required row weights: {keys}")

    def weight(self, row: LedgerRowKey) -> float:
        self.validate_required_rows((row,))
        return float(self.row_weights[row])

    def formula_description(self) -> str:
        return self.quality_formula.text


def load_cost_protocol(path: Path | None = None) -> CostProtocol:
    target = DEFAULT_COST_PROTOCOL_PATH if path is None else Path(path)
    data = _parse_protocol_yaml(target)
    return _cost_protocol_from_mapping(data)


def validate_required_rows(rows: Iterable[LedgerRowKey]) -> None:
    load_cost_protocol().validate_required_rows(rows)


def weight(row: LedgerRowKey) -> float:
    return load_cost_protocol().weight(row)


def formula_description() -> str:
    return load_cost_protocol().formula_description()


def _format_row_key(row: LedgerRowKey) -> str:
    return f"{row.kind}/{row.residue}"


def _parse_row_key(raw: str) -> LedgerRowKey:
    if raw.count("/") != 1:
        raise ValueError(f"cost protocol row key must be <kind>/<residue>: {raw!r}")
    kind, residue = raw.split("/", 1)
    if not kind or not residue:
        raise ValueError(f"cost protocol row key must be <kind>/<residue>: {raw!r}")
    return LedgerRowKey(kind, residue)


def _parse_scalar(raw: str) -> Any:
    value = raw.strip()
    if not value:
        return ""
    if value[0] == value[-1:] and value[0] in {"'", '"'}:
        return value[1:-1]
    try:
        return float(value)
    except ValueError:
        return value


def _parse_list(raw: str) -> list[str]:
    value = raw.strip()
    if not (value.startswith("[") and value.endswith("]")):
        raise ValueError("cost protocol list values must use inline [a, b] syntax")
    body = value[1:-1].strip()
    if not body:
        return []
    return [str(_parse_scalar(item.strip())) for item in body.split(",")]


def _parse_protocol_yaml(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise ValueError(f"cost protocol file does not exist: {path}")
    root: dict[str, Any] = {}
    current_section: str | None = None
    seen_entries: dict[str, set[str]] = {}
    for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw_line.strip() or raw_line.lstrip().startswith("#"):
            continue
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        if indent not in {0, 2}:
            raise ValueError(f"unsupported cost protocol indentation at line {line_number}")
        key, sep, raw_value = raw_line.strip().partition(":")
        if not sep or not key:
            raise ValueError(f"invalid cost protocol line {line_number}")
        if indent == 0:
            if key in root:
                raise ValueError(f"duplicate cost protocol key: {key}")
            if key not in _ALLOWED_TOP_LEVEL_KEYS:
                raise ValueError(f"unknown cost protocol key: {key}")
            if raw_value.strip():
                root[key] = _parse_scalar(raw_value)
                current_section = None
            else:
                root[key] = {}
                current_section = key
                seen_entries[key] = set()
            continue
        if current_section is None or not isinstance(root.get(current_section), dict):
            raise ValueError(f"cost protocol nested value without section at line {line_number}")
        if key in seen_entries[current_section]:
            raise ValueError(f"duplicate cost protocol key in {current_section}: {key}")
        seen_entries[current_section].add(key)
        value = _parse_list(raw_value) if raw_value.strip().startswith("[") else _parse_scalar(raw_value)
        root[current_section][key] = value
    return root


def _require_mapping(data: Mapping[str, Any], key: str) -> Mapping[str, Any]:
    value = data.get(key)
    if not isinstance(value, dict):
        raise ValueError(f"cost protocol {key} must be a mapping")
    return value


def _require_string(data: Mapping[str, Any], key: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"cost protocol {key} must be a non-empty string")
    return value


def _cost_protocol_from_mapping(data: Mapping[str, Any]) -> CostProtocol:
    unknown_top = frozenset(data) - _ALLOWED_TOP_LEVEL_KEYS
    if unknown_top:
        raise ValueError(f"unknown cost protocol keys: {sorted(unknown_top)}")

    name = _require_string(data, "name")
    formula_data = _require_mapping(data, "quality_formula")
    row_weight_data = _require_mapping(data, "row_weights")
    not_claimed_data = _require_mapping(data, "not_claimed")

    if frozenset(formula_data) - _ALLOWED_FORMULA_KEYS:
        raise ValueError("unknown quality_formula keys")
    formula_id = _require_string(formula_data, "id")
    if formula_id not in _ALLOWED_FORMULA_IDS:
        raise ValueError(f"unknown quality formula id: {formula_id}")
    formula_text = _require_string(formula_data, "text")
    if formula_text != quality_formula_description():
        raise ValueError("quality formula text does not match metrics arithmetic")

    if frozenset(not_claimed_data) - _ALLOWED_NOT_CLAIMED_KEYS:
        raise ValueError("unknown not_claimed keys")
    boundary = not_claimed_data.get("global_boundary")
    if not isinstance(boundary, list) or not boundary or any(not isinstance(item, str) or not item for item in boundary):
        raise ValueError("not_claimed.global_boundary must be a non-empty list of strings")
    treatment = _require_string(not_claimed_data, "treatment")

    row_weights: dict[LedgerRowKey, float] = {}
    for raw_key, raw_weight in row_weight_data.items():
        if not isinstance(raw_key, str):
            raise ValueError("cost protocol row weight keys must be strings")
        row = _parse_row_key(raw_key)
        if row not in REQUIRED_DEBT_ROWS:
            raise ValueError(f"unknown cost protocol row: {raw_key}")
        if row in row_weights:
            raise ValueError(f"duplicate cost protocol row: {raw_key}")
        if not isinstance(raw_weight, (int, float)):
            raise ValueError(f"cost protocol weight must be numeric: {raw_key}")
        weight = float(raw_weight)
        if weight < 0.0 or weight > 1.0:
            raise ValueError(f"cost protocol weight out of bounds: {raw_key}")
        row_weights[row] = weight

    protocol = CostProtocol(
        name=name,
        row_weights=MappingProxyType(dict(row_weights)),
        quality_formula=QualityFormula(id=formula_id, text=formula_text),
        not_claimed=NotClaimedPolicy(global_boundary=tuple(boundary), treatment=treatment),
    )
    protocol.validate_required_rows(REQUIRED_DEBT_ROWS)
    return protocol


def format_cost_protocol_lines(protocol: CostProtocol) -> list[str]:
    lines = [
        f"- Protocol: `{protocol.name}`",
        f"- Formula: `{protocol.quality_formula.id}` = `{protocol.formula_description()}`",
        "- Row weights:",
    ]
    for row in sorted(protocol.row_weights):
        lines.append(f"  - `{_format_row_key(row)}`: {protocol.weight(row):.6f}")
    boundary = ", ".join(f"`{item}`" for item in protocol.not_claimed.global_boundary)
    lines.extend(
        [
            "- Not claimed global boundary:",
            f"  - tokens: {boundary}",
            f"  - treatment: {protocol.not_claimed.treatment}",
        ]
    )
    return lines

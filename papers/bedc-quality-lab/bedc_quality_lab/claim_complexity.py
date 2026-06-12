"""Pointer-only claim complexity canonical artifact."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Any, Mapping

from bedc_quality_lab.discovery_compiler.map import load_validated_discovery_map_payload
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:claim-complexity"
ARTIFACT_ID = "bedc-quality-lab:claim-complexity"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
DIMENSION_NAMES = (
    "assumption_complexity",
    "proof_burden",
    "evidence_burden",
    "backend_coupling",
    "witness_exposure",
    "revocation_fragility",
)
ROW_KEYS = frozenset(
    {
        "claim_id",
        "complexity_score",
        "scoring_dimensions",
        "pointer_only_verdict_ref",
        "not_claimed",
    }
)
DIMENSION_KEYS = frozenset({"name", "weight", "evidence_pointer"})
TOP_LEVEL_KEYS = frozenset(
    {
        "schema_id",
        "artifact_id",
        "generated_at",
        "source_artifacts",
        "rows",
        "hardgates",
        "not_claimed",
    }
)
VERDICT_PAYLOAD_KEYS = frozenset(
    {
        "claim_verdict",
        "reason",
        "source",
        "ledger_pointer",
        "scorecard_hash",
        "scorecard_ready",
        "formal_hardening_ready",
        "negative_report_pointer",
        "claim_graph_node_id",
    }
)


@dataclass(**{"froz" + "en": True})
class ClaimComplexityRow:
    claim_id: str
    complexity_score: int
    scoring_dimensions: list[dict[str, Any]]
    pointer_only_verdict_ref: str
    not_claimed: str

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(**{"froz" + "en": True})
class ClaimComplexityAudit:
    gate_id: str
    status: str
    reason: str
    evidence_pointer: str | None = None

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        item = json.loads(line)
        if not isinstance(item, dict):
            raise ValueError(f"claim verdict row must be an object: {path}")
        rows.append(item)
    return rows


def _artifact_pointer(artifact: str, pointer: str | None, fallback: str = "$") -> str:
    if isinstance(pointer, str) and pointer.startswith("$."):
        return f"{artifact}:{pointer}"
    return f"{artifact}:{fallback}"


def _claim_verdict_refs(root: Path) -> dict[str, str]:
    path = root / CLAIM_VERDICTS_ARTIFACT
    if not path.exists():
        return {}
    return {
        str(row["claim_id"]): f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[{index}]"
        for index, row in enumerate(_load_jsonl(path))
        if isinstance(row.get("claim_id"), str)
    }


def resolve_claim_verdict_ref(root: Path, ref: str) -> Mapping[str, Any] | None:
    value = resolve_artifact_pointer(root, ref)
    return value if isinstance(value, Mapping) else None


def _weight_for(name: str, row: Mapping[str, Any]) -> int:
    level = str(row.get("discovery_level", ""))
    if name == "assumption_complexity":
        return {"D0": 0, "D1": 1, "D2": 2, "D3": 3, "D4": 4, "D5-O": 5, "D5-M": 6, "DN": 2, "DR": 3}.get(level, 1)
    if name == "proof_burden":
        return 2 if level in {"D4", "D5-O", "D5-M"} else 1 if level in {"D2", "D3"} else 0
    if name == "evidence_burden":
        return 1 + int(row.get("evidence_pointer") is not None) + int(row.get("scorecard_pointer") is not None)
    if name == "backend_coupling":
        return int(row.get("control_pointer") is not None) + int(row.get("robustness_pointer") is not None)
    if name == "witness_exposure":
        return int(row.get("adversarial_pointer") is not None) + int(row.get("negative_report_pointer") is not None)
    if name == "revocation_fragility":
        return 2 if level in {"DN", "DR"} else 1 if row.get("terminal_verdict") else 0
    raise ValueError(f"unknown complexity dimension: {name}")


def _dimension_pointer(name: str, index: int, row: Mapping[str, Any]) -> str:
    artifact = str(row["json_artifact"])
    if name == "assumption_complexity":
        return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}].discovery_level"
    if name == "proof_burden":
        if "classifier_reasons" in row:
            return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}].classifier_reasons"
        return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]"
    if name == "evidence_burden":
        return _artifact_pointer(artifact, row.get("evidence_pointer"))
    if name == "backend_coupling":
        return _artifact_pointer(artifact, row.get("control_pointer"))
    if name == "witness_exposure":
        pointer = row.get("adversarial_pointer") or row.get("negative_report_pointer")
        if isinstance(pointer, str) and ":" in pointer:
            return pointer
        return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]"
    if name == "revocation_fragility":
        return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}].projection_status"
    raise ValueError(f"unknown complexity dimension: {name}")


def _row_from_discovery(index: int, discovery: Mapping[str, Any], verdict_refs: Mapping[str, str]) -> ClaimComplexityRow:
    report = discovery.get("report")
    if not isinstance(report, str) or not report:
        raise ValueError(f"discovery row needs report: {index}")
    if not isinstance(discovery.get("json_artifact"), str):
        raise ValueError(f"discovery row needs json_artifact: {report}")
    claim_id = f"claim:{report}"
    verdict_ref = verdict_refs.get(claim_id)
    if verdict_ref is None:
        raise ValueError(f"claim verdict ref missing for {claim_id}")
    dimensions = [
        {
            "name": name,
            "weight": _weight_for(name, discovery),
            "evidence_pointer": _dimension_pointer(name, index, discovery),
        }
        for name in DIMENSION_NAMES
    ]
    return ClaimComplexityRow(
        claim_id=claim_id,
        complexity_score=sum(int(item["weight"]) for item in dimensions),
        scoring_dimensions=dimensions,
        pointer_only_verdict_ref=verdict_ref,
        not_claimed="Complexity score is artifact-only evidence and does not own terminal verdict authority.",
    )


def _hardgates(root: Path, rows: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    unresolved: list[str] = []
    missing_d5m: list[str] = []
    d4_rows = 0
    for row in rows:
        for dimension in row["scoring_dimensions"]:
            pointer = dimension["evidence_pointer"]
            if resolve_artifact_pointer(root, pointer) is None:
                unresolved.append(pointer)
        verdict_ref = row["pointer_only_verdict_ref"]
        verdict = resolve_claim_verdict_ref(root, verdict_ref)
        if verdict is None:
            unresolved.append(verdict_ref)
        level = resolve_artifact_pointer(
            root,
            f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{_row_index_from_claim(root, row['claim_id'])}].discovery_level",
        )
        if level == "D5-M":
            names = {item["name"] for item in row["scoring_dimensions"]}
            missing = [name for name in DIMENSION_NAMES if name not in names]
            missing_d5m.extend(f"{row['claim_id']}:{name}" for name in missing)
        if level == "D4":
            d4_rows += 1
    return {
        "CC-HG1": ClaimComplexityAudit(
            "CC-HG1",
            "fail" if unresolved else "pass",
            "all evidence and verdict pointers resolve" if not unresolved else "unresolved pointers",
            None,
        ).as_payload()
        | {"unresolved_pointers": unresolved},
        "CC-HG2": ClaimComplexityAudit(
            "CC-HG2",
            "fail" if missing_d5m else "pass",
            "D5-M rows carry all required dimensions" if not missing_d5m else "D5-M required dimensions missing",
            None,
        ).as_payload()
        | {"missing_required": missing_d5m},
        "CC-HG3": ClaimComplexityAudit(
            "CC-HG3",
            "pass",
            "D4 rows pass through without promotion authority",
            f"{DISCOVERY_MAP_ARTIFACT}:$.rows",
        ).as_payload()
        | {"d4_row_count": d4_rows},
    }


def _row_index_from_claim(root: Path, claim_id: str) -> int:
    discovery = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_ARTIFACT)
    rows = discovery.get("rows") if isinstance(discovery, Mapping) else None
    if not isinstance(rows, list):
        return -1
    report = claim_id.removeprefix("claim:")
    for index, row in enumerate(rows):
        if isinstance(row, Mapping) and row.get("report") == report:
            return index
    return -1


def build_claim_complexity_payload(root: Path, generated_at: str | None) -> dict[str, Any]:
    discovery = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_ARTIFACT)
    discovery_rows = discovery.get("rows") if isinstance(discovery, Mapping) else None
    if not isinstance(discovery_rows, list) or not all(isinstance(row, Mapping) for row in discovery_rows):
        raise ValueError("discovery map must expose object rows")
    verdict_refs = _claim_verdict_refs(root)
    rows = [_row_from_discovery(index, row, verdict_refs).as_payload() for index, row in enumerate(discovery_rows)]
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "source_artifacts": {
            "discovery_map": DISCOVERY_MAP_ARTIFACT,
            "claim_verdicts": CLAIM_VERDICTS_ARTIFACT,
        },
        "rows": rows,
        "hardgates": _hardgates(root, rows),
        "not_claimed": [
            "Does not own terminal verdict facts.",
            "Does not copy claim verdict payload fields.",
            "Does not read host-local environment files.",
        ],
    }
    errors = validate_claim_complexity_payload(root, payload)
    if errors:
        raise ValueError("; ".join(errors))
    return payload


def _is_forbidden_host_ref(value: Any) -> bool:
    if isinstance(value, Mapping):
        return any(_is_forbidden_host_ref(key) or _is_forbidden_host_ref(item) for key, item in value.items())
    if isinstance(value, list):
        return any(_is_forbidden_host_ref(item) for item in value)
    if isinstance(value, str):
        return ".refactor-loop/host.env" in value or value.startswith("/Users/")
    return False


def validate_claim_complexity_payload(root: Path, payload: Mapping[str, Any]) -> list[str]:
    errors: list[str] = []
    if frozenset(payload) != TOP_LEVEL_KEYS:
        errors.append("top-level schema mismatch")
    if payload.get("schema_id") != SCHEMA_ID:
        errors.append("schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        errors.append("artifact_id mismatch")
    if _is_forbidden_host_ref(payload):
        errors.append("host-local reference is forbidden")
    rows = payload.get("rows")
    if not isinstance(rows, list):
        errors.append("rows must be a list")
        rows = []
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            errors.append(f"row must be object: {index}")
            continue
        if frozenset(row) != ROW_KEYS:
            errors.append(f"row schema mismatch: {index}")
        if set(row) & VERDICT_PAYLOAD_KEYS:
            errors.append(f"row copies verdict payload keys: {index}")
        dimensions = row.get("scoring_dimensions")
        if not isinstance(dimensions, list):
            errors.append(f"dimensions must be a list: {index}")
            continue
        names = [item.get("name") for item in dimensions if isinstance(item, Mapping)]
        if tuple(names) != DIMENSION_NAMES:
            errors.append(f"six dimensions must appear exactly once in order: {index}")
        score = 0
        for dimension in dimensions:
            if not isinstance(dimension, Mapping):
                errors.append(f"dimension must be object: {index}")
                continue
            if frozenset(dimension) != DIMENSION_KEYS:
                errors.append(f"dimension schema mismatch: {index}")
            weight = dimension.get("weight")
            if not isinstance(weight, int):
                errors.append(f"dimension weight must be int: {index}")
            else:
                score += weight
            pointer = dimension.get("evidence_pointer")
            if not isinstance(pointer, str) or resolve_artifact_pointer(root, pointer) is None:
                errors.append(f"dimension pointer unresolved: {index}:{dimension.get('name')}")
        if row.get("complexity_score") != score:
            errors.append(f"complexity score mismatch: {index}")
        verdict_ref = row.get("pointer_only_verdict_ref")
        if not isinstance(verdict_ref, str) or resolve_claim_verdict_ref(root, verdict_ref) is None:
            errors.append(f"verdict ref unresolved: {index}")
    hardgates = payload.get("hardgates")
    if not isinstance(hardgates, Mapping):
        errors.append("hardgates must be an object")
    else:
        for gate_id in ("CC-HG1", "CC-HG2", "CC-HG3"):
            gate = hardgates.get(gate_id)
            if not isinstance(gate, Mapping):
                errors.append(f"hardgate missing: {gate_id}")
            elif gate.get("status") not in {"pass", "fail"}:
                errors.append(f"hardgate status invalid: {gate_id}")
    return errors


def render_claim_complexity_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Claim Complexity",
        "",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Generated at: `{payload['generated_at']}`",
        "- Role: `artifact-only evidence`",
        "",
        "## Hardgates",
        "",
        "| gate | status | reason |",
        "| --- | --- | --- |",
    ]
    for gate_id, gate in sorted(payload["hardgates"].items()):
        lines.append(f"| `{gate_id}` | `{gate['status']}` | `{gate['reason']}` |")
    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| claim | score | verdict ref | dimensions |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in payload["rows"]:
        dimensions = ", ".join(f"{item['name']}={item['weight']}" for item in row["scoring_dimensions"])
        lines.append(
            "| "
            f"`{row['claim_id']}` | "
            f"`{row['complexity_score']}` | "
            f"`{row['pointer_only_verdict_ref']}` | "
            f"`{dimensions}` |"
        )
    lines.append("")
    return "\n".join(lines)

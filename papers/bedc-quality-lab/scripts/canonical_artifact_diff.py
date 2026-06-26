#!/usr/bin/env python3
"""Audit PR-time canonical artifact diffs with pinned verdict declarations."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
from typing import Any, Mapping


SCHEMA_ID = "bedc-quality-lab:canonical-artifact-diff-check"
CLAIM_VERDICTS_DEFAULT = "reports/canonical/claim_verdicts.jsonl"
DISCOVERY_MAP_DEFAULT = "reports/canonical/discovery_map.json"
CANONICAL_DIFF_RE = re.compile(r"(?m)^```canonical-diff[ \t]*\n(?P<body>.*?)^```[ \t]*$", re.DOTALL)
ANY_FENCE_RE = re.compile(r"(?m)^```(?P<lang>[A-Za-z0-9_-]+)[ \t]*\n.*?^```[ \t]*$", re.DOTALL)
DECLARATION_HEADER = ("claim_id", "from", "to", "reason")


@dataclass(frozen=True)
class CanonicalDiffDeclaration:
    claim_id: str
    from_verdict: str | None
    to_verdict: str | None

    @property
    def key(self) -> tuple[str, str | None, str | None]:
        return (self.claim_id, self.from_verdict, self.to_verdict)


@dataclass(frozen=True)
class _IndexSource:
    index: Mapping[str, Any]
    root: Path


def _load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _index_root(path: Path) -> Path:
    parts = path.parts
    suffix = ("reports", "canonical", "index.json")
    if len(parts) >= 3 and tuple(parts[-3:]) == suffix:
        return Path(*parts[:-3]) if parts[:-3] else Path(".")
    return path.parent


def _coerce_index(source: Mapping[str, Any] | str | Path) -> _IndexSource:
    if isinstance(source, Mapping):
        return _IndexSource(index=source, root=Path.cwd())
    path = Path(source)
    return _IndexSource(index=_load_json(path), root=_index_root(path))


def _safe_artifact_path(root: Path, artifact: str) -> Path | None:
    if not artifact or _is_excluded_artifact(artifact):
        return None
    path = Path(artifact)
    if path.is_absolute() or ".." in path.parts:
        return None
    return root / path


def _is_excluded_artifact(artifact: str) -> bool:
    return (
        artifact.startswith(".refactor-loop/")
        or artifact == ".refactor-loop"
        or artifact.startswith("reports/canonical/artifact-diff-audit.")
    )


def _row_has_excluded_artifact(row: Mapping[str, Any]) -> bool:
    for value in row.values():
        if isinstance(value, str) and _is_excluded_artifact(value):
            return True
    return False


def _row_artifact(row_name: str, row: Mapping[str, Any]) -> str:
    for key in (
        "json_artifact",
        "jsonl_artifact",
        "markdown_artifact",
        "fingerprint_artifact",
        "source_index_artifact",
        "schema_artifact",
        "spec_artifact",
    ):
        value = row.get(key)
        if isinstance(value, str) and value:
            return value
    return str(row.get("artifact_id") or row_name)


def _canonical_rows(index: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    rows: dict[str, Mapping[str, Any]] = {}
    for name, row in index.items():
        if name == "generated_at" or not isinstance(row, Mapping):
            continue
        if _row_has_excluded_artifact(row):
            continue
        rows[name] = row
    return rows


def _row_transition(kind: str, name: str, row: Mapping[str, Any] | None) -> dict[str, Any]:
    return {
        "status": "diagnostic",
        "gate": "ADIFF-HG4",
        "kind": kind,
        "name": name,
        "artifact_path": _row_artifact(name, row or {}),
    }


def _index_row_transitions(base: Mapping[str, Any], head: Mapping[str, Any]) -> list[dict[str, Any]]:
    base_rows = _canonical_rows(base)
    head_rows = _canonical_rows(head)
    transitions: list[dict[str, Any]] = []
    for name in sorted(set(base_rows) | set(head_rows)):
        if name not in base_rows:
            transitions.append(_row_transition("added", name, head_rows[name]))
        elif name not in head_rows:
            transitions.append(_row_transition("deleted", name, base_rows[name]))
        elif base_rows[name] != head_rows[name]:
            transitions.append(_row_transition("changed", name, head_rows[name]))
    return transitions


def _fingerprint_artifacts(index: Mapping[str, Any]) -> dict[str, str]:
    artifacts: dict[str, str] = {}
    for name, row in _canonical_rows(index).items():
        value = row.get("fingerprint_artifact")
        if isinstance(value, str) and value:
            artifacts[name] = value
    return artifacts


def _fingerprint_transitions(base: _IndexSource, head: _IndexSource) -> list[dict[str, Any]]:
    base_artifacts = _fingerprint_artifacts(base.index)
    head_artifacts = _fingerprint_artifacts(head.index)
    transitions: list[dict[str, Any]] = []
    for name in sorted(set(base_artifacts) | set(head_artifacts)):
        base_artifact = base_artifacts.get(name)
        head_artifact = head_artifacts.get(name)
        base_payload = _read_optional_json(base.root, base_artifact)
        head_payload = _read_optional_json(head.root, head_artifact)
        if base_artifact != head_artifact or base_payload != head_payload:
            transitions.append(
                {
                    "status": "diagnostic",
                    "gate": "ADIFF-HG4",
                    "kind": "fingerprint",
                    "name": name,
                    "artifact_path": head_artifact or base_artifact,
                }
            )
    return transitions


def _read_optional_json(root: Path, artifact: str | None) -> Any:
    if artifact is None:
        return None
    path = _safe_artifact_path(root, artifact)
    if path is None or not path.exists():
        return None
    return _load_json(path)


def _claim_verdict_artifact(index: Mapping[str, Any]) -> str:
    row = index.get("claim_verdicts")
    if isinstance(row, Mapping):
        value = row.get("jsonl_artifact")
        if isinstance(value, str) and value:
            return value
    return CLAIM_VERDICTS_DEFAULT


def _claim_verdicts(source: _IndexSource) -> dict[str, str]:
    artifact = _claim_verdict_artifact(source.index)
    path = _safe_artifact_path(source.root, artifact)
    if path is None or not path.exists():
        return {}
    verdicts: dict[str, str] = {}
    with path.open("r", encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            stripped = line.strip()
            if not stripped:
                continue
            row = json.loads(stripped)
            claim_id = row.get("claim_id")
            verdict = row.get("claim_verdict")
            if isinstance(claim_id, str) and isinstance(verdict, str):
                verdicts[claim_id] = verdict
            else:
                raise ValueError(f"{artifact}:{line_number} missing claim_id or claim_verdict")
    return verdicts


def _verdict_transitions(base: _IndexSource, head: _IndexSource) -> list[dict[str, Any]]:
    base_verdicts = _claim_verdicts(base)
    head_verdicts = _claim_verdicts(head)
    transitions: list[dict[str, Any]] = []
    for claim_id in sorted(set(base_verdicts) | set(head_verdicts)):
        from_verdict = base_verdicts.get(claim_id)
        to_verdict = head_verdicts.get(claim_id)
        if from_verdict == to_verdict:
            continue
        if from_verdict is None:
            gate = "ADIFF-HG2"
            kind = "added"
        elif to_verdict is None:
            gate = "ADIFF-HG3"
            kind = "deleted"
        else:
            gate = "ADIFF-HG1"
            kind = "changed"
        transitions.append(
            {
                "claim_id": claim_id,
                "from": from_verdict,
                "to": to_verdict,
                "kind": kind,
                "gate": gate,
            }
        )
    return transitions


def _discovery_map_artifact(index: Mapping[str, Any]) -> str:
    row = index.get("discovery_map")
    if isinstance(row, Mapping):
        value = row.get("json_artifact")
        if isinstance(value, str) and value:
            return value
    return DISCOVERY_MAP_DEFAULT


def _coverage_cells(source: _IndexSource) -> dict[str, Any]:
    artifact = _discovery_map_artifact(source.index)
    payload = _read_optional_json(source.root, artifact)
    if not isinstance(payload, Mapping):
        return {}
    coverage = payload.get("coverage_matrix")
    if not isinstance(coverage, Mapping):
        return {}
    cells = coverage.get("cells")
    if not isinstance(cells, list):
        return {}
    keyed: dict[str, Any] = {}
    for index, cell in enumerate(cells):
        if not isinstance(cell, Mapping):
            continue
        key = cell.get("component_id") or cell.get("surface_id") or cell.get("claim_id") or str(index)
        keyed[str(key)] = cell
    return keyed


def _coverage_transitions(base: _IndexSource, head: _IndexSource) -> list[dict[str, Any]]:
    base_cells = _coverage_cells(base)
    head_cells = _coverage_cells(head)
    transitions: list[dict[str, Any]] = []
    for key in sorted(set(base_cells) | set(head_cells)):
        from_cell = base_cells.get(key)
        to_cell = head_cells.get(key)
        if from_cell == to_cell:
            continue
        transitions.append(
            {
                "status": "diagnostic",
                "gate": "ADIFF-HG4",
                "cell_id": key,
                "from": from_cell,
                "to": to_cell,
            }
        )
    return transitions


def _decode_verdict(value: str) -> str | None:
    stripped = value.strip()
    if stripped == "null":
        return None
    return stripped


def _parse_declarations(markdown: str) -> tuple[list[CanonicalDiffDeclaration], dict[str, Any]]:
    blocks = list(CANONICAL_DIFF_RE.finditer(markdown or ""))
    fenced_languages = [match.group("lang") for match in ANY_FENCE_RE.finditer(markdown or "")]
    diagnostics: dict[str, Any] = {
        "status": "pass",
        "gate": "ADIFF-HG5",
        "block_count": len(blocks),
        "ignored_fence_languages": sorted(lang for lang in fenced_languages if lang != "canonical-diff"),
        "errors": [],
    }
    if not markdown:
        diagnostics["status"] = "missing"
        return [], diagnostics
    if len(blocks) != 1:
        diagnostics["status"] = "invalid"
        diagnostics["errors"].append("expected exactly one canonical-diff fenced block")
        return [], diagnostics

    raw_lines = [line.strip() for line in blocks[0].group("body").splitlines() if line.strip()]
    if not raw_lines:
        diagnostics["status"] = "invalid"
        diagnostics["errors"].append("canonical-diff block is empty")
        return [], diagnostics
    header = tuple(part.strip() for part in raw_lines[0].split("|"))
    if header != DECLARATION_HEADER:
        diagnostics["status"] = "invalid"
        diagnostics["errors"].append("canonical-diff header must be: claim_id | from | to | reason")
        return [], diagnostics

    declarations: list[CanonicalDiffDeclaration] = []
    for line_number, line in enumerate(raw_lines[1:], start=2):
        parts = [part.strip() for part in line.split("|")]
        if len(parts) != 4 or not all(parts):
            diagnostics["status"] = "invalid"
            diagnostics["errors"].append(f"line {line_number} must have four non-empty columns")
            return [], diagnostics
        claim_id, from_verdict, to_verdict, reason = parts
        declarations.append(
            CanonicalDiffDeclaration(
                claim_id=claim_id,
                from_verdict=_decode_verdict(from_verdict),
                to_verdict=_decode_verdict(to_verdict),
            )
        )
    return declarations, diagnostics


def _hardgate(verdict_transitions: list[dict[str, Any]], declaration_keys: set[tuple[str, str | None, str | None]], parse_status: str) -> dict[str, Any]:
    missing: list[dict[str, Any]] = []
    for transition in verdict_transitions:
        key = (transition["claim_id"], transition["from"], transition["to"])
        if key not in declaration_keys:
            missing.append(transition)

    gates = {
        "ADIFF-HG1": {"status": "pass", "reason": "changed verdict rows are declared"},
        "ADIFF-HG2": {"status": "pass", "reason": "added verdict rows are declared"},
        "ADIFF-HG3": {"status": "pass", "reason": "deleted verdict rows are declared"},
        "ADIFF-HG4": {"status": "diagnostic", "reason": "non-verdict canonical diffs are diagnostics"},
        "ADIFF-HG5": {"status": "pass", "reason": "canonical-diff declaration boundary is valid when required"},
    }
    for transition in missing:
        gates[transition["gate"]] = {
            "status": "fail",
            "reason": "claim verdict transition lacks an exact canonical-diff declaration",
        }
    if verdict_transitions and parse_status != "pass":
        gates["ADIFF-HG5"] = {
            "status": "fail",
            "reason": "claim verdict transitions require one well-formed canonical-diff block",
        }

    failed = sorted(name for name, row in gates.items() if row["status"] == "fail")
    return {
        "status": "fail" if failed else "pass",
        "failed_gates": failed,
        "gates": gates,
        "missing_declarations": missing,
    }


def audit_canonical_artifact_diff(
    base_index: Mapping[str, Any] | str | Path,
    head_index: Mapping[str, Any] | str | Path,
    *,
    pr_body: str = "",
) -> dict[str, Any]:
    base = _coerce_index(base_index)
    head = _coerce_index(head_index)
    declarations, declaration_diagnostics = _parse_declarations(pr_body)
    declaration_keys = {declaration.key for declaration in declarations}
    verdict_transitions = _verdict_transitions(base, head)
    coverage_transitions = _coverage_transitions(base, head)
    index_row_transitions = _index_row_transitions(base.index, head.index)
    fingerprint_transitions = _fingerprint_transitions(base, head)

    hardgate = _hardgate(verdict_transitions, declaration_keys, declaration_diagnostics["status"])
    return {
        "schema_id": SCHEMA_ID,
        "hardgate": hardgate,
        "declaration_diagnostics": declaration_diagnostics,
        "declared_transitions": [
            {"claim_id": item.claim_id, "from": item.from_verdict, "to": item.to_verdict}
            for item in declarations
        ],
        "claim_verdict_transitions": verdict_transitions,
        "coverage_transitions": coverage_transitions,
        "index_row_transitions": index_row_transitions,
        "fingerprint_transitions": fingerprint_transitions,
        "diagnostics": {
            "ADIFF-HG4": {
                "status": "diagnostic",
                "coverage_transition_count": len(coverage_transitions),
                "index_row_transition_count": len(index_row_transitions),
                "fingerprint_transition_count": len(fingerprint_transitions),
            }
        },
    }


def _read_text(path: str | None) -> str:
    if path is None:
        return ""
    return Path(path).read_text(encoding="utf-8")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-index", required=True, help="Base reports/canonical/index.json path")
    parser.add_argument("--head-index", required=True, help="Head reports/canonical/index.json path")
    parser.add_argument("--pr-body", help="Markdown file containing the PR body")
    parser.add_argument("--output", help="Optional JSON output path")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    result = audit_canonical_artifact_diff(args.base_index, args.head_index, pr_body=_read_text(args.pr_body))
    rendered = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        Path(args.output).write_text(rendered + "\n", encoding="utf-8")
    else:
        print(rendered)
    return 1 if result["hardgate"]["status"] == "fail" else 0


if __name__ == "__main__":
    raise SystemExit(main())

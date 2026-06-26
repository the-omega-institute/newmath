#!/usr/bin/env python3
"""Check BEDC paper artifact markers against the canonical consistency owner."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
LAB_ROOT = REPO_ROOT / "papers" / "bedc-quality-lab"
SOURCE_REGISTRY = ROOT / "paper_artifact_sources.json"
OWNER_ARTIFACT = LAB_ROOT / "reports/canonical/claim-artifact-consistency.json"
PAPER_SURFACE_TYPES = frozenset({"table", "figure", "main_claim_chain"})
PAPER_VALUE_TRANSFORMS = frozenset({"number", "integer", "string"})
MARKER_RE = re.compile(
    r"\\paperartifact\{(?P<surface>[^{}]+)\}\{(?P<value>[^{}]+)\}\{(?P<literal>[^{}]+)\}"
)


@dataclass(frozen=True)
class PaperArtifactFinding:
    status: str
    reason: str
    surface_id: str
    value_id: str
    pointer: str
    expected: str
    actual: str

    def to_text(self) -> str:
        return (
            f"{self.status}: {self.reason}: surface={self.surface_id} value={self.value_id} "
            f"pointer={self.pointer} expected={self.expected} actual={self.actual}"
        )


@dataclass(frozen=True)
class PaperArtifactMarker:
    surface_id: str
    value_id: str
    paper_literal: str
    source_path: str
    line: int

    @property
    def key(self) -> tuple[str, str]:
        return self.surface_id, self.value_id

    @property
    def pointer(self) -> str:
        return f"{self.source_path}:{self.line}"


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _source_roots(root: Path) -> tuple[Path, ...]:
    registry = root / "paper_artifact_sources.json"
    if not registry.exists():
        return (root / "parts", root / "frontmatter", root / "appendices")
    payload = _load_json(registry)
    if not isinstance(payload, Mapping):
        raise ValueError("paper artifact source registry must be a JSON object")
    roots = payload.get("source_roots", ["parts", "frontmatter", "appendices"])
    if not isinstance(roots, list) or not all(isinstance(item, str) for item in roots):
        raise ValueError("paper artifact source registry source_roots must be string list")
    out: list[Path] = []
    for item in roots:
        path = root / item
        if path.exists():
            out.append(path)
    return tuple(out)


def _scan_markers(root: Path) -> list[PaperArtifactMarker]:
    markers: list[PaperArtifactMarker] = []
    for source_root in _source_roots(root):
        for path in sorted(source_root.rglob("*.tex")):
            relative = path.relative_to(root).as_posix()
            for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
                for match in MARKER_RE.finditer(line):
                    markers.append(
                        PaperArtifactMarker(
                            surface_id=match.group("surface"),
                            value_id=match.group("value"),
                            paper_literal=match.group("literal"),
                            source_path=relative,
                            line=line_number,
                        )
                    )
    return markers


def _is_forbidden_pointer(pointer: Any) -> bool:
    if pointer is None:
        return False
    if not isinstance(pointer, str) or not pointer:
        return True
    if "://" in pointer or pointer.startswith(("/", "~")):
        return True
    artifact = pointer.split(":", 1)[0]
    parts = Path(artifact).parts
    return ".." in parts or ".refactor-loop" in parts


def _resolve_pointer_value(pointer: Any, *, owner_root: Path) -> Any:
    if not isinstance(pointer, str) or _is_forbidden_pointer(pointer):
        return None
    artifact, _, local_pointer = pointer.partition(":")
    if not artifact or not local_pointer.startswith("$"):
        return None
    path = owner_root / artifact
    if not path.exists():
        return None
    try:
        if artifact.endswith(".jsonl"):
            rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]
            return _pointer_value({"lines": rows}, local_pointer)
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if local_pointer == "$":
        return payload
    return _pointer_value(payload, local_pointer)


def _pointer_resolves(pointer: Any, *, owner_root: Path) -> bool:
    return _resolve_pointer_value(pointer, owner_root=owner_root) is not None


def _pointer_value(payload: Any, pointer: str) -> Any:
    if pointer == "$":
        return payload
    if not pointer.startswith("$."):
        return None
    cursor = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(cursor, Mapping) or key not in cursor:
                    return None
                cursor = cursor[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(cursor, list):
                return None
            index = int(index_text)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            part = ""
        if not part:
            continue
        if isinstance(cursor, Mapping) and part in cursor:
            cursor = cursor[part]
        elif isinstance(cursor, list) and part.isdigit() and int(part) < len(cursor):
            cursor = cursor[int(part)]
        else:
            return None
    return cursor


def _numeric_equal(expected: str, actual: str, tolerance: float) -> bool:
    try:
        return abs(float(expected) - float(actual)) <= float(tolerance)
    except (TypeError, ValueError):
        return False


def _integer_value(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return int(value) if value.is_integer() else None
    if isinstance(value, str):
        text = value.strip()
        if re.fullmatch(r"[+-]?\d+", text):
            return int(text)
        try:
            numeric = float(text)
        except ValueError:
            return None
        return int(numeric) if numeric.is_integer() else None
    return None


def _coerce_tolerance(value: Any) -> float | None:
    try:
        tolerance = float(value)
    except (TypeError, ValueError):
        return None
    return tolerance if tolerance >= 0.0 else None


def _literal_matches(owner_value: Mapping[str, Any], marker: PaperArtifactMarker, *, owner_root: Path) -> bool:
    actual = _resolve_pointer_value(owner_value.get("artifact_pointer"), owner_root=owner_root)
    if actual is None:
        return True
    transform = owner_value.get("transform")
    tolerance = _coerce_tolerance(owner_value.get("tolerance", 0.0))
    if transform == "integer":
        marker_value = _integer_value(marker.paper_literal)
        actual_value = _integer_value(actual)
        return marker_value is not None and actual_value is not None and marker_value == actual_value
    if transform == "number" and tolerance is not None:
        return _numeric_equal(str(actual), marker.paper_literal, tolerance)
    if transform == "string":
        return str(actual) == marker.paper_literal
    return False


def _owner_payload(owner_root: Path) -> Mapping[str, Any]:
    path = owner_root / "reports/canonical/claim-artifact-consistency.json"
    if not path.exists():
        return {"_owner_artifact_missing": True, "paper_surfaces": []}
    payload = _load_json(path)
    if not isinstance(payload, Mapping):
        return {"_owner_artifact_malformed": type(payload).__name__, "paper_surfaces": []}
    if "paper_surfaces" not in payload:
        return dict(payload) | {"paper_surfaces": []}
    return payload


def _findings_for_owner_payload(root: Path, owner_payload: Mapping[str, Any], *, owner_root: Path) -> list[PaperArtifactFinding]:
    markers = _scan_markers(root)
    findings: list[PaperArtifactFinding] = []
    if owner_payload.get("_owner_artifact_missing") is True:
        return [
            PaperArtifactFinding(
                "fail",
                "owner artifact is missing",
                "",
                "",
                "reports/canonical/claim-artifact-consistency.json:$",
                "claim-artifact-consistency owner artifact",
                "missing",
            )
        ]
    if owner_payload.get("_owner_artifact_malformed") is not None:
        return [
            PaperArtifactFinding(
                "fail",
                "owner artifact is malformed",
                "",
                "",
                "reports/canonical/claim-artifact-consistency.json:$",
                "JSON object",
                str(owner_payload.get("_owner_artifact_malformed")),
            )
        ]
    surfaces = owner_payload.get("paper_surfaces")
    if not isinstance(surfaces, list):
        return [
            PaperArtifactFinding(
                "fail",
                "missing owner paper_surfaces",
                "",
                "",
                "reports/canonical/claim-artifact-consistency.json:$.paper_surfaces",
                "paper_surfaces list",
                str(type(surfaces).__name__),
            )
        ]
    if owner_payload.get("status") not in {None, "pass"}:
        return [
            PaperArtifactFinding(
                "fail",
                "owner status is not pass",
                "",
                "",
                "reports/canonical/claim-artifact-consistency.json:$.status",
                "pass",
                str(owner_payload.get("status")),
            )
        ]
    surface_by_id: dict[str, Mapping[str, Any]] = {}
    invalid_value_keys: set[tuple[str, str]] = set()
    for surface in surfaces:
        if not isinstance(surface, Mapping):
            continue
        surface_id = surface.get("surface_id")
        if not isinstance(surface_id, str):
            continue
        if surface_id in surface_by_id:
            findings.append(
                PaperArtifactFinding("fail", "duplicate owner paper surface", surface_id, "", surface_id, "unique surface_id", surface_id)
            )
        surface_by_id[surface_id] = surface
        surface_type = surface.get("surface_type")
        if surface_type not in PAPER_SURFACE_TYPES:
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "invalid owner paper surface type",
                    surface_id,
                    "",
                    surface_id,
                    ", ".join(sorted(PAPER_SURFACE_TYPES)),
                    str(surface_type),
                )
            )
        if not isinstance(surface.get("artifact_pointer"), str) or not surface.get("artifact_pointer"):
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "missing owner surface artifact pointer",
                    surface_id,
                    "",
                    f"{surface_id}.artifact_pointer",
                    "repo-local artifact pointer",
                    str(surface.get("artifact_pointer")),
                )
            )
        for field in ("artifact_pointer", "claim_pointer", "hardgate_pointer", "not_claimed_pointer"):
            pointer = surface.get(field)
            if _is_forbidden_pointer(pointer):
                findings.append(
                    PaperArtifactFinding("fail", "forbidden artifact pointer", surface_id, "", str(pointer), "repo-local pointer", str(pointer))
                )
            elif pointer is not None and not _pointer_resolves(pointer, owner_root=owner_root):
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "unresolved artifact pointer",
                        surface_id,
                        "",
                        str(pointer),
                        "resolving artifact pointer",
                        str(pointer),
                    )
                )
        values = surface.get("values")
        if not isinstance(values, list):
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "missing owner surface values",
                    surface_id,
                    "",
                    f"{surface_id}.values",
                    "values list",
                    str(type(values).__name__),
                )
            )
            continue
        seen_value_ids: set[str] = set()
        for value in values:
            if not isinstance(value, Mapping):
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "malformed owner value row",
                        surface_id,
                        "",
                        f"{surface_id}.values",
                        "value object",
                        str(type(value).__name__),
                    )
                )
                continue
            value_id = value.get("value_id")
            if not isinstance(value_id, str) or not value_id:
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "malformed owner value row",
                        surface_id,
                        str(value_id),
                        str(value.get("artifact_pointer", "")),
                        "non-empty value_id",
                        str(value_id),
                    )
                )
                continue
            if value_id in seen_value_ids:
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "duplicate owner value row",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer", "")),
                        "unique value_id",
                        value_id,
                    )
                )
            seen_value_ids.add(value_id)
            transform = value.get("transform")
            if transform not in PAPER_VALUE_TRANSFORMS:
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "invalid owner value transform",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer", "")),
                        ", ".join(sorted(PAPER_VALUE_TRANSFORMS)),
                        str(transform),
                    )
                )
                invalid_value_keys.add((surface_id, value_id))
                continue
            tolerance = _coerce_tolerance(value.get("tolerance", 0.0))
            if tolerance is None:
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "invalid owner value tolerance",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer", "")),
                        "nonnegative number",
                        str(value.get("tolerance")),
                    )
                )
                invalid_value_keys.add((surface_id, value_id))
                continue
            if _is_forbidden_pointer(value.get("artifact_pointer")):
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "forbidden artifact pointer",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer")),
                        "repo-local pointer",
                        str(value.get("artifact_pointer")),
                    )
                )
            elif not _pointer_resolves(value.get("artifact_pointer"), owner_root=owner_root):
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "unresolved artifact pointer",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer")),
                        "resolving artifact pointer",
                        str(value.get("artifact_pointer")),
                    )
                )
    seen_markers: set[tuple[str, str]] = set()
    for marker in markers:
        if marker.key in seen_markers:
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "duplicate paper artifact marker",
                    marker.surface_id,
                    marker.value_id,
                    marker.pointer,
                    "single source marker",
                    marker.paper_literal,
                )
            )
            continue
        seen_markers.add(marker.key)
        surface = surface_by_id.get(marker.surface_id)
        if surface is None:
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "paper marker has no owner surface row",
                    marker.surface_id,
                    marker.value_id,
                    marker.pointer,
                    "owner surface row",
                    marker.paper_literal,
                )
            )
            continue
        values = surface.get("values")
        value_by_id = (
            {str(value.get("value_id")): value for value in values if isinstance(value, Mapping)}
            if isinstance(values, list)
            else {}
        )
        owner_value = value_by_id.get(marker.value_id)
        if owner_value is None:
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "paper marker has no owner value row",
                    marker.surface_id,
                    marker.value_id,
                    marker.pointer,
                    "owner value row",
                    marker.paper_literal,
                )
            )
            continue
        if marker.key in invalid_value_keys:
            continue
        if not _literal_matches(owner_value, marker, owner_root=owner_root):
            expected = _resolve_pointer_value(owner_value.get("artifact_pointer"), owner_root=owner_root)
            findings.append(
                PaperArtifactFinding(
                    "fail",
                    "paper literal mismatch",
                    marker.surface_id,
                    marker.value_id,
                    marker.pointer,
                    str(expected),
                    marker.paper_literal,
                )
            )
    for surface_id, surface in surface_by_id.items():
        values = surface.get("values")
        if not isinstance(values, list):
            continue
        for value in values:
            if not isinstance(value, Mapping):
                continue
            value_id = value.get("value_id")
            if not isinstance(value_id, str):
                continue
            if (surface_id, value_id) not in seen_markers:
                findings.append(
                    PaperArtifactFinding(
                        "fail",
                        "owner value has no paper marker",
                        surface_id,
                        value_id,
                        str(value.get("artifact_pointer", "")),
                        "single source marker",
                        value_id,
                    )
                )
    return findings


def check_paper_artifacts(
    root: Path = ROOT,
    *,
    owner_payload: Mapping[str, Any] | None = None,
    owner_root: Path = LAB_ROOT,
) -> list[PaperArtifactFinding]:
    root = Path(root)
    resolved_owner_root = Path(owner_root)
    payload = owner_payload if owner_payload is not None else _owner_payload(resolved_owner_root)
    return _findings_for_owner_payload(root, payload, owner_root=resolved_owner_root)


def main(argv: Sequence[str] | None = None) -> int:
    findings = check_paper_artifacts(ROOT)
    for finding in findings:
        print(finding.to_text())
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())

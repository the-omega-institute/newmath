#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
from typing import Any, Literal


SCHEMA_ID = "bedc-quality-lab:release-manifest-sidecar"
ARTIFACT_ID = SCHEMA_ID
CANONICAL_ROLE = "sidecar_not_in_CANONICAL_REPORTS"
JSON_ARTIFACT = "reports/release_manifest_sidecar.json"
MARKDOWN_ARTIFACT = "reports/release_manifest_sidecar.md"
NOT_CLAIMED = (
    "tag_status is falsifiable metadata, not a release-quality proof",
    "not the release tag itself",
    "not lab bundle release-ready unless all required pointers and the tag predicate resolve",
    "not a positive scientific result",
    "not model-quality evidence",
    "not a BEDC closure, NameCert, or scorecard upgrade",
    "not a substitute for PR-3 or PR-6 hardening coverage",
)
REVOKE_IF = (
    "Revoke ready status if any required pointer stops resolving, "
    "the requested tag becomes stale, or this sidecar is used as report status evidence."
)


PointerStatus = Literal["resolved", "missing"]
TagStatus = Literal["absent", "present", "stale", "unknown"]
ReleaseBundleStatus = Literal["ready", "not-ready"]


@dataclass(frozen=True)
class ReleasePointerRow:
    id: str
    path: str
    pointer: str
    status: PointerStatus
    failure: str | None

    def to_payload(self) -> dict[str, Any]:
        return {
            "id": self.id,
            "path": self.path,
            "pointer": self.pointer,
            "status": self.status,
            "failure": self.failure,
        }


@dataclass(frozen=True)
class ReleaseManifestSidecar:
    schema_id: str
    artifact_id: str
    canonical_role: str
    generated_at: str
    version: str
    tag_ref: str | None
    release_bundle_status: ReleaseBundleStatus
    tag_status: TagStatus
    source_pointers: dict[str, dict[str, str]]
    required_pointers: tuple[ReleasePointerRow, ...]
    not_claimed: tuple[str, ...]
    revoke_if: str

    def to_payload(self) -> dict[str, Any]:
        return {
            "schema_id": self.schema_id,
            "artifact_id": self.artifact_id,
            "canonical_role": self.canonical_role,
            "generated_at": self.generated_at,
            "version": self.version,
            "tag_ref": self.tag_ref,
            "release_bundle_status": self.release_bundle_status,
            "tag_status": self.tag_status,
            "source_pointers": self.source_pointers,
            "required_pointers": [row.to_payload() for row in self.required_pointers],
            "not_claimed": list(self.not_claimed),
            "revoke_if": self.revoke_if,
        }


class ReleasePointerResolver:
    def __init__(self, root: Path):
        self.root = Path(root).resolve()
        self.repo_root = self._find_repo_root(self.root)

    def resolve(self, generated_at: str | None = None, tag_ref: str | None = None) -> ReleaseManifestSidecar:
        timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
        version = self._version()
        rows = tuple(self._required_pointer_rows())
        tag_status = self._tag_status(tag_ref)
        release_status: ReleaseBundleStatus = (
            "ready" if all(row.status == "resolved" for row in rows) and tag_status != "stale" else "not-ready"
        )
        return ReleaseManifestSidecar(
            schema_id=SCHEMA_ID,
            artifact_id=ARTIFACT_ID,
            canonical_role=CANONICAL_ROLE,
            generated_at=timestamp,
            version=version,
            tag_ref=tag_ref,
            release_bundle_status=release_status,
            tag_status=tag_status,
            source_pointers=self._source_pointers(),
            required_pointers=rows,
            not_claimed=NOT_CLAIMED,
            revoke_if=REVOKE_IF,
        )

    def _source_pointers(self) -> dict[str, dict[str, str]]:
        return {
            "canonical_index": {"path": "reports/canonical/index.json", "pointer": "$"},
            "artifact_manifest": {"path": "docs/artifact_manifest.md", "pointer": "## Quality Baseline Surfaces"},
            "literature_ledger_release_navigation": {
                "path": "docs/lit/literature_ledger.yaml",
                "pointer": "$.records[id=lit-artifact-release-navigation]",
            },
            "version": {"path": "VERSION", "pointer": "file"},
        }

    def _required_pointer_rows(self) -> list[ReleasePointerRow]:
        specs = (
            (
                "canonical-index",
                "reports/canonical/index.json",
                "$.schema_id",
                self._json_object_has_key,
            ),
            (
                "artifact-manifest-navigation",
                "docs/artifact_manifest.md",
                "## Quality Baseline Surfaces",
                self._text_contains,
            ),
            (
                "literature-ledger-release-navigation",
                "docs/lit/literature_ledger.yaml",
                "$.records[id=lit-artifact-release-navigation]",
                self._ledger_has_release_navigation,
            ),
            (
                "version-file",
                "VERSION",
                "file",
                self._version_file_resolves,
            ),
            (
                "canonical-index-markdown",
                "reports/canonical/index.md",
                "# Canonical Report Index",
                self._text_contains,
            ),
            (
                "artifact-manifest-self-row",
                "docs/artifact_manifest.md",
                "row:bedc-quality-lab:artifact-manifest",
                self._text_contains,
            ),
        )
        rows: list[ReleasePointerRow] = []
        for row_id, path_text, pointer, checker in specs:
            failure = checker(path_text, pointer)
            rows.append(
                ReleasePointerRow(
                    id=row_id,
                    path=path_text,
                    pointer=pointer,
                    status="resolved" if failure is None else "missing",
                    failure=failure,
                )
            )
        return rows

    def _json_object_has_key(self, path_text: str, pointer: str) -> str | None:
        path = self._path(path_text)
        if not path.exists():
            return f"missing path: {path_text}"
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            return f"invalid JSON: {exc}"
        if not isinstance(payload, dict):
            return "JSON root is not an object"
        key = pointer.removeprefix("$.")
        if key not in payload:
            return f"missing pointer: {pointer}"
        return None

    def _text_contains(self, path_text: str, pointer: str) -> str | None:
        path = self._path(path_text)
        if not path.exists():
            return f"missing path: {path_text}"
        text = path.read_text(encoding="utf-8")
        needle = pointer.removeprefix("row:")
        if needle not in text:
            return f"missing pointer: {pointer}"
        return None

    def _ledger_has_release_navigation(self, path_text: str, pointer: str) -> str | None:
        path = self._path(path_text)
        if not path.exists():
            return f"missing path: {path_text}"
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            return f"invalid ledger payload: {exc}"
        records = payload.get("records") if isinstance(payload, dict) else None
        if not isinstance(records, list):
            return "ledger records are missing"
        for record in records:
            if isinstance(record, dict) and record.get("id") == "lit-artifact-release-navigation":
                return None
        return f"missing pointer: {pointer}"

    def _version_file_resolves(self, _path_text: str, _pointer: str) -> str | None:
        path = self.repo_root / "VERSION"
        if not path.exists():
            return "missing path: VERSION"
        if not path.read_text(encoding="utf-8").strip():
            return "VERSION is empty"
        return None

    def _version(self) -> str:
        path = self.repo_root / "VERSION"
        if not path.exists():
            return "missing"
        value = path.read_text(encoding="utf-8").strip()
        return value if value else "missing"

    def _path(self, path_text: str) -> Path:
        if path_text == "VERSION":
            return self.repo_root / path_text
        return self.root / path_text

    def _tag_status(self, tag_ref: str | None) -> TagStatus:
        if tag_ref is None:
            return "absent"
        tag = self._git_stdout("rev-parse", "--verify", f"refs/tags/{tag_ref}^{{commit}}")
        if tag is None:
            return "absent"
        head = self._git_stdout("rev-parse", "HEAD")
        if head is None:
            return "unknown"
        return "present" if tag == head else "stale"

    def _git_stdout(self, *args: str) -> str | None:
        try:
            completed = subprocess.run(
                ("git", "-C", str(self.repo_root), *args),
                check=False,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
        except OSError:
            return None
        if completed.returncode != 0:
            return None
        return completed.stdout.strip()

    @staticmethod
    def _find_repo_root(root: Path) -> Path:
        for candidate in (root, root.parent, root.parent.parent, *root.parents):
            if (candidate / "VERSION").exists():
                return candidate
        return root


def resolve_release_manifest(root: Path, tag_ref: str | None = None) -> ReleaseManifestSidecar:
    return ReleasePointerResolver(root).resolve(tag_ref=tag_ref)


def write_release_manifest_sidecar(
    root: Path,
    generated_at: str | None = None,
    tag_ref: str | None = None,
) -> ReleaseManifestSidecar:
    sidecar = ReleasePointerResolver(root).resolve(generated_at=generated_at, tag_ref=tag_ref)
    _write_json(root / JSON_ARTIFACT, sidecar.to_payload())
    _write_text(root / MARKDOWN_ARTIFACT, render_release_manifest_markdown(sidecar))
    return sidecar


def render_release_manifest_markdown(sidecar: ReleaseManifestSidecar) -> str:
    payload = sidecar.to_payload()
    lines = [
        "# Release Manifest Sidecar",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Canonical role: `{payload['canonical_role']}`",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Version: `{payload['version']}`",
        f"- Tag ref: `{payload['tag_ref']}`",
        f"- Release bundle status: `{payload['release_bundle_status']}`",
        f"- Tag status: `{payload['tag_status']}`",
        "",
        "## Source Pointers",
        "",
        "| source | path | pointer |",
        "| --- | --- | --- |",
    ]
    for source, pointer in payload["source_pointers"].items():
        lines.append(f"| `{source}` | `{pointer['path']}` | `{pointer['pointer']}` |")
    lines.extend(
        [
            "",
            "## Required Pointers",
            "",
            "| id | path | pointer | status | failure |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for row in payload["required_pointers"]:
        lines.append(
            "| "
            f"`{row['id']}` | "
            f"`{row['path']}` | "
            f"`{row['pointer']}` | "
            f"`{row['status']}` | "
            f"`{row['failure']}` |"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Revoke If", "", payload["revoke_if"], ""])
    return "\n".join(lines)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)

#!/usr/bin/env python3
"""BEDC Lean automation helpers for audit, inventory, and verification.

Run ``python3 lean4/scripts/bedc_ci.py --help`` for the canonical subcommand list.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
REPO_ROOT = LEAN_ROOT.parent
BEDC_ROOT = LEAN_ROOT / "BEDC"
PAPER_ROOT = REPO_ROOT / "papers" / "bedc"
PAPER_PARTS_ROOT = PAPER_ROOT / "parts"
TYPE_MANIFEST_PATH = SCRIPT_DIR / "bedc_manifest.json"
LEANSTMT_DEBT_MANIFEST_PATH = SCRIPT_DIR / "leanstmt_debt_manifest.json"

DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|inductive|class|structure)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)?"
)
FIELD_RE = re.compile(r"^\s{2,}(?P<name>[A-Za-z0-9_']+)\s*:")
CTOR_RE = re.compile(r"^\s*\|\s+(?P<name>[A-Za-z0-9_']+)\b")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leanvariant|leansorryd|leanstmt|leandef)\{([^}]+)\}")
MARKER_EXISTENCE_RE = re.compile(
    r"\\(leanchecked|leanvariant|leantarget|leandef|leanstmt|leansorryd)\{([^}]+)\}"
)
LEAN_CHECKED_RE = re.compile(r"\\leanchecked\{([^}]+)\}")
THEOREM_STATUS_ENVS = (
    "definition",
    "principle",
    "kernelrule",
    "rulebox",
    "convention",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "protocol",
    "remark",
    "example",
    "axiomlike",
    "conjecture",
)
THEOREM_STATUS_BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(THEOREM_STATUS_ENVS) + r")\}"
    r"(?:\[(?P<title>[^\]]*)\])?"
)
THEOREM_STATUS_NEXT_BOUNDARY_RE = re.compile(
    r"\\begin\{(?:" + "|".join(THEOREM_STATUS_ENVS) + r")\}|\\chapter\{|\\section\{"
)
THEOREM_STATUS_PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
THEOREM_STATUS_PROOF_END_RE = re.compile(r"\\end\{proof\}")
LOCAL_REF_RE = re.compile(r"\\(?P<macro>autoref|ref\*?)\{(?P<label>[^}]+)\}")
CLAIM_ENTRY_RE = re.compile(r'⟨"[^"]*",\s*"([^"]+)"')
PREAMBLE_COMMAND_RE = re.compile(
    r"^\\(?P<kind>newcommand|providecommand|renewcommand|DeclareRobustCommand"
    r"|newenvironment|newtheorem)\*?\{(?P<name>\\?\w+)\}"
)
CONCRETE_REGION_PREFIX_RE = re.compile(r"^([0-9]+[a-z]?_[a-z][a-z0-9]*)_")
CONCRETE_CHAPTER_RE = re.compile(r"^\s*\\chapter\{", re.MULTILINE)
CONCRETE_INPUT_LINE_RE = re.compile(r"^\s*\\input\{[^}]+\}\s*$")
CONCRETE_BODY_ENV_RE = re.compile(
    r"\\begin\{(?:theorem|definition|lemma|proof|aligned)\}"
)
ORIGIN_TAG_RE = re.compile(r"\\origin\{([^}]*)\}")
CHAPTER_LABEL_RE = re.compile(r"\\label\{ch:concrete-instances-([a-z0-9_-]+)-namecert\}")
CLOSURESTATUS_BLOCK_RE = re.compile(
    r"\\begin\{closurestatus\}.*?\\end\{closurestatus\}",
    re.DOTALL,
)
TOP_LEVEL_ORIGIN_RE = re.compile(r"^\s*\\origin\{([^}]*)\}\s*$", re.MULTILINE)
VALID_ORIGINS = {"human", "ai"}

NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z0-9_'.]+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(?P<name>[A-Za-z0-9_'.]+))?\s*$")
MARKER_DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual)\s+)*"
    r"(?P<kind>theorem|def|lemma|abbrev|instance|inductive|structure|class)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)\b"
)

FORBIDDEN_PATTERNS = {
    "axiom": re.compile(r"\baxiom\b"),
    "sorry": re.compile(r"\bsorry\b"),
    "import Mathlib": re.compile(r"^\s*import\s+Mathlib(?:\.|\b)", re.MULTILINE),
    "import mathlib": re.compile(r"^\s*import\s+mathlib(?:\.|\b)", re.MULTILINE),
    "constant": re.compile(r"^\s*constant\s+", re.MULTILINE),
}


@dataclass(frozen=True)
class DeclarationRecord:
    module: str
    file: str
    line: int
    kind: str
    name: str
    qualified_name: str
    is_private: bool = False


@dataclass(frozen=True)
class FieldRecord:
    parent: str
    name: str
    qualified_name: str
    file: str
    line: int


@dataclass(frozen=True)
class LeanMarkerRecord:
    file: str
    line: int
    macro: str
    target: str


@dataclass(frozen=True)
class LeanStmtDebtEntry:
    file: str
    target: str
    discharge_plan: str
    line: int | None = None
    owner_scope: str | None = None


@dataclass(frozen=True)
class TheoremStatusEnvironment:
    kind: str
    title: str | None
    start_line: int
    statement_body: str
    statement_base_line: int
    relation_text: str
    relation_base_line: int


@dataclass(frozen=True)
class TheoremStatusRelationWindow:
    proof_line: int | None
    marker_scan_end: int
    reference_scan_end: int


@dataclass(frozen=True)
class AxiomReportRecord:
    name: str
    kind: str
    axioms: tuple[str, ...]


@dataclass(frozen=True)
class CarrierRecord:
    name: str
    file: str
    field_names: tuple[str, ...]
    field_types: tuple[str, ...]
    phase2_status: str
    to_event_flow_shape: tuple[tuple[str, int], ...] | None
    namecert_hash: str | None

    @property
    def arity(self) -> int:
        return len(self.field_names)


def read_text(path: Path) -> str:
    # Race-safe: lean_files() / paper file walkers snapshot the directory,
    # but a concurrent worker may delete / rename a file between the walk
    # and this read (chapter cleanup, refactor, sibling merge). Return an
    # empty string rather than crash the entire audit — downstream parsers
    # treat empty content as "no declarations / no labels", which is the
    # correct semantics for a file that no longer exists.
    try:
        return path.read_text(encoding="utf-8")
    except (FileNotFoundError, OSError):
        return ""


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def module_name(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_olean_path(module: str) -> Path:
    return LEAN_ROOT / ".lake" / "build" / "lib" / "lean" / Path(*module.split(".")).with_suffix(".olean")


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    n = len(text)
    while i < n:
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            if ch == "\\" and i + 1 < n:
                out.extend("  ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
            continue

        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def line_col(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    last_nl = text.rfind("\n", 0, offset)
    col = offset + 1 if last_nl < 0 else offset - last_nl
    return line, col


def lean_files() -> list[Path]:
    return sorted(BEDC_ROOT.rglob("*.lean"))


def tex_files() -> list[Path]:
    return sorted(PAPER_ROOT.rglob("*.tex"))


def part_tex_files() -> list[Path]:
    return sorted(PAPER_PARTS_ROOT.rglob("*.tex"))


def collect_forbidden_tokens(path: Path) -> list[dict[str, object]]:
    text = read_text(path)
    stripped = strip_comments_and_strings(text)
    violations: list[dict[str, object]] = []
    for token, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(stripped):
            line, col = line_col(stripped, match.start())
            violations.append(
                {
                    "file": str(path.relative_to(REPO_ROOT)),
                    "line": line,
                    "column": col,
                    "token": token,
                }
            )
    return violations


def declaration_namespace(module: str, namespace_stack: list[str]) -> str:
    if not namespace_stack:
        return module
    return namespace_stack[-1]


def qualified_name(name: str, namespace: str) -> str:
    if name.startswith("BEDC.") or name.startswith(f"{namespace}."):
        return name
    return f"{namespace}.{name}"


def resolve_namespace(name: str, namespace_stack: list[str]) -> str:
    if not namespace_stack or name.startswith("BEDC."):
        return name
    return f"{namespace_stack[-1]}.{name}"


def update_namespace_stack(line: str, namespace_stack: list[str]) -> None:
    namespace_match = NAMESPACE_RE.match(line)
    if namespace_match:
        namespace_stack.append(resolve_namespace(namespace_match.group("name"), namespace_stack))
        return

    end_match = END_RE.match(line)
    if not end_match or not namespace_stack:
        return

    name = end_match.group("name")
    if name is None or namespace_stack[-1] == name or namespace_stack[-1].endswith(f".{name}"):
        namespace_stack.pop()


def collect_declarations(path: Path) -> tuple[list[DeclarationRecord], list[FieldRecord]]:
    text = strip_comments_and_strings(read_text(path))
    lines = text.splitlines()
    module = module_name(path)
    namespace_stack: list[str] = []
    decls: list[DeclarationRecord] = []
    fields: list[FieldRecord] = []

    for idx, line in enumerate(lines, start=1):
        update_namespace_stack(line, namespace_stack)
        namespace = declaration_namespace(module, namespace_stack)
        match = DECL_RE.match(line)
        if not match:
            continue
        kind = match.group("kind")
        name = (match.group("name") or f"<anonymous_{kind}_{idx}>").strip()
        qualified = qualified_name(name, namespace)
        is_private = re.match(r"^\s*(?:@\[[^\]]+\]\s*)*private\b", line) is not None
        decls.append(
            DeclarationRecord(
                module=module,
                file=str(path.relative_to(REPO_ROOT)),
                line=idx,
                kind=kind,
                name=name,
                qualified_name=qualified,
                is_private=is_private,
            )
        )

        if kind in ("structure", "class"):
            parent = qualified
            j = idx
            while j < len(lines):
                next_line = lines[j]
                if next_line.strip() == "":
                    j += 1
                    continue
                if not next_line.startswith((" ", "\t")):
                    break
                field_match = FIELD_RE.match(next_line)
                if field_match:
                    field_name = field_match.group("name")
                    fields.append(
                        FieldRecord(
                            parent=parent,
                            name=field_name,
                            qualified_name=f"{parent}.{field_name}",
                            file=str(path.relative_to(REPO_ROOT)),
                            line=j + 1,
                        )
                    )
                j += 1
            continue

        if kind == "inductive":
            parent = qualified
            j = idx
            while j < len(lines):
                next_line = lines[j]
                if next_line.strip() == "":
                    j += 1
                    continue
                if not next_line.startswith((" ", "\t")):
                    break
                ctor_match = CTOR_RE.match(next_line)
                if ctor_match:
                    ctor_name = ctor_match.group("name")
                    fields.append(
                        FieldRecord(
                            parent=parent,
                            name=ctor_name,
                            qualified_name=f"{namespace}.{ctor_name}",
                            file=str(path.relative_to(REPO_ROOT)),
                            line=j + 1,
                        )
                    )
                j += 1

    return decls, fields


def build_declaration_inventory() -> tuple[list[DeclarationRecord], list[FieldRecord]]:
    decls: list[DeclarationRecord] = []
    fields: list[FieldRecord] = []
    for path in lean_files():
        file_decls, file_fields = collect_declarations(path)
        decls.extend(file_decls)
        fields.extend(file_fields)
    return decls, fields


def collect_part_labels() -> list[dict[str, object]]:
    out: list[dict[str, object]] = []
    for path in part_tex_files():
        text = read_text(path)
        for match in LABEL_RE.finditer(text):
            label = match.group(1).strip()
            line = text.count("\n", 0, match.start()) + 1
            out.append({"label": label, "file": str(path.relative_to(PAPER_ROOT)), "line": line})
    return out


def collect_lean_markers() -> list[LeanMarkerRecord]:
    markers: list[LeanMarkerRecord] = []
    for path in tex_files():
        text = read_text(path)
        for line_no, raw_line in enumerate(text.splitlines(), start=1):
            stripped = raw_line.lstrip()
            if stripped.startswith("%"):
                continue
            for match in LEAN_MARKER_RE.finditer(raw_line):
                target = match.group(2).replace(r"\_", "_").strip()
                markers.append(LeanMarkerRecord(
                    file=str(path.relative_to(PAPER_ROOT)),
                    line=line_no,
                    macro=match.group(1),
                    target=target,
                ))
    return markers


def collect_leanstmt_sites(markers: Iterable[LeanMarkerRecord]) -> list[LeanMarkerRecord]:
    return [marker for marker in markers if marker.macro == "leanstmt"]


def _leanstmt_site_key(file: str, target: str) -> tuple[str, str]:
    return file.strip(), target.strip()


def _leanstmt_placeholder_plan(plan: str) -> bool:
    text = re.sub(r"[\s._-]+", "", plan).lower()
    placeholders = {
        "",
        "todo",
        "tbd",
        "none",
        "na",
        "n/a",
        "placeholder",
        "fixme",
        "later",
    }
    return text in {re.sub(r"[\s._-]+", "", item).lower() for item in placeholders}


def load_leanstmt_debt_manifest(
    path: Path = LEANSTMT_DEBT_MANIFEST_PATH,
) -> tuple[list[LeanStmtDebtEntry], list[dict[str, object]]]:
    diagnostics: list[dict[str, object]] = []
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return [], [{
            "kind": "manifest_missing",
            "path": display_path(path),
            "message": f"manifest not found: {display_path(path)}",
        }]
    except json.JSONDecodeError as exc:
        return [], [{
            "kind": "manifest_invalid_json",
            "path": display_path(path),
            "line": exc.lineno,
            "message": f"invalid JSON: {exc.msg}",
        }]

    entries: list[LeanStmtDebtEntry] = []
    if not isinstance(raw, dict):
        return [], [{
            "kind": "manifest_invalid_shape",
            "path": display_path(path),
            "message": "manifest root must be an object",
        }]

    allowed_top_keys = {"schema", "entries"}
    extra_top_keys = sorted(set(raw) - allowed_top_keys)
    missing_top_keys = sorted(allowed_top_keys - set(raw))
    if extra_top_keys:
        diagnostics.append({
            "kind": "manifest_extra_top_keys",
            "path": display_path(path),
            "keys": extra_top_keys,
            "message": f"unexpected top-level keys: {', '.join(extra_top_keys)}",
        })
    if missing_top_keys:
        diagnostics.append({
            "kind": "manifest_missing_top_keys",
            "path": display_path(path),
            "keys": missing_top_keys,
            "message": f"missing top-level keys: {', '.join(missing_top_keys)}",
        })
    if raw.get("schema") != "leanstmt_debt_manifest.v1":
        diagnostics.append({
            "kind": "manifest_schema_mismatch",
            "path": display_path(path),
            "schema": raw.get("schema"),
            "message": "schema must be leanstmt_debt_manifest.v1",
        })

    raw_entries = raw.get("entries")
    if not isinstance(raw_entries, list):
        diagnostics.append({
            "kind": "manifest_entries_invalid",
            "path": display_path(path),
            "message": "entries must be a list",
        })
        return [], diagnostics

    seen: dict[tuple[str, str], int] = {}
    required = {"file", "target", "discharge_plan"}
    allowed_entry_keys = required | {"line", "owner_scope"}
    for idx, raw_entry in enumerate(raw_entries):
        entry_site = {"path": display_path(path), "entry_index": idx}
        if not isinstance(raw_entry, dict):
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_invalid",
                "message": "entry must be an object",
            })
            continue

        missing = sorted(required - set(raw_entry))
        extra = sorted(set(raw_entry) - allowed_entry_keys)
        if missing:
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_missing_keys",
                "keys": missing,
                "message": f"entry missing required keys: {', '.join(missing)}",
            })
        if extra:
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_extra_keys",
                "keys": extra,
                "message": f"entry has unexpected keys: {', '.join(extra)}",
            })

        file_value = raw_entry.get("file")
        target_value = raw_entry.get("target")
        plan_value = raw_entry.get("discharge_plan")
        line_value = raw_entry.get("line")
        owner_scope_value = raw_entry.get("owner_scope")

        if not isinstance(file_value, str) or not file_value.strip():
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_invalid_file",
                "message": "file must be a non-empty string",
            })
        if not isinstance(target_value, str) or not target_value.strip():
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_invalid_target",
                "message": "target must be a non-empty string",
            })
        if not isinstance(plan_value, str) or _leanstmt_placeholder_plan(plan_value):
            diagnostics.append({
                **entry_site,
                "kind": "manifest_entry_invalid_discharge_plan",
                "file": file_value if isinstance(file_value, str) else None,
                "target": target_value if isinstance(target_value, str) else None,
                "message": "discharge_plan must be a non-placeholder string",
            })

        parsed_line: int | None = None
        if line_value is not None:
            if isinstance(line_value, int) and line_value > 0:
                parsed_line = line_value
            else:
                diagnostics.append({
                    **entry_site,
                    "kind": "manifest_entry_invalid_line",
                    "file": file_value if isinstance(file_value, str) else None,
                    "target": target_value if isinstance(target_value, str) else None,
                    "message": "line must be a positive integer when present",
                })

        parsed_owner_scope: str | None = None
        if owner_scope_value is not None:
            if isinstance(owner_scope_value, str) and owner_scope_value.strip():
                parsed_owner_scope = owner_scope_value.strip()
            else:
                diagnostics.append({
                    **entry_site,
                    "kind": "manifest_entry_invalid_owner_scope",
                    "file": file_value if isinstance(file_value, str) else None,
                    "target": target_value if isinstance(target_value, str) else None,
                    "message": "owner_scope must be a non-empty string when present",
                })

        if not isinstance(file_value, str) or not isinstance(target_value, str) or not isinstance(plan_value, str):
            continue

        file_name = file_value.strip()
        target = target_value.strip()
        key = _leanstmt_site_key(file_name, target)
        if key in seen:
            diagnostics.append({
                **entry_site,
                "kind": "manifest_duplicate_key",
                "file": file_name,
                "target": target,
                "first_entry_index": seen[key],
                "message": f"duplicate manifest key: {file_name} -> {target}",
            })
        else:
            seen[key] = idx

        entries.append(LeanStmtDebtEntry(
            file=file_name,
            target=target,
            discharge_plan=plan_value.strip(),
            line=parsed_line,
            owner_scope=parsed_owner_scope,
        ))

    return entries, diagnostics


def leanstmt_debt_payload(
    markers: Iterable[LeanMarkerRecord],
    manifest: Iterable[LeanStmtDebtEntry],
    manifest_diagnostics: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    live_sites = collect_leanstmt_sites(markers)
    manifest_entries = list(manifest)
    diagnostics = list(manifest_diagnostics or [])

    live_by_key: dict[tuple[str, str], list[LeanMarkerRecord]] = {}
    for marker in live_sites:
        live_by_key.setdefault(_leanstmt_site_key(marker.file, marker.target), []).append(marker)

    manifest_by_key: dict[tuple[str, str], list[LeanStmtDebtEntry]] = {}
    for entry in manifest_entries:
        manifest_by_key.setdefault(_leanstmt_site_key(entry.file, entry.target), []).append(entry)

    duplicate_live_sites: list[dict[str, object]] = []
    for (file_name, target), records in sorted(live_by_key.items()):
        if len(records) <= 1:
            continue
        duplicate_live_sites.append({
            "kind": "duplicate_live_site",
            "file": file_name,
            "target": target,
            "lines": [record.line for record in records],
            "message": f"duplicate live leanstmt site: {file_name} -> {target}",
        })

    unregistered_live_sites: list[dict[str, object]] = []
    for (file_name, target), records in sorted(live_by_key.items()):
        if (file_name, target) in manifest_by_key:
            continue
        for record in records:
            unregistered_live_sites.append({
                "kind": "unregistered_live_site",
                "file": record.file,
                "line": record.line,
                "target": record.target,
                "message": f"live leanstmt site is not registered: {record.file}:{record.line} -> {record.target}",
            })

    stale_manifest_entries: list[dict[str, object]] = []
    for (file_name, target), entries in sorted(manifest_by_key.items()):
        if (file_name, target) in live_by_key:
            continue
        for entry in entries:
            item: dict[str, object] = {
                "kind": "stale_manifest_entry",
                "file": entry.file,
                "target": entry.target,
                "message": f"manifest entry has no live leanstmt site: {entry.file} -> {entry.target}",
            }
            if entry.line is not None:
                item["line"] = entry.line
            stale_manifest_entries.append(item)

    return {
        "schema": "leanstmt_debt_manifest.v1",
        "manifest_path": str(LEANSTMT_DEBT_MANIFEST_PATH.relative_to(REPO_ROOT)),
        "live_sites": [
            {
                "file": marker.file,
                "line": marker.line,
                "target": marker.target,
            }
            for marker in live_sites
        ],
        "manifest_entries": [
            {
                **{
                    "file": entry.file,
                    "target": entry.target,
                    "discharge_plan": entry.discharge_plan,
                },
                **({"line": entry.line} if entry.line is not None else {}),
                **({"owner_scope": entry.owner_scope} if entry.owner_scope is not None else {}),
            }
            for entry in manifest_entries
        ],
        "manifest_diagnostics": diagnostics,
        "unregistered_live_sites": unregistered_live_sites,
        "stale_manifest_entries": stale_manifest_entries,
        "duplicate_live_sites": duplicate_live_sites,
        "violations": diagnostics + unregistered_live_sites + stale_manifest_entries + duplicate_live_sites,
    }


def collect_paper_leanchecked_targets() -> set[str]:
    targets: set[str] = set()
    for path in part_tex_files():
        text = read_text(path)
        for raw_line in text.splitlines():
            if raw_line.lstrip().startswith("%"):
                continue
            for match in LEAN_CHECKED_RE.finditer(raw_line):
                targets.add(match.group(1).replace(r"\_", "_").strip())
    return targets


def collect_marker_existence_markers() -> list[LeanMarkerRecord]:
    markers: list[LeanMarkerRecord] = []
    for path in part_tex_files():
        text = read_text(path)
        for line_no, raw_line in enumerate(text.splitlines(), start=1):
            if raw_line.lstrip().startswith("%"):
                continue
            for match in MARKER_EXISTENCE_RE.finditer(raw_line):
                target = match.group(2).replace(r"\_", "_").strip()
                markers.append(LeanMarkerRecord(
                    file=str(path.relative_to(REPO_ROOT)),
                    line=line_no,
                    macro=match.group(1),
                    target=target,
                ))
    return markers


def collect_marker_existence_lean_names() -> set[str]:
    names: set[str] = set()
    for path in lean_files():
        text = strip_comments_and_strings(read_text(path))
        module = module_name(path)
        namespace_stack: list[str] = []
        for raw_line in text.splitlines():
            update_namespace_stack(raw_line, namespace_stack)
            match = MARKER_DECL_RE.match(raw_line)
            if not match:
                continue
            name = match.group("name").strip()
            namespace = declaration_namespace(module, namespace_stack)
            names.add(qualified_name(name, namespace))
    return names


def theorem_status_empty_dna_roles() -> dict[str, object]:
    return {
        "statement": None,
        "dependencies": [],
        "proof": None,
        "certificates": [],
        "ledger": None,
        "status": None,
        "canonical_site": None,
        "closing_seal": None,
    }


def _line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _title_value(raw_title: str | None) -> str | None:
    title = (raw_title or "").strip()
    return title or None


def _label_records_in_text(text: str, base_line: int) -> list[dict[str, object]]:
    labels: list[dict[str, object]] = []
    for match in LABEL_RE.finditer(text):
        labels.append({
            "label": match.group(1).strip(),
            "line": base_line + text.count("\n", 0, match.start()),
        })
    return labels


def _references_in_text(text: str, base_line: int) -> list[dict[str, object]]:
    refs: list[dict[str, object]] = []
    seen: set[tuple[str, str, int]] = set()
    for match in LOCAL_REF_RE.finditer(text):
        line = base_line + text.count("\n", 0, match.start())
        item = (match.group("macro"), match.group("label").strip(), line)
        if item in seen:
            continue
        seen.add(item)
        refs.append({"macro": item[0], "label": item[1], "line": item[2]})
    return refs


def _lean_marker_records_in_text(
    text: str,
    base_line: int,
    file_name: str,
) -> list[LeanMarkerRecord]:
    markers: list[LeanMarkerRecord] = []
    for line_idx, raw_line in enumerate(text.splitlines(), start=0):
        if raw_line.lstrip().startswith("%"):
            continue
        for match in LEAN_MARKER_RE.finditer(raw_line):
            markers.append(LeanMarkerRecord(
                file=file_name,
                line=base_line + line_idx,
                macro=match.group(1),
                target=match.group(2).replace(r"\_", "_").strip(),
            ))
    return markers


def _site(file_name: str, line: int | None) -> dict[str, object] | None:
    if line is None:
        return None
    return {"file": file_name, "line": line}


def _chapter_label_before(text: str, offset: int) -> str | None:
    label: str | None = None
    for match in LABEL_RE.finditer(text, 0, offset):
        candidate = match.group(1).strip()
        if candidate.startswith("ch:"):
            label = candidate
    return label


def _closurestatus_projection(block: dict) -> dict[str, object]:
    return {
        "file": block.get("file"),
        "line": block.get("line"),
        "region": block.get("region"),
        "theory_closure": block.get("theory_closure"),
        "bridge_status": block.get("bridge_status"),
        "has_scope": block.get("has_scope"),
        "has_notclaimed": block.get("has_notclaimed"),
        "has_upgradepath": block.get("has_upgradepath"),
        "open_fields": dict(block.get("open_fields") or {}),
    }


def _lean_resolution_for_markers(
    markers: list[LeanMarkerRecord],
    lean_names: set[str],
) -> list[dict[str, object]]:
    return [
        {
            "target": marker.target,
            "resolved": marker.target in lean_names,
        }
        for marker in markers
    ]


def _closure_blocks_by_file() -> dict[str, list[dict]]:
    closure_by_file: dict[str, list[dict]] = {}
    for block in collect_closurestatus_blocks(PAPER_PARTS_ROOT):
        closure_by_file.setdefault(str(block.get("file", "")), []).append(block)
    return closure_by_file


def _theorem_status_environment(
    text: str,
    match: re.Match[str],
) -> TheoremStatusEnvironment:
    kind = match.group("kind")
    end_re = re.compile(r"\\end\{" + re.escape(kind) + r"\}")
    end_match = end_re.search(text, match.end())
    statement_end = end_match.end() if end_match else match.end()
    statement_body = text[match.end(): end_match.start() if end_match else match.end()]

    next_match = THEOREM_STATUS_NEXT_BOUNDARY_RE.search(text, statement_end)
    relation_end = next_match.start() if next_match else len(text)

    return TheoremStatusEnvironment(
        kind=kind,
        title=_title_value(match.group("title")),
        start_line=_line_for_offset(text, match.start()),
        statement_body=statement_body,
        statement_base_line=_line_for_offset(text, match.end()),
        relation_text=text[statement_end:relation_end],
        relation_base_line=_line_for_offset(text, statement_end),
    )


def _theorem_status_relation_window(
    env: TheoremStatusEnvironment,
) -> TheoremStatusRelationWindow:
    proof_match = THEOREM_STATUS_PROOF_BEGIN_RE.search(env.relation_text)
    if not proof_match:
        return TheoremStatusRelationWindow(
            proof_line=None,
            marker_scan_end=len(env.relation_text),
            reference_scan_end=len(env.relation_text),
        )

    proof_line = env.relation_base_line + env.relation_text.count("\n", 0, proof_match.start())
    proof_end_match = THEOREM_STATUS_PROOF_END_RE.search(
        env.relation_text,
        proof_match.end(),
    )
    return TheoremStatusRelationWindow(
        proof_line=proof_line,
        marker_scan_end=proof_match.start(),
        reference_scan_end=proof_end_match.end() if proof_end_match else len(env.relation_text),
    )


def _theorem_status_label(env: TheoremStatusEnvironment) -> str | None:
    labels = [
        item["label"]
        for item in _label_records_in_text(env.statement_body, env.statement_base_line)
    ]
    return str(labels[0]) if labels else None


def _marker_payload(markers: list[LeanMarkerRecord]) -> list[dict[str, object]]:
    return [
        {
            "file": marker.file,
            "line": marker.line,
            "macro": marker.macro,
            "target": marker.target,
        }
        for marker in markers
    ]


def _theorem_status_markers(
    env: TheoremStatusEnvironment,
    window: TheoremStatusRelationWindow,
    file_name: str,
) -> list[LeanMarkerRecord]:
    local_marker_text = env.relation_text[:window.marker_scan_end]
    markers = _lean_marker_records_in_text(env.statement_body, env.statement_base_line, file_name)
    markers.extend(_lean_marker_records_in_text(local_marker_text, env.relation_base_line, file_name))
    return markers


def _theorem_status_references(
    env: TheoremStatusEnvironment,
    window: TheoremStatusRelationWindow,
) -> list[dict[str, object]]:
    refs = _references_in_text(env.statement_body, env.statement_base_line)
    refs.extend(_references_in_text(env.relation_text[:window.reference_scan_end], env.relation_base_line))
    seen_refs: set[tuple[str, str, int]] = set()
    reference_payload: list[dict[str, object]] = []
    for ref in refs:
        key = (str(ref["macro"]), str(ref["label"]), int(ref["line"]))
        if key in seen_refs:
            continue
        seen_refs.add(key)
        reference_payload.append(ref)
    return reference_payload


def _next_closurestatus(
    blocks: list[dict],
    start_line: int,
) -> dict[str, object] | None:
    for block in blocks:
        if int(block.get("line") or 0) >= start_line:
            return _closurestatus_projection(block)
    return None


def _theorem_status_record(
    text: str,
    match: re.Match[str],
    file_name: str,
    closure_blocks: list[dict],
    lean_names: set[str],
) -> dict[str, object]:
    env = _theorem_status_environment(text, match)
    window = _theorem_status_relation_window(env)
    markers = _theorem_status_markers(env, window, file_name)
    return {
        "label": _theorem_status_label(env),
        "kind": env.kind,
        "title": env.title,
        "file": file_name,
        "line": env.start_line,
        "chapter_label": _chapter_label_before(text, match.start()),
        "statement_site": _site(file_name, env.start_line),
        "proof_site": _site(file_name, window.proof_line),
        "references": _theorem_status_references(env, window),
        "lean_markers": _marker_payload(markers),
        "lean_resolution": _lean_resolution_for_markers(markers, lean_names),
        "chapter_closurestatus": _next_closurestatus(closure_blocks, env.start_line),
        "dna_roles": theorem_status_empty_dna_roles(),
    }


def collect_theorem_status_records() -> list[dict[str, object]]:
    lean_names = collect_marker_existence_lean_names()
    closure_by_file = _closure_blocks_by_file()

    records: list[dict[str, object]] = []
    for path in part_tex_files():
        text = read_text(path)
        file_name = str(path.relative_to(REPO_ROOT))
        local_closure_blocks = sorted(
            closure_by_file.get(file_name, []),
            key=lambda block: int(block.get("line") or 0),
        )
        for match in THEOREM_STATUS_BEGIN_RE.finditer(text):
            records.append(_theorem_status_record(
                text,
                match,
                file_name,
                local_closure_blocks,
                lean_names,
            ))
    return records


def theorem_status_payload() -> dict[str, object]:
    records = collect_theorem_status_records()
    return {
        "source": "derived-from-canonical-sources",
        "records_total": len(records),
        "theorem_status_records": records,
    }


def collect_manifest_entry_targets() -> set[str]:
    entries_path = BEDC_ROOT / "Manifest" / "Entries.lean"
    if not entries_path.exists():
        return set()
    text = read_text(entries_path)
    return {match.group(1).strip() for match in CLAIM_ENTRY_RE.finditer(text)}


def inventory_payload(
    declarations: Iterable[DeclarationRecord],
    fields: Iterable[FieldRecord],
    part_labels: Iterable[dict[str, object]],
    markers: Iterable[LeanMarkerRecord],
) -> dict[str, object]:
    decls = list(declarations)
    field_list = list(fields)
    part_label_list = list(part_labels)
    marker_list = list(markers)

    return {
        "lean_files_scanned": len(lean_files()),
        "paper_part_files_scanned": len(part_tex_files()),
        "paper_tex_files_scanned": len(tex_files()),
        "declarations_total": len(decls),
        "field_targets_total": len(field_list),
        "declaration_kinds": dict(sorted(Counter(d.kind for d in decls).items())),
        "part_labels_total": len(part_label_list),
        "part_label_prefixes": dict(sorted(Counter(item["label"].split(":", 1)[0] for item in part_label_list if ":" in str(item["label"])).items())),
        "lean_markers_total": len(marker_list),
        "lean_marker_macros": dict(sorted(Counter(m.macro for m in marker_list).items())),
        "declarations": [
            {
                "module": d.module,
                "file": d.file,
                "line": d.line,
                "kind": d.kind,
                "name": d.name,
                "qualified_name": d.qualified_name,
                "is_private": d.is_private,
            }
            for d in decls
        ],
        "field_targets": [
            {
                "parent": f.parent,
                "name": f.name,
                "qualified_name": f.qualified_name,
                "file": f.file,
                "line": f.line,
            }
            for f in field_list
        ],
        "paper_labels": part_label_list,
        "lean_markers": [
            {
                "file": m.file,
                "line": m.line,
                "macro": m.macro,
                "target": m.target,
            }
            for m in marker_list
        ],
    }


def detect_case_collision_paths() -> list[dict[str, object]]:
    """Detect git index entries that differ only by case.

    On case-insensitive filesystems (default macOS APFS, Windows NTFS) the
    working tree can only hold one of the two paths, so the other index
    entry's blob never matches disk and ``git status`` reports a
    perpetually-modified file. The duplicate also breaks Lean's
    case-sensitive import resolution on Linux CI even when local builds
    pass. We scan ``git ls-files`` (the index, not the FS) so the check
    catches the bug regardless of which path is currently materialized.
    """
    try:
        out = subprocess.run(
            ["git", "ls-files", "-z", "--full-name"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return []
    paths = [p for p in out.split("\x00") if p]
    by_lower: dict[str, list[str]] = {}
    for p in paths:
        by_lower.setdefault(p.lower(), []).append(p)
    return [
        {"lower": lower, "paths": sorted(group)}
        for lower, group in sorted(by_lower.items())
        if len(group) > 1
    ]


def detect_preamble_duplicate_commands() -> list[dict[str, object]]:
    occurrences_by_name: dict[str, list[dict[str, object]]] = {}
    for path in sorted(PAPER_ROOT.glob("preamble*.tex")):
        if not path.is_file():
            continue
        for line_no, raw_line in enumerate(read_text(path).splitlines(), start=1):
            match = PREAMBLE_COMMAND_RE.match(raw_line)
            if not match:
                continue
            name = match.group("name").lstrip("\\")
            occurrences_by_name.setdefault(name, []).append({
                "file": str(path.relative_to(REPO_ROOT)),
                "line": line_no,
                "kind": match.group("kind"),
                "raw_line": raw_line,
            })

    duplicates: list[dict[str, object]] = []
    for name, occurrences in sorted(occurrences_by_name.items()):
        if len(occurrences) <= 1:
            continue
        kinds = {str(item["kind"]) for item in occurrences}
        if "newcommand" in kinds and "renewcommand" in kinds:
            continue
        duplicates.append({"name": name, "occurrences": occurrences})
    return duplicates


def _get_commit_changed_files() -> set[str] | None:
    """Return files changed by HEAD relative to its first parent."""
    try:
        dirty = subprocess.run(
            ["git", "diff", "--name-only", "HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if dirty.returncode == 0:
            dirty_files = {ln.strip() for ln in dirty.stdout.splitlines() if ln.strip()}
            if dirty_files:
                return dirty_files
        r = subprocess.run(
            ["git", "diff", "--name-only", "HEAD~1..HEAD"],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
        )
        if r.returncode != 0:
            return None
        return {ln.strip() for ln in r.stdout.splitlines() if ln.strip()}
    except Exception:
        return None


def _repo_relative_candidates(raw: object) -> list[str]:
    if not raw:
        return []
    text = str(raw)
    candidates = [text]
    path = Path(text)
    if path.is_absolute():
        try:
            candidates.append(str(path.resolve().relative_to(REPO_ROOT)))
        except ValueError:
            pass
    else:
        if not text.startswith("papers/") and text.endswith(".tex"):
            candidates.append(str(Path("papers") / "bedc" / text))
        if not text.startswith("lean4/") and text.endswith(".lean"):
            candidates.append(str(Path("lean4") / text))
    return list(dict.fromkeys(candidates))


def _classify_violation(violation: dict, changed_files: set[str] | None) -> str:
    """Return new when a violation touches HEAD's changed files.

    If git context is unavailable, classify conservatively as new.
    """
    if changed_files is None:
        return "new"
    candidates = [
        violation.get(k)
        for k in ("file", "paper_file", "carrier_file", "path", "subdir")
    ]
    if isinstance(violation.get("files"), list):
        candidates.extend(violation["files"])
    if isinstance(violation.get("paths"), list):
        candidates.extend(violation["paths"])
    if isinstance(violation.get("occurrences"), list):
        for occ in violation["occurrences"]:
            if isinstance(occ, dict):
                candidates.append(occ.get("file"))
    for c in candidates:
        for candidate in _repo_relative_candidates(c):
            if candidate in changed_files:
                return "new"
            if any(changed.startswith(f"{candidate.rstrip('/')}/") for changed in changed_files):
                return "new"
    return "legacy"


def _split_violations(
    results: list[dict[str, object]],
    changed_files: set[str] | None,
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    new = [v for v in results if _classify_violation(v, changed_files) == "new"]
    legacy = [v for v in results if _classify_violation(v, changed_files) == "legacy"]
    return new, legacy


def _attach_violation_split(
    payload: dict[str, object],
    name: str,
    results: list[dict[str, object]],
    changed_files: set[str] | None,
) -> None:
    new, legacy = _split_violations(results, changed_files)
    payload[name] = results
    payload[f"{name}_count"] = len(results)
    payload[f"{name}_new_count"] = len(new)
    payload[f"{name}_legacy_count"] = len(legacy)
    payload[f"{name}_new"] = new
    payload[f"{name}_legacy"] = legacy


def detect_concrete_instance_number_collisions() -> list[dict[str, object]]:
    instances = PAPER_PARTS_ROOT / "concrete_instances"
    if not instances.is_dir():
        return []

    groups: dict[str, list[Path]] = {}
    for path in sorted(instances.glob("*.tex")):
        match = CONCRETE_REGION_PREFIX_RE.match(path.name)
        if not match:
            continue
        groups.setdefault(match.group(1), []).append(path)

    collisions: list[dict[str, object]] = []
    for region, files in sorted(groups.items()):
        if len(files) <= 1:
            continue
        slug = region.split("_", 1)[1]
        subdir = instances / slug
        subdir_exists = subdir.is_dir()
        if subdir_exists:
            continue
        collisions.append({
            "region": region,
            "files": [str(path.relative_to(REPO_ROOT)) for path in files],
            "subdir_exists": subdir_exists,
        })
    return collisions


def is_concrete_instance_hub_only(text: str) -> bool:
    lines = [
        line.strip()
        for line in text.splitlines()
        if line.strip() and not line.lstrip().startswith("%")
    ]
    if not lines:
        return True
    if CONCRETE_BODY_ENV_RE.search(text):
        return False
    for line in lines:
        if CONCRETE_INPUT_LINE_RE.match(line):
            continue
        if line.startswith(r"\chapter{") or line.startswith(r"\label{"):
            continue
        if line.startswith(r"\begin{closurestatus}") or line.startswith(r"\end{closurestatus}"):
            continue
        if line.startswith(r"\theoryclosure{") or line.startswith(r"\scopeclosed{"):
            continue
        if line.startswith(r"\formalstatus{") or line.startswith(r"\leantarget{"):
            continue
        if line.startswith(r"\bridgestatus{") or line.startswith(r"\notclaimed{"):
            continue
        if line.startswith(r"\upgradepath{") or line.startswith(r"\constructivestory{"):
            continue
        if line.startswith(r"\origin{"):
            continue
        return False
    return True


def detect_concrete_instance_missing_origin() -> list[dict[str, object]]:
    instances = PAPER_PARTS_ROOT / "concrete_instances"
    if not instances.is_dir():
        return []

    changed = changed_concrete_instance_tex_paths()
    missing: list[dict[str, object]] = []
    for path in sorted(instances.rglob("*.tex")):
        if not path.is_file():
            continue
        if changed is not None and path not in changed:
            continue
        text = read_text(path)
        if not CONCRETE_CHAPTER_RE.search(text):
            continue
        if is_concrete_instance_hub_only(text):
            continue
        has_structural_origin_surface = (
            CLOSURESTATUS_BLOCK_RE.search(text) is not None
            or TOP_LEVEL_ORIGIN_RE.search(text) is not None
        )
        if not has_structural_origin_surface:
            continue
        origins = []
        for block in CLOSURESTATUS_BLOCK_RE.finditer(text):
            origins.extend(
                match.group(1).strip()
                for match in ORIGIN_TAG_RE.finditer(block.group(0))
            )
        if not origins:
            origins = [
                match.group(1).strip()
                for match in TOP_LEVEL_ORIGIN_RE.finditer(text)
            ]
        kind = ""
        if not origins:
            kind = "missing-origin"
        elif len(origins) != 1:
            kind = "duplicate-origin"
        elif origins[0] not in VALID_ORIGINS:
            kind = "invalid-origin"
        if kind:
            missing.append({
                "file": str(path.relative_to(REPO_ROOT)),
                "kind": kind,
            })
    return sorted(missing, key=lambda item: str(item["file"]))


def detect_paper_chapter_origin_tags() -> list[dict[str, object]]:
    if not PAPER_PARTS_ROOT.is_dir():
        return []

    violations: list[dict[str, object]] = []
    for path in sorted(PAPER_PARTS_ROOT.rglob("*.tex")):
        if not path.is_file():
            continue
        text = read_text(path)
        chapter = CONCRETE_CHAPTER_RE.search(text)
        if not chapter:
            continue
        surface_text = CLOSURESTATUS_BLOCK_RE.sub("", text)
        origins = [
            match.group(1).strip()
            for match in TOP_LEVEL_ORIGIN_RE.finditer(surface_text)
        ]
        kind = ""
        if not origins:
            kind = "missing-origin"
        elif len(origins) != 1:
            kind = "duplicate-origin"
        elif origins[0] not in VALID_ORIGINS:
            kind = "invalid-origin"
        if not kind:
            continue
        line = text.count("\n", 0, chapter.start()) + 1
        violations.append({
            "file": str(path.relative_to(REPO_ROOT)),
            "line": line,
            "kind": kind,
        })
    return violations


def changed_concrete_instance_tex_paths() -> set[Path] | None:
    """Return changed concrete-instance tex paths when git base context exists."""
    base_ref = os.environ.get("BEDC_CI_BASE_REF", "origin/codex-auto-dev")
    try:
        merge_base = subprocess.check_output(
            ["git", "merge-base", base_ref, "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except subprocess.CalledProcessError:
        return None
    if not merge_base:
        return None
    try:
        output = subprocess.check_output(
            ["git", "diff", "--name-only", merge_base, "--", "papers/bedc/parts/concrete_instances"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return None
    paths: set[Path] = set()
    for line in output.splitlines():
        if line.endswith(".tex"):
            paths.add((REPO_ROOT / line).resolve())
    return paths


CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}"
)
CLOSURESTATUS_END_RE = re.compile(r"\\end\{closurestatus\}")
CLOSURESTATUS_OPEN_FIELDS = (
    "closureclaimkind",
    "closureclassifierincrement",
    "closurenamecert",
    "closureledger",
    "closuregate",
    "closureweightprofile",
    "closureparents",
    "closurelineage",
)
_CLOSURESTATUS_FIELD_NAMES = (
    "theoryclosure",
    "formalstatus",
    "leantarget",
    "bridgestatus",
    "scopeclosed",
    "notclaimed",
    "upgradepath",
    "constructivestory",
    "origin",
    *CLOSURESTATUS_OPEN_FIELDS,
)
CLOSURESTATUS_FIELD_RE = re.compile(
    r"\\(" + "|".join(_CLOSURESTATUS_FIELD_NAMES) + r")\{([^}]*)\}"
)

VALID_CLOSURE_GRADES = {
    "seedClosure", "obligationClosure", "scopedClosure",
    "publicClosure", "bridgedClosure", "matureClosure",
}
VALID_FORMAL_GRADES = {
    "unformalizedV", "formalTargetV", "encodedDefV",
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
}
GRADE_REQUIRES_LEAN_TARGET = {
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
}
STRONG_CLOSURESTATUS_CLAIMS = {"discovery", "positiveDiscovery"}
CLOSURESTATUS_STRONG_CLAIM_REQUIREMENTS = {
    "closurenamecert": "NameCert evidence",
    "closureledger": "ledger evidence",
    "closureclassifierincrement": "classifier increment evidence",
}
POSITIVE_DISCOVERY_REQUIREMENTS = {
    "closuregate": "gate evidence",
    "closureweightprofile": "weight profile evidence",
}
DISCOVERY_LEDGER_KIND_KEYWORDS = {
    "transcription": (
        "transcription",
        "transcribe",
        "paper-to-lean",
        "paper to lean",
        "statement",
    ),
    "backend": (
        "backend",
        "lean",
        "kernel",
        "lake",
        "ci",
        "pdflatex",
    ),
    "trust": (
        "trust",
        "trusted",
        "audit",
        "checked",
        "witness",
    ),
    "dependency": (
        "dependency",
        "dependencies",
        "depends",
        "import",
        "parent",
        "parents",
        "upstream",
        "lineage",
    ),
    "positive": (
        "positive",
        "gate",
        "weight",
        "classifier",
    ),
    "namecert": (
        "namecert",
        "name cert",
    ),
}
DISCOVERY_VERIFICATION_CUES = ("transcription", "backend", "trust", "dependency")
DISCOVERY_SCOPE_GLOBAL_TERMS = (
    "global",
    "globally",
    "universal",
    "universally",
    "all",
    "every",
    "any",
    "arbitrary",
    "canonical",
    "complete",
    "general",
)


def detect_orphan_concrete_subdirs() -> list[dict]:
    """Every subdirectory of `papers/bedc/parts/concrete_instances/` MUST
    name a real BEDC region — i.e. a region for which either:
      (a) `lean4/BEDC/Derived/<X>Up.lean` exists (the standard derived horizon), OR
      (b) the paper has a top-level `<NN>_<X>_namecert_construction.tex`
          chapter (the paper-side region marker).

    Sub-folders that don't match (e.g. `rat_proofs/` holding rat helper
    lemmas) inflate the dossier dependency-graph node set and break
    glossary completeness gates. Move their files up to the parent
    region's directory or rename the folder to a real region name.
    """
    instances = PAPER_PARTS_ROOT / "concrete_instances"
    if not instances.exists():
        return []
    derived = REPO_ROOT / "lean4" / "BEDC" / "Derived"
    # Region names from Lean: BEDC/Derived/<X>Up.lean (file or directory)
    lean_regions: set[str] = set()
    if derived.exists():
        for p in derived.iterdir():
            stem = p.stem if p.is_file() else p.name
            if stem.endswith("Up"):
                core = stem[:-2]
                lean_regions.add(re.sub(r"([a-z])([A-Z])", r"\1_\2", core).lower())
    # Region names from paper: NN_<X>_namecert_construction.tex
    paper_chapter_re = re.compile(r"^\d+_([a-z][a-z0-9_]*)_namecert_construction\.tex$")
    paper_regions: set[str] = set()
    for f in instances.iterdir():
        if f.is_file():
            m = paper_chapter_re.match(f.name)
            if m:
                paper_regions.add(m.group(1))
    known = lean_regions | paper_regions
    orphans: list[dict] = []
    for sub in sorted(instances.iterdir()):
        if not sub.is_dir():
            continue
        if sub.name not in known:
            sample = sorted(p.name for p in sub.iterdir() if p.suffix == ".tex")[:3]
            orphans.append({
                "subdir": str(sub.relative_to(REPO_ROOT)),
                "sample_files": sample,
            })
    return orphans


def collect_closurestatus_blocks(part_root: Path) -> list[dict]:
    out: list[dict] = []
    for tex in part_root.rglob("*.tex"):
        try:
            text = tex.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for m in CLOSURESTATUS_BEGIN_RE.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            tail = text[m.end():]
            end_match = CLOSURESTATUS_END_RE.search(tail)
            if not end_match:
                out.append({
                    "file": str(tex.relative_to(part_root.parent.parent.parent)),
                    "line": line,
                    "region": m.group(1),
                    "error": "no \\end{closurestatus}",
                    "theory_closure": None,
                    "formal_status": None,
                    "lean_target": None,
                    "bridge_status": None,
                    "has_scope": False,
                    "has_notclaimed": False,
                    "has_upgradepath": False,
                    "has_constructive_story": False,
                    "open_fields": {},
                })
                continue
            body = tail[:end_match.start()]
            fields: dict[str, str] = {}
            for fm in CLOSURESTATUS_FIELD_RE.finditer(body):
                fields[fm.group(1)] = fm.group(2).strip()
            open_fields = {
                name: fields[name]
                for name in CLOSURESTATUS_OPEN_FIELDS
                if name in fields
            }
            tc = fields.get("theoryclosure", "").lstrip("\\")
            fs = fields.get("formalstatus", "").lstrip("\\")
            lt = fields.get("leantarget")
            if lt is not None:
                lt = lt.replace("\\_", "_").strip()
            origin = (fields.get("origin") or "human").strip().lower()
            out.append({
                "file": str(tex.relative_to(part_root.parent.parent.parent)),
                "line": line,
                "region": m.group(1),
                "theory_closure": tc or None,
                "formal_status": fs or None,
                "lean_target": lt,
                "bridge_status": fields.get("bridgestatus"),
                "origin": origin,
                "raw_body": body,
                "open_fields": open_fields,
                "has_scope": "scopeclosed" in fields,
                "has_notclaimed": "notclaimed" in fields,
                "has_upgradepath": "upgradepath" in fields,
                "has_constructive_story": "constructivestory" in fields,
            })
    return out


def diagnose_closurestatus_block(block: dict, lean_symbols: set[str]) -> list[str]:
    issues: list[str] = []
    where = f"{block['file']}:{block['line']} (region {block['region']}Up)"
    if block.get("error"):
        issues.append(f"{where}: {block['error']}")
        return issues
    tc = block.get("theory_closure")
    fs = block.get("formal_status")
    lt = block.get("lean_target")
    if not tc:
        issues.append(f"{where}: missing \\theoryclosure")
    elif tc not in VALID_CLOSURE_GRADES:
        issues.append(f"{where}: invalid theoryclosure grade '{tc}'")
    if not fs:
        issues.append(f"{where}: missing \\formalstatus")
    elif fs not in VALID_FORMAL_GRADES:
        issues.append(f"{where}: invalid formalstatus grade '{fs}'")
    if fs in GRADE_REQUIRES_LEAN_TARGET and not lt:
        issues.append(
            f"{where}: \\formalstatus={fs} requires \\leantarget"
        )
    if lt and lt not in lean_symbols:
        issues.append(
            f"{where}: \\leantarget '{lt}' does not resolve under lean4/BEDC/"
        )
    if not block.get("has_scope"):
        issues.append(f"{where}: missing \\scopeclosed (binding scope text)")
    if not block.get("has_notclaimed"):
        issues.append(f"{where}: missing \\notclaimed (claims off the table)")
    if not block.get("has_upgradepath"):
        issues.append(f"{where}: missing \\upgradepath (next-grade obligation)")
    if not block.get("has_constructive_story"):
        issues.append(
            f"{where}: missing \\constructivestory (bottom-up construction story; empty arg ok)"
        )
    origin = block.get("origin", "human")
    if origin not in VALID_ORIGINS:
        issues.append(
            f"{where}: \\origin='{origin}' is not in {{human, ai}}"
        )
    if origin == "ai":
        body = block.get("raw_body") or ""
        # AI-proposed chapters past seedClosure must witness a TasteGate instance.
        non_seed = tc and tc != "seedClosure"
        region = block.get("region") or ""
        instance_marker = f"BEDC.Derived.{region}Up.taste_gate"
        marker_present = instance_marker.replace("_", "\\_") in body or instance_marker in body
        if non_seed and not marker_present:
            issues.append(
                f"{where}: \\origin=ai chapter at theoryclosure={tc} requires "
                f"\\leanchecked{{{instance_marker}}} (TasteGate instance) before leaving seedClosure"
            )
    return issues


def _closurestatus_open_message(block: dict, message: str) -> dict[str, object]:
    return {
        "file": block["file"],
        "line": block["line"],
        "region": f"{block['region']}Up",
        "message": f"{block['file']}:{block['line']} (region {block['region']}Up): {message}",
    }


def diagnose_closurestatus_open_fields(block: dict) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    """Return (warnings, errors) for closurestatus open-field capability lint."""
    if block.get("error"):
        return [], []
    warnings: list[dict[str, object]] = []
    errors: list[dict[str, object]] = []
    open_fields = block.get("open_fields") or {}
    claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
    if not claim_kind:
        return warnings, errors

    missing_base = [
        (field, label)
        for field, label in CLOSURESTATUS_STRONG_CLAIM_REQUIREMENTS.items()
        if not str(open_fields.get(field, "")).strip()
    ]
    classifier_increment = str(open_fields.get("closureclassifierincrement", "")).strip()
    if classifier_increment and classifier_increment != "1":
        errors.append(
            _closurestatus_open_message(
                block,
                "\\closureclassifierincrement must be 1 for open closurestatus claims",
            )
        )
    if claim_kind not in STRONG_CLOSURESTATUS_CLAIMS:
        for field, label in missing_base:
            warnings.append(
                _closurestatus_open_message(
                    block,
                    f"\\closureclaimkind{{{claim_kind}}} lacks \\{field} ({label})",
                )
            )
        return warnings, errors

    for field, label in missing_base:
        errors.append(
            _closurestatus_open_message(
                block,
                f"\\closureclaimkind{{{claim_kind}}} requires \\{field} ({label})",
            )
        )
    if claim_kind == "positiveDiscovery":
        for field, label in POSITIVE_DISCOVERY_REQUIREMENTS.items():
            if not str(open_fields.get(field, "")).strip():
                errors.append(
                    _closurestatus_open_message(
                        block,
                        f"\\closureclaimkind{{{claim_kind}}} requires \\{field} ({label})",
                    )
                )
    return warnings, errors


def _discovery_item(block: dict, kind: str, message: str, evidence: str = "") -> dict[str, object]:
    item: dict[str, object] = {
        "file": block["file"],
        "line": block["line"],
        "region": f"{block['region']}Up",
        "kind": kind,
        "message": message,
    }
    if evidence:
        item["evidence"] = evidence
    return item


def _classify_discovery_ledger_kind(text: str) -> str:
    lower = text.lower()
    hits = [
        kind
        for kind, needles in DISCOVERY_LEDGER_KIND_KEYWORDS.items()
        if any(needle in lower for needle in needles)
    ]
    return hits[0] if len(hits) == 1 else "kind_unknown"


def _discovery_candidate_blocks(blocks: list[dict]) -> list[dict]:
    return [
        block
        for block in blocks
        if block.get("origin") == "ai"
        and block.get("theory_closure") not in (None, "seedClosure")
        and not block.get("error")
    ]


def _field_text(open_fields: dict, *names: str) -> str:
    return "\n".join(
        str(open_fields.get(name, ""))
        for name in names
        if str(open_fields.get(name, "")).strip()
    )


def discovery_audit_payload(blocks: list[dict]) -> dict[str, object]:
    candidates = _discovery_candidate_blocks(blocks)
    ledger_gaps: list[dict[str, object]] = []
    scope_global_risks: list[dict[str, object]] = []
    verification_ledger_gaps: list[dict[str, object]] = []

    for block in candidates:
        open_fields = block.get("open_fields") or {}
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        namecert = str(open_fields.get("closurenamecert", "")).strip()
        ledger = str(open_fields.get("closureledger", "")).strip()
        classifier_increment = str(open_fields.get("closureclassifierincrement", "")).strip()
        ledger_kind = _classify_discovery_ledger_kind(ledger) if ledger else "kind_unknown"

        if not claim_kind:
            ledger_gaps.append(
                _discovery_item(
                    block,
                    "missing_closureclaimkind",
                    "\\closureclaimkind is absent",
                )
            )
        if not namecert:
            ledger_gaps.append(
                _discovery_item(
                    block,
                    "missing_closurenamecert",
                    "\\closurenamecert is absent",
                )
            )
        if not ledger:
            ledger_gaps.append(
                _discovery_item(
                    block,
                    "missing_closureledger",
                    "\\closureledger is absent",
                )
            )
        if not classifier_increment:
            ledger_gaps.append(
                _discovery_item(
                    block,
                    "missing_closureclassifierincrement",
                    "\\closureclassifierincrement is absent",
                )
            )
        if ledger and ledger_kind == "kind_unknown":
            ledger_gaps.append(
                _discovery_item(
                    block,
                    "kind_unknown",
                    "\\closureledger exists but no ledger kind keyword was detected",
                    ledger,
                )
            )
        if claim_kind == "positiveDiscovery":
            for field in ("closuregate", "closureweightprofile"):
                if not str(open_fields.get(field, "")).strip():
                    ledger_gaps.append(
                        _discovery_item(
                            block,
                            f"missing_{field}",
                            f"\\{field} is absent for positiveDiscovery",
                        )
                    )

        raw_body = str(block.get("raw_body") or "")
        lower_body = raw_body.lower()
        for term in DISCOVERY_SCOPE_GLOBAL_TERMS:
            if re.search(rf"\b{re.escape(term)}\b", lower_body):
                scope_global_risks.append(
                    _discovery_item(
                        block,
                        "scope_global_keyword",
                        f"scope text contains global-sounding keyword '{term}'",
                        term,
                    )
                )
                break

        verification_text = _field_text(
            open_fields,
            "closureledger",
            "closureparents",
            "closurelineage",
        )
        lower_verification_text = verification_text.lower()
        for cue in DISCOVERY_VERIFICATION_CUES:
            if cue not in lower_verification_text:
                verification_ledger_gaps.append(
                    _discovery_item(
                        block,
                        f"missing_{cue}_ledger_cue",
                        f"formal verification claim lacks {cue} ledger cue",
                    )
                )

    return {
        "informational": True,
        "candidate_count": len(candidates),
        "ledger_gaps": ledger_gaps,
        "ledger_gap_count": len(ledger_gaps),
        "scope_global_risks": scope_global_risks,
        "scope_global_risk_count": len(scope_global_risks),
        "verification_ledger_gaps": verification_ledger_gaps,
        "verification_ledger_gap_count": len(verification_ledger_gaps),
    }


def audit_payload() -> dict[str, object]:
    changed_files = _get_commit_changed_files()
    declarations, fields = build_declaration_inventory()
    part_labels = collect_part_labels()
    markers = collect_lean_markers()
    leanstmt_manifest, leanstmt_manifest_diagnostics = load_leanstmt_debt_manifest()
    leanstmt_debt = leanstmt_debt_payload(
        markers,
        leanstmt_manifest,
        leanstmt_manifest_diagnostics,
    )

    forbidden: list[dict[str, object]] = []
    for path in lean_files():
        forbidden.extend(collect_forbidden_tokens(path))

    symbols = {d.qualified_name for d in declarations}
    symbols.update(f.qualified_name for f in fields)

    part_label_names = [str(item["label"]) for item in part_labels]
    duplicate_part_labels = {label: count for label, count in Counter(part_label_names).items() if count > 1}
    missing_marker_targets = [
        {"file": m.file, "line": m.line, "macro": m.macro, "target": m.target}
        for m in markers
        if m.target not in symbols
    ]
    case_collisions = detect_case_collision_paths()
    preamble_duplicate_commands = detect_preamble_duplicate_commands()
    concrete_number_collisions = detect_concrete_instance_number_collisions()
    concrete_missing_origin = detect_concrete_instance_missing_origin()
    paper_chapter_origin_tags = detect_paper_chapter_origin_tags()
    closurestatus_blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    closurestatus_diagnostics: list[str] = []
    closurestatus_open_warnings: list[dict[str, object]] = []
    closurestatus_open_errors: list[dict[str, object]] = []
    for block in closurestatus_blocks:
        closurestatus_diagnostics.extend(
            diagnose_closurestatus_block(block, symbols)
        )
        open_warnings, open_errors = diagnose_closurestatus_open_fields(block)
        closurestatus_open_warnings.extend(open_warnings)
        closurestatus_open_errors.extend(open_errors)

    orphan_concrete_subdirs = detect_orphan_concrete_subdirs()

    payload: dict[str, object] = {
        "changed_files": sorted(changed_files) if changed_files is not None else None,
        "forbidden_constructs": forbidden,
        "forbidden_construct_count": len(forbidden),
        "duplicate_part_labels": duplicate_part_labels,
        "missing_marker_targets": missing_marker_targets,
        "case_collisions": case_collisions,
        "closurestatus_blocks_total": len(closurestatus_blocks),
        "closurestatus_blocks": closurestatus_blocks,
        "leanstmt_debt": leanstmt_debt,
        "inventory": inventory_payload(declarations, fields, part_labels, markers),
    }
    _attach_violation_split(payload, "missing_marker_targets", missing_marker_targets, changed_files)
    _attach_violation_split(payload, "case_collisions", case_collisions, changed_files)
    _attach_violation_split(payload, "preamble_duplicate_commands", preamble_duplicate_commands, changed_files)
    _attach_violation_split(payload, "concrete_number_collisions", concrete_number_collisions, changed_files)
    _attach_violation_split(payload, "concrete_missing_origin", concrete_missing_origin, changed_files)
    _attach_violation_split(payload, "paper_chapter_origin_tags", paper_chapter_origin_tags, changed_files)
    closurestatus_diagnostic_items = [
        {"path": str(item).split(":", 1)[0], "message": item}
        for item in closurestatus_diagnostics
    ]
    closurestatus_new, closurestatus_legacy = _split_violations(
        closurestatus_diagnostic_items,
        changed_files,
    )
    payload["closurestatus_diagnostics"] = closurestatus_diagnostics
    payload["closurestatus_diagnostics_count"] = len(closurestatus_diagnostics)
    payload["closurestatus_diagnostics_new_count"] = len(closurestatus_new)
    payload["closurestatus_diagnostics_legacy_count"] = len(closurestatus_legacy)
    payload["closurestatus_diagnostics_new"] = [str(item["message"]) for item in closurestatus_new]
    payload["closurestatus_diagnostics_legacy"] = [str(item["message"]) for item in closurestatus_legacy]
    _attach_violation_split(
        payload,
        "closurestatus_open_errors",
        closurestatus_open_errors,
        changed_files,
    )
    _attach_violation_split(
        payload,
        "closurestatus_open_warnings",
        closurestatus_open_warnings,
        changed_files,
    )
    _attach_violation_split(payload, "orphan_concrete_subdirs", orphan_concrete_subdirs, changed_files)
    return payload


def resolve_lean_file(raw_path: str) -> Path:
    path = Path(raw_path)
    if not path.is_absolute():
        path = (LEAN_ROOT / path).resolve()
    if not path.exists():
        raise FileNotFoundError(f"Lean file not found: {raw_path}")
    if path.suffix != ".lean":
        raise ValueError(f"Expected a .lean file: {raw_path}")
    return path


DERIVED_DOMAIN_PREFIXES = [
    "TaggedOption", "FramedList", "CommRing", "AbGroup",
    "Bool", "Int", "Rat", "Field", "Ring", "Complex", "List", "Option",
    "Prod", "Sum", "Group", "Monoid", "Preorder", "Interval", "Nat",
    "Add", "Vec", "Matrix", "Polynomial", "Module", "Lattice",
]


def _strip_derived_domain_prefix(name: str) -> tuple[str | None, str]:
    """Return (domain, suffix) if name begins with a known derived horizon
    prefix, else (None, name). Longer prefixes are tried first so 'CommRing'
    wins over 'Ring' and 'TaggedOption' wins over 'Option'."""
    for prefix in sorted(DERIVED_DOMAIN_PREFIXES, key=len, reverse=True):
        if name.startswith(prefix):
            return prefix, "_" + name[len(prefix):]
    return None, name


def report_shape_saturation(threshold: int = 3) -> int:
    """Group every theorem/lemma name under BEDC.Derived.* by its
    domain-prefix-stripped suffix and print shapes that are reproduced
    across >= threshold distinct horizons. Phase B uses this as the
    'add fourth instance vs hoist a typeclass' decision input.
    """
    declarations, _ = build_declaration_inventory()
    shape_to_domains: dict[str, set[str]] = {}
    shape_to_examples: dict[str, list[str]] = {}
    for d in declarations:
        if not d.module.startswith("BEDC.Derived."):
            continue
        if d.kind not in ("theorem", "lemma"):
            continue
        domain, suffix = _strip_derived_domain_prefix(d.name)
        if domain is None or len(suffix) <= 1:
            continue
        shape_to_domains.setdefault(suffix, set()).add(domain)
        shape_to_examples.setdefault(suffix, []).append(d.qualified_name)
    saturated = sorted(
        ((shape, doms, shape_to_examples[shape])
         for shape, doms in shape_to_domains.items()
         if len(doms) >= threshold),
        key=lambda t: (-len(t[1]), t[0]),
    )
    if not saturated:
        print(f"[bedc-ci] shape-saturation: no shapes reproduced across >= {threshold} horizons")
        return 0
    print(f"[bedc-ci] shape-saturation: {len(saturated)} saturated shape(s) (threshold = {threshold})")
    for shape, doms, examples in saturated:
        domain_list = ", ".join(sorted(doms))
        print(f"  {shape}  [{len(doms)} horizons: {domain_list}]")
        for example in examples[:3]:
            print(f"    e.g. {example}")
    print(
        "[bedc-ci] phase B HARD GATE: when a candidate target's "
        "domain-stripped conclusion shape appears above, hoist a typeclass "
        "or pivot — do not add the next concrete instance."
    )
    return 0


def cmd_audit(args: argparse.Namespace) -> int:
    if getattr(args, "shape_saturation", False):
        return report_shape_saturation()
    payload = audit_payload()
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        inv = payload["inventory"]
        print(
            "[bedc-ci] audit:"
            f" lean_files={inv['lean_files_scanned']}"
            f" declarations={inv['declarations_total']}"
            f" part_labels={inv['part_labels_total']}"
            f" lean_markers={inv['lean_markers_total']}"
        )
        if payload["forbidden_constructs"]:
            print(f"[bedc-ci] forbidden constructs: {payload['forbidden_construct_count']}")
            for item in payload["forbidden_constructs"][:50]:
                print(f"  {item['file']}:{item['line']}:{item['column']}: {item['token']}")
        if payload["missing_marker_targets"]:
            print(
                "[bedc-ci] unresolved Lean markers: "
                f"{payload['missing_marker_targets_new_count']} new (BLOCKING), "
                f"{payload['missing_marker_targets_legacy_count']} legacy (warning)"
            )
            for item in payload["missing_marker_targets"][:50]:
                print(f"  {item['file']}:{item['line']} {item['macro']} -> {item['target']}")
        if payload["duplicate_part_labels"]:
            dup = payload["duplicate_part_labels"]
            print(f"[bedc-ci] duplicate paper labels: {len(dup)}")
            label_to_files: dict[str, list[str]] = {}
            for item in collect_part_labels():
                lbl = str(item.get("label", ""))
                if lbl in dup:
                    f = item.get("file", "?")
                    ln = item.get("line", "?")
                    label_to_files.setdefault(lbl, []).append(f"{f}:{ln}")
            for label, count in list(dup.items())[:50]:
                locs = label_to_files.get(label, [])
                loc_str = ", ".join(locs) if locs else f"appears {count} times"
                print(f"  {label}  @ {loc_str}")
        if payload["case_collisions"]:
            print(
                "[bedc-ci] case-only-different paths in git index: "
                f"{payload['case_collisions_new_count']} new (BLOCKING), "
                f"{payload['case_collisions_legacy_count']} legacy (warning)"
            )
            for item in payload["case_collisions"][:50]:
                print(f"  {' , '.join(item['paths'])}")
            print(
                "[bedc-ci] resolution: pick the canonical casing, then "
                "`git update-index --force-remove <wrong-case-path>`; "
                "also remove the duplicate import / reference."
            )
        if payload["preamble_duplicate_commands"]:
            print(
                "[bedc-ci] preamble duplicate commands: "
                f"{payload['preamble_duplicate_commands_new_count']} new (BLOCKING), "
                f"{payload['preamble_duplicate_commands_legacy_count']} legacy (warning)"
            )
            for item in payload["preamble_duplicate_commands"][:50]:
                print(f"  {item['name']}")
                for occurrence in item["occurrences"]:
                    print(
                        f"    {occurrence['file']}:{occurrence['line']} "
                        f"{occurrence['kind']}"
                    )
        if payload["concrete_number_collisions"]:
            print(
                "[bedc-ci] concrete_instances numbering collisions: "
                f"{payload['concrete_number_collisions_new_count']} new (BLOCKING), "
                f"{payload['concrete_number_collisions_legacy_count']} legacy (warning)"
            )
            for item in payload["concrete_number_collisions"][:50]:
                print(f"  {item['region']}  subdir_exists={item['subdir_exists']}")
                for path in item["files"]:
                    print(f"    {path}")
        if payload["concrete_missing_origin"]:
            print(
                "[bedc-ci] concrete_instances missing/invalid origin tags: "
                f"{payload['concrete_missing_origin_new_count']} new (BLOCKING), "
                f"{payload['concrete_missing_origin_legacy_count']} legacy (warning)"
            )
            for item in payload["concrete_missing_origin"][:50]:
                print(f"  {item['file']}: {item['kind']}")
        if payload["paper_chapter_origin_tags"]:
            print(
                "[bedc-ci] paper_chapter_origin_tags: "
                f"{payload['paper_chapter_origin_tags_new_count']} new (BLOCKING), "
                f"{payload['paper_chapter_origin_tags_legacy_count']} legacy (warning)"
            )
            for item in payload["paper_chapter_origin_tags"][:50]:
                print(f"  {item['file']}:{item['line']}: {item['kind']}")
        if payload["closurestatus_diagnostics"]:
            print(
                "[bedc-ci] closurestatus block diagnostics: "
                f"{payload['closurestatus_diagnostics_new_count']} new (BLOCKING), "
                f"{payload['closurestatus_diagnostics_legacy_count']} legacy (warning)"
            )
            for msg in payload["closurestatus_diagnostics"][:80]:
                print(f"  {msg}")
            print(
                "[bedc-ci] resolution: every \\begin{closurestatus}{<X>Up}"
                " block must declare \\theoryclosure, \\formalstatus, "
                "\\scopeclosed, \\notclaimed, \\upgradepath; if "
                "\\formalstatus is theoremCheckedV or above, \\leantarget "
                "is required and must resolve under lean4/BEDC/."
            )
        if payload["closurestatus_open_warnings"]:
            print(
                "[bedc-ci] closurestatus open-field warnings: "
                f"{payload['closurestatus_open_warnings_count']}"
            )
            for item in payload["closurestatus_open_warnings"][:80]:
                print(f"  {item['message']}")
        if payload["closurestatus_open_errors"]:
            print(
                "[bedc-ci] closurestatus open-field errors: "
                f"{payload['closurestatus_open_errors_new_count']} new (BLOCKING), "
                f"{payload['closurestatus_open_errors_legacy_count']} legacy (warning)"
            )
            for item in payload["closurestatus_open_errors"][:80]:
                print(f"  {item['message']}")
        if payload["orphan_concrete_subdirs"]:
            print(
                "[bedc-ci] orphan concrete_instances/ subdirectories: "
                f"{payload['orphan_concrete_subdirs_new_count']} new (BLOCKING), "
                f"{payload['orphan_concrete_subdirs_legacy_count']} legacy (warning)"
            )
            for item in payload["orphan_concrete_subdirs"][:50]:
                files = ", ".join(item["sample_files"]) or "(empty)"
                print(f"  {item['subdir']}/  files: {files}")
            print(
                "[bedc-ci] resolution: every concrete_instances/<X>/ folder "
                "must name a real BEDC region (i.e. a derived horizon with "
                "lean4/BEDC/Derived/<X>Up.lean OR a paper namecert chapter "
                "named NN_<X>_namecert_construction.tex). Move helper files "
                "into the parent region's folder or rename the orphan."
            )
        leanstmt_debt = payload["leanstmt_debt"]
        print(
            "[bedc-ci] leanstmt debt:"
            f" live_sites={len(leanstmt_debt['live_sites'])}"
            f" manifest_entries={len(leanstmt_debt['manifest_entries'])}"
            f" violations={len(leanstmt_debt['violations'])}"
        )
        if leanstmt_debt["violations"]:
            for item in leanstmt_debt["violations"][:80]:
                site = item.get("file") or item.get("path") or "manifest"
                line = item.get("line") or item.get("entry_index")
                target = item.get("target")
                where = f"{site}:{line}" if line is not None else str(site)
                suffix = f" -> {target}" if target else ""
                print(f"  {item.get('kind')}: {where}{suffix}: {item.get('message')}")

    failures = (
        payload["forbidden_construct_count"]
        + payload["missing_marker_targets_new_count"]
        + len(payload["duplicate_part_labels"])
        + payload["case_collisions_new_count"]
        + payload["preamble_duplicate_commands_new_count"]
        + payload["concrete_number_collisions_new_count"]
        + payload["concrete_missing_origin_new_count"]
        + payload["paper_chapter_origin_tags_new_count"]
        + payload["closurestatus_diagnostics_new_count"]
        + payload["closurestatus_open_errors_new_count"]
        + payload["orphan_concrete_subdirs_new_count"]
        + len(payload["leanstmt_debt"]["violations"])
    )
    return 0 if failures == 0 else 1


def cmd_inventory(args: argparse.Namespace) -> int:
    declarations, fields = build_declaration_inventory()
    payload = inventory_payload(
        declarations,
        fields,
        collect_part_labels(),
        collect_lean_markers(),
    )
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            "[bedc-ci] inventory:"
            f" lean_files={payload['lean_files_scanned']}"
            f" declarations={payload['declarations_total']}"
            f" field_targets={payload['field_targets_total']}"
            f" part_labels={payload['part_labels_total']}"
            f" lean_markers={payload['lean_markers_total']}"
        )
    return 0


def cmd_theorem_status(args: argparse.Namespace) -> int:
    payload = theorem_status_payload()
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            "[bedc-ci] theorem-status:"
            f" source={payload['source']}"
            f" records={payload['records_total']}"
        )
    return 0


def cmd_manifest(args: argparse.Namespace) -> int:
    """Emit a release-grade manifest combining declaration inventory, paper
    labels, lean-marker correspondence, and git/package metadata. Suitable as
    a release artifact alongside the PDF."""
    declarations, fields = build_declaration_inventory()
    inv = inventory_payload(
        declarations,
        fields,
        collect_part_labels(),
        collect_lean_markers(),
    )

    try:
        git_sha = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=True,
        ).stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        git_sha = ""

    lakefile_path = LEAN_ROOT / "lakefile.lean"
    toolchain_path = LEAN_ROOT / "lean-toolchain"
    lakefile = lakefile_path.read_text(encoding="utf-8") if lakefile_path.exists() else ""
    toolchain = toolchain_path.read_text(encoding="utf-8").strip() if toolchain_path.exists() else ""
    pkg_match = re.search(r'package\s+"?([A-Za-z0-9_]+)', lakefile)
    package_name = pkg_match.group(1) if pkg_match else "BEDC"
    mathlib_free = "mathlib" not in lakefile.lower()

    release_tag = args.release_tag or os.environ.get("RELEASE_TAG") or None

    manifest = {
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "git": {
            "sha": git_sha,
            "tag": release_tag,
        },
        "package": {
            "name": package_name,
            "entry_module": "BEDC",
            "lean_toolchain": toolchain,
            "mathlib_free": mathlib_free,
            "axiom_policy": "zero (enforced by tools/check-axioms.py)",
            "sorry_policy": "zero (enforced by Phase D in lean4/scripts/codex_formalize.py)",
        },
        "stats": {
            "lean_files": inv["lean_files_scanned"],
            "paper_part_files": inv["paper_part_files_scanned"],
            "paper_tex_files": inv["paper_tex_files_scanned"],
            "declarations_total": inv["declarations_total"],
            "field_targets_total": inv["field_targets_total"],
            "declaration_kinds": inv["declaration_kinds"],
            "part_labels_total": inv["part_labels_total"],
            "part_label_prefixes": inv["part_label_prefixes"],
            "lean_markers_total": inv["lean_markers_total"],
            "lean_marker_macros": inv["lean_marker_macros"],
        },
        "modules": sorted({d["module"] for d in inv["declarations"]}),
        "declarations": inv["declarations"],
        "field_targets": inv["field_targets"],
        "paper_labels": inv["paper_labels"],
        "lean_markers": inv["lean_markers"],
    }

    text = json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        out = Path(args.output)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(text, encoding="utf-8")
        print(f"[bedc-ci] manifest written to {out}")
    else:
        sys.stdout.write(text)
    return 0


def cmd_manifest_coverage(args: argparse.Namespace) -> int:
    paper_markers = collect_paper_leanchecked_targets()
    manifest_entries = collect_manifest_entry_targets()
    if args.scope:
        paper_markers = {
            target for target in paper_markers
            if target.startswith(args.scope)
        }
        manifest_entries = {
            target for target in manifest_entries
            if target.startswith(args.scope)
        }
    marker_count = len(paper_markers)
    entry_count = len(manifest_entries)
    ratio = (entry_count / marker_count * 100.0) if marker_count else 100.0
    missing = sorted(paper_markers - manifest_entries)

    print("manifest-coverage report")
    if args.scope:
        print(f"  scope: {args.scope}")
    print(f"  paper_markers (\\leanchecked): {marker_count}")
    print(f"  manifest_entries (Lean-side):  {entry_count}")
    print(f"  coverage_ratio: {entry_count}/{marker_count} = {ratio:.2f}%")
    print()
    print("  Not yet in manifest (sample of 20):")
    for target in missing[:20]:
        print(f"    {target}")
    return 0


def cmd_marker_existence_audit(args: argparse.Namespace) -> int:
    markers = collect_marker_existence_markers()
    lean_names = collect_marker_existence_lean_names()
    missing = [marker for marker in markers if marker.target not in lean_names]
    resolved = len(markers) - len(missing)
    missing_ratio = (len(missing) / len(markers) * 100.0) if markers else 0.0

    print("marker-existence-audit report")
    print(f"  markers_total: {len(markers)}")
    print(f"  markers_resolved: {resolved}")
    print(f"  markers_missing: {len(missing)} (M/N = {missing_ratio:.2f}%)")
    print()
    print("  -- Missing markers (first 30) by kind:")
    if not missing:
        print("  none")
        return 0

    by_kind: dict[str, list[LeanMarkerRecord]] = {}
    for marker in missing:
        by_kind.setdefault(marker.macro, []).append(marker)
    emitted = 0
    for kind in sorted(by_kind):
        if emitted >= 30:
            break
        print(f"  {kind}:")
        for marker in by_kind[kind]:
            if emitted >= 30:
                break
            print(f"    {marker.target}  ({marker.file}:{marker.line})")
            emitted += 1
    return 0


DEFAULT_FORBIDDEN_AXIOMS: tuple[str, ...] = (
    "Classical.choice",
    "Quot.sound",
)
STRICT_FORBIDDEN_AXIOMS: tuple[str, ...] = DEFAULT_FORBIDDEN_AXIOMS + ("propext",)
PRINT_AXIOMS_RE = re.compile(
    r"'([\w.·’]+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[(.*?)\])"
)
METACIC_SCOPE = "BEDC.MetaCIC"
METACIC_IMPORT = "BEDC.MetaCIC"


def scan_metacic_declarations() -> list[DeclarationRecord]:
    decls: list[DeclarationRecord] = []
    metacic_root = BEDC_ROOT / "MetaCIC"
    if not metacic_root.exists():
        return []
    for path in sorted(metacic_root.rglob("*.lean")):
        file_decls, _fields = collect_declarations(path)
        for decl in file_decls:
            if decl.qualified_name.startswith(METACIC_SCOPE + "."):
                decls.append(decl)
    return sorted(decls, key=lambda d: (d.qualified_name, d.kind, d.file, d.line))


def parse_axioms_output(output: str, declarations: dict[str, str]) -> list[AxiomReportRecord]:
    reports: list[AxiomReportRecord] = []
    for match in PRINT_AXIOMS_RE.finditer(output):
        name = match.group(1)
        if name not in declarations:
            continue
        raw_axioms = match.group(2)
        axioms = tuple(a.strip() for a in (raw_axioms or "").split(",") if a.strip())
        reports.append(AxiomReportRecord(name=name, kind=declarations[name], axioms=axioms))
    return reports


def metacic_axiom_summary(report: AxiomReportRecord) -> str:
    if not report.axioms:
        if report.kind in {"inductive", "structure", "class"}:
            return "inhabited"
        return "no axioms"
    return ", ".join(report.axioms)


def format_axiom_set(axioms: Iterable[str]) -> str:
    return "{" + ", ".join(sorted(axioms)) + "}"


def cmd_metacic_purity(args: argparse.Namespace) -> int:
    decls = scan_metacic_declarations()
    if not decls:
        print("metacic-purity report (scope: BEDC.MetaCIC)")
        print("total: 0 declarations")
        print(f"forbidden: {format_axiom_set(STRICT_FORBIDDEN_AXIOMS)}")
        print("violations: 0")
        return 0

    declaration_kinds = {decl.qualified_name: decl.kind for decl in decls}
    lean_source = (
        f"import {METACIC_IMPORT}\n\n"
        + "\n".join(f"#print axioms {decl.qualified_name}" for decl in decls)
        + "\n"
    )
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=LEAN_ROOT,
        input=lean_source,
        text=True,
        capture_output=True,
        check=False,
    )
    output = (result.stdout or "") + "\n" + (result.stderr or "")
    reports = parse_axioms_output(output, declaration_kinds)
    by_name = {report.name: report for report in reports}
    ordered_reports = [by_name[decl.qualified_name] for decl in decls if decl.qualified_name in by_name]
    missing = [decl.qualified_name for decl in decls if decl.qualified_name not in by_name]

    forbidden = set(STRICT_FORBIDDEN_AXIOMS)
    violation_kinds = {"theorem", "lemma"}
    violations = [
        report for report in ordered_reports
        if report.kind in violation_kinds and forbidden.intersection(report.axioms)
    ]

    print("metacic-purity report (scope: BEDC.MetaCIC)")
    for report in ordered_reports:
        print(
            f"  {report.name:<56}"
            f" ({report.kind:<9}) -- {metacic_axiom_summary(report)}"
        )
    print(f"total: {len(ordered_reports)} declarations")
    print(f"forbidden: {format_axiom_set(STRICT_FORBIDDEN_AXIOMS)}")
    print(f"violations: {len(violations)}")

    if result.returncode != 0:
        print(f"[bedc-ci] metacic-purity FAIL: lean returned {result.returncode}", file=sys.stderr)
        tail = "\n".join(output.strip().splitlines()[-20:])
        if tail:
            print(tail, file=sys.stderr)
        return result.returncode
    if missing:
        print(
            f"[bedc-ci] metacic-purity FAIL: {len(missing)} declaration(s) had no parsed #print axioms result",
            file=sys.stderr,
        )
        for name in missing[:50]:
            print(f"  {name}", file=sys.stderr)
        if len(missing) > 50:
            print(f"  ... and {len(missing) - 50} more", file=sys.stderr)
        return 1
    if args.strict and violations:
        print(f"[bedc-ci] metacic-purity FAIL: {len(violations)} forbidden dependency declaration(s)")
        for report in violations[:50]:
            bad = sorted(forbidden.intersection(report.axioms))
            print(f"  {report.name} -> {', '.join(bad)}")
        if len(violations) > 50:
            print(f"  ... and {len(violations) - 50} more")
        return 1
    return 0


def normalize_type_text(text: str) -> str:
    text = (text
        .replace("∀", "forall")
        .replace("→", "->")
        .replace("∧", "/\\")
        .replace("↔", "<->"))
    return " ".join(text.split())


def run_lean_check(lean_name: str) -> tuple[int, str]:
    preamble = "\n".join([
        "import BEDC",
        "open BEDC.FKernel.Mark",
        "open BEDC.FKernel.Hist",
        "open BEDC.FKernel.Cont",
        "open BEDC.FKernel.Ext",
        "open BEDC.FKernel.Sig",
        "open BEDC.FKernel.Bundle",
        "open BEDC.FKernel.Ask",
        "open BEDC.FKernel.Package",
        "open BEDC.FKernel.NameCert",
        "open BEDC.FKernel.Unary",
        "open BEDC.BaseReflection",
        f"#check {lean_name}",
        "",
    ])
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=LEAN_ROOT,
        input=preamble,
        text=True,
        capture_output=True,
        check=False,
    )
    return result.returncode, (result.stdout or "") + "\n" + (result.stderr or "")


def cmd_manifest_check(args: argparse.Namespace) -> int:
    manifest_path = Path(args.manifest)
    if not manifest_path.is_absolute():
        manifest_path = (REPO_ROOT / manifest_path).resolve()
    try:
        entries = json.loads(manifest_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"[bedc-ci] manifest-check: missing manifest {manifest_path}", file=sys.stderr)
        return 1
    except json.JSONDecodeError as exc:
        print(f"[bedc-ci] manifest-check: invalid JSON {manifest_path}: {exc}", file=sys.stderr)
        return 1

    if not isinstance(entries, list):
        print("[bedc-ci] manifest-check: manifest root must be a list", file=sys.stderr)
        return 1

    failures: list[dict[str, object]] = []
    results: list[dict[str, object]] = []
    for idx, entry in enumerate(entries, start=1):
        if not isinstance(entry, dict):
            failures.append({"index": idx, "error": "entry is not an object"})
            continue
        lean_name = str(entry.get("lean_name", "")).strip()
        expected = entry.get("expected_type_contains", [])
        if not lean_name or not isinstance(expected, list) or not all(isinstance(item, str) for item in expected):
            failures.append({"index": idx, "lean_name": lean_name, "error": "invalid lean_name or expected_type_contains"})
            continue
        rc, output = run_lean_check(lean_name)
        normalized_output = normalize_type_text(output)
        missing = [
            fragment for fragment in expected
            if normalize_type_text(fragment) not in normalized_output
        ]
        passed = rc == 0 and not missing
        result = {
            "lean_name": lean_name,
            "paper_claim_label": entry.get("paper_claim_label", ""),
            "passed": passed,
            "missing_fragments": missing,
        }
        results.append(result)
        if not passed:
            result["lean_returncode"] = rc
            result["lean_output"] = output.strip()
            failures.append(result)

    if args.json:
        print(json.dumps({
            "manifest": str(manifest_path),
            "entries": len(entries),
            "passed": len(failures) == 0,
            "results": results,
        }, indent=2, ensure_ascii=False))
    else:
        print(f"[bedc-ci] manifest-check: entries={len(entries)} manifest={manifest_path.relative_to(REPO_ROOT)}")
        for result in results:
            status = "PASS" if result["passed"] else "FAIL"
            label = result["paper_claim_label"]
            suffix = f" ({label})" if label else ""
            print(f"  {status} {result['lean_name']}{suffix}")
            for fragment in result["missing_fragments"]:
                print(f"    missing: {fragment}")

    return 0 if not failures else 1


def camel_stem(up_name: str) -> str:
    base = up_name[:-2] if up_name.endswith("Up") else up_name
    return base[:1].lower() + base[1:]


def split_lean_tokens(text: str) -> list[str]:
    return re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text)


def normalize_lean_type(text: str) -> str:
    return re.sub(r"\s+", " ", text.strip())


def parse_carrier_fields(mk_body: str, carrier_name: str) -> tuple[tuple[str, ...], tuple[str, ...]] | None:
    body = normalize_lean_type(mk_body)
    if not body:
        return None

    segments: list[tuple[str, str]] = []
    for match in re.finditer(r"\((?P<names>[^():]+?)\s*:\s*(?P<typ>[^()]+?)\)", body):
        names = tuple(split_lean_tokens(match.group("names")))
        typ = normalize_lean_type(match.group("typ"))
        if names and typ:
            segments.append((" ".join(names), typ))

    if segments:
        field_names: list[str] = []
        field_types: list[str] = []
        for names_raw, typ in segments:
            names = split_lean_tokens(names_raw)
            field_names.extend(names)
            field_types.extend([typ] * len(names))
        if field_names and field_types:
            return tuple(field_names), tuple(field_types)

    before_result = body.split("→", 1)[0]
    before_result = before_result.split(f": {carrier_name}", 1)[0]
    match = re.search(r":\s*(?P<typ>[A-Za-z0-9_'.]+)\s*$", before_result)
    if not match:
        return None
    typ = match.group("typ")
    names_part = before_result[:match.start()].replace(":", " ")
    names = tuple(split_lean_tokens(names_part))
    if not names:
        return None
    return names, tuple(typ for _ in names)


def extract_inductive_block(text: str, carrier_name: str) -> str | None:
    pattern = re.compile(
        rf"(?ms)^\s*inductive\s+{re.escape(carrier_name)}\s*:\s*Type\s+where\s*(?P<body>.*?)(?=^\s*(?:deriving|namespace|end|def|private\s+def|theorem|private\s+theorem|lemma|instance|inductive|structure|class)\b|\Z)"
    )
    match = pattern.search(text)
    return match.group("body") if match else None


def parse_carrier_records(path: Path, text: str) -> list[CarrierRecord]:
    rel = str(path.relative_to(REPO_ROOT))
    records: list[CarrierRecord] = []
    for match in re.finditer(r"(?m)^\s*inductive\s+(?P<name>[A-Za-z0-9_']+Up)\s*:\s*Type\s+where\b", text):
        name = match.group("name")
        block = extract_inductive_block(text[match.start():], name)
        if not block:
            continue
        mk_match = re.search(r"(?ms)^\s*\|\s+mk\b(?P<body>.*?)(?=^\s*\||^\s*deriving\b|\Z)", block)
        if not mk_match:
            continue
        parsed = parse_carrier_fields(mk_match.group("body"), name)
        if not parsed:
            continue
        field_names, field_types = parsed
        shape, status = parse_to_event_flow_shape(text, name, field_names)
        records.append(
            CarrierRecord(
                name=name,
                file=rel,
                field_names=field_names,
                field_types=field_types,
                phase2_status=status,
                to_event_flow_shape=shape,
                namecert_hash=extract_namecert_hash(text, name),
            )
        )
    return records


def extract_def_body(text: str, def_name: str) -> str | None:
    pattern = re.compile(
        rf"(?ms)^\s*(?:private\s+)?def\s+{re.escape(def_name)}\b.*?(?P<body>(?:--[^\n]*\n\s*)?\|.*?)(?=^\s*(?:private\s+)?(?:def|theorem|lemma|instance|inductive|structure|class)\b|\Z)"
    )
    match = pattern.search(text)
    if match:
        return match.group("body")
    typed_pattern = re.compile(
        rf"(?ms)^\s*(?:private\s+)?def\s+{re.escape(def_name)}\b.*?EventFlow\s*(?P<body>.*?)(?=^\s*(?:private\s+)?(?:def|theorem|lemma|instance|inductive|structure|class)\b|\Z)"
    )
    match = typed_pattern.search(text)
    return match.group("body") if match else None


def parse_tag_bits(raw: str) -> int | None:
    bits = re.findall(r"BMark\.(b[01])", raw)
    if not bits or bits[-1] != "b0" or any(bit != "b1" for bit in bits[:-1]):
        return None
    return len(bits) - 1


def parse_direct_event_flow_shape(body: str, stem: str, field_positions: dict[str, int]) -> tuple[tuple[str, int], ...] | None:
    body = strip_comments_and_strings(body)
    token_re = re.compile(
        rf"\[(?P<tag>(?:\s*BMark\.b[01]\s*,?)+)\]|{re.escape(stem)}EncodeBHist\s+(?P<field>[A-Za-z0-9_']+)"
    )
    shape: list[tuple[str, int]] = []
    for match in token_re.finditer(body):
        tag_raw = match.group("tag")
        if tag_raw is not None:
            tag = parse_tag_bits(tag_raw)
            if tag is not None:
                shape.append(("tag", tag))
            continue
        field = match.group("field")
        if field in field_positions:
            shape.append(("encode", field_positions[field]))
    if not shape:
        return None
    encode_positions = [value for kind, value in shape if kind == "encode"]
    if not encode_positions:
        return None
    return tuple(shape)


def parse_fields_map_shape(body: str, stem: str, arity: int) -> tuple[tuple[str, int], ...] | None:
    if re.search(rf"\.map\s+{re.escape(stem)}EncodeBHist\b", body):
        return tuple(("encode", idx) for idx in range(arity))
    return None


def parse_to_event_flow_shape(
    text: str,
    carrier_name: str,
    field_names: tuple[str, ...],
) -> tuple[tuple[tuple[str, int], ...] | None, str]:
    stem = camel_stem(carrier_name)
    body = extract_def_body(text, f"{stem}ToEventFlow")
    if body is None:
        return None, "no_toEventFlow"
    field_positions = {name: idx for idx, name in enumerate(field_names)}
    direct = parse_direct_event_flow_shape(body, stem, field_positions)
    if direct is not None:
        return direct, "parsed"
    mapped = parse_fields_map_shape(body, stem, len(field_names))
    if mapped is not None:
        return mapped, "parsed"
    return None, "unparseable_toEventFlow"


def normalize_namecert_text(text: str) -> str:
    cleaned = strip_comments_and_strings(text)
    cleaned = re.sub(r"\{[^{}]*:\s*BHist\s*\}", "{_ : BHist}", cleaned)
    cleaned = re.sub(r"\([^()]*:\s*BHist\s*\)", "(_ : BHist)", cleaned)
    cleaned = re.sub(r"\b[A-Za-z_][A-Za-z0-9_']*\s*:\s*BHist\b", "_ : BHist", cleaned)
    return re.sub(r"\s+", " ", cleaned).strip()


def extract_namecert_hash(text: str, carrier_name: str) -> str | None:
    candidates = [
        rf"(?ms)^\s*theorem\s+{re.escape(carrier_name[:-2])}NameCert\b(?P<body>.*?)(?=^\s*(?:private\s+)?(?:def|theorem|lemma|instance|inductive|structure|class)\b|\Z)",
        rf"(?ms)^\s*theorem\s+[A-Za-z0-9_']*(?:NameCert|semanticNameCert)\b(?P<body>.*?)(?=^\s*(?:private\s+)?(?:def|theorem|lemma|instance|inductive|structure|class)\b|\Z)",
        rf"(?ms)^\s*instance\s+[A-Za-z0-9_']*\b[^\n]*NameCert\s+{re.escape(carrier_name)}\b(?P<body>.*?)(?=^\s*(?:private\s+)?(?:def|theorem|lemma|instance|inductive|structure|class)\b|\Z)",
    ]
    for pattern in candidates:
        match = re.search(pattern, text)
        if not match:
            continue
        normalized = normalize_namecert_text(match.group("body"))
        if normalized:
            return hashlib.sha256(normalized.encode("utf-8")).hexdigest()[:16]
    return None


def collect_carrier_records() -> list[CarrierRecord]:
    records: list[CarrierRecord] = []
    derived_root = BEDC_ROOT / "Derived"
    for path in sorted(derived_root.rglob("*.lean")):
        try:
            text = read_text(path)
        except OSError:
            continue
        records.extend(parse_carrier_records(path, text))
    return records


def carrier_member_payload(record: CarrierRecord, include_phase2: bool = True) -> dict[str, object]:
    payload: dict[str, object] = {
        "name": record.name,
        "file": record.file,
        "field_names": list(record.field_names),
        "field_types": list(record.field_types),
        "nameCert_hash": record.namecert_hash,
    }
    if include_phase2:
        payload["phase2_status"] = record.phase2_status
        payload["toEventFlow_shape"] = shape_to_json(record.to_event_flow_shape)
    return payload


def shape_to_json(shape: tuple[tuple[str, int], ...] | None) -> list[dict[str, int | str]] | None:
    if shape is None:
        return None
    return [{"kind": kind, "value": value} for kind, value in shape]


def shape_sketch(shape: tuple[tuple[str, int], ...] | None, limit: int = 14) -> str:
    if shape is None:
        return "unparsed"
    parts = [f"t{value}" if kind == "tag" else f"e{value}" for kind, value in shape]
    if len(parts) > limit:
        return " ".join(parts[:limit]) + f" ... +{len(parts) - limit}"
    return " ".join(parts)


def cmd_carrier_isomorphism(args: argparse.Namespace) -> int:
    records = collect_carrier_records()
    phase1_map: dict[tuple[int, tuple[str, ...]], list[CarrierRecord]] = {}
    for record in records:
        key = (record.arity, tuple(sorted(record.field_types)))
        phase1_map.setdefault(key, []).append(record)
    phase1_items = [
        (key, sorted(members, key=lambda item: (item.name, item.file)))
        for key, members in sorted(phase1_map.items(), key=lambda item: (item[0][0], item[0][1]))
        if len(members) >= 2
    ]

    phase1_survivors = {record.name for _key, members in phase1_items for record in members}
    phase2_map: dict[tuple[int, tuple[str, ...], tuple[tuple[str, int], ...]], list[CarrierRecord]] = {}
    for record in records:
        if record.name not in phase1_survivors or record.to_event_flow_shape is None:
            continue
        key = (record.arity, tuple(sorted(record.field_types)), record.to_event_flow_shape)
        phase2_map.setdefault(key, []).append(record)
    phase2_items = [
        (key, sorted(members, key=lambda item: (item.name, item.file)))
        for key, members in sorted(
            phase2_map.items(),
            key=lambda item: (item[0][0], item[0][1], item[0][2]),
        )
        if len(members) >= 2
    ]

    hash_map: dict[str, list[CarrierRecord]] = {}
    for record in records:
        if record.namecert_hash is not None:
            hash_map.setdefault(record.namecert_hash, []).append(record)
    phase3_clusters = [
        (key, sorted(members, key=lambda item: (item.name, item.file)))
        for key, members in sorted(hash_map.items())
        if len(members) >= 2
    ]
    phase3_hits = sum(1 for record in records if record.namecert_hash is not None)

    if args.json:
        payload = {
            "carriers_scanned": len(records),
            "phase1_buckets": [
                {
                    "fingerprint": {"arity": key[0], "field_types": list(key[1])},
                    "members": [carrier_member_payload(member) for member in members],
                }
                for key, members in phase1_items
            ],
            "phase2_buckets": [
                {
                    "fingerprint": {
                        "arity": key[0],
                        "field_types": list(key[1]),
                        "shape": shape_to_json(key[2]),
                    },
                    "members": [carrier_member_payload(member) for member in members],
                }
                for key, members in phase2_items
            ],
            "phase3_clusters": [
                {
                    "nameCert_hash": namecert_hash,
                    "members": [carrier_member_payload(member) for member in members],
                }
                for namecert_hash, members in phase3_clusters
            ],
            "informational": True,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print("[bedc-ci] carrier-isomorphism (informational):")
        print(f"  carriers_scanned={len(records)}")
        print(f"  phase1_buckets={len(phase1_items)}  (≥2-member structural)")
        print(f"  phase2_buckets={len(phase2_items)}  (≥2-member after toEventFlow shape refinement)")
        print(f"  phase3_hits={phase3_hits}     (chapters with matching nameCert_hash)")
        if args.verbose:
            for idx, (key, members) in enumerate(phase2_items, start=1):
                arity, _field_types, shape = key
                print(f"  phase2 bucket #{idx} [arity={arity}, shape={shape_sketch(shape)}]:")
                width = max(len(member.name) for member in members)
                for member in members:
                    print(f"    {member.name.ljust(width)} ({member.file})")
            no_phase2 = [
                record for _key, members in phase1_items for record in members
                if record.to_event_flow_shape is None
            ]
            if no_phase2:
                print("  phase1 members without parseable toEventFlow:")
                for record in sorted(no_phase2, key=lambda item: (item.name, item.file))[:40]:
                    print(f"    {record.name} ({record.file}) phase2_status={record.phase2_status}")
                if len(no_phase2) > 40:
                    print(f"    ... and {len(no_phase2) - 40} more")
    return 0


def cmd_conservativity_audit(args: argparse.Namespace) -> int:
    """Informational survey of baseline imports of ai-proposed chapters.

    Historically (2026-05-10 introduction) this was a hard gate: baseline
    (\\origin=human) chapters were forbidden from importing ai-proposed
    (\\origin=ai) chapter modules, enforcing a machine version of
    metalogical conservativity (Lean 4 module-level isolation guarantees
    baseline theorem provability is unaffected by ai chapters when no
    such import exists).

    The gate was removed by user decision: with sufficient taste, human
    work *should* be able to consume ai-discovered structure — that's
    what theory discovery looks like. This subcommand is retained as an
    informational survey so the cross-chapter import graph stays
    observable, but it never fails the build (always returns 0).

    Implementation:
      1. read closurestatus blocks, group chapters by \\origin
      2. for each ai chapter, determine its lean module prefix
         (BEDC.Derived.<X>Up.* by convention)
      3. grep "import <ai_module>" in every lean file outside ai-chapter
         modules; report any hit as an informational baseline→ai edge
    """
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    ai_chapters: list[str] = []
    for b in blocks:
        if b.get("origin") == "ai":
            region = b.get("region")
            if region:
                ai_chapters.append(region)
    ai_chapters = sorted(set(ai_chapters))

    if not ai_chapters:
        msg = "[bedc-ci] conservativity-audit (informational): no \\origin=ai chapters; nothing to survey"
        if args.json:
            print(json.dumps({"ai_chapters": [], "baseline_to_ai_edges": [], "informational": True}, indent=2))
        else:
            print(msg)
        return 0

    # ai chapter -> module prefixes that count as "owned" by this chapter.
    # The region recovered from \begin{closurestatus}{\<X>Up} is `<X>` (no Up
    # suffix); the lean module convention is `BEDC.Derived.<X>Up.*`.
    ai_prefixes: dict[str, list[str]] = {}
    for region in ai_chapters:
        ai_prefixes[region] = [f"BEDC.Derived.{region}Up"]

    flat_prefixes = [p for ps in ai_prefixes.values() for p in ps]

    def _is_ai_owned_module(module_name: str) -> bool:
        return any(
            module_name == p or module_name.startswith(p + ".")
            for p in flat_prefixes
        )

    violations: list[dict[str, object]] = []
    baseline_files_scanned = 0
    for lean_file in BEDC_ROOT.rglob("*.lean"):
        rel = lean_file.relative_to(LEAN_ROOT)
        module = ".".join(rel.with_suffix("").parts)
        if _is_ai_owned_module(module):
            continue  # ai chapter file may import other ai chapters
        baseline_files_scanned += 1
        try:
            text = lean_file.read_text()
        except OSError:
            continue
        for line_no, raw in enumerate(text.splitlines(), start=1):
            stripped = raw.strip()
            if not stripped.startswith("import "):
                continue
            imported = stripped[len("import "):].split("--", 1)[0].strip()
            for region, prefixes in ai_prefixes.items():
                for p in prefixes:
                    if imported == p or imported.startswith(p + "."):
                        violations.append({
                            "baseline_module": module,
                            "baseline_file": str(rel),
                            "line": line_no,
                            "imports": imported,
                            "leaks_from_ai_chapter": region,
                        })
                        break

    if args.json:
        payload = {
            "ai_chapters": ai_chapters,
            "ai_module_prefixes": flat_prefixes,
            "baseline_files_scanned": baseline_files_scanned,
            "baseline_to_ai_edges": violations,
            "baseline_to_ai_edge_count": len(violations),
            "informational": True,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            f"[bedc-ci] conservativity-audit (informational):"
            f" ai_chapters={len(ai_chapters)}"
            f" baseline_files_scanned={baseline_files_scanned}"
            f" baseline_to_ai_edges={len(violations)}"
        )
        if args.verbose:
            for region in ai_chapters:
                prefixes = ai_prefixes[region]
                print(f"  ai chapter {region} -> {prefixes}")
        if violations:
            print(f"[bedc-ci] {len(violations)} baseline import(s) of ai chapters (allowed, reported for observability):")
            for v in violations[:30]:
                print(
                    f"  {v['baseline_file']}:{v['line']}"
                    f" imports {v['imports']}"
                    f" (ai chapter: {v['leaks_from_ai_chapter']})"
                )
            if len(violations) > 30:
                print(f"  ... and {len(violations) - 30} more")
    return 0


def cmd_discovery_audit(args: argparse.Namespace) -> int:
    payload = discovery_audit_payload(collect_closurestatus_blocks(PAPER_PARTS_ROOT))
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            "[bedc-ci] discovery-audit (informational):"
            f" candidates={payload['candidate_count']}"
            f" ledger_gaps={payload['ledger_gap_count']}"
            f" scope_global_risks={payload['scope_global_risk_count']}"
            f" verification_ledger_gaps={payload['verification_ledger_gap_count']}"
        )
        if args.verbose:
            for title, key in (
                ("ledger gaps", "ledger_gaps"),
                ("scope/global risks", "scope_global_risks"),
                ("verification ledger gaps", "verification_ledger_gaps"),
            ):
                items = payload[key]
                if not items:
                    continue
                print(f"[bedc-ci] {title}:")
                for item in items[:80]:
                    evidence = item.get("evidence")
                    suffix = f" evidence={evidence!r}" if evidence else ""
                    print(
                        f"  {item['file']}:{item['line']}"
                        f" {item['region']} {item['kind']}:"
                        f" {item['message']}{suffix}"
                    )
                if len(items) > 80:
                    print(f"  ... and {len(items) - 80} more")
    return 0


def cmd_axiom_purity(args: argparse.Namespace) -> int:
    """Check that every BEDC theorem's transitive axiom dependency set is
    contained within the allowed Lean stdlib subset.

    Default forbidden: Classical.choice, Quot.sound (the controversial axioms).
    --strict additionally forbids propext (true zero-axiom-dependency mode).

    Implementation: writes a temp Lean file that does `#print axioms X` for
    every public BEDC theorem (from inventory), runs `lake env lean`, parses
    the output, and reports any forbidden axiom dependency.
    """
    import tempfile

    if args.allow_propext:
        forbidden = set(DEFAULT_FORBIDDEN_AXIOMS)
    else:
        forbidden = set(STRICT_FORBIDDEN_AXIOMS) if args.strict else set(DEFAULT_FORBIDDEN_AXIOMS)
    extra = [a.strip() for a in (args.also_forbid or "").split(",") if a.strip()]
    forbidden.update(extra)

    declarations, _fields = build_declaration_inventory()
    theorems = sorted(
        {
            d.qualified_name
            for d in declarations
            if d.kind in ("theorem", "lemma")
            and d.qualified_name.startswith("BEDC.")
            and not d.is_private
            and module_olean_path(d.module).exists()
        }
    )
    if not theorems:
        print("[bedc-ci] axiom-purity: no BEDC theorems found", file=sys.stderr)
        return 0

    # Race-safe tmp-dir handling. Default --tmp-dir is LEAN_ROOT, which is a
    # worker worktree directory under .worktrees/round_R<N>/lean4/ during
    # recovery. Worktree cleanup can race the audit subprocess: orchestrator
    # may remove the worktree (or its parent dir) between argparse and
    # tempfile.NamedTemporaryFile creation, causing FileNotFoundError that
    # marks the recovery ticket "unrecoverable" even though the round's
    # commit was already produced. Two-step guard:
    #   1. mkdir(parents=True, exist_ok=True) on tmp_dir before any tempfile
    #      creation — handles the common case where the dir was removed but
    #      can be re-created.
    #   2. If the dir is unreachable (parent gone, permission denied),
    #      fall back to the system tempfile dir. `lake env lean` accepts an
    #      absolute path to the source file; its import resolution is set
    #      by `cwd=LEAN_ROOT` and the lake project's manifest, not by the
    #      tempfile's location.
    tmp_dir_path = Path(args.tmp_dir)
    try:
        tmp_dir_path.mkdir(parents=True, exist_ok=True)
    except OSError:
        import tempfile as _tempfile
        tmp_dir_path = Path(_tempfile.gettempdir())
    args.tmp_dir = tmp_dir_path

    # Startup sweep: tempfile cleanup. Each chunk's `try/finally:
    # tmp_path.unlink()` below works for normal exit, but a SIGKILL'd
    # axiom-purity (e.g. cooldown burst, recovery worker killed) leaves
    # stale axiom_audit_*.lean files in tmp_dir. Sweep files older than
    # 1h to bound accumulation without racing concurrent audits (a
    # sibling audit's chunk file written less than 1h ago is safe).
    # Observed in production: 918 leftover files accumulated under
    # `lean4/axiom_audit_*.lean` over 2 weeks of high-concurrency runs.
    import time as _time
    sweep_now = _time.time()
    sweep_cutoff = sweep_now - 3600  # 1h
    try:
        for stale in tmp_dir_path.glob("axiom_audit_*.lean"):
            try:
                if stale.stat().st_mtime < sweep_cutoff:
                    stale.unlink()
            except OSError:
                pass
    except OSError:
        pass

    # Walk every .lean file under BEDC/ so that every theorem in `theorems`
    # is in scope. Root `BEDC.lean` cannot re-export all sub-files because
    # the project uses a parent-hub + namespace-extension pattern: sub-files
    # import the parent hub, so the parent hub re-exporting them would
    # cycle.
    all_modules: list[str] = []
    seen_public_decls: set[str] = set()
    for path in sorted(BEDC_ROOT.rglob("*.lean")):
        module = ".".join(path.relative_to(LEAN_ROOT).with_suffix("").parts)
        if not module_olean_path(module).exists():
            continue
        file_decls, _fields = collect_declarations(path)
        public_decls = {d.qualified_name for d in file_decls if not d.is_private}
        if public_decls and public_decls.issubset(seen_public_decls):
            continue
        all_modules.append(module)
        seen_public_decls.update(public_decls)
    import_lines = [f"import {m}" for m in all_modules]
    chunk_size = max(1, int(args.chunk_size))
    chunks = [theorems[i : i + chunk_size] for i in range(0, len(theorems), chunk_size)]

    pure: list[str] = []
    impure: list[tuple[str, list[str]]] = []
    violations: list[tuple[str, str]] = []
    lean_failed = False
    last_returncode = 0
    tail_outputs: list[str] = []
    for idx, chunk in enumerate(chunks, start=1):
        lean_lines = list(import_lines)
        lean_lines.append("")
        lean_lines.extend(f"#print axioms {name}" for name in chunk)
        lean_source = "\n".join(lean_lines) + "\n"

        # Race-safe tempfile creation. The tmp_dir may disappear between
        # the entry-point mkdir and this call when worktree cleanup races
        # the audit; retry once after re-creating it, then fall back to
        # the system tempdir.
        def _make_tempfile(dir_path: Path):
            return tempfile.NamedTemporaryFile(
                mode="w",
                suffix=".lean",
                prefix=f"axiom_audit_{idx:03d}_",
                dir=str(dir_path),
                delete=False,
                encoding="utf-8",
            )

        try:
            tmp = _make_tempfile(args.tmp_dir)
        except FileNotFoundError:
            try:
                args.tmp_dir.mkdir(parents=True, exist_ok=True)
                tmp = _make_tempfile(args.tmp_dir)
            except (OSError, FileNotFoundError):
                args.tmp_dir = Path(tempfile.gettempdir())
                tmp = _make_tempfile(args.tmp_dir)
        try:
            tmp.write(lean_source)
            tmp_path = Path(tmp.name)
        finally:
            tmp.close()

        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(tmp_path)],
                cwd=LEAN_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
        finally:
            try:
                tmp_path.unlink()
            except OSError:
                pass

        output = (result.stdout or "") + "\n" + (result.stderr or "")
        for match in PRINT_AXIOMS_RE.finditer(output):
            decl = match.group(1)
            axs_raw = match.group(2)
            if axs_raw is None:
                pure.append(decl)
                continue
            axs = [a.strip() for a in axs_raw.split(",") if a.strip()]
            impure.append((decl, axs))
            for ax in axs:
                if ax in forbidden:
                    violations.append((decl, ax))
        if result.returncode != 0:
            lean_failed = True
            last_returncode = result.returncode
            tail = "\n".join(output.strip().splitlines()[-20:])
            if tail:
                tail_outputs.append(f"[chunk {idx}/{len(chunks)} rc={result.returncode}]\n{tail}")

    parsed = set(pure)
    parsed.update(decl for decl, _axs in impure)
    missing = sorted(set(theorems) - parsed)
    result_returncode = last_returncode

    if args.json:
        payload = {
            "theorems_total": len(theorems),
            "pure_count": len(pure),
            "impure_count": len(impure),
            "pure": sorted(pure),
            "violations": [
                {"declaration": decl, "axiom": ax} for decl, ax in violations
            ],
            "missing_results": missing,
            "lean_returncode": result_returncode,
            "chunks": len(chunks),
            "chunk_size": chunk_size,
            "forbidden_axioms": sorted(forbidden),
            "passed": not lean_failed and not missing and len(violations) == 0,
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            f"[bedc-ci] axiom-purity:"
            f" theorems={len(theorems)}"
            f" pure={len(pure)}"
            f" impure={len(impure)}"
            f" forbidden={sorted(forbidden)}"
        )
        if impure and args.verbose:
            counts: Counter[str] = Counter()
            for _decl, axs in impure:
                for ax in axs:
                    counts[ax] += 1
            for ax, n in counts.most_common():
                print(f"  axiom dep: {ax} ({n} declarations)")
        if violations:
            print(f"[bedc-ci] axiom-purity FAIL: {len(violations)} forbidden dependency(s)")
            for decl, ax in violations[:50]:
                print(f"  {decl} -> {ax}")
            if len(violations) > 50:
                print(f"  ... and {len(violations) - 50} more")
        if lean_failed:
            print(f"[bedc-ci] axiom-purity FAIL: lean returned {result_returncode} (in {len(chunks)} chunks of {chunk_size})")
            for tail in tail_outputs:
                print(tail)
        if missing:
            print(f"[bedc-ci] axiom-purity FAIL: {len(missing)} theorem(s) had no parsed #print axioms result")
            for decl in missing[:50]:
                print(f"  {decl}")
            if len(missing) > 50:
                print(f"  ... and {len(missing) - 50} more")

    return 0 if not lean_failed and not missing and not violations else 1


def cmd_verify_files(args: argparse.Namespace) -> int:
    lean_files_to_check = [resolve_lean_file(p) for p in args.paths]
    overall_rc = 0
    for lean_file in lean_files_to_check:
        rel = lean_file.relative_to(LEAN_ROOT)
        print(f"[bedc-ci] verifying {rel}")
        result = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=LEAN_ROOT,
            text=True,
            capture_output=True,
        )
        if result.stdout:
            print(result.stdout, end="")
        if result.stderr:
            print(result.stderr, end="", file=sys.stderr)
        if result.returncode != 0:
            overall_rc = result.returncode
            print(f"[bedc-ci] verification failed: {rel}", file=sys.stderr)
    return overall_rc


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="BEDC Lean automation helpers")
    sub = p.add_subparsers(dest="command", required=True)

    audit_p = sub.add_parser("audit", help="Run BEDC audit checks")
    audit_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    audit_p.add_argument(
        "--shape-saturation",
        action="store_true",
        help=(
            "Report Derived/<X>Up shape saturation (count of horizons that "
            "carry each conclusion shape). Phase B uses count >= 3 as a hard "
            "gate to switch from 'add another instance' to 'hoist a typeclass'."
        ),
    )
    audit_p.set_defaults(func=cmd_audit)

    inv_p = sub.add_parser("inventory", help="Emit declaration and paper inventory")
    inv_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    inv_p.set_defaults(func=cmd_inventory)

    theorem_status_p = sub.add_parser(
        "theorem-status",
        help="Emit an informational derived theorem-status reader view",
    )
    theorem_status_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    theorem_status_p.set_defaults(func=cmd_theorem_status)

    manifest_p = sub.add_parser("manifest", help="Emit release-grade JSON manifest (inventory + git/package metadata)")
    manifest_p.add_argument("--output", type=str, default=None, help="Output file path (defaults to stdout)")
    manifest_p.add_argument("--release-tag", type=str, default=None, help="Release tag to embed (overrides $RELEASE_TAG env)")
    manifest_p.set_defaults(func=cmd_manifest)

    manifest_coverage_p = sub.add_parser(
        "manifest-coverage",
        help="Report informational coverage of paper \\leanchecked markers in BEDC.Manifest.Entries",
    )
    manifest_coverage_p.add_argument(
        "--scope",
        type=str,
        default=None,
        help="Filter paper markers and manifest entries to Lean names with this namespace prefix",
    )
    manifest_coverage_p.set_defaults(func=cmd_manifest_coverage)

    marker_existence_p = sub.add_parser(
        "marker-existence-audit",
        help="Report informational paper Lean markers that do not exist in lean4/BEDC/",
    )
    marker_existence_p.set_defaults(func=cmd_marker_existence_audit)

    manifest_check_p = sub.add_parser(
        "manifest-check",
        help="Check selected canonical Lean theorem type shapes against bedc_manifest.json",
    )
    manifest_check_p.add_argument(
        "--manifest",
        type=str,
        default=str(TYPE_MANIFEST_PATH.relative_to(REPO_ROOT)),
        help="Manifest JSON path, relative to the repository root by default",
    )
    manifest_check_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    manifest_check_p.set_defaults(func=cmd_manifest_check)

    purity_p = sub.add_parser(
        "axiom-purity",
        help="Audit transitive axiom dependencies of BEDC theorems (forbids Classical.choice, Quot.sound)",
    )
    purity_p.add_argument("--strict", action="store_true",
                          help="Additionally forbid propext (true zero-axiom-dependency mode)")
    purity_p.add_argument("--allow-propext", action="store_true",
                          help="Explicitly allow propext (override --strict)")
    purity_p.add_argument("--also-forbid", type=str, default="",
                          help="Comma-separated axiom names to additionally forbid")
    purity_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    purity_p.add_argument("--verbose", "-v", action="store_true", help="Show axiom dep counts")
    purity_p.add_argument("--tmp-dir", type=str, default=str(LEAN_ROOT),
                          help="Directory for the temporary Lean axiom-audit file")
    purity_p.add_argument("--chunk-size", type=int, default=2000,
                          help="Split #print axioms queries into chunks of this size, one lean subprocess each (default: 2000, prevents stack overflow on large theorem sets)")
    purity_p.set_defaults(func=cmd_axiom_purity)

    metacic_purity_p = sub.add_parser(
        "metacic-purity",
        help="Report axiom dependencies for BEDC.MetaCIC declarations",
    )
    metacic_purity_p.add_argument(
        "--strict",
        action="store_true",
        help="Exit 1 if a BEDC.MetaCIC theorem or lemma depends on Classical.choice, Quot.sound, or propext",
    )
    metacic_purity_p.set_defaults(func=cmd_metacic_purity)

    verify_p = sub.add_parser("verify-files", help="Run lake env lean on selected files")
    verify_p.add_argument("paths", nargs="+", help="Lean file paths, relative to lean4/")
    verify_p.set_defaults(func=cmd_verify_files)

    conservativity_p = sub.add_parser(
        "conservativity-audit",
        help="Informational survey of baseline imports of ai-proposed chapters (always exit 0)",
    )
    conservativity_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    conservativity_p.add_argument("--verbose", "-v", action="store_true", help="Show per-chapter detail")
    conservativity_p.set_defaults(func=cmd_conservativity_audit)

    discovery_p = sub.add_parser(
        "discovery-audit",
        help="Informational survey of ai-origin discovery ledger, scope, and verification cues (always exit 0)",
    )
    discovery_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    discovery_p.add_argument("--verbose", "-v", action="store_true", help="Show per-gap detail")
    discovery_p.set_defaults(func=cmd_discovery_audit)

    carrier_iso_p = sub.add_parser(
        "carrier-isomorphism",
        help="Informational survey of structurally isomorphic Derived <X>Up carriers (always exit 0)",
    )
    carrier_iso_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    carrier_iso_p.add_argument("--verbose", "-v", action="store_true", help="Show bucket members")
    carrier_iso_p.set_defaults(func=cmd_carrier_isomorphism)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except BrokenPipeError:
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
        raise SystemExit(0)

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
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual|local)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|inductive|class|structure)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)?"
)
FIELD_RE = re.compile(r"^\s{2,}(?P<name>[A-Za-z0-9_']+)\s*:")
CTOR_RE = re.compile(r"^\s*\|\s+(?P<name>[A-Za-z0-9_']+)\b")
DISCOVERY_DELTA_LEDGER_TYPE_RE = re.compile(
    r":\s*(?:[A-Za-z0-9_'.]+\.)?DiscoveryDeltaLedger\b",
    re.DOTALL,
)
DISCOVERY_DELTA_LEDGER_RESULT_RE = re.compile(
    r"^\s*(?:[A-Za-z0-9_'.]+\.)?DiscoveryDeltaLedger\b"
)
DISCOVERY_TASTE_GATE_RESULT_RE = re.compile(
    r"^\s*(?:[A-Za-z0-9_'.]+\.)?DiscoveryTasteGate\b"
)
POSITIVE_DISCOVERY_RESULT_RE = re.compile(
    r"^\s*(?:[A-Za-z0-9_'.]+\.)?PositiveDiscovery\b"
)
CLASSIFIER_DISAGREEMENT_RESULT_RE = re.compile(
    r"^\s*(?:[A-Za-z0-9_'.]+\.)?ClassifierDisagreement\b"
)
DISAGREEMENT_SUPPORT_RESULT_RE = re.compile(
    r"\b(?:[A-Za-z0-9_'.]+\.)?DisagreementSupport\b"
)
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
DNA_HASH_RE = re.compile(
    r"(?m)^\s*\\dnahash\{(?P<value>[^{}\n]+)\}\s*$"
)
DNA_HASH_LINE_RE = re.compile(
    r"(?m)^\s*\\dnahash\{[^{}\n]+\}\s*\n?"
)
DNA_LOCUS_NAMES = (
    "statement",
    "dependencies",
    "proof",
    "certificates",
    "ledger",
    "status",
    "canonicalSite",
    "closingSeal",
)
DNA_CLOSURE_LEDGER_FIELDS = {
    "closureclaimkind",
    "closureclassifierincrement",
    "closureledger",
    "closureweightprofile",
    "closureparents",
    "closurelineage",
}
DNA_CLOSURE_STATUS_FIELDS = {"theoryclosure", "formalstatus"}
DNA_CLOSURE_CERTIFICATE_FIELDS = {
    "constructivestory",
    "scopeclosed",
    "bridgestatus",
    "notclaimed",
    "upgradepath",
    "origin",
    "closurenamecert",
    "closuregate",
}
DNA_CLOSUREAT_RE = re.compile(
    r"(?m)^\s*\\closureat\{[^}]*\}\{[^}]*\}(?:\[[^\]]*\])?\s*$"
)
DNA_PROOF_ENV_RE = re.compile(
    r"(?ms)\\begin\{proof\}.*?\\end\{proof\}"
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


@dataclass(frozen=True)
class DiscoveryDeltaLedgerRecord:
    name: str
    qualified_name: str
    file: str
    line: int
    chapter_region: str
    chapter_key: str
    has_classifier_shift: bool


@dataclass(frozen=True)
class AdversarialWitness:
    target: str
    target_fingerprint: str
    family: str
    strength: str
    lens: str
    verdict: str
    evidence: dict[str, object]
    clearance: list[str]

    def to_json(self) -> dict[str, object]:
        return {
            "target": self.target,
            "target_fingerprint": self.target_fingerprint,
            "family": self.family,
            "strength": self.strength,
            "lens": self.lens,
            "verdict": self.verdict,
            "evidence": self.evidence,
            "clearance": self.clearance,
        }


@dataclass(frozen=True)
class LeanSourceScan:
    declarations: list[DeclarationRecord]
    fields: list[FieldRecord]
    declaration_headers: dict[str, str]
    declaration_bodies: dict[str, str]
    discovery_delta_ledgers: list[DiscoveryDeltaLedgerRecord]


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


def _strip_lean_guillemet(name: str) -> str:
    if name.startswith("«") and name.endswith("»"):
        return name[1:-1]
    return name


def _camel_to_snake(name: str) -> str:
    name = _strip_lean_guillemet(name)
    name = re.sub(r"[^A-Za-z0-9]+", "_", name)
    name = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    name = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", name)
    return re.sub(r"_+", "_", name).strip("_").lower()


def _ledger_name_stem(name: str) -> str:
    stem = _strip_lean_guillemet(name)
    for suffix in (
        "DeltaLedger",
        "DiscoveryDeltaLedger",
        "_delta_ledger",
        "_discovery_delta_ledger",
    ):
        if stem.endswith(suffix):
            return stem[: -len(suffix)]
    return stem


def _region_key(region: object) -> str:
    text = str(region or "")
    if text.endswith("Up"):
        text = text[:-2]
    return _camel_to_snake(text)


def _normalize_lean_target(text: object) -> str:
    return str(text or "").replace(r"\_", "_").strip()


def _declaration_header_result_type(header: str) -> str | None:
    if ":" not in header:
        return None
    header_prefix = header
    for delimiter in (":=", " where", "\nwhere"):
        if delimiter in header_prefix:
            header_prefix = header_prefix.split(delimiter, 1)[0]
    depth = 0
    result_colon: int | None = None
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    for idx, ch in enumerate(header_prefix):
        if ch in pairs:
            depth += 1
        elif ch in closing and depth > 0:
            depth -= 1
        elif ch == ":" and depth == 0:
            result_colon = idx
    if result_colon is None:
        return None
    return " ".join(header_prefix[result_colon + 1:].strip().split())


def _result_type_mentions(pattern: re.Pattern[str], header: str) -> bool:
    result_type = _declaration_header_result_type(header)
    if result_type is None:
        return False
    return pattern.search(result_type) is not None


def _header_has_discovery_delta_ledger_result(header: str) -> bool:
    result_type = _declaration_header_result_type(header)
    if result_type is None:
        return False
    return DISCOVERY_DELTA_LEDGER_TYPE_RE.search(f": {result_type}") is not None


def _declaration_body_from_lines(lines: list[str], start_idx: int) -> str:
    body_lines = [lines[start_idx]]
    j = start_idx + 1
    while j < len(lines):
        line = lines[j]
        if (
            line.strip()
            and not line.startswith((" ", "\t", "|"))
            and not re.match(r"^\s*(where|deriving)\b", line)
        ):
            break
        body_lines.append(line)
        j += 1
    return "\n".join(body_lines)


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


def scan_lean_sources() -> LeanSourceScan:
    declarations: list[DeclarationRecord] = []
    fields: list[FieldRecord] = []
    declaration_headers: dict[str, str] = {}
    declaration_bodies: dict[str, str] = {}
    ledgers: list[DiscoveryDeltaLedgerRecord] = []

    for path in lean_files():
        text = strip_comments_and_strings(read_text(path))
        lines = text.splitlines()
        module = module_name(path)
        rel_file = str(path.relative_to(REPO_ROOT))
        namespace_stack: list[str] = []
        for idx, line in enumerate(lines, start=1):
            update_namespace_stack(line, namespace_stack)
            namespace = declaration_namespace(module, namespace_stack)
            match = DECL_RE.match(line)
            if not match:
                continue
            kind = match.group("kind")
            name = (match.group("name") or f"<anonymous_{kind}_{idx}>").strip()
            qualified = qualified_name(name, namespace)
            is_private = re.match(
                r"^\s*(?:@\[[^\]]+\]\s*)*private\b",
                line,
            ) is not None
            declarations.append(
                DeclarationRecord(
                    module=module,
                    file=rel_file,
                    line=idx,
                    kind=kind,
                    name=name,
                    qualified_name=qualified,
                    is_private=is_private,
                )
            )

            header_lines = [line]
            scan_idx = idx
            while (
                scan_idx < len(lines)
                and len(header_lines) < 24
                and ":=" not in "\n".join(header_lines)
                and not re.search(r"\bwhere\b", "\n".join(header_lines))
            ):
                next_line = lines[scan_idx]
                if next_line.strip() and not next_line.startswith((" ", "\t")):
                    break
                header_lines.append(next_line)
                scan_idx += 1
            header_text = "\n".join(header_lines)
            declaration_headers[qualified] = header_text
            body_text = _declaration_body_from_lines(lines, idx - 1)
            declaration_bodies[qualified] = body_text

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
                                file=rel_file,
                                line=j + 1,
                            )
                        )
                    j += 1

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
                                file=rel_file,
                                line=j + 1,
                            )
                        )
                    j += 1

            if kind in ("def", "abbrev") and _header_has_discovery_delta_ledger_result(
                header_text,
            ):
                ledgers.append(
                    DiscoveryDeltaLedgerRecord(
                        name=name,
                        qualified_name=qualified,
                        file=rel_file,
                        line=idx,
                        chapter_region=_ledger_name_stem(name),
                        chapter_key=_region_key(_ledger_name_stem(name)),
                        has_classifier_shift=re.search(
                            r"\bclassifier_shift\s*:=\s*some\b",
                            body_text,
                        ) is not None,
                    )
                )

    return LeanSourceScan(
        declarations=declarations,
        fields=fields,
        declaration_headers=declaration_headers,
        declaration_bodies=declaration_bodies,
        discovery_delta_ledgers=sorted(
            ledgers,
            key=lambda record: (record.chapter_key, record.qualified_name),
        ),
    )


def collect_declaration_headers() -> dict[str, str]:
    return scan_lean_sources().declaration_headers


def build_declaration_inventory() -> tuple[list[DeclarationRecord], list[FieldRecord]]:
    scan = scan_lean_sources()
    return scan.declarations, scan.fields


def collect_discovery_delta_ledgers() -> list[DiscoveryDeltaLedgerRecord]:
    return scan_lean_sources().discovery_delta_ledgers


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


def _manifest_diagnostic(
    path: Path,
    kind: str,
    message: str,
    **extra: object,
) -> dict[str, object]:
    return {
        "kind": kind,
        "path": display_path(path),
        "message": message,
        **extra,
    }


def _validate_leanstmt_manifest_root(
    raw: object,
    path: Path,
) -> tuple[dict[str, object] | None, list[dict[str, object]]]:
    if not isinstance(raw, dict):
        return None, [
            _manifest_diagnostic(
                path,
                "manifest_invalid_shape",
                "manifest root must be an object",
            )
        ]

    diagnostics: list[dict[str, object]] = []
    allowed_top_keys = {"schema", "entries"}
    extra_top_keys = sorted(set(raw) - allowed_top_keys)
    missing_top_keys = sorted(allowed_top_keys - set(raw))
    if extra_top_keys:
        diagnostics.append(_manifest_diagnostic(
            path,
            "manifest_extra_top_keys",
            f"unexpected top-level keys: {', '.join(extra_top_keys)}",
            keys=extra_top_keys,
        ))
    if missing_top_keys:
        diagnostics.append(_manifest_diagnostic(
            path,
            "manifest_missing_top_keys",
            f"missing top-level keys: {', '.join(missing_top_keys)}",
            keys=missing_top_keys,
        ))
    if raw.get("schema") != "leanstmt_debt_manifest.v1":
        diagnostics.append(_manifest_diagnostic(
            path,
            "manifest_schema_mismatch",
            "schema must be leanstmt_debt_manifest.v1",
            schema=raw.get("schema"),
        ))
    if not isinstance(raw.get("entries"), list):
        diagnostics.append(_manifest_diagnostic(
            path,
            "manifest_entries_invalid",
            "entries must be a list",
        ))
        return None, diagnostics

    return raw, diagnostics


def _parse_leanstmt_manifest_entry(
    raw_entry: object,
    path: Path,
    entry_index: int,
) -> tuple[LeanStmtDebtEntry | None, list[dict[str, object]]]:
    entry_site = {"path": display_path(path), "entry_index": entry_index}
    if not isinstance(raw_entry, dict):
        return None, [{
            **entry_site,
            "kind": "manifest_entry_invalid",
            "message": "entry must be an object",
        }]

    diagnostics: list[dict[str, object]] = []
    required = {"file", "target", "discharge_plan"}
    allowed_entry_keys = required
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

    if not isinstance(file_value, str) or not isinstance(target_value, str) or not isinstance(plan_value, str):
        return None, diagnostics

    return LeanStmtDebtEntry(
        file=file_value.strip(),
        target=target_value.strip(),
        discharge_plan=plan_value.strip(),
    ), diagnostics


def load_leanstmt_debt_manifest(
    path: Path = LEANSTMT_DEBT_MANIFEST_PATH,
) -> tuple[list[LeanStmtDebtEntry], list[dict[str, object]]]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return [], [
            _manifest_diagnostic(path, "manifest_missing", f"manifest not found: {display_path(path)}")
        ]
    except json.JSONDecodeError as exc:
        return [], [
            _manifest_diagnostic(path, "manifest_invalid_json", f"invalid JSON: {exc.msg}", line=exc.lineno)
        ]

    manifest, diagnostics = _validate_leanstmt_manifest_root(raw, path)
    if manifest is None:
        return [], diagnostics

    entries: list[LeanStmtDebtEntry] = []
    seen: dict[tuple[str, str], int] = {}
    for idx, raw_entry in enumerate(manifest["entries"]):
        entry, entry_diagnostics = _parse_leanstmt_manifest_entry(raw_entry, path, idx)
        diagnostics.extend(entry_diagnostics)
        if entry is None:
            continue

        key = _leanstmt_site_key(entry.file, entry.target)
        if key in seen:
            diagnostics.append({
                "path": display_path(path),
                "entry_index": idx,
                "kind": "manifest_duplicate_key",
                "file": entry.file,
                "target": entry.target,
                "first_entry_index": seen[key],
                "message": f"duplicate manifest key: {entry.file} -> {entry.target}",
            })
        else:
            seen[key] = idx

        entries.append(entry)

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
            stale_manifest_entries.append({
                "kind": "stale_manifest_entry",
                "file": entry.file,
                "target": entry.target,
                "message": f"manifest entry has no live leanstmt site: {entry.file} -> {entry.target}",
            })

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
                "file": entry.file,
                "target": entry.target,
                "discharge_plan": entry.discharge_plan,
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
    return {decl.qualified_name for decl in scan_lean_sources().declarations}


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
    paths: set[Path] = set()
    try:
        dirty_output = subprocess.check_output(
            ["git", "diff", "--name-only", "HEAD", "--", "papers/bedc/parts/concrete_instances"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        )
        for line in dirty_output.splitlines():
            if line.endswith(".tex"):
                paths.add((REPO_ROOT / line).resolve())
    except subprocess.CalledProcessError:
        pass

    base_ref = os.environ.get("BEDC_CI_BASE_REF", "origin/codex-auto-dev")
    try:
        merge_base = subprocess.check_output(
            ["git", "merge-base", base_ref, "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except subprocess.CalledProcessError:
        return paths or None
    if not merge_base:
        return paths or None
    try:
        output = subprocess.check_output(
            ["git", "diff", "--name-only", merge_base, "--", "papers/bedc/parts/concrete_instances"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return paths or None
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

DNA_MACRO_NAMES = {
    "autoref",
    "ref",
    "ref*",
    "leanchecked",
    "leanvariant",
    "leansorryd",
    "leanstmt",
    "leandef",
    "leantarget",
    "theoryclosure",
    "formalstatus",
    "constructivestory",
    "scopeclosed",
    "bridgestatus",
    "notclaimed",
    "upgradepath",
    "origin",
    *CLOSURESTATUS_OPEN_FIELDS,
}


@dataclass(frozen=True)
class TheoremDnaRecord:
    path: Path
    rel_path: str
    region: str
    locus_text: dict[str, str]
    computed_hash: str
    computed_locus_hashes: dict[str, str]
    stored_hash: str | None
    stored_locus_hashes: dict[str, str]
    stored_value: str | None

    @property
    def covered(self) -> bool:
        return self.stored_value is not None

    @property
    def current(self) -> bool:
        if self.stored_hash != self.computed_hash:
            return False
        if not self.stored_locus_hashes:
            return True
        return all(
            self.stored_locus_hashes.get(name) == self.computed_locus_hashes.get(name)
            for name in DNA_LOCUS_NAMES
        )


def _parse_balanced_arg(text: str, open_brace: int) -> tuple[str, int] | None:
    if open_brace >= len(text) or text[open_brace] != "{":
        return None
    depth = 0
    start = open_brace + 1
    i = open_brace
    while i < len(text):
        char = text[i]
        if char == "\\":
            i += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    return None


def _latex_macro_args(text: str, names: set[str]) -> list[tuple[str, str]]:
    args: list[tuple[str, str]] = []
    for match in re.finditer(r"\\(?P<name>[A-Za-z]+)(?P<star>\*)?\s*\{", text):
        name = match.group("name") + ("*" if match.group("star") else "")
        if name not in names:
            continue
        parsed = _parse_balanced_arg(text, match.end() - 1)
        if parsed is None:
            continue
        args.append((name, parsed[0]))
    return args


def _normalize_dna_text(text: str) -> str:
    text = text.replace("\\_", "_")
    text = re.sub(r"%[^\n]*", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def _normalize_dna_list(items: Iterable[str]) -> str:
    normalized = sorted({
        item
        for item in (_normalize_dna_text(raw) for raw in items)
        if item
    })
    return "\n".join(normalized)


def _chapter_title(text: str) -> str:
    for name, arg in _latex_macro_args(text, {"chapter"}):
        if name == "chapter":
            return _normalize_dna_text(arg)
    return ""


def _chapter_labels(text: str) -> list[str]:
    labels = [
        _normalize_dna_text(match.group(1))
        for match in LABEL_RE.finditer(text)
        if match.group(1).startswith("ch:")
    ]
    return labels[:1]


def _theorem_dna_region(text: str) -> str | None:
    match = CLOSURESTATUS_BEGIN_RE.search(text)
    if match:
        return match.group(1)
    return None


def _statement_locus(text: str) -> str:
    parts: list[str] = []
    title = _chapter_title(text)
    if title:
        parts.append(f"chapter: {title}")
    for label in _chapter_labels(text):
        parts.append(f"label: {label}")
    env_re = re.compile(
        r"(?ms)\\begin\{(?P<kind>" + "|".join(THEOREM_STATUS_ENVS) + r")\}"
        r"(?:\[(?P<title>[^\]]*)\])?"
        r"(?P<body>.*?)"
        r"\\end\{(?P=kind)\}"
    )
    for match in env_re.finditer(text):
        kind = match.group("kind")
        env_title = _normalize_dna_text(match.group("title") or "")
        body = _normalize_dna_text(match.group("body"))
        if env_title:
            parts.append(f"{kind}[{env_title}]: {body}")
        else:
            parts.append(f"{kind}: {body}")
    return "\n".join(part for part in parts if part)


def _proof_locus(text: str) -> str:
    return "\n".join(
        _normalize_dna_text(match.group(0))
        for match in DNA_PROOF_ENV_RE.finditer(text)
        if _normalize_dna_text(match.group(0))
    )


def _closurestatus_body(text: str) -> str:
    match = CLOSURESTATUS_BLOCK_RE.search(text)
    return match.group(0) if match else ""


def _closurestatus_fields_by_name(text: str) -> dict[str, list[str]]:
    names = set(_CLOSURESTATUS_FIELD_NAMES)
    fields: dict[str, list[str]] = {}
    for name, arg in _latex_macro_args(text, names):
        fields.setdefault(name, []).append(arg)
    return fields


def _field_group_locus(fields: dict[str, list[str]], names: set[str]) -> str:
    rows: list[str] = []
    for name in sorted(names):
        for value in fields.get(name, []):
            normalized = _normalize_dna_text(value)
            if normalized:
                rows.append(f"{name}: {normalized}")
    return "\n".join(rows)


def _dependency_locus(text: str) -> str:
    deps: list[str] = []
    for name, arg in _latex_macro_args(text, DNA_MACRO_NAMES):
        if name in {"autoref", "ref", "ref*"}:
            deps.append(f"{name}:{arg}")
        elif name.startswith("lean") or name == "leantarget":
            deps.append(f"{name}:{arg}")
    return _normalize_dna_list(deps)


def _closing_seal_locus(text: str) -> str:
    return "\n".join(
        _normalize_dna_text(match.group(0))
        for match in DNA_CLOSUREAT_RE.finditer(text)
    )


def _theorem_dna_loci(path: Path, text: str) -> dict[str, str]:
    text = DNA_HASH_LINE_RE.sub("", text)
    closure_body = _closurestatus_body(text)
    fields = _closurestatus_fields_by_name(closure_body)
    rel_path = display_path(path)
    chapter_labels = _chapter_labels(text)
    canonical_site = "\n".join([rel_path, *chapter_labels])
    loci = {
        "statement": _statement_locus(text),
        "dependencies": _dependency_locus(text),
        "proof": _proof_locus(text),
        "certificates": _field_group_locus(fields, DNA_CLOSURE_CERTIFICATE_FIELDS),
        "ledger": _field_group_locus(fields, DNA_CLOSURE_LEDGER_FIELDS),
        "status": _field_group_locus(fields, DNA_CLOSURE_STATUS_FIELDS),
        "canonicalSite": _normalize_dna_text(canonical_site),
        "closingSeal": _closing_seal_locus(text),
    }
    return {name: loci[name] for name in DNA_LOCUS_NAMES}


def _theorem_dna_hash(loci: dict[str, str]) -> str:
    payload = {
        "schema": "bedc.theorem-dna",
        "loci": {name: loci.get(name, "") for name in DNA_LOCUS_NAMES},
    }
    encoded = json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return "sha256:" + hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _theorem_dna_locus_hashes(loci: dict[str, str]) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for name in DNA_LOCUS_NAMES:
        payload = {
            "schema": "bedc.theorem-dna.locus",
            "locus": name,
            "text": loci.get(name, ""),
        }
        encoded = json.dumps(payload, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
        hashes[name] = "sha256:" + hashlib.sha256(encoded.encode("utf-8")).hexdigest()
    return hashes


def _parse_theorem_dna_value(value: str | None) -> tuple[str | None, dict[str, str]]:
    if value is None:
        return None, {}
    value = value.strip()
    if re.fullmatch(r"sha256:[0-9a-f]{64}", value):
        return value, {}
    fields: dict[str, str] = {}
    for raw_part in value.split(";"):
        part = raw_part.strip()
        if not part or "=" not in part:
            continue
        key, raw_hash = part.split("=", 1)
        key = key.strip()
        raw_hash = raw_hash.strip()
        if re.fullmatch(r"sha256:[0-9a-f]{64}", raw_hash):
            fields[key] = raw_hash
    aggregate = fields.get("aggregate")
    locus_hashes = {
        name: fields[name]
        for name in DNA_LOCUS_NAMES
        if name in fields
    }
    return aggregate, locus_hashes


def _format_theorem_dna_value(record: TheoremDnaRecord) -> str:
    fields = [f"aggregate={record.computed_hash}"]
    fields.extend(
        f"{name}={record.computed_locus_hashes[name]}"
        for name in DNA_LOCUS_NAMES
    )
    return ";".join(fields)


def _theorem_dna_record(path: Path, text: str | None = None) -> TheoremDnaRecord | None:
    if text is None:
        text = read_text(path)
    if not CONCRETE_CHAPTER_RE.search(text) or is_concrete_instance_hub_only(text):
        return None
    loci = _theorem_dna_loci(path, text)
    stored_match = DNA_HASH_RE.search(text)
    stored_value = stored_match.group("value").strip() if stored_match else None
    stored_hash, stored_locus_hashes = _parse_theorem_dna_value(stored_value)
    return TheoremDnaRecord(
        path=path,
        rel_path=display_path(path),
        region=_theorem_dna_region(text) or "",
        locus_text=loci,
        computed_hash=_theorem_dna_hash(loci),
        computed_locus_hashes=_theorem_dna_locus_hashes(loci),
        stored_hash=stored_hash,
        stored_locus_hashes=stored_locus_hashes,
        stored_value=stored_value,
    )


def collect_theorem_dna_records() -> list[TheoremDnaRecord]:
    instances = PAPER_PARTS_ROOT / "concrete_instances"
    if not instances.is_dir():
        return []
    records: list[TheoremDnaRecord] = []
    for path in sorted(instances.rglob("*.tex")):
        if not path.is_file():
            continue
        record = _theorem_dna_record(path)
        if record is not None:
            records.append(record)
    return records


def _git_merge_base_for_theorem_dna() -> str | None:
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
    return merge_base or None


def _git_text_at(ref: str, rel_path: str) -> str | None:
    try:
        return subprocess.check_output(
            ["git", "show", f"{ref}:{rel_path}"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return None


def _dna_excerpt(text: str, limit: int = 220) -> str:
    text = _normalize_dna_text(text)
    if len(text) <= limit:
        return text
    return text[:limit].rstrip() + "..."


def _dna_changed_excerpts(before: str, after: str, radius: int = 120) -> tuple[str, str]:
    before = _normalize_dna_text(before)
    after = _normalize_dna_text(after)
    if not before:
        return "", _dna_excerpt(after, radius * 2)
    idx = 0
    limit = min(len(before), len(after))
    while idx < limit and before[idx] == after[idx]:
        idx += 1
    start = max(0, idx - radius)
    end_before = min(len(before), idx + radius)
    end_after = min(len(after), idx + radius)

    def window(text: str, end: int) -> str:
        prefix = "..." if start > 0 else ""
        suffix = "..." if end < len(text) else ""
        return prefix + text[start:end].strip() + suffix

    return window(before, end_before), window(after, end_after)


def _theorem_dna_mismatched_loci(
    record: TheoremDnaRecord,
    previous_loci: dict[str, str],
) -> list[dict[str, str]]:
    mismatches: list[dict[str, str]] = []
    stored_has_loci = bool(record.stored_locus_hashes)
    for name in DNA_LOCUS_NAMES:
        expected_hash = record.stored_locus_hashes.get(name)
        actual_hash = record.computed_locus_hashes.get(name)
        if stored_has_loci and expected_hash == actual_hash:
            continue
        if not stored_has_loci and record.stored_hash == record.computed_hash:
            continue

        item = {
            "locus": name,
            "expected_excerpt_or_hash": expected_hash or record.stored_hash or "",
            "actual_excerpt": _dna_excerpt(record.locus_text.get(name, "")),
            "actual_hash": actual_hash or "",
        }
        if previous_loci:
            base_excerpt, actual_excerpt = _dna_changed_excerpts(
                previous_loci.get(name, ""),
                record.locus_text.get(name, ""),
            )
            if base_excerpt:
                item["base_excerpt"] = base_excerpt
            item["actual_excerpt"] = actual_excerpt
        mismatches.append(item)
    return mismatches


def theorem_dna_coverage_payload(
    records: list[TheoremDnaRecord] | None = None,
    include_files: bool = True,
) -> dict[str, object]:
    records = collect_theorem_dna_records() if records is None else records
    covered = [record for record in records if record.covered]
    current = [record for record in covered if record.current]
    payload: dict[str, object] = {
        "chapters_total": len(records),
        "covered_count": len(covered),
        "current_count": len(current),
        "missing_count": len(records) - len(covered),
        "mismatch_count": len(covered) - len(current),
        "coverage_ratio": (len(covered) / len(records)) if records else 0.0,
    }
    if include_files:
        payload.update({
        "covered_files": [record.rel_path for record in covered],
        "missing_files": [record.rel_path for record in records if not record.covered],
        "mismatch_files": [
            {
                "file": record.rel_path,
                "region": record.region,
                "stored_hash": record.stored_hash,
                "computed_hash": record.computed_hash,
                "stale_loci": _theorem_dna_mismatched_loci(record, {}),
            }
            for record in covered
            if not record.current
        ],
        })
    return payload


def theorem_dna_stale_payload(records: list[TheoremDnaRecord] | None = None) -> dict[str, object]:
    records = collect_theorem_dna_records() if records is None else records
    changed = changed_concrete_instance_tex_paths()
    if changed is None:
        changed_records = records
    else:
        changed_records = [record for record in records if record.path.resolve() in changed]
    merge_base = _git_merge_base_for_theorem_dna()
    stale: list[dict[str, object]] = []
    for record in changed_records:
        if not record.covered or record.current:
            continue
        previous_loci: dict[str, str] = {}
        if merge_base:
            old_text = _git_text_at(merge_base, record.rel_path)
            if old_text is not None:
                old_record = _theorem_dna_record(record.path, old_text)
                if old_record is not None:
                    previous_loci = old_record.locus_text
        stale_loci = _theorem_dna_mismatched_loci(record, previous_loci)
        stale.append({
            "file": record.rel_path,
            "region": record.region,
            "stored_hash": record.stored_hash,
            "computed_hash": record.computed_hash,
            "stale_loci": stale_loci,
        })
    return {
        "changed_chapters_count": len(changed_records),
        "stale_count": len(stale),
        "stale": stale,
        "informational": True,
    }


def theorem_dna_payload() -> dict[str, object]:
    records = collect_theorem_dna_records()
    return {
        "coverage": theorem_dna_coverage_payload(records, include_files=True),
        "staleness": theorem_dna_stale_payload(records),
    }


def write_theorem_dna_hash(raw_path: str) -> TheoremDnaRecord:
    path = Path(raw_path)
    if not path.is_absolute():
        path = (REPO_ROOT / path).resolve()
    text = read_text(path)
    record = _theorem_dna_record(path, text)
    if record is None:
        raise ValueError(f"not a concrete-instance content chapter: {raw_path}")
    line = f"  \\dnahash{{{_format_theorem_dna_value(record)}}}\n"
    if DNA_HASH_LINE_RE.search(text):
        updated = DNA_HASH_LINE_RE.sub(lambda _match: line, text, count=1)
    else:
        end_match = CLOSURESTATUS_END_RE.search(text)
        if not end_match:
            raise ValueError(f"missing closurestatus block: {raw_path}")
        updated = text[:end_match.start()] + line + text[end_match.start():]
    path.write_text(updated, encoding="utf-8")
    updated_record = _theorem_dna_record(path)
    if updated_record is None:
        raise ValueError(f"failed to reread theorem DNA record: {raw_path}")
    return updated_record

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
DISCOVERY_CANDIDATE_HARD_REJECT_TAGS = {
    "smoke_template_reuse",
    "trivial_classifier",
    "target_substring_evidence",
    "target_missing",
    "target_axiom",
    "target_sorry",
}
DISCOVERY_CANDIDATE_SUPPORT_TYPES = (
    "ClassifierNonEquivalent",
    "ClassifierDisagreement",
    "DisagreementSupport",
    "StructuralDiscovery",
)
DISCOVERY_MECHANICAL_REASONS = {
    "known_math_namecert",
    "carrier_only",
    "classifier_unchanged",
    "bridge_only",
    "marker_sync_only",
    "human_chapter_reconstruction",
    "insufficient_evidence",
    "duplicate_of_existing",
}
A_LAYER_HARD_REJECT_THEORY_CLOSURES = {"matureClosure"}
A_LAYER_HARD_REJECT_FORMAL_STATUSES = {"auditCleanV", "axiomCleanV", "bridgeCheckedV"}
A_LAYER_HARD_REJECT_BRIDGE_STATUSES = {"bridgeChecked"}
MECHANICAL_INSUFFICIENT_EVIDENCE_TOKENS = (
    "inspected_carrier",
    "inspected_classifier",
    "inspected_parent",
    "inspected_sibling",
    "inspected_evidence",
    "carrier_inspected",
    "classifier_inspected",
    "parent_inspected",
    "sibling_inspected",
    "reject_candidate",
    "explicit_reject",
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
                "scopeclosed": fields.get("scopeclosed", ""),
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


def _ai_origin_blocks(blocks: list[dict]) -> list[dict]:
    return [
        block
        for block in blocks
        if block.get("origin") == "ai" and not block.get("error")
    ]


META_SMOKE_DELTA_LEDGER_NAMES = {
    "BEDC.Meta.DiscoveryDeltaLedger.groundCompilerDeltaLedger",
    "BEDC.Meta.DiscoveryDeltaLedger.smokeShiftDeltaLedger",
}


def _is_meta_smoke_delta_ledger(record: DiscoveryDeltaLedgerRecord) -> bool:
    return record.qualified_name in META_SMOKE_DELTA_LEDGER_NAMES


def discovery_ledger_coverage_payload(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord] | None = None,
    declaration_headers: dict[str, str] | None = None,
) -> dict[str, object]:
    ledgers = collect_discovery_delta_ledgers() if ledgers is None else ledgers
    declaration_headers = (
        collect_declaration_headers() if declaration_headers is None else declaration_headers
    )
    coverage_ledgers = [
        record for record in ledgers if not _is_meta_smoke_delta_ledger(record)
    ]
    excluded_ledgers = [
        record for record in ledgers if _is_meta_smoke_delta_ledger(record)
    ]
    ledgers_by_name = {record.qualified_name: record for record in coverage_ledgers}
    by_key: dict[str, list[DiscoveryDeltaLedgerRecord]] = {}
    for ledger in coverage_ledgers:
        by_key.setdefault(ledger.chapter_key, []).append(ledger)

    chapters: list[dict[str, object]] = []
    covered: list[dict[str, object]] = []
    missing: list[dict[str, object]] = []
    unresolved_targets: list[dict[str, object]] = []
    wrong_type_targets: list[dict[str, object]] = []
    stem_warnings: list[dict[str, object]] = []
    for block in _ai_origin_blocks(blocks):
        region = str(block.get("region") or "")
        key = _region_key(region)
        open_fields = block.get("open_fields") or {}
        explicit_targets: list[str] = []
        for field in ("closureledger", "closuregate"):
            target = _normalize_lean_target(open_fields.get(field))
            if target and target not in explicit_targets:
                explicit_targets.append(target)
        resolved_ledgers: list[DiscoveryDeltaLedgerRecord] = []
        resolved_nonledgers: list[str] = []
        unresolved: list[str] = []
        for target in explicit_targets:
            if target in ledgers_by_name:
                resolved_ledgers.append(ledgers_by_name[target])
                continue
            header = declaration_headers.get(target)
            if header is None:
                unresolved.append(target)
                continue
            if _header_has_discovery_delta_ledger_result(header):
                resolved_ledgers.append(
                    DiscoveryDeltaLedgerRecord(
                        name=target.rsplit(".", 1)[-1],
                        qualified_name=target,
                        file="",
                        line=0,
                        chapter_region=_ledger_name_stem(target.rsplit(".", 1)[-1]),
                        chapter_key=_region_key(_ledger_name_stem(target.rsplit(".", 1)[-1])),
                        has_classifier_shift=False,
                    )
                )
            else:
                resolved_nonledgers.append(target)
        name_matches = by_key.get(key, [])
        item: dict[str, object] = {
            "file": block["file"],
            "line": block["line"],
            "region": f"{region}Up",
            "chapter_key": key,
            "explicit_targets": explicit_targets,
            "ledger_targets": [record.qualified_name for record in resolved_ledgers],
            "name_stem_candidates": [record.qualified_name for record in name_matches],
        }
        chapters.append(item)
        if resolved_ledgers:
            covered.append(item)
            for record in resolved_ledgers:
                if record.chapter_key and record.chapter_key != key:
                    stem_warnings.append({
                        "file": block["file"],
                        "line": block["line"],
                        "region": f"{region}Up",
                        "target": record.qualified_name,
                        "chapter_key": key,
                        "ledger_name_key": record.chapter_key,
                    })
        else:
            missing.append(item)
        for target in unresolved:
            unresolved_targets.append({
                "file": block["file"],
                "line": block["line"],
                "region": f"{region}Up",
                "target": target,
            })
        for target in resolved_nonledgers:
            wrong_type_targets.append({
                "file": block["file"],
                "line": block["line"],
                "region": f"{region}Up",
                "target": target,
            })
        if name_matches and not resolved_ledgers:
            stem_warnings.append({
                "file": block["file"],
                "line": block["line"],
                "region": f"{region}Up",
                "chapter_key": key,
                "name_stem_candidates": [record.qualified_name for record in name_matches],
                "message": "name-stem ledger candidate is not explicit closurestatus evidence",
            })

    return {
        "informational": True,
        "ai_origin_chapter_count": len(chapters),
        "covered_count": len(covered),
        "missing_count": len(missing),
        "ledger_declaration_count": len(coverage_ledgers),
        "excluded_meta_smoke_ledger_count": len(excluded_ledgers),
        "unresolved_target_count": len(unresolved_targets),
        "wrong_type_target_count": len(wrong_type_targets),
        "stem_warning_count": len(stem_warnings),
        "covered": covered,
        "missing": missing,
        "unresolved_targets": unresolved_targets,
        "wrong_type_targets": wrong_type_targets,
        "stem_warnings": stem_warnings,
        "ledger_declarations": [
            {
                "name": record.qualified_name,
                "file": record.file,
                "line": record.line,
                "chapter_region": record.chapter_region,
                "chapter_key": record.chapter_key,
                "has_classifier_shift": record.has_classifier_shift,
            }
            for record in coverage_ledgers
        ],
        "excluded_meta_smoke_ledgers": [
            {
                "name": record.qualified_name,
                "file": record.file,
                "line": record.line,
                "has_classifier_shift": record.has_classifier_shift,
            }
            for record in excluded_ledgers
        ],
    }


def _symbol_kind_map(declarations: list[DeclarationRecord]) -> dict[str, str]:
    return {decl.qualified_name: decl.kind for decl in declarations}


def _positive_discovery_evidence_kind(
    target: str,
    symbol_kinds: dict[str, str],
    declaration_headers: dict[str, str],
) -> str | None:
    if target not in symbol_kinds:
        return None
    header = declaration_headers.get(target, "")
    if _result_type_mentions(DISCOVERY_TASTE_GATE_RESULT_RE, header):
        return "DiscoveryTasteGate"
    # A direct PositiveDiscovery package is accepted as the unwrapped contract
    # beneath DiscoveryTasteGate; wrappers or aliases that hide the result type
    # stay informational until the paper cites an explicit gate/package target.
    if _result_type_mentions(POSITIVE_DISCOVERY_RESULT_RE, header):
        return "PositiveDiscovery"
    return None


def positive_discovery_target_warnings(
    blocks: list[dict],
    declarations: list[DeclarationRecord],
    declaration_headers: dict[str, str] | None = None,
) -> list[dict[str, object]]:
    symbol_kinds = _symbol_kind_map(declarations)
    declaration_headers = (
        collect_declaration_headers() if declaration_headers is None else declaration_headers
    )
    warnings: list[dict[str, object]] = []
    for block in blocks:
        if block.get("error"):
            continue
        open_fields = block.get("open_fields") or {}
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        if claim_kind != "positiveDiscovery":
            continue
        targets: list[str] = []
        gate = str(open_fields.get("closuregate", "")).replace(r"\_", "_").strip()
        lean_target = str(block.get("lean_target") or "").replace(r"\_", "_").strip()
        for raw in (gate, lean_target):
            if raw and raw not in targets:
                targets.append(raw)
        matches = [
            {
                "target": target,
                "evidence_kind": evidence_kind,
            }
            for target in targets
            if (
                evidence_kind := _positive_discovery_evidence_kind(
                    target,
                    symbol_kinds,
                    declaration_headers,
                )
            )
        ]
        if matches:
            continue
        expected = " or ".join(("DiscoveryTasteGate", "PositiveDiscovery"))
        target_text = ", ".join(targets) if targets else "(none)"
        warnings.append(
            _closurestatus_open_message(
                block,
                "\\closureclaimkind{positiveDiscovery} should cite a resolved "
                f"{expected} declaration through \\closuregate or \\leantarget; "
                f"observed {target_text}",
            )
        )
    return warnings


CONSTRUCTOR_SEPARATION_TERMS = (
    "not_hsame_emp_e0",
    "not_hsame_emp_e1",
    "not_hsame_e0_empty",
    "not_hsame_e1_empty",
    "noConfusion",
    "no_confusion",
    "nomatch",
)
TRIVIAL_CLASSIFIER_TERMS = (
    "True.intro",
    "rfl",
    "hsame_refl",
    "trivial",
)
SEMANTIC_SHIFT_TERMS = (
    "SemanticNameCert",
    "NameCertFiveRows",
    "LedgerPolicy",
    "PatternSpec",
    "StabilitySpec",
    "StableSemanticSeparation",
    "observable_namecert",
    "BHistCarrier.toEventFlow",
    "BHistCarrier.fromEventFlow",
    "toEventFlow",
    "fromEventFlow",
    "FieldFaithful",
)
DISCOVERY_SUPPORT_TERMS = (
    "SemanticNameCert",
    "NameCertFiveRows",
    "DiscoveryTasteGate",
    "PositiveDiscovery",
    "FieldFaithful",
    "BHistCarrier",
    "StableSemanticSeparation",
)
SUBSTRING_EVIDENCE_SUPPORT_TERMS = (
    "decode",
    "readback",
    "role",
    "witness",
    "NameCert",
    "ledger",
    "TasteGate",
    "FieldFaithful",
    "carrier",
    "row",
    "scopeSeal",
    "weight",
)
SCOPE_OVERCLAIM_TERMS = (
    "global",
    "all ",
    "all-",
    "every",
    "canonical",
)
WITNESS_ENDPOINT_READ_DEPTH = 5
SUPPORT_OBSERVABLE_READ_DEPTH = 4
SUPPORT_DISAGREEMENT_READ_DEPTH = 8
F1_WRAPPER_TERMS = (
    "readback",
    "Readback",
    "wrapper",
    "alias",
    "Iff",
    "iff",
    "change",
    "exact",
)
F1_NON_WRAPPER_TERMS = (
    "Decode",
    "StableSemanticSeparation",
    "ObservableSupportFamily",
    "FieldFaithful",
    "SemanticNameCert",
)
F4_CONSTRUCTOR_PROOF_TERMS = (
    *CONSTRUCTOR_SEPARATION_TERMS,
)
F5_LEDGER_COST_CLEARANCE = (
    "expose an independent weight profile instead of raw row-count benefit",
    "record bridge rows, debt rows, and a scope seal in the ledger or paper closure site",
)


def _semantic_shift_terms_for_target(target: str) -> tuple[str, ...]:
    terms = list(SEMANTIC_SHIFT_TERMS)
    local_prefix = target.rsplit(".", 1)[-1]
    for suffix in (
        "Rel",
        "Relation",
        "Classifier",
        "Policy",
        "Spec",
        "Source",
        "Pattern",
        "Stability",
    ):
        if local_prefix.endswith(suffix) and len(local_prefix) > len(suffix):
            terms.append(local_prefix)
    return tuple(terms)


def _has_any(text: str, terms: Iterable[str]) -> list[str]:
    return [term for term in terms if term in text]


def _has_any_casefold(text: str, terms: Iterable[str]) -> list[str]:
    lower = text.lower()
    return [term for term in terms if term.lower() in lower]


def _local_declaration_name(target: str) -> str:
    return target.rsplit(".", 1)[-1]


def _decl_text(
    qualified: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> str:
    return f"{declaration_headers.get(qualified, '')}\n{declaration_bodies.get(qualified, '')}"


def _local_to_qualified_index(declaration_headers: dict[str, str]) -> dict[str, list[str]]:
    local_to_qualified: dict[str, list[str]] = {}
    for qualified in declaration_headers:
        local_to_qualified.setdefault(_local_declaration_name(qualified), []).append(qualified)
    return local_to_qualified


def _referenced_qualified_names(
    qualified: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
    local_to_qualified: dict[str, list[str]],
) -> set[str]:
    text = _decl_text(qualified, declaration_headers, declaration_bodies)
    refs: set[str] = set()
    dotted_refs = set(re.findall(r"\b[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+\b", text))
    for dotted in dotted_refs:
        if dotted in declaration_headers and dotted != qualified:
            refs.add(dotted)
    tokens = set(re.findall(r"\b[A-Za-z][A-Za-z0-9_']*\b", text))
    for token in tokens:
        for candidate in local_to_qualified.get(token, []):
            if candidate != qualified:
                refs.add(candidate)
    return refs


def _reachable_declarations(
    seeds: Iterable[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
    *,
    max_depth: int = 6,
) -> set[str]:
    local_to_qualified = _local_to_qualified_index(declaration_headers)
    queue: list[tuple[str, int]] = [
        (seed, 0) for seed in seeds if seed in declaration_headers
    ]
    visited: set[str] = set()
    while queue:
        current, depth = queue.pop(0)
        if current in visited:
            continue
        visited.add(current)
        if depth >= max_depth:
            continue
        for referenced in _referenced_qualified_names(
            current,
            declaration_headers,
            declaration_bodies,
            local_to_qualified,
        ):
            if referenced not in visited:
                queue.append((referenced, depth + 1))
    return visited


def _target_disagreement_anchors(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> set[str]:
    reachable = _reachable_declarations(
        [target],
        declaration_headers,
        declaration_bodies,
        max_depth=SUPPORT_DISAGREEMENT_READ_DEPTH,
    )
    anchors = {target} if target in declaration_headers else set()
    for qualified in reachable:
        header = declaration_headers.get(qualified, "")
        result_type = _declaration_header_result_type(header) or ""
        if _result_type_mentions(CLASSIFIER_DISAGREEMENT_RESULT_RE, header):
            anchors.add(qualified)
            continue
        if re.search(
            r"\b(?:[A-Za-z0-9_'.]+\.)?"
            r"(?:DiscoveryShift|StructuralDiscovery|ClassifierNonEquivalent)\b",
            result_type,
        ):
            anchors.add(qualified)
    return anchors


def _declares_disagreement_support(header: str) -> bool:
    return _result_type_mentions(DISAGREEMENT_SUPPORT_RESULT_RE, header)


def _declaration_mentions_target(
    qualified: str,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    local = _local_declaration_name(target)
    text = _decl_text(qualified, declaration_headers, declaration_bodies)
    if re.search(rf"\b{re.escape(target)}\b", text):
        return True
    if local and re.search(rf"\b{re.escape(local)}\b", text):
        return True
    return False


def _disagreement_assignment_text(body: str) -> str:
    lines = body.splitlines()
    for idx, line in enumerate(lines):
        match = re.match(r"^(?P<indent>\s*)disagreement\s*:=", line)
        if not match:
            continue
        indent = len(match.group("indent").replace("\t", "  "))
        assigned = [line.split(":=", 1)[1].strip()]
        for next_line in lines[idx + 1:]:
            if not next_line.strip():
                continue
            next_indent = len(re.match(r"^\s*", next_line).group(0).replace("\t", "  "))
            if next_indent <= indent and re.match(r"^\s*[A-Za-z][A-Za-z0-9_']*\s*:=", next_line):
                break
            assigned.append(next_line.strip())
        return "\n".join(part for part in assigned if part)
    return ""


def _identifier_tokens(text: str) -> set[str]:
    return set(re.findall(r"\b[A-Za-z][A-Za-z0-9_']*\b", text))


def _find_top_level_assignment(text: str) -> int:
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    for idx, ch in enumerate(text):
        if ch in pairs:
            depth += 1
            continue
        if ch in closing and depth > 0:
            depth -= 1
            continue
        if ch == ":" and idx + 1 < len(text) and text[idx + 1] == "=" and depth == 0:
            return idx
    return -1


def _split_top_level_semicolon(text: str) -> tuple[str, str] | None:
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    for idx, ch in enumerate(text):
        if ch in pairs:
            depth += 1
            continue
        if ch in closing and depth > 0:
            depth -= 1
            continue
        if ch == ";" and depth == 0:
            return text[:idx].strip(), text[idx + 1:].strip()
    return None


def _consume_lean_let_binding(text: str) -> tuple[str, str, str] | None:
    stripped = text.strip()
    match = re.match(r"^let\s+(?P<name>[A-Za-z][A-Za-z0-9_']*)\b", stripped)
    if not match:
        return None
    assign_idx = _find_top_level_assignment(stripped)
    if assign_idx < 0:
        return None
    after_assign = stripped[assign_idx + 2:].strip()
    semicolon_split = _split_top_level_semicolon(after_assign)
    if semicolon_split is not None:
        rhs, rest = semicolon_split
        return match.group("name"), rhs, rest

    lines = [line.strip() for line in after_assign.splitlines() if line.strip()]
    if not lines:
        return None
    rhs = lines[0]
    rest = "\n".join(lines[1:]).strip()
    return match.group("name"), rhs, rest


def _disagreement_effective_return_text(assignment: str) -> tuple[str, set[str]]:
    text = assignment.strip()
    bindings: list[tuple[str, str]] = []
    bound_names: set[str] = set()
    while text:
        consumed = _consume_lean_let_binding(text)
        if consumed is None:
            break
        name, rhs, text = consumed
        bindings.append((name, rhs))
        bound_names.add(name)

    effective_parts = [text] if text else []
    needed = _identifier_tokens(text)
    for name, rhs in reversed(bindings):
        if name not in needed:
            continue
        effective_parts.append(rhs)
        needed.update(_identifier_tokens(rhs))
    return "\n".join(part for part in effective_parts if part), bound_names


def _referenced_qualified_names_in_text(
    text: str,
    declaration_headers: dict[str, str],
    local_to_qualified: dict[str, list[str]],
    shadowed_locals: set[str] | None = None,
) -> set[str]:
    shadowed_locals = set() if shadowed_locals is None else shadowed_locals
    refs: set[str] = set()
    dotted_refs = set(
        re.findall(r"\b[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+\b", text)
    )
    for dotted in dotted_refs:
        if dotted in declaration_headers:
            refs.add(dotted)
    tokens = _identifier_tokens(text) - shadowed_locals
    for token in tokens:
        refs.update(local_to_qualified.get(token, []))
    return refs


def _support_disagreement_read_model(
    support_target: str,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> tuple[set[str], set[str], set[str]]:
    assignment = _disagreement_assignment_text(declaration_bodies.get(support_target, ""))
    if not assignment:
        return set(), set(), set()
    effective_assignment, shadowed_locals = _disagreement_effective_return_text(assignment)
    if not effective_assignment:
        return set(), set(), set()
    local_to_qualified = _local_to_qualified_index(declaration_headers)
    seeds = _referenced_qualified_names_in_text(
        effective_assignment,
        declaration_headers,
        local_to_qualified,
        shadowed_locals,
    )
    anchors = _target_disagreement_anchors(target, declaration_headers, declaration_bodies)
    reachable = _reachable_declarations(
        sorted(seeds),
        declaration_headers,
        declaration_bodies,
        max_depth=SUPPORT_DISAGREEMENT_READ_DEPTH,
    )
    return seeds, anchors, reachable


def _support_disagreement_assignment_reaches_target(
    support_target: str,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    seeds, anchors, reachable = _support_disagreement_read_model(
        support_target,
        target,
        declaration_headers,
        declaration_bodies,
    )
    if not seeds and not anchors and not reachable:
        return False
    if target in seeds or anchors.intersection(seeds):
        return True
    return target in reachable or bool(anchors.intersection(reachable))


def _disagreement_support_declarations(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    local_to_qualified = _local_to_qualified_index(declaration_headers)

    target_local = _local_declaration_name(target)
    direct_support_names = {
        f"{target_local}_support",
        f"{target_local}Support",
        f"{target_local}_disagreementSupport",
        f"{target_local}DisagreementSupport",
    }
    support_targets: set[str] = {
        qualified
        for qualified, header in declaration_headers.items()
        if _declares_disagreement_support(header)
        and (
            _support_disagreement_assignment_reaches_target(
                qualified,
                target,
                declaration_headers,
                declaration_bodies,
            )
            or (
                _local_declaration_name(qualified) in direct_support_names
                and _support_reaches_target(
                    qualified,
                    target,
                    declaration_headers,
                    declaration_bodies,
                )
            )
        )
    }

    queue = [target]
    visited: set[str] = set()
    disagreement_targets: set[str] = set()
    for _ in range(64):
        if not queue:
            break
        current = queue.pop(0)
        if current in visited:
            continue
        visited.add(current)
        header = declaration_headers.get(current, "")
        body = declaration_bodies.get(current, "")
        if _result_type_mentions(CLASSIFIER_DISAGREEMENT_RESULT_RE, header):
            disagreement_targets.add(current)
            continue
        if _declares_disagreement_support(header):
            support_targets.add(current)
        text = f"{header}\n{body}"
        referenced_locals = set(re.findall(r"\b[A-Za-z][A-Za-z0-9_']*\b", text))
        for local in referenced_locals:
            qualified_names = local_to_qualified.get(local, [])
            for qualified in qualified_names:
                if qualified not in visited:
                    queue.append(qualified)

    if disagreement_targets:
        for qualified, header in declaration_headers.items():
            if not _declares_disagreement_support(header):
                continue
            if any(
                _support_disagreement_assignment_reaches_target(
                    qualified,
                    disagreement,
                    declaration_headers,
                    declaration_bodies,
                )
                for disagreement in disagreement_targets
            ):
                    support_targets.add(qualified)

    return sorted(support_targets)


def _support_reaches_target(
    support_target: str,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    return _support_disagreement_assignment_reaches_target(
        support_target,
        target,
        declaration_headers,
        declaration_bodies,
    )


def _support_observable_read_targets(
    support_target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> set[str]:
    return _reachable_declarations(
        [support_target],
        declaration_headers,
        declaration_bodies,
        max_depth=SUPPORT_OBSERVABLE_READ_DEPTH,
    )


def _support_body_mentions_observable_witness(
    support_target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    reachable = _support_observable_read_targets(
        support_target,
        declaration_headers,
        declaration_bodies,
    )
    text = "\n".join(
        _decl_text(qualified, declaration_headers, declaration_bodies)
        for qualified in sorted(reachable)
    )
    has_family_payload = re.search(
        r"\bSupportFamily\.(?:decode|readback|ledger|role)\b",
        text,
    ) is not None
    if not has_family_payload:
        return False
    required_fields = (
        "observable_family_supported",
        "observable_namecert",
        "semantic_separation",
        "family_independent",
    )
    return all(re.search(rf"\b{field}\b", text) for field in required_fields)


def _support_has_independent_observable_witness(
    support_target: str,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    return (
        _declares_disagreement_support(declaration_headers.get(support_target, ""))
        and _support_reaches_target(
            support_target,
            target,
            declaration_headers,
            declaration_bodies,
        )
        and _support_body_mentions_observable_witness(
            support_target,
            declaration_headers,
            declaration_bodies,
        )
    )


def _declaration_reference_index(
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> dict[str, set[str]]:
    local_names = {_local_declaration_name(qualified) for qualified in declaration_headers}
    index: dict[str, set[str]] = {qualified: set() for qualified in declaration_headers}
    for qualified in declaration_headers:
        text = f"{declaration_headers.get(qualified, '')}\n{declaration_bodies.get(qualified, '')}"
        tokens = set(re.findall(r"\b[A-Za-z][A-Za-z0-9_']*\b", text))
        for token in tokens.intersection(local_names):
            index.setdefault(token, set()).add(qualified)
    return index


def _support_targets_by_referenced_local(
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> dict[str, list[str]]:
    references = _declaration_reference_index(declaration_headers, declaration_bodies)
    out: dict[str, list[str]] = {}
    for qualified, header in declaration_headers.items():
        if not _declares_disagreement_support(header):
            continue
        local = _local_declaration_name(qualified)
        candidates = set(references.get(local, set()))
        for referenced in candidates:
            if _support_reaches_target(
                qualified,
                referenced,
                declaration_headers,
                declaration_bodies,
            ):
                out.setdefault(referenced, []).append(qualified)
    return {key: sorted(set(value)) for key, value in out.items()}


def _disagreement_support_text(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> str:
    support_targets = _disagreement_support_declarations(
        target,
        declaration_headers,
        declaration_bodies,
    )
    support = []
    for qualified in support_targets:
        support.append(declaration_headers.get(qualified, ""))
        support.append(declaration_bodies.get(qualified, ""))
    if support:
        return "\n".join(support)

    disagreement_targets: set[str] = set()
    for qualified, header in declaration_headers.items():
        if (
            _result_type_mentions(CLASSIFIER_DISAGREEMENT_RESULT_RE, header)
            and qualified == target
        ):
            disagreement_targets.add(qualified)
    for qualified in sorted(disagreement_targets):
        support.append(declaration_headers.get(qualified, ""))
        support.append(declaration_bodies.get(qualified, ""))
    if not support:
        support.append("\n".join((
            declaration_headers.get(target, ""),
            declaration_bodies.get(target, ""),
        )))
    return "\n".join(support)


def _negative_disagreement_branch_payload(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> tuple[str, list[str]]:
    anchors = _target_disagreement_anchors(
        target,
        declaration_headers,
        declaration_bodies,
    )
    reachable = _reachable_declarations(
        anchors,
        declaration_headers,
        declaration_bodies,
        max_depth=5,
    )
    negative_parts: list[str] = []
    read_targets: set[str] = set(anchors)
    local_to_qualified = _local_to_qualified_index(declaration_headers)
    for qualified in sorted(anchors | reachable):
        header = declaration_headers.get(qualified, "")
        if not _result_type_mentions(CLASSIFIER_DISAGREEMENT_RESULT_RE, header):
            continue
        branch_text = _lean_field_assignment(
            declaration_bodies.get(qualified, ""),
            "negative",
        )
        if not branch_text:
            continue
        negative_parts.append(branch_text)
        read_targets.add(qualified)
        read_targets.update(_referenced_qualified_names_in_text(
            branch_text,
            declaration_headers,
            local_to_qualified,
        ))
    return "\n".join(negative_parts), sorted(read_targets)


def _support_target_names(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    return _disagreement_support_declarations(
        target,
        declaration_headers,
        declaration_bodies,
    )


def _has_independent_disagreement_support(
    support_targets: list[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
    target: str,
) -> bool:
    return any(
        _support_has_independent_observable_witness(
            support_target,
            target,
            declaration_headers,
            declaration_bodies,
        )
        for support_target in support_targets
    )


def _support_result_types(
    support_targets: list[str],
    declaration_headers: dict[str, str],
) -> dict[str, str]:
    out: dict[str, str] = {}
    for support_target in support_targets:
        result_type = _declaration_header_result_type(
            declaration_headers.get(support_target, ""),
        )
        if result_type:
            out[support_target] = result_type
    return out


def _is_container_result_type(result_type: str, target: str) -> bool:
    local = _local_declaration_name(target)
    words = result_type.strip()
    stripped = re.sub(r"\s+", "", result_type)
    if re.match(r"^(?:[A-Za-z0-9_'.]+\.)?DiscoveryDeltaLedger(?:\b|\s|\[|\().*", words):
        return True
    if re.match(r"^(?:[A-Za-z0-9_'.]+\.)?DisagreementSupport(?:\b|\s|\[|\().*", words):
        return True
    if local and re.match(
        rf"^(?:[A-Za-z0-9_'.]+\.)?{re.escape(local)}(?:\b|\s|\[|\().*",
        words,
    ):
        return True
    if re.fullmatch(r"(?:[A-Za-z0-9_'.]+\.)?DiscoveryDeltaLedger(?:\[[^\]]+\])?.*", stripped):
        return True
    if re.fullmatch(r"(?:[A-Za-z0-9_'.]+\.)?DisagreementSupport(?:\b|\[|\().*", stripped):
        return True
    if local and re.fullmatch(rf"(?:[A-Za-z0-9_'.]+\.)?{re.escape(local)}(?:\b|\[|\().*", stripped):
        return True
    return False


def _endpoint_evidence_terms(text: str) -> list[str]:
    patterns = {
        "decode": r"\b(?:Decode|decode|decoded)\b",
        "readback": r"\b(?:Readback|readback)\b",
        "role": r"\b(?:Role|role)\b",
        "ledger_row": r"\b(?:LedgerRow|ledger_row|ledgerRow|row_witness|rowWitness)\b",
        "event_flow": r"\b(?:BHistCarrier\.(?:toEventFlow|fromEventFlow)|toEventFlow|fromEventFlow)\b",
        "namecert": r"\b(?:SemanticNameCert|NameCertFiveRows|NameCert)\b",
        "ledger_policy": r"\bLedgerPolicy\b",
        "pattern_spec": r"\bPatternSpec\b",
        "stability_spec": r"\bStabilitySpec\b",
        "field_faithful": r"\bFieldFaithful\b",
    }
    return [name for name, pattern in patterns.items() if re.search(pattern, text)]


def _is_public_semantic_endpoint(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    header = declaration_headers.get(target, "")
    result_type = _declaration_header_result_type(header) or ""
    if not result_type or _is_container_result_type(result_type, target):
        return False
    return _endpoint_evidence_terms(result_type) != []


def _reachable_endpoint_targets(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> set[str]:
    return _reachable_declarations(
        [target],
        declaration_headers,
        declaration_bodies,
        max_depth=WITNESS_ENDPOINT_READ_DEPTH,
    )


def _reachable_endpoint_evidence_terms(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    terms: list[str] = []
    reachable = _reachable_endpoint_targets(
        target,
        declaration_headers,
        declaration_bodies,
    )
    for qualified in sorted(reachable):
        if qualified == target:
            continue
        result_type = _declaration_header_result_type(
            declaration_headers.get(qualified, ""),
        ) or ""
        if _is_container_result_type(result_type, target):
            continue
        terms.extend(_endpoint_evidence_terms(result_type))
        terms.extend(_endpoint_evidence_terms(declaration_bodies.get(qualified, "")))
    return sorted(set(terms))


def _support_semantic_evidence_terms(
    support_targets: list[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    terms: list[str] = []
    for support_target in support_targets:
        terms.extend(_endpoint_evidence_terms(_decl_text(
            support_target,
            declaration_headers,
            declaration_bodies,
        )))
        if _support_body_mentions_observable_witness(
            support_target,
            declaration_headers,
            declaration_bodies,
        ):
            terms.append("observable_family_witness")
    return sorted(set(terms))


def _classifier_shift_target_names(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord],
    declaration_headers: dict[str, str],
) -> list[dict[str, object]]:
    targets: list[dict[str, object]] = []
    seen: set[str] = set()
    for ledger in ledgers:
        if ledger.has_classifier_shift and ledger.qualified_name not in seen:
            seen.add(ledger.qualified_name)
            targets.append({
                "target": ledger.qualified_name,
                "source": "classifier_shift",
                "file": ledger.file,
                "line": ledger.line,
            })
    for block in blocks:
        if block.get("error"):
            continue
        open_fields = block.get("open_fields") or {}
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        gate = _normalize_lean_target(open_fields.get("closuregate"))
        lean_target = _normalize_lean_target(block.get("lean_target"))
        for target in (gate, lean_target):
            if not target or target in seen or target not in declaration_headers:
                continue
            evidence = _positive_discovery_evidence_kind(
                target,
                {target: ""},
                declaration_headers,
            )
            if claim_kind == "positiveDiscovery" or evidence in (
                "DiscoveryTasteGate",
                "PositiveDiscovery",
            ):
                seen.add(target)
                targets.append({
                    "target": target,
                    "source": "positiveDiscovery",
                    "file": block["file"],
                    "line": block["line"],
                })
    return targets


def _make_sieve_witness(
    reason_tag: str,
    severity: str,
    evidence: object,
    deterministic: bool,
) -> dict[str, object]:
    return {
        "reason_tag": reason_tag,
        "severity": severity,
        "evidence": evidence,
        "deterministic": deterministic,
    }


def _parse_nat_assignment(text: str, name: str) -> int | None:
    match = re.search(rf"\b{name}\s*:=\s*(?P<rhs>[^\n,}}]+)", text)
    if not match:
        return None
    rhs = match.group("rhs").strip()
    return int(rhs) if re.fullmatch(r"[0-9]+", rhs) else None


def _target_word_hits(target: str, evidence_text: str) -> list[str]:
    local = _local_declaration_name(target)
    pieces = [
        part.lower()
        for part in re.split(r"[_\W]+", _camel_to_snake(local))
        if len(part) >= 4
    ]
    lower = evidence_text.lower()
    hits = [piece for piece in pieces if piece in lower]
    if local and local in evidence_text:
        hits.append(local)
    return sorted(set(hits))


def _structured_scope_seal_fields(open_fields: dict[str, object]) -> list[str]:
    return [
        field
        for field in ("closureweightprofile", "closuregate")
        if str(open_fields.get(field, "")).strip()
    ]


def _has_structured_scope_seal(open_fields: dict[str, object]) -> bool:
    return bool(_structured_scope_seal_fields(open_fields))


def _body_mentions_sorry(text: str) -> bool:
    return re.search(r"\bsorry\b", text) is not None


def _body_mentions_axiom(text: str) -> bool:
    return re.search(r"(?m)^\s*axiom\s+", text) is not None


def _json_sha256(payload: object) -> str:
    encoded = json.dumps(
        payload,
        sort_keys=True,
        ensure_ascii=False,
        separators=(",", ":"),
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _text_snippet(text: str, needle: str = "", limit: int = 240) -> str:
    compact = re.sub(r"\s+", " ", text).strip()
    if not compact:
        return ""
    if needle and needle in compact:
        start = max(0, compact.index(needle) - limit // 3)
    else:
        start = 0
    return compact[start:start + limit]


def _witness_read_graph_targets(
    target: str,
    support_targets: list[str],
    adversarial_input_targets: list[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    refs: set[str] = set([target])
    refs.update(support_targets)
    refs.update(adversarial_input_targets)
    refs.update(_reachable_endpoint_targets(
        target,
        declaration_headers,
        declaration_bodies,
    ))
    for support_target in support_targets:
        refs.update(_support_observable_read_targets(
            support_target,
            declaration_headers,
            declaration_bodies,
        ))
        seeds, anchors, reachable = _support_disagreement_read_model(
            support_target,
            target,
            declaration_headers,
            declaration_bodies,
        )
        refs.update(seeds)
        refs.update(anchors)
        refs.update(reachable)
    return sorted(ref for ref in refs if ref in declaration_headers)


def _target_fingerprint(
    target: str,
    support_targets: list[str],
    adversarial_input_targets: list[str],
    block: dict | None,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> str:
    fingerprint_targets = _witness_read_graph_targets(
        target,
        support_targets,
        adversarial_input_targets,
        declaration_headers,
        declaration_bodies,
    )
    support_payload = [
        {
            "target": support_target,
            "header": declaration_headers.get(support_target, ""),
            "body": declaration_bodies.get(support_target, ""),
        }
        for support_target in sorted(set(support_targets))
    ]
    adversarial_input_payload = [
        {
            "target": input_target,
            "header": declaration_headers.get(input_target, ""),
            "body": declaration_bodies.get(input_target, ""),
        }
        for input_target in sorted(set(adversarial_input_targets))
    ]
    witness_graph_payload = [
        {
            "target": input_target,
            "header": declaration_headers.get(input_target, ""),
            "body": declaration_bodies.get(input_target, ""),
        }
        for input_target in fingerprint_targets
    ]
    paper_payload = {}
    if block is not None:
        paper_payload = {
            "file": block.get("file", ""),
            "line": block.get("line", 0),
            "closurestatus": block.get("raw_body", ""),
            "scopeclosed": block.get("scopeclosed", ""),
            "open_fields": block.get("open_fields", {}),
        }
    return _json_sha256({
        "schema": "bedc.adversarial-witness.fingerprint",
        "target": target,
        "target_header": declaration_headers.get(target, ""),
        "target_body": declaration_bodies.get(target, ""),
        "support": support_payload,
        "adversarial_input_graph": adversarial_input_payload,
        "witness_read_graph": witness_graph_payload,
        "paper": paper_payload,
    })


def _lean_field_assignment(body: str, field: str) -> str:
    lines = body.splitlines()
    for idx, line in enumerate(lines):
        match = re.match(rf"^(?P<indent>\s*){re.escape(field)}\s*:=", line)
        if not match:
            continue
        indent = len(match.group("indent").replace("\t", "  "))
        assigned = [line.split(":=", 1)[1].strip()]
        for next_line in lines[idx + 1:]:
            if not next_line.strip():
                continue
            next_indent = len(re.match(r"^\s*", next_line).group(0).replace("\t", "  "))
            if (
                next_indent <= indent
                and re.match(r"^\s*[A-Za-z][A-Za-z0-9_']*\s*:=", next_line)
            ):
                break
            assigned.append(next_line.strip())
        return "\n".join(part for part in assigned if part)
    return ""


def _resolve_decl_refs_from_text(
    text: str,
    declaration_headers: dict[str, str],
) -> list[str]:
    local_to_qualified = _local_to_qualified_index(declaration_headers)
    refs: set[str] = set()
    dotted_refs = set(
        re.findall(r"\b[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+\b", text)
    )
    refs.update(ref for ref in dotted_refs if ref in declaration_headers)
    for token in _identifier_tokens(text):
        refs.update(local_to_qualified.get(token, []))
    return sorted(refs)


def _classifier_shift_read_targets(
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[str]:
    body = declaration_bodies.get(target, "")
    shift_text = _lean_field_assignment(body, "classifier_shift")
    if not shift_text:
        return []
    refs: set[str] = set(_resolve_decl_refs_from_text(shift_text, declaration_headers))
    for shift_ref in list(refs):
        shift_body = declaration_bodies.get(shift_ref, "")
        if not shift_body:
            continue
        refs.update(_resolve_decl_refs_from_text(shift_body, declaration_headers))
        before_text = _lean_field_assignment(shift_body, "BeforeClassifier")
        after_text = _lean_field_assignment(shift_body, "AfterClassifier")
        refs.update(_resolve_decl_refs_from_text(before_text, declaration_headers))
        refs.update(_resolve_decl_refs_from_text(after_text, declaration_headers))
    reachable = _reachable_declarations(
        refs,
        declaration_headers,
        declaration_bodies,
        max_depth=WITNESS_ENDPOINT_READ_DEPTH,
    )
    refs.update(reachable)
    return sorted(ref for ref in refs if ref in declaration_headers)


def _lean_refs_payload(refs: Iterable[str]) -> list[dict[str, str]]:
    return [{"name": ref} for ref in sorted(set(refs)) if ref]


def _paper_refs_payload(block: dict | None) -> list[dict[str, object]]:
    if block is None:
        return []
    return [{
        "file": block.get("file", ""),
        "line": block.get("line", 0),
        "region": f"{block.get('region', '')}Up",
    }]


def _classifier_body_signature(text: str, local_name: str) -> str:
    body = re.sub(r"--[^\n]*", " ", text)
    body = re.sub(r"/-.*?-/", " ", body, flags=re.DOTALL)
    body = re.sub(rf"\b{re.escape(local_name)}\b", "CLASSIFIER", body)
    body = re.sub(r"\b(?:h|k|left|right|_h|_k|a|b)\b", "ARG", body)
    return re.sub(r"\s+", " ", body).strip()


def _f1_classifier_has_independent_endpoint(
    target: str,
    shift_ref: str,
    after_ref: str,
    support_targets: list[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    shift_body = declaration_bodies.get(shift_ref, "")
    after_text = "\n".join((
        _lean_field_assignment(shift_body, "AfterClassifier"),
        _decl_text(after_ref, declaration_headers, declaration_bodies),
    ))
    shift_reachable = _reachable_declarations(
        [shift_ref, after_ref],
        declaration_headers,
        declaration_bodies,
        max_depth=5,
    )
    shift_endpoint_hits: list[str] = []
    for reachable in sorted(shift_reachable):
        if reachable == after_ref:
            continue
        result_type = _declaration_header_result_type(
            declaration_headers.get(reachable, ""),
        ) or ""
        shift_endpoint_hits.extend(_endpoint_evidence_terms(result_type))
        shift_endpoint_hits.extend(_endpoint_evidence_terms(
            declaration_bodies.get(reachable, ""),
        ))
    after_names_independent_endpoint = bool(
        re.search(r"\bIndependentEndpoint\b", after_text)
        and _endpoint_evidence_terms(after_text)
    )
    support_has_independent_endpoint = _has_independent_disagreement_support(
        support_targets,
        declaration_headers,
        declaration_bodies,
        target,
    )
    return (
        after_names_independent_endpoint
        or bool(shift_endpoint_hits)
        or support_has_independent_endpoint
    )


def _f1_static_witness(
    target: str,
    fingerprint: str,
    block: dict | None,
    support_targets: list[str],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> AdversarialWitness | None:
    body = declaration_bodies.get(target, "")
    shift_text = _lean_field_assignment(body, "classifier_shift")
    if "some" not in shift_text:
        return None
    shift_refs = [
        ref for ref in _resolve_decl_refs_from_text(shift_text, declaration_headers)
        if ref in declaration_bodies
    ]
    for shift_ref in shift_refs:
        shift_body = declaration_bodies.get(shift_ref, "")
        before_text = _lean_field_assignment(shift_body, "BeforeClassifier")
        after_text = _lean_field_assignment(shift_body, "AfterClassifier")
        before_refs = [
            ref for ref in _resolve_decl_refs_from_text(before_text, declaration_headers)
            if _local_declaration_name(ref).endswith("Classifier")
        ]
        after_refs = [
            ref for ref in _resolve_decl_refs_from_text(after_text, declaration_headers)
            if _local_declaration_name(ref).endswith("Classifier")
        ]
        if not after_refs:
            continue
        prior_refs = before_refs or [
            ref for ref in _resolve_decl_refs_from_text(shift_body, declaration_headers)
            if _local_declaration_name(ref).endswith("Classifier")
            and ref not in after_refs
        ]
        for after_ref in after_refs:
            after_decl_text = _decl_text(after_ref, declaration_headers, declaration_bodies)
            after_local = _local_declaration_name(after_ref)
            for prior_ref in prior_refs:
                if prior_ref == after_ref:
                    continue
                prior_decl_text = _decl_text(prior_ref, declaration_headers, declaration_bodies)
                prior_local = _local_declaration_name(prior_ref)
                after_signature = _classifier_body_signature(after_decl_text, after_local)
                prior_signature = _classifier_body_signature(prior_decl_text, prior_local)
                direct_wrapper = (
                    re.search(rf"\b{re.escape(prior_local)}\b", after_decl_text) is not None
                    and not _has_any(after_decl_text, F1_NON_WRAPPER_TERMS)
                )
                same_shape = (
                    after_signature == prior_signature
                    and after_signature
                    and after_signature != "CLASSIFIER"
                )
                wrapper_terms = _has_any(after_decl_text, F1_WRAPPER_TERMS)
                if same_shape and not (direct_wrapper or wrapper_terms):
                    return AdversarialWitness(
                        target=target,
                        target_fingerprint=fingerprint,
                        family="F1-static",
                        strength="heuristic",
                        lens="prior-classifier-shape-ambiguity",
                        verdict="inconclusive-by-F1",
                        evidence={
                            "lean_refs": _lean_refs_payload([shift_ref, prior_ref, after_ref]),
                            "paper_refs": _paper_refs_payload(block),
                            "prior_classifier": prior_ref,
                            "after_classifier": after_ref,
                            "reduction": "AfterClassifier has the same normalized text shape as a prior classifier; this is not enough to mark a wrapper without alias evidence.",
                            "body_fragment": _text_snippet(after_decl_text, prior_local),
                        },
                        clearance=[
                            "inspect whether the same-shape classifier is a deliberate independent endpoint or a pure alias",
                        ],
                    )
                if not (direct_wrapper or wrapper_terms and direct_wrapper):
                    continue
                if _f1_classifier_has_independent_endpoint(
                    target,
                    shift_ref,
                    after_ref,
                    support_targets,
                    declaration_headers,
                    declaration_bodies,
                ):
                    continue
                return AdversarialWitness(
                    target=target,
                    target_fingerprint=fingerprint,
                    family="F1-static",
                    strength="deterministic",
                    lens="prior-classifier-wrapper-detection",
                    verdict="suspected-composite-by-F1",
                    evidence={
                        "lean_refs": _lean_refs_payload([shift_ref, prior_ref, after_ref]),
                        "paper_refs": _paper_refs_payload(block),
                        "prior_classifier": prior_ref,
                        "after_classifier": after_ref,
                        "reduction": "AfterClassifier has wrapper, alias, or same-shape body evidence against a prior classifier.",
                        "body_fragment": _text_snippet(after_decl_text, prior_local),
                    },
                    clearance=[
                        "show an after-classifier observable that is not a wrapper, argument permutation, alias, or readback of the prior classifier",
                    ],
                )
    return None


def _f4_static_witness(
    target: str,
    fingerprint: str,
    block: dict | None,
    support_targets: list[str],
    negative_witnesses: list[dict[str, object]],
    negative_branch_text: str,
) -> AdversarialWitness | None:
    constructor_terms = _has_any(negative_branch_text, F4_CONSTRUCTOR_PROOF_TERMS)
    has_constructor_sieve = any(
        witness.get("reason_tag") == "constructor_only_disagreement"
        for witness in negative_witnesses
    )
    if not constructor_terms and not has_constructor_sieve:
        return None
    evidence_refs = support_targets + [
        str(ref)
        for ref in re.findall(
            r"\b[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)+\b",
            negative_branch_text,
        )
    ]
    return AdversarialWitness(
        target=target,
        target_fingerprint=fingerprint,
        family="F4-static",
        strength="deterministic",
        lens="constructor-normal-form-deepening",
        verdict="suspected-composite-by-F4",
        evidence={
            "lean_refs": _lean_refs_payload(evidence_refs),
            "paper_refs": _paper_refs_payload(block),
            "constructor_terms": constructor_terms,
            "reduction": "The negative branch reduces to BHist constructor separation rather than an independent classifier endpoint.",
            "body_fragment": _text_snippet(negative_branch_text, constructor_terms[0] if constructor_terms else ""),
        },
        clearance=[
            "replace constructor disequality with an observable endpoint separation that changes the classifier beyond BHist constructor normal form",
        ],
    )


def _f5_static_witness(
    target: str,
    fingerprint: str,
    block: dict | None,
    ledger_by_name: dict[str, DiscoveryDeltaLedgerRecord],
    body: str,
    has_independent_endpoint: bool,
) -> AdversarialWitness | None:
    if target not in ledger_by_name:
        return None
    introduced = _parse_nat_assignment(body, "introduced_rows")
    refusal = _parse_nat_assignment(body, "refusal_rows")
    bridge = _parse_nat_assignment(body, "bridge_rows")
    debt = _parse_nat_assignment(body, "not_claimed_rows")
    if None in (introduced, refusal, bridge, debt):
        return None
    scope_seal = 1 if re.search(r"\bclassifier_shift\s*:=\s*some\b", body) else 0
    benefit = introduced + refusal
    paper_text = ""
    has_weight_profile = False
    has_paper_scope_seal = False
    structured_scope_seal_fields: list[str] = []
    if block is not None:
        open_fields = block.get("open_fields") or {}
        paper_text = "\n".join((
            str(block.get("raw_body", "")),
            str(block.get("scopeclosed", "")),
            str(open_fields.get("closureweightprofile", "")),
        ))
        has_weight_profile = bool(str(open_fields.get("closureweightprofile", "")).strip())
        structured_scope_seal_fields = _structured_scope_seal_fields(open_fields)
        has_paper_scope_seal = bool(structured_scope_seal_fields)
    row_count_only = benefit >= 3 and bridge == 0 and debt == 0
    unanchored_benefit = (
        row_count_only
        and not has_weight_profile
        and not has_paper_scope_seal
        and not has_independent_endpoint
    )
    if not unanchored_benefit:
        return None
    ledger = ledger_by_name[target]
    return AdversarialWitness(
        target=target,
        target_fingerprint=fingerprint,
        family="F5-static",
        strength="deterministic",
        lens="cost-ledger-reduction",
        verdict="suspected-composite-by-F5",
        evidence={
            "lean_refs": _lean_refs_payload([target]),
            "paper_refs": _paper_refs_payload(block),
            "introduced_rows": introduced,
            "refusal_rows": refusal,
            "bridge_rows": bridge,
            "not_claimed_rows": debt,
            "scopeSeal": scope_seal,
            "benefit": benefit,
            "cost_plus_debt_plus_scopeSeal": bridge + debt + scope_seal,
            "has_weight_profile": has_weight_profile,
            "paper_scope_seal_present": has_paper_scope_seal,
            "structured_scope_seal_fields": structured_scope_seal_fields,
            "has_independent_endpoint": has_independent_endpoint,
            "reduction": "Benefit is a bare row-count margin without weight profile, paper scope-seal evidence, or reachable independent semantic endpoint.",
            "ledger_site": {"file": ledger.file, "line": ledger.line},
            "paper_fragment": _text_snippet(paper_text),
        },
        clearance=list(F5_LEDGER_COST_CLEARANCE),
    )


def _adversarial_resistance_score(witnesses: list[AdversarialWitness]) -> int:
    deterministic_weight = 1
    suspected_count = sum(
        1 for witness in witnesses if witness.verdict.startswith("suspected-composite")
    )
    penalty = deterministic_weight * 25 * suspected_count
    return max(0, 100 - penalty)


def _recomputed_witness_snapshot_payload(
    fingerprint: str,
    witnesses: list[AdversarialWitness],
) -> dict[str, object]:
    return {
        "snapshot_semantics": "recomputed_read_model_fingerprint_gated",
        "target_fingerprint": fingerprint,
        "verdicts": [
            {
                "family": witness.family,
                "lens": witness.lens,
                "verdict": witness.verdict,
                "strength": witness.strength,
            }
            for witness in witnesses
        ],
    }


def _adversarial_witnesses_for_target(
    target: str,
    fingerprint: str,
    block: dict | None,
    support_targets: list[str],
    negative_witnesses: list[dict[str, object]],
    negative_branch_text: str,
    ledger_by_name: dict[str, DiscoveryDeltaLedgerRecord],
    has_independent_endpoint: bool,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[AdversarialWitness]:
    witnesses: list[AdversarialWitness] = []
    for maybe_witness in (
        _f1_static_witness(
            target,
            fingerprint,
            block,
            support_targets,
            declaration_headers,
            declaration_bodies,
        ),
        _f4_static_witness(
            target,
            fingerprint,
            block,
            support_targets,
            negative_witnesses,
            negative_branch_text,
        ),
        _f5_static_witness(
            target,
            fingerprint,
            block,
            ledger_by_name,
            declaration_bodies.get(target, ""),
            has_independent_endpoint,
        ),
    ):
        if maybe_witness is not None:
            witnesses.append(maybe_witness)
    return witnesses


def _discovery_sieve_sites(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord],
    declaration_headers: dict[str, str],
) -> list[dict[str, object]]:
    sites: dict[str, dict[str, object]] = {}

    def ensure_site(target: str, source: str, file: str, line: int, block: dict | None = None) -> None:
        if not target:
            return
        site = sites.setdefault(target, {
            "target": target,
            "sources": [],
            "file": file,
            "line": line,
            "blocks": [],
        })
        if source not in site["sources"]:
            site["sources"].append(source)
        if block is not None:
            site["blocks"].append(block)

    ledger_by_name = {ledger.qualified_name: ledger for ledger in ledgers}
    for ledger in ledgers:
        if ledger.has_classifier_shift:
            ensure_site(
                ledger.qualified_name,
                "classifier_shift",
                ledger.file,
                ledger.line,
            )

    for block in blocks:
        if block.get("error"):
            continue
        open_fields = block.get("open_fields") or {}
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        gate = _normalize_lean_target(open_fields.get("closuregate"))
        lean_target = _normalize_lean_target(block.get("lean_target"))
        ledger_target = _normalize_lean_target(open_fields.get("closureledger"))
        block_targets = [target for target in (gate, lean_target, ledger_target) if target]
        has_discovery_gate = any(
            target in declaration_headers
            and _positive_discovery_evidence_kind(target, {target: ""}, declaration_headers)
            in ("DiscoveryTasteGate", "PositiveDiscovery")
            for target in block_targets
        )
        if claim_kind not in STRONG_CLOSURESTATUS_CLAIMS and not has_discovery_gate:
            continue
        if not block_targets:
            block_targets = [f"{block.get('region')}Up"]
        for target in block_targets:
            source = "positiveDiscovery" if claim_kind == "positiveDiscovery" else "discovery_claim"
            if target in ledger_by_name and ledger_by_name[target].has_classifier_shift:
                source = "classifier_shift"
            ensure_site(target, source, block["file"], block["line"], block)

    for target, header in declaration_headers.items():
        if _result_type_mentions(DISCOVERY_TASTE_GATE_RESULT_RE, header):
            ensure_site(target, "DiscoveryTasteGate", "", 0)

    return sorted(sites.values(), key=lambda site: (str(site["target"]), str(site["file"])))


def discovery_sieve_payload(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> dict[str, object]:
    sites = _discovery_sieve_sites(blocks, ledgers, declaration_headers)
    ledger_by_name = {ledger.qualified_name: ledger for ledger in ledgers}
    support_by_local = _support_targets_by_referenced_local(
        declaration_headers,
        declaration_bodies,
    )
    profiles: list[dict[str, object]] = []
    grade_counts: Counter[str] = Counter()
    adversarial_verdict_counts: Counter[str] = Counter()

    for site in sites:
        target = str(site["target"])
        blocks_for_target = [
            block for block in site.get("blocks", []) if isinstance(block, dict)
        ]
        block = blocks_for_target[0] if blocks_for_target else None
        open_fields = block.get("open_fields") if block else {}
        open_fields = open_fields if isinstance(open_fields, dict) else {}
        region = f"{block['region']}Up" if block else (
            f"{ledger_by_name[target].chapter_region}Up" if target in ledger_by_name
            else target.rsplit(".", 1)[-1]
        )
        header = declaration_headers.get(target, "")
        body = declaration_bodies.get(target, "")
        target_text = f"{header}\n{body}"
        support_targets = sorted(set(
            (
                support_by_local.get(_local_declaration_name(target), [])
                if target in declaration_headers else []
            )
            + (
                _disagreement_support_declarations(
                    target,
                    declaration_headers,
                    declaration_bodies,
                )
                if target in declaration_headers else []
            )
        ))
        support_text = "\n".join(
            f"{declaration_headers.get(support_target, '')}\n"
            f"{declaration_bodies.get(support_target, '')}"
            for support_target in support_targets
        )
        combined_text = f"{target_text}\n{support_text}"
        support_result_types = _support_result_types(support_targets, declaration_headers)
        has_independent_support = _has_independent_disagreement_support(
            support_targets,
            declaration_headers,
            declaration_bodies,
            target,
        )
        target_result_type = _declaration_header_result_type(header) or ""
        reachable_endpoint_hits = _reachable_endpoint_evidence_terms(
            target,
            declaration_headers,
            declaration_bodies,
        )
        target_semantic_hits = (
            _has_any(target_result_type, _semantic_shift_terms_for_target(target))
            if not _is_container_result_type(target_result_type, target) else []
        )
        support_semantic_hits = _support_semantic_evidence_terms(
            support_targets,
            declaration_headers,
            declaration_bodies,
        )
        semantic_hits = sorted(
            set(target_semantic_hits + support_semantic_hits + reachable_endpoint_hits)
        )
        support_hits = sorted(
            set(
                (
                    _has_any(target_result_type, DISCOVERY_SUPPORT_TERMS)
                    if not _is_container_result_type(target_result_type, target) else []
                )
                + _has_any("\n".join(support_result_types.values()), DISCOVERY_SUPPORT_TERMS)
            )
        )
        public_semantic_endpoint = _is_public_semantic_endpoint(
            target,
            declaration_headers,
            declaration_bodies,
        )
        evidence_text = "\n".join([
            str(open_fields.get(name, ""))
            for name in CLOSURESTATUS_OPEN_FIELDS
            if str(open_fields.get(name, "")).strip()
        ])

        negative_witnesses: list[dict[str, object]] = []
        missing_support: list[str] = []
        clearance_requirements: list[str] = []

        if target not in declaration_headers:
            negative_witnesses.append(_make_sieve_witness(
                "target_missing",
                "confirmed",
                {"target": target},
                True,
            ))
        elif _body_mentions_axiom(target_text):
            negative_witnesses.append(_make_sieve_witness(
                "target_axiom",
                "confirmed",
                {"target": target},
                True,
            ))
        elif _body_mentions_sorry(target_text):
            negative_witnesses.append(_make_sieve_witness(
                "target_sorry",
                "confirmed",
                {"target": target},
                True,
            ))

        disagreement_text = "\n".join(
            _decl_text(
                qualified,
                declaration_headers,
                declaration_bodies,
            )
            for qualified in _target_disagreement_anchors(
                target,
                declaration_headers,
                declaration_bodies,
            )
        )
        negative_branch_text, negative_branch_read_targets = _negative_disagreement_branch_payload(
            target,
            declaration_headers,
            declaration_bodies,
        )
        constructor_hits = _has_any(
            negative_branch_text,
            CONSTRUCTOR_SEPARATION_TERMS,
        )
        trivial_hits = _has_any(support_text, TRIVIAL_CLASSIFIER_TERMS)

        if constructor_hits:
            negative_witnesses.append(_make_sieve_witness(
                "constructor_only_disagreement",
                "suspicious",
                {
                    "constructor_hits": constructor_hits,
                    "support_targets": support_targets,
                    "independent_support": has_independent_support,
                    "public_semantic_endpoint": public_semantic_endpoint,
                },
                False,
            ))
            clearance_requirements.append(
                "replace constructor separation with an observable separation not reducible to BHist constructor inequality"
            )
        if trivial_hits:
            negative_witnesses.append(_make_sieve_witness(
                "trivial_classifier",
                "suspicious",
                {"trivial_hits": trivial_hits},
                False,
            ))
            clearance_requirements.append(
                "replace constant or hsame-only classifier evidence with a nontrivial classifier shift"
            )
        reachable_support_has_semantic_anchor = any(
            _support_reaches_target(
                support_target,
                target,
                declaration_headers,
                declaration_bodies,
            )
            and _endpoint_evidence_terms(
                _decl_text(support_target, declaration_headers, declaration_bodies)
            )
            for support_target in support_targets
        )
        semantic_refs_clear = bool(semantic_hits) or reachable_support_has_semantic_anchor
        has_independent_endpoint = (
            has_independent_support
            or public_semantic_endpoint
            or bool(reachable_endpoint_hits)
            or reachable_support_has_semantic_anchor
        )
        if not semantic_refs_clear and not public_semantic_endpoint:
            negative_witnesses.append(_make_sieve_witness(
                "no_semantic_refs",
                "suspicious",
                {
                    "checked_terms": list(_semantic_shift_terms_for_target(target)),
                    "semantic_hits": semantic_hits,
                    "reachable_support_has_semantic_anchor": reachable_support_has_semantic_anchor,
                    "constructor_only": bool(constructor_hits),
                },
                False,
            ))
            missing_support.append("semantic_anchor")

        substring_hits = _target_word_hits(target, evidence_text)
        substring_support_hits = _has_any(evidence_text, SUBSTRING_EVIDENCE_SUPPORT_TERMS)
        if block is not None and substring_hits and not substring_support_hits:
            negative_witnesses.append(_make_sieve_witness(
                "target_substring_evidence",
                "confirmed",
                {"substring_hits": substring_hits, "file": block["file"], "line": block["line"]},
                True,
            ))
            clearance_requirements.append(
                "replace name-substring evidence with decode, role, row, ledger, or NameCert witness"
            )

        if re.search(r"\bsmoke[A-Z_]", combined_text) or "smoke" in target.lower():
            negative_witnesses.append(_make_sieve_witness(
                "smoke_template_reuse",
                "suspicious",
                {"target": target},
                False,
            ))
            clearance_requirements.append("instantiate the site away from smoke template data")

        if block is not None and block.get("origin") == "ai" and block.get("theory_closure") != "seedClosure":
            missing_fields = [
                field for field in (
                    "closureclaimkind",
                    "closurenamecert",
                    "closureledger",
                    "closureclassifierincrement",
                )
                if not str(open_fields.get(field, "")).strip()
            ]
            if missing_fields:
                negative_witnesses.append(_make_sieve_witness(
                    "missing_discovery_rows",
                    "confirmed",
                    {"missing_fields": missing_fields, "file": block["file"], "line": block["line"]},
                    True,
                ))
                missing_support.extend(missing_fields)
                clearance_requirements.append(
                    "fill discovery closureclaimkind, NameCert, ledger, and classifier increment rows"
                )

        scopeclosed = str(block.get("scopeclosed", "")) if block is not None else ""
        if (
            scopeclosed
            and any(term in scopeclosed.lower() for term in SCOPE_OVERCLAIM_TERMS)
            and not _has_structured_scope_seal(open_fields)
        ):
            negative_witnesses.append(_make_sieve_witness(
                "scope_overclaim",
                "suspicious",
                {"scopeclosed": scopeclosed[:240]},
                False,
            ))
            clearance_requirements.append("add a scoped seal or narrow the scopeclosed claim")

        introduced = _parse_nat_assignment(body, "introduced_rows")
        refusal = _parse_nat_assignment(body, "refusal_rows")
        bridge = _parse_nat_assignment(body, "bridge_rows")
        debt = _parse_nat_assignment(body, "not_claimed_rows")
        scope_seal = 1 if re.search(r"\bclassifier_shift\s*:=\s*some\b", body) else 0
        parsed_accounting = None not in (introduced, refusal, bridge, debt)
        benefit = (introduced or 0) + (refusal or 0)
        has_weight_profile = bool(str(open_fields.get("closureweightprofile", "")).strip())
        if (
            target in ledger_by_name
            and parsed_accounting
            and benefit >= 3
            and (bridge or 0) == 0
            and (debt or 0) == 0
            and scope_seal == 0
            and not has_weight_profile
        ):
            negative_witnesses.append(_make_sieve_witness(
                "inflated_benefit",
                "suspicious",
                {
                    "benefit": benefit,
                    "cost": bridge or 0,
                    "debt": debt or 0,
                    "scopeSeal": scope_seal,
                },
                False,
            ))
            clearance_requirements.append(
                "add a weight profile or expose cost, debt, and scope-seal accounting"
            )

        tags = [str(witness["reason_tag"]) for witness in negative_witnesses]
        confirmed_tags = {
            "target_missing",
            "target_axiom",
            "target_sorry",
            "target_substring_evidence",
            "missing_discovery_rows",
        }
        suspicious_count = sum(
            1
            for witness in negative_witnesses
            if witness.get("severity") == "suspicious"
        )
        has_nontrivial_shift = (
            "classifier_shift" in site.get("sources", [])
            and "trivial_classifier" not in tags
            and "smoke_template_reuse" not in tags
        )
        has_complete_rows = "missing_discovery_rows" not in tags
        has_strong_structure = has_independent_support
        if any(tag in confirmed_tags for tag in tags):
            grade = "confirmed_composite"
        elif suspicious_count >= 2:
            grade = "probable_composite"
        elif not negative_witnesses and has_strong_structure and has_nontrivial_shift and has_complete_rows:
            grade = "certified_prime"
        elif not negative_witnesses and (semantic_hits or support_hits):
            grade = "probable_prime"
        else:
            grade = "probable_composite" if negative_witnesses else "probable_prime"

        missing_support = sorted(set(missing_support))
        clearance_requirements = sorted(set(clearance_requirements))
        adversarial_input_targets = sorted(set(
            support_targets
            + _classifier_shift_read_targets(
                target,
                declaration_headers,
                declaration_bodies,
            )
            + negative_branch_read_targets
        ))
        target_fingerprint = _target_fingerprint(
            target,
            support_targets,
            adversarial_input_targets,
            block,
            declaration_headers,
            declaration_bodies,
        )
        adversarial_witness_records = _adversarial_witnesses_for_target(
            target,
            target_fingerprint,
            block,
            support_targets,
            negative_witnesses,
            negative_branch_text,
            ledger_by_name,
            has_independent_endpoint,
            declaration_headers,
            declaration_bodies,
        )
        adversarial_witnesses = [
            witness.to_json() for witness in adversarial_witness_records
        ]
        for witness in adversarial_witness_records:
            adversarial_verdict_counts[witness.verdict] += 1
        adversarial_score = _adversarial_resistance_score(adversarial_witness_records)
        profile = {
            "region": region,
            "target": target,
            "target_fingerprint": target_fingerprint,
            "sources": site.get("sources", []),
            "grade": grade,
            "grade_semantics": "static_sieve_only_not_truth",
            "sieve_profile": {
                "reason_tags": tags,
                "semantic_anchors": semantic_hits,
                "support_anchors": support_hits,
                "support_targets": support_targets,
                "adversarial_input_targets": adversarial_input_targets,
                "support_result_types": support_result_types,
                "support_reachable": [
                    support_target for support_target in support_targets
                    if _support_reaches_target(
                        support_target,
                        target,
                        declaration_headers,
                        declaration_bodies,
                    )
                ],
                "public_semantic_endpoint": public_semantic_endpoint,
                "suspicious_count": suspicious_count,
            },
            "negative_witnesses": negative_witnesses,
            "adversarial_witnesses": adversarial_witnesses,
            "adversarial_resistance_score": adversarial_score,
            "score_semantics": "ranking_only_not_probability",
            "recomputed_witness_snapshot": _recomputed_witness_snapshot_payload(
                target_fingerprint,
                adversarial_witness_records,
            ),
            "missing_support": missing_support,
            "clearance_requirements": clearance_requirements,
            "file": site.get("file") or (block["file"] if block else ""),
            "line": site.get("line") or (block["line"] if block else 0),
        }
        profiles.append(profile)
        grade_counts[grade] += 1

    return {
        "informational": True,
        "checked_target_count": len(profiles),
        "grade_counts": dict(sorted(grade_counts.items())),
        "adversarial_witness_count": sum(adversarial_verdict_counts.values()),
        "adversarial_verdict_counts": dict(sorted(adversarial_verdict_counts.items())),
        "score_semantics": "ranking_only_not_probability",
        "targets": profiles,
    }


def _region_to_derived_module(region: object) -> str:
    text = str(region or "").strip()
    if text.endswith("Up"):
        text = text[:-2]
    return f"BEDC.Derived.{text}Up"


def _region_to_chapter_key(region: object) -> str:
    text = str(region or "")
    if text.endswith("Up"):
        text = text[:-2]
    return _camel_to_snake(text)


def _block_is_a_layer_hard_reject(block: dict, origin: str) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    if origin == "human":
        reasons.append("origin_human")
    theory_closure = str(block.get("theory_closure") or "")
    formal_status = str(block.get("formal_status") or "")
    bridge_status = str(block.get("bridge_status") or "")
    if theory_closure in A_LAYER_HARD_REJECT_THEORY_CLOSURES:
        reasons.append(f"theory_closure:{theory_closure}")
    if formal_status in A_LAYER_HARD_REJECT_FORMAL_STATUSES:
        reasons.append(f"formal_status:{formal_status}")
    if bridge_status in A_LAYER_HARD_REJECT_BRIDGE_STATUSES:
        reasons.append(f"bridge_status:{bridge_status}")
    return bool(reasons), reasons


def _decl_kind_map(declarations: list[DeclarationRecord]) -> dict[str, str]:
    return {decl.qualified_name: decl.kind for decl in declarations}


def _support_type_hits(
    targets: Iterable[str],
    declaration_headers: dict[str, str],
) -> list[str]:
    hits: set[str] = set()
    for target in targets:
        result_type = _declaration_header_result_type(
            declaration_headers.get(target, ""),
        ) or ""
        for term in DISCOVERY_CANDIDATE_SUPPORT_TYPES:
            if re.search(rf"\b(?:[A-Za-z0-9_'.]+\.)?{term}\b", result_type):
                hits.add(term)
    return sorted(hits)


def _candidate_semantic_endpoint_classes(semantic_hits: Iterable[str]) -> list[str]:
    hits = set(semantic_hits)
    classes: set[str] = set()
    if hits.intersection({"namecert", "ledger_policy", "pattern_spec", "stability_spec"}):
        classes.add("certified_rows")
    if hits.intersection({"decode", "readback", "role", "ledger_row", "event_flow"}):
        classes.add("observable_endpoint")
    if hits.intersection({"field_faithful", "observable_family_witness"}):
        classes.add("field_faithful_route")
    return sorted(classes)


def _declaration_is_alias_or_wrapper(
    before: str,
    after: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> bool:
    if before == after:
        return True
    body = declaration_bodies.get(after, "")
    result_type = _declaration_header_result_type(declaration_headers.get(after, "")) or ""
    before_local = _local_declaration_name(before)
    after_local = _local_declaration_name(after)
    body_no_ws = re.sub(r"\s+", " ", body).strip()
    if re.fullmatch(
        rf".*:=\s*(?:{re.escape(before)}|{re.escape(before_local)})\s*$",
        body_no_ws,
    ):
        return True
    if before_local and after_local:
        stripped_before = before_local.lower().removesuffix("classifier")
        stripped_after = after_local.lower().removesuffix("classifier")
        if stripped_before and stripped_before == stripped_after:
            return True
    if before in result_type and after_local in before_local:
        return True
    return False


def _candidate_endpoint_pairs(
    block: dict,
    target: str,
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> list[tuple[str, str, str]]:
    open_fields = block.get("open_fields") or {}
    if not isinstance(open_fields, dict):
        open_fields = {}
    before_sources = [
        _normalize_lean_target(part)
        for field in ("closureparents", "closurelineage")
        for part in re.split(r"[,;\s]+", str(open_fields.get(field, "")))
        if _normalize_lean_target(part)
    ]
    after_sources = [
        _normalize_lean_target(open_fields.get("closuregate")),
        _normalize_lean_target(open_fields.get("closureledger")),
        _normalize_lean_target(block.get("lean_target")),
        _normalize_lean_target(target),
    ]
    text = "\n".join([
        str(block.get("raw_body", "")),
        declaration_headers.get(target, ""),
        declaration_bodies.get(target, ""),
    ])
    mentioned = [
        name for name in sorted(set(
            re.findall(
                r"\bBEDC(?:\.[A-Za-z][A-Za-z0-9_']+)+\b",
                text,
            )
        ))
        if name in declaration_headers
        and re.search(r"(Classifier|Disagreement|Discovery|Gate|Ledger)$", _local_declaration_name(name))
    ]
    before_sources.extend(mentioned)
    after_sources.extend(mentioned)
    before_valid = [name for name in dict.fromkeys(before_sources) if name in declaration_headers]
    after_valid = [name for name in dict.fromkeys(after_sources) if name in declaration_headers]
    pairs: list[tuple[str, str, str]] = []
    for before in before_valid:
        for after in after_valid:
            if before == after:
                continue
            if _declaration_is_alias_or_wrapper(
                before,
                after,
                declaration_headers,
                declaration_bodies,
            ):
                continue
            pairs.append((before, after, "resolved_from_closure_or_lean_declaration"))
    return pairs[:8]


def _discovery_candidate_note(
    block: dict,
    target: str,
    reason: str,
    *,
    extra: dict[str, object] | None = None,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "tier": "B",
        "region": f"{block.get('region')}Up",
        "chapter_key": _region_to_chapter_key(block.get("region")),
        "target": target,
        "file": block.get("file"),
        "line": block.get("line"),
        "reason": reason,
    }
    if extra:
        payload.update(extra)
    return payload


def discovery_candidate_payload(
    blocks: list[dict],
    lean_scan: LeanSourceScan,
    *,
    max_a: int = 3,
    sieve_payload: dict[str, object] | None = None,
) -> dict[str, object]:
    """High-precision production-side discovery candidate survey.

    This is an informational miner. It admits dispatchable candidates only when
    the chapter supplies real Lean before/after endpoints, graph-reachable
    disagreement support, semantic endpoint classes, and no hard negative tags.
    """
    declarations = lean_scan.declarations
    declaration_headers = lean_scan.declaration_headers
    declaration_bodies = lean_scan.declaration_bodies
    ledgers = lean_scan.discovery_delta_ledgers
    decl_kinds = _decl_kind_map(declarations)
    ledger_targets = {ledger.qualified_name for ledger in ledgers}
    dispatchable: list[dict[str, object]] = []
    notes: list[dict[str, object]] = []
    discarded = 0

    for block in blocks:
        if block.get("error"):
            continue
        origin = str(block.get("origin") or "human").lower()
        open_fields = block.get("open_fields") or {}
        open_fields = open_fields if isinstance(open_fields, dict) else {}
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        if origin == "human" and claim_kind not in STRONG_CLOSURESTATUS_CLAIMS:
            discarded += 1
            continue
        if claim_kind in {"confirmed_composite", "mechanical_reconstruction"}:
            discarded += 1
            continue
        hard_reject, hard_reject_reasons = _block_is_a_layer_hard_reject(block, origin)
        if hard_reject:
            notes.append(_discovery_candidate_note(
                block,
                _normalize_lean_target(block.get("lean_target")),
                "hard reject from dispatchable discovery candidate layer",
                extra={"candidate_reasons": hard_reject_reasons, "in_A": False},
            ))
            continue
        has_explicit_candidate_surface = (
            claim_kind in STRONG_CLOSURESTATUS_CLAIMS
            or any(
                str(open_fields.get(field, "")).strip()
                for field in (
                    "closureparents",
                    "closurelineage",
                    "closuregate",
                    "closureledger",
                    "closureclassifierincrement",
                )
            )
        )
        if not has_explicit_candidate_surface:
            if origin == "ai" and block.get("theory_closure") != "seedClosure":
                notes.append(_discovery_candidate_note(
                    block,
                    "",
                    "ai non-seed chapter has no explicit before/after or discovery ledger surface",
                ))
            else:
                discarded += 1
            continue

        target_candidates = [
            _normalize_lean_target(open_fields.get("closuregate")),
            _normalize_lean_target(open_fields.get("closureledger")),
            _normalize_lean_target(block.get("lean_target")),
            _region_to_derived_module(block.get("region")),
        ]
        target_candidates = [target for target in dict.fromkeys(target_candidates) if target]
        target = next((name for name in target_candidates if name in declaration_headers), "")
        if not target:
            if origin == "ai" and block.get("theory_closure") != "seedClosure":
                notes.append(_discovery_candidate_note(
                    block,
                    target_candidates[0] if target_candidates else "",
                    "ai non-seed chapter lacks a resolved Lean target endpoint",
                ))
            else:
                discarded += 1
            continue

        pairs = _candidate_endpoint_pairs(block, target, declaration_headers, declaration_bodies)
        if not pairs:
            if origin == "ai" and block.get("theory_closure") != "seedClosure":
                notes.append(_discovery_candidate_note(
                    block,
                    target,
                    "no resolved before/after Lean classifier endpoint pair",
                ))
            else:
                discarded += 1
            continue

        reachable = _reachable_declarations(
            [target],
            declaration_headers,
            declaration_bodies,
            max_depth=8,
        )
        support_targets = sorted(set(
            _disagreement_support_declarations(
                target,
                declaration_headers,
                declaration_bodies,
            )
        ))
        support_hits = _support_type_hits(
            set(reachable) | set(support_targets) | {target},
            declaration_headers,
        )
        if not support_hits:
            notes.append(_discovery_candidate_note(
                block,
                target,
                "reachable declaration graph lacks classifier disagreement support",
                extra={"before_after_pairs": pairs},
            ))
            continue

        tags: list[str] = []
        target_text = _decl_text(target, declaration_headers, declaration_bodies)
        if _body_mentions_axiom(target_text):
            tags.append("target_axiom")
        if _body_mentions_sorry(target_text):
            tags.append("target_sorry")
        if re.search(r"\bsmoke[A-Z_]", target_text) or "smoke" in target.lower():
            tags.append("smoke_template_reuse")
        evidence_text = "\n".join(str(open_fields.get(name, "")) for name in CLOSURESTATUS_OPEN_FIELDS)
        if _target_word_hits(target, evidence_text) and not _has_any(
            evidence_text,
            SUBSTRING_EVIDENCE_SUPPORT_TERMS,
        ):
            tags.append("target_substring_evidence")
        support_text_for_tags = "\n".join(
            _decl_text(support_target, declaration_headers, declaration_bodies)
            for support_target in support_targets
        )
        if _has_any(support_text_for_tags, TRIVIAL_CLASSIFIER_TERMS):
            tags.append("trivial_classifier")
        disagreement_text_for_tags = "\n".join(
            _decl_text(qualified, declaration_headers, declaration_bodies)
            for qualified in _target_disagreement_anchors(
                target,
                declaration_headers,
                declaration_bodies,
            )
        )
        constructor_only = bool(_has_any(
            f"{support_text_for_tags}\n{disagreement_text_for_tags}",
            CONSTRUCTOR_SEPARATION_TERMS,
        ))
        if constructor_only:
            tags.append("constructor_only_disagreement")
        hard_tags = sorted(set(tags).intersection(DISCOVERY_CANDIDATE_HARD_REJECT_TAGS))
        if hard_tags:
            notes.append(_discovery_candidate_note(
                block,
                target,
                "hard negative sieve witness prevents dispatch",
                extra={"negative_tags": hard_tags},
            ))
            continue

        semantic_hits = sorted(set(
            _reachable_endpoint_evidence_terms(
                target,
                declaration_headers,
                declaration_bodies,
            )
            + _support_semantic_evidence_terms(
                support_targets,
                declaration_headers,
                declaration_bodies,
            )
            + _endpoint_evidence_terms(
                _decl_text(target, declaration_headers, declaration_bodies),
            )
        ))
        classes = _candidate_semantic_endpoint_classes(semantic_hits)
        has_independent_support = _has_independent_disagreement_support(
            support_targets,
            declaration_headers,
            declaration_bodies,
            target,
        )
        if len(classes) < 2:
            notes.append(_discovery_candidate_note(
                block,
                target,
                "fewer than two nontrivial semantic endpoint classes",
                extra={"semantic_anchors": semantic_hits, "endpoint_classes": classes},
            ))
            continue
        if constructor_only and not has_independent_support:
            notes.append(_discovery_candidate_note(
                block,
                target,
                "constructor-only disagreement lacks independent observable witness",
                extra={"semantic_anchors": semantic_hits, "support_targets": support_targets},
            ))
            continue

        before, after, endpoint_source = pairs[0]
        stable_key = "|".join([
            _region_to_chapter_key(block.get("region")),
            "classifier_shift_candidate",
            target,
            before,
            after,
        ])
        candidate_reasons = [
            reason for reason, active in (
                ("origin_ai_non_seed", origin == "ai" and block.get("theory_closure") != "seedClosure"),
                ("strong_closurestatus_claim", claim_kind in STRONG_CLOSURESTATUS_CLAIMS),
                ("resolved_lean_target", bool(target)),
                ("resolved_before_after_pair", bool(pairs)),
                ("reachable_disagreement_support", bool(support_hits)),
                ("semantic_endpoint_classes", len(classes) >= 2),
                ("independent_disagreement_support", has_independent_support),
            )
            if active
        ]
        score = 0.0
        score += 0.30 if origin == "ai" and block.get("theory_closure") != "seedClosure" else 0.0
        score += 0.20 if {"certified_rows", "observable_endpoint"}.issubset(classes) else 0.0
        score += 0.20 if "field_faithful_route" in classes else 0.0
        score += 0.10 if claim_kind in STRONG_CLOSURESTATUS_CLAIMS else 0.0
        score -= 0.30 if origin == "human" else 0.0
        dispatchable.append({
            "tier": "A",
            "kind": "discovery_candidate",
            "candidate_kind": "classifier_shift_candidate",
            "stable_key": stable_key,
            "region": f"{block.get('region')}Up",
            "chapter_key": _region_to_chapter_key(block.get("region")),
            "file_paper": block.get("file"),
            "line": block.get("line"),
            "target": target,
            "target_kind": decl_kinds.get(target),
            "before_classifier": before,
            "after_classifier": after,
            "endpoint_source": endpoint_source,
            "support_targets": support_targets,
            "support_anchors": support_hits,
            "semantic_anchors": semantic_hits,
            "semantic_endpoint_classes": classes,
            "negative_tags": tags,
            "candidate_reasons": candidate_reasons,
            "candidate_score": round(score, 4),
            "confidence": "high",
            "dispatch_intent": "attempt_delta_ledger_or_mark_mechanical",
            "dispatch_note": (
                "Try one bounded pass to prove concrete before/after classifier "
                "disagreement with positive cost margin and semantic endpoint; "
                "otherwise record auditable mechanical_reconstruction."
            ),
            "mechanical_risk": [
                risk for risk, active in (
                    ("known_math_namecert", origin == "human"),
                    ("constructor_only_disagreement", constructor_only),
                    ("insufficient_evidence", len(classes) < 3),
                )
                if active
            ],
            "allowed_outcomes": [
                "positiveDiscovery",
                "discovery",
                "mechanical_reconstruction",
                "reject_candidate",
            ],
        })

    dispatchable.sort(
        key=lambda row: (-float(row.get("candidate_score", 0.0)), str(row["stable_key"]))
    )
    for idx, row in enumerate(dispatchable, start=1):
        row["selection_rank"] = idx

    sieve = sieve_payload or discovery_sieve_payload(
        blocks,
        ledgers,
        declaration_headers,
        declaration_bodies,
    )
    grade_counts = Counter(str(item.get("grade")) for item in sieve.get("targets", []) if isinstance(item, dict))
    declared_candidate = sum(
        1 for item in sieve.get("targets", [])
        if isinstance(item, dict)
        and (
            "classifier_shift" in item.get("sources", [])
            or item.get("target") in ledger_targets
        )
    )
    sieve_survivor = sum(
        1 for item in sieve.get("targets", [])
        if isinstance(item, dict)
        and item.get("grade") in ("probable_prime", "certified_prime")
    )
    certified_prime = int(grade_counts.get("certified_prime", 0))
    falseish = int(grade_counts.get("confirmed_composite", 0)) + int(grade_counts.get("probable_composite", 0))
    mechanical_optout = sum(
        1 for block in blocks
        if str((block.get("open_fields") or {}).get("closureclaimkind", "")).strip()
        in {"mechanical_reconstruction", "confirmed_composite"}
    )
    inspected = declared_candidate + mechanical_optout
    metrics = {
        "declared_candidate": declared_candidate,
        "sieve_survivor": sieve_survivor,
        "certified_prime": certified_prime,
        "false_discovery_rate": round(falseish / declared_candidate, 4) if declared_candidate else None,
        "mechanical_optout_rate": round(mechanical_optout / inspected, 4) if inspected else None,
        "silent_candidate_escape_rate": round(
            len(notes) / max(len(notes) + len(dispatchable) + mechanical_optout, 1),
            4,
        ),
    }
    optout_findings = mechanical_optout_audit_payload(blocks, declaration_headers)
    return {
        "informational": True,
        "semantics": "high_precision_low_recall_static_candidate_survey_not_truth",
        "candidate_count": len(dispatchable[:max_a]),
        "candidate_count_total": len(dispatchable),
        "diagnostic_count": len(notes),
        "discarded_count": discarded,
        "candidates": dispatchable[:max_a],
        "diagnostic_notes": notes[:200],
        "metrics": metrics,
        "mechanical_optout_audit": optout_findings,
    }


def _parse_mechanical_metadata(text: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for key in ("mechanical_reason", "nearest_existing_target", "checked_by_worker"):
        match = re.search(rf"\b{key}\s*=\s*([A-Za-z0-9_'.:-]+)", text)
        if match:
            fields[key] = match.group(1)
    return fields


def _resolve_mechanical_nearest_target(
    target: str,
    block: dict,
    declaration_headers: dict[str, str],
    chapter_targets: set[str],
) -> tuple[bool, str]:
    normalized = _normalize_lean_target(target)
    if not normalized:
        return False, "missing"
    if normalized in declaration_headers:
        return True, "lean_target"
    if normalized in chapter_targets or _region_to_chapter_key(normalized) in chapter_targets:
        return True, "chapter_target"
    chapter_key = _region_to_chapter_key(block.get("region"))
    candidates = {
        str(block.get("region") or ""),
        f"{block.get('region')}Up",
        _region_to_derived_module(block.get("region")),
        str(block.get("lean_target") or ""),
    }
    if normalized in {candidate for candidate in candidates if candidate}:
        return True, "chapter_target"
    if _region_to_chapter_key(normalized) == chapter_key:
        return True, "chapter_target"
    return False, "unresolved"


def mechanical_optout_audit_payload(
    blocks: list[dict],
    declaration_headers: dict[str, str] | None = None,
) -> dict[str, object]:
    findings: list[dict[str, object]] = []
    reason_counts: Counter[str] = Counter()
    declaration_headers = collect_declaration_headers() if declaration_headers is None else declaration_headers
    chapter_targets = {
        candidate
        for block in blocks
        for candidate in (
            _region_to_chapter_key(block.get("region")),
            str(block.get("region") or ""),
            f"{block.get('region')}Up",
            _region_to_derived_module(block.get("region")),
            str(block.get("lean_target") or ""),
        )
        if candidate and candidate != "NoneUp"
    }
    for block in blocks:
        open_fields = block.get("open_fields") or {}
        if not isinstance(open_fields, dict):
            continue
        claim_kind = str(open_fields.get("closureclaimkind", "")).strip()
        if claim_kind not in {"mechanical_reconstruction", "confirmed_composite"}:
            continue
        text = "\n".join(str(open_fields.get(field, "")) for field in CLOSURESTATUS_OPEN_FIELDS)
        text = f"{text}\n{block.get('raw_body', '')}"
        metadata = _parse_mechanical_metadata(text)
        reason = metadata.get("mechanical_reason", "")
        if reason:
            reason_counts[reason] += 1
        if not reason:
            findings.append(_discovery_item(
                block,
                "missing_mechanical_reason",
                "mechanical opt-out lacks mechanical_reason",
            ))
        elif reason not in DISCOVERY_MECHANICAL_REASONS:
            findings.append(_discovery_item(
                block,
                "unknown_mechanical_reason",
                "mechanical_reason is outside the accepted enumeration",
                evidence=reason,
            ))
        nearest_target = metadata.get("nearest_existing_target", "")
        nearest_resolved, nearest_resolution = _resolve_mechanical_nearest_target(
            nearest_target,
            block,
            declaration_headers,
            chapter_targets,
        )
        if not nearest_resolved:
            findings.append(_discovery_item(
                block,
                "missing_resolved_nearest_existing_target",
                "mechanical opt-out must name nearest_existing_target resolving to a chapter or Lean target",
                evidence=nearest_resolution if not nearest_target else nearest_target,
            ))
        if reason == "insufficient_evidence":
            worker = metadata.get("checked_by_worker")
            if not worker:
                findings.append(_discovery_item(
                    block,
                    "insufficient_evidence_missing_worker",
                    "insufficient_evidence must name checked_by_worker",
                ))
            if not _has_any(text, MECHANICAL_INSUFFICIENT_EVIDENCE_TOKENS):
                findings.append(_discovery_item(
                    block,
                    "insufficient_evidence_missing_inspected_token",
                    "insufficient_evidence must name inspected carrier/classifier/parent/sibling evidence or an explicit reject",
                ))
        if reason == "classifier_unchanged" and not re.search(
            r"\b(same_classifier|same_source|same_pattern|formalstatus_only|bridge_only)\b",
            text,
        ):
            findings.append(_discovery_item(
                block,
                "classifier_unchanged_missing_invariant",
                "classifier_unchanged must name the concrete unchanged classifier item",
            ))
        if reason == "duplicate_of_existing" and not nearest_resolved:
            findings.append(_discovery_item(
                block,
                "duplicate_missing_resolved_target",
                "duplicate_of_existing must name a nearest_existing_target resolving to a chapter or Lean target",
            ))
        if not metadata.get("checked_by_worker"):
            findings.append(_discovery_item(
                block,
                "missing_checked_by_worker",
                "mechanical opt-out must record checked_by_worker",
            ))
    return {
        "informational": True,
        "finding_count": len(findings),
        "mechanical_optout_violation_count": len(findings),
        "findings": findings,
        "mechanical_reason_counts": dict(sorted(reason_counts.items())),
        "accepted_reasons": sorted(DISCOVERY_MECHANICAL_REASONS),
    }


def classifier_shift_quality_payload(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> dict[str, object]:
    sieve = discovery_sieve_payload(blocks, ledgers, declaration_headers, declaration_bodies)
    classifier_targets = {
        str(item["target"])
        for item in _classifier_shift_target_names(blocks, ledgers, declaration_headers)
    }
    findings: list[dict[str, object]] = []
    for profile in sieve["targets"]:
        if profile["target"] not in classifier_targets:
            continue
        if profile["grade"] not in ("probable_composite", "confirmed_composite"):
            continue
        reason_tags = profile["sieve_profile"]["reason_tags"]
        if not set(reason_tags).intersection({
            "constructor_only_disagreement",
            "trivial_classifier",
            "no_semantic_refs",
            "smoke_template_reuse",
        }):
            continue
        findings.append({
            "kind": profile["grade"],
            "target": profile["target"],
            "reason": "classifier shift profile failed discovery sieve",
            "sieve_profile": profile["sieve_profile"],
            "grade_semantics": profile.get("grade_semantics"),
            "source": ",".join(profile.get("sources", [])),
            "file": profile["file"],
            "line": profile["line"],
        })
    return {
        "informational": True,
        "checked_target_count": len(classifier_targets),
        "finding_count": len(findings),
        "findings": findings,
    }


def discovery_adversarial_payload(
    blocks: list[dict],
    ledgers: list[DiscoveryDeltaLedgerRecord],
    declaration_headers: dict[str, str],
    declaration_bodies: dict[str, str],
) -> dict[str, object]:
    sieve = discovery_sieve_payload(
        blocks,
        ledgers,
        declaration_headers,
        declaration_bodies,
    )
    targets: list[dict[str, object]] = []
    witness_count = 0
    verdict_counts: Counter[str] = Counter()
    for item in sieve["targets"]:
        witnesses = list(item.get("adversarial_witnesses", []))
        witness_count += len(witnesses)
        for witness in witnesses:
            if isinstance(witness, dict):
                verdict_counts[str(witness.get("verdict", ""))] += 1
        targets.append({
            "target": item["target"],
            "target_fingerprint": item.get("target_fingerprint", ""),
            "adversarial_resistance_score": item.get("adversarial_resistance_score", 100),
            "score_semantics": item.get(
                "score_semantics",
                "ranking_only_not_probability",
            ),
            "recomputed_witness_snapshot": item.get("recomputed_witness_snapshot", {}),
            "adversarial_witnesses": witnesses,
        })
    return {
        "informational": True,
        "checked_target_count": sieve["checked_target_count"],
        "adversarial_witness_count": witness_count,
        "adversarial_verdict_counts": dict(sorted(verdict_counts.items())),
        "score_semantics": "ranking_only_not_probability",
        "snapshot_semantics": "recomputed_read_model_fingerprint_gated",
        "truth_boundary": "suspected-composite-by-Fi only; no composite or prime truth verdict is emitted",
        "targets": targets,
    }


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
    lean_scan = scan_lean_sources()
    declarations = lean_scan.declarations
    fields = lean_scan.fields
    discovery_delta_ledgers = lean_scan.discovery_delta_ledgers
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
    theorem_dna_records = collect_theorem_dna_records()
    theorem_dna_coverage = theorem_dna_coverage_payload(
        theorem_dna_records,
        include_files=False,
    )
    theorem_dna_stale = theorem_dna_stale_payload(theorem_dna_records)
    discovery_ledger_coverage = discovery_ledger_coverage_payload(
        closurestatus_blocks,
        discovery_delta_ledgers,
        lean_scan.declaration_headers,
    )
    mechanical_optout_audit = mechanical_optout_audit_payload(
        closurestatus_blocks,
        lean_scan.declaration_headers,
    )
    classifier_shift_quality = classifier_shift_quality_payload(
        closurestatus_blocks,
        discovery_delta_ledgers,
        lean_scan.declaration_headers,
        lean_scan.declaration_bodies,
    )
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
    positive_discovery_warnings = positive_discovery_target_warnings(
        closurestatus_blocks,
        declarations,
        lean_scan.declaration_headers,
    )
    closurestatus_open_warnings.extend(positive_discovery_warnings)

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
        "theorem_dna_coverage": theorem_dna_coverage,
        "theorem_dna_stale": theorem_dna_stale,
        "theorem_dna_staleness": theorem_dna_stale,
        "discovery_ledger_coverage": discovery_ledger_coverage,
        "mechanical_optout_audit": mechanical_optout_audit,
        "mechanical_optout_violation_count": mechanical_optout_audit["mechanical_optout_violation_count"],
        "classifier_shift_quality": classifier_shift_quality,
        "positive_discovery_target_warnings": positive_discovery_warnings,
        "positive_discovery_target_warning_count": len(positive_discovery_warnings),
        "theorem_dna_coverage_count": theorem_dna_coverage["covered_count"],
        "theorem_dna_stale_count": theorem_dna_stale["stale_count"],
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
        ledger_coverage = payload["discovery_ledger_coverage"]
        print(
            "[bedc-ci] discovery ledger coverage (informational):"
            f" ai_origin_chapters={ledger_coverage['ai_origin_chapter_count']}"
            f" covered={ledger_coverage['covered_count']}"
            f" missing={ledger_coverage['missing_count']}"
            f" ledger_declarations={ledger_coverage['ledger_declaration_count']}"
            f" stem_warnings={ledger_coverage['stem_warning_count']}"
        )
        if ledger_coverage["missing"]:
            for item in ledger_coverage["missing"][:20]:
                print(
                    f"  missing {item['file']}:{item['line']}"
                    f" {item['region']} key={item['chapter_key']}"
                )
        if ledger_coverage["covered"]:
            for item in ledger_coverage["covered"][:20]:
                targets = ", ".join(str(target) for target in item["ledger_targets"])
                print(
                    f"  covered {item['file']}:{item['line']}"
                    f" {item['region']} -> {targets}"
                )
        optout_audit = payload["mechanical_optout_audit"]
        print(
            "[bedc-ci] mechanical opt-out audit (informational):"
            f" findings={optout_audit['finding_count']}"
            f" violations={optout_audit['mechanical_optout_violation_count']}"
        )
        for item in optout_audit["findings"][:20]:
            evidence = f" evidence={item['evidence']}" if item.get("evidence") else ""
            print(
                f"  {item['file']}:{item['line']} {item['region']}"
                f" {item['kind']}: {item['message']}{evidence}"
            )
        shift_quality = payload["classifier_shift_quality"]
        print(
            "[bedc-ci] classifier shift quality (informational):"
            f" checked={shift_quality['checked_target_count']}"
            f" probable_composite={shift_quality['finding_count']}"
        )
        for item in shift_quality["findings"][:20]:
            print(
                f"  {item['kind']} {item['target']}: "
                f"{item['reason']}"
            )
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
        dna_coverage = payload["theorem_dna_coverage"]
        dna_stale = payload["theorem_dna_stale"]
        print(
            "[bedc-ci] theorem-dna capability:"
            f" covered={dna_coverage['covered_count']}/{dna_coverage['chapters_total']}"
            f" current={dna_coverage['current_count']}"
            f" stale_changed={dna_stale['stale_count']}"
            f" changed_chapters={dna_stale['changed_chapters_count']}"
        )
        if dna_stale["stale"]:
            for item in dna_stale["stale"][:20]:
                loci = ", ".join(
                    str(locus["locus"])
                    for locus in item.get("stale_loci", [])[:8]
                )
                print(f"  {item['file']} region={item.get('region', '')}: stale DNA loci={loci}")
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


def cmd_theorem_dna(args: argparse.Namespace) -> int:
    if args.write:
        record = write_theorem_dna_hash(args.write)
        print(f"[bedc-ci] theorem-dna wrote {record.rel_path}: {record.computed_hash}")
        return 0

    payload = theorem_dna_payload()
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    coverage = payload["coverage"]
    staleness = payload["staleness"]
    if args.coverage:
        print(
            "[bedc-ci] theorem-dna coverage:"
            f" covered={coverage['covered_count']}/{coverage['chapters_total']}"
            f" current={coverage['current_count']}"
            f" missing={coverage['missing_count']}"
            f" mismatched={coverage['mismatch_count']}"
        )
        if args.verbose:
            for path in coverage["covered_files"]:
                print(f"  covered {path}")
            for path in coverage["missing_files"][:80]:
                print(f"  missing {path}")
            if len(coverage["missing_files"]) > 80:
                print(f"  ... and {len(coverage['missing_files']) - 80} more missing")
            for item in coverage["mismatch_files"][:80]:
                loci = ", ".join(
                    str(locus["locus"])
                    for locus in item.get("stale_loci", [])[:8]
                )
                print(
                    f"  mismatch {item['file']}:"
                    f" region={item.get('region', '')}"
                    f" stored={item['stored_hash']} computed={item['computed_hash']}"
                    f" loci={loci}"
                )

    print(
        "[bedc-ci] theorem-dna staleness:"
        f" changed_chapters={staleness['changed_chapters_count']}"
        f" stale={staleness['stale_count']}"
        " (capability mode)"
    )
    for item in staleness["stale"][:80]:
        print(f"  {item['file']} region={item.get('region', '')}")
        print(f"    stored:  {item['stored_hash']}")
        print(f"    current: {item['computed_hash']}")
        for locus in item.get("stale_loci", []):
            print(f"    locus {locus['locus']}: {locus['actual_excerpt']}")
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
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    lean_scan = scan_lean_sources()
    payload = discovery_audit_payload(blocks)
    payload["discovery_ledger_coverage"] = discovery_ledger_coverage_payload(
        blocks,
        lean_scan.discovery_delta_ledgers,
        lean_scan.declaration_headers,
    )
    payload["classifier_shift_quality"] = classifier_shift_quality_payload(
        blocks,
        lean_scan.discovery_delta_ledgers,
        lean_scan.declaration_headers,
        lean_scan.declaration_bodies,
    )
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        coverage = payload["discovery_ledger_coverage"]
        print(
            "[bedc-ci] discovery-audit (informational):"
            f" candidates={payload['candidate_count']}"
            f" ledger_gaps={payload['ledger_gap_count']}"
            f" scope_global_risks={payload['scope_global_risk_count']}"
            f" verification_ledger_gaps={payload['verification_ledger_gap_count']}"
            f" delta_ledger_missing={coverage['missing_count']}"
            f" probable_composite={payload['classifier_shift_quality']['finding_count']}"
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
            if coverage["missing"]:
                print("[bedc-ci] DeltaLedger coverage gaps:")
                for item in coverage["missing"][:80]:
                    print(
                        f"  {item['file']}:{item['line']}"
                        f" {item['region']} key={item['chapter_key']}"
                    )
            quality = payload["classifier_shift_quality"]
            if quality["findings"]:
                print("[bedc-ci] classifier shift quality findings:")
                for item in quality["findings"][:80]:
                    print(
                        f"  {item['kind']} {item['target']}:"
                        f" {item['reason']}"
                    )
    return 0


def cmd_discovery_sieve(args: argparse.Namespace) -> int:
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    lean_scan = scan_lean_sources()
    payload = discovery_sieve_payload(
        blocks,
        lean_scan.discovery_delta_ledgers,
        lean_scan.declaration_headers,
        lean_scan.declaration_bodies,
    )
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        counts = payload["grade_counts"]
        print(
            "[bedc-ci] discovery-sieve (informational):"
            f" checked={payload['checked_target_count']}"
            f" confirmed_composite={counts.get('confirmed_composite', 0)}"
            f" probable_composite={counts.get('probable_composite', 0)}"
            f" probable_prime={counts.get('probable_prime', 0)}"
            f" certified_prime={counts.get('certified_prime', 0)}"
        )
        if args.verbose:
            for item in payload["targets"][:120]:
                tags = ",".join(item["sieve_profile"]["reason_tags"]) or "clear"
                print(f"  {item['grade']} {item['target']} [{tags}]")
            if len(payload["targets"]) > 120:
                print(f"  ... and {len(payload['targets']) - 120} more")
    return 0


def cmd_discovery_adversarial(args: argparse.Namespace) -> int:
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    lean_scan = scan_lean_sources()
    payload = discovery_adversarial_payload(
        blocks,
        lean_scan.discovery_delta_ledgers,
        lean_scan.declaration_headers,
        lean_scan.declaration_bodies,
    )
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            "[bedc-ci] discovery-adversarial (informational):"
            f" checked={payload['checked_target_count']}"
            f" witnesses={payload['adversarial_witness_count']}"
            f" score_semantics={payload['score_semantics']}"
        )
        if args.verbose:
            for item in payload["targets"][:120]:
                verdicts = [
                    str(witness.get("verdict", ""))
                    for witness in item.get("adversarial_witnesses", [])
                    if isinstance(witness, dict)
                ]
                verdict_text = ",".join(verdicts) or "clear"
                print(
                    f"  score={item['adversarial_resistance_score']}"
                    f" {item['target']} [{verdict_text}]"
                )
            if len(payload["targets"]) > 120:
                print(f"  ... and {len(payload['targets']) - 120} more")
def cmd_discovery_candidates(args: argparse.Namespace) -> int:
    blocks = collect_closurestatus_blocks(PAPER_PARTS_ROOT)
    lean_scan = scan_lean_sources()
    payload = discovery_candidate_payload(blocks, lean_scan, max_a=args.max_a)
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        metrics = payload["metrics"]
        print(
            "[bedc-ci] discovery-candidates (informational):"
            f" A={payload['candidate_count']}"
            f" A_total={payload['candidate_count_total']}"
            f" B_notes={payload['diagnostic_count']}"
            f" declared_candidate={metrics['declared_candidate']}"
            f" sieve_survivor={metrics['sieve_survivor']}"
            f" certified_prime={metrics['certified_prime']}"
        )
        if args.verbose:
            for item in payload["candidates"]:
                print(
                    f"  A {item['region']} {item['target']}"
                    f" before={item['before_classifier']}"
                    f" after={item['after_classifier']}"
                    f" score={item['candidate_score']}"
                )
            for item in payload["diagnostic_notes"][:80]:
                print(
                    f"  B {item.get('region')} {item.get('target')}:"
                    f" {item.get('reason')}"
                )
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
    # worker worktree directory under a formalize worktree during
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

    theorem_dna_p = sub.add_parser(
        "theorem-dna",
        help="Report and maintain per-chapter theorem-DNA content hashes",
    )
    theorem_dna_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    theorem_dna_p.add_argument("--coverage", action="store_true", help="Show coverage counts")
    theorem_dna_p.add_argument("--verbose", "-v", action="store_true", help="Show covered/missing files")
    theorem_dna_p.add_argument("--write", type=str, default=None, help="Write/update \\dnahash for one concrete-instance chapter")
    theorem_dna_p.set_defaults(func=cmd_theorem_dna)

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

    discovery_sieve_p = sub.add_parser(
        "discovery-sieve",
        help="Informational multi-pass sieve for claimed discovery targets (always exit 0)",
    )
    discovery_sieve_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    discovery_sieve_p.add_argument("--verbose", "-v", action="store_true", help="Show per-target detail")
    discovery_sieve_p.set_defaults(func=cmd_discovery_sieve)

    discovery_adversarial_p = sub.add_parser(
        "discovery-adversarial",
        help="Informational deterministic adversarial witnesses for discovery targets (always exit 0)",
    )
    discovery_adversarial_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    discovery_adversarial_p.add_argument("--verbose", "-v", action="store_true", help="Show per-target detail")
    discovery_adversarial_p.set_defaults(func=cmd_discovery_adversarial)
    discovery_candidates_p = sub.add_parser(
        "discovery-candidates",
        help="Informational high-precision survey of production-side discovery candidates (always exit 0)",
    )
    discovery_candidates_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    discovery_candidates_p.add_argument("--verbose", "-v", action="store_true", help="Show candidate and diagnostic detail")
    discovery_candidates_p.add_argument("--max-a", type=int, default=3, help="Maximum dispatchable A-tier candidates to emit")
    discovery_candidates_p.set_defaults(func=cmd_discovery_candidates)

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

#!/usr/bin/env python3
"""BEDC Lean automation helpers for audit, inventory, and verification.

Subcommands:
  - audit: scan Lean / paper sources for BEDC-specific forbidden constructs and mismatches
  - inventory: build a declaration + paper-label + Lean-marker inventory
  - verify-files: run ``lake env lean`` on one or more Lean files

Newmath adaptation note:
  - This is a BEDC rewrite of automath's ``omega_ci.py``.
  - There is no deeply nested theory root here; the paper lives under ``papers/bedc/``.
  - The dedicated zero-axiom gate remains ``python3 tools/check-axioms.py``; this helper covers the broader audit surface.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
REPO_ROOT = LEAN_ROOT.parent
BEDC_ROOT = LEAN_ROOT / "BEDC"
PAPER_ROOT = REPO_ROOT / "papers" / "bedc"
PAPER_PARTS_ROOT = PAPER_ROOT / "parts"

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
LEAN_MARKER_RE = re.compile(r"\\(leanchecked|leansorryd|leanstmt|leandef)\{([^}]+)\}")

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


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def module_name(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


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


def collect_declarations(path: Path) -> tuple[list[DeclarationRecord], list[FieldRecord]]:
    text = strip_comments_and_strings(read_text(path))
    lines = text.splitlines()
    module = module_name(path)
    decls: list[DeclarationRecord] = []
    fields: list[FieldRecord] = []

    for idx, line in enumerate(lines, start=1):
        match = DECL_RE.match(line)
        if not match:
            continue
        kind = match.group("kind")
        name = (match.group("name") or f"<anonymous_{kind}_{idx}>").strip()
        qualified = name if name.startswith(module + ".") else f"{module}.{name}"
        decls.append(
            DeclarationRecord(
                module=module,
                file=str(path.relative_to(REPO_ROOT)),
                line=idx,
                kind=kind,
                name=name,
                qualified_name=qualified,
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
                            qualified_name=f"{module}.{ctor_name}",
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
        for match in LEAN_MARKER_RE.finditer(text):
            target = match.group(2).replace(r"\_", "_").strip()
            line = text.count("\n", 0, match.start()) + 1
            markers.append(LeanMarkerRecord(
                file=str(path.relative_to(PAPER_ROOT)),
                line=line,
                macro=match.group(1),
                target=target,
            ))
    return markers


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


def audit_payload() -> dict[str, object]:
    declarations, fields = build_declaration_inventory()
    part_labels = collect_part_labels()
    markers = collect_lean_markers()

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

    return {
        "forbidden_constructs": forbidden,
        "forbidden_construct_count": len(forbidden),
        "duplicate_part_labels": duplicate_part_labels,
        "missing_marker_targets": missing_marker_targets,
        "missing_marker_targets_count": len(missing_marker_targets),
        "inventory": inventory_payload(declarations, fields, part_labels, markers),
    }


def resolve_lean_file(raw_path: str) -> Path:
    path = Path(raw_path)
    if not path.is_absolute():
        path = (LEAN_ROOT / path).resolve()
    if not path.exists():
        raise FileNotFoundError(f"Lean file not found: {raw_path}")
    if path.suffix != ".lean":
        raise ValueError(f"Expected a .lean file: {raw_path}")
    return path


def cmd_audit(args: argparse.Namespace) -> int:
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
            print(f"[bedc-ci] unresolved Lean markers: {payload['missing_marker_targets_count']}")
            for item in payload["missing_marker_targets"][:50]:
                print(f"  {item['file']}:{item['line']} {item['macro']} -> {item['target']}")

    failures = (
        payload["forbidden_construct_count"]
        + payload["missing_marker_targets_count"]
        + len(payload["duplicate_part_labels"])
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
    audit_p.set_defaults(func=cmd_audit)

    inv_p = sub.add_parser("inventory", help="Emit declaration and paper inventory")
    inv_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    inv_p.set_defaults(func=cmd_inventory)

    verify_p = sub.add_parser("verify-files", help="Run lake env lean on selected files")
    verify_p.add_argument("paths", nargs="+", help="Lean file paths, relative to lean4/")
    verify_p.set_defaults(func=cmd_verify_files)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

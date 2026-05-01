#!/usr/bin/env python3
"""BEDC Lean automation helpers for audit, inventory, and verification.

Subcommands:
  - audit: scan Lean / paper sources for BEDC-specific forbidden constructs and mismatches
  - inventory: build a declaration + paper-label + Lean-marker inventory
  - manifest: emit a release-grade JSON manifest (inventory + git/package metadata)
  - manifest-check: check selected Lean theorem type shapes against a manifest
  - verify-files: run ``lake env lean`` on one or more Lean files

Newmath adaptation note:
  - This is a BEDC rewrite of automath's ``omega_ci.py``.
  - There is no deeply nested theory root here; the paper lives under ``papers/bedc/``.
  - The dedicated zero-axiom gate remains ``python3 tools/check-axioms.py``; this helper covers the broader audit surface.
"""

from __future__ import annotations

import argparse
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

NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z0-9_'.]+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(?P<name>[A-Za-z0-9_'.]+))?\s*$")

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


DEFAULT_FORBIDDEN_AXIOMS: tuple[str, ...] = (
    "Classical.choice",
    "Quot.sound",
)
STRICT_FORBIDDEN_AXIOMS: tuple[str, ...] = DEFAULT_FORBIDDEN_AXIOMS + ("propext",)
PRINT_AXIOMS_RE = re.compile(
    r"'([\w.·’]+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[(.*?)\])"
)


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
        }
    )
    if not theorems:
        print("[bedc-ci] axiom-purity: no BEDC theorems found", file=sys.stderr)
        return 0

    lean_lines = ["import BEDC", ""]
    lean_lines.extend(f"#print axioms {name}" for name in theorems)
    lean_source = "\n".join(lean_lines) + "\n"

    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix="axiom_audit_",
        dir=str(args.tmp_dir),
        delete=False,
        encoding="utf-8",
    ) as tmp:
        tmp.write(lean_source)
        tmp_path = Path(tmp.name)

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
    pure: list[str] = []
    impure: list[tuple[str, list[str]]] = []
    violations: list[tuple[str, str]] = []
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
    parsed = set(pure)
    parsed.update(decl for decl, _axs in impure)
    missing = sorted(set(theorems) - parsed)
    lean_failed = result.returncode != 0

    if args.json:
        payload = {
            "theorems_total": len(theorems),
            "pure_count": len(pure),
            "impure_count": len(impure),
            "violations": [
                {"declaration": decl, "axiom": ax} for decl, ax in violations
            ],
            "missing_results": missing,
            "lean_returncode": result.returncode,
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
            print(f"[bedc-ci] axiom-purity FAIL: lean returned {result.returncode}")
            tail = "\n".join(output.strip().splitlines()[-20:])
            if tail:
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
    audit_p.set_defaults(func=cmd_audit)

    inv_p = sub.add_parser("inventory", help="Emit declaration and paper inventory")
    inv_p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    inv_p.set_defaults(func=cmd_inventory)

    manifest_p = sub.add_parser("manifest", help="Emit release-grade JSON manifest (inventory + git/package metadata)")
    manifest_p.add_argument("--output", type=str, default=None, help="Output file path (defaults to stdout)")
    manifest_p.add_argument("--release-tag", type=str, default=None, help="Release tag to embed (overrides $RELEASE_TAG env)")
    manifest_p.set_defaults(func=cmd_manifest)

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
    purity_p.set_defaults(func=cmd_axiom_purity)

    verify_p = sub.add_parser("verify-files", help="Run lake env lean on selected files")
    verify_p.add_argument("paths", nargs="+", help="Lean file paths, relative to lean4/")
    verify_p.set_defaults(func=cmd_verify_files)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

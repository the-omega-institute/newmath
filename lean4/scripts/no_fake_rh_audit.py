#!/usr/bin/env python3
"""No-fake-RH source audit for BEDC Lean declarations.

This host-owned CI gate enforces the permanent BEDC_NO_FAKE_RH invariant:
Lean may carry conditional RH-route scaffolds, but it must not expose an
unconditional inhabitant of the RH core carriers.  The check is deliberately
stronger than a local ``exact?`` sentinel because it scans the whole BEDC Lean
tree and fails on any theorem/lemma/def/instance/abbrev whose result is one of
the core RH targets without a binder between the declaration name and the result
colon.

The Lean kernel remains the semantic authority.  This script is a source-level
environment gate that prevents accidental or dishonest unconditional RH/CRPC
inhabitants from entering CI.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable


TOKEN = "BEDC_NO_FAKE_RH"
SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
REPO_ROOT = LEAN_ROOT.parent
BEDC_ROOT = LEAN_ROOT / "BEDC"

DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual|local)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|inductive|class|structure)\s+"
    r"(?:(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)\b)?"
)
CHECKED_KINDS = {"theorem", "lemma", "def", "instance", "abbrev"}
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(?P<name>[A-Za-z0-9_'.]+)\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(?P<name>[A-Za-z0-9_'.]+))?\s*$")

QUALIFIED_CONSTRUCTIVE_RH_RE = r"(?:[A-Za-z0-9_'.]+\.)?ConstructiveRH"
QUALIFIED_CRPC_RE = r"(?:[A-Za-z0-9_'.]+\.)?CausalReflectionPositiveCone"
CORE_TARGET_RE = re.compile(
    r"^(?:"
    rf"{QUALIFIED_CONSTRUCTIVE_RH_RE}"
    r"|"
    rf"{QUALIFIED_CRPC_RE}"
    r"|Nonempty\s+\(?\s*"
    rf"{QUALIFIED_CONSTRUCTIVE_RH_RE}"
    r"\s*\)?"
    r"|Nonempty\s+\(?\s*"
    rf"{QUALIFIED_CRPC_RE}"
    r"\s*\)?"
    r")$"
)
CONSTRUCTIVE_RH_RE = re.compile(rf"^{QUALIFIED_CONSTRUCTIVE_RH_RE}$")
ANCHOR_RE = re.compile(
    r"\b(?:CausalReflectionPositiveCone|CRPC|AnalyticGombocRHHandoff)\b"
)
TOY_ROUTE_RE = re.compile(
    r"\b(?:HerglotzPositivity|StieltjesPositiveSpectral|"
    r"WeilGramReduction|PickHilbertDecomposition)\b"
)


@dataclass(frozen=True)
class LeanDeclaration:
    kind: str
    name: str
    qualified_name: str
    file: str
    line: int
    header: str
    result_type: str | None
    prefix: str


@dataclass(frozen=True)
class AuditFinding:
    declaration: str
    kind: str
    file: str
    line: int
    result_type: str
    reason: str


@dataclass(frozen=True)
class AuditWarning:
    declaration: str
    kind: str
    file: str
    line: int
    final_result_type: str
    hypothesis_surface: str
    reason: str


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def strip_comments_and_strings(text: str) -> str:
    """Remove Lean comments and string contents while preserving line layout."""
    out: list[str] = []
    i = 0
    block_depth = 0
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    out.append(" ")
                    if i + 1 < len(text):
                        out.append("\n" if text[i + 1] == "\n" else " ")
                    i += 2
                    continue
                if text[i] == '"':
                    out.append(" ")
                    i += 1
                    break
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def lean_files(root: Path) -> list[Path]:
    return sorted(path for path in root.rglob("*.lean") if path.is_file())


def module_name(path: Path, bedc_root: Path) -> str:
    try:
        rel = path.relative_to(bedc_root)
    except ValueError:
        return path.stem
    parts = ("BEDC",) + rel.with_suffix("").parts
    return ".".join(parts)


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


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


def declaration_namespace(module: str, namespace_stack: list[str]) -> str:
    return namespace_stack[-1] if namespace_stack else module


def qualified_name(name: str, namespace: str) -> str:
    if name.startswith("BEDC."):
        return name
    return f"{namespace}.{name}" if namespace else name


def declaration_block(lines: list[str], start_idx: int) -> str:
    block_lines = [lines[start_idx]]
    j = start_idx + 1
    while j < len(lines):
        line = lines[j]
        if (
            line.strip()
            and not line.startswith((" ", "\t", "|", "·"))
            and not re.match(r"^\s*(where|deriving)\b", line)
        ):
            break
        block_lines.append(line)
        j += 1
    return "\n".join(block_lines)


def declaration_header(block: str) -> str:
    marker_positions = [pos for pos in (block.find(":="), block.find(" where")) if pos >= 0]
    if not marker_positions:
        return block
    return block[: min(marker_positions)]


def normalize_type(text: str) -> str:
    compact = " ".join(text.strip().split())
    while compact.startswith("(") and compact.endswith(")") and encloses_whole(compact):
        compact = compact[1:-1].strip()
    return compact


def encloses_whole(text: str) -> bool:
    depth = 0
    pairs = {"(": ")"}
    for idx, ch in enumerate(text):
        if ch in pairs:
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and idx != len(text) - 1:
                return False
        if depth < 0:
            return False
    return depth == 0


def header_prefix_and_result_type(header: str) -> tuple[str, str | None]:
    if ":" not in header:
        return header, None

    prefix = header
    for delimiter in (":=", " where", "\nwhere"):
        if delimiter in prefix:
            prefix = prefix.split(delimiter, 1)[0]

    depth = 0
    result_colon: int | None = None
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    for idx, ch in enumerate(prefix):
        if ch in pairs:
            depth += 1
        elif ch in closing and depth > 0:
            depth -= 1
        elif ch == ":" and depth == 0:
            result_colon = idx

    if result_colon is None:
        return prefix, None
    return prefix[:result_colon], normalize_type(prefix[result_colon + 1 :])


def strip_decl_head(prefix: str) -> str:
    lines = prefix.splitlines()
    if not lines:
        return ""
    match = DECL_RE.match(lines[0])
    if not match:
        return prefix
    tail = lines[0][match.end() :]
    if len(lines) == 1:
        return tail
    return "\n".join([tail, *lines[1:]])


def has_binder_between_name_and_colon(prefix: str) -> bool:
    return re.search(r"[\(\[\{]", strip_decl_head(prefix)) is not None


def split_top_level_arrows(text: str) -> list[str]:
    pieces: list[str] = []
    start = 0
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing = set(pairs.values())
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in pairs:
            depth += 1
            i += 1
            continue
        if ch in closing and depth > 0:
            depth -= 1
            i += 1
            continue
        if depth == 0 and text.startswith("->", i):
            pieces.append(normalize_type(text[start:i]))
            i += 2
            start = i
            continue
        if depth == 0 and ch == "→":
            pieces.append(normalize_type(text[start:i]))
            i += 1
            start = i
            continue
        i += 1
    pieces.append(normalize_type(text[start:]))
    return pieces


def extract_binder_groups(text: str) -> list[str]:
    groups: list[str] = []
    pairs = {"(": ")", "{": "}", "[": "]"}
    closing_to_open = {")": "(", "}": "{", "]": "["}
    stack: list[str] = []
    start: int | None = None
    for idx, ch in enumerate(text):
        if ch in pairs:
            if not stack:
                start = idx
            stack.append(ch)
            continue
        if ch in closing_to_open and stack:
            expected = closing_to_open[ch]
            if stack[-1] == expected:
                stack.pop()
                if not stack and start is not None:
                    groups.append(text[start : idx + 1])
                    start = None
    return groups


def hypothesis_surfaces(prefix: str, result_type: str) -> list[str]:
    surfaces: list[str] = []
    for group in extract_binder_groups(strip_decl_head(prefix)):
        surfaces.append(normalize_type(group.strip("(){}[]")))
    arrow_parts = split_top_level_arrows(result_type)
    if len(arrow_parts) > 1:
        surfaces.extend(arrow_parts[:-1])
    return [surface for surface in surfaces if surface]


def final_result_type(result_type: str) -> str:
    arrow_parts = split_top_level_arrows(result_type)
    return arrow_parts[-1] if arrow_parts else result_type


def scan_declarations(bedc_root: Path) -> list[LeanDeclaration]:
    declarations: list[LeanDeclaration] = []
    bedc_root = bedc_root.resolve()
    for path in lean_files(bedc_root):
        text = strip_comments_and_strings(read_text(path))
        lines = text.splitlines()
        module = module_name(path, bedc_root)
        namespace_stack: list[str] = []
        for idx, line in enumerate(lines):
            update_namespace_stack(line, namespace_stack)
            match = DECL_RE.match(line)
            if not match:
                continue
            kind = match.group("kind")
            if kind not in CHECKED_KINDS:
                continue
            name = (match.group("name") or f"<anonymous_{kind}_{idx + 1}>").strip()
            namespace = declaration_namespace(module, namespace_stack)
            header = declaration_header(declaration_block(lines, idx))
            prefix, result_type = header_prefix_and_result_type(header)
            declarations.append(
                LeanDeclaration(
                    kind=kind,
                    name=name,
                    qualified_name=qualified_name(name, namespace),
                    file=display_path(path),
                    line=idx + 1,
                    header=header,
                    result_type=result_type,
                    prefix=prefix,
                )
            )
    return declarations


def core_violations(declarations: Iterable[LeanDeclaration]) -> list[AuditFinding]:
    violations: list[AuditFinding] = []
    for decl in declarations:
        if decl.result_type is None:
            continue
        result_type = normalize_type(decl.result_type)
        if not CORE_TARGET_RE.fullmatch(result_type):
            continue
        if has_binder_between_name_and_colon(decl.prefix):
            continue
        violations.append(
            AuditFinding(
                declaration=decl.qualified_name,
                kind=decl.kind,
                file=decl.file,
                line=decl.line,
                result_type=result_type,
                reason=(
                    "unconditional declaration inhabits RH core target without "
                    "a binder before the result colon"
                ),
            )
        )
    return violations


def toy_route_warnings(declarations: Iterable[LeanDeclaration]) -> list[AuditWarning]:
    warnings: list[AuditWarning] = []
    for decl in declarations:
        if decl.result_type is None:
            continue
        result_type = normalize_type(decl.result_type)
        final_type = final_result_type(result_type)
        if not CONSTRUCTIVE_RH_RE.fullmatch(final_type):
            continue
        hypotheses = hypothesis_surfaces(decl.prefix, result_type)
        if not hypotheses:
            continue
        hypothesis_text = " ; ".join(hypotheses)
        if ANCHOR_RE.search(hypothesis_text):
            continue
        if any(TOY_ROUTE_RE.search(surface) for surface in hypotheses):
            warnings.append(
                AuditWarning(
                    declaration=decl.qualified_name,
                    kind=decl.kind,
                    file=decl.file,
                    line=decl.line,
                    final_result_type=final_type,
                    hypothesis_surface=hypothesis_text,
                    reason=(
                        "ConstructiveRH route mentions an inhabited toy surface "
                        "and has no CRPC or AnalyticGombocRHHandoff anchor"
                    ),
                )
            )
    return warnings


def payload(args: argparse.Namespace) -> dict[str, object]:
    declarations = scan_declarations(Path(args.bedc_root))
    violations = core_violations(declarations)
    warnings = toy_route_warnings(declarations)
    exit_code = 0 if not violations else 1
    return {
        "token": TOKEN,
        "script": str(Path(__file__).relative_to(REPO_ROOT)),
        "repo_root": str(REPO_ROOT),
        "bedc_root": str(Path(args.bedc_root).resolve()),
        "scope": (
            "No theorem/lemma/def/instance/abbrev may unconditionally inhabit "
            "ConstructiveRH, CausalReflectionPositiveCone, or their Nonempty forms."
        ),
        "checked_kinds": sorted(CHECKED_KINDS),
        "scanned_files": len(lean_files(Path(args.bedc_root))),
        "declarations_checked": len(declarations),
        "passed": exit_code == 0,
        "exit_code": exit_code,
        "violations": [asdict(record) for record in violations],
        "warnings": [asdict(record) for record in warnings],
    }


def emit_text(data: dict[str, object]) -> None:
    status = "PASS" if data["passed"] else "FAIL"
    print(
        f"{TOKEN} {status}: declarations={data['declarations_checked']} "
        f"violations={len(data['violations'])} warnings={len(data['warnings'])}"
    )
    for record in data["violations"]:
        print(
            "VIOLATION "
            f"{record['file']}:{record['line']} {record['declaration']} "
            f"result={record['result_type']} reason={record['reason']}"
        )
    for record in data["warnings"]:
        print(
            "WARNING "
            f"{record['file']}:{record['line']} {record['declaration']} "
            f"hypotheses={record['hypothesis_surface']} reason={record['reason']}"
        )


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Audit BEDC Lean sources for fake unconditional RH inhabitants"
    )
    p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    p.add_argument(
        "--bedc-root",
        default=str(BEDC_ROOT),
        help="Root containing BEDC Lean sources, for tests and local audits",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    data = payload(args)
    if args.json:
        print(json.dumps(data, indent=2, sort_keys=True))
    else:
        emit_text(data)
    return int(data["exit_code"])


if __name__ == "__main__":
    sys.exit(main())

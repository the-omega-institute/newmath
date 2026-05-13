#!/usr/bin/env python3
"""从论文 Lean 标记生成 BEDC.Manifest.Entries 候选项。"""

from __future__ import annotations

import argparse
import datetime as _datetime
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


MARKER_PATTERNS = {
    "checked": re.compile(r"\\leanchecked\{([^}]+)\}"),
    "variant": re.compile(r"\\leanvariant\{([^}]+)\}"),
    "target": re.compile(r"\\leantarget\{([^}]+)\}"),
}

LABEL_PATTERN = re.compile(r"\\label\{([^}]+)\}")
LEAN_DECL_PATTERN = re.compile(
    r"^\s*(?:theorem|def|lemma|abbrev|instance)\s+([A-Za-z0-9_'.]+)"
)


@dataclass(frozen=True)
class Marker:
    kind: str
    lean_name: str
    paper_label: str
    path: Path
    line: int
    column: int


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate Lean ClaimEntry stubs from paper-side Lean markers."
    )
    parser.add_argument("--paper-dir", default="papers/bedc/parts")
    parser.add_argument("--manifest-json", default="lean4/scripts/bedc_manifest.json")
    parser.add_argument(
        "--kind",
        choices=("checked", "variant", "target", "all"),
        default="checked",
        help="marker kind to scan",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="print a coverage report instead of emitting stubs",
    )
    parser.add_argument("--output", help="write generated stubs to this path")
    parser.add_argument(
        "--limit",
        type=int,
        default=0,
        help="maximum number of parsed markers to consider; 0 means no limit",
    )
    return parser.parse_args(argv)


def marker_kinds(kind: str) -> list[str]:
    if kind == "all":
        return ["checked", "variant", "target"]
    return [kind]


def normalize_lean_name(raw_name: str) -> str:
    return "".join(raw_name.strip().replace(r"\_", "_").split())


def line_col(source: str, offset: int) -> tuple[int, int]:
    line = source.count("\n", 0, offset) + 1
    line_start = source.rfind("\n", 0, offset)
    column = offset + 1 if line_start < 0 else offset - line_start
    return line, column


def nearest_preceding_label(source: str, offset: int) -> str:
    label = "TBD"
    for match in LABEL_PATTERN.finditer(source, 0, offset):
        label = match.group(1).strip() or "TBD"
    return label


def iter_tex_files(paper_dir: Path) -> Iterable[Path]:
    return sorted(path for path in paper_dir.glob("**/*.tex") if path.is_file())


def scan_markers(paper_dir: Path, kind: str, limit: int) -> list[Marker]:
    kinds = marker_kinds(kind)
    markers: list[Marker] = []
    for path in iter_tex_files(paper_dir):
        source = path.read_text(encoding="utf-8")
        file_matches: list[tuple[int, str, re.Match[str]]] = []
        for marker_kind in kinds:
            pattern = MARKER_PATTERNS[marker_kind]
            file_matches.extend(
                (match.start(), marker_kind, match) for match in pattern.finditer(source)
            )
        for offset, marker_kind, match in sorted(file_matches, key=lambda item: item[0]):
            line, column = line_col(source, offset)
            markers.append(
                Marker(
                    kind=marker_kind,
                    lean_name=normalize_lean_name(match.group(1)),
                    paper_label=nearest_preceding_label(source, offset),
                    path=path,
                    line=line,
                    column=column,
                )
            )
            if limit > 0 and len(markers) >= limit:
                return markers
    return markers


def extract_manifest_names(value: object) -> set[str]:
    names: set[str] = set()
    if isinstance(value, str):
        if value.startswith("BEDC."):
            names.add(value)
        return names
    if isinstance(value, list):
        for item in value:
            names.update(extract_manifest_names(item))
        return names
    if isinstance(value, dict):
        for key in ("lean_name", "leanName", "name", "decl_name", "declName"):
            item = value.get(key)
            if isinstance(item, str) and item.startswith("BEDC."):
                names.add(item)
        if not names:
            for item in value.values():
                names.update(extract_manifest_names(item))
        return names
    return names


def load_manifest_names(path: Path) -> set[str]:
    try:
        with path.open(encoding="utf-8") as handle:
            data = json.load(handle)
    except (OSError, json.JSONDecodeError):
        return set()
    return extract_manifest_names(data)


def namespace_for_file(path: Path) -> str:
    namespace = ""
    try:
        with path.open(encoding="utf-8") as handle:
            for line in handle:
                stripped = line.strip()
                if stripped.startswith("namespace "):
                    namespace = stripped.split(None, 1)[1].strip()
    except OSError:
        return ""
    return namespace


def scan_lean_decl_names(lean_root: Path) -> set[str]:
    names: set[str] = set()
    if not lean_root.exists():
        return names
    for path in sorted(lean_root.glob("**/*.lean")):
        namespace = namespace_for_file(path)
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for line in lines:
            match = LEAN_DECL_PATTERN.match(line)
            if not match:
                continue
            decl = match.group(1)
            if decl.startswith("BEDC."):
                names.add(decl)
            elif namespace:
                names.add(namespace + "." + decl)
            else:
                names.add(decl)
    return names


def declaration_names(manifest_json: Path) -> set[str]:
    names = load_manifest_names(manifest_json)
    repo_root = manifest_json.resolve().parent.parent.parent
    names.update(scan_lean_decl_names(repo_root / "lean4" / "BEDC"))
    return names


def render_stub(marker: Marker) -> str:
    return (
        f"⟨\"{marker.paper_label}\", \"{marker.lean_name}\", _, "
        f"{marker.lean_name}⟩,"
    )


def render_stubs(markers: list[Marker], known_names: set[str]) -> str:
    missing_count = sum(1 for marker in markers if marker.lean_name not in known_names)
    resolved_count = len(markers) - missing_count
    timestamp = _datetime.datetime.now(_datetime.timezone.utc).isoformat()
    lines = [
        "-- Auto-generated ClaimEntry stubs from papers/bedc/parts/**/*.tex \\leanchecked markers.",
        "-- HUMAN REVIEW REQUIRED: paste curated subset into BEDC.Manifest.Entries.",
        f"-- Generated: {timestamp}",
        f"-- Total markers: {len(markers)}; resolved: {resolved_count}; missing: {missing_count}",
        "",
    ]
    lines.extend(render_stub(marker) for marker in markers)
    return "\n".join(lines) + "\n"


def render_check_report(markers: list[Marker], known_names: set[str]) -> str:
    missing = [marker for marker in markers if marker.lean_name not in known_names]
    resolved_count = len(markers) - len(missing)
    lines = [
        "manifest-codegen check report",
        f"  total_markers: {len(markers)}",
        f"  resolved: {resolved_count} (in bedc_manifest.json)",
        f"  missing: {len(missing)}",
        "",
        "  -- Missing names (first 20):",
    ]
    for marker in missing[:20]:
        lines.append(f"  {marker.lean_name}  ({marker.path}:{marker.line})")
    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    paper_dir = Path(args.paper_dir)
    manifest_json = Path(args.manifest_json)
    markers = scan_markers(paper_dir, args.kind, args.limit)
    known_names = declaration_names(manifest_json)

    if args.check:
        report = render_check_report(markers, known_names)
        sys.stdout.write(report)
        return 1 if any(marker.lean_name not in known_names for marker in markers) else 0

    output = render_stubs(markers, known_names)
    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
    else:
        sys.stdout.write(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

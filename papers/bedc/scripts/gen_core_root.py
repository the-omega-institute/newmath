#!/usr/bin/env python3
"""Write additive BEDC PDF roots from the monolithic main.tex structure."""

from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import NamedTuple


ROOT = Path(__file__).parent.parent
MAIN = ROOT / "main.tex"
CORE = ROOT / "main_core.tex"
DERIVED_DIR = ROOT / "derived"
DERIVED_SLUG = "concrete_instances"
DERIVED_ROOT = DERIVED_DIR / f"{DERIVED_SLUG}.tex"
DERIVED_MANIFEST_PREFIX = f"{DERIVED_SLUG}_inputs"
DERIVED_PARTS = {"Concrete Instances", "Concrete Hardening"}
MANIFEST_CHUNK_SIZE = 500
MAX_TEX_LINES = 800

PART_RE = re.compile(r"^\\part\{([^{}]+)\}\s*$")
INPUT_RE = re.compile(r"\\input\{")


class PartBlock(NamedTuple):
    title: str
    lines: list[str]


class MainShape(NamedTuple):
    prefix: list[str]
    parts: list[PartBlock]
    suffix: list[str]


def read_main_shape() -> MainShape:
    lines = MAIN.read_text(encoding="utf-8").splitlines()
    prefix: list[str] = []
    parts: list[PartBlock] = []
    suffix: list[str] = []
    current_title: str | None = None
    current_lines: list[str] = []
    in_suffix = False

    for line in lines:
        if in_suffix:
            suffix.append(line)
            continue

        if line.strip() == r"\end{document}":
            if current_title is not None:
                parts.append(PartBlock(current_title, current_lines))
                current_title = None
                current_lines = []
            suffix.append(line)
            in_suffix = True
            continue

        match = PART_RE.match(line.strip())
        if match:
            if current_title is not None:
                parts.append(PartBlock(current_title, current_lines))
            current_title = match.group(1)
            current_lines = [line]
            continue

        if current_title is None:
            prefix.append(line)
        else:
            current_lines.append(line)

    if current_title is not None:
        parts.append(PartBlock(current_title, current_lines))

    return MainShape(prefix=prefix, parts=parts, suffix=suffix)


def banner() -> list[str]:
    return [
        "% This root is written by scripts/gen_core_root.py.",
        "% Edit main.tex or the generator, then run the generator.",
    ]


def core_lines(shape: MainShape) -> list[str]:
    lines = banner()
    lines.extend(shape.prefix)
    for part in shape.parts:
        if part.title not in DERIVED_PARTS:
            lines.extend(part.lines)
    lines.extend(shape.suffix)
    return lines


def derived_header() -> list[str]:
    return [
        *banner(),
        r"\documentclass[11pt,oneside,openany]{book}",
        r"\usepackage{xr-hyper}",
        r"\input{preamble.tex}",
        r"\makeatletter",
        r"\IfFileExists{main_core.aux}{\externaldocument[core-]{main_core}}{%",
        r"  \IfFileExists{main.aux}{\externaldocument[main-]{main}}{}%",
        r"}",
        r"\providecommand{\BEDCExternalRef}[1]{%",
        r"  \@ifundefined{r@core-#1}{%",
        r"    \@ifundefined{r@main-#1}{\texttt{#1}}{\autoref{main-#1}}%",
        r"  }{\autoref{core-#1}}%",
        r"}",
        r"\makeatother",
        r"\begin{document}",
        r"\frontmatter",
        r"\tableofcontents",
        r"\mainmatter",
    ]


def manifest_blocks(shape: MainShape) -> list[list[str]]:
    lines: list[str] = []
    for part in shape.parts:
        if part.title in DERIVED_PARTS:
            lines.extend(part.lines)
    return [
        lines[index : index + MANIFEST_CHUNK_SIZE]
        for index in range(0, len(lines), MANIFEST_CHUNK_SIZE)
    ]


def manifest_paths(blocks: list[list[str]]) -> list[Path]:
    width = max(2, len(str(len(blocks))))
    return [
        DERIVED_DIR / f"{DERIVED_MANIFEST_PREFIX}_{index:0{width}d}.tex"
        for index in range(1, len(blocks) + 1)
    ]


def derived_lines(paths: list[Path]) -> list[str]:
    lines = derived_header()
    for path in paths:
        lines.append(rf"\input{{{path.relative_to(ROOT).as_posix()}}}")
    lines.append(r"\end{document}")
    return lines


def validate(path: Path, lines: list[str]) -> None:
    text = "\n".join(lines)
    if not text.strip():
        raise SystemExit(f"{path.relative_to(ROOT)} is empty")
    if not INPUT_RE.search(text):
        raise SystemExit(f"{path.relative_to(ROOT)} has no input line")
    if len(lines) > MAX_TEX_LINES:
        raise SystemExit(
            f"{path.relative_to(ROOT)} has {len(lines)} lines, cap {MAX_TEX_LINES}"
        )


def write_text(path: Path, lines: list[str], *, dry_run: bool) -> None:
    text = "\n".join(lines).rstrip() + "\n"
    if dry_run:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def clear_stale_manifests(*, dry_run: bool) -> None:
    if dry_run or not DERIVED_DIR.is_dir():
        return
    for path in DERIVED_DIR.glob(f"{DERIVED_MANIFEST_PREFIX}_*.tex"):
        path.unlink()


def count_inputs(lines: list[str]) -> int:
    return sum(1 for line in lines if INPUT_RE.search(line))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Write main_core.tex and derived/concrete_instances.tex."
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate generated text without writing files",
    )
    args = parser.parse_args()

    shape = read_main_shape()
    selected = {part.title for part in shape.parts if part.title in DERIVED_PARTS}
    missing = DERIVED_PARTS - selected
    if missing:
        raise SystemExit(f"missing derived part(s): {', '.join(sorted(missing))}")

    core = core_lines(shape)
    blocks = manifest_blocks(shape)
    paths = manifest_paths(blocks)
    derived = derived_lines(paths)
    manifests = list(zip(paths, blocks, strict=True))

    validate(CORE, core)
    validate(DERIVED_ROOT, derived)
    for path, lines in manifests:
        validate(path, [*banner(), *lines])

    clear_stale_manifests(dry_run=args.check)
    write_text(CORE, core, dry_run=args.check)
    write_text(DERIVED_ROOT, derived, dry_run=args.check)
    for path, lines in manifests:
        write_text(path, [*banner(), *lines], dry_run=args.check)

    action = "checked" if args.check else "wrote"
    print(
        f"{action} {CORE.relative_to(ROOT)} "
        f"parts={sum(1 for p in shape.parts if p.title not in DERIVED_PARTS)} "
        f"inputs={count_inputs(core)}"
    )
    print(
        f"{action} {DERIVED_ROOT.relative_to(ROOT)} "
        f"parts={len(selected)} inputs={count_inputs(derived)}"
    )
    for path, lines in manifests:
        print(
            f"{action} {path.relative_to(ROOT)} "
            f"inputs={count_inputs(lines)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

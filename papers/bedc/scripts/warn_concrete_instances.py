#!/usr/bin/env python3
"""Warning gate for parts/concrete_instances/ conventions.

Reports drift from established conventions as WARN (exit 0 by default).
Designed to plug into `make precheck` without blocking the PDF build, while
giving a single dashboard to drive incremental cleanup.

Checks (IDs match the analysis report):
  A  \\closureat{X}{L}: L must be in {seed,obligation,scoped,public,bridged,mature}Str
  C  Every \\begin{closurestatus} must have all 5 required fields
     (theoryclosure / formalstatus / scopeclosed / notclaimed / upgradepath)
  D  Content namecert file (with \\chapter) must reach a closurestatus block
     directly or via \\input chain
  E  Hub namecert file (no \\chapter, only \\input lines) must not contain
     theorem-like environments or closurestatus blocks
  F  Content namecert chapter must \\label{ch:concrete-instances-<slug>-namecert}
  G  If \\origin{...} appears in a content namecert chapter, it must be human|ai
  H  \\bridgestatus value must be in {none, paperBridge, bridgeChecked}
  I  every tex basename is lowercase snake_case with optional NN_/NNa_ prefix
     or leading _ for aggregate index files
  J  every concrete_instances/<region>/ subdir name is lowercase + alphanum
  K  every region with 2+ top-level files should consolidate to one hub +
     parts/concrete_instances/<slug>/ siblings
  L  BEDC \\FooUp chapter macros must not appear outside math mode
  M  every \\input{path} under parts/frontmatter/appendices must resolve
  N  content namecert chapters must not duplicate chapter labels
  O  each region \\<X>Up has at most one \\begin{closurestatus} block site
  P  each (region, level) pair has at most one \\closureat site

Modes:
  default       human-readable WARN to stderr, exit 0
  --json        machine-readable JSON to stdout, exit 0
  --check ID    run a single check
  --strict      exit 1 on any violation (for future hard-gate promotion)
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

PAPER_DIR = Path(__file__).resolve().parents[1]
CONCRETE_DIR = PAPER_DIR / "parts" / "concrete_instances"
SCAN_ROOTS = [PAPER_DIR / "parts", PAPER_DIR / "frontmatter", PAPER_DIR / "appendices"]

CLOSUREAT_RE = re.compile(r"\\closureat\{([^}]+)\}\{([^}]+)\}")
VALID_CLOSUREAT_LEVELS = {
    "seedStr", "obligationStr", "scopedStr",
    "publicStr", "bridgedStr", "matureStr",
}

CLOSURE_BEGIN_RE = re.compile(r"\\begin\{closurestatus\}\{[^}]*\}")
CLOSURE_END_RE = re.compile(r"\\end\{closurestatus\}")
REQUIRED_CLOSURE_FIELDS = (
    "theoryclosure", "formalstatus", "scopeclosed", "notclaimed", "upgradepath",
)
FIELD_RE = re.compile(r"\\([a-zA-Z]+)\{")

INPUT_RE = re.compile(r"\\input\{([^}]+)\}")
CHAPTER_RE = re.compile(r"^\\chapter\b", re.MULTILINE)
NAMECERT_CONTENT_GLOB = "*_namecert_construction.tex"

HUB_FORBIDDEN_ENVS = (
    "theorem", "definition", "lemma", "corollary",
    "proposition", "proof", "closurestatus",
)
HUB_FORBIDDEN_RE = re.compile(r"\\begin\{(" + "|".join(HUB_FORBIDDEN_ENVS) + r")\*?\}")

LABEL_CH_RE = re.compile(r"\\label\{ch:concrete-instances-[a-z0-9][a-z0-9-]*\}")
ORIGIN_RE = re.compile(r"\\origin\{([^}]+)\}")
VALID_ORIGINS = {"human", "ai", "ai-composite"}

BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{([^}]+)\}")
VALID_BRIDGESTATUS = {"none", "paperBridge", "bridgeChecked"}

# Check I: any .tex basename under parts/frontmatter/appendices must be
# lowercase snake_case. Two prefix forms recognized:
#   NN_ or NNa_  -- numbered chapter or chunk file
#   _            -- aggregated index / sub-hub file (e.g. _index_files.tex)
TEX_BASENAME_RE = re.compile(r"^_?(?:[0-9]+[a-z]?_)?[a-z][a-z0-9_]*\.tex$")

# Check J: concrete_instances/<region>/ subdirectory names must be lowercase
# alphanumeric, optional internal underscores.
REGION_DIR_RE = re.compile(r"^[a-z][a-z0-9_]*$")

# Check K: regions with 2+ top-level files should be consolidated into a hub
# at top + sibling files in parts/concrete_instances/<slug>/. Top-level
# basename is <NN>_<slug>_<rest>.tex (NN may carry an [a-z] suffix).
REGION_PREFIX_RE = re.compile(r"^([0-9]+[a-z]?_[a-z][a-z0-9]*)_")

UP_MACRO_RE = re.compile(r"\\[A-Z][a-zA-Z]+Up\b")
UP_MACRO_DEFINITION_RE = re.compile(
    r"^\s*\\(?:re)?newcommand\*?\{\\[A-Z][a-zA-Z]+Up\}"
    r"|^\s*\\providecommand\*?\{\\[A-Z][a-zA-Z]+Up\}"
    r"|^\s*\\DeclareRobustCommand\*?\{\\[A-Z][a-zA-Z]+Up\}"
    r"|^\s*\\def\\[A-Z][a-zA-Z]+Up\b"
)
BEGIN_END_ENV_RE = re.compile(r"\\(begin|end)\{([^}]+)\*?\}")
MATH_ENV_NAMES = {
    "math", "displaymath", "equation", "equation*", "align", "align*",
    "aligned", "alignedat", "gather", "gather*", "gathered",
    "multline", "multline*", "split", "array", "matrix", "pmatrix",
    "bmatrix", "Bmatrix", "vmatrix", "Vmatrix", "cases",
}
TEXT_ARG_COMMANDS = {
    "chapter", "section", "subsection", "subsubsection", "paragraph",
    "textbf", "textit", "emph", "falsifiablePrediction",
    "independenceWitness", "closureat",
}
TEXT_ARG_COMMAND_RE = re.compile(
    r"\\(" + "|".join(sorted(TEXT_ARG_COMMANDS, key=len, reverse=True)) + r")\b"
)


def read_text(p: Path) -> str:
    try:
        return p.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


VERBATIM_RE = re.compile(
    r"\\begin\{(verbatim|lstlisting|minted)\*?\}.*?\\end\{\1\*?\}",
    re.DOTALL,
)


def strip_verbatim_preserve_lines(text: str) -> str:
    """Replace verbatim/lstlisting/minted bodies with blank lines so regex
    scans skip example snippets while line numbers stay aligned."""
    def _blank(m: re.Match[str]) -> str:
        return "\n" * m.group(0).count("\n")
    return VERBATIM_RE.sub(_blank, text)


def iter_part_tex() -> list[Path]:
    files: list[Path] = []
    for root in SCAN_ROOTS:
        if root.exists():
            files.extend(sorted(root.rglob("*.tex")))
    return files


def resolve_input(target: str) -> Path | None:
    target = target.strip()
    if not target.endswith(".tex"):
        target = target + ".tex"
    candidate = (PAPER_DIR / target)
    if candidate.exists():
        return candidate.resolve()
    return None


def collect_reachable(root: Path) -> set[Path]:
    seen: set[Path] = set()
    stack = [root.resolve()]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        for m in INPUT_RE.finditer(read_text(cur)):
            child = resolve_input(m.group(1))
            if child is not None:
                stack.append(child)
    return seen


def closurestatus_blocks(text: str) -> list[tuple[int, str]]:
    out: list[tuple[int, str]] = []
    for m in CLOSURE_BEGIN_RE.finditer(text):
        start_line = text.count("\n", 0, m.start()) + 1
        tail = text[m.end():]
        em = CLOSURE_END_RE.search(tail)
        body = tail[:em.start()] if em else ""
        out.append((start_line, body))
    return out


def _line_text_without_comment(line: str) -> str:
    escaped = False
    for i, ch in enumerate(line):
        if ch == "%" and not escaped:
            return line[:i]
        escaped = ch == "\\" and not escaped
        if ch != "\\":
            escaped = False
    return line


def _scan_math_segments(line: str, in_display: bool, math_env_depth: int) -> tuple[list[tuple[int, int, bool]], bool, int]:
    """Return contiguous line segments with their starting math-mode state."""
    segments: list[tuple[int, int, bool]] = []
    i = 0
    seg_start = 0
    in_inline = False

    def in_math() -> bool:
        return in_inline or in_display or math_env_depth > 0

    while i < len(line):
        if line.startswith(r"\(", i) or line.startswith(r"\[", i):
            segments.append((seg_start, i, in_math()))
            if line.startswith(r"\[", i):
                in_display = True
            else:
                in_inline = True
            i += 2
            seg_start = i
            continue
        if line.startswith(r"\)", i) or line.startswith(r"\]", i):
            segments.append((seg_start, i, in_math()))
            if line.startswith(r"\]", i):
                in_display = False
            else:
                in_inline = False
            i += 2
            seg_start = i
            continue

        env = BEGIN_END_ENV_RE.match(line, i)
        if env:
            segments.append((seg_start, i, in_math()))
            kind, name = env.group(1), env.group(2)
            if name in MATH_ENV_NAMES:
                if kind == "begin":
                    math_env_depth += 1
                else:
                    math_env_depth = max(0, math_env_depth - 1)
            i = env.end()
            seg_start = i
            continue

        if line.startswith("$$", i):
            segments.append((seg_start, i, in_math()))
            in_display = not in_display
            i += 2
            seg_start = i
            continue

        if line[i] == "$" and (i == 0 or line[i - 1] != "\\"):
            segments.append((seg_start, i, in_math()))
            in_inline = not in_inline
            i += 1
            seg_start = i
            continue

        i += 1

    segments.append((seg_start, len(line), in_math()))
    return segments, in_display, math_env_depth


def _text_mode_up_macro_hits(line: str, in_display: bool, math_env_depth: int) -> tuple[list[tuple[str, int]], bool, int]:
    code = _line_text_without_comment(line)
    hits: list[tuple[str, int]] = []
    segments, in_display, math_env_depth = _scan_math_segments(code, in_display, math_env_depth)
    for start, end, is_math in segments:
        if is_math:
            continue
        for m in UP_MACRO_RE.finditer(code, start, end):
            hits.append((m.group(0), m.start() + 1))
    return hits, in_display, math_env_depth


def _brace_argument_spans(line: str, open_brace: int) -> tuple[int, int] | None:
    if open_brace >= len(line) or line[open_brace] != "{":
        return None
    depth = 0
    i = open_brace
    while i < len(line):
        ch = line[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return open_brace + 1, i
        i += 1
    return None


def _text_command_argument_up_hits(line: str) -> list[tuple[str, int, str]]:
    code = _line_text_without_comment(line)
    hits: list[tuple[str, int, str]] = []
    for cmd in TEXT_ARG_COMMAND_RE.finditer(code):
        pos = cmd.end()
        while pos < len(code) and code[pos].isspace():
            pos += 1
        while pos < len(code) and code[pos] == "[":
            close = code.find("]", pos + 1)
            if close == -1:
                break
            pos = close + 1
            while pos < len(code) and code[pos].isspace():
                pos += 1
        while pos < len(code) and code[pos] == "{":
            span = _brace_argument_spans(code, pos)
            if span is None:
                break
            start, end = span
            arg = code[start:end]
            arg_hits, _, _ = _text_mode_up_macro_hits(arg, False, 0)
            for macro, col in arg_hits:
                hits.append((macro, start + col, cmd.group(1)))
            pos = end + 1
            while pos < len(code) and code[pos].isspace():
                pos += 1
    return hits


def check_a_closureat_enum() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        text = strip_verbatim_preserve_lines(read_text(tex))
        for i, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for m in CLOSUREAT_RE.finditer(line):
                level = m.group(2)
                if level not in VALID_CLOSUREAT_LEVELS:
                    out.append({
                        "check": "A",
                        "file": str(rel),
                        "line": i,
                        "msg": f"\\closureat level '{level}' not in {sorted(VALID_CLOSUREAT_LEVELS)}",
                    })
    return out


def check_c_closurestatus_fields() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        text = strip_verbatim_preserve_lines(read_text(tex))
        for start_line, body in closurestatus_blocks(text):
            fields = {m.group(1) for m in FIELD_RE.finditer(body)}
            missing = [f for f in REQUIRED_CLOSURE_FIELDS if f not in fields]
            for f in missing:
                out.append({
                    "check": "C",
                    "file": str(rel),
                    "line": start_line,
                    "msg": f"closurestatus block missing \\{f}",
                })
    return out


CHAPTER_REGION_RE = re.compile(r"\\chapter\{[^}]*?\\([A-Z][A-Za-z]+Up)\b")
CLOSURE_BEGIN_REGION_RE = re.compile(r"\\begin\{closurestatus\}\{\\?([A-Z][A-Za-z]*Up)\}")


def _regions_with_closurestatus_anywhere() -> set[str]:
    """Scan all parts/ tex files for \\begin{closurestatus}{\\<X>Up} blocks and
    return the set of region macros that have at least one block somewhere."""
    out: set[str] = set()
    for tex in iter_part_tex():
        text = read_text(tex)
        for m in CLOSURE_BEGIN_REGION_RE.finditer(text):
            out.add(m.group(1))
    return out


def check_d_content_reaches_closurestatus() -> list[dict]:
    """Each chapter binding \\<X>Up (via \\chapter{... \\<X>Up ...}) is OK iff
    some closurestatus block for \\<X>Up exists somewhere in concrete_instances/.
    Per-region rule (not per-file): one canonical chapter per region owns the
    closurestatus; sibling chapters covering the same region don't need their
    own block. Combine with check O for region uniqueness."""
    out: list[dict] = []
    covered_regions = _regions_with_closurestatus_anywhere()
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        m = CHAPTER_REGION_RE.search(text)
        if not m:
            # Chapter without an Up-macro region binding — skip (rare)
            continue
        region = m.group(1)
        if region in covered_regions:
            continue
        # No closurestatus anywhere for this region's macro — also check
        # \input chain in case the chapter forwards to an off-region block
        reachable = collect_reachable(tex)
        if any(CLOSURE_BEGIN_RE.search(read_text(f)) for f in reachable):
            continue
        out.append({
            "check": "D",
            "file": str(rel),
            "line": 1,
            "msg": (
                f"content namecert chapter binds region \\{region} but no "
                f"\\begin{{closurestatus}}{{\\{region}}} block exists anywhere"
            ),
        })
    return out


def check_e_hub_purity() -> list[dict]:
    out: list[dict] = []
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        raw = read_text(tex)
        if CHAPTER_RE.search(raw):
            continue
        text = strip_verbatim_preserve_lines(raw)
        for i, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            m = HUB_FORBIDDEN_RE.search(line)
            if m:
                out.append({
                    "check": "E",
                    "file": str(rel),
                    "line": i,
                    "msg": f"hub file (no \\chapter) contains forbidden environment \\begin{{{m.group(1)}}}",
                })
    return out


def check_f_label_convention() -> list[dict]:
    out: list[dict] = []
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        if not LABEL_CH_RE.search(text):
            out.append({
                "check": "F",
                "file": str(rel),
                "line": 1,
                "msg": "content namecert chapter missing any \\label{ch:concrete-instances-<slug>...} (must be lowercase)",
            })
    return out


def check_g_origin_value() -> list[dict]:
    out: list[dict] = []
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        stripped = strip_verbatim_preserve_lines(text)
        for i, line in enumerate(stripped.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            code = _line_text_without_comment(line)
            for m in ORIGIN_RE.finditer(code):
                val = m.group(1).strip()
                if val not in VALID_ORIGINS:
                    out.append({
                        "check": "G",
                        "file": str(rel),
                        "line": i,
                        "msg": f"\\origin value '{val}' not in {sorted(VALID_ORIGINS)}",
                    })
    return out


def check_h_bridgestatus_enum() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        text = strip_verbatim_preserve_lines(read_text(tex))
        for i, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for m in BRIDGESTATUS_RE.finditer(line):
                val = m.group(1).strip()
                if val not in VALID_BRIDGESTATUS:
                    out.append({
                        "check": "H",
                        "file": str(rel),
                        "line": i,
                        "msg": f"\\bridgestatus '{val}' not in {sorted(VALID_BRIDGESTATUS)}",
                    })
    return out


def check_i_tex_basename_naming() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        if not TEX_BASENAME_RE.match(tex.name):
            out.append({
                "check": "I",
                "file": str(rel),
                "line": 1,
                "msg": (
                    "tex basename must match ^([0-9]+[a-z]?_)?[a-z][a-z0-9_]*\\.tex$ "
                    "(lowercase snake_case, optional NN_ or NNa_ prefix)"
                ),
            })
    return out


def check_k_region_top_level_consolidation() -> list[dict]:
    """A region with 2+ top-level <NN>_<slug>_*.tex files should keep one hub
    at top (\\input only) and move the rest into parts/concrete_instances/<slug>/.
    Emits one violation per multi-file region (not per file)."""
    out: list[dict] = []
    if not CONCRETE_DIR.is_dir():
        return out
    from collections import defaultdict
    groups: dict[str, list[str]] = defaultdict(list)
    for f in sorted(CONCRETE_DIR.glob("*.tex")):
        m = REGION_PREFIX_RE.match(f.name)
        if m:
            groups[m.group(1)].append(f.name)
    for prefix, files in sorted(groups.items()):
        if len(files) <= 1:
            continue
        slug = prefix.split("_", 1)[1]
        subdir = CONCRETE_DIR / slug
        subdir_status = "exists" if subdir.is_dir() else "missing"
        out.append({
            "check": "K",
            "file": f"parts/concrete_instances/ (region {prefix}_*)",
            "line": 1,
            "msg": (
                f"region {prefix}_ has {len(files)} top-level files; consolidate "
                f"into one hub + parts/concrete_instances/{slug}/ siblings "
                f"(subdir {subdir_status}). Files: {', '.join(files)}"
            ),
        })
    return out


def check_l_math_mode_in_text() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        text = strip_verbatim_preserve_lines(read_text(tex))
        in_display = False
        math_env_depth = 0
        first_content_seen = False
        at_paragraph_start = True
        for i, line in enumerate(text.splitlines(), 1):
            stripped = line.strip()
            if not stripped:
                at_paragraph_start = True
                continue
            if stripped.startswith("%"):
                continue
            if UP_MACRO_DEFINITION_RE.match(line):
                continue
            command_hits = _text_command_argument_up_hits(line)
            for macro, col, command in command_hits:
                out.append({
                    "check": "L",
                    "file": str(rel),
                    "line": i,
                    "msg": f"{macro} appears outside math mode in \\{command} argument (column {col}); wrap as ${macro}$",
                })
            line_hits, next_display, next_depth = _text_mode_up_macro_hits(
                line, in_display, math_env_depth,
            )
            for macro, col in line_hits:
                prefix = line[: col - 1].strip()
                if prefix:
                    continue
                if not first_content_seen:
                    context = "first content line"
                elif at_paragraph_start:
                    context = "paragraph start"
                else:
                    continue
                out.append({
                    "check": "L",
                    "file": str(rel),
                    "line": i,
                    "msg": f"{macro} appears outside math mode at {context} (column {col}); wrap as ${macro}$",
                })
            first_content_seen = True
            at_paragraph_start = line.rstrip().endswith(r"\end{proof}") or line.rstrip().startswith(r"\end{")
            in_display = next_display
            math_env_depth = next_depth
    return out


def check_m_stale_input() -> list[dict]:
    out: list[dict] = []
    for tex in iter_part_tex():
        rel = tex.relative_to(PAPER_DIR)
        text = strip_verbatim_preserve_lines(read_text(tex))
        for i, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            code = _line_text_without_comment(line)
            for m in INPUT_RE.finditer(code):
                target = m.group(1).strip()
                if resolve_input(target) is None:
                    resolved = target if target.endswith(".tex") else f"{target}.tex"
                    out.append({
                        "check": "M",
                        "file": str(rel),
                        "line": i,
                        "msg": f"\\input target '{resolved}' does not exist relative to papers/bedc",
                    })
    return out


def check_n_duplicate_chapter_label() -> list[dict]:
    out: list[dict] = []
    label_re = re.compile(r"\\label\{ch:concrete-instances-[^}]+\}")
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        matches: list[tuple[int, str]] = []
        for i, line in enumerate(text.splitlines(), 1):
            for m in label_re.finditer(line):
                matches.append((i, m.group(0)))
        if len(matches) > 1:
            lines = ", ".join(str(line) for line, _ in matches)
            labels = ", ".join(label for _, label in matches)
            out.append({
                "check": "N",
                "file": str(rel),
                "line": matches[0][0],
                "msg": f"duplicate concrete-instances chapter labels at lines {lines}: {labels}",
            })
    return out


def check_j_region_subdir_naming() -> list[dict]:
    out: list[dict] = []
    if not CONCRETE_DIR.is_dir():
        return out
    for entry in sorted(CONCRETE_DIR.iterdir()):
        if not entry.is_dir():
            continue
        if not REGION_DIR_RE.match(entry.name):
            out.append({
                "check": "J",
                "file": str(entry.relative_to(PAPER_DIR)),
                "line": 1,
                "msg": (
                    "concrete_instances/ region subdir must match ^[a-z][a-z0-9_]*$ "
                    "(lowercase + alphanumeric + optional underscores)"
                ),
            })
    return out


def check_o_closurestatus_region_unique() -> list[dict]:
    """For each region \\<X>Up, \\begin{closurestatus}{\\<X>Up} should appear
    in at most one file (one canonical owner per region). Multiple sites
    cause data drift between blocks."""
    out: list[dict] = []
    sites: dict[str, list[tuple[str, int]]] = {}
    for tex in iter_part_tex():
        rel = str(tex.relative_to(PAPER_DIR))
        text = read_text(tex)
        for m in CLOSURE_BEGIN_REGION_RE.finditer(text):
            line_no = text.count("\n", 0, m.start()) + 1
            sites.setdefault(m.group(1), []).append((rel, line_no))
    for region, locs in sorted(sites.items()):
        files = {f for f, _ in locs}
        if len(files) <= 1:
            continue
        for f, ln in locs:
            out.append({
                "check": "O",
                "file": f,
                "line": ln,
                "msg": (
                    f"\\begin{{closurestatus}}{{\\{region}}} appears in "
                    f"{len(files)} distinct files; only one canonical owner allowed"
                ),
            })
    return out


def check_p_closureat_region_level_unique() -> list[dict]:
    """For each (region, level), \\closureat{<X>Up}{<level>Str} should appear
    in at most one file. Multiple sites for the same (region, level) are
    redundant progression entries that drift apart."""
    out: list[dict] = []
    sites: dict[tuple[str, str], list[tuple[str, int]]] = {}
    pat = re.compile(r"\\closureat\{([A-Z][A-Za-z]*Up)\}\{([a-z]+Str)\}")
    for tex in iter_part_tex():
        rel = str(tex.relative_to(PAPER_DIR))
        text = strip_verbatim_preserve_lines(read_text(tex))
        for i, line in enumerate(text.splitlines(), 1):
            if line.lstrip().startswith("%"):
                continue
            for m in pat.finditer(line):
                key = (m.group(1), m.group(2))
                sites.setdefault(key, []).append((rel, i))
    for (region, level), locs in sorted(sites.items()):
        files = {f for f, _ in locs}
        if len(files) <= 1:
            continue
        for f, ln in locs:
            out.append({
                "check": "P",
                "file": f,
                "line": ln,
                "msg": (
                    f"\\closureat{{{region}}}{{{level}}} appears in "
                    f"{len(files)} distinct files; only one canonical site allowed"
                ),
            })
    return out


CHECKS = {
    "A": check_a_closureat_enum,
    "C": check_c_closurestatus_fields,
    "D": check_d_content_reaches_closurestatus,
    "E": check_e_hub_purity,
    "F": check_f_label_convention,
    "G": check_g_origin_value,
    "H": check_h_bridgestatus_enum,
    "I": check_i_tex_basename_naming,
    "J": check_j_region_subdir_naming,
    "K": check_k_region_top_level_consolidation,
    "L": check_l_math_mode_in_text,
    "M": check_m_stale_input,
    "N": check_n_duplicate_chapter_label,
    "O": check_o_closurestatus_region_unique,
    "P": check_p_closureat_region_level_unique,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", choices=sorted(CHECKS), help="run a single check")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--strict", action="store_true", help="exit 1 on any violation")
    ap.add_argument("--limit", type=int, default=5, help="max examples per check in human mode (default 5)")
    args = ap.parse_args()

    selected = [args.check] if args.check else sorted(CHECKS)
    violations: list[dict] = []
    for cid in selected:
        violations.extend(CHECKS[cid]())

    by_check: dict[str, list[dict]] = defaultdict(list)
    for v in violations:
        by_check[v["check"]].append(v)

    if args.json:
        json.dump({
            "total": len(violations),
            "by_check": {k: len(v) for k, v in sorted(by_check.items())},
            "violations": violations,
        }, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        if not violations:
            print("[OK] warn_concrete_instances: no violations.", file=sys.stderr)
        else:
            for cid in sorted(by_check):
                vs = by_check[cid]
                print(f"[WARN] check {cid}: {len(vs)} violation(s)", file=sys.stderr)
                for v in vs[: args.limit]:
                    print(f"  {v['file']}:{v['line']}: {v['msg']}", file=sys.stderr)
                if len(vs) > args.limit:
                    print(f"  ... {len(vs) - args.limit} more (use --json for full list)", file=sys.stderr)
            tag = "[ERROR]" if args.strict else "[WARN]"
            mode = "Blocking (--strict)" if args.strict else "Non-blocking"
            print(
                f"{tag} warn_concrete_instances: {len(violations)} total violation(s) across "
                f"{len(by_check)} check(s). {mode}; run with --json for full data.",
                file=sys.stderr,
            )

    return 1 if args.strict and violations else 0


if __name__ == "__main__":
    raise SystemExit(main())

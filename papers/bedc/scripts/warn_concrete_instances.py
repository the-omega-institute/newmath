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
  G  Content namecert chapter must declare \\origin{human|ai}
  H  \\bridgestatus value must be in {none, paperBridge, bridgeChecked}

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
ORIGIN_RE = re.compile(r"\\origin\{(human|ai)\}")

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


def check_d_content_reaches_closurestatus() -> list[dict]:
    out: list[dict] = []
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        reachable = collect_reachable(tex)
        if any(CLOSURE_BEGIN_RE.search(read_text(f)) for f in reachable):
            continue
        out.append({
            "check": "D",
            "file": str(rel),
            "line": 1,
            "msg": "content namecert chapter does not reach \\begin{closurestatus} (directly or via \\input chain)",
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


def check_g_origin_tag() -> list[dict]:
    out: list[dict] = []
    for tex in sorted(CONCRETE_DIR.glob(NAMECERT_CONTENT_GLOB)):
        rel = tex.relative_to(PAPER_DIR)
        text = read_text(tex)
        if not CHAPTER_RE.search(text):
            continue
        if not ORIGIN_RE.search(text):
            out.append({
                "check": "G",
                "file": str(rel),
                "line": 1,
                "msg": "content namecert chapter missing \\origin{human|ai}",
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


CHECKS = {
    "A": check_a_closureat_enum,
    "C": check_c_closurestatus_fields,
    "D": check_d_content_reaches_closurestatus,
    "E": check_e_hub_purity,
    "F": check_f_label_convention,
    "G": check_g_origin_tag,
    "H": check_h_bridgestatus_enum,
    "I": check_i_tex_basename_naming,
    "J": check_j_region_subdir_naming,
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
            print(
                f"[WARN] warn_concrete_instances: {len(violations)} total violation(s) across "
                f"{len(by_check)} check(s). Non-blocking; run with --json for full data.",
                file=sys.stderr,
            )

    return 1 if args.strict and violations else 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Prior-art lookup for BEDC oracle deep-reasoning targets.

Before sending an initial prompt to the oracle, scan papers/bedc/parts/ for
existing definitions / theorems / propositions whose names or labels overlap
with the target's BOARD entry. Inject the matches as an "Already in paper"
block so the oracle does not re-derive material that is already canonical.

Pure stdlib. No third-party dependencies. No file edits — read-only scan.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PAPER_PARTS = REPO_ROOT / "papers" / "bedc" / "parts"

LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
THEOREM_OPEN_RE = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary|definition)\}")
DEFINITION_NAME_RE = re.compile(r"\\(?:newcommand|def|DeclareMathOperator)\*?\s*\{?\\([A-Za-z]+)\}?")
LEAN_MARKER_RE = re.compile(r"\\(?:leanchecked|leanvariant|leansorryd|leandef|leanstmt)\{([^}]+)\}")

MAX_HITS = 12
SNIPPET_BEFORE = 1
SNIPPET_AFTER = 6
KEYWORD_MIN_LEN = 4


@dataclass(frozen=True)
class PriorArtHit:
    file_rel: str
    line_no: int
    matched_keyword: str
    snippet: str


def _camel_split(token: str) -> list[str]:
    pieces = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", token)
    return [p for p in re.split(r"[^A-Za-z0-9]+", pieces) if p]


def _keywords_from(target_object: str, target_title: str) -> list[str]:
    raw = f"{target_object} {target_title}"
    keywords: set[str] = set()
    for token in re.findall(r"[A-Za-z][A-Za-z0-9_]+", raw):
        for piece in [token, *_camel_split(token)]:
            if len(piece) >= KEYWORD_MIN_LEN:
                keywords.add(piece.lower())
    return sorted(keywords)


def _iter_part_files() -> Iterable[Path]:
    if not PAPER_PARTS.exists():
        return []
    return [p for p in PAPER_PARTS.rglob("*.tex") if p.is_file()]


def _snippet(lines: list[str], idx: int) -> str:
    start = max(0, idx - SNIPPET_BEFORE)
    end = min(len(lines), idx + SNIPPET_AFTER + 1)
    return "\n".join(lines[start:end])


def lookup(target_object: str, target_title: str) -> list[PriorArtHit]:
    """Return up to MAX_HITS prior-art snippets matching the target."""
    keywords = _keywords_from(target_object, target_title)
    if not keywords:
        return []
    hits: list[PriorArtHit] = []
    for path in _iter_part_files():
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        rel = str(path.relative_to(REPO_ROOT))
        for idx, line in enumerate(lines):
            low = line.lower()
            if not (THEOREM_OPEN_RE.search(line) or LABEL_RE.search(line)):
                continue
            for kw in keywords:
                if kw and kw in low:
                    hits.append(PriorArtHit(rel, idx + 1, kw, _snippet(lines, idx)))
                    break
            if len(hits) >= MAX_HITS:
                return hits
    return hits


def render_block(hits: list[PriorArtHit]) -> str:
    """Render hits into a markdown block to inject into the initial prompt."""
    if not hits:
        return ""
    lines = ["### Already in paper (prior-art scan; do not re-derive)\n"]
    for h in hits:
        lines.append(f"**{h.file_rel}:{h.line_no}** (matched `{h.matched_keyword}`)")
        lines.append("```latex")
        lines.append(h.snippet.rstrip())
        lines.append("```")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def _normalize_canonical(name: str) -> str:
    return name.strip().strip("`").strip().lower()


def _split_canonicals(object_field: str) -> list[str]:
    raw = (object_field or "").strip()
    if not raw:
        return []
    return [s.strip().strip("`").strip() for s in raw.split(",") if s.strip().strip("`").strip()]


def _camel_tokens(canonical: str) -> set[str]:
    out: set[str] = set()
    for token in re.findall(r"[A-Za-z][A-Za-z0-9]*", canonical):
        spaced = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", token)
        for piece in spaced.split():
            piece = piece.strip().lower()
            if len(piece) >= 3:
                out.add(piece)
    return out


def _label_tokens(label: str) -> set[str]:
    return {t for t in re.findall(r"[a-z0-9]+", label.lower()) if len(t) >= 3}


def find_paper_coverage(object_field: str) -> list[dict]:
    """Detect whether target's Object is already covered by paper markers/labels.

    Returns list of hit dicts. Empty list means the target appears genuinely
    new and is safe to send through Stage 1.
    """
    canonicals = _split_canonicals(object_field)
    if not canonicals:
        return []
    hits: list[dict] = []
    for canonical in canonicals:
        canon_lower = canonical.lower()
        canon_tokens = _camel_tokens(canonical)
        if not canon_tokens:
            continue
        for path in _iter_part_files():
            try:
                text = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            rel = str(path.relative_to(REPO_ROOT))

            for m in LEAN_MARKER_RE.finditer(text):
                target_name_raw = m.group(1)
                target_name = target_name_raw.replace("\\_", "_").replace("\\\\_", "_")
                if target_name.lower().endswith(canon_lower):
                    line_no = text.count("\n", 0, m.start()) + 1
                    hits.append({
                        "kind": "lean_marker",
                        "file": rel,
                        "line": line_no,
                        "matched": target_name,
                        "object": canonical,
                    })

            for m in LABEL_RE.finditer(text):
                label = m.group(1)
                if canon_tokens.issubset(_label_tokens(label)):
                    line_no = text.count("\n", 0, m.start()) + 1
                    hits.append({
                        "kind": "label",
                        "file": rel,
                        "line": line_no,
                        "matched": label,
                        "object": canonical,
                    })
    return hits


def main() -> int:
    import argparse
    import json
    import sys

    parser = argparse.ArgumentParser(description="prior-art lookup for BEDC targets")
    parser.add_argument("--object", required=True, help="target Object name, e.g. PsameBase.inversion")
    parser.add_argument("--title", default="", help="target title")
    parser.add_argument("--coverage", action="store_true", help="Run already-in-paper coverage check instead of prior-art block")
    args = parser.parse_args()

    if args.coverage:
        hits = find_paper_coverage(args.object)
        if not hits:
            print("(no paper coverage hits — target appears new)", file=sys.stderr)
            return 0
        print(json.dumps(hits, ensure_ascii=False, indent=2))
        return 0

    hits = lookup(args.object, args.title)
    if not hits:
        print("(no prior-art hits)", file=sys.stderr)
        return 0
    print(render_block(hits))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Scan papers/bedc/parts/ for gaps that should become BOARD targets.

Detection sources (deterministic, no LLM):
- conjecture / question / remark environments without a nearby matching
  theorem/lemma/proposition in the same chapter file
- LaTeX comments tagged with TODO / open / unproven / to-verify
- explicit prose markers: "remains open", "leave for future work",
  "to be established", "to be shown", "未证", "尚未证明"
- definitions whose chapter file has no theorem label citing the same concept

Each gap becomes a candidate dict matching the schema accepted by
oracle_client.append_candidates_to_board. With --append, the scanner appends
qualifying candidates directly to BOARD.md so the next loop pass picks them
up automatically.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PAPER_PARTS = REPO_ROOT / "papers" / "bedc" / "parts"

CONJECTURE_RE = re.compile(r"\\begin\{(conjecture|question)\}")
THEOREM_RE = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
DEFINITION_RE = re.compile(r"\\begin\{definition\}\s*\\label\{([^}]+)\}")
END_ENV_RE = re.compile(r"\\end\{(conjecture|question|definition)\}")

TODO_COMMENT_RE = re.compile(r"%\s*(?:TODO|FIXME|UNPROVEN|TO\s*VERIFY|TO\s*PROVE)\b[^\n]*", re.IGNORECASE)

OPEN_PROSE_PATTERNS = [
    re.compile(r"remains?\s+open", re.IGNORECASE),
    re.compile(r"leave[sd]?\s+(?:this|.*?)\s*for\s+future\s+work", re.IGNORECASE),
    re.compile(r"to\s+be\s+(?:established|shown|proved|verified)\b", re.IGNORECASE),
    re.compile(r"未证(?:明)?"),
    re.compile(r"尚未证明"),
]

CONTEXT_BEFORE = 2
CONTEXT_AFTER = 12
MIN_RATIONALE_CHARS = 80
TITLE_MAX_CHARS = 90
NON_TARGET_PREFIXES = (
    "\\label",
    "\\chapter",
    "\\section",
    "\\subsection",
    "\\subsubsection",
    "\\begin{remark}",
    "\\begin{example}",
)


@dataclass(frozen=True)
class GapHit:
    file_rel: str
    line_no: int
    kind: str  # "conjecture" | "todo" | "open_prose" | "orphan_definition"
    snippet: str
    label: str = ""


def _theme_from_path(path: Path) -> str:
    rel = path.relative_to(PAPER_PARTS)
    parts_list = list(rel.parts)
    return parts_list[0] if parts_list else "unknown"


def _read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _snippet(lines: list[str], idx: int) -> str:
    start = max(0, idx - CONTEXT_BEFORE)
    end = min(len(lines), idx + CONTEXT_AFTER + 1)
    return "\n".join(lines[start:end])


def _find_label_in_block(lines: list[str], idx: int) -> str:
    """Find first \\label{...} after the given line, within the env."""
    for offset in range(0, min(CONTEXT_AFTER + 1, len(lines) - idx)):
        line = lines[idx + offset]
        m = LABEL_RE.search(line)
        if m:
            return m.group(1)
        if END_ENV_RE.search(line):
            break
    return ""


def _scan_file(path: Path) -> list[GapHit]:
    text = _read(path)
    if not text:
        return []
    lines = text.splitlines()
    rel = str(path.relative_to(REPO_ROOT))
    hits: list[GapHit] = []

    for idx, line in enumerate(lines):
        m = CONJECTURE_RE.search(line)
        if m:
            label = _find_label_in_block(lines, idx)
            hits.append(GapHit(rel, idx + 1, m.group(1), _snippet(lines, idx), label))
            continue
        if TODO_COMMENT_RE.search(line):
            hits.append(GapHit(rel, idx + 1, "todo", _snippet(lines, idx)))
            continue
        for pat in OPEN_PROSE_PATTERNS:
            if pat.search(line):
                hits.append(GapHit(rel, idx + 1, "open_prose", _snippet(lines, idx)))
                break

    # orphan-definition heuristic: definitions whose file has zero theorems
    # citing the same concept name (very weak; intentionally conservative).
    has_theorem = bool(THEOREM_RE.search(text))
    if not has_theorem:
        for m in DEFINITION_RE.finditer(text):
            line_no = text.count("\n", 0, m.start()) + 1
            label = m.group(1)
            hits.append(GapHit(rel, line_no, "orphan_definition", _snippet(lines, line_no - 1), label))

    return hits


def scan_all() -> list[GapHit]:
    hits: list[GapHit] = []
    if not PAPER_PARTS.exists():
        return hits
    for path in sorted(PAPER_PARTS.rglob("*.tex")):
        hits.extend(_scan_file(path))
    return hits


def _title_from_hit(hit: GapHit) -> str:
    if hit.label:
        words = hit.label.split(":", 1)
        tail = words[1] if len(words) > 1 else words[0]
        return tail.replace("-", " ").replace("_", " ").strip()[:TITLE_MAX_CHARS] or hit.kind
    first_line = next(
        (ln.strip() for ln in hit.snippet.splitlines() if ln.strip() and not ln.strip().startswith("%")),
        hit.kind,
    )
    return first_line[:TITLE_MAX_CHARS]


def _first_substantive_line(snippet: str) -> str:
    return next(
        (ln.strip() for ln in snippet.splitlines() if ln.strip() and not ln.strip().startswith("%")),
        "",
    )


def _is_substantive_gap(hit: GapHit, candidate: dict) -> bool:
    """Keep deterministic gap scans from turning structural prose into targets."""
    title = str(candidate.get("title") or "").strip()
    claim = str(candidate.get("concrete_claim") or "").strip()
    first = _first_substantive_line(hit.snippet)
    if hit.kind == "open_prose":
        if first.startswith(NON_TARGET_PREFIXES):
            return False
        if title.startswith("\\") or claim.startswith(NON_TARGET_PREFIXES):
            return False
    if title.startswith("\\label") or title.startswith("\\begin{remark}"):
        return False
    return True


def hit_to_candidate(hit: GapHit) -> dict:
    """Convert a GapHit to the candidate dict shape append_candidates_to_board expects."""
    title = _title_from_hit(hit)
    if hit.kind == "conjecture":
        fit, novelty = 8, 8
    elif hit.kind == "open_prose":
        fit, novelty = 7, 7
    elif hit.kind == "orphan_definition":
        fit, novelty = 7, 6
    else:
        fit, novelty = 6, 6
    rationale = (
        f"Surfaced from paper gap scan: {hit.kind} at "
        f"{hit.file_rel}:{hit.line_no}"
        f"{' label=' + hit.label if hit.label else ''}.\n\n"
        f"Snippet:\n{hit.snippet}"
    )
    if len(rationale) < MIN_RATIONALE_CHARS:
        rationale = rationale + "\n\n(snippet was short; widen CONTEXT_AFTER if needed)"
    return {
        "title": title,
        "concrete_claim": (
            hit.snippet.split("\n\n", 1)[0][:600]
            if hit.snippet
            else f"see {hit.file_rel}:{hit.line_no}"
        ),
        "local_inputs": [hit.file_rel],
        "fit_score": fit,
        "novelty": novelty,
        "rationale": rationale,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Scan papers/bedc/parts for theory gaps")
    parser.add_argument("--append", action="store_true", help="Append qualifying gaps to BOARD.md as candidate B-XX entries")
    parser.add_argument("--min-fit", type=int, default=7)
    parser.add_argument("--min-novelty", type=int, default=6)
    parser.add_argument("--limit", type=int, default=0, help="Cap number of candidates (0 = no cap)")
    parser.add_argument("--json", action="store_true", help="Emit candidates as JSON")
    args = parser.parse_args()

    hits = scan_all()
    candidates = []
    for hit in hits:
        candidate = hit_to_candidate(hit)
        if _is_substantive_gap(hit, candidate):
            candidates.append(candidate)
    candidates = [
        c for c in candidates
        if c["fit_score"] >= args.min_fit and c["novelty"] >= args.min_novelty
    ]
    if args.limit > 0:
        candidates = candidates[: args.limit]

    if args.json:
        print(json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2))

    if args.append:
        if not candidates:
            print("(no candidates passed thresholds; nothing appended)", file=sys.stderr)
            return 0
        from oracle_client import append_candidates_to_board
        accepted = append_candidates_to_board(candidates)
        print(f"appended {len(accepted)} candidates to BOARD.md: {accepted}", file=sys.stderr)
        return 0

    if not args.json:
        for c in candidates:
            print(f"- {c['title']}  (fit={c['fit_score']}, novelty={c['novelty']})  ← {c['local_inputs'][0] if c['local_inputs'] else ''}")
        print(f"\ntotal: {len(candidates)} candidates (use --append to add to BOARD.md)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

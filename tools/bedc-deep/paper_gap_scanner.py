#!/usr/bin/env python3
"""Scan papers/bedc/parts/ for gaps that should become BOARD targets.

Detection sources (deterministic, no LLM):
- conjecture / question / remark environments without a nearby matching
  theorem/lemma/proposition in the same chapter file
- LaTeX comments tagged with TODO / open / unproven / to-verify
- explicit prose markers: "remains open", "leave for future work",
  "to be established", "to be shown", "未证", "尚未证明"
- definitions whose chapter file has no theorem label citing the same concept

Each gap becomes a candidate dict matching the shared board_spawn candidate
shape. With --append, the scanner routes qualifying candidates through
board_spawn, candidate_inbox, the judge, and logic_packet_gate before any
BOARD.md append. It is a deterministic source, not a shortcut around intake
discipline.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PAPER_PARTS = REPO_ROOT / "papers" / "bedc" / "parts"

CONJECTURE_RE = re.compile(r"\\begin\{(conjecture|question)\}")
THEOREM_RE = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
DEFINITION_RE = re.compile(r"\\begin\{definition\}\s*\\label\{([^}]+)\}")
END_ENV_RE = re.compile(r"\\end\{(conjecture|question|definition)\}")
CONJECTURE_STATUS_RE = re.compile(r"\\conjectureStatus\{([^}]+)\}")
METACIC_OBLIGATION_ITEM_RE = re.compile(r"\\item\s+\$\\mathrm\{([^}]+)\}\$\.\s*(.*)")

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
NAMECERT_SURFACE_LINE_CAP = 660
NAMECERT_SURFACE_TERMS_RE = re.compile(
    r"(?:route|ledger|consumer|downstream|readback|handoff|boundary|selected|row)"
    r"[a-z0-9_\- ]{0,80}"
    r"(?:determinacy|exactness|non[- ]?escape|exhaustion|coverage|handoff)|"
    r"(?:determinacy|exactness|non[- ]?escape|exhaustion|coverage|handoff)"
    r"[a-z0-9_\- ]{0,80}"
    r"(?:route|ledger|consumer|downstream|readback|handoff|boundary|selected|row)",
    re.IGNORECASE,
)
NAMECERT_ROUTE_SURFACE_RE = re.compile(
    r"\b(?:consumer|downstream|route|readback|handoff|boundary)\b",
    re.IGNORECASE,
)
RATE_LIKE_RE = re.compile(
    r"\b(cauchy|completion|complete|compact|continuity|continuous|limit|"
    r"convergence|converge|modulus|rate|tail|dyadic|regularization)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class GapHit:
    file_rel: str
    line_no: int
    kind: str  # "conjecture" | "todo" | "open_prose" | "orphan_definition" | "metacic_obligation"
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
    conjecture_status = ""
    status_match = CONJECTURE_STATUS_RE.search(text)
    if status_match:
        conjecture_status = status_match.group(1).strip().lower()
    skip_conjecture_file_gaps = (
        rel.startswith("papers/bedc/parts/conjectures/")
        and conjecture_status
        and conjecture_status != "open"
    )

    if rel == "papers/bedc/parts/visions/metacic_open_problems.tex":
        for idx, line in enumerate(lines):
            m = METACIC_OBLIGATION_ITEM_RE.search(line)
            if not m:
                continue
            label = "metacic-" + re.sub(r"[^a-z0-9]+", "-", m.group(1).lower()).strip("-")
            hits.append(GapHit(rel, idx + 1, "metacic_obligation", _snippet(lines, idx), label))

    for idx, line in enumerate(lines):
        m = CONJECTURE_RE.search(line)
        if m:
            if skip_conjecture_file_gaps:
                continue
            label = _find_label_in_block(lines, idx)
            hits.append(GapHit(rel, idx + 1, m.group(1), _snippet(lines, idx), label))
            continue
        if skip_conjecture_file_gaps:
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
    if hit.kind == "metacic_obligation" and hit.label.startswith("metacic-"):
        tail = hit.label.removeprefix("metacic-").replace("-", " ")
        return f"MetaCIC {tail} discharge obligation"[:TITLE_MAX_CHARS]
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


def _claim_from_hit(hit: GapHit) -> str:
    """Extract a human claim line rather than a LaTeX structural marker."""
    substantive: list[str] = []
    for raw in hit.snippet.splitlines():
        line = raw.strip()
        if not line or line.startswith("%"):
            continue
        if line.startswith(("\\label", "\\chapter", "\\section", "\\subsection", "\\subsubsection")):
            continue
        if re.match(r"\\(?:begin|end)\{(?:conjecture|question|proof|enumerate|itemize)\}", line):
            continue
        if line.startswith("\\item"):
            line = line.removeprefix("\\item").strip()
        if line:
            substantive.append(line)
        if len(" ".join(substantive)) >= 600:
            break
    claim = " ".join(substantive).strip()
    return claim[:600] if claim else f"see {hit.file_rel}:{hit.line_no}"


def _rationale_snippet(snippet: str) -> str:
    """Keep context useful without feeding structural labels into pre-gate."""
    kept: list[str] = []
    for raw in snippet.splitlines():
        line = raw.rstrip()
        stripped = line.strip()
        if stripped.startswith("\\label"):
            continue
        if stripped.startswith(("\\leanvariant", "\\concretizedIn")):
            continue
        kept.append(line)
    return "\n".join(kept).strip()


def _object_title_from_carrier(rec: dict[str, Any], file_rel: str) -> str:
    title = str(rec.get("title") or "").strip()
    label = str(rec.get("label") or "").strip()
    source = title or label
    source = re.sub(r"\\[A-Za-z]+(?:\{[^}]*\})?", "", source)
    source = re.sub(r"\b(?:concrete|finite|local|accepted)\b", "", source, flags=re.I)
    source = re.sub(r"\bcarrier\b", "", source, flags=re.I)
    source = source.replace("_", " ").replace("-", " ")
    source = re.sub(r"\s+", " ", source).strip(" :")
    if source:
        return source[:55]
    name = Path(file_rel).name
    name = re.sub(r"^\d+_", "", name)
    name = re.sub(r"_namecert_construction\.tex$", "", name)
    name = name.replace("_", " ")
    return name[:55] or "NameCert packet"


def _budget_for_namecert_surface(obj: str, labels_text: str) -> tuple[str, str, str]:
    haystack = " ".join([obj, labels_text])
    if RATE_LIKE_RE.search(haystack):
        return (
            "B2_rate_or_modulus",
            (
                "Finite readback over an already displayed NameCert carrier "
                "and obligation surface, with any Cauchy/completion/rate "
                "content restricted to the displayed modulus, schedule, "
                "window, or threshold rows."
            ),
            (
                "Displayed finite modulus/schedule/window/threshold rows are "
                "the complete rate surface; no ambient compactness or hidden "
                "choice argument is used."
            ),
        )
    return (
        "B0_finite_witness",
        (
            "Finite readback over an already displayed NameCert carrier and "
            "obligation surface; no host equality, compactness, or "
            "choice-like principle is required."
        ),
        (
            "Finite displayed packet rows provide the complete schedule; no "
            "limit, completion, compactness, or Cauchy surface is used."
        ),
    )


def _namecert_surface_candidates() -> list[dict]:
    """Surface small existing-chapter NameCert route candidates.

    This is deliberately weaker than a theorem writer: it only finds files that
    already expose both a carrier and a NameCert obligation surface, then asks
    the ordinary board_spawn judge and logic_packet_gate whether a small
    readback-determinacy lemma is worth landing there.
    """
    try:
        import paper_index
    except Exception:
        return []

    try:
        index = paper_index.load_or_build()
    except Exception:
        return []

    candidates: list[dict] = []
    for item in index.get("files") or []:
        rel = str(item.get("file") or "")
        if not rel.startswith("papers/bedc/parts/concrete_instances/"):
            continue
        if not rel.endswith("_namecert_construction.tex"):
            continue
        line_count = int(item.get("line_count") or 0)
        if line_count >= NAMECERT_SURFACE_LINE_CAP:
            continue
        labels = item.get("theorem_like_labels") or item.get("labels") or []
        carrier = next(
            (
                rec for rec in labels
                if str(rec.get("env") or "") == "definition"
                and "carrier" in " ".join([
                    str(rec.get("title") or ""),
                    str(rec.get("label") or ""),
                ]).lower()
            ),
            None,
        )
        obligation = next(
            (
                rec for rec in labels
                if str(rec.get("env") or "") in {"theorem", "lemma", "proposition"}
                and "namecert" in " ".join([
                    str(rec.get("title") or ""),
                    str(rec.get("label") or ""),
                ]).lower()
                and re.search(
                    r"\bobligation|surface\b",
                    " ".join([
                        str(rec.get("title") or ""),
                        str(rec.get("label") or ""),
                    ]),
                    re.IGNORECASE,
                )
            ),
            None,
        )
        if not carrier or not obligation:
            continue
        theorem_surface = "\n".join(
            " ".join([str(rec.get("title") or ""), str(rec.get("label") or "")])
            for rec in labels
            if str(rec.get("env") or "") in {"theorem", "lemma", "proposition"}
        )
        if (
            NAMECERT_SURFACE_TERMS_RE.search(theorem_surface)
            or NAMECERT_ROUTE_SURFACE_RE.search(theorem_surface)
        ):
            continue

        obj = _object_title_from_carrier(carrier, rel)
        labels_text = theorem_surface + " " + " ".join([
            str(carrier.get("title") or ""),
            str(carrier.get("label") or ""),
            str(obligation.get("title") or ""),
            str(obligation.get("label") or ""),
        ])
        budget, budget_reason, rate_surface = _budget_for_namecert_surface(obj, labels_text)
        title = f"{obj} finite route readback determinacy"[:TITLE_MAX_CHARS]
        carrier_label = str(carrier.get("label") or "")
        obligation_label = str(obligation.get("label") or "")
        claim = (
            f"For an accepted {obj} carrier, every finite consumer bridge route "
            "that reads the displayed packet rows is determined by projecting "
            f"{carrier_label} and replaying the local NameCert obligation "
            f"surface {obligation_label}; no additional host, global, or "
            "unlisted source row is introduced."
        )
        dependency = (
            f"Depends only on {carrier_label}, {obligation_label}, and the "
            "displayed BHist/hsame/Cont/Pkg/NameCert rows already present in "
            f"{rel}."
        )
        resource = (
            "Uses one finite carrier projection plus the listed local "
            "obligation rows; no oracle output, copied history, choice "
            "principle, or external theorem object is consumed."
        )
        candidates.append({
            "title": title,
            "claim": claim,
            "concrete_claim": claim,
            "local_inputs": [rel],
            "fit_score": 7,
            "novelty": 6,
            "landing_kind": "existing_chapter_lemma",
            "tastegate_mode": "existing_chapter",
            "axiom_budget": budget,
            "strength_level": budget,
            "budget_reason": budget_reason,
            "existence_mode": "constructive_witness",
            "witness_extractor": (
                f"Project the accepted {obj} carrier rows and read the "
                "consumer route through the displayed local NameCert "
                "obligation surface."
            ),
            "cut_rank": "1",
            "elimination_plan": (
                "Eliminate the bridge by carrier projection, then replay the "
                "displayed obligation rows and refuse any route requiring a "
                "host/global/unlisted coordinate."
            ),
            "equality_kind": "bisimilar",
            "interpretation_kind": "none",
            "resource_trace": resource,
            "dependency_trace": dependency,
            "rate_modulus_surface": rate_surface,
            "oracle_mode": "candidate_generation",
            "rationale": (
                "Deterministic NameCert surface scan found an existing carrier "
                f"and obligation surface in {rel}: {carrier_label} with "
                f"{obligation_label}. The proposed landing is a small "
                "existing-chapter lemma over those displayed rows only."
            ),
            "source": "paper_gap_scanner",
        })
    return candidates


def _is_substantive_gap(hit: GapHit, candidate: dict) -> bool:
    """Keep deterministic gap scans from turning structural prose into targets."""
    title = str(candidate.get("title") or "").strip()
    claim = str(candidate.get("concrete_claim") or "").strip()
    first = _first_substantive_line(hit.snippet)
    if (
        hit.kind == "open_prose"
        and hit.file_rel == "papers/bedc/parts/visions/metacic_open_problems.tex"
    ):
        return False
    if hit.kind == "open_prose":
        if first.startswith(NON_TARGET_PREFIXES):
            return False
        if title.startswith("\\") or claim.startswith(NON_TARGET_PREFIXES):
            return False
    if title.startswith("\\label") or title.startswith("\\begin{remark}"):
        return False
    return True


def hit_to_candidate(hit: GapHit) -> dict:
    """Convert a GapHit to the shared BOARD candidate dict shape."""
    title = _title_from_hit(hit)
    if hit.kind == "conjecture":
        fit, novelty = 8, 8
    elif hit.kind == "metacic_obligation":
        fit, novelty = 8, 7
    elif hit.kind == "open_prose":
        fit, novelty = 7, 7
    elif hit.kind == "orphan_definition":
        fit, novelty = 7, 6
    else:
        fit, novelty = 6, 6
    label_note = ""
    if hit.label and hit.kind != "metacic_obligation":
        label_note = " label=" + hit.label
    rationale = (
        f"Surfaced from paper gap scan: {hit.kind} at "
        f"{hit.file_rel}:{hit.line_no}"
        f"{label_note}.\n\n"
        f"Snippet:\n{_rationale_snippet(hit.snippet)}"
    )
    if len(rationale) < MIN_RATIONALE_CHARS:
        rationale = rationale + "\n\n(snippet was short; widen CONTEXT_AFTER if needed)"
    claim = _claim_from_hit(hit)
    if hit.kind == "metacic_obligation" and hit.label.startswith("metacic-"):
        obligation = hit.label.removeprefix("metacic-").replace("-", "")
        claim = (
            "If the MetaCIC subject-reduction discharge interface is used, "
            f"then the {obligation} row must be supplied as an explicit finite "
            "setup obligation rather than inferred from the parameterised theorem."
        )
    return {
        "title": title,
        "claim": claim,
        "concrete_claim": claim,
        "local_inputs": [hit.file_rel],
        "fit_score": fit,
        "novelty": novelty,
        "rationale": rationale,
        "source": "paper_gap_scanner",
    }


def append_via_board_spawn(
    candidates: list[dict],
    *,
    fit_threshold: int,
    novelty_threshold: int,
) -> object:
    """Route deterministic gap candidates through the shared intake gate."""
    import board_spawn

    return board_spawn.spawn_from_candidates(
        codex_candidates=candidates,
        oracle_candidates=[],
        fit_threshold=fit_threshold,
        novelty_threshold=novelty_threshold,
    )


def generate_candidates(
    *,
    min_fit: int = 7,
    min_novelty: int = 6,
    limit: int = 0,
) -> list[dict]:
    hits = scan_all()
    existing_titles = _existing_board_titles()
    candidates = []
    for hit in hits:
        candidate = hit_to_candidate(hit)
        title_key = str(candidate.get("title") or "").strip().lower()
        if title_key in existing_titles:
            continue
        if _is_substantive_gap(hit, candidate):
            candidates.append(candidate)
    for candidate in _namecert_surface_candidates():
        title_key = str(candidate.get("title") or "").strip().lower()
        if title_key in existing_titles:
            continue
        candidates.append(candidate)
    candidates = [
        c for c in candidates
        if c["fit_score"] >= min_fit and c["novelty"] >= min_novelty
    ]
    seen_titles: set[str] = set()
    deduped: list[dict] = []
    for candidate in candidates:
        title_key = str(candidate.get("title") or "").strip().lower()
        if title_key in seen_titles:
            continue
        seen_titles.add(title_key)
        deduped.append(candidate)
    candidates = deduped
    if limit > 0:
        candidates = candidates[:limit]
    return candidates


def _existing_board_titles() -> set[str]:
    try:
        import board_archive
        return board_archive.existing_target_titles(include_archive=True)
    except Exception:
        return set()


def main() -> int:
    parser = argparse.ArgumentParser(description="Scan papers/bedc/parts for theory gaps")
    parser.add_argument("--append", action="store_true", help="Submit qualifying gaps through board_spawn before any BOARD.md append")
    parser.add_argument("--min-fit", type=int, default=7)
    parser.add_argument("--min-novelty", type=int, default=6)
    parser.add_argument("--limit", type=int, default=0, help="Cap number of candidates (0 = no cap)")
    parser.add_argument("--json", action="store_true", help="Emit candidates as JSON")
    args = parser.parse_args()

    candidates = generate_candidates(
        min_fit=args.min_fit,
        min_novelty=args.min_novelty,
        limit=args.limit,
    )

    if args.json:
        print(json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2))

    if args.append:
        if not candidates:
            print("(no candidates passed thresholds; nothing appended)", file=sys.stderr)
            return 0
        result = append_via_board_spawn(
            candidates,
            fit_threshold=args.min_fit,
            novelty_threshold=args.min_novelty,
        )
        appended = getattr(result, "appended_ids", [])
        accepted = getattr(result, "accepted", [])
        rejected = getattr(result, "rejected", [])
        error = getattr(result, "error", "")
        print(
            f"board_spawn ok={getattr(result, 'ok', False)} "
            f"accepted={len(accepted)} rejected={len(rejected)} "
            f"appended={len(appended)}: {appended}",
            file=sys.stderr,
        )
        if error:
            print(f"ERROR: {error}", file=sys.stderr)
            return 1
        return 0

    if not args.json:
        for c in candidates:
            print(f"- {c['title']}  (fit={c['fit_score']}, novelty={c['novelty']})  ← {c['local_inputs'][0] if c['local_inputs'] else ''}")
        print(f"\ntotal: {len(candidates)} candidates (use --append to add to BOARD.md)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

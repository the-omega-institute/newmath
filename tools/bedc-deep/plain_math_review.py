#!/usr/bin/env python3
"""Plain-reading review layer for BEDC candidate intake.

This is a wide-in, strict-out audit layer.  It reads broad candidate supply
from runtime inboxes, research packets, and vision notes; converts each item to
a plain philosophy / plain mathematics / BEDC-native reading; and writes only
local state.  It does not edit BOARD or paper files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import logic_packet_gate
import paper_index
from dispatch_bedc_target import REPO_ROOT, SCRIPT_DIR


STATE_DIR = SCRIPT_DIR / "state"
REVIEWS_JSONL = STATE_DIR / "plain_math_reviews.jsonl"
REVIEWS_LATEST = STATE_DIR / "plain_math_reviews_latest.md"
CANDIDATE_INBOX = STATE_DIR / "candidate_inbox.jsonl"
RESEARCH_CANDIDATES = STATE_DIR / "research_candidates.jsonl"
VISIONS_DIR = REPO_ROOT / "papers" / "bedc" / "parts" / "visions"

DEFAULT_LIMIT = 80
TAIL_LINES = 1200
VISION_MAX_CHARS = 5000
TITLE_MAX = 88

SOURCE_AUTOMATH_RE = re.compile(
    r"automath|bridge continuation|external theorem signal|review_packets?|"
    r"source theorem signal|source_path|source_repo",
    re.IGNORECASE,
)
VISION_PATH_RE = re.compile(r"^papers/bedc/parts/visions/", re.IGNORECASE)
ANALYSIS_RE = re.compile(
    r"\b(cauchy|completion|complete|compact|continuity|continuous|limit|"
    r"converge|modulus|rate|tail|finite cover|hyperbolic|phase)\b",
    re.IGNORECASE,
)
BRIDGE_RE = re.compile(
    r"\b(bridge|transport|translation|continuation|factor|compose|handoff|"
    r"readback|substrate|automath|rule\s*110|lean)\b",
    re.IGNORECASE,
)
EQUALITY_RE = re.compile(
    r"\b(equal|equality|same|equivalent|equivalence|isomorphic|mirror|"
    r"bisimilar|correspond)\b",
    re.IGNORECASE,
)
EXISTENCE_RE = re.compile(
    r"\b(exists?|there exists|admits?|has a|has an|witness|input|faith|"
    r"entry|generator)\b",
    re.IGNORECASE,
)
TOO_BROAD_RE = re.compile(
    r"\b(universe|all mathematics|everything|entire|complete theory|"
    r"foundation|philosophy|consciousness|riemann hypothesis|hard problems?)\b",
    re.IGNORECASE,
)
REJECT_RE = re.compile(
    r"duplicate_title|forbidden_axis|non_paper_local_input|"
    r"below_fit_threshold|below_novelty_threshold|predicted_label_collision|"
    r"structural_title|missing_title|missing_claim|claim_too_short",
    re.IGNORECASE,
)
HOLD_RE = re.compile(
    r"missing_local_input|missing_local_inputs|no_indexed_safe_landing|"
    r"hub_only_landing|inspiration_only_not_board_landing|"
    r"predicted_line_cap_overflow|logic_packet_gate|missing_logic_budget|"
    r"external_signal_|too_weak",
    re.IGNORECASE,
)
PREFERRED_LANDING_RE = re.compile(
    r"^papers/bedc/parts/(?:concrete_instances|proof_sprint|proof_standing)/",
    re.IGNORECASE,
)
BLOCKED_PART_RE = re.compile(
    r"^papers/bedc/parts/(?:visions|conjectures)/",
    re.IGNORECASE,
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _as_list(value: Any) -> list[str]:
    if isinstance(value, list):
        return [str(v).strip() for v in value if str(v).strip()]
    if isinstance(value, str) and value.strip():
        return [value.strip()]
    return []


def _clean(text: Any, limit: int = 900) -> str:
    out = re.sub(r"\s+", " ", str(text or "")).strip()
    if len(out) > limit:
        out = out[: limit - 3].rstrip() + "..."
    return out


def _claim(record: dict[str, Any]) -> str:
    return _clean(
        record.get("claim")
        or record.get("concrete_claim")
        or record.get("problem")
        or record.get("rationale")
        or record.get("raw_claim")
        or ""
    )


def _source_id(source_event: str, title: str, claim: str, source_path: str = "") -> str:
    payload = {
        "source_event": source_event,
        "title": title.strip().lower(),
        "claim": claim.strip().lower(),
        "source_path": source_path,
    }
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()
    return f"plain-{digest[:16]}"


def _title_from_tex(text: str, path: Path) -> str:
    match = re.search(r"\\chapter\{([^}]+)\}", text)
    if match:
        return _clean(match.group(1), TITLE_MAX)
    name = re.sub(r"\.tex$", "", path.name)
    return _clean(name.replace("_", " ").title(), TITLE_MAX)


def _strip_tex(text: str) -> str:
    text = re.sub(r"%.*", " ", text)
    text = re.sub(r"\\(?:chapter|section|subsection|label|concretizedIn)\{[^}]*\}", " ", text)
    text = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?", " ", text)
    text = re.sub(r"[{}$]", " ", text)
    return _clean(text, 1300)


def _read_jsonl_tail(path: Path, limit: int) -> list[dict[str, Any]]:
    if not path.exists() or limit <= 0:
        return []
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()[-TAIL_LINES:]
    except OSError:
        return []
    rows: list[dict[str, Any]] = []
    for line in reversed(lines):
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(record, dict):
            rows.append(record)
        if len(rows) >= limit:
            break
    return rows


def _candidate_from_research_packet(packet: dict[str, Any]) -> dict[str, Any]:
    candidate = packet.get("candidate")
    if isinstance(candidate, dict):
        out = dict(candidate)
    else:
        out = dict(packet)
    out.setdefault("status", packet.get("status"))
    out.setdefault("reasons", packet.get("reasons"))
    out.setdefault("source", packet.get("source") or out.get("source") or "research_candidate")
    return out


def _vision_records(limit: int) -> list[dict[str, Any]]:
    if not VISIONS_DIR.exists() or limit <= 0:
        return []
    rows: list[dict[str, Any]] = []
    for path in sorted(VISIONS_DIR.glob("*.tex"), key=lambda p: p.stat().st_mtime, reverse=True):
        if path.name.startswith("_") or path.name == "index.tex":
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="replace")[:VISION_MAX_CHARS]
        except OSError:
            continue
        rel = str(path.relative_to(REPO_ROOT))
        rows.append(
            {
                "title": _title_from_tex(text, path),
                "claim": _strip_tex(text),
                "local_inputs": [rel],
                "source": "vision",
                "source_path": rel,
                "landing_kind": "review_only",
                "tastegate_mode": "vision_inspiration",
            }
        )
        if len(rows) >= limit:
            break
    return rows


def collect_sources(limit: int = DEFAULT_LIMIT) -> list[tuple[str, dict[str, Any]]]:
    per_source = max(1, limit // 3)
    rows: list[tuple[str, dict[str, Any]]] = []
    for rec in _read_jsonl_tail(CANDIDATE_INBOX, per_source):
        if str(rec.get("event") or "") in {
            "received",
            "pre_gate_hold",
            "held_for_refinement",
            "pre_gate_reject",
            "rejected",
        }:
            rows.append(("candidate_inbox", rec))
    for packet in _read_jsonl_tail(RESEARCH_CANDIDATES, per_source):
        rows.append(("research_candidate", _candidate_from_research_packet(packet)))
    for rec in _vision_records(per_source):
        rows.append(("vision", rec))
    return _dedupe_sources(rows)[:limit]


def _dedupe_sources(rows: list[tuple[str, dict[str, Any]]]) -> list[tuple[str, dict[str, Any]]]:
    out: list[tuple[str, dict[str, Any]]] = []
    seen: set[str] = set()
    for source_event, rec in rows:
        title = _clean(rec.get("title"), TITLE_MAX)
        claim = _claim(rec)
        path = str(rec.get("source_path") or "")
        key = _source_id(source_event, title, claim, path)
        if key in seen or not title or not claim:
            continue
        seen.add(key)
        out.append((source_event, rec))
    return out


def _paper_files() -> dict[str, dict[str, Any]]:
    try:
        idx = paper_index.load_or_build()
    except Exception:
        return {}
    return {str(item.get("file") or ""): item for item in idx.get("files") or []}


def _safe_landing_inputs(inputs: list[str], files: dict[str, dict[str, Any]]) -> list[str]:
    safe: list[str] = []
    for rel in inputs:
        if BLOCKED_PART_RE.search(rel):
            continue
        if not PREFERRED_LANDING_RE.search(rel):
            continue
        if not (REPO_ROOT / rel).exists():
            continue
        info = files.get(rel) or {}
        if info.get("hub_like"):
            continue
        try:
            if int(info.get("line_count") or info.get("lines") or 0) >= 740:
                continue
        except (TypeError, ValueError):
            continue
        safe.append(rel)
    return safe


def _fallback_landing(
    files: dict[str, dict[str, Any]],
    text: str,
    preferred_inputs: list[str] | None = None,
) -> str:
    words = {
        w.lower()
        for w in re.findall(r"[A-Za-z][A-Za-z0-9]{4,}", text)
        if w.lower() not in {"candidate", "chapter", "local", "claim", "surface"}
    }
    preferred_dirs = {
        str(Path(rel).parent)
        for rel in (preferred_inputs or [])
        if rel.startswith("papers/bedc/parts/")
    }
    scored: list[tuple[int, str]] = []
    for rel, info in files.items():
        if not PREFERRED_LANDING_RE.search(rel):
            continue
        if info.get("hub_like"):
            continue
        try:
            if int(info.get("line_count") or 0) >= 740:
                continue
        except (TypeError, ValueError):
            continue
        hay = " ".join([rel, str(info.get("title") or "")]).lower()
        score = sum(1 for word in words if word in hay)
        if str(Path(rel).parent) in preferred_dirs:
            score += 3
        if score:
            scored.append((score, rel))
    if not scored:
        return ""
    scored.sort(key=lambda item: (-item[0], item[1]))
    return scored[0][1]


def _plain_philosophy(title: str, claim: str) -> str:
    text = f"{title}. {claim}"
    notes: list[str] = []
    if SOURCE_AUTOMATH_RE.search(text):
        notes.append("External formal signals are treated as hints, not as authority.")
    if VISION_PATH_RE.search(text) or TOO_BROAD_RE.search(text):
        notes.append("A broad vision must be read as a request for smaller observable distinctions.")
    if EXISTENCE_RE.search(text):
        notes.append("Any asserted entry, input, generator, or existence needs a displayed witness.")
    if BRIDGE_RE.search(text):
        notes.append("Any cross-surface route needs an eliminable bridge reading.")
    if EQUALITY_RE.search(text):
        notes.append("Sameness must be typed as equality, equivalence, mirror, or interpretation.")
    if ANALYSIS_RE.search(text):
        notes.append("Limit or geometry language must expose rate, modulus, boundary, or finite readout data.")
    if not notes:
        notes.append("Read the item as a local observation about displayed BEDC rows and dependencies.")
    return " ".join(notes)


def _plain_math(title: str, claim: str) -> str:
    text = f"{title}. {claim}"
    if SOURCE_AUTOMATH_RE.search(text):
        return (
            "Forget the external source path and ask whether a BEDC-local chapter already "
            "contains rows that support a small lemma, obligation, obstruction, or ledger entry."
        )
    if ANALYSIS_RE.search(text):
        return (
            "Replace geometric or analytic prose by a finite statement about readout maps, "
            "boundary rows, rates, moduli, tail bounds, or finite-cover witnesses."
        )
    if BRIDGE_RE.search(text):
        return (
            "Replace the route by source rows, target rows, cut-rank, and an elimination "
            "plan for the intermediate carrier."
        )
    if EQUALITY_RE.search(text):
        return (
            "Replace loose sameness by a declared equality kind plus the two displayed "
            "directions or an explicit one-way interpretation boundary."
        )
    if EXISTENCE_RE.search(text):
        return (
            "Replace existence by a finite witness extractor or keep it in a nonconstructive "
            "review layer."
        )
    return (
        "Ask for the smallest local BEDC implication over existing carrier, classifier, "
        "ledger, NameCert, history, observation, termination, and certificate rows."
    )


def _logic_fields(title: str, claim: str) -> dict[str, str]:
    text = f"{title}. {claim}"
    is_analysis = bool(ANALYSIS_RE.search(text))
    is_bridge = bool(BRIDGE_RE.search(text))
    is_equal = bool(EQUALITY_RE.search(text))
    is_exist = bool(EXISTENCE_RE.search(text))
    budget = "B2_rate_or_modulus" if is_analysis else "B0_finite_witness"
    return {
        "axiom_budget": budget,
        "strength_level": budget,
        "budget_reason": (
            "The plain reading only permits displayed rate/modulus/tail or finite boundary rows."
            if is_analysis
            else "The plain reading is restricted to finite displayed rows in an existing BEDC chapter."
        ),
        "existence_mode": "constructive_witness" if is_exist else "none",
        "witness_extractor": (
            "Project the finite carrier, classifier, ledger, or NameCert row named by the target chapter."
            if is_exist
            else ""
        ),
        "cut_rank": "1" if is_bridge else "0",
        "elimination_plan": (
            "Eliminate the intermediate route by projecting the displayed source rows, target rows, and certificate rows; reject unlisted coordinates."
            if is_bridge
            else "No bridge carrier is introduced; the statement remains an existing-chapter local implication."
        ),
        "equality_kind": "equivalent" if is_equal else "none",
        "interpretation_kind": "interpretation" if is_bridge else "none",
        "resource_trace": "Consumes only the named local rows; no external source path is a resource.",
        "dependency_trace": "Depends only on displayed BEDC-local labels selected by the landing gate.",
        "rate_modulus_surface": (
            "Expose rate, modulus, finite-cover, tail-bound, boundary, or readout rows before writeback."
            if is_analysis
            else ""
        ),
        "oracle_mode": "rewrite_to_packet",
    }


def _split_candidates(title: str, claim: str, target: str) -> list[dict[str, Any]]:
    fields = _logic_fields(title, claim)
    base_inputs = [target] if target else []
    text = f"{title}. {claim}"
    candidates: list[dict[str, Any]] = []
    if BRIDGE_RE.search(text):
        candidates.append(
            {
                "title": _clean(f"{title} bridge elimination boundary", TITLE_MAX),
                "claim": "Show that the proposed route is either eliminated by displayed source and target rows or remains a recorded one-way boundary.",
                "landing_kind": "existing_chapter_obligation",
                "local_inputs": base_inputs,
                **fields,
            }
        )
    if EQUALITY_RE.search(text):
        candidates.append(
            {
                "title": _clean(f"{title} equality kind boundary", TITLE_MAX),
                "claim": "Classify the proposed sameness as definitional equality, equivalence, mirror, bisimulation, or one-way interpretation before any merge.",
                "landing_kind": "existing_chapter_ledger_row",
                "local_inputs": base_inputs,
                **fields,
            }
        )
    if EXISTENCE_RE.search(text):
        candidates.append(
            {
                "title": _clean(f"{title} witness extractor boundary", TITLE_MAX),
                "claim": "Name the finite witness extractor or keep the existence claim outside constructive BEDC writeback.",
                "landing_kind": "existing_chapter_obligation",
                "local_inputs": base_inputs,
                **fields,
            }
        )
    if ANALYSIS_RE.search(text):
        candidates.append(
            {
                "title": _clean(f"{title} rate modulus readout boundary", TITLE_MAX),
                "claim": "Replace the analytic or geometric assertion by displayed rate, modulus, tail, finite-cover, boundary, or readout rows.",
                "landing_kind": "existing_chapter_lemma",
                "local_inputs": base_inputs,
                **fields,
            }
        )
    if not candidates:
        candidates.append(
            {
                "title": _clean(f"{title} local BEDC row boundary", TITLE_MAX),
                "claim": "Re-express the claim as the smallest implication over displayed BEDC carrier, classifier, ledger, history, observation, termination, and certificate rows.",
                "landing_kind": "existing_chapter_lemma",
                "local_inputs": base_inputs,
                **fields,
            }
        )
    return candidates[:4]


def _decision(
    record: dict[str, Any],
    title: str,
    claim: str,
    safe_inputs: list[str],
    target: str,
) -> tuple[str, str, str, list[str]]:
    text = f"{title}. {claim} {record.get('reason') or ''} {' '.join(_as_list(record.get('reasons')))}"
    risk_flags: list[str] = []
    if SOURCE_AUTOMATH_RE.search(text):
        risk_flags.append("external_signal_metadata_only")
    if any(VISION_PATH_RE.search(p) for p in _as_list(record.get("local_inputs"))):
        risk_flags.append("vision_inspiration_only")
    if TOO_BROAD_RE.search(text):
        risk_flags.append("too_broad_requires_split")

    reason = _clean(record.get("reason") or " ".join(_as_list(record.get("reasons"))), 400)
    if REJECT_RE.search(reason):
        return "reject", f"Hard pre-gate reason remains valid for review: {reason}", "none", risk_flags
    if not safe_inputs and not target:
        return "hold", "No BEDC-native landing file has been selected yet.", "none", risk_flags
    if HOLD_RE.search(reason) or risk_flags or TOO_BROAD_RE.search(text):
        return "split", "Promising or broad item must be split into minimal BEDC-native obligations before BOARD.", "existing_chapter_obligation", risk_flags

    probe = {
        "title": title,
        "claim": claim,
        "landing_kind": "existing_chapter_lemma",
        **_logic_fields(title, claim),
    }
    gate = logic_packet_gate.validate_logic_packet(probe)
    if gate.ok:
        return "keep", "Plain logic packet is locally shaped; final writeback gate still required.", "existing_chapter_lemma", risk_flags
    return "split", "Logic packet still needs smaller surfaces: " + "; ".join(gate.reasons), "existing_chapter_obligation", risk_flags


def review_record(source_event: str, record: dict[str, Any], files: dict[str, dict[str, Any]]) -> dict[str, Any]:
    title = _clean(record.get("title"), TITLE_MAX)
    claim = _claim(record)
    inputs = _as_list(record.get("local_inputs"))
    safe_inputs = _safe_landing_inputs(inputs, files)
    target = safe_inputs[0] if safe_inputs else _fallback_landing(files, f"{title} {claim}", inputs)
    decision, decision_reason, landing_kind, risk_flags = _decision(record, title, claim, safe_inputs, target)
    missing_support: list[str] = []
    if not target:
        missing_support.append("bedc_native_landing")
    if SOURCE_AUTOMATH_RE.search(f"{title} {claim}"):
        missing_support.append("local_rederivation_from_bedc_rows")
    if any(VISION_PATH_RE.search(p) for p in inputs):
        missing_support.append("vision_to_existing_chapter_target")

    source_path = str(record.get("source_path") or "")
    source_id = str(record.get("candidate_id") or _source_id(source_event, title, claim, source_path))
    split = _split_candidates(title, claim, target) if decision in {"keep", "split", "needs_oracle"} else []
    do_not_write_reason = ""
    if decision != "keep":
        do_not_write_reason = "Review layer is holding or splitting the item before executable BOARD/writeback."
    elif risk_flags:
        do_not_write_reason = "Risk flags require final writeback gate confirmation."
    return {
        "ts": now_iso(),
        "source_event": source_event,
        "source_id": source_id,
        "source_path": source_path,
        "title": title,
        "raw_claim": claim,
        "plain_philosophy": _plain_philosophy(title, claim),
        "plain_math": _plain_math(title, claim),
        "bedc_reading": (
            "Candidate may only land as a BEDC-native minimal lemma, obligation, "
            "ledger row, obstruction, or refusal over displayed local rows."
        ),
        "decision": decision,
        "decision_reason": decision_reason,
        "minimal_landing_kind": landing_kind,
        "target_file": target,
        "split_candidates": split,
        "missing_support": missing_support,
        "risk_flags": risk_flags,
        "do_not_write_reason": do_not_write_reason,
    }


def write_reviews(reviews: list[dict[str, Any]]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with REVIEWS_JSONL.open("a", encoding="utf-8") as f:
        for review in reviews:
            f.write(json.dumps(review, ensure_ascii=False, sort_keys=True) + "\n")
    REVIEWS_LATEST.write_text(render_latest(reviews), encoding="utf-8")


def render_latest(reviews: list[dict[str, Any]]) -> str:
    counts: dict[str, int] = {}
    for review in reviews:
        key = str(review.get("decision") or "unknown")
        counts[key] = counts.get(key, 0) + 1
    lines = [
        "# plain math review latest",
        "",
        f"- checked_at: {now_iso()}",
        f"- reviews: {len(reviews)}",
        f"- decisions: {_render_counts(counts)}",
        "",
        "## Keep / Split",
        "",
    ]
    for review in [r for r in reviews if r.get("decision") in {"keep", "split"}][:24]:
        lines.append(
            f"- {review.get('title')} [{review.get('decision')}] -> "
            f"{review.get('minimal_landing_kind')} `{review.get('target_file') or 'unselected'}`"
        )
    lines.extend(["", "## Hold / Reject", ""])
    for review in [r for r in reviews if r.get("decision") not in {"keep", "split"}][:24]:
        lines.append(f"- {review.get('title')} [{review.get('decision')}]: {review.get('decision_reason')}")
    return "\n".join(lines).rstrip() + "\n"


def _render_counts(counts: dict[str, int]) -> str:
    if not counts:
        return "none"
    return ", ".join(f"{key}={counts[key]}" for key in sorted(counts))


def load_recent_reviews(limit: int = 200) -> list[dict[str, Any]]:
    return _read_jsonl_tail(REVIEWS_JSONL, limit)


def candidate_supply_from_reviews(limit: int = 20) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for review in load_recent_reviews(max(limit * 4, 40)):
        if review.get("decision") not in {"keep", "split"}:
            continue
        for candidate in review.get("split_candidates") or []:
            if not isinstance(candidate, dict):
                continue
            if not _as_list(candidate.get("local_inputs")):
                continue
            title = str(candidate.get("title") or "").strip()
            key = title.lower()
            if not title or key in seen:
                continue
            seen.add(key)
            enriched = dict(candidate)
            enriched["source"] = "plain_math_review"
            enriched["fit_score"] = int(enriched.get("fit_score") or 8)
            enriched["novelty"] = int(enriched.get("novelty") or 7)
            enriched.setdefault(
                "rationale",
                (
                    f"Derived from plain_math_review source={review.get('source_event')} "
                    f"decision={review.get('decision')}; external metadata and vision prose "
                    "are not paper evidence."
                ),
            )
            enriched.setdefault("tastegate_mode", "existing_chapter")
            out.append(enriched)
            if len(out) >= limit:
                return out
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC plain philosophy/plain math candidate review")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--json", action="store_true", help="Print reviews as JSON.")
    args = parser.parse_args()

    files = _paper_files()
    sources = collect_sources(args.limit)
    reviews = [review_record(source_event, record, files) for source_event, record in sources]
    write_reviews(reviews)
    if args.json:
        print(json.dumps({"reviews": reviews}, ensure_ascii=False, indent=2))
    else:
        counts: dict[str, int] = {}
        for review in reviews:
            decision = str(review.get("decision") or "unknown")
            counts[decision] = counts.get(decision, 0) + 1
        print(
            f"plain_math_review reviews={len(reviews)} "
            f"decisions={_render_counts(counts)} "
            f"latest={REVIEWS_LATEST.relative_to(REPO_ROOT)}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

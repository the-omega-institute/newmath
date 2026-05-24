#!/usr/bin/env python3
"""Codex research lane for BEDC candidate supply.

This lane is a candidate factory, not a paper writer.  It gathers deterministic
gap candidates, enriches them with the logic packet contract, pre-screens with
local gates, and writes research packets for the main supervisor to absorb.
With --append it may route packets through the shared board_spawn intake, but
the default mode never edits BOARD or paper files.
"""

from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import board_archive
import burden_candidate_miner
import candidate_substance
import candidate_inbox
import logic_packet_gate
import paper_gap_scanner
import paper_index
import plain_math_review
import structural_relation_miner

from dispatch_bedc_target import REPO_ROOT, SCRIPT_DIR


STATE_DIR = SCRIPT_DIR / "state"
RESEARCH_JSONL = STATE_DIR / "research_candidates.jsonl"
RESEARCH_LATEST = STATE_DIR / "research_candidates_latest.md"
ORACLE_ESCALATIONS = STATE_DIR / "research_oracle_escalations.jsonl"
BOARD_SPAWN_LATEST = STATE_DIR / "research_board_spawn_latest.json"

DEFAULT_LIMIT = 20
INBOX_TAIL = 800
DEFAULT_FIT_THRESHOLD = 7
DEFAULT_NOVELTY_THRESHOLD = 6

ANALYSIS_RE = re.compile(
    r"\b(cauchy|completion|compact|continuous|continuity|limit|converge|modulus|rate|tail|dyadic)\b",
    re.IGNORECASE,
)
BRIDGE_RE = re.compile(
    r"\b(bridge|transport|composition|compose|handoff|route|readback|factor|continuation)\b",
    re.IGNORECASE,
)
EQUALITY_RE = re.compile(
    r"\b(equal|same|equivalent|equivalence|isomorphic|bisimilar|mirror|correspond)\b",
    re.IGNORECASE,
)
EXISTENCE_RE = re.compile(
    r"\b(exists?|there exists|admits?|has a|has an|witness|inhabited)\b",
    re.IGNORECASE,
)
ORACLE_WORTHY_RE = re.compile(
    r"\b(obstruction|counterexample|classification|uniqueness|non[- ]?escape|impossib|failure|deep)\b",
    re.IGNORECASE,
)
INBOX_RECOVER_EVENTS = {
    "received",
    "pre_gate_accept",
    "pre_gate_hold",
    "held_for_refinement",
}
INBOX_HARD_REJECT_EVENTS = {"pre_gate_reject", "rejected"}
INBOX_SOFT_REJECT_SOURCES = {
    "oracle",
    "oracle_board_refill",
    "paper_review",
    "paper_gap_scanner",
    "research_lane:paper_gap_scanner",
}
BLOCKED_LANDING_PATH_RE = re.compile(
    r"^papers/bedc/parts/(?:conjectures|visions)/",
    re.IGNORECASE,
)
PROSE_TITLE_RE = re.compile(r"[.;:]\s*$|\\(?:label|begin|chapter|section)\b", re.IGNORECASE)
SOURCE_MARKER_RE = re.compile(
    r"\\(?:begin|end|label|input|include|leanchecked|leantarget|leanvariant|leandef)\b",
    re.IGNORECASE,
)
UNRECOVERABLE_REASON_RE = re.compile(
    r"already_in_paper|duplicate_title|forbidden_axis|out_of_scope|"
    r"predicted_label_collision|conjecture_fallback",
    re.IGNORECASE,
)
SOFT_RECOVERABLE_REASON_RE = re.compile(
    r"below_fit_threshold|below_novelty_threshold|too_weak|"
    r"logic_packet_gate:|missing_logic_budget|missing_local_input|"
    r"missing_local_inputs|hub_only_landing|no_indexed_safe_landing|"
    r"non_paper_local_input|"
    r"external_signal_missing_landing_kind|external_signal_missing_chapter_worthiness",
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


def _paper_files() -> dict[str, dict[str, Any]]:
    try:
        idx = paper_index.load_or_build()
    except Exception:
        return {}
    return {str(item.get("file") or ""): item for item in idx.get("files") or []}


def _line_count(rel: str, files: dict[str, dict[str, Any]]) -> int:
    info = files.get(rel) or {}
    try:
        return int(info.get("line_count") or info.get("lines") or 0)
    except (TypeError, ValueError):
        return 0


def _safe_inputs(inputs: list[str], files: dict[str, dict[str, Any]]) -> tuple[list[str], list[str]]:
    safe: list[str] = []
    reasons: list[str] = []
    for rel in inputs:
        if not rel.startswith("papers/bedc/parts/"):
            reasons.append(f"non_paper_local_input:{rel}")
            continue
        if BLOCKED_LANDING_PATH_RE.search(rel):
            reasons.append(f"inspiration_only_not_board_landing:{rel}")
            continue
        path = REPO_ROOT / rel
        if not path.exists():
            reasons.append(f"missing_local_input:{rel}")
            continue
        info = files.get(rel) or {}
        if info.get("hub_like"):
            reasons.append(f"hub_like_input:{rel}")
            continue
        line_count = _line_count(rel, files)
        if line_count >= 760:
            reasons.append(f"near_line_cap:{rel}:{line_count}")
            continue
        safe.append(rel)
    if not safe:
        reasons.append("no_safe_landing_input")
    return safe, reasons


def _landing_words(candidate: dict[str, Any]) -> set[str]:
    text = _text(candidate)
    return {
        word.lower()
        for word in re.findall(r"[A-Za-z][A-Za-z0-9]{4,}", text)
        if word.lower()
        not in {
            "candidate",
            "chapter",
            "local",
            "claim",
            "surface",
            "boundary",
            "displayed",
            "existing",
        }
    }


def _fallback_safe_inputs(
    candidate: dict[str, Any],
    original_inputs: list[str],
    files: dict[str, dict[str, Any]],
    *,
    limit: int = 2,
) -> list[str]:
    """Pick smaller BEDC-native landing files for held/refinement packets.

    The final board_spawn/writeback gates still decide whether the candidate is
    executable.  This only prevents useful held packets from looping forever
    on a near-800-line file when an adjacent concrete body file is available.
    """

    words = _landing_words(candidate)
    preferred_dirs = {
        str(Path(rel).parent)
        for rel in original_inputs
        if rel.startswith("papers/bedc/parts/")
    }
    scored: list[tuple[int, int, str]] = []
    for rel, info in files.items():
        if not rel.startswith("papers/bedc/parts/"):
            continue
        if BLOCKED_LANDING_PATH_RE.search(rel):
            continue
        if info.get("hub_like"):
            continue
        path = REPO_ROOT / rel
        if not path.exists():
            continue
        line_count = _line_count(rel, files)
        if line_count >= 720:
            continue
        hay = " ".join([rel, str(info.get("title") or "")]).lower()
        score = sum(1 for word in words if word in hay)
        if str(Path(rel).parent) in preferred_dirs:
            score += 4
        if score:
            scored.append((-score, line_count, rel))
    scored.sort()
    return [rel for _neg_score, _line_count, rel in scored[:limit]]


def _text(candidate: dict[str, Any]) -> str:
    return " ".join(
        str(candidate.get(k) or "")
        for k in ("title", "claim", "concrete_claim", "rationale")
    )


def _set_missing(out: dict[str, Any], key: str, value: Any) -> None:
    if out.get(key) in (None, ""):
        out[key] = value


def _fill_logic_packet(candidate: dict[str, Any]) -> dict[str, Any]:
    out = dict(candidate)
    text = _text(out)
    is_analysis = bool(ANALYSIS_RE.search(text))
    is_bridge = bool(BRIDGE_RE.search(text))
    is_equality = bool(EQUALITY_RE.search(text))
    is_existence = bool(EXISTENCE_RE.search(text))

    budget = str(out.get("axiom_budget") or "").strip()
    if not budget:
        budget = "B2_rate_or_modulus" if is_analysis else "B0_finite_witness"
    _set_missing(out, "axiom_budget", budget)
    _set_missing(out, "strength_level", budget)
    _set_missing(
        out,
        "budget_reason",
        (
            "The candidate is restricted to displayed rate/modulus/tail rows "
            "and does not require countable choice."
            if budget == "B2_rate_or_modulus"
            else "The candidate is a finite displayed-row implication over an existing BEDC packet."
        ),
    )
    _set_missing(out, "existence_mode", "constructive_witness" if is_existence else "none")
    if is_existence:
        _set_missing(
            out,
            "witness_extractor",
            "Project the displayed carrier, ledger, or NameCert row named in local_inputs; the witness is that finite row packet.",
        )
    else:
        _set_missing(out, "witness_extractor", "")
    _set_missing(out, "cut_rank", "1" if is_bridge else "0")
    if is_bridge:
        _set_missing(
            out,
            "elimination_plan",
            "Eliminate the intermediate route by projecting the displayed source, route, and consumer rows; reject unlisted coordinates.",
        )
    else:
        _set_missing(out, "elimination_plan", "No bridge carrier is introduced; the statement stays in the existing chapter surface.")
    _set_missing(out, "equality_kind", "equivalent" if is_equality else "none")
    _set_missing(out, "interpretation_kind", "interpretation" if is_bridge else "none")
    _set_missing(
        out,
        "resource_trace",
        "Consumes only the listed local_inputs rows and the displayed BHist/hsame/Cont/Pkg/NameCert resources.",
    )
    _set_missing(
        out,
        "dependency_trace",
        "Depends only on labels and carrier rows already present in the listed local_inputs; no ambient source repository is used.",
    )
    _set_missing(
        out,
        "rate_modulus_surface",
        (
            "Uses the displayed rate/modulus/tail/schedule/window rows named by the local chapter."
            if is_analysis
            else ""
        ),
    )
    _set_missing(out, "oracle_mode", "candidate_generation")
    _set_missing(out, "landing_kind", "existing_chapter_lemma")
    _set_missing(out, "tastegate_mode", "existing_chapter")
    return out


def _packet(candidate: dict[str, Any], *, source: str, files: dict[str, dict[str, Any]]) -> dict[str, Any]:
    enriched = _fill_logic_packet(candidate)
    original_inputs = _as_list(enriched.get("local_inputs"))
    inputs, input_reasons = _safe_inputs(original_inputs, files)
    if not inputs and any(
        reason.startswith(("near_line_cap:", "no_safe_landing_input", "hub_like_input:"))
        for reason in input_reasons
    ):
        fallback_inputs = _fallback_safe_inputs(enriched, original_inputs, files)
        if fallback_inputs:
            inputs = fallback_inputs
            input_reasons = [
                f"rerouted_landing_from:{','.join(original_inputs) or 'none'}",
            ]
    enriched["local_inputs"] = inputs
    if "claim" not in enriched and enriched.get("concrete_claim"):
        enriched["claim"] = enriched.get("concrete_claim")
    gate = logic_packet_gate.validate_logic_packet(enriched)
    title = str(enriched.get("title") or "").strip()
    title_key = title.lower()
    existing_titles = board_archive.existing_target_titles(include_archive=True)
    reasons = list(input_reasons)
    if reasons and all(reason.startswith("rerouted_landing_from:") for reason in reasons):
        reasons = []
    if title_key in existing_titles:
        reasons.append("duplicate_title_in_board_or_archive")
    if PROSE_TITLE_RE.search(title):
        reasons.append("prose_or_structural_title")
    if SOURCE_MARKER_RE.search(str(enriched.get("claim") or "")):
        reasons.append("source_marker_in_claim")
    if SOURCE_MARKER_RE.search(str(enriched.get("concrete_claim") or "")):
        reasons.append("source_marker_in_concrete_claim")
    if any(BLOCKED_LANDING_PATH_RE.search(rel) for rel in inputs):
        reasons.append("review_lane_input_not_board_landing")
    score_warnings: list[str] = []
    if _score(enriched, "fit_score") < DEFAULT_FIT_THRESHOLD:
        score_warnings.append(f"below_fit_threshold:{_score(enriched, 'fit_score')}")
    if _score(enriched, "novelty") < DEFAULT_NOVELTY_THRESHOLD:
        score_warnings.append(f"below_novelty_threshold:{_score(enriched, 'novelty')}")
    if not gate.ok:
        reasons.extend("logic_packet_gate:" + reason for reason in gate.reasons)
    substance_rejection = candidate_substance.substance_rejection(enriched)
    if substance_rejection:
        reasons.append(substance_rejection)
    text = _text(enriched)
    oracle_recommended = bool(ORACLE_WORTHY_RE.search(text)) and not reasons
    # This is an escalation hint, not a routing decision.  BOARD targets still
    # run through Codex deep reasoning first; oracle receives them only if
    # Codex names a concrete missing structure or exhausts the local route.
    if oracle_recommended:
        enriched["oracle_mode"] = "proof_search"
    _set_missing(enriched, "difficulty", _difficulty(enriched))
    _set_missing(enriched, "quality_score", _quality_score(enriched, reasons))
    _set_missing(enriched, "selection_rank", "")
    return {
        "ts": now_iso(),
        "source": source,
        "status": "ready" if not reasons else "blocked",
        "reasons": reasons,
        "warnings": score_warnings,
        "oracle_recommended": oracle_recommended,
        "candidate": enriched,
    }


def _quality_score(candidate: dict[str, Any], reasons: list[str]) -> dict[str, int]:
    fit = _score(candidate, "fit_score")
    novelty = _score(candidate, "novelty")
    safe_landing = bool(candidate.get("local_inputs")) and not reasons
    text = _text(candidate).lower()
    return {
        "verifiability": 3 if safe_landing else 0,
        "locality": 2 if safe_landing else 0,
        "downstream_use": 2 if fit >= 8 else 1 if fit >= DEFAULT_FIT_THRESHOLD else 0,
        "line_cap_safety": 2 if safe_landing else 0,
        "nontriviality": 2 if novelty >= 8 else 1 if novelty >= DEFAULT_NOVELTY_THRESHOLD else 0,
        "cross_chapter_unification": 2 if len(_as_list(candidate.get("local_inputs"))) >= 3 else 1 if "sibling" in text else 0,
    }


def _difficulty(candidate: dict[str, Any]) -> str:
    fit = _score(candidate, "fit_score")
    novelty = _score(candidate, "novelty")
    text = _text(candidate)
    if novelty >= 8 and (ORACLE_WORTHY_RE.search(text) or BRIDGE_RE.search(text)):
        return "high"
    if fit >= 8 and novelty >= 7:
        return "medium"
    return "low"


def collect_candidates(limit: int) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    source_limit = max(limit * 4, 40)

    candidates.extend(burden_candidate_miner.generate_candidates(limit=source_limit))
    gap_candidates = paper_gap_scanner.generate_candidates(limit=source_limit)
    candidates.extend(gap_candidates)
    for cand in candidates:
        if str(cand.get("source") or "") == "paper_gap_scanner":
            cand["source"] = "research_lane:paper_gap_scanner"
        else:
            cand.setdefault("source", "research_lane:paper_gap_scanner")

    candidates.extend(structural_relation_miner.generate_candidates(limit=source_limit))
    candidates.extend(_candidate_inbox_candidates(source_limit))
    candidates.extend(plain_math_review.candidate_supply_from_reviews(source_limit))
    return _dedupe_candidates(candidates)[:limit]


def _candidate_inbox_candidates(limit: int) -> list[dict[str, Any]]:
    path = candidate_inbox.INBOX_PATH
    if not path.exists() or limit <= 0:
        return []
    rows: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()[-INBOX_TAIL:]
    except OSError:
        return []
    blocked_titles = _blocked_inbox_titles(lines)
    seen: set[str] = set()
    for line in reversed(lines):
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        event = str(rec.get("event") or "")
        reason = str(rec.get("reason") or "")
        if event not in INBOX_RECOVER_EVENTS and not _soft_recoverable_reject(rec):
            continue
        title = str(rec.get("title") or "").strip()
        claim = str(rec.get("claim") or "").strip()
        if not title or not claim:
            continue
        key = title.lower()
        if key in seen or key in blocked_titles:
            continue
        seen.add(key)
        candidate = {
            key_: rec.get(key_)
            for key_ in (
                "title",
                "claim",
                "local_inputs",
                "fit_score",
                "novelty",
                "landing_kind",
                "tastegate_mode",
                "axiom_budget",
                "strength_level",
                "budget_reason",
                "witness_extractor",
                "existence_mode",
                "cut_rank",
                "elimination_plan",
                "equality_kind",
                "interpretation_kind",
                "resource_trace",
                "dependency_trace",
                "rate_modulus_surface",
                "oracle_mode",
                "difficulty",
                "quality_score",
                "selection_rank",
            )
        }
        if _soft_recoverable_reject(rec):
            candidate["fit_score"] = max(_score(candidate, "fit_score"), DEFAULT_FIT_THRESHOLD)
            candidate["novelty"] = max(_score(candidate, "novelty"), DEFAULT_NOVELTY_THRESHOLD)
            candidate["landing_kind"] = candidate.get("landing_kind") or "existing_chapter_obligation"
            candidate["tastegate_mode"] = candidate.get("tastegate_mode") or "existing_chapter"
        candidate["source"] = "research_lane:candidate_inbox"
        candidate["rationale"] = (
            f"Recovered from candidate_inbox event={event} "
            f"source={rec.get('source')} reason={reason or 'none'} at {rec.get('ts')}. "
            "Research lane revalidates local_inputs and logic packet fields "
            "before any BOARD intake; soft rejected inputs are re-read as "
            "plain BEDC-native obligations rather than accepted as-is."
        )
        rows.append(candidate)
        if len(rows) >= limit:
            break
    return rows


def _soft_recoverable_reject(rec: dict[str, Any]) -> bool:
    event = str(rec.get("event") or "")
    if event not in INBOX_HARD_REJECT_EVENTS:
        return False
    source = str(rec.get("source") or "")
    if source not in INBOX_SOFT_REJECT_SOURCES:
        return False
    reason = str(rec.get("reason") or "")
    if not reason or UNRECOVERABLE_REASON_RE.search(reason):
        return False
    if not SOFT_RECOVERABLE_REASON_RE.search(reason):
        return False
    if candidate_substance.is_substance_rejection(reason):
        return False
    if "below_fit_threshold:0" in reason and source not in {"oracle", "oracle_board_refill", "paper_review"}:
        return False
    title = str(rec.get("title") or "").strip()
    claim = str(rec.get("claim") or "").strip()
    inputs = _as_list(rec.get("local_inputs"))
    if len(title) < 8 or len(claim) < 40:
        return False
    if not any(rel.startswith("papers/bedc/parts/") for rel in inputs):
        return False
    return True


def _score(candidate: dict[str, Any], key: str) -> int:
    try:
        return int(candidate.get(key) or 0)
    except (TypeError, ValueError):
        return 0


def _blocked_inbox_titles(lines: list[str]) -> set[str]:
    blocked: set[str] = set()
    for line in lines:
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        event = str(rec.get("event") or "")
        if event == "promoted_to_board":
            title = str(rec.get("title") or "").strip().lower()
            if title:
                blocked.add(title)
            continue
        if event not in INBOX_HARD_REJECT_EVENTS:
            continue
        if _soft_recoverable_reject(rec):
            continue
        reason = str(rec.get("reason") or "")
        if not UNRECOVERABLE_REASON_RE.search(reason):
            continue
        title = str(rec.get("title") or "").strip().lower()
        if title:
            blocked.add(title)
    return blocked


def _dedupe_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for candidate in candidates:
        title = str(candidate.get("title") or "").strip().lower()
        if not title or title in seen:
            continue
        seen.add(title)
        out.append(candidate)
    return out


def write_outputs(packets: list[dict[str, Any]]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with RESEARCH_JSONL.open("a", encoding="utf-8") as f:
        for packet in packets:
            f.write(json.dumps(packet, ensure_ascii=False, sort_keys=True) + "\n")
    with ORACLE_ESCALATIONS.open("a", encoding="utf-8") as f:
        for packet in packets:
            if packet.get("oracle_recommended"):
                f.write(json.dumps(packet, ensure_ascii=False, sort_keys=True) + "\n")
    RESEARCH_LATEST.write_text(render_latest(packets), encoding="utf-8")


def render_latest(packets: list[dict[str, Any]]) -> str:
    ready = [p for p in packets if p.get("status") == "ready"]
    blocked = [p for p in packets if p.get("status") != "ready"]
    oracle = [p for p in packets if p.get("oracle_recommended")]
    ready_budget = _count_field(ready, "axiom_budget")
    ready_difficulty = _count_field(ready, "difficulty")
    ready_oracle_mode = _count_field(ready, "oracle_mode")
    lines = [
        "# research candidate lane latest",
        "",
        f"- checked_at: {now_iso()}",
        f"- packets: {len(packets)}",
        f"- ready: {len(ready)}",
        f"- blocked: {len(blocked)}",
        f"- oracle_recommended_after_codex: {len(oracle)}",
        f"- ready_budget: {_render_counts(ready_budget)}",
        f"- ready_difficulty: {_render_counts(ready_difficulty)}",
        f"- ready_oracle_mode: {_render_counts(ready_oracle_mode)}",
        "",
        "## Ready",
        "",
    ]
    for packet in ready[:20]:
        c = packet["candidate"]
        lines.append(
            f"- {c.get('title')} [{c.get('axiom_budget')}, oracle_after_codex={packet.get('oracle_recommended')}]"
        )
    lines.extend(["", "## Blocked", ""])
    for packet in blocked[:20]:
        c = packet["candidate"]
        lines.append(f"- {c.get('title')}: {'; '.join(packet.get('reasons') or [])}")
    return "\n".join(lines).rstrip() + "\n"


def _count_field(packets: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for packet in packets:
        candidate = packet.get("candidate")
        if not isinstance(candidate, dict):
            continue
        value = str(candidate.get(field) or "unspecified").strip() or "unspecified"
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def _render_counts(counts: dict[str, int]) -> str:
    if not counts:
        return "none"
    return ", ".join(f"{key}={value}" for key, value in counts.items())


def append_ready(packets: list[dict[str, Any]]) -> object:
    import board_spawn

    ready = [p["candidate"] for p in packets if p.get("status") == "ready"]
    return board_spawn.spawn_from_candidates(codex_candidates=ready, oracle_candidates=[])


def write_board_spawn_status(result: object, *, ready_count: int) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    error = str(getattr(result, "error", "") or "")
    record = {
        "ts": now_iso(),
        "ok": bool(getattr(result, "ok", False)),
        "ready_count": ready_count,
        "accepted": len(getattr(result, "accepted", []) or []),
        "held": len(getattr(result, "held", []) or []),
        "rejected": len(getattr(result, "rejected", []) or []),
        "appended_ids": getattr(result, "appended_ids", []) or [],
        "error_kind": str(getattr(result, "error_kind", "") or ""),
        "error": " ".join(error.split())[:500],
    }
    BOARD_SPAWN_LATEST.write_text(
        json.dumps(record, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC codex research candidate lane")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--append", action="store_true", help="Route ready packets through shared board_spawn intake.")
    parser.add_argument("--json", action="store_true", help="Print packets as JSON.")
    args = parser.parse_args()

    files = _paper_files()
    raw = collect_candidates(args.limit)
    packets = [
        _packet(candidate, source=str(candidate.get("source") or "research_lane"), files=files)
        for candidate in raw
    ]
    write_outputs(packets)
    if args.json:
        print(json.dumps({"packets": packets}, ensure_ascii=False, indent=2))
    else:
        ready = sum(1 for p in packets if p.get("status") == "ready")
        oracle = sum(1 for p in packets if p.get("oracle_recommended"))
        print(
            f"research_lane packets={len(packets)} ready={ready} "
            f"oracle_recommended={oracle} latest={RESEARCH_LATEST.relative_to(REPO_ROOT)}"
        )
    if args.append:
        ready_count = sum(1 for p in packets if p.get("status") == "ready")
        result = append_ready(packets)
        write_board_spawn_status(result, ready_count=ready_count)
        error_kind = str(getattr(result, "error_kind", "") or "")
        error = str(getattr(result, "error", "") or "")
        error_summary = " ".join(error.split())[:300]
        print(
            "board_spawn "
            f"ok={getattr(result, 'ok', False)} "
            f"accepted={len(getattr(result, 'accepted', []) or [])} "
            f"rejected={len(getattr(result, 'rejected', []) or [])} "
            f"appended={getattr(result, 'appended_ids', [])}"
            + (f" error_kind={error_kind}" if error_kind else "")
            + (f" error={error_summary}" if error_summary else "")
        )
        return 0 if getattr(result, "ok", False) else 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

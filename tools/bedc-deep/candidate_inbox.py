#!/usr/bin/env python3
"""Runtime candidate inbox and deterministic pre-gate for BOARD candidates."""

from __future__ import annotations

import hashlib
import argparse
import json
import re
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

import board_archive
import candidate_substance
import paper_index
import verification_axis
from dispatch_bedc_target import REPO_ROOT, SCRIPT_DIR
from locks import file_lock


INBOX_PATH = SCRIPT_DIR / "state" / "candidate_inbox.jsonl"
FORBIDDEN_AXIS_RE = re.compile(
    r"closurestatus|theoryclosure|formalstatus|leantarget|leanchecked|"
    r"leanvariant|leansorry|leanstmt|leandef|marker-only|verification-axis|"
    r"chapter retirement|Lean[- ]target|lean4/|formal[- ]target|formal[- ]readiness|"
    r"single[-_ ]carrier[-_ ]alignment|taste[-_ ]gate|BEDC\.Derived\.",
    re.IGNORECASE,
)
NEGATED_FORBIDDEN_AXIS_RE = re.compile(
    r"\b(?:not|no|without|avoid(?:s|ing)?|exclud(?:e|es|ed|ing)|rather than|instead of)\b",
    re.IGNORECASE,
)
STRUCTURAL_TITLE_RE = re.compile(
    r"^\s*\\(?:label|begin|chapter|section|subsection|input|include)\b",
    re.IGNORECASE,
)
EXTERNAL_SIGNAL_RE = re.compile(
    r"Automath|automath|Bridge continuation target|Automath continuation|"
    r"bridge_consumption_mode|review_packets?|discovery_report|"
    r"external theorem signal|source theorem signal",
    re.IGNORECASE,
)
LANDING_KINDS = {
    "existing_chapter_lemma",
    "existing_chapter_obligation",
    "existing_chapter_ledger_row",
    "new_chapter",
    "reject",
}
LABEL_SLUG_RE = re.compile(r"[^a-z0-9]+")
LITERAL_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
STANDARD_LABEL_PREFIXES = ("sec", "subsec", "fact", "obs", "rmk", "thm", "lem", "prop", "cor", "def", "eq")
LINE_CAP = 800
FALLBACK_LINE_READ_BYTES = 100 * 1024
INSPIRATION_ONLY_PATH_RE = re.compile(
    r"^papers/bedc/parts/(?:visions|conjectures)/",
    re.IGNORECASE,
)
REFINABLE_REASON_RE = re.compile(
    r"missing_local_input|missing_local_inputs|no_indexed_safe_landing|"
    r"hub_only_landing|inspiration_only_not_board_landing|"
    r"logic_packet_gate:|missing_logic_budget|"
    r"existence_missing_|bridge_missing_|equality_missing_|"
    r"completion_missing_|external_signal_missing_landing_kind|"
    r"external_signal_landing_reject|external_signal_missing_chapter_worthiness|"
    r"too_weak|below_fit_threshold|below_novelty_threshold|"
    r"predicted_label_collision|non_paper_local_input",
    re.IGNORECASE,
)
HARD_REJECT_REASON_RE = re.compile(
    r"duplicate_title|structural_title|missing_title|missing_claim|"
    r"claim_too_short|forbidden_axis_or_marker_candidate|"
    r"conjecture_fallback_not_board_lane",
    re.IGNORECASE,
)


@dataclass
class ScreenResult:
    accepted: list[dict[str, Any]] = field(default_factory=list)
    rejected: list[dict[str, Any]] = field(default_factory=list)
    held: list[dict[str, Any]] = field(default_factory=list)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _as_list(value: Any) -> list[str]:
    if isinstance(value, list):
        return [str(v).strip() for v in value if str(v).strip()]
    if isinstance(value, str) and value.strip():
        return [value.strip()]
    return []


def _claim(candidate: dict[str, Any]) -> str:
    return str(
        candidate.get("claim")
        or candidate.get("concrete_claim")
        or candidate.get("problem")
        or ""
    ).strip()


def _has_forbidden_axis_marker(title: str, claim: str, rationale: str) -> bool:
    """Reject marker-axis targets without punishing negated evidence notes."""
    if verification_axis.has_verification_axis_surface(" ".join([title, claim])):
        return True
    if FORBIDDEN_AXIS_RE.search(" ".join([title, claim])):
        return True
    for segment in re.split(r"(?<=[.!?])\s+|\n+", rationale):
        if not FORBIDDEN_AXIS_RE.search(segment):
            continue
        if NEGATED_FORBIDDEN_AXIS_RE.search(segment):
            continue
        return True
    return False


def _is_conjecture_fallback(candidate: dict[str, Any]) -> bool:
    """Conjecture fallback is a review lane, not an executable BOARD lane."""
    tastegate_mode = str(candidate.get("tastegate_mode") or "").strip().lower()
    if tastegate_mode == "conjecture_fallback":
        return True
    value = str(candidate.get("conjecture_fallback") or "").strip().lower()
    if not value:
        return False
    if value in {"false", "no", "none", "n/a", "na", "0"}:
        return False
    return True


def _candidate_id(candidate: dict[str, Any], source: str) -> str:
    payload = {
        "source": source,
        "title": str(candidate.get("title", "")).strip().lower(),
        "claim": _claim(candidate).lower(),
        "local_inputs": _as_list(candidate.get("local_inputs")),
    }
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()
    return f"cand-{digest[:16]}"


def _record(event: str, candidate: dict[str, Any], source: str, **extra: Any) -> None:
    INBOX_PATH.parent.mkdir(parents=True, exist_ok=True)
    title = str(candidate.get("title", "")).strip()
    record = {
        "ts": _now_iso(),
        "event": event,
        "candidate_id": candidate.get("_candidate_id") or _candidate_id(candidate, source),
        "source": source,
        "title": title,
        "claim": _claim(candidate),
        "local_inputs": _as_list(candidate.get("local_inputs")),
        "fit_score": candidate.get("fit_score"),
        "novelty": candidate.get("novelty"),
        "landing_kind": candidate.get("landing_kind"),
        "tastegate_mode": candidate.get("tastegate_mode"),
        "carrier_surface": candidate.get("carrier_surface"),
        "classifier_surface": candidate.get("classifier_surface"),
        "nontrivial_witness_plan": candidate.get("nontrivial_witness_plan"),
        "field_faithful_plan": candidate.get("field_faithful_plan"),
        "structural_atomicity": candidate.get("structural_atomicity"),
        "falsifiable_prediction": candidate.get("falsifiable_prediction"),
        "independence_witness": candidate.get("independence_witness"),
        "ripeness_risk": candidate.get("ripeness_risk"),
        "conjecture_fallback": candidate.get("conjecture_fallback"),
        "axiom_budget": candidate.get("axiom_budget"),
        "strength_level": candidate.get("strength_level"),
        "budget_reason": candidate.get("budget_reason"),
        "witness_extractor": candidate.get("witness_extractor"),
        "existence_mode": candidate.get("existence_mode"),
        "cut_rank": candidate.get("cut_rank"),
        "elimination_plan": candidate.get("elimination_plan"),
        "equality_kind": candidate.get("equality_kind"),
        "interpretation_kind": candidate.get("interpretation_kind"),
        "resource_trace": candidate.get("resource_trace"),
        "dependency_trace": candidate.get("dependency_trace"),
        "rate_modulus_surface": candidate.get("rate_modulus_surface"),
        "oracle_mode": candidate.get("oracle_mode"),
        "difficulty": candidate.get("difficulty"),
        "quality_score": candidate.get("quality_score"),
        "selection_rank": candidate.get("selection_rank"),
        **extra,
    }
    with file_lock("candidate_inbox"):
        with INBOX_PATH.open("a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def is_refinable_reason(reason: str) -> bool:
    reason = str(reason or "")
    if not reason:
        return False
    if HARD_REJECT_REASON_RE.search(reason):
        return False
    return bool(REFINABLE_REASON_RE.search(reason))


def _paper_file_lookup() -> dict[str, dict[str, Any]]:
    index = paper_index.load_or_build()
    return {item.get("file", ""): item for item in index.get("files", [])}


def _paper_labels(file_lookup: dict[str, dict[str, Any]]) -> set[str]:
    labels: set[str] = set()
    try:
        for item in file_lookup.values():
            for rec in item.get("labels") or []:
                label = str(rec.get("label") or "").strip()
                if label:
                    labels.add(label)
    except Exception:
        return set()
    return labels


def _title_label_slug(title: str) -> str:
    return LABEL_SLUG_RE.sub("-", title.lower()).strip("-")


def _label_prefixes_for_inputs(
    inputs: list[str],
    file_lookup: dict[str, dict[str, Any]],
) -> tuple[str, ...]:
    prefixes: list[str] = []
    for rel in inputs:
        item = file_lookup.get(rel) or {}
        for rec in item.get("theorem_like_labels") or item.get("labels") or []:
            prefix = str(rec.get("prefix") or "").strip()
            if prefix in STANDARD_LABEL_PREFIXES and prefix not in prefixes:
                prefixes.append(prefix)
    for prefix in STANDARD_LABEL_PREFIXES:
        if prefix not in prefixes:
            prefixes.append(prefix)
    return tuple(prefixes)


def _predicted_label_collision(
    title: str,
    claim: str,
    rationale: str,
    inputs: list[str],
    file_lookup: dict[str, dict[str, Any]],
    existing_labels: set[str],
) -> str:
    if not existing_labels:
        return ""
    for text in (claim, rationale):
        for match in LITERAL_LABEL_RE.finditer(text):
            label = match.group(1).strip()
            if label in existing_labels:
                return label
    slug = _title_label_slug(title)
    if not slug:
        return ""
    for prefix in _label_prefixes_for_inputs(inputs, file_lookup):
        label = f"{prefix}:{slug}"
        if label in existing_labels:
            return label
    return ""


def _fallback_line_count(rel: str) -> int:
    path = (REPO_ROOT / rel).resolve()
    try:
        path.relative_to(REPO_ROOT)
    except ValueError:
        return 0
    try:
        with path.open("rb") as f:
            data = f.read(FALLBACK_LINE_READ_BYTES)
    except OSError:
        return 0
    return len(data.decode("utf-8", errors="replace").splitlines())


def _paper_line_count(rel: str, file_lookup: dict[str, dict[str, Any]]) -> int:
    info = file_lookup.get(rel) or {}
    for key in ("line_count", "lines"):
        value = info.get(key)
        if isinstance(value, int):
            return value
        try:
            return int(value)
        except (TypeError, ValueError):
            pass
    return _fallback_line_count(rel)


def _estimated_write_lines(claim: str) -> int:
    return max(120, len(claim) // 60)


def _predicted_line_cap_overflow(
    claim: str,
    inputs: list[str],
    file_lookup: dict[str, dict[str, Any]],
) -> str:
    estimate = _estimated_write_lines(claim)
    landing_inputs = [
        rel for rel in inputs
        if not (file_lookup.get(rel) or {}).get("hub_like")
    ]
    if not landing_inputs:
        return ""
    overflow: list[tuple[str, int]] = []
    for rel in landing_inputs:
        projected = _paper_line_count(rel, file_lookup) + estimate
        if projected >= LINE_CAP:
            overflow.append((rel, projected))
    if len(overflow) == len(landing_inputs):
        rel, projected = overflow[0]
        return f"predicted_line_cap_overflow:{rel}:{projected}"
    return ""


def _path_exists(rel: str) -> bool:
    path = (REPO_ROOT / rel).resolve()
    try:
        path.relative_to(REPO_ROOT)
    except ValueError:
        return False
    return path.exists()


def _score(candidate: dict[str, Any], key: str) -> int:
    try:
        return int(candidate.get(key, 0))
    except (TypeError, ValueError):
        return 0


def _rejection_reason(
    candidate: dict[str, Any],
    *,
    source: str,
    existing_titles: set[str],
    seen_titles: set[str],
    file_lookup: dict[str, dict[str, Any]],
    existing_labels: set[str],
    fit_threshold: int,
    novelty_threshold: int,
) -> str:
    title = str(candidate.get("title", "")).strip()
    claim = _claim(candidate)
    rationale = str(candidate.get("rationale", ""))
    inputs = _as_list(candidate.get("local_inputs"))

    if not title:
        return "missing_title"
    title_key = title.lower()
    if title_key in seen_titles:
        return "duplicate_title_in_batch"
    if title_key in existing_titles:
        return "duplicate_title_in_board_or_archive"
    if STRUCTURAL_TITLE_RE.search(title):
        return "structural_title"
    if not claim:
        return "missing_claim"
    if len(claim) < 30:
        return "claim_too_short"
    if _is_conjecture_fallback(candidate):
        return "conjecture_fallback_not_board_lane"
    if _has_forbidden_axis_marker(title, claim, rationale):
        return "forbidden_axis_or_marker_candidate"
    substance_rejection = candidate_substance.substance_rejection(candidate)
    if substance_rejection:
        return substance_rejection
    landing_kind = str(candidate.get("landing_kind") or "").strip()
    haystack = " ".join([title, claim, rationale, str(candidate.get("chapter_worthiness") or "")])
    if EXTERNAL_SIGNAL_RE.search(haystack):
        if not landing_kind:
            if source in {"codex", "oracle"}:
                landing_kind = "pending_judge_classification"
            else:
                return "external_signal_missing_landing_kind"
        if landing_kind != "pending_judge_classification" and landing_kind not in LANDING_KINDS:
            return f"external_signal_invalid_landing_kind:{landing_kind}"
        if landing_kind == "reject":
            return "external_signal_landing_reject"
        if landing_kind == "new_chapter":
            worthiness = str(candidate.get("chapter_worthiness") or "").strip()
            required = ("carrier", "classifier", "NameCert", "dependency", "downstream", "existing chapter")
            if len(worthiness) < 240 or any(term.lower() not in worthiness.lower() for term in required):
                return "external_signal_missing_chapter_worthiness"
            if inputs and any(p in {"papers/bedc/main.tex", "papers/bedc/preamble.tex"} for p in inputs):
                return "external_signal_new_chapter_not_allowed_on_board"
        elif any(p in {"papers/bedc/main.tex", "papers/bedc/preamble.tex"} for p in inputs):
            return "external_signal_existing_landing_main_or_preamble"
    if not inputs:
        return "missing_local_inputs"

    safe_landing = False
    for rel in inputs:
        if rel.startswith("lean4/"):
            return f"non_paper_local_input:{rel}"
        if not rel.startswith("papers/bedc/parts/"):
            return f"non_paper_local_input:{rel}"
        if INSPIRATION_ONLY_PATH_RE.search(rel):
            return f"inspiration_only_not_board_landing:{rel}"
        if not _path_exists(rel):
            return f"missing_local_input:{rel}"
        info = file_lookup.get(rel)
        if info and not info.get("hub_like"):
            safe_landing = True

    if not safe_landing:
        if any((file_lookup.get(rel) or {}).get("hub_like") for rel in inputs):
            return "hub_only_landing"
        return "no_indexed_safe_landing"

    overflow = _predicted_line_cap_overflow(claim, inputs, file_lookup)
    if overflow:
        return overflow

    collision = _predicted_label_collision(title, claim, rationale, inputs, file_lookup, existing_labels)
    if collision:
        return f"predicted_label_collision:{collision}"

    return ""


def screen_candidates(
    candidates: list[dict[str, Any]],
    *,
    source: str,
    fit_threshold: int,
    novelty_threshold: int,
) -> ScreenResult:
    """Record candidates in the runtime inbox and return those safe for judge."""

    result = ScreenResult()
    if not candidates:
        return result

    existing_titles = board_archive.existing_target_titles(include_archive=True)
    file_lookup = _paper_file_lookup()
    existing_labels = _paper_labels(file_lookup)
    seen_titles: set[str] = set()

    for raw in candidates:
        if not isinstance(raw, dict):
            continue
        cand = dict(raw)
        cand_source = str(cand.get("source") or source)
        cand["source"] = cand_source
        cand["_candidate_id"] = _candidate_id(cand, cand_source)
        if "claim" not in cand and "concrete_claim" in cand:
            cand["claim"] = cand.get("concrete_claim")
        _record("received", cand, cand_source)

        reason = _rejection_reason(
            cand,
            source=cand_source,
            existing_titles=existing_titles,
            seen_titles=seen_titles,
            file_lookup=file_lookup,
            existing_labels=existing_labels,
            fit_threshold=fit_threshold,
            novelty_threshold=novelty_threshold,
        )
        title_key = str(cand.get("title", "")).strip().lower()
        if reason:
            blocked = {**cand, "source": cand_source, "reason": reason}
            if is_refinable_reason(reason):
                result.held.append(blocked)
                _record("pre_gate_hold", blocked, cand_source, reason=reason)
            else:
                result.rejected.append(blocked)
                _record("pre_gate_reject", blocked, cand_source, reason=reason)
            continue
        seen_titles.add(title_key)
        accepted = {**cand, "source": cand_source}
        result.accepted.append(accepted)
        _record("pre_gate_accept", accepted, cand_source)

    return result


def record_board_promotions(candidates: list[dict[str, Any]], appended_ids: list[str], *, mode: str) -> None:
    for candidate, target_id in zip(candidates, appended_ids):
        source = str(candidate.get("source") or mode)
        _record("promoted_to_board", candidate, source, target_id=target_id, mode=mode)


def record_rejections(candidates: list[dict[str, Any]], *, mode: str) -> None:
    for candidate in candidates:
        source = str(candidate.get("source") or mode)
        reason = str(candidate.get("reason") or candidate.get("verdict_reason") or "")
        event = "held_for_refinement" if is_refinable_reason(reason) else "rejected"
        _record(event, candidate, source, reason=reason, mode=mode)


def _parse_record_ts(value: Any) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        ts = datetime.fromisoformat(text)
    except ValueError:
        return None
    if ts.tzinfo is None:
        return ts.replace(tzinfo=timezone.utc)
    return ts.astimezone(timezone.utc)


def stats(limit: int = 5000, *, since_hours: float = 0.0) -> dict[str, Any]:
    if not INBOX_PATH.exists():
        return {
            "events": 0,
            "sampled": 0,
            "windowed": 0,
            "latest_event_ts": None,
            "latest_event_age_seconds": None,
            "latest_event": None,
            "latest_by_source": {},
            "latest_by_source_sampled": {},
            "by_event": {},
        }
    lines = INBOX_PATH.read_text(encoding="utf-8", errors="replace").splitlines()
    tail = lines[-limit:] if limit > 0 else lines
    window_start: datetime | None = None
    if since_hours > 0:
        window_start = datetime.now(timezone.utc) - timedelta(hours=since_hours)
    by_event: dict[str, int] = {}
    by_rejection_reason: dict[str, int] = {}
    by_refinement_reason: dict[str, int] = {}
    by_logic_packet_reason: dict[str, int] = {}
    by_current_logic_packet_reason: dict[str, int] = {}
    by_rejection_source: dict[str, int] = {}
    by_source_reason: dict[str, dict[str, int]] = {}
    seen_rejection_keys: set[tuple[str, str]] = set()
    stale_logic_packet_rejections = 0
    by_current_forbidden_axis_reason: dict[str, int] = {}
    stale_forbidden_axis_rejections = 0
    windowed = 0
    latest_ts: datetime | None = None
    latest_event: dict[str, Any] | None = None
    latest_by_source: dict[str, tuple[datetime, dict[str, Any]]] = {}
    latest_by_source_sampled: dict[str, tuple[datetime, dict[str, Any]]] = {}
    for line in tail:
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        ts = _parse_record_ts(rec.get("ts"))
        if ts is not None and (latest_ts is None or ts > latest_ts):
            latest_ts = ts
            latest_event = {
                "event": rec.get("event"),
                "source": rec.get("source"),
                "title": rec.get("title"),
            }
        source_key = str(rec.get("source") or "unknown").strip() or "unknown"
        if ts is not None:
            current = latest_by_source_sampled.get(source_key)
            if current is None or ts > current[0]:
                latest_by_source_sampled[source_key] = (
                    ts,
                    {
                        "event": rec.get("event"),
                        "title": rec.get("title"),
                    },
                )
        if window_start is not None:
            if ts is None or ts < window_start:
                continue
        windowed += 1
        if ts is not None:
            current = latest_by_source.get(source_key)
            if current is None or ts > current[0]:
                latest_by_source[source_key] = (
                    ts,
                    {
                        "event": rec.get("event"),
                        "title": rec.get("title"),
                    },
                )
        event = str(rec.get("event") or "unknown")
        by_event[event] = by_event.get(event, 0) + 1
        if event in {"pre_gate_hold", "held_for_refinement"}:
            reason = str(rec.get("reason") or "").strip() or "unspecified"
            by_refinement_reason[reason] = by_refinement_reason.get(reason, 0) + 1
        if event not in {"pre_gate_reject", "rejected"}:
            continue
        reason = str(rec.get("reason") or "").strip()
        if not reason:
            reason = "unspecified"
        candidate_id = str(rec.get("candidate_id") or "").strip()
        rejection_key = (candidate_id, reason) if candidate_id else (str(id(rec)), reason)
        if rejection_key in seen_rejection_keys:
            continue
        seen_rejection_keys.add(rejection_key)
        source = str(rec.get("source") or "unknown").strip() or "unknown"
        by_rejection_reason[reason] = by_rejection_reason.get(reason, 0) + 1
        by_rejection_source[source] = by_rejection_source.get(source, 0) + 1
        source_counts = by_source_reason.setdefault(source, {})
        source_counts[reason] = source_counts.get(reason, 0) + 1
        if reason.startswith("logic_packet_gate:"):
            payload = reason.split(":", 1)[1]
            for part in payload.split(";"):
                key = part.split(":", 1)[0].strip()
                if key:
                    by_logic_packet_reason[key] = by_logic_packet_reason.get(key, 0) + 1
            try:
                import logic_packet_gate

                replay = logic_packet_gate.validate_logic_packet(rec)
            except Exception:
                replay = None
            if replay is not None and replay.ok:
                stale_logic_packet_rejections += 1
            elif replay is not None:
                for part in replay.reasons:
                    key = part.split(":", 1)[0].strip()
                    if key:
                        by_current_logic_packet_reason[key] = (
                            by_current_logic_packet_reason.get(key, 0) + 1
                        )
        elif reason == "forbidden_axis_or_marker_candidate":
            if _has_forbidden_axis_marker(
                str(rec.get("title") or ""),
                str(rec.get("claim") or ""),
                str(rec.get("rationale") or ""),
            ):
                by_current_forbidden_axis_reason[reason] = (
                    by_current_forbidden_axis_reason.get(reason, 0) + 1
                )
            else:
                stale_forbidden_axis_rejections += 1

    def _top(counts: dict[str, int], n: int = 20) -> list[dict[str, Any]]:
        return [
            {"reason": key, "count": count}
            for key, count in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:n]
        ]

    def _latest_source_payload(
        latest: dict[str, tuple[datetime, dict[str, Any]]],
    ) -> dict[str, dict[str, Any]]:
        return {
            source: {
                "ts": ts.isoformat(timespec="seconds"),
                "age_seconds": int((datetime.now(timezone.utc) - ts).total_seconds()),
                **event,
            }
            for source, (ts, event) in sorted(latest.items())
        }

    return {
        "events": len(lines),
        "sampled": len(tail),
        "windowed": windowed,
        "since_hours": since_hours,
        "window_start": window_start.isoformat(timespec="seconds") if window_start else None,
        "latest_event_ts": latest_ts.isoformat(timespec="seconds") if latest_ts else None,
        "latest_event_age_seconds": (
            int((datetime.now(timezone.utc) - latest_ts).total_seconds())
            if latest_ts else None
        ),
        "latest_event": latest_event,
        "latest_by_source": _latest_source_payload(latest_by_source),
        "latest_by_source_sampled": _latest_source_payload(latest_by_source_sampled),
        "by_event": dict(sorted(by_event.items())),
        "rejection_reasons": _top(by_rejection_reason),
        "refinement_reasons": _top(by_refinement_reason),
        "rejection_sources": _top(by_rejection_source),
        "rejection_reasons_by_source": {
            source: _top(counts, n=10)
            for source, counts in sorted(by_source_reason.items())
        },
        "logic_packet_gate_reasons": _top(by_logic_packet_reason),
        "current_logic_packet_gate_reasons": _top(by_current_logic_packet_reason),
        "stale_logic_packet_gate_rejections": stale_logic_packet_rejections,
        "current_forbidden_axis_reasons": _top(by_current_forbidden_axis_reason),
        "stale_forbidden_axis_rejections": stale_forbidden_axis_rejections,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Summarize the BEDC candidate inbox")
    parser.add_argument("--limit", type=int, default=5000, help="Maximum recent JSONL records to scan; <=0 scans all")
    parser.add_argument("--since-hours", type=float, default=0.0, help="Only count records newer than this many hours")
    args = parser.parse_args()
    if args.since_hours < 0:
        parser.error("--since-hours must be non-negative")
    print(json.dumps(stats(limit=args.limit, since_hours=args.since_hours), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

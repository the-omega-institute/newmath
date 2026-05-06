#!/usr/bin/env python3
"""Runtime candidate inbox and deterministic pre-gate for BOARD candidates."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import board_archive
import paper_index
from dispatch_bedc_target import REPO_ROOT, SCRIPT_DIR
from locks import file_lock


INBOX_PATH = SCRIPT_DIR / "state" / "candidate_inbox.jsonl"
FORBIDDEN_AXIS_RE = re.compile(
    r"closurestatus|theoryclosure|formalstatus|leantarget|leanchecked|"
    r"leanvariant|leansorry|leanstmt|leandef|marker-only|verification-axis|"
    r"chapter retirement",
    re.IGNORECASE,
)
STRUCTURAL_TITLE_RE = re.compile(
    r"^\s*\\(?:label|begin|chapter|section|subsection|input|include)\b",
    re.IGNORECASE,
)


@dataclass
class ScreenResult:
    accepted: list[dict[str, Any]] = field(default_factory=list)
    rejected: list[dict[str, Any]] = field(default_factory=list)


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
        **extra,
    }
    with file_lock("candidate_inbox"):
        with INBOX_PATH.open("a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _paper_file_lookup() -> dict[str, dict[str, Any]]:
    index = paper_index.load_or_build()
    return {item.get("file", ""): item for item in index.get("files", [])}


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
    if FORBIDDEN_AXIS_RE.search(" ".join([title, claim, rationale])):
        return "forbidden_axis_or_marker_candidate"
    if _score(candidate, "fit_score") < fit_threshold:
        return f"below_fit_threshold:{_score(candidate, 'fit_score')}"
    if _score(candidate, "novelty") < novelty_threshold:
        return f"below_novelty_threshold:{_score(candidate, 'novelty')}"
    if not inputs:
        return "missing_local_inputs"

    safe_landing = False
    for rel in inputs:
        if rel.startswith("lean4/"):
            return f"non_paper_local_input:{rel}"
        if not rel.startswith("papers/bedc/parts/"):
            return f"non_paper_local_input:{rel}"
        if not _path_exists(rel):
            return f"missing_local_input:{rel}"
        info = file_lookup.get(rel)
        if info and not info.get("hub_like") and not info.get("near_line_cap"):
            safe_landing = True

    if not safe_landing:
        if any((file_lookup.get(rel) or {}).get("hub_like") for rel in inputs):
            return "hub_only_landing"
        if any((file_lookup.get(rel) or {}).get("near_line_cap") for rel in inputs):
            return "near_line_cap_no_safe_landing"
        return "no_indexed_safe_landing"

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
    seen_titles: set[str] = set()

    for raw in candidates:
        if not isinstance(raw, dict):
            continue
        cand = dict(raw)
        cand_source = str(cand.get("source") or source)
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
            fit_threshold=fit_threshold,
            novelty_threshold=novelty_threshold,
        )
        title_key = str(cand.get("title", "")).strip().lower()
        if reason:
            rejected = {**cand, "source": cand_source, "reason": reason}
            result.rejected.append(rejected)
            _record("pre_gate_reject", rejected, cand_source, reason=reason)
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
        _record("rejected", candidate, source, reason=reason, mode=mode)


def stats(limit: int = 5000) -> dict[str, Any]:
    if not INBOX_PATH.exists():
        return {"events": 0, "by_event": {}}
    lines = INBOX_PATH.read_text(encoding="utf-8", errors="replace").splitlines()
    tail = lines[-limit:]
    by_event: dict[str, int] = {}
    for line in tail:
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        event = str(rec.get("event") or "unknown")
        by_event[event] = by_event.get(event, 0) + 1
    return {"events": len(lines), "sampled": len(tail), "by_event": dict(sorted(by_event.items()))}


def main() -> int:
    print(json.dumps(stats(), ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

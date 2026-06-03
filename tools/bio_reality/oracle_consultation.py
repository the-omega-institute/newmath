#!/usr/bin/env python3
"""High-level BioReality oracle consultation helpers."""

from __future__ import annotations

import json
import re
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable

try:
    from oracle import oracle_client
except ModuleNotFoundError:  # pragma: no cover
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from oracle import oracle_client


def _utc_stamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def _safe_slug(value: str, *, max_len: int = 80) -> str:
    slug = re.sub(r"[^A-Za-z0-9._-]+", "-", value.strip()).strip("-._")
    return (slug or "oracle-topic")[:max_len]


def _tail(value: Any, limit: int = 800) -> str:
    text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, sort_keys=True)
    if len(text) <= limit:
        return text
    return text[-limit:]


def _response_text(result: Any) -> str:
    if not isinstance(result, dict):
        return _tail(result)
    for key in ("response", "answer", "output", "text", "detail"):
        value = result.get(key)
        if isinstance(value, str) and value:
            return value
    return json.dumps(result, ensure_ascii=False, sort_keys=True)


def _turn_summaries(turn_history: list[dict[str, Any]]) -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    for turn in turn_history:
        result = turn.get("result") if isinstance(turn.get("result"), dict) else {}
        summaries.append(
            {
                "turn": turn.get("turn"),
                "prompt_tail": _tail(turn.get("prompt", ""), 800),
                "status": result.get("status") if isinstance(result, dict) else "",
                "conversation_id": result.get("conversation_id") if isinstance(result, dict) else "",
                "response_tail": _tail(_response_text(result), 800),
            }
        )
    return summaries


def _extract_codex_event_text(stdout: str) -> str:
    texts: list[str] = []
    for line in stdout.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        try:
            event = json.loads(stripped)
        except json.JSONDecodeError:
            texts.append(stripped)
            continue
        if not isinstance(event, dict):
            continue
        for key in ("text", "message", "content"):
            value = event.get(key)
            if isinstance(value, str) and value.strip():
                texts.append(value)
        item = event.get("item")
        if isinstance(item, dict):
            value = item.get("text")
            if isinstance(value, str) and value.strip():
                texts.append(value)
            content = item.get("content")
            if isinstance(content, list):
                for part in content:
                    if isinstance(part, dict):
                        part_text = part.get("text")
                        if isinstance(part_text, str) and part_text.strip():
                            texts.append(part_text)
            elif isinstance(content, str) and content.strip():
                texts.append(content)
        delta = event.get("delta")
        if isinstance(delta, str) and delta.strip():
            texts.append(delta)
    return texts[-1] if texts else stdout


def _extract_json_object(text: str) -> dict[str, Any] | None:
    stripped = text.strip()
    candidates: list[str] = []
    for match in re.finditer(r"```(?:json)?\s*(\{.*?\})\s*```", stripped, re.DOTALL | re.IGNORECASE):
        candidates.append(match.group(1))
    if stripped:
        candidates.append(stripped)
    first = stripped.find("{")
    last = stripped.rfind("}")
    if first != -1 and last > first:
        candidates.append(stripped[first : last + 1])
    for candidate in reversed(candidates):
        try:
            parsed = json.loads(candidate)
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict):
            return parsed
    return None


def _normalize_decision(parsed: dict[str, Any]) -> dict[str, Any] | None:
    if "continue" not in parsed or "useful_score" not in parsed:
        return None
    try:
        useful_score = int(parsed.get("useful_score"))
    except (TypeError, ValueError):
        return None
    useful_score = max(0, min(10, useful_score))
    if bool(parsed.get("continue")):
        next_prompt = str(parsed.get("next_prompt") or "").strip()
        rationale = str(parsed.get("rationale") or "").strip()
        if not next_prompt:
            return None
        return {
            "continue": True,
            "next_prompt": next_prompt,
            "rationale": rationale,
            "useful_score": useful_score,
        }
    reason = str(parsed.get("reason") or parsed.get("rationale") or "codex judge stopped").strip()
    return {"continue": False, "reason": reason, "useful_score": useful_score}


def codex_judge_callback(
    repo_root: Path,
    lane: str,
    topic_brief: str,
    max_total_turns: int,
    codex_timeout_seconds: int = 240,
) -> Callable[[list[dict[str, Any]]], dict[str, Any]]:
    """Return a callback that asks Codex whether the oracle session should continue."""

    root = Path(repo_root).resolve()
    max_turns = max(0, int(max_total_turns))

    def callback(turn_history: list[dict[str, Any]]) -> dict[str, Any]:
        callback.judge_calls = int(getattr(callback, "judge_calls", 0)) + 1
        if len(turn_history) >= max_turns:
            return {"continue": False, "reason": "max_total_turns reached", "useful_score": 0}
        payload = {
            "lane": lane,
            "topic_brief": topic_brief,
            "completed_turns": len(turn_history),
            "max_total_turns": max_turns,
            "turn_history": _turn_summaries(turn_history),
        }
        prompt = "\n".join(
            [
                "You are the Codex reasoning judge for a BioReality ChatGPT oracle session.",
                "Decide whether the same ChatGPT conversation can still produce useful content.",
                "Ground only in the lane, topic brief, and summarized turn history below.",
                "If continuing, ask one concrete follow-up question for the same conversation_id.",
                "Return exactly one JSON object matching one of these schemas:",
                '{"continue": true, "next_prompt": "...", "rationale": "...", "useful_score": 0}',
                '{"continue": false, "reason": "...", "useful_score": 0}',
                "useful_score must be an integer from 0 to 10.",
                "",
                json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2),
            ]
        )
        try:
            completed = subprocess.run(
                [
                    "codex",
                    "exec",
                    "--dangerously-bypass-approvals-and-sandbox",
                    "--sandbox",
                    "read-only",
                    "--json",
                    "-C",
                    str(root),
                    "-",
                ],
                input=prompt,
                text=True,
                capture_output=True,
                timeout=codex_timeout_seconds,
                check=False,
            )
        except (subprocess.TimeoutExpired, OSError) as exc:
            return {"continue": False, "reason": f"codex judge error: {exc}", "useful_score": 0}
        if completed.returncode != 0:
            detail = (completed.stderr or completed.stdout or "codex judge failed").strip()
            return {"continue": False, "reason": detail[:400], "useful_score": 0}
        parsed = _extract_json_object(_extract_codex_event_text(completed.stdout or ""))
        decision = _normalize_decision(parsed or {})
        if decision is None:
            return {"continue": False, "reason": "codex judge returned invalid JSON", "useful_score": 0}
        return decision

    callback.judge_calls = 0
    return callback


def _write_transcript_jsonl(path: Path, result: dict[str, Any], *, lane: str, topic: str, pdf_attached: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        header = {
            "record_kind": "session",
            "lane": lane,
            "topic": topic,
            "conversation_id": result.get("conversation_id"),
            "closed_reason": result.get("closed_reason"),
            "max_turns_reached": result.get("max_turns_reached"),
            "pdf_attached": pdf_attached,
            "pdf_skipped_reason": result.get("pdf_skipped_reason") or "",
            "turn_count": len(result.get("turns") if isinstance(result.get("turns"), list) else []),
        }
        handle.write(json.dumps(header, ensure_ascii=False, sort_keys=True) + "\n")
        for turn in result.get("turns", []):
            if isinstance(turn, dict):
                handle.write(json.dumps({"record_kind": "turn", **turn}, ensure_ascii=False, sort_keys=True) + "\n")


def _write_digest(path: Path, result: dict[str, Any], *, lane: str, topic: str, pdf_attached: bool) -> None:
    lines = [
        f"# Oracle consultation: {topic}",
        "",
        f"- lane: {lane}",
        f"- conversation_id: {result.get('conversation_id') or ''}",
        f"- closed_reason: {result.get('closed_reason') or ''}",
        f"- pdf_attached: {str(pdf_attached).lower()}",
        f"- pdf_skipped_reason: {result.get('pdf_skipped_reason') or ''}",
        f"- turns: {len(result.get('turns') if isinstance(result.get('turns'), list) else [])}",
        "",
    ]
    for turn in result.get("turns", []):
        if not isinstance(turn, dict):
            continue
        result_obj = turn.get("result") if isinstance(turn.get("result"), dict) else {}
        lines.extend(
            [
                f"## Turn {turn.get('turn')}",
                "",
                "Prompt tail:",
                "",
                "```text",
                _tail(turn.get("prompt", ""), 1200),
                "```",
                "",
                "Response tail:",
                "",
                "```text",
                _tail(_response_text(result_obj), 2000),
                "```",
                "",
            ]
        )
    path.write_text("\n".join(lines), encoding="utf-8")


def run_oracle_consultation(
    repo_root: Path,
    lane: str,
    topic: str,
    initial_prompt: str,
    *,
    intended_claim_id: str = "",
    pdf_path: Path | str | None = None,
    max_turns: int = 12,
    persist_dir: Path | None = None,
    server_url: str = "http://127.0.0.1:8769",
    poll_timeout: int = 600,
    codex_judge_timeout: int = 240,
    existing_conversation_id: str = "",
    close_on_exit: bool = False,
) -> dict[str, Any]:
    """Run a multi-turn oracle consultation and optionally persist its transcript."""

    pdf_base64, pdf_name = oracle_client.encode_pdf_for_attach(pdf_path)
    pdf_attached = bool(pdf_base64)
    pdf_skipped_reason = ""
    if pdf_path is not None and not pdf_attached:
        pdf_skipped_reason = "pdf_missing_or_unreadable"
    judge = codex_judge_callback(
        Path(repo_root),
        lane,
        topic,
        max_turns,
        codex_timeout_seconds=codex_judge_timeout,
    )
    # Skip PDF attach when resuming an existing conversation (ChatGPT already has the file).
    if existing_conversation_id:
        pdf_base64 = ""
        pdf_name = ""
        pdf_skipped_reason = pdf_skipped_reason or "resuming_existing_conversation"
    result = oracle_client.run_session(
        initial_prompt,
        topic=topic,
        judge_callback=judge,
        max_turns=max_turns,
        intended_claim_id=intended_claim_id,
        intended_lane=lane,
        pdf_base64=pdf_base64,
        pdf_name=pdf_name,
        existing_conversation_id=existing_conversation_id,
        close_on_exit=close_on_exit,
        server_url=server_url,
        poll_timeout=poll_timeout,
    )
    if not isinstance(result, dict):
        result = {"topic": topic, "conversation_id": "", "turns": [], "closed_reason": "run_session returned non-dict"}
    result = dict(result)
    result["pdf_attached"] = pdf_attached
    result["pdf_skipped_reason"] = pdf_skipped_reason
    result["judge_calls"] = int(getattr(judge, "judge_calls", 0))
    if persist_dir is not None:
        stamp = _utc_stamp()
        base = Path(persist_dir) / lane
        stem = f"{stamp}__{_safe_slug(topic)}"
        jsonl_path = base / f"{stem}.jsonl"
        md_path = base / f"{stem}.md"
        _write_transcript_jsonl(jsonl_path, result, lane=lane, topic=topic, pdf_attached=pdf_attached)
        _write_digest(md_path, result, lane=lane, topic=topic, pdf_attached=pdf_attached)
        result["transcript_jsonl"] = str(jsonl_path)
        result["transcript_md"] = str(md_path)
    return result

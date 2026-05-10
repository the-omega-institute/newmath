#!/usr/bin/env python3
"""Promote gated Automath-to-NewMath bridge records into BEDC BOARD candidates.

This adapter deliberately reuses `tools/bedc-deep/board_spawn.py` instead of
hand-appending BOARD.md. The bridge only prepares durable review packets and
candidate dicts; BEDC's native fit, novelty, dedup, Claude judge, and atomic
append gates decide whether anything reaches the BOARD.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_PACKET_DIR = SCRIPT_DIR / "review_packets"
BEDC_DEEP_DIR = REPO_ROOT / "tools" / "bedc-deep"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    records: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            data = json.loads(text)
            if not isinstance(data, dict):
                raise ValueError(f"{path}:{line_no}: expected object record")
            records.append(data)
    return records


def _safe_slug(text: str, *, limit: int = 96) -> str:
    cleaned = "".join(ch.lower() if ch.isalnum() else "-" for ch in text)
    cleaned = "-".join(part for part in cleaned.split("-") if part)
    return cleaned[:limit].strip("-") or "bridge-record"


def _short_digest(record: dict[str, Any]) -> str:
    payload = json.dumps(
        {
            "artifact_key": record.get("artifact_key"),
            "source_commit": record.get("source_commit"),
            "source_path": record.get("source_path"),
        },
        sort_keys=True,
    )
    return hashlib.sha1(payload.encode("utf-8")).hexdigest()[:12]


def _packet_path(record: dict[str, Any], packet_dir: Path) -> Path:
    source_path = str(record.get("source_path") or record.get("id") or "bridge-record")
    slug = _safe_slug(source_path)
    return packet_dir / f"{slug}-{_short_digest(record)}.json"


def _write_packet(record: dict[str, Any], packet_dir: Path) -> Path:
    packet_dir.mkdir(parents=True, exist_ok=True)
    path = _packet_path(record, packet_dir)
    packet = {
        "schema_version": "automath-newmath-bridge-review-packet-v1",
        "created_at": _now_iso(),
        "status": "needs_bedc_board_review",
        "source_repo": record.get("source_repo"),
        "source_branch_or_ref": record.get("source_branch_or_ref"),
        "source_commit": record.get("source_commit"),
        "source_path": record.get("source_path"),
        "source_artifact_kind": record.get("source_artifact_kind"),
        "destination_repo": record.get("destination_repo"),
        "destination_branch_or_ref": record.get("destination_branch_or_ref"),
        "destination_path": "tools/bedc-deep/BOARD.md",
        "destination_artifact_kind": "open_problem_target",
        "bridge_direction": "automath_to_newmath",
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "gate_result": record,
        "non_actions": [
            "no direct BEDC paper write",
            "no direct BEDC Lean write",
            "no direct proposal acceptance",
            "no external publication",
            "no push from this adapter",
        ],
    }
    path.write_text(json.dumps(packet, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def _title(record: dict[str, Any]) -> str:
    kind = str(record.get("source_artifact_kind") or "artifact").replace("_", " ")
    path = str(record.get("source_path") or record.get("artifact_key") or "Automath artifact")
    stem = Path(path).stem.replace("_", " ").replace("-", " ").strip()
    if len(stem) > 64:
        stem = stem[:61].rstrip() + "..."
    return f"Automath bridge review: {stem} ({kind})"


def _claim(record: dict[str, Any], packet_rel: str) -> str:
    evidence = record.get("evidence_summary")
    if not isinstance(evidence, list) or not evidence:
        evidence = [record.get("next_action") or "Automath source evidence is ready for NewMath-side review."]
    evidence_text = "; ".join(str(item) for item in evidence if str(item).strip())
    source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
    return (
        "Evaluate whether this Automath artifact should become a BEDC research "
        f"target. Source: {source}. Bridge packet: {packet_rel}. Evidence: "
        f"{evidence_text}. The task is to extract a NewMath-native theorem, "
        "obstruction, or planning target without copying Automath runtime state."
    )


def _candidate(record: dict[str, Any], packet_rel: str) -> dict[str, Any]:
    priority = int(record.get("priority") or 50)
    fit = min(10, max(7, priority // 10))
    novelty = min(10, max(6, (priority + 8) // 10))
    return {
        "title": _title(record),
        "claim": _claim(record, packet_rel),
        "chapter": "concrete_instances",
        "relation": "bridge_input",
        "source": "automath_newmath_bridge",
        "local_inputs": [packet_rel],
        "rationale": (
            "Automath-to-NewMath bridge gate passed. BEDC board_spawn must still "
            "judge fit, novelty, dedup, and paper coverage before BOARD append."
        ),
        "fit_score": fit,
        "novelty": novelty,
    }


def _eligible(record: dict[str, Any]) -> bool:
    if record.get("bridge_direction") != "automath_to_newmath":
        return False
    if record.get("gate_status") != "gate_passed":
        return False
    if record.get("readiness") not in {"ready_for_local_packet", "needs_operator_review"}:
        return False
    if record.get("destination_repo") != "the-omega-institute/newmath":
        return False
    if record.get("source_artifact_kind") not in {
        "lean_theorem",
        "paper_claim",
        "writeback_packet",
        "candidate_mechanism",
        "audit_failure",
    }:
        return False
    return True


def build_candidates(
    records: list[dict[str, Any]],
    *,
    packet_dir: Path,
    limit: int,
    write_packets: bool,
) -> tuple[list[dict[str, Any]], list[Path]]:
    candidates: list[dict[str, Any]] = []
    packets: list[Path] = []
    for record in records:
        if len(candidates) >= limit:
            break
        if not _eligible(record):
            continue
        packet_path = _write_packet(record, packet_dir) if write_packets else _packet_path(record, packet_dir)
        packet_rel = str(packet_path.relative_to(REPO_ROOT))
        packets.append(packet_path)
        candidates.append(_candidate(record, packet_rel))
    return candidates, packets


def run_board_spawn(candidates: list[dict[str, Any]], *, fit_threshold: int, novelty_threshold: int) -> Any:
    sys.path.insert(0, str(BEDC_DEEP_DIR))
    import board_spawn  # type: ignore

    return board_spawn.spawn_from_candidates(
        codex_candidates=candidates,
        oracle_candidates=[],
        fit_threshold=fit_threshold,
        novelty_threshold=novelty_threshold,
    )


def _accepted_packet_rels(result: Any) -> set[str]:
    accepted = getattr(result, "accepted", []) or []
    rels: set[str] = set()
    for item in accepted:
        if not isinstance(item, dict):
            continue
        inputs = item.get("local_inputs") or []
        if isinstance(inputs, str):
            inputs = [inputs]
        for rel in inputs:
            text = str(rel).strip()
            if text.startswith("tools/automath_newmath_bridge/review_packets/"):
                rels.add(text)
    return rels


def _cleanup_unaccepted_packets(packet_paths: list[Path], accepted_rels: set[str]) -> list[str]:
    removed: list[str] = []
    for path in packet_paths:
        try:
            rel = str(path.relative_to(REPO_ROOT))
        except ValueError:
            continue
        if rel in accepted_rels:
            continue
        try:
            path.unlink()
        except FileNotFoundError:
            pass
        else:
            removed.append(rel)
    return removed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Bridge Automath gate results into BEDC BOARD candidates")
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--packet-dir", default=str(DEFAULT_PACKET_DIR))
    parser.add_argument("--limit", type=int, default=3)
    parser.add_argument("--fit-threshold", type=int, default=7)
    parser.add_argument("--novelty-threshold", type=int, default=6)
    parser.add_argument("--apply", action="store_true", help="Run BEDC board_spawn and allow BOARD append")
    parser.add_argument(
        "--write-packets",
        action="store_true",
        help="Write durable review packet JSON files without applying BOARD ingest",
    )
    args = parser.parse_args(argv)

    records = _read_jsonl(Path(args.gate_results))
    candidates, packets = build_candidates(
        records,
        packet_dir=Path(args.packet_dir),
        limit=max(0, args.limit),
        write_packets=bool(args.apply or args.write_packets),
    )
    summary: dict[str, Any] = {
        "eligible_candidates": len(candidates),
        "packet_paths": [str(path.relative_to(REPO_ROOT)) for path in packets],
        "apply": bool(args.apply),
    }
    if not candidates:
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0
    if args.apply:
        result = run_board_spawn(
            candidates,
            fit_threshold=args.fit_threshold,
            novelty_threshold=args.novelty_threshold,
        )
        summary.update(
            {
                "board_spawn_ok": bool(getattr(result, "ok", False)),
                "appended_ids": list(getattr(result, "appended_ids", []) or []),
                "accepted_count": len(getattr(result, "accepted", []) or []),
                "rejected_count": len(getattr(result, "rejected", []) or []),
                "error": getattr(result, "error", ""),
            }
        )
        accepted_rels = _accepted_packet_rels(result)
        summary["removed_unaccepted_packets"] = _cleanup_unaccepted_packets(packets, accepted_rels)
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0 if getattr(result, "ok", False) else 1
    summary["dry_run_candidates"] = candidates
    print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

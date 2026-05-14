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

try:
    from logic_discipline import bridge_payload
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from logic_discipline import bridge_payload


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_PACKET_DIR = SCRIPT_DIR / "review_packets"
BEDC_DEEP_DIR = REPO_ROOT / "tools" / "bedc-deep"
BEDC_PARTS_PREFIX = "papers/bedc/parts/"
INSPIRATION_ONLY_PREFIXES = (
    "papers/bedc/parts/visions/",
    "papers/bedc/parts/conjectures/",
)


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


def _as_list(value: Any) -> list[str]:
    if isinstance(value, list):
        return [str(item).strip() for item in value if str(item).strip()]
    if isinstance(value, str) and value.strip():
        return [value.strip()]
    return []


def _is_bedc_native_landing(rel: str) -> bool:
    text = str(rel).strip()
    if not text.startswith(BEDC_PARTS_PREFIX):
        return False
    if any(text.startswith(prefix) for prefix in INSPIRATION_ONLY_PREFIXES):
        return False
    return (REPO_ROOT / text).exists()


def _candidate_landing_inputs(record: dict[str, Any]) -> tuple[list[str], list[str]]:
    """Split BEDC-native paper landings from source/review metadata.

    Bridge records are allowed to carry broad source signals, including JSON
    packets and sibling-repo paths.  Those are fixed-point memory, not BOARD
    execution surfaces.  Only concrete BEDC paper files can become
    `local_inputs`.
    """

    raw: list[str] = []
    metadata: list[str] = []
    for key in (
        "bedc_landing_files",
        "paper_files",
        "local_inputs",
        "destination_path",
        "destination_paths",
        "target_path",
        "target_paths",
    ):
        raw.extend(_as_list(record.get(key)))
    nested = record.get("candidate")
    if isinstance(nested, dict):
        for key in ("bedc_landing_files", "paper_files", "local_inputs"):
            raw.extend(_as_list(nested.get(key)))

    landings: list[str] = []
    seen: set[str] = set()
    for rel in raw:
        if _is_bedc_native_landing(rel):
            if rel not in seen:
                landings.append(rel)
                seen.add(rel)
        elif rel:
            metadata.append(rel)
    return landings, metadata


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
        "destination_path": "tools/bedc-deep/state/candidate_inbox.jsonl",
        "destination_artifact_kind": "candidate_review_signal",
        "bridge_direction": "automath_to_newmath",
        "operator_review_required": True,
        "taste_gate_required": False,
        "audit_required": True,
        "gate_result": record,
        "logic_discipline": record.get("logic_discipline") or bridge_payload(
            readiness=str(record.get("readiness") or ""),
            oracle_mode="continuation_refill",
        ),
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


def _claim(record: dict[str, Any], packet_rel: str, local_inputs: list[str]) -> str:
    evidence = record.get("evidence_summary")
    if not isinstance(evidence, list) or not evidence:
        evidence = [record.get("next_action") or "Automath source evidence is ready for NewMath-side review."]
    evidence_text = "; ".join(str(item) for item in evidence if str(item).strip())
    landing_text = (
        "BEDC landing: " + ", ".join(local_inputs) + ". "
        if local_inputs
        else "No BEDC-native landing has been identified yet; classify and defer unless a concrete existing chapter landing is supplied. "
    )
    return (
        "Evaluate whether this external theorem signal should become a BEDC "
        f"research target. {landing_text}Review packet metadata: {packet_rel}. "
        f"Evidence summary: {evidence_text}. The task is to extract a NewMath-native theorem, "
        "obstruction, or planning target without copying Automath runtime state. "
        "The source and packet strings are BOARD review metadata only; if any "
        "candidate becomes paper LaTeX, do not reproduce Automath paths, the "
        "word Automath, JSON paths, bridge packet paths, repository coordinates, or external "
        "provenance phrases in the paper body. "
        "Apply the logic-minimization discipline: expose axiom budget, "
        "witness status, cut/elimination status, equality or interpretation "
        "kind, dependency/resource trace, oracle mode, and descent-certificate "
        "boundary."
    )


def _candidate(record: dict[str, Any], packet_rel: str) -> dict[str, Any]:
    priority = int(record.get("priority") or 50)
    fit = min(10, max(7, priority // 10))
    novelty = min(10, max(6, (priority + 8) // 10))
    local_inputs, metadata_inputs = _candidate_landing_inputs(record)
    landing_kind = str(record.get("landing_kind") or "").strip()
    if landing_kind not in {
        "existing_chapter_lemma",
        "existing_chapter_obligation",
        "existing_chapter_ledger_row",
        "new_chapter",
        "reject",
    }:
        landing_kind = "existing_chapter_lemma" if local_inputs else "reject"
    metadata_note = (
        "Review metadata retained outside BOARD local_inputs: "
        + ", ".join([packet_rel, *metadata_inputs])
    )
    return {
        "title": _title(record),
        "claim": _claim(record, packet_rel, local_inputs),
        "chapter": "concrete_instances",
        "relation": "bridge_input",
        "source": "automath_newmath_bridge",
        "kind": "automath_concretization",
        "landing_kind": landing_kind,
        "tastegate_mode": "existing_chapter" if landing_kind != "new_chapter" else "new_chapter",
        "local_inputs": local_inputs,
        "review_packet": packet_rel,
        "review_metadata_inputs": [packet_rel, *metadata_inputs],
        "selection_rank": record.get("selection_rank") or "",
        "difficulty": record.get("difficulty") or "medium",
        "quality_score": record.get("quality_score") or "",
        "rationale": (
            "Automath-to-NewMath bridge gate passed. BEDC board_spawn must still "
            "judge fit, novelty, dedup, paper coverage, and logic-minimization "
            "discipline before BOARD append. " + metadata_note
        ),
        "fit_score": fit,
        "novelty": novelty,
        "resource_trace": metadata_note,
        "dependency_trace": (
            "No ambient sibling-repo dependency is admitted; only listed "
            "BEDC local_inputs may be used after gate acceptance."
        ),
        "oracle_mode": "candidate_generation",
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
        summary["retained_review_packets"] = [str(path.relative_to(REPO_ROOT)) for path in packets]
        print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
        return 0 if getattr(result, "ok", False) else 1
    summary["dry_run_candidates"] = candidates
    print(json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

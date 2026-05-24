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
import re
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
S1_FINITE_RANK_LANDING = "papers/bedc/parts/concrete_instances/s1/finite_rank_host_obstruction.tex"
LANDING_LINE_CAP = 720
LANDING_TEXT_LIMIT = 80_000
LANDING_MIN_SCORE = 8
LANDING_MIN_MATCHES = 3
LANDING_STOPWORDS = {
    "automath",
    "bedc",
    "bridge",
    "candidate",
    "chapter",
    "conclusion",
    "derived",
    "gate",
    "golden",
    "killo",
    "lean",
    "lean4",
    "landing",
    "lemma",
    "newmath",
    "noise",
    "omega",
    "paper",
    "signal",
    "source",
    "theorem",
    "unmapped",
    "unrelated",
    "vocabulary",
    "with",
}
LANDING_ALIASES = {
    "circledimension": ["circle", "sone", "s1"],
    "homologizable": ["homolog", "homologization"],
    "homologization": ["homolog"],
    "fibonacci": ["fibonacci", "fibonaccicube"],
    "goldenmean": ["goldenmean", "goldenmeanshift"],
    "goldenmeanshift": ["goldenmean", "goldenmeanshift"],
}
_LANDING_CATALOG: list[dict[str, Any]] | None = None


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


def _explicit_family_landing(record: dict[str, Any]) -> list[str]:
    source_path = str(record.get("source_path") or "").lower()
    kind = str(record.get("source_artifact_kind") or "").strip()
    if kind == "lean_theorem" and (
        "circledimension" in source_path
        or "finite" in source_path and "rank" in source_path and "host" in source_path
    ):
        if _is_bedc_native_landing(S1_FINITE_RANK_LANDING):
            return [S1_FINITE_RANK_LANDING]
    return []


def _json_fragments(value: Any, *, depth: int = 0) -> list[str]:
    if depth > 3:
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, (int, float, bool)) or value is None:
        return []
    if isinstance(value, list):
        out: list[str] = []
        for item in value[:24]:
            out.extend(_json_fragments(item, depth=depth + 1))
        return out
    if isinstance(value, dict):
        out = []
        for key, item in list(value.items())[:40]:
            out.append(str(key))
            out.extend(_json_fragments(item, depth=depth + 1))
        return out
    return [str(value)]


def _split_terms(text: str) -> list[str]:
    spaced = re.sub(r"([a-z])([A-Z])", r"\1 \2", text)
    raw = re.findall(r"[A-Za-z][A-Za-z0-9]{2,}", spaced)
    out: list[str] = []
    seen: set[str] = set()
    for item in raw:
        term = item.lower()
        for part in re.findall(r"[a-z][a-z0-9]{2,}", re.sub(r"[^a-z0-9]+", " ", term)):
            if len(part) < 4 or part in LANDING_STOPWORDS:
                continue
            for expanded in [part, *LANDING_ALIASES.get(part, [])]:
                if expanded not in seen and expanded not in LANDING_STOPWORDS:
                    out.append(expanded)
                    seen.add(expanded)
    return out


def _record_terms(record: dict[str, Any]) -> list[str]:
    fragments: list[str] = []
    for key in (
        "source_path",
        "source_artifact_kind",
        "artifact_key",
        "notes",
        "next_action",
        "evidence_summary",
        "matching_newmath_evidence",
        "matching_automath_evidence",
        "synthesis",
    ):
        fragments.extend(_json_fragments(record.get(key)))
    return _split_terms(" ".join(fragments))


def _load_paper_index() -> dict[str, Any]:
    sys.path.insert(0, str(BEDC_DEEP_DIR))
    import paper_index  # type: ignore

    return paper_index.load_or_build()


def _landing_haystack(rel: str, info: dict[str, Any]) -> str:
    labels = info.get("labels") or []
    label_text = " ".join(
        " ".join(
            str(rec.get(key) or "")
            for key in ("label", "env", "title")
        )
        for rec in labels[:80]
        if isinstance(rec, dict)
    )
    path = REPO_ROOT / rel
    try:
        body = path.read_text(encoding="utf-8", errors="replace")[:LANDING_TEXT_LIMIT]
    except OSError:
        body = ""
    return " ".join([rel, label_text, body]).lower()


def _landing_catalog() -> list[dict[str, Any]]:
    global _LANDING_CATALOG
    if _LANDING_CATALOG is not None:
        return _LANDING_CATALOG
    catalog: list[dict[str, Any]] = []
    for info in _load_paper_index().get("files") or []:
        if not isinstance(info, dict):
            continue
        rel = str(info.get("file") or "")
        if not _is_bedc_native_landing(rel):
            continue
        if info.get("hub_like"):
            continue
        try:
            line_count = int(info.get("line_count") or info.get("lines") or 0)
        except (TypeError, ValueError):
            line_count = 0
        if line_count >= LANDING_LINE_CAP:
            continue
        catalog.append(
            {
                "file": rel,
                "line_count": line_count,
                "haystack": _landing_haystack(rel, info),
            }
        )
    _LANDING_CATALOG = catalog
    return catalog


def _term_weight(term: str) -> int:
    if term in {"finite", "rank", "host", "fibonacci", "fibonaccicube", "collision", "kernel"}:
        return 3
    if len(term) >= 10:
        return 3
    if len(term) >= 7:
        return 2
    return 1


def _specific_terms(terms: list[str]) -> set[str]:
    return {
        term for term in terms
        if len(term) >= 7 or term in {"rank", "host", "sone", "fibonacci", "circle"}
    }


def _discovered_bedc_landing(record: dict[str, Any]) -> list[str]:
    terms = _record_terms(record)
    specific = _specific_terms(terms)
    if len(specific) < 2:
        return []
    scored: list[tuple[int, int, int, str]] = []
    for item in _landing_catalog():
        haystack = str(item["haystack"])
        matches = [term for term in terms if term in haystack]
        if len(set(matches)) < LANDING_MIN_MATCHES:
            continue
        if len(specific.intersection(matches)) < 2:
            continue
        score = sum(_term_weight(term) for term in set(matches))
        if score < LANDING_MIN_SCORE:
            continue
        scored.append((-score, int(item["line_count"]), -len(set(matches)), str(item["file"])))
    scored.sort()
    return [rel for _score, _line_count, _neg_matches, rel in scored[:1]]


def _inferred_bedc_landing(record: dict[str, Any]) -> list[str]:
    """Find BEDC body-file landings before emitting executable candidates."""
    explicit = _explicit_family_landing(record)
    if explicit:
        return explicit
    return _discovered_bedc_landing(record)


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
    if not landings:
        for rel in _inferred_bedc_landing(record):
            if rel not in seen:
                landings.append(rel)
                seen.add(rel)
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


def _landing_subject(record: dict[str, Any], local_inputs: list[str]) -> str:
    if local_inputs:
        stem = Path(local_inputs[0]).stem
        stem = stem.removesuffix("_namecert_construction")
        stem = stem.removesuffix("_construction")
        stem = stem.removesuffix("_core")
        stem = stem.removesuffix("_rows")
    else:
        path = str(record.get("source_path") or record.get("artifact_key") or "source signal")
        stem = Path(path).stem
    stem = re.sub(r"^\d+[_-]+", "", stem)
    stem = stem.replace("_", " ").replace("-", " ").strip()
    return stem.title() or "BEDC"


def _title(record: dict[str, Any], local_inputs: list[str]) -> str:
    stem = _landing_subject(record, local_inputs)
    if len(stem) > 64:
        stem = stem[:61].rstrip() + "..."
    if not local_inputs:
        return f"{stem} BEDC landing required"
    return f"{stem} downstream consumer lemma"


def _claim(record: dict[str, Any], packet_rel: str, local_inputs: list[str]) -> str:
    subject = _landing_subject(record, local_inputs)
    if not local_inputs:
        return (
            "This source theorem signal has no BEDC-native body-file landing. "
            "Keep it as review metadata until a concrete existing chapter file "
            "is supplied; it must not become an executable BOARD target."
        )
    return (
        f"Using the selected BEDC body file, prove a downstream consumer coverage lemma for {subject}: "
        "every accepted sibling consumer, readback, route, or handoff for the named local surface "
        "must factor through the finite rows already displayed in that chapter, and any unlisted "
        "coordinate remains unavailable to the consumer theorem."
    )


def _rationale(record: dict[str, Any], packet_rel: str, local_inputs: list[str], metadata_inputs: list[str]) -> str:
    if not local_inputs:
        return (
            "The bridge source is retained only as review metadata because no "
            "BEDC body file was selected as an execution surface."
        )
    return (
        "The source-selection packet only chooses a promising BEDC landing. "
        "Execution must inspect the listed local body file, name the existing "
        "rows or labels it consumes, and append at most one existing-chapter "
        "consumer theorem."
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
    return {
        "title": _title(record, local_inputs),
        "claim": _claim(record, packet_rel, local_inputs),
        "chapter": "concrete_instances",
        "relation": "sibling_consumer",
        "source": "automath_newmath_bridge",
        "kind": "bedc_downstream_consumer",
        "landing_kind": landing_kind,
        "tastegate_mode": "existing_chapter" if landing_kind != "new_chapter" else "new_chapter",
        "local_inputs": local_inputs,
        "review_packet": packet_rel,
        "review_metadata_inputs": [packet_rel, *metadata_inputs],
        "selection_rank": record.get("selection_rank") or "downstream_consumer",
        "difficulty": record.get("difficulty") or "medium",
        "quality_score": record.get("quality_score") or "",
        "rationale": _rationale(record, packet_rel, local_inputs, metadata_inputs),
        "fit_score": fit,
        "novelty": novelty,
        "axiom_budget": "B0_finite_witness",
        "strength_level": "B0_finite_witness",
        "budget_reason": (
            "The target is a finite consumer coverage lemma over rows already "
            "displayed in the selected BEDC chapter; it adds no host object, "
            "choice principle, or extra carrier."
        ),
        "existence_mode": "none",
        "witness_extractor": "",
        "cut_rank": "1" if local_inputs else "unknown",
        "elimination_plan": (
            "Read the named local rows in the selected BEDC body file, then "
            "show that each consumer route or handoff factors through those "
            "rows and rejects unlisted coordinates."
            if local_inputs
            else "No local landing is available, so no bridge elimination can be executed."
        ),
        "equality_kind": "none",
        "interpretation_kind": "interpretation" if local_inputs else "none",
        "resource_trace": (
            "Executable evidence is restricted to BEDC local_inputs: "
            + (", ".join(local_inputs) if local_inputs else "none")
            + ". Review metadata is retained only in structured adapter fields, "
            "not as BOARD execution evidence."
        ),
        "dependency_trace": (
            "Depends only on the selected BEDC body file and its existing "
            "labels or displayed rows; source packets and sibling-repo paths "
            "remain review metadata and cannot appear in paper body."
        ),
        "rate_modulus_surface": "",
        "oracle_mode": "proof_search",
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
    seen_candidate_keys: set[tuple[str, tuple[str, ...]]] = set()
    for record in records:
        if len(candidates) >= limit:
            break
        if not _eligible(record):
            continue
        packet_path = _write_packet(record, packet_dir) if write_packets else _packet_path(record, packet_dir)
        packet_rel = str(packet_path.relative_to(REPO_ROOT))
        candidate = _candidate(record, packet_rel)
        key = (
            str(candidate.get("title") or "").strip().lower(),
            tuple(str(item) for item in candidate.get("local_inputs") or []),
        )
        if key in seen_candidate_keys:
            continue
        seen_candidate_keys.add(key)
        packets.append(packet_path)
        candidates.append(candidate)
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
